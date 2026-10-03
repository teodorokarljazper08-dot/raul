"""
𝘾𝙊𝙇𝙎 ✘ Karl Hosting - hardened version

Configuration (environment variables):
  SECRET_KEY      Flask session key (auto-generated into .secret_key if unset)
  ADMIN_PASSWORD  Admin password (a random one is generated and printed once if unset)
  API_KEY         Required to use /api/create (endpoint is disabled if unset)
  HOST / PORT     Bind address (default 127.0.0.1:5000 - put a reverse proxy in front)
  COOKIE_SECURE   Set to 1 when serving over HTTPS
  ENABLE_TERMINAL Set to 0 to disable the limited terminal endpoint
  FLASK_DEBUG     Set to 1 only for local development

IMPORTANT: bots are still ordinary processes running as the same OS user as
this panel. For real multi-tenant isolation run each bot in a container or
under its own unprivileged OS user.
"""
import json
import os
import re
import secrets
import shlex
import shutil
import string
import subprocess
import sys
import threading
import time
import zipfile
from collections import defaultdict, deque
from datetime import datetime, timedelta
from functools import wraps
from urllib.parse import urlparse

import psutil
from flask import Flask, jsonify, redirect, render_template, request, session, url_for
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
USERS_FILE = os.path.join(BASE_DIR, 'users.json')
BOTS_DIR = os.path.join(BASE_DIR, 'bots')
SECRET_FILE = os.path.join(BASE_DIR, '.secret_key')

API_KEY = os.environ.get('API_KEY', '')
TERMINAL_ENABLED = os.environ.get('ENABLE_TERMINAL', '1') != '0'
MAX_ZIP_FILES = 5000
MAX_ZIP_BYTES = 500 * 1024 * 1024
MAX_DOWNLOAD_BYTES = 100 * 1024 * 1024

USERS_LOCK = threading.RLock()
START_LOCK = threading.Lock()
CRASH_COUNT = {}
LOGIN_ATTEMPTS = defaultdict(deque)

os.makedirs(BOTS_DIR, exist_ok=True)


def get_secret_key():
    key = os.environ.get('SECRET_KEY')
    if key:
        return key
    if os.path.exists(SECRET_FILE):
        with open(SECRET_FILE, 'r') as f:
            return f.read().strip()
    key = secrets.token_hex(32)
    with open(SECRET_FILE, 'w') as f:
        f.write(key)
    try:
        os.chmod(SECRET_FILE, 0o600)
    except OSError:
        pass
    return key


app = Flask(__name__)
app.secret_key = get_secret_key()
app.config.update(
    MAX_CONTENT_LENGTH=65 * 1024 * 1024,  # 65 MB
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE='Lax',
    SESSION_COOKIE_SECURE=os.environ.get('COOKIE_SECURE') == '1',
    PERMANENT_SESSION_LIFETIME=timedelta(hours=12),
)

# ============================================
# Validation / path safety
# ============================================

ID_RE = re.compile(r'^[0-9a-f]{8,32}$')
USERNAME_RE = re.compile(r'^[A-Za-z0-9_.-]{3,32}$')
RES_RE = re.compile(r'^\d{1,5}(MB|GB)$', re.I)
TYPE_RE = re.compile(r'^[a-z0-9_-]{1,20}$')
GH_NAME_RE = re.compile(r'^[A-Za-z0-9_.-]+$')
GH_BRANCH_RE = re.compile(r'^[A-Za-z0-9_./-]+$')


def valid_id(server_id):
    return isinstance(server_id, str) and bool(ID_RE.match(server_id))


def to_int(value, default):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def safe_join(base, *parts, allow_root=False):
    """Join paths and refuse anything that resolves outside `base`."""
    base_real = os.path.realpath(base)
    target = os.path.realpath(os.path.join(base_real, *parts))
    if target == base_real:
        if allow_root:
            return target
        raise ValueError('Path not allowed')
    if not target.startswith(base_real + os.sep):
        raise ValueError('Path not allowed')
    return target


def get_server_dir(server_id):
    if not valid_id(server_id):
        raise ValueError('Invalid server id')
    server_dir = os.path.join(BOTS_DIR, server_id)
    os.makedirs(server_dir, exist_ok=True)
    return server_dir


def safe_extract(zf, dest, strip_root=False, log=None):
    members = zf.infolist()
    if len(members) > MAX_ZIP_FILES or sum(m.file_size for m in members) > MAX_ZIP_BYTES:
        raise ValueError('Archive is too large')
    for m in members:
        name = m.filename
        if strip_root:
            name = '/'.join(name.split('/')[1:])
        if not name:
            continue
        if (m.external_attr >> 16) & 0o170000 == 0o120000:  # skip symlinks
            continue
        target = safe_join(dest, name)  # raises on traversal
        if m.is_dir():
            os.makedirs(target, exist_ok=True)
        else:
            os.makedirs(os.path.dirname(target), exist_ok=True)
            with zf.open(m) as src, open(target, 'wb') as out:
                shutil.copyfileobj(src, out)
            if log:
                log(f"  ✓ {name}")


# ============================================
# Users store (locked + atomic)
# ============================================

def _is_hashed(value):
    return isinstance(value, str) and value.startswith(('scrypt:', 'pbkdf2:'))


def generate_random_password(length=12):
    chars = string.ascii_letters + string.digits
    return ''.join(secrets.choice(chars) for _ in range(length))


def initial_admin_password():
    pw = os.environ.get('ADMIN_PASSWORD')
    if pw:
        return pw
    pw = generate_random_password(16)
    print(f"[SETUP] Generated admin password: {pw}  (set ADMIN_PASSWORD to choose your own)")
    return pw


def save_users(data):
    with USERS_LOCK:
        tmp = USERS_FILE + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False)
        os.replace(tmp, USERS_FILE)


def load_users():
    with USERS_LOCK:
        if not os.path.exists(USERS_FILE):
            data = {'admin': {'password': generate_password_hash(initial_admin_password()), 'role': 'admin'}}
            save_users(data)
            return data
        with open(USERS_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        changed = False
        if 'admin' not in data:
            data['admin'] = {'password': generate_password_hash(initial_admin_password()), 'role': 'admin'}
            changed = True
        for u in data.values():  # migrate old plaintext passwords
            if not _is_hashed(u.get('password')):
                u['password'] = generate_password_hash(u.get('password') or secrets.token_urlsafe(12))
                changed = True
        if changed:
            save_users(data)
        return data


def iter_servers(users):
    for uname, data in users.items():
        if uname == 'admin':
            continue
        servers = data.get('servers', [])
        if not isinstance(servers, list):
            continue
        for s in servers:
            if isinstance(s, dict):
                yield uname, s


def get_server_by_id(server_id):
    for uname, s in iter_servers(load_users()):
        if s.get('server_id') == server_id:
            return s, uname
    return None, None


def update_server(server_id, **fields):
    with USERS_LOCK:
        users = load_users()
        for _, s in iter_servers(users):
            if s.get('server_id') == server_id:
                s.update(fields)
                save_users(users)
                return s
    return None


def check_server_valid(server_id):
    s, _ = get_server_by_id(server_id)
    if not s:
        return False, 'deleted'
    expiry = s.get('expiry', '')
    if expiry:
        try:
            if datetime.now() > datetime.fromisoformat(expiry):
                return False, 'expired'
        except ValueError:
            pass
    return True, s


def ensure_admin():
    with USERS_LOCK:
        users = load_users()
        env_pw = os.environ.get('ADMIN_PASSWORD')
        if env_pw and not check_password_hash(users['admin']['password'], env_pw):
            users['admin']['password'] = generate_password_hash(env_pw)
            save_users(users)
        if check_password_hash(users['admin']['password'], 'admin123'):
            sys.exit('Refusing to start: admin password is still "admin123". Set ADMIN_PASSWORD and restart.')


# ============================================
# Auth helpers
# ============================================

def check_access(server_id):
    """Return None if the session may use this server, else an error response."""
    if not valid_id(server_id):
        return jsonify({'error': 'Not found'}), 404
    server, owner = get_server_by_id(server_id)
    if not server:
        return jsonify({'error': 'Not found'}), 404
    role = session.get('role')
    if role == 'admin':
        return None
    if role != 'user' or session.get('current_server_id') != server_id or session.get('user') != owner:
        return jsonify({'error': 'Unauthorized'}), 403
    ok, result = check_server_valid(server_id)
    if not ok:
        return jsonify({'error': result}), 403
    return None


def server_access(f):
    @wraps(f)
    def wrapper(server_id, *args, **kwargs):
        err = check_access(server_id)
        if err:
            return err
        return f(server_id, *args, **kwargs)
    return wrapper


def admin_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if session.get('role') != 'admin':
            return jsonify({'error': 'Unauthorized'}), 403
        return f(*args, **kwargs)
    return wrapper


@app.before_request
def origin_check():
    """Reject cross-site state-changing requests (CSRF defence in depth with SameSite=Lax)."""
    if request.method in ('POST', 'PUT', 'DELETE', 'PATCH'):
        origin = request.headers.get('Origin')
        if origin and urlparse(origin).netloc != request.host:
            return jsonify({'error': 'Bad origin'}), 403


def too_many_attempts():
    q = LOGIN_ATTEMPTS[request.remote_addr]
    now = time.time()
    while q and now - q[0] > 600:
        q.popleft()
    return len(q) >= 8


def record_failure():
    LOGIN_ATTEMPTS[request.remote_addr].append(time.time())


# ============================================
# Process management
# ============================================

def bot_env(server_dir):
    keep = ('PATH', 'SYSTEMROOT', 'TEMP', 'TMP', 'LANG', 'LC_ALL', 'VIRTUAL_ENV')
    env = {k: os.environ[k] for k in keep if k in os.environ}
    env.update({'HOME': server_dir, 'PYTHONIOENCODING': 'utf-8', 'PYTHONUNBUFFERED': '1'})
    return env  # panel secrets (SECRET_KEY, ADMIN_PASSWORD, API_KEY) are not passed on


def owns_pid(pid, server_id):
    """True only if `pid` is alive and was started from this server's directory."""
    if not pid:
        return False
    try:
        cmd = psutil.Process(pid).cmdline()
    except psutil.Error:
        return False
    prefix = os.path.join(BOTS_DIR, server_id) + os.sep
    return any(prefix in a for a in cmd)


def kill_tree(pid):
    try:
        parent = psutil.Process(pid)
        procs = parent.children(recursive=True) + [parent]
    except psutil.Error:
        return False
    for p in procs:
        try:
            p.terminate()
        except psutil.Error:
            pass
    _, alive = psutil.wait_procs(procs, timeout=3)
    for p in alive:
        try:
            p.kill()
        except psutil.Error:
            pass
    return True


def should_auto_restart(server_id):
    info = CRASH_COUNT.setdefault(server_id, {'count': 0, 'last_crash': time.time()})
    if time.time() - info['last_crash'] < 60:
        if info['count'] >= 3:
            return False
    else:
        info['count'] = 0
    info['count'] += 1
    info['last_crash'] = time.time()
    return True


def create_default_files(server_dir):
    main_py = os.path.join(server_dir, 'main.py')
    if not os.path.exists(main_py):
        with open(main_py, 'w', encoding='utf-8') as f:
            f.write('''# 𝘾𝙊𝙇𝙎 ✘ Karl Hosting - Default Bot
import time

print("=" * 40)
print("Bot is running on 𝘾𝙊𝙇𝙎 ✘ Karl Hosting")
print("Server is ready!")
print("=" * 40)

counter = 0
while True:
    counter += 1
    print(f"[{time.strftime('%H:%M:%S')}] Heartbeat #{counter} | Server active")
    time.sleep(10)
''')
    req_file = os.path.join(server_dir, 'requirements.txt')
    if not os.path.exists(req_file):
        with open(req_file, 'w', encoding='utf-8') as f:
            f.write('# Add your pip packages here\n')


def run_bot(server_id, main_file='main.py', requirements_file='requirements.txt'):
    server_dir = get_server_dir(server_id)
    log_file = os.path.join(server_dir, 'output.log')
    python_exe = sys.executable

    def log(msg):
        try:
            with open(log_file, 'a', encoding='utf-8') as f:
                f.write(f"{msg}\n")
        except OSError:
            pass

    try:
        main_path = safe_join(server_dir, main_file)
    except ValueError:
        return None, 'Invalid main file path!'
    if not os.path.isfile(main_path):
        return None, f"ERROR: {main_file} not found!"

    try:
        os.remove(log_file)
    except OSError:
        pass

    ts = lambda: datetime.now().strftime('%I:%M:%S %p')
    server, _ = get_server_by_id(server_id)
    cpu_limit = server.get('cpu_limit', 80) if server else 80
    log(f"[{ts()}] Rate limit: {cpu_limit}%")
    log("")
    env = bot_env(server_dir)
    popen_flags = {'creationflags': subprocess.CREATE_NO_WINDOW} if sys.platform == 'win32' else {}

    if requirements_file and requirements_file.strip():
        try:
            req_path = safe_join(server_dir, requirements_file.strip())
        except ValueError:
            return None, 'Invalid requirements file path!'
        log(f"[{ts()}] Run: pip install -r {requirements_file}")
        if os.path.isfile(req_path):
            with open(req_path, 'r', encoding='utf-8', errors='replace') as f:
                lines = [l.strip() for l in f if l.strip() and not l.strip().startswith('#')]
            if lines:
                try:
                    p = subprocess.Popen(
                        [python_exe, '-m', 'pip', 'install', '-r', req_path, '--disable-pip-version-check'],
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                        cwd=server_dir, env=env, **popen_flags)
                    for line in iter(p.stdout.readline, ''):
                        if line.strip():
                            log(f"[{ts()}] {line.rstrip()}")
                    p.wait()
                    log(f"[{ts()}] " + ("Requirements installation complete!" if p.returncode == 0
                                        else "Some packages failed to install"))
                except Exception as e:
                    log(f"[{ts()}] pip error: {e}")
            else:
                log(f"[{ts()}] {requirements_file} is empty, skipping...")
        else:
            log(f"[{ts()}] {requirements_file} not found, skipping...")
    else:
        log(f"[{ts()}] No requirements file set, skipping...")

    log("")
    log(f"[{ts()}] Run: python {main_file}")
    log(f"[{ts()}] Python {sys.version.split()[0]}")
    log("")

    try:
        proc = subprocess.Popen(
            [python_exe, main_path], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            cwd=server_dir, text=True, encoding='utf-8', errors='replace',
            bufsize=1, env=env, **popen_flags)
    except Exception as e:
        log(f"[{ts()}] Error: {e}")
        return None, str(e)

    log(f"[{ts()}] Server marked as running")
    log(f"[{ts()}] PID: {proc.pid}")
    log("")

    def rate_monitor():
        try:
            ps = psutil.Process(proc.pid)
        except psutil.Error:
            return
        samples = deque()
        while proc.poll() is None:
            time.sleep(4)
            try:
                cpu = ps.cpu_percent(interval=1)
                cpu += sum(c.cpu_percent(interval=None) for c in ps.children(recursive=True))
            except psutil.Error:
                break
            now = time.time()
            samples.append((now, cpu))
            while samples and now - samples[0][0] > 10:
                samples.popleft()
            avg = sum(c for _, c in samples) / len(samples)
            if len(samples) >= 2 and avg > cpu_limit:
                log(f"[{datetime.now().strftime('%I:%M:%S %p')}] CPU Limit! {avg:.1f}% > {cpu_limit}%")
                update_server(server_id, status='stopped', pid=None,
                              rate_limit_exceeded=True, stopped_by_user=False)
                kill_tree(proc.pid)
                break

    def stream_output():
        try:
            with open(log_file, 'a', encoding='utf-8') as f:
                for line in iter(proc.stdout.readline, ''):
                    line = line.rstrip('\n\r')
                    if line:
                        f.write(f"[{datetime.now().strftime('%I:%M:%S %p')}] {line}\n")
                        f.flush()
        except (OSError, ValueError):
            pass

    threading.Thread(target=rate_monitor, daemon=True).start()
    threading.Thread(target=stream_output, daemon=True).start()
    return proc.pid, None


def monitor_bot(server_id, pid):
    while owns_pid(pid, server_id):
        time.sleep(5)

    server, _ = get_server_by_id(server_id)
    if not server or server.get('status') != 'running' or server.get('pid') != pid:
        return  # stopped/replaced by someone else
    if server.get('stopped_by_user') or server.get('rate_limit_exceeded'):
        return
    ok, _ = check_server_valid(server_id)
    if not ok:
        update_server(server_id, status='stopped', pid=None)
        return

    if should_auto_restart(server_id):
        time.sleep(3)
        new_pid, _err = run_bot(server_id, server.get('main_file', 'main.py'),
                                server.get('requirements_file', 'requirements.txt'))
        if new_pid:
            update_server(server_id, status='running', pid=new_pid, started_at=str(datetime.now()),
                          rate_limit_exceeded=False, stopped_by_user=False)
            threading.Thread(target=monitor_bot, args=(server_id, new_pid), daemon=True).start()
            return
    update_server(server_id, status='stopped', pid=None)


def get_process_stats(pid):
    try:
        proc = psutil.Process(pid)
        cpu = proc.cpu_percent(interval=0.5)
        ram = proc.memory_info().rss / (1024 * 1024)
        return {'cpu_percent': round(cpu, 1),
                'ram_display': f"{ram:.1f} MB" if ram < 1024 else f"{ram / 1024:.1f} GB"}
    except psutil.Error:
        return {'cpu_percent': 0, 'ram_display': '0 MB'}


def format_bytes(kb):
    if kb < 1024:
        return f"{kb:.1f} KB"
    mb = kb / 1024
    return f"{mb:.1f} MB" if mb < 1024 else f"{mb / 1024:.2f} GB"


def get_network_stats(pid):
    try:
        io = psutil.Process(pid).io_counters()
        return format_bytes(io.read_bytes / 1024), format_bytes(io.write_bytes / 1024)
    except (psutil.Error, AttributeError):
        return "0 KB", "0 KB"


def housekeeping():
    """Stop bots whose subscription has expired."""
    while True:
        time.sleep(60)
        try:
            for _, s in list(iter_servers(load_users())):
                sid = s.get('server_id')
                if s.get('status') == 'running' and not check_server_valid(sid)[0]:
                    update_server(sid, status='stopped', stopped_by_user=True)
                    if owns_pid(s.get('pid'), sid):
                        kill_tree(s['pid'])
                    update_server(sid, pid=None)
        except Exception as e:  # keep the loop alive
            print(f"[housekeeping] {e}")


def reconcile_on_startup():
    """Bot pipes die with the panel, so anything marked running is no longer managed."""
    for _, s in list(iter_servers(load_users())):
        if s.get('status') == 'running':
            sid = s.get('server_id')
            if owns_pid(s.get('pid'), sid):
                kill_tree(s['pid'])
            update_server(sid, status='stopped', pid=None)


# ============================================
# Public API - create server (API key required)
# ============================================

@app.route('/api/create', methods=['GET', 'POST'])
def api_create_server():
    if not API_KEY:
        return jsonify({'status': 'error', 'message': 'API disabled: set the API_KEY environment variable.'}), 503
    params = request.get_json(silent=True) or request.values
    supplied = request.headers.get('X-API-Key') or params.get('key', '')
    if not secrets.compare_digest(str(supplied), API_KEY):
        return jsonify({'status': 'error', 'message': 'Invalid API key'}), 401

    username = str(params.get('username', '')).strip() or f"user{secrets.randbelow(900000) + 100000}"
    password = str(params.get('password', '')).strip() or generate_random_password()
    server_type = str(params.get('type', 'python')).strip().lower()
    ram = str(params.get('ram', '1GB')).strip()
    disk = str(params.get('disk', '1GB')).strip()
    cpu_limit = to_int(params.get('cpu', 30), None)
    days = to_int(params.get('days', 3), None)

    def err(msg):
        return jsonify({'status': 'error', 'message': msg}), 400

    if not USERNAME_RE.match(username) or username.lower() == 'admin':
        return err('Username must be 3-32 chars (letters, digits, _ . -) and not "admin".')
    if len(password) < 6:
        return err('Password must be at least 6 characters!')
    if not TYPE_RE.match(server_type) or not RES_RE.match(ram) or not RES_RE.match(disk):
        return err('Invalid type, ram or disk value!')
    if cpu_limit is None or not 10 <= cpu_limit <= 100:
        return err('CPU limit must be a number between 10 and 100!')
    if days is None or not 1 <= days <= 365:
        return err('Days must be a number between 1 and 365!')

    server_id = secrets.token_hex(6)
    expiry_date = datetime.now() + timedelta(days=days)
    host = request.host
    is_local = host.startswith(('localhost', '127.0.0.1', '192.168'))
    full_url = f"{'http' if is_local else 'https'}://{host}/{server_id}/login"

    with USERS_LOCK:
        users = load_users()
        if username in users:
            return err(f"Username '{username}' already exists!")
        create_default_files(get_server_dir(server_id))
        users[username] = {
            'password': generate_password_hash(password), 'role': 'user',
            'servers': [{
                'server_id': server_id, 'login_url': f"/{server_id}/login",
                'dashboard_url': f"/{server_id}/home", 'full_link': full_url,
                'type': server_type, 'ram': ram, 'disk': disk,
                'status': 'stopped', 'pid': None,
                'created': str(datetime.now()), 'expiry': str(expiry_date),
                'main_file': 'main.py', 'requirements_file': 'requirements.txt',
                'cpu_limit': cpu_limit, 'rate_limit_exceeded': False, 'stopped_by_user': False,
            }],
        }
        save_users(users)

    return jsonify({
        'status': 'success', 'message': 'Panel created successfully!',
        'username': username, 'password': password, 'server_type': server_type,
        'ram': ram, 'disk': disk, 'cpu_limit': cpu_limit, 'validity': f'{days} days',
        'expiry_date': expiry_date.strftime('%Y-%m-%d'), 'full_url': full_url, 'server_id': server_id,
    }), 200


# ============================================
# Pages / auth
# ============================================

@app.route('/')
@app.route('/landing')
def index():
    return render_template('landing.html')


@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        if too_many_attempts():
            return render_template('login.html', error="Too many attempts. Try again later."), 429
        username = request.form.get('username', '')
        password = request.form.get('password', '')
        admin = load_users().get('admin', {})
        if username == 'admin' and check_password_hash(admin.get('password', ''), password):
            session.clear()
            session.permanent = True
            session['user'] = 'admin'
            session['role'] = 'admin'
            LOGIN_ATTEMPTS.pop(request.remote_addr, None)
            return redirect(url_for('admin_dashboard'))
        record_failure()
        return render_template('login.html', error="Invalid credentials!")
    return render_template('login.html', error=None)


@app.route('/<server_id>/login', methods=['GET', 'POST'])
def server_login(server_id):
    if not valid_id(server_id):
        return render_template('error.html', error_type='deleted', server_link=''), 404
    valid, result = check_server_valid(server_id)
    if not valid:
        return render_template('error.html', error_type=result or 'deleted', server_link=server_id)

    if request.method == 'POST':
        if too_many_attempts():
            return render_template('login.html', error="Too many attempts. Try again later."), 429
        username = request.form.get('username', '')
        password = request.form.get('password', '')
        server, owner = get_server_by_id(server_id)
        user = load_users().get(owner, {})
        if server and username == owner and check_password_hash(user.get('password', ''), password):
            session.clear()
            session.permanent = True
            session['user'] = owner
            session['role'] = 'user'
            session['current_server_id'] = server_id
            LOGIN_ATTEMPTS.pop(request.remote_addr, None)
            return redirect(url_for('server_home', server_id=server_id))
        record_failure()
        return render_template('login.html', error="Invalid credentials!")
    return render_template('login.html', error=None)


@app.route('/<server_id>/home')
def server_home(server_id):
    if not valid_id(server_id):
        return render_template('error.html', error_type='deleted', server_link=''), 404
    if session.get('role') != 'user':
        return redirect(url_for('server_login', server_id=server_id))
    if session.get('current_server_id') != server_id:
        session.clear()
        return redirect(url_for('server_login', server_id=server_id))
    valid, result = check_server_valid(server_id)
    if not valid:
        session.clear()
        return render_template('error.html', error_type=result or 'deleted', server_link=server_id)
    return render_template('home.html', username=session['user'], current_server=result)


@app.route('/logout')
def logout():
    server_id = session.get('current_server_id')
    session.clear()
    if server_id:
        return redirect(url_for('server_login', server_id=server_id))
    return redirect(url_for('login'))


# ============================================
# Admin
# ============================================

@app.route('/admin')
def admin_dashboard():
    if session.get('role') != 'admin':
        return redirect(url_for('login'))
    users = load_users()
    user_list, total_servers, total_running = [], 0, 0
    for uname, data in users.items():
        if uname == 'admin':
            continue
        servers = [s for s in data.get('servers', []) if isinstance(s, dict)]
        running = sum(1 for s in servers if s.get('status') == 'running')
        total_servers += len(servers)
        total_running += running
        user_list.append({'username': uname, 'password': '(hashed - use reset)', 'servers': servers,
                          'server_count': len(servers), 'running_count': running})
    return render_template('admin.html', users=user_list, total_servers=total_servers,
                           total_running=total_running)


@app.route('/admin/create_server', methods=['POST'])
@admin_required
def create_server():
    data = request.get_json(silent=True) or {}
    username = str(data.get('username', '')).strip()
    password = str(data.get('password', ''))
    server_type = str(data.get('server_type', 'python')).strip().lower()
    ram = str(data.get('ram', '512MB')).strip()
    disk = str(data.get('disk', '1GB')).strip()
    expiry_days = to_int(data.get('expiry_days', 30), None)
    cpu_limit = to_int(data.get('cpu_limit', 80), None)

    if not username or not password:
        return jsonify({'error': 'Required!'}), 400
    if not USERNAME_RE.match(username) or username.lower() == 'admin':
        return jsonify({'error': 'Invalid username!'}), 400
    if not TYPE_RE.match(server_type) or not RES_RE.match(ram) or not RES_RE.match(disk):
        return jsonify({'error': 'Invalid type, ram or disk!'}), 400
    if expiry_days is None or not 1 <= expiry_days <= 3650 or cpu_limit is None or not 10 <= cpu_limit <= 100:
        return jsonify({'error': 'Invalid expiry or CPU limit!'}), 400

    server_id = secrets.token_hex(6)
    new_server = {
        'server_id': server_id, 'link': server_id,
        'login_url': f"/{server_id}/login", 'dashboard_url': f"/{server_id}/home",
        'full_link': request.host_url.rstrip('/') + f"/{server_id}/home",
        'type': server_type, 'ram': ram, 'disk': disk, 'status': 'stopped', 'pid': None,
        'created': str(datetime.now()), 'expiry': str(datetime.now() + timedelta(days=expiry_days)),
        'main_file': 'main.py', 'requirements_file': 'requirements.txt',
        'cpu_limit': cpu_limit, 'rate_limit_exceeded': False, 'stopped_by_user': False,
    }
    with USERS_LOCK:
        users = load_users()
        create_default_files(get_server_dir(server_id))
        if username not in users:
            users[username] = {'password': generate_password_hash(password), 'role': 'user', 'servers': []}
        users[username].setdefault('servers', []).append(new_server)
        save_users(users)

    return jsonify({'success': True, 'username': username, 'password': password,
                    'login_url': new_server['login_url'], 'hostname': new_server['full_link'],
                    'server_id': server_id})


@app.route('/admin/set_rate_limit/<server_id>', methods=['POST'])
@admin_required
def set_rate_limit(server_id):
    cpu_limit = to_int((request.get_json(silent=True) or {}).get('cpu_limit', 80), None)
    if cpu_limit is None or not 10 <= cpu_limit <= 100:
        return jsonify({'error': 'CPU limit must be 10-100'}), 400
    if valid_id(server_id) and update_server(server_id, cpu_limit=cpu_limit):
        return jsonify({'success': True, 'cpu_limit': cpu_limit})
    return jsonify({'error': 'Not found'}), 404


@app.route('/admin/reset_password/<username>', methods=['POST'])
@admin_required
def reset_password(username):
    with USERS_LOCK:
        users = load_users()
        if username == 'admin' or username not in users:
            return jsonify({'error': 'Not found'}), 404
        new_pw = generate_random_password()
        users[username]['password'] = generate_password_hash(new_pw)
        save_users(users)
    return jsonify({'success': True, 'password': new_pw})


@app.route('/admin/delete_server/<username>/<server_id>', methods=['POST'])
@admin_required
def delete_server(username, server_id):
    if not valid_id(server_id):
        return jsonify({'error': 'Not found'}), 404
    with USERS_LOCK:
        users = load_users()
        if username in users and username != 'admin':
            servers = [s for s in users[username].get('servers', []) if isinstance(s, dict)]
            for s in servers:
                if s.get('server_id') == server_id:
                    if owns_pid(s.get('pid'), server_id):
                        kill_tree(s['pid'])
                    shutil.rmtree(os.path.join(BOTS_DIR, server_id), ignore_errors=True)
            users[username]['servers'] = [s for s in servers if s.get('server_id') != server_id]
            if not users[username]['servers']:
                del users[username]
            save_users(users)
    return jsonify({'success': True})


# ============================================
# Bot control API (all require access to the server)
# ============================================

@app.route('/api/run/<server_id>', methods=['POST'])
@server_access
def api_run(server_id):
    with START_LOCK:
        server, _ = get_server_by_id(server_id)
        if server.get('status') == 'running' and owns_pid(server.get('pid'), server_id):
            return jsonify({'status': 'error', 'msg': 'Already running!'})
        ok, result = check_server_valid(server_id)
        if not ok:
            return jsonify({'status': 'error', 'msg': f'Server {result}'})
        pid, error = run_bot(server_id, server.get('main_file', 'main.py'),
                             server.get('requirements_file', 'requirements.txt'))
        if not pid:
            return jsonify({'status': 'error', 'msg': error or 'Failed'})
        update_server(server_id, status='running', pid=pid, started_at=str(datetime.now()),
                      rate_limit_exceeded=False, stopped_by_user=False)
    threading.Thread(target=monitor_bot, args=(server_id, pid), daemon=True).start()
    return jsonify({'status': 'success', 'msg': 'Started!'})


@app.route('/api/stop/<server_id>', methods=['POST'])
@server_access
def api_stop(server_id):
    server, _ = get_server_by_id(server_id)
    update_server(server_id, status='stopped', stopped_by_user=True)
    if owns_pid(server.get('pid'), server_id):
        kill_tree(server['pid'])
    update_server(server_id, pid=None)
    try:
        with open(os.path.join(get_server_dir(server_id), 'output.log'), 'a', encoding='utf-8') as f:
            f.write(f"\n[{datetime.now().strftime('%I:%M:%S %p')}] Server stopped by user\n")
    except OSError:
        pass
    return jsonify({'status': 'success', 'msg': 'Stopped'})


@app.route('/api/logs/<server_id>')
@server_access
def api_logs(server_id):
    log_file = os.path.join(get_server_dir(server_id), 'output.log')
    logs = ''
    if os.path.exists(log_file):
        with open(log_file, 'r', encoding='utf-8', errors='replace') as f:
            logs = f.read()
    return jsonify({'logs': logs})


@app.route('/api/clear_logs/<server_id>', methods=['POST'])
@server_access
def api_clear_logs(server_id):
    try:
        open(os.path.join(get_server_dir(server_id), 'output.log'), 'w').close()
        return jsonify({'status': 'success', 'msg': 'Cleared'})
    except OSError:
        return jsonify({'status': 'error'}), 500


ALLOWED_CMDS = {'ls', 'pwd', 'cat', 'echo', 'pip', 'pip3', 'python', 'python3'}


@app.route('/api/command', methods=['POST'])
def api_command():
    """Limited terminal: allow-listed programs only, no shell, confined paths."""
    data = request.get_json(silent=True) or {}
    server_id = str(data.get('server_id', ''))
    err = check_access(server_id)
    if err:
        return err
    if not TERMINAL_ENABLED:
        return jsonify({'status': 'error', 'msg': 'Terminal is disabled'}), 403
    try:
        argv = shlex.split(str(data.get('cmd', '')))
    except ValueError:
        return jsonify({'status': 'error', 'msg': 'Could not parse command'}), 400
    if not argv or argv[0] not in ALLOWED_CMDS:
        return jsonify({'status': 'error', 'msg': 'Allowed: ' + ', '.join(sorted(ALLOWED_CMDS))}), 400

    server_dir = get_server_dir(server_id)
    exe = argv[0]
    if exe in ('pip', 'pip3'):
        argv = [sys.executable, '-m', 'pip'] + argv[1:]
    elif exe in ('python', 'python3'):
        argv = [sys.executable] + argv[1:]
    elif exe in ('ls', 'cat'):
        for a in argv[1:]:
            if a.startswith('-'):
                continue
            try:
                safe_join(server_dir, a, allow_root=True)
            except ValueError:
                return jsonify({'status': 'error', 'msg': 'Path not allowed'}), 400

    log_file = os.path.join(server_dir, 'output.log')
    try:
        result = subprocess.run(argv, shell=False, capture_output=True, text=True, cwd=server_dir,
                                timeout=30, env=bot_env(server_dir), errors='replace')
        output = (result.stdout + result.stderr)[:2000]
    except subprocess.TimeoutExpired:
        return jsonify({'status': 'error', 'msg': 'Timeout'})
    except OSError as e:
        return jsonify({'status': 'error', 'msg': str(e)})
    with open(log_file, 'a', encoding='utf-8') as f:
        f.write(f"[{datetime.now().strftime('%I:%M:%S %p')}] $ {data.get('cmd', '')}\n{output}\n")
    return jsonify({'status': 'success', 'output': output})


@app.route('/api/stats/<server_id>')
@server_access
def api_stats(server_id):
    server, _ = get_server_by_id(server_id)
    uptime, cpu, ram, net_in, net_out = "0h 0m", "0%", "0 MB", "0 KB", "0 KB"
    running = server.get('status') == 'running' and owns_pid(server.get('pid'), server_id)
    if running:
        stats = get_process_stats(server['pid'])
        cpu, ram = f"{stats['cpu_percent']}%", stats['ram_display']
        net_in, net_out = get_network_stats(server['pid'])
        try:
            diff = datetime.now() - datetime.fromisoformat(server['started_at'])
            if diff.days > 0:
                uptime = f"{diff.days}d {diff.seconds // 3600}h"
            else:
                uptime = f"{diff.seconds // 3600}h {(diff.seconds % 3600) // 60}m {diff.seconds % 60}s"
        except (KeyError, ValueError):
            pass
    return jsonify({'cpu': cpu, 'ram': ram, 'uptime': uptime, 'net_in': net_in, 'net_out': net_out,
                    'cpu_limit': server.get('cpu_limit', 80),
                    'status': 'running' if running else 'stopped'})


@app.route('/api/change_password/<server_id>', methods=['POST'])
@server_access
def api_change_password(server_id):
    data = request.get_json(silent=True) or {}
    current_password = data.get('current_password', '')
    new_password = data.get('new_password', '')
    if not current_password or not new_password:
        return jsonify({'error': 'All fields are required!'})
    if len(new_password) < 6:
        return jsonify({'error': 'Password must be at least 6 characters!'})
    if session.get('role') == 'admin':
        return jsonify({'error': 'Use the admin login to manage the admin password.'}), 400
    with USERS_LOCK:
        users = load_users()
        username = session.get('user')
        if username not in users:
            return jsonify({'error': 'User not found!'}), 404
        if not check_password_hash(users[username].get('password', ''), current_password):
            return jsonify({'error': 'Current password is incorrect!'})
        users[username]['password'] = generate_password_hash(new_password)
        save_users(users)
    return jsonify({'success': True, 'msg': 'Password changed!'})


# ============================================
# GitHub deploy (no git needed)
# ============================================

def parse_github_url(url):
    m = re.match(r'^https?://(?:www\.)?github\.com/([^/\s?#]+)/([^/\s?#]+?)(?:\.git)?(?:/tree/([^\s?#]+?))?/?$',
                 url.strip())
    if not m:
        return None
    owner, repo, branch = m.groups()
    if not GH_NAME_RE.match(owner) or not GH_NAME_RE.match(repo):
        return None
    if branch and (not GH_BRANCH_RE.match(branch) or '..' in branch):
        return None
    return owner, repo, branch


@app.route('/api/github/deploy/<server_id>', methods=['POST'])
@server_access
def api_github_deploy(server_id):
    data = request.get_json(silent=True) or {}
    repo_url = str(data.get('repo_url', '')).strip()
    access_token = str(data.get('access_token', '')).strip()
    if not repo_url:
        return jsonify({'status': 'error', 'msg': 'Repository URL is required!'}), 400
    parsed = parse_github_url(repo_url)
    if not parsed:
        return jsonify({'status': 'error', 'msg': 'Invalid GitHub repository URL!'}), 400
    owner, repo, branch = parsed

    server_dir = get_server_dir(server_id)
    log_file = os.path.join(server_dir, 'github_deploy.log')

    def deploy_log(msg):
        try:
            with open(log_file, 'a', encoding='utf-8') as f:
                f.write(f"[{datetime.now().strftime('%I:%M:%S %p')}] {msg}\n")
        except OSError:
            pass

    open(log_file, 'w').close()
    deploy_log("Starting GitHub deployment...")
    deploy_log(f"Repository: {owner}/{repo}" + (f" (branch {branch})" if branch else " (default branch)"))

    def deploy_thread():
        import requests
        temp_zip = os.path.join(server_dir, '_github_temp.zip')
        try:
            api_url = f"https://api.github.com/repos/{owner}/{repo}/zipball" + (f"/{branch}" if branch else "")
            headers = {'Accept': 'application/vnd.github+json'}
            if access_token:
                headers['Authorization'] = f'Bearer {access_token}'
                deploy_log("Using access token for authentication")
            deploy_log("Downloading ZIP archive...")
            r = requests.get(api_url, headers=headers, stream=True, timeout=60)
            if r.status_code != 200:
                msgs = {404: 'Repository not found (or private - provide a token)',
                        401: 'Authentication failed - check your token',
                        403: 'Rate limit exceeded or access denied'}
                deploy_log(f"❌ Error: {msgs.get(r.status_code, f'HTTP {r.status_code}')}")
                return
            size = 0
            with open(temp_zip, 'wb') as f:
                for chunk in r.iter_content(chunk_size=8192):
                    size += len(chunk)
                    if size > MAX_DOWNLOAD_BYTES:
                        deploy_log("❌ Error: Repository archive is too large")
                        return
                    f.write(chunk)
            deploy_log("✓ Downloaded. Extracting files...")
            with zipfile.ZipFile(temp_zip) as zf:
                safe_extract(zf, server_dir, strip_root=True, log=deploy_log)
            deploy_log("")
            deploy_log("✅ Deployment completed successfully!")
        except requests.exceptions.Timeout:
            deploy_log("❌ Error: Connection timeout!")
        except Exception as e:
            deploy_log(f"❌ Error: {e}")
        finally:
            try:
                os.remove(temp_zip)
            except OSError:
                pass

    threading.Thread(target=deploy_thread, daemon=True).start()
    return jsonify({'status': 'success', 'msg': 'Deployment started! Check terminal for progress.'})


@app.route('/api/github/logs/<server_id>')
@server_access
def api_github_logs(server_id):
    log_file = os.path.join(get_server_dir(server_id), 'github_deploy.log')
    logs = "> Ready for deployment..."
    if os.path.exists(log_file):
        with open(log_file, 'r', encoding='utf-8', errors='replace') as f:
            logs = f.read()
    return jsonify({'logs': logs})


@app.route('/api/github/clear_logs/<server_id>', methods=['POST'])
@server_access
def api_github_clear_logs(server_id):
    try:
        os.remove(os.path.join(get_server_dir(server_id), 'github_deploy.log'))
    except FileNotFoundError:
        pass
    except OSError:
        return jsonify({'status': 'error'}), 500
    return jsonify({'status': 'success'})


# ============================================
# File API
# ============================================

def _path_error():
    return jsonify({'error': 'Invalid path'}), 400


@app.route('/api/files/<server_id>')
@server_access
def api_files(server_id):
    base = get_server_dir(server_id)
    try:
        target = safe_join(base, request.args.get('folder', ''), allow_root=True)
    except ValueError:
        return jsonify({'files': []})
    files = []
    if os.path.isdir(target):
        for item in os.listdir(target):
            p = os.path.join(target, item)
            try:
                files.append({'name': item, 'is_dir': os.path.isdir(p),
                              'size': os.path.getsize(p) if os.path.isfile(p) else 0,
                              'modified': datetime.fromtimestamp(os.path.getmtime(p)).strftime('%Y-%m-%d %H:%M')})
            except OSError:
                pass
    return jsonify({'files': files})


@app.route('/api/file/<server_id>', methods=['GET'])
@server_access
def api_get_file(server_id):
    try:
        path = safe_join(get_server_dir(server_id), request.args.get('filename', ''))
    except ValueError:
        return _path_error()
    if not os.path.isfile(path):
        return jsonify({'error': 'Not found'}), 404
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return jsonify({'content': f.read()})
    except UnicodeDecodeError:
        return jsonify({'error': 'Binary file cannot be edited'}), 415


@app.route('/api/file/<server_id>', methods=['POST'])
@server_access
def api_save_file(server_id):
    data = request.get_json(silent=True) or {}
    try:
        path = safe_join(get_server_dir(server_id), str(data.get('filename', '')))
    except ValueError:
        return _path_error()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write(str(data.get('content', '')))
    return jsonify({'success': True})


@app.route('/api/file/<server_id>', methods=['DELETE'])
@server_access
def api_delete_file(server_id):
    data = request.get_json(silent=True) or {}
    try:
        path = safe_join(get_server_dir(server_id), str(data.get('filename', '')))
    except ValueError:
        return _path_error()
    if os.path.isdir(path):
        shutil.rmtree(path)
    elif os.path.exists(path):
        os.remove(path)
    return jsonify({'success': True})


@app.route('/api/upload/<server_id>', methods=['POST'])
@server_access
def api_upload(server_id):
    if 'file' not in request.files:
        return jsonify({'error': 'No file'}), 400
    base = get_server_dir(server_id)
    try:
        folder = safe_join(base, request.form.get('folder', ''), allow_root=True)
    except ValueError:
        return _path_error()
    f = request.files['file']
    name = secure_filename(f.filename or '')
    if not name:
        return jsonify({'error': 'Invalid file name'}), 400
    os.makedirs(folder, exist_ok=True)
    f.save(os.path.join(folder, name))
    return jsonify({'success': True})


@app.route('/api/create_folder/<server_id>', methods=['POST'])
@server_access
def api_create_folder(server_id):
    data = request.get_json(silent=True) or {}
    try:
        path = safe_join(get_server_dir(server_id), str(data.get('foldername', '')))
    except ValueError:
        return _path_error()
    os.makedirs(path, exist_ok=True)
    return jsonify({'success': True})


@app.route('/api/rename/<server_id>', methods=['POST'])
@server_access
def api_rename(server_id):
    d = request.get_json(silent=True) or {}
    base = get_server_dir(server_id)
    try:
        old_path = safe_join(base, str(d.get('old_name', '')))
        new_path = safe_join(base, str(d.get('new_name', '')))
    except ValueError:
        return _path_error()
    if not os.path.exists(old_path):
        return jsonify({'error': 'Not found'}), 404
    os.makedirs(os.path.dirname(new_path), exist_ok=True)
    os.rename(old_path, new_path)
    return jsonify({'success': True})


@app.route('/api/unzip/<server_id>', methods=['POST'])
@server_access
def api_unzip(server_id):
    data = request.get_json(silent=True) or {}
    try:
        zip_path = safe_join(get_server_dir(server_id), str(data.get('filename', '')))
    except ValueError:
        return _path_error()
    if not (zip_path.lower().endswith('.zip') and os.path.isfile(zip_path)):
        return jsonify({'status': 'error', 'msg': 'Invalid zip'}), 400
    try:
        with zipfile.ZipFile(zip_path) as zf:
            safe_extract(zf, os.path.dirname(zip_path))
        return jsonify({'status': 'success', 'msg': 'Extracted!'})
    except (zipfile.BadZipFile, ValueError) as e:
        return jsonify({'status': 'error', 'msg': str(e)}), 400


@app.route('/api/get_startup/<server_id>')
@server_access
def api_get_startup(server_id):
    server, _ = get_server_by_id(server_id)
    return jsonify({'main_file': server.get('main_file', 'main.py'),
                    'requirements_file': server.get('requirements_file', 'requirements.txt')})


@app.route('/api/set_startup/<server_id>', methods=['POST'])
@server_access
def api_set_startup(server_id):
    d = request.get_json(silent=True) or {}
    main_file = str(d.get('main_file') or 'main.py').strip()
    req_file = str(d.get('requirements_file') or '').strip()
    base = get_server_dir(server_id)
    try:
        safe_join(base, main_file)
        if req_file:
            safe_join(base, req_file)
    except ValueError:
        return _path_error()
    update_server(server_id, main_file=main_file, requirements_file=req_file)
    return jsonify({'success': True})


# ============================================
# Start
# ============================================

ensure_admin()
reconcile_on_startup()
threading.Thread(target=housekeeping, daemon=True).start()

if __name__ == '__main__':
    host = os.environ.get('HOST', '0.0.0.0')
    port = to_int(os.environ.get('PORT', 5000), 5000)
    print(f"\n𝘾𝙊𝙇𝙎 ✘ Karl Hosting running on http://{host}:{port}  (admin login: /login)")
    if not API_KEY:
        print("Note: /api/create is disabled until API_KEY is set.")
    app.run(debug=os.environ.get('FLASK_DEBUG') == '1', host=host, port=port, use_reloader=False)
