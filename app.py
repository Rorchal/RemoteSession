# -*- coding: utf-8 -*-
"""
模拟会话 —— 基于 md 文件的问答系统（只依赖 Python 标准库）

流程：
  1. 用户用账号密码登录；管理员可以新建 / 修改 / 禁用 / 删除用户，并给每个用户配置 md 目录
  2. 用户每提一个问题，就在他的 md 目录里生成一个自增编号的文件：1.md、2.md、3.md ...
         问题：<问题内容>

         回答：

  3. 回答方（人工或其他程序）在 “回答：” 下面写回答，写完后加上 “回答完毕”
  4. 后台线程监听待回答 md 所在的目录（Windows 下用目录变化通知，其他系统每秒轮询），一旦出现 “回答完毕”，
     就把 “回答：” 和 “回答完毕” 之间的内容立即返回给正在等待的这个用户

运行：python app.py
      默认地址 http://127.0.0.1:8000，首次启动自动创建管理员 admin / admin123
"""
import argparse
import hashlib
import hmac
import json
import os
import re
import secrets
import sqlite3
import threading
import time
import traceback
from contextlib import contextmanager
from datetime import datetime
from http.cookies import CookieError, SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
STATIC_DIR = os.path.join(BASE_DIR, "static")

# 可通过命令行参数覆盖，见 main()
CONFIG = {
    "db_path": os.path.join(BASE_DIR, "data", "app.db"),
    "default_md_dir": r"C:\Users\23695\Documents\longlingl",
}

DONE_MARK = "回答完毕"
POLL_INTERVAL = 1.0          # 系统不支持目录变化通知时，轮询 md 的间隔（秒）
RESCAN_INTERVAL = 5.0        # 有目录变化通知时的兜底复查间隔（秒），防止漏掉通知
SETTLE_SECONDS = 0.5         # md 最后一次修改后至少静止这么久才读取，避免读到写了一半的文件
SESSION_TTL = 7 * 24 * 3600  # 登录有效期（秒）
MAX_WAIT = 60                # 接口长轮询最长等待（秒）
MAX_QUESTION_LEN = 20000
MAX_BODY = 1 << 20
PBKDF2_ITER = 200_000
USERNAME_RE = re.compile(r"^[\w.@-]{2,32}$")


def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def log(msg):
    print(f"[{now_str()}] {msg}", flush=True)


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


# ---------------------------------------------------------------- 数据库

SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
    id             INTEGER PRIMARY KEY AUTOINCREMENT,
    username       TEXT    NOT NULL UNIQUE COLLATE NOCASE,
    password_hash  TEXT    NOT NULL,
    role           TEXT    NOT NULL DEFAULT 'user',   -- admin / user
    md_dir         TEXT    NOT NULL,                  -- 该用户问题 md 的保存目录
    enabled        INTEGER NOT NULL DEFAULT 1,
    must_change_pw INTEGER NOT NULL DEFAULT 0,
    created_at     TEXT    NOT NULL
);
CREATE TABLE IF NOT EXISTS sessions (
    token_hash TEXT    PRIMARY KEY,
    user_id    INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    expires_at REAL    NOT NULL
);
CREATE TABLE IF NOT EXISTS questions (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id     INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    md_no       INTEGER NOT NULL,
    md_path     TEXT    NOT NULL,
    question    TEXT    NOT NULL,
    answer      TEXT,
    status      TEXT    NOT NULL DEFAULT 'pending',   -- pending / answered / cancelled
    created_at  TEXT    NOT NULL,
    answered_at TEXT
);
CREATE INDEX IF NOT EXISTS idx_questions_user   ON questions(user_id, id);
CREATE INDEX IF NOT EXISTS idx_questions_status ON questions(status);
"""


@contextmanager
def db():
    conn = sqlite3.connect(CONFIG["db_path"], timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    try:
        yield conn
        conn.commit()
    finally:
        conn.close()


def init_db(admin_password):
    os.makedirs(os.path.dirname(CONFIG["db_path"]), exist_ok=True)
    with db() as c:
        c.executescript(SCHEMA)
        c.execute("PRAGMA journal_mode = WAL")
        if c.execute("SELECT COUNT(*) FROM users").fetchone()[0] == 0:
            c.execute(
                "INSERT INTO users(username, password_hash, role, md_dir, must_change_pw, created_at) "
                "VALUES('admin', ?, 'admin', ?, 1, ?)",
                (hash_password(admin_password), CONFIG["default_md_dir"], now_str()),
            )
            log(f"已创建管理员账号 admin，初始密码：{admin_password}（首次登录后会要求修改）")


def hash_password(password):
    salt = secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, PBKDF2_ITER)
    return f"pbkdf2_sha256${PBKDF2_ITER}${salt.hex()}${dk.hex()}"


def verify_password(password, stored):
    try:
        _, iterations, salt, digest = stored.split("$")
        dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(salt), int(iterations))
        return hmac.compare_digest(dk.hex(), digest)
    except (ValueError, TypeError):
        return False


def token_hash(token):
    return hashlib.sha256(token.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------- md 文件

MD_NAME_RE = re.compile(r"^(\d+)\.md$", re.IGNORECASE)
_dir_locks = {}
_dir_locks_guard = threading.Lock()


def _dir_lock(path):
    key = os.path.normcase(os.path.abspath(path))
    with _dir_locks_guard:
        return _dir_locks.setdefault(key, threading.Lock())


def write_question_md(md_dir, question):
    """在 md_dir 下生成下一个编号的 md，返回 (编号, 路径)。编号 = 目录里现有 N.md 的最大 N + 1"""
    os.makedirs(md_dir, exist_ok=True)
    content = f"问题：{question}\n\n回答：\n\n"
    with _dir_lock(md_dir):
        numbers = [int(m.group(1)) for name in os.listdir(md_dir) if (m := MD_NAME_RE.match(name))]
        no = max(numbers, default=0) + 1
        while True:
            path = os.path.join(md_dir, f"{no}.md")
            try:
                # "x" 模式：文件已存在就报错，防止覆盖别人刚建的同名文件
                with open(path, "x", encoding="utf-8") as f:
                    f.write(content)
                return no, path
            except FileExistsError:
                no += 1


def read_md(path):
    with open(path, "rb") as f:
        raw = f.read()
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError:
        text = raw.decode("gb18030", errors="replace")
    return text.replace("\r\n", "\n").replace("\r", "\n")


ANSWER_HEAD_RE = re.compile(r"^[ \t>#*]*回答[ \t]*[：:]", re.MULTILINE)
HR_TAIL_RE = re.compile(r"\n[ \t]*([-*_=])[ \t]*(?:\1[ \t]*){2,}$")
DONE_LINE_DECOR = " \t*_#>【[（(「『<—-=~：:"


def extract_answer(text, question):
    """取出 “回答：” 和最后一个 “回答完毕” 之间的内容；还没出现 “回答完毕” 时返回 None"""
    # 从问题正文之后开始找，避免问题里本身含有 “回答：”/“回答完毕” 造成误判
    anchor = 0
    q = question.strip()
    if q:
        pos = text.find(q)
        if pos >= 0:
            anchor = pos + len(q)
    head = ANSWER_HEAD_RE.search(text, anchor) or ANSWER_HEAD_RE.search(text)
    start = head.end() if head else anchor
    end = text.rfind(DONE_MARK, start)
    if end < 0:
        return None

    body = text[start:end]
    # “回答完毕” 所在行前面的装饰去掉，例如 **回答完毕**、【回答完毕】
    line_start = body.rfind("\n") + 1
    body = body[:line_start] + body[line_start:].rstrip(DONE_LINE_DECOR)
    body = body.rstrip()
    # 去掉结尾的分隔线 --- / *** / ===
    while True:
        trimmed = HR_TAIL_RE.sub("", body).rstrip()
        if trimmed == body:
            break
        body = trimmed
    return body.strip()


# ---------------------------------------------------------------- 目录变化通知

class PollWatcher:
    """系统不支持目录变化通知时的退路：按超时睡眠，wake() 可以提前叫醒"""
    native = False

    def __init__(self):
        self._event = threading.Event()

    def wake(self):
        self._event.set()

    def wait(self, dirs, timeout):
        if self._event.wait(timeout):
            self._event.clear()


class WinDirWatcher:
    """Windows 目录变化通知：md 所在目录里有文件新建、写入、改名时，wait() 立即返回"""
    native = True
    # FILE_NOTIFY_CHANGE_FILE_NAME | FILE_NOTIFY_CHANGE_SIZE | FILE_NOTIFY_CHANGE_LAST_WRITE
    NOTIFY_FILTER = 0x01 | 0x08 | 0x10
    MAX_DIRS = 63  # WaitForMultipleObjects 最多等 64 个句柄，留一个给 wake 事件
    WAIT_FAILED = 0xFFFFFFFF

    def __init__(self):
        import ctypes
        from ctypes import wintypes

        k = ctypes.WinDLL("kernel32", use_last_error=True)
        H, B, D = wintypes.HANDLE, wintypes.BOOL, wintypes.DWORD
        for name, argtypes, restype in [
            ("FindFirstChangeNotificationW", [wintypes.LPCWSTR, B, D], H),
            ("FindNextChangeNotification", [H], B),
            ("FindCloseChangeNotification", [H], B),
            ("CreateEventW", [wintypes.LPVOID, B, B, wintypes.LPCWSTR], H),
            ("SetEvent", [H], B),
            ("WaitForMultipleObjects", [D, ctypes.POINTER(H), B, D], D),
        ]:
            fn = getattr(k, name)
            fn.argtypes, fn.restype = argtypes, restype
        self._ctypes = ctypes
        self._k = k
        self._HANDLE = H
        self._invalid = ctypes.c_void_p(-1).value  # INVALID_HANDLE_VALUE
        self._wake = k.CreateEventW(None, False, False, None)  # 自动复位事件
        if not self._wake:
            raise ctypes.WinError(ctypes.get_last_error())
        self._handles = {}    # 规范化后的目录 -> 通知句柄
        self._failed = set()  # 打不开的目录，只记一次日志

    def wake(self):
        self._k.SetEvent(self._wake)

    def _sync(self, dirs):
        """让监听的目录和 dirs 保持一致：多的关掉，少的补上"""
        want = {}
        for d in dirs:
            want.setdefault(os.path.normcase(os.path.abspath(d)), d)
        for key in list(self._handles):
            if key not in want:
                self._k.FindCloseChangeNotification(self._handles.pop(key))
        for key, d in want.items():
            if key in self._handles:
                continue
            if len(self._handles) >= self.MAX_DIRS:
                break  # 超出的目录靠兜底复查
            h = self._k.FindFirstChangeNotificationW(d, False, self.NOTIFY_FILTER)
            if not h or h == self._invalid:
                if key not in self._failed:
                    self._failed.add(key)
                    log(f"无法监听目录 {d}（错误码 {self._ctypes.get_last_error()}），"
                        f"该目录改为每 {RESCAN_INTERVAL:g} 秒复查一次")
                continue
            self._failed.discard(key)
            self._handles[key] = h

    def wait(self, dirs, timeout):
        self._sync(dirs)
        keys = list(self._handles)
        arr = (self._HANDLE * (len(keys) + 1))(self._wake, *(self._handles[k] for k in keys))
        r = self._k.WaitForMultipleObjects(len(keys) + 1, arr, False, max(0, int(timeout * 1000)))
        if 1 <= r <= len(keys):
            key = keys[r - 1]
            # 每次收到通知后要重新挂上；挂不上（比如目录被删了）就关掉，下一轮 _sync 再重新打开
            if not self._k.FindNextChangeNotification(self._handles[key]):
                self._k.FindCloseChangeNotification(self._handles.pop(key))
        elif r == self.WAIT_FAILED:
            raise self._ctypes.WinError(self._ctypes.get_last_error())


def create_dir_watcher():
    if os.name == "nt":
        try:
            return WinDirWatcher()
        except Exception as e:
            log(f"目录变化通知不可用（{e}），改为每 {POLL_INTERVAL:g} 秒轮询")
    return PollWatcher()


# ---------------------------------------------------------------- 监控线程

_seen = {}  # 问题 id -> (mtime_ns, size)：文件没变化就不重复读
_watcher = None  # start_monitor() 里创建

# 问题状态（回答完毕 / 取消）每变一次加 1，正在长轮询等待的请求据此立即返回
_status_cond = threading.Condition()
_status_version = 0


def notify_status_change():
    global _status_version
    with _status_cond:
        _status_version += 1
        _status_cond.notify_all()


def wake_monitor():
    """有新问题时叫醒监控线程，让它马上开始监听新问题所在的目录"""
    if _watcher:
        _watcher.wake()


def check_pending_once():
    """检查所有待回答的 md。返回 (这些 md 所在的目录, 还在写的文件最多再等几秒才算静止；没有则为 None)"""
    # 每个用户同一时间只允许一个待回答问题，所以这里的每一条就是该用户编号最大的 md
    with db() as c:
        rows = c.execute(
            "SELECT q.id, q.md_path, q.md_no, q.question, u.username FROM questions q "
            "JOIN users u ON u.id = q.user_id WHERE q.status = 'pending'"
        ).fetchall()

    alive = set()
    dirs = set()
    settle_wait = None
    answered = False
    for r in rows:
        alive.add(r["id"])
        dirs.add(os.path.dirname(r["md_path"]))
        try:
            st = os.stat(r["md_path"])
        except OSError:
            continue
        sig = (st.st_mtime_ns, st.st_size)
        if _seen.get(r["id"]) == sig:
            continue
        quiet = time.time() - st.st_mtime
        if quiet < SETTLE_SECONDS:
            # 回答方可能还在写，等静止够了再看
            remain = min(SETTLE_SECONDS - quiet, SETTLE_SECONDS)
            settle_wait = remain if settle_wait is None else min(settle_wait, remain)
            continue
        try:
            text = read_md(r["md_path"])
        except OSError:
            continue
        answer = extract_answer(text, r["question"])
        if answer is None:
            _seen[r["id"]] = sig
            continue
        with db() as c:
            c.execute(
                "UPDATE questions SET status = 'answered', answer = ?, answered_at = ? "
                "WHERE id = ? AND status = 'pending'",
                (answer, now_str(), r["id"]),
            )
        answered = True
        log(f"{r['username']} 的 {r['md_no']}.md 已回答完毕（{len(answer)} 字）")

    for qid in list(_seen):
        if qid not in alive:
            del _seen[qid]
    if answered:
        notify_status_change()
    return dirs, settle_wait


def monitor_loop(watcher):
    if watcher.native:
        idle = RESCAN_INTERVAL
        log(f"开始监控 md（监听目录变化，出现“{DONE_MARK}”立即返回结果；另每 {idle:g} 秒兜底复查一次）")
    else:
        idle = POLL_INTERVAL
        log(f"开始监控 md（每 {idle:g} 秒检查一次，出现“{DONE_MARK}”即返回结果）")
    while True:
        dirs, settle_wait = set(), None
        try:
            dirs, settle_wait = check_pending_once()
        except Exception:
            traceback.print_exc()
        timeout = idle if settle_wait is None else min(idle, settle_wait + 0.05)
        try:
            watcher.wait(dirs, timeout)
        except Exception:
            traceback.print_exc()
            time.sleep(POLL_INTERVAL)


def start_monitor():
    global _watcher
    _watcher = create_dir_watcher()
    threading.Thread(target=monitor_loop, args=(_watcher,), name="md-monitor", daemon=True).start()


# ---------------------------------------------------------------- 工具函数

def public_user(row):
    return {
        "id": row["id"],
        "username": row["username"],
        "role": row["role"],
        "md_dir": row["md_dir"],
        "enabled": bool(row["enabled"]),
        "must_change_pw": bool(row["must_change_pw"]),
        "created_at": row["created_at"],
    }


def public_question(row):
    q = {k: row[k] for k in ("id", "md_no", "md_path", "question", "answer", "status", "created_at", "answered_at")}
    q["md_name"] = f"{row['md_no']}.md"
    if row["status"] == "pending":
        q["file_exists"] = os.path.exists(row["md_path"])
    return q


def check_new_password(password):
    if len(password) < 6:
        raise ApiError(400, "密码至少 6 位")
    if len(password) > 128:
        raise ApiError(400, "密码太长")


def parse_role(value):
    if value not in ("admin", "user"):
        raise ApiError(400, "角色只能是 admin 或 user")
    return value


def normalize_dir(value):
    d = os.path.expanduser(str(value or "").strip().strip('"'))
    if not d:
        raise ApiError(400, "md 目录不能为空")
    if not os.path.isabs(d):
        raise ApiError(400, r"md 目录必须是绝对路径，例如 C:\Users\xxx\Documents\longlingl")
    d = os.path.normpath(d)
    try:
        os.makedirs(d, exist_ok=True)
    except OSError as e:
        raise ApiError(400, f"无法创建目录 {d}：{e.strerror or e}")
    return d


def get_user_row(uid):
    with db() as c:
        row = c.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone()
    if not row:
        raise ApiError(404, "用户不存在")
    return row


# ---------------------------------------------------------------- 接口

ROUTES = []
_create_lock = threading.Lock()


def route(method, path, auth="user"):
    """auth: None 不需要登录 / "user" 需要登录 / "admin" 需要管理员"""
    def deco(fn):
        ROUTES.append((method, re.compile(f"^{path}$"), auth, fn))
        return fn
    return deco


@route("POST", "/api/login", auth=None)
def api_login(h, user):
    username = str(h.body.get("username", "")).strip()
    password = str(h.body.get("password", ""))
    with db() as c:
        row = c.execute("SELECT * FROM users WHERE username = ?", (username,)).fetchone()
    if not row or not verify_password(password, row["password_hash"]):
        time.sleep(0.5)
        raise ApiError(401, "用户名或密码错误")
    if not row["enabled"]:
        raise ApiError(403, "账号已被禁用，请联系管理员")
    token = secrets.token_urlsafe(32)
    with db() as c:
        c.execute("DELETE FROM sessions WHERE expires_at < ?", (time.time(),))
        c.execute(
            "INSERT INTO sessions(token_hash, user_id, expires_at) VALUES(?, ?, ?)",
            (token_hash(token), row["id"], time.time() + SESSION_TTL),
        )
    h.set_cookie(f"sid={token}; Path=/; Max-Age={SESSION_TTL}; HttpOnly; SameSite=Lax")
    log(f"{row['username']} 登录")
    return {"user": public_user(row), "default_dir": CONFIG["default_md_dir"]}


@route("POST", "/api/logout", auth=None)
def api_logout(h, user):
    token = h.session_token()
    if token:
        with db() as c:
            c.execute("DELETE FROM sessions WHERE token_hash = ?", (token_hash(token),))
    h.set_cookie("sid=; Path=/; Max-Age=0; HttpOnly; SameSite=Lax")


@route("GET", "/api/me")
def api_me(h, user):
    return {"user": public_user(user), "default_dir": CONFIG["default_md_dir"]}


@route("POST", "/api/me/password")
def api_change_password(h, user):
    old = str(h.body.get("old_password", ""))
    new = str(h.body.get("new_password", ""))
    if not verify_password(old, user["password_hash"]):
        raise ApiError(400, "原密码不正确")
    check_new_password(new)
    if new == old:
        raise ApiError(400, "新密码不能和原密码相同")
    with db() as c:
        c.execute("UPDATE users SET password_hash = ?, must_change_pw = 0 WHERE id = ?",
                  (hash_password(new), user["id"]))
        # 其他设备上的登录全部失效，保留当前这个
        c.execute("DELETE FROM sessions WHERE user_id = ? AND token_hash != ?",
                  (user["id"], token_hash(h.session_token())))
    log(f"{user['username']} 修改了密码")


@route("GET", "/api/questions")
def api_list_questions(h, user):
    with db() as c:
        rows = c.execute(
            "SELECT * FROM (SELECT * FROM questions WHERE user_id = ? ORDER BY id DESC LIMIT 200) ORDER BY id",
            (user["id"],),
        ).fetchall()
    return {"questions": [public_question(r) for r in rows]}


@route("POST", "/api/questions")
def api_ask(h, user):
    question = str(h.body.get("question", "")).strip()
    if not question:
        raise ApiError(400, "问题不能为空")
    if len(question) > MAX_QUESTION_LEN:
        raise ApiError(400, f"问题太长（最多 {MAX_QUESTION_LEN} 字）")
    with _create_lock:
        with db() as c:
            pending = c.execute(
                "SELECT md_no FROM questions WHERE user_id = ? AND status = 'pending'", (user["id"],)
            ).fetchone()
        if pending:
            raise ApiError(409, f"上一个问题（{pending['md_no']}.md）还在等待回答，请等回答完毕或先取消")
        try:
            no, path = write_question_md(user["md_dir"], question)
        except OSError as e:
            raise ApiError(500, f"写入 md 失败：{e}")
        with db() as c:
            cur = c.execute(
                "INSERT INTO questions(user_id, md_no, md_path, question, created_at) VALUES(?, ?, ?, ?, ?)",
                (user["id"], no, path, question, now_str()),
            )
            row = c.execute("SELECT * FROM questions WHERE id = ?", (cur.lastrowid,)).fetchone()
    wake_monitor()
    log(f"{user['username']} 提问 -> {path}")
    return {"question": public_question(row)}


@route("GET", r"/api/questions/(\d+)")
def api_get_question(h, user, qid):
    """?wait=秒数：问题还没回答时最多等这么久（长轮询），回答完毕立即返回"""
    try:
        wait = min(max(float(h.query.get("wait", ["0"])[0]), 0), MAX_WAIT)
    except ValueError:
        wait = 0
    deadline = time.time() + wait
    while True:
        version = _status_version  # 先记下再查库，查库期间状态变了也不会漏掉
        with db() as c:
            row = c.execute("SELECT * FROM questions WHERE id = ? AND user_id = ?",
                            (int(qid), user["id"])).fetchone()
        if not row:
            raise ApiError(404, "问题不存在")
        remaining = deadline - time.time()
        if row["status"] != "pending" or remaining <= 0:
            return {"question": public_question(row)}
        # 回答完毕或取消时监控线程会通知，立即醒来；最多等 5 秒再查一次库兜底
        with _status_cond:
            _status_cond.wait_for(lambda: _status_version != version, min(remaining, 5))


@route("POST", r"/api/questions/(\d+)/cancel")
def api_cancel_question(h, user, qid):
    with db() as c:
        c.execute("UPDATE questions SET status = 'cancelled' WHERE id = ? AND user_id = ? AND status = 'pending'",
                  (int(qid), user["id"]))
        row = c.execute("SELECT * FROM questions WHERE id = ? AND user_id = ?", (int(qid), user["id"])).fetchone()
    if not row:
        raise ApiError(404, "问题不存在")
    notify_status_change()
    return {"question": public_question(row)}


@route("GET", "/api/admin/users", auth="admin")
def api_admin_users(h, user):
    with db() as c:
        rows = c.execute(
            "SELECT u.*, COUNT(q.id) AS q_total, COALESCE(SUM(q.status = 'pending'), 0) AS q_pending "
            "FROM users u LEFT JOIN questions q ON q.user_id = u.id GROUP BY u.id ORDER BY u.id"
        ).fetchall()
    return {"users": [public_user(r) | {"q_total": r["q_total"], "q_pending": r["q_pending"]} for r in rows]}


@route("POST", "/api/admin/users", auth="admin")
def api_admin_create_user(h, user):
    b = h.body
    username = str(b.get("username", "")).strip()
    if not USERNAME_RE.match(username):
        raise ApiError(400, "用户名需为 2~32 位的字母、数字、汉字或 . _ - @")
    password = str(b.get("password", ""))
    check_new_password(password)
    role = parse_role(b.get("role", "user"))
    md_dir = normalize_dir(b.get("md_dir") or CONFIG["default_md_dir"])
    enabled = 1 if b.get("enabled", True) else 0
    with db() as c:
        if c.execute("SELECT 1 FROM users WHERE username = ?", (username,)).fetchone():
            raise ApiError(409, "用户名已存在")
        cur = c.execute(
            "INSERT INTO users(username, password_hash, role, md_dir, enabled, created_at) VALUES(?, ?, ?, ?, ?, ?)",
            (username, hash_password(password), role, md_dir, enabled, now_str()),
        )
        row = c.execute("SELECT * FROM users WHERE id = ?", (cur.lastrowid,)).fetchone()
    log(f"管理员 {user['username']} 新建用户 {username}（{role}，{md_dir}）")
    return {"user": public_user(row)}


@route("PUT", r"/api/admin/users/(\d+)", auth="admin")
def api_admin_update_user(h, user, uid):
    uid = int(uid)
    target = get_user_row(uid)
    b = h.body
    sets, params = [], []
    kick = False  # 是否让该用户重新登录
    if "role" in b:
        role = parse_role(b["role"])
        if uid == user["id"] and role != "admin":
            raise ApiError(400, "不能取消自己的管理员身份")
        sets.append("role = ?")
        params.append(role)
    if "enabled" in b:
        enabled = 1 if b["enabled"] else 0
        if uid == user["id"] and not enabled:
            raise ApiError(400, "不能禁用自己")
        sets.append("enabled = ?")
        params.append(enabled)
        kick = kick or not enabled
    if "md_dir" in b:
        sets.append("md_dir = ?")
        params.append(normalize_dir(b["md_dir"]))
    if b.get("password"):
        password = str(b["password"])
        check_new_password(password)
        sets += ["password_hash = ?", "must_change_pw = 0"]
        params.append(hash_password(password))
        kick = kick or uid != user["id"]
    if not sets:
        raise ApiError(400, "没有要修改的内容")
    with db() as c:
        c.execute(f"UPDATE users SET {', '.join(sets)} WHERE id = ?", (*params, uid))
        if kick:
            c.execute("DELETE FROM sessions WHERE user_id = ?", (uid,))
        row = c.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone()
    log(f"管理员 {user['username']} 修改用户 {target['username']}")
    return {"user": public_user(row)}


@route("DELETE", r"/api/admin/users/(\d+)", auth="admin")
def api_admin_delete_user(h, user, uid):
    uid = int(uid)
    if uid == user["id"]:
        raise ApiError(400, "不能删除自己")
    target = get_user_row(uid)
    with db() as c:
        c.execute("DELETE FROM users WHERE id = ?", (uid,))
    log(f"管理员 {user['username']} 删除用户 {target['username']}（md 文件保留）")


# ---------------------------------------------------------------- HTTP

class Handler(BaseHTTPRequestHandler):
    server_version = "MoniHuihua/1.0"

    def log_message(self, fmt, *args):
        pass  # 前端会长轮询，逐条打印请求太吵

    def do_GET(self):
        self.dispatch("GET")

    def do_POST(self):
        self.dispatch("POST")

    def do_PUT(self):
        self.dispatch("PUT")

    def do_DELETE(self):
        self.dispatch("DELETE")

    def dispatch(self, method):
        try:
            self._dispatch(method)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass  # 浏览器提前断开（例如长轮询时刷新页面）

    def _dispatch(self, method):
        url = urlparse(self.path)
        self.query = parse_qs(url.query)
        self.body = {}
        self.cookies_out = []
        if not url.path.startswith("/api/"):
            if method == "GET":
                return self.serve_static(url.path)
            return self.send_json(404, {"error": "Not Found"})
        for m, rx, auth, fn in ROUTES:
            match = rx.match(url.path)
            if m != method or not match:
                continue
            try:
                user = self.current_user()
                if auth and not user:
                    raise ApiError(401, "请先登录")
                if auth == "admin" and user["role"] != "admin":
                    raise ApiError(403, "需要管理员权限")
                if method in ("POST", "PUT"):
                    self.body = self.read_json()
                result = fn(self, user, *match.groups())
                self.send_json(200, result if result is not None else {"ok": True})
            except ApiError as e:
                self.send_json(e.status, {"error": e.message})
            except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
                raise
            except Exception:
                traceback.print_exc()
                self.send_json(500, {"error": "服务器内部错误"})
            return
        self.send_json(404, {"error": "接口不存在"})

    def session_token(self):
        try:
            morsel = SimpleCookie(self.headers.get("Cookie", "")).get("sid")
        except CookieError:
            return None
        return morsel.value if morsel and morsel.value else None

    def current_user(self):
        token = self.session_token()
        if not token:
            return None
        with db() as c:
            row = c.execute(
                "SELECT u.* FROM sessions s JOIN users u ON u.id = s.user_id "
                "WHERE s.token_hash = ? AND s.expires_at > ? AND u.enabled = 1",
                (token_hash(token), time.time()),
            ).fetchone()
        return dict(row) if row else None

    def read_json(self):
        # 只收 JSON：普通的跨站表单发不出这种请求，顺带挡住 CSRF
        if "application/json" not in self.headers.get("Content-Type", ""):
            raise ApiError(415, "请求必须是 JSON")
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            raise ApiError(400, "Content-Length 错误")
        if length > MAX_BODY:
            raise ApiError(413, "请求体过大")
        raw = self.rfile.read(length) if length else b"{}"
        try:
            data = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            raise ApiError(400, "JSON 格式错误")
        if not isinstance(data, dict):
            raise ApiError(400, "JSON 格式错误")
        return data

    def set_cookie(self, value):
        self.cookies_out.append(value)

    def send_bytes(self, status, data, content_type):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        for cookie in self.cookies_out:
            self.send_header("Set-Cookie", cookie)
        self.end_headers()
        self.wfile.write(data)

    def send_json(self, status, obj):
        self.send_bytes(status, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                        "application/json; charset=utf-8")

    def serve_static(self, path):
        if path not in ("/", "/index.html"):
            return self.send_bytes(404, b"Not Found", "text/plain; charset=utf-8")
        with open(os.path.join(STATIC_DIR, "index.html"), "rb") as f:
            self.send_bytes(200, f.read(), "text/html; charset=utf-8")


def main():
    ap = argparse.ArgumentParser(description="模拟会话：基于 md 文件的问答系统")
    ap.add_argument("--host", default="127.0.0.1", help="监听地址；让局域网其他电脑访问请用 0.0.0.0（默认 127.0.0.1）")
    ap.add_argument("--port", type=int, default=8000, help="端口（默认 8000）")
    ap.add_argument("--default-dir", default=CONFIG["default_md_dir"], help="新用户默认的 md 目录")
    ap.add_argument("--db", default=CONFIG["db_path"], help="数据库文件（默认 data/app.db）")
    ap.add_argument("--admin-password", default="admin123", help="首次启动创建管理员 admin 时用的密码")
    args = ap.parse_args()

    CONFIG["db_path"] = os.path.abspath(args.db)
    CONFIG["default_md_dir"] = os.path.normpath(args.default_dir)
    init_db(args.admin_password)
    start_monitor()

    server = ThreadingHTTPServer((args.host, args.port), Handler)
    server.daemon_threads = True
    shown = "127.0.0.1" if args.host in ("", "0.0.0.0") else args.host
    log(f"服务已启动：http://{shown}:{args.port}  （按 Ctrl+C 退出）")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log("已退出")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
