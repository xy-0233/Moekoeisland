# -*- coding: utf-8 -*-
"""
MoeKoeIsland —— MoeKoe Music 桌面组件 v1.1（可独立显示 / 可换肤 / 带托盘设置）
两个组件（同一进程，可分别开关）:
  1) 灵动岛: 屏幕顶部胶囊 —— 圆角方形封面 + 歌词
             版式 compact(单行) / dual(双行: 歌词 + 翻译)
             播放中且有字级时间戳则逐字卡拉OK高亮，超宽自动跑马灯
             左键按住拖动; 拖到屏幕顶部附近（≤90px）释放自动吸附并水平居中
  2) 任务栏组件: 扁平融入任务栏（透明背景、无胶囊底）
             圆角封面 + ⏮ ⏯ ⏭（**鼠标移入才展开，移开自动回收**，给歌词让位）
             **当前歌词卡拉OK逐字高亮 + 歌词跟踪**，第二行显示翻译
             文字颜色可自动适配任务栏明暗，也可自定义
后台设置: 系统托盘图标（双击/右键）→ 显示开关 + 外观（颜色/圆角/字号/透明度）
播放控制: SMTC（winrt.windows.media.control，常驻 worker loop）→ WS 插件通道（带回执校验+重试）→ 系统媒体键
数据源: ws://127.0.0.1:6520 (需在 MoeKoe 设置中开启 API 模式 / apiMode='on')

v1.4.5 修复：SMTC 调用不再每次新建 event loop（旧写法在「调用线程自己
已有 running loop」时会抛 RuntimeError 并静默降级）；WS 通道下发后读回执
并重试，解决「第一次打开 MoeKoe 时三键按不动」。
"""

import sys, os, json, time, base64, re, math, threading, socket, ctypes, ctypes.wintypes as wt, urllib.request
import asyncio          # SMTC worker 常驻 loop 用（见 smtc_control）
from PyQt5.QtWidgets import (QApplication, QWidget, QMenu, QAction, QSystemTrayIcon,
                             QDialog, QLabel, QCheckBox, QComboBox, QSpinBox,
                             QPushButton, QGridLayout, QHBoxLayout, QVBoxLayout,
                             QGroupBox, QFrame, QColorDialog, QSizePolicy)
from PyQt5.QtCore import Qt, QTimer, QRectF, QPointF, QPoint, QEasingCurve, QPropertyAnimation
from PyQt5.QtGui import (QPainter, QColor, QPixmap, QPainterPath, QTransform,
                         QImage, QFont, QFontMetrics, QFontMetricsF, QLinearGradient, QPen, QPolygonF,
                         QBrush, QIcon)

APP_VERSION = '1.7.24'
APP_NAME    = 'MoeKoeIsland'

# ---- v1.4.9：WM_NCHITTEST 命中测试（把「哪里可点」交给操作系统逐点回答）----
# 依据：SPlayer-Next 的任务栏歌词**不靠手工轮询**，命中测试完全由 Windows 做
#      （读其 resources/native/taskbar-lyric.node + out/main/index.js 得到）。
# Windows 上「局部可点、其余穿透」的标准 API 就是 WM_NCHITTEST：
#   HTTRANSPARENT(-1) → 此处所有鼠标消息转交下层窗口（穿透，任务栏照常可用）
#   HTCLIENT(1)       → 本窗口接收（三键点击）
WM_NCHITTEST  = 0x0084
HTTRANSPARENT = -1
HTCLIENT      = 1
HTCAPTION     = 2
HOST_ID     = 'moekoe-island-host'      # 与插件 manifest 的 moekoe_native_hosts[].id 一致
IS_FROZEN   = bool(getattr(sys, 'frozen', False))   # True = 已被 PyInstaller 打包成 exe
EXIT_SHUTDOWN = 42      # 收到插件 shutdown 时的退出码，看门狗父进程据此同步退出
EXIT_ANOTHER_INSTANCE = 43   # 已有实例在画 UI：看门狗据此停止重启（避免空转刷屏）

APP_DIR   = os.path.join(os.environ.get('APPDATA', os.path.expanduser('~')), 'MoeKoeIsland')
CONFIG_F  = os.path.join(APP_DIR, 'config.json')
DEBUG_F   = os.path.join(APP_DIR, 'debug.log')
QUIT_F    = os.path.join(APP_DIR, 'quit.flag')   # 「用户主动退出」标记：standby 实例看到就别再接管
SESSION_F = os.path.join(APP_DIR, 'last_session.json')  # 上次关闭时的歌曲/歌词/进度缓存
WS_HOST, WS_PORT = '127.0.0.1', 6520

# 主题默认值（实际使用请读 CFG，见 island_colors() / tb_colors()）
T_BORDER     = QColor(255, 255, 255, 30)
T_DOT_OK     = QColor('#3DDC84')
T_DOT_BAD    = QColor(255, 255, 255, 70)

MARGIN = 18   # 灵动岛阴影预留边距

def _splayer_line_ease(k):
    """CSS cubic-bezier(0.4, 0, 0.2, 1), matching SPlayer line transitions."""
    k = max(0.0, min(1.0, float(k)))
    if k <= 0.0 or k >= 1.0:
        return k
    x1, y1, x2, y2 = 0.4, 0.0, 0.2, 1.0

    def bez(a, b, t):
        mt = 1.0 - t
        return 3.0 * mt * mt * t * a + 3.0 * mt * t * t * b + t * t * t

    lo, hi = 0.0, 1.0
    t = k
    for _ in range(8):
        x = bez(x1, x2, t)
        if x < k:
            lo = t
        else:
            hi = t
        t = (lo + hi) * 0.5
    return bez(y1, y2, t)


def _cubic_bezier(p1x, p1y, p2x, p2y, steps=10):
    """通用 CSS cubic-bezier 求值器（按 x 反解 t 后取 y）。

    比 QEasingCurve 更贴 CSS：可以精确复刻 SPlayer 的
    `cubic-bezier(0.34, 1.56, 0.64, 1)`（回弹过冲）与 `ease-in`。
    """
    def bez(a, b, t):
        mt = 1.0 - t
        return 3.0 * mt * mt * t * a + 3.0 * mt * t * t * b + t * t * t

    def fn(k):
        k = max(0.0, min(1.0, float(k)))
        if k <= 0.0 or k >= 1.0:
            return k
        lo, hi, t = 0.0, 1.0, k
        for _ in range(steps):
            x = bez(p1x, p2x, t)
            if x < k:
                lo = t
            else:
                hi = t
            t = (lo + hi) * 0.5
        return bez(p1y, p2y, t)

    return fn


# ---- SPlayer Next 灵动岛换句动画的三条缓动（源码：windows/dynamic-island/App.vue）----
#   ① 收缩 .lyric.is-shrinking  → transition: width .25s ease-in, opacity .25s ease-in
#   ② 展开 .lyric                → transition: width .5s cubic-bezier(.34,1.56,.64,1)
#   ③      展开期的淡入          → opacity .25s ease-out
sp_ease_in = _cubic_bezier(0.42, 0.0, 1.0, 1.0)        # CSS ease-in
sp_back_out = _cubic_bezier(0.34, 1.56, 0.64, 1.0)     # CSS 回弹（峰值 ≈ 1.10）
sp_ease_out = _cubic_bezier(0.0, 0.0, 0.58, 1.0)       # CSS ease-out

# ---- v1.7.17 → v1.7.18：灵动岛「展开」曲线的两次修正 ----
#   需求①（v1.7.17）：「那个灵动岛那边跳转歌词伸缩的时候会"震动"一下，请你把"震动"这个效果给去掉」
#   需求②（v1.7.18）：「你改了之后，歌词闪动变得更加严重了，请你再继续修改」
#
#   取证（2026-10-10，compact 版式 150% 缩放；逐帧像素量「墨迹 ink / 槽宽 slot / 不透明度 op」）：
#     · 「震动」的真身 = `sp_back_out` 的 **10% 过冲**：峰值槽宽冲到 713.6 再回落到
#       650.1（回缩 63.5px）——「弹过头再缩回来」这一来一回。**不是**「起步快」本身。
#     · v1.7.17 为去过冲，把展开曲线换成 Material `cubic-bezier(0.4,0,0.2,1)`，
#       并**顺手把「展开淡入」也换成了同一条曲线** —— 这一步过头了：
#       Material 起点太平缓（16ms 只走 0.2%，100ms 才 13.4%），于是
#       ① 槽宽在 0~100px 的「窄槽」区间里停留约 90ms（旧曲线只有约 20ms），
#          而窄槽里文字是**居中裁切**的 → 这 90ms 屏幕上只露出句子正中间的
#          几个陌生字、且每帧换一批 → 这就是「闪动」；
#       ② 不透明度也从「前快（ease-out）」变成「前慢」，文字真正亮起来更晚，
#          中间那段「胶囊在、字没有」的空窗被拉长 → 「闪」的感受加剧。
#     实测空窗（文字墨迹几乎为零的连续帧）：v1.7.16 = 8 帧、v1.7.17 = 22 帧（8ms/帧）。
#
#   修法（v1.7.18）：展开曲线改用 `cubic-bezier(0.25, 0.9, 0.25, 1)` ——
#     ① 起步速度与 v1.7.16 的原曲线**几乎一致**（16ms 涨 11.6% vs 14.1%，
#        100ms 涨 65.1% vs 70.3%）→ 窄槽区间一闪而过，「闪动」回到原水平；
#     ② 控制点 y 值均 ≤ 1（0.9 / 1.0）→ 数值扫描（k 步进 0.01）峰值恰为 **1.0000**，
#        **零过冲**且恒单调 → v1.7.17 修掉的「震动」不会回来。
#     · 展开淡入同步**还原成 SPlayer 原版 `sp_ease_out`**（`cubic-bezier(0,0,.58,1)`，
#       前快后慢）—— 与上面 500ms 的宽度曲线在时间轴上天然同步
#       （64ms：宽 45% / 透明 39%；160ms：宽 85% / 透明 82%），
#       既没有「字先亮、槽还窄」的割裂，也不再把空窗拉长。
#   开关：`Island.EXPAND_BOUNCE`（默认 False）。置 True 即完整恢复 v1.7.7~v1.7.16
#     的 SPlayer 原味回弹（`sp_back_out` 与其代码路径**原样保留**，未删除）。
sp_expand_out = _cubic_bezier(0.4, 0.0, 0.2, 1.0)       # Material standard（v1.7.17 用过，已弃用）
sp_expand_fast = _cubic_bezier(0.25, 0.9, 0.25, 1.0)    # v1.7.18：快起 + 零过冲


# ---- v1.7.10：绘制坐标「整数像素吸附」 ----
#   ⚠️⚠️ 这是「灵动岛换句震动」与「任务栏放大发虚」两条 bug 的共同根因 ⚠️⚠️
#
#   现场（真实测量，diag_jank / exp_fix）：
#     灵动岛换句收缩期，文字绘制原点的小数部分是**逐帧翻转**的：
#       89.00 → 88.50 → 86.50 → 83.50 → 80.00 → 75.50 → 70.50 …
#     `.0` 与 `.5` 交替出现，占比约 7:3。
#
#   为什么这会让画面「震」：
#     Qt 的 `drawText(QPointF)` 对**小数原点**走**子像素定位**——同一个字
#     在不同小数相位下会被栅格化成**不同的位图**（glyph cache 里各存一份）。
#     换句时槽宽每帧都变 → 原点相位逐帧翻转 → 字形位图每帧换一次，
#     「清晰 ↔ 半像素发虚」来回跳，加上位移随相位呈 2.5/3.0px 的不均匀步长，
#     肉眼就是「跳转歌词的那一下有震动」。
#
#   为什么这还会「卡」：
#     任务栏换句放大时主行 `cy` 是**连续插值**的（47.72 → 46.84 → …），
#     小数 y 相位每帧都不同 → 整串文字每帧重新栅格化（CJK 字形昂贵）→
#     掉帧。吸附到整数后字形自然命中缓存。实测这一项就是 5~10ms/帧的代价。
#
#   修法：所有**会随动画变化**的绘制坐标，一律吸附到整数像素。
#     注意 `_line_fx` 里有 translate 变换，必须对**设备坐标**取整
#     （见该函数里 `_px(...) - x` 的写法），只对局部坐标取整是没用的。
#
#   ⚠️ v1.7.11 曾想把取整网格改成 1/DPR（怀疑 150% 缩放下「逻辑整数 ≠ 设备整数」），
#     但**实测证伪**：本进程 `QScreen.devicePixelRatio() = 1.0` 且
#     `geometry = 2560×1600`（物理像素）—— Qt 没有做缩放（未启用
#     `AA_EnableHighDpiScaling`），逻辑像素**就是**设备像素，1/DPR 网格与整数网格
#     完全等价。故保持整数网格不动（少改一处、少一处风险）。
def _px(v):
    """把绘制坐标吸附到整数像素（消除子像素相位抖动 / 字形重复栅格化）。

    ⚠️ v1.7.19：这只解决「子像素发虚」。若坐标本身还要叠上**窗口位置**的取整
    误差（换句伸缩时窗口逐帧变宽），局部取整会留下 ±1px 的整数拍频 —— 那种
    「抖动」必须改用 `Island._px_abs()`（在屏幕绝对坐标取整一次）。"""
    return float(round(v))

# ---------------- 配置 ----------------
DEFAULT_CFG = {
    'x': None, 'y': 0,             # None = 屏幕顶格居中（内容区贴屏幕顶）
    'autostart': False,
    'snap_top': True,
    'tb_x': 100,                    # 任务栏组件相对任务栏左缘的偏移

    # ---- 显示开关（可只显示其一，也可同时显示）----
    'show_island': True,
    'show_taskbar': True,

    # ---- 歌词 ----
    'show_translation': True,       # 显示翻译（两个组件都生效）

    # ---- 灵动岛外观 ----
    'island_layout': 'compact',     # compact=单行(有翻译自动展开) | dual=恒双行
    'island_bg': '#1e1e24',         # 胶囊底色（渐变上端）
    'island_bg2': '#0c0c0f',        # 胶囊底色（渐变下端）
    'island_alpha': 246,            # 不透明度 120~255
    'island_text': '#ffffff',       # 歌词/文字色
    'island_sub': '#a8a8b4',        # 翻译/次要文字色
    'island_accent': '#4CC2FF',     # 卡拉OK高亮色
    'island_radius': 24,            # 圆角
    'island_font': 11,              # 主文字字号

    # ---- 任务栏组件外观 ----
    'tb_theme': 'auto',             # auto=跟随任务栏明暗 | light | dark | custom
    'tb_text': '#1a1a1a',           # 自定义文字色（tb_theme == 'custom' 时生效）
    'tb_accent': '#2F80ED',         # 卡拉OK高亮色
    'tb_show_cover': True,          # 显示封面
    'tb_show_btns': True,           # 显示 ⏮⏯⏭
    'tb_btns_auto_hide': True,      # 三键「回收/展开」：鼠标移到组件上才展开
    'tb_font': 10,                  # 主文字字号（v1.7.0 按 1.mp4 校准）
    'tb_font_profile': 'video1',    # 用于把旧默认字号 14 自动迁移到 1.mp4 的 10

    'tray_hint_shown': False,       # 首次启动时提示「已缩到托盘」
}

def log(msg):
    try:
        with open(DEBUG_F, 'a', encoding='utf-8') as f:
            f.write(time.strftime('[%m-%d %H:%M:%S] ') + str(msg) + '\n')
    except Exception:
        pass

def load_cfg():
    try:
        with open(CONFIG_F, encoding='utf-8') as f:
            c = json.load(f)
        if 'tb_font_profile' not in c and int(c.get('tb_font', 14) or 14) == 14:
            c['tb_font'] = 10
            c['tb_font_profile'] = 'video1'
        if 'island_top_profile' not in c and int(c.get('y', 10 + MARGIN) or 0) == 10 + MARGIN:
            c['y'] = 0
            c['island_top_profile'] = 'splayer-top'
        for k, v in DEFAULT_CFG.items():
            c.setdefault(k, v)
        return c
    except Exception:
        return dict(DEFAULT_CFG)

def save_cfg(cfg):
    try:
        os.makedirs(APP_DIR, exist_ok=True)
        with open(CONFIG_F, 'w', encoding='utf-8') as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        if ISLAND is not None:              # 自己的写入不该触发「外部改动」重载
            try:
                ISLAND._cfg_mtime = os.path.getmtime(CONFIG_F)
            except OSError:
                pass
    except Exception as e:
        log('save_cfg fail: %r' % e)

# ---------------- 主题读取（所有绘制都从这里取色） ----------------
def qcol(value, alpha=None, fallback='#ffffff'):
    """宽松取色：非法值回退，alpha 可选覆盖"""
    c = QColor(value) if isinstance(value, str) else QColor(value or fallback)
    if not c.isValid():
        c = QColor(fallback)
    if alpha is not None:
        c.setAlpha(int(max(0, min(255, alpha))))
    return c

def island_colors():
    a = int(max(60, min(255, CFG.get('island_alpha', 246))))
    return dict(
        bg1   = qcol(CFG.get('island_bg'), a),
        bg2   = qcol(CFG.get('island_bg2'), min(255, a + 4)),
        border= QColor(255, 255, 255, 30),
        text  = qcol(CFG.get('island_text'), fallback='#ffffff'),
        sub   = qcol(CFG.get('island_sub'), fallback='#a8a8b4'),
        accent= qcol(CFG.get('island_accent'), fallback='#4CC2FF'),
        dot_ok= QColor(T_DOT_OK), dot_bad= QColor(T_DOT_BAD),
    )

# ---------------- 跨线程指令 / 全局引用 ----------------
PENDING_CMDS = []      # 其它线程（native host）往这里塞指令，GUI 线程定时取
ISLAND = None          # Island 实例
STRIP = None           # TaskbarWidget 实例
TRAY = None            # Tray 实例
SETTINGS_DLG = None    # 设置面板实例

# ---------------- 「退出」的唯一出口 ----------------
def quit_flag_set():
    return os.path.exists(QUIT_F)

def clear_quit_flag():
    try:
        if os.path.exists(QUIT_F):
            os.remove(QUIT_F)
    except Exception:
        pass

def request_quit(reason=''):
    """真正退出进程（托盘菜单 / 岛右键菜单 / 设置面板 / 插件后台都走它）。

    ⚠️ 千万别再用 QApplication.quit()：它只结束事件循环、进程退出码是 0，
    而看门狗（supervise）只在子进程退出码为 42/43 时才停止重启 —— 0 会被当成
    「崩溃」→ 3 秒后又把组件拉起来。用户看到的现象就是：
    「点了退出，窗口消失几秒又自己冒出来，死活退不掉。」
    """
    log('quit requested (%s) -> exit' % (reason or 'user'))
    # 退出前强制落盘「上次播放会话」→ 下次启动能直接回放这首歌
    try:
        STATE.save_session(force=True)
    except Exception:
        pass
    try:
        open(QUIT_F, 'w').close()          # 告诉插件拉起的 standby 实例：别再接管
    except Exception:
        pass
    try:
        if TRAY is not None:
            TRAY.hide()
    except Exception:
        pass
    os._exit(EXIT_SHUTDOWN if os.environ.get('MOEKOE_SUPERVISED') else 0)

def sync_tray_checks():
    if TRAY is not None:
        try:
            TRAY.sync()
        except Exception:
            pass

def set_flag(key, value, save=True, notify=True):
    """写单个配置并立即生效（右键菜单 / 托盘 / 插件都走它）"""
    CFG[key] = value
    if save:
        save_cfg(CFG)
    if notify:
        PENDING_CMDS.append('cfg_changed')
    else:
        sync_tray_checks()

def apply_cfg_everywhere(reason=''):
    """把 CFG 的外观/显示设置应用到两个组件 + 托盘勾选状态"""
    try:
        if ISLAND is not None:
            ISLAND.apply_cfg()
        if STRIP is not None:
            STRIP.apply_cfg()
        sync_tray_checks()
        if reason and reason != 'cfg_changed':
            log('cfg applied (%s)' % reason)
    except Exception as e:
        log('apply_cfg_everywhere fail: %r' % e)

def open_settings_dialog():
    global SETTINGS_DLG
    try:
        if SETTINGS_DLG is None:
            SETTINGS_DLG = SettingsDialog()
        SETTINGS_DLG.reload()
        SETTINGS_DLG.show()
        SETTINGS_DLG.raise_()
        SETTINGS_DLG.activateWindow()
    except Exception as e:
        log('open settings fail: %r' % e)

def settings_view():
    """给插件弹窗看的设置快照"""
    keys = ('show_island', 'show_taskbar', 'show_translation', 'snap_top',
            'island_layout', 'island_bg', 'island_bg2', 'island_text',
            'island_accent', 'island_radius', 'island_font', 'island_alpha',
            'tb_theme', 'tb_text', 'tb_accent', 'tb_show_cover', 'tb_show_btns',
            'tb_btns_auto_hide', 'tb_font')
    return {k: CFG.get(k) for k in keys}

def apply_settings_patch(patch):
    """插件下发设置：白名单 + 类型校验后才写入（避免脏数据把配置搞坏）"""
    if not isinstance(patch, dict):
        return False
    bools = ('show_island', 'show_taskbar', 'show_translation', 'snap_top',
             'tb_show_cover', 'tb_show_btns', 'tb_btns_auto_hide')
    ints  = {'island_radius': (6, 40), 'island_font': (8, 22),
             'island_alpha': (60, 255), 'tb_font': (8, 18)}
    strs  = ('island_layout', 'island_bg', 'island_bg2', 'island_text',
             'island_sub', 'island_accent', 'tb_theme', 'tb_text', 'tb_accent')
    ok = False
    for k, v in patch.items():
        if k in bools:
            CFG[k] = bool(v); ok = True
        elif k in ints:
            try:
                lo, hi = ints[k]
                CFG[k] = max(lo, min(hi, int(v))); ok = True
            except Exception:
                pass
        elif k in strs:
            if isinstance(v, str) and 0 < len(v) < 40:
                CFG[k] = v; ok = True
    if ok:
        save_cfg(CFG)
        PENDING_CMDS.append('cfg_changed')
    return ok

def local_status():
    """当前实例的实时状态（插件弹窗读它）"""
    try:
        autostart = bool(load_cfg().get('autostart'))
    except Exception:
        autostart = False
    with STATE.lock:
        song = STATE.song or {}
        connected = bool(STATE.connected)
        playing = bool(STATE.is_playing)
    return {
        'version': APP_VERSION,
        'ui': True,
        'connected': connected,
        'playing': playing,
        'song': song.get('name') or '',
        'artist': song.get('author') or '',
        'autostart': autostart,
        'settings': settings_view(),
    }

def handle_local_request(req):
    """在 UI 进程里处理来自「standby native host」转发的请求。
    注意：跑在 bridge 线程里 → 任何 UI 操作只能通过 PENDING_CMDS 异步下发。"""
    act = (req or {}).get('action')
    if act == 'ping':
        return {'type': 'pong', 'time': int(time.time() * 1000)}
    if act == 'status':
        return {'type': 'status', 'data': local_status()}
    if act == 'get_settings':
        return {'type': 'settings', 'data': settings_view()}
    if act == 'set_settings':
        ok = apply_settings_patch((req or {}).get('settings') or {})
        return {'type': 'ack', 'action': act, 'ok': bool(ok), 'data': settings_view()}
    if act == 'open_settings':
        PENDING_CMDS.append('open_settings')
        return {'type': 'ack', 'action': act, 'ok': True}
    if act == 'center_island':
        PENDING_CMDS.append('center_island')
        return {'type': 'ack', 'action': act, 'ok': True}
    if act == 'quit':
        PENDING_CMDS.append('quit_app')
        return {'type': 'ack', 'action': act, 'ok': True}
    if act == 'open_config_dir':
        try:
            os.makedirs(APP_DIR, exist_ok=True)
            os.startfile(APP_DIR)
            return {'type': 'ack', 'action': act, 'ok': True}
        except Exception as e:
            return {'type': 'ack', 'action': act, 'ok': False, 'error': str(e)}
    return {'type': 'echo', 'request': req}

# 本地 IPC 端口：让「插件拉起的 standby 进程」把请求转给真正在画 UI 的实例，
# 否则弹窗会读到 standby 进程的空状态（表现为「组件在跑却显示未连接」）
BRIDGE_PORT = 65434

class LocalBridge(threading.Thread):
    """UI 进程内的本地 JSON-Lines 服务（127.0.0.1:65434）"""

    def __init__(self):
        super().__init__(daemon=True)
        self.srv = None
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind(('127.0.0.1', BRIDGE_PORT))
            s.listen(8)
            self.srv = s
        except OSError as e:
            try:
                s.close()
            except Exception:
                pass
            log('local bridge bind fail: %r' % e)

    def run(self):
        if self.srv is None:
            return
        log('local bridge listening on %d' % BRIDGE_PORT)
        while True:
            try:
                conn, _ = self.srv.accept()
            except Exception:
                return
            threading.Thread(target=self._serve, args=(conn,), daemon=True).start()

    def _serve(self, conn):
        try:
            conn.settimeout(6)
            buf = b''
            while True:
                while b'\n' not in buf:
                    chunk = conn.recv(65536)
                    if not chunk:
                        return
                    buf += chunk
                line, buf = buf.split(b'\n', 1)
                if not line.strip():
                    continue
                try:
                    req = json.loads(line.decode('utf-8', 'replace'))
                except Exception:
                    continue
                resp = handle_local_request(req)
                conn.sendall((json.dumps(resp, ensure_ascii=False) + '\n').encode('utf-8'))
        except Exception as e:
            log('bridge serve end: %r' % e)
        finally:
            try:
                conn.close()
            except Exception:
                pass

def bridge_request(req, timeout=2.0):
    """standby native host 用：把请求转发给 UI 实例；失败返回 None"""
    try:
        s = socket.create_connection(('127.0.0.1', BRIDGE_PORT), timeout=timeout)
    except OSError:
        return None
    try:
        s.sendall((json.dumps(req, ensure_ascii=False) + '\n').encode('utf-8'))
        buf = b''
        while b'\n' not in buf:
            chunk = s.recv(65536)
            if not chunk:
                return None
            buf += chunk
        return json.loads(buf.split(b'\n', 1)[0].decode('utf-8', 'replace'))
    except Exception:
        return None
    finally:
        try:
            s.close()
        except Exception:
            pass


# ---------------- 播放状态(WS 线程 → UI) ----------------
def is_error_text(s):
    """识别播放器泄漏进数据通道的**错误文案**（不是真歌名/歌词）。

    ⚠️ 真机实锤（2026-10-07 debug.log 19:49:17）：MoeKoe 取歌 URL 失败时，
    会把「获取音乐地址失败」当 song.name 经 WS 推来（歌词通道同样被污染），
    组件把错误串当歌名画在任务栏上（用户截图：⏸ + 两行「获取音乐地址失败」），
    还被 save_session 写进 last_session.json，重启后继续显示。
    判据：已知错误串精确命中，或「短文本 + 失败/错误类词根」（真歌名极少长这样，
    即使误伤也只是回到上一首的有效状态，代价远小于把错误串当歌名展示）。"""
    if not isinstance(s, str):
        return False
    t = s.strip()
    if not t or len(t) > 30:
        return False
    if t in ('获取音乐地址失败', '获取歌词失败', '获取歌曲失败', '加载失败',
             '网络错误', '播放失败', '请求失败', '未知歌曲'):
        return True
    return bool(re.search(r'(失败|错误|超时|异常|无法获取|无法播放)', t))


class PlayerState:
    def __init__(self):
        self.lock = threading.Lock()
        self.connected = False
        self.is_playing = False
        self.base_time = 0.0
        self.base_ts = time.time()
        self.lines = []               # [(start, end, text, trans, chars)]
        self.song = {}
        self.song_gen = 0
        self.control_gen = 0          # 播放态 / 歌曲 / 歌词任一变化都会递增，供按钮确认
        self.last_state_ts = 0.0
        self.has_lyrics = False
        # ⚠️⚠️【v1.7.22 修复「切歌时上一首的歌词多跳出来一次」】⚠️⚠️
        #   现象（用户 2026-10-10）：歌尾切到下一首时，灵动岛和任务栏都会把
        #   **上一首**的歌词再显示一次。
        #   机理（WS 推送时序竞态）：`playerState` 包**只带 isPlaying+currentTime、
        #   不带歌曲标识**。下一首歌开始播放时它先到（currentTime≈0），而
        #   `STATE.lines` 还是上一首的歌词 —— `current_line(旧歌词, 0ms)` 恰好命中
        #   **上一首的第 0 句** → 岛/任务栏把上一首开头那句显示出来，~250ms 后
        #   `server-lyrics`（歌+歌词同包）才到 → 又换一次。肉眼就是「多跳出来一次」。
        #   处置：**歌词持有窗口** —— 检测到「进度大幅回跳」（= 换歌/回跳 seek 的
        #   唯一可靠信号）时，把显示用进度时钟 `now()` 冻结在回跳前的值：
        #   行选择、卡拉OK、滚动进度全部冻在「上一首末尾」的原样 → 屏幕完全静止；
        #   新歌词包到达（`apply_lyrics`）即解冻，正好完成一次干净的换句。
        self.lyric_hold = False       # True = 显示冻结中（等待新歌词）
        self.hold_time = 0.0          # 冻结时锁定的显示进度（秒）
        self.hold_ts = 0.0            # 冻结开始的墙钟（安全超时用）

    def now(self):
        with self.lock:
            # v1.7.22：歌词持有期内冻结显示时钟（详见 __init__ 里的机理注释）。
            #   9 个显示侧调用点（_two_lines/_want_texts/岛 tick/岛 paint/
            #   任务栏 _cur_line/_span/paint）全部经由本函数 → 一处冻结、
            #   整块显示（选行+卡拉OK+滚动）完全一致地静止。
            if self.lyric_hold:
                # 安全阀：冻结超 2s（新歌词迟迟不来）→ 自行解冻，宁换勿卡
                if time.time() - self.hold_ts > 2.0:
                    self.lyric_hold = False
                else:
                    return self.hold_time
            if self.is_playing:
                return self.base_time + (time.time() - self.base_ts)
            return self.base_time

    # ---------- 上次播放会话的持久化（启动时恢复，实现「加载上次的歌曲」） ----------
    def restore_session(self):
        """程序启动时先读回上次关闭时的歌曲/歌词/进度。

        为什么需要：MoeKoe 的 WS 只推「当前播放」——用户上次听完了关掉，
        下次开程序时播放器还没推送，界面就显示「未知歌曲」（用户截图里的问题）。
        恢复后立即可见上次的歌，等 WS 真实数据到达再覆盖。
        """
        try:
            with open(SESSION_F, encoding='utf-8') as f:
                d = json.load(f)
        except Exception:
            return False
        try:
            song = d.get('song') or {}
            lines = d.get('lines') or []
            # ⚠️ v1.4.6：缓存可能已被上一版污染（19:49 实锤 song='获取音乐地址失败'
            #    被写进 session）→ 恢复时同样丢弃错误包 = 顺手清洗脏缓存
            #    （下次 save_session 会重写干净值；本次宁可不显示也不显示错误串）。
            _nm = song.get('name') if isinstance(song, dict) else ''
            if is_error_text(_nm or ''):
                log('session restore blocked: error text in cached song %r' % (_nm,))
                song = {}
                lines = []
            with self.lock:
                if isinstance(song, dict) and song:
                    self.song = song
                    self.song_gen += 1
                if isinstance(lines, list) and lines:
                    # 存的是 list（JSON 无 tuple）→ 还原成内部元组结构
                    self.lines = [tuple(x) for x in lines]
                    # chars 里是 [t0,t1,ch] 的 list，也还原成 tuple
                    self.lines = [(a, b, c, e, [tuple(ch) for ch in (fc or [])])
                                  for (a, b, c, e, fc) in self.lines]
                    self.has_lyrics = True
                self.base_time = float(d.get('time') or 0)
                self.base_ts = time.time()
                self.is_playing = False      # ⚠️ 恢复态一律按「暂停」显示：别让假进度继续走
            log('session restored: song=%r lines=%d time=%.1fs'
                % (song.get('name'), len(self.lines), self.base_time))
            return True
        except Exception as e:
            log('restore_session fail: %r' % e)
            return False

    def save_session(self, force=False):
        """把当前歌曲/歌词/进度落盘（节流：调用方可高频调，这里按时间间隔丢弃）。

        没连接播放器、或还没拿到歌词时不写——避免把「未知歌曲」空状态覆盖掉
        上次有效的那份缓存。"""
        try:
            now = time.time()
            if not force and now - getattr(self, '_sess_ts', 0) < 3.0:
                return
            with self.lock:
                song = dict(self.song) if self.song else {}
                lines = list(self.lines)
                t = self.base_time
            if not song and not lines:
                return
            self._sess_ts = now
            os.makedirs(APP_DIR, exist_ok=True)
            tmp = SESSION_F + '.tmp'
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump({'song': song, 'lines': lines, 'time': t,
                           'ts': now}, f, ensure_ascii=False)
            os.replace(tmp, SESSION_F)     # 原子替换，避免写一半崩了留下坏文件
        except Exception as e:
            log('save_session fail: %r' % e)

    def apply_state(self, is_playing, current_time):
        with self.lock:
            old_play = self.is_playing
            old_time = self.base_time
            now = time.time()
            new_time = float(current_time or 0)
            # ⚠️⚠️【v1.7.12 修复「暂停时灵动岛把上一句又伸缩一遍」】⚠️⚠️
            #   现象（用户）：暂停时，**歌词快**的歌里，岛上还会把**上一句**的歌词
            #   再伸缩一遍。
            #   机理：播放期间本程序靠 `now() = base_time + 已过时间` **自己外推**，
            #   而 MoeKoe 只在 play/pause 事件推一次 `playerState`
            #   （electron/main.js 的 `play-pause-action` → `apiService.updatePlayerState`，
            #   全项目只有这一处；播放中另有 ~250ms 一次的 `server-lyrics` 帮忙对齐）。
            #   暂停那一刻上报的 `audio.currentTime` 可能比本程序的外推值**略早**
            #   （采样→IPC 延迟 + 250ms 重同步节拍）。快歌每句只有几百 ms，
            #   这点回跳就足够跨过句界 → 岛上退回上一句 → 换句状态机**又播一轮**
            #   「收缩→展开」，肉眼就是「上一句被又伸缩了一遍」。
            #   处置：从「播放→暂停」这一步，进度取二者**较大**值（歌词时钟只前不后）。
            #   差值上限 0.75s：超过就说明用户真的往回拖了进度（seek），必须照实接受
            #   —— 另外「暂停中再跳转」不属于本条（old_play 已是 False），照常生效。
            extrap = old_time + (now - self.base_ts)
            if old_play and not is_playing and new_time < extrap \
                    and (extrap - new_time) <= 0.75:
                new_time = extrap
            # ⚠️⚠️【v1.7.22 歌词持有窗口】⚠️⚠️
            #   进度**大幅回跳**（>1s）= 换歌/回跳 seek 的唯一可靠信号
            #   （playerState 包不带歌曲标识，无法直接知道换歌）。
            #   换歌形态：旧歌已放到 ~200s，下一首从 ≈0 开始 → 必触发；
            #   误伤面：同歌内回跳 seek >1s → 只冻 ≤250ms（下个 server-lyrics
            #   包就解冻），视觉为「显示停一拍」，可接受。
            #   冻结值取回跳**前**的外推进度 → 屏上画面与回跳前完全一致。
            if current_time is not None and new_time < old_time - 1.0:
                self.lyric_hold = True
                self.hold_time = extrap
                self.hold_ts = now
                log('lyric hold: time jumped back %.1fs (%.1f→%.1f) → freeze display'
                    % (old_time - new_time, old_time, new_time))
            self.is_playing = bool(is_playing)
            self.base_time = new_time
            self.base_ts = now
            self.last_state_ts = self.base_ts
            if old_play != self.is_playing or abs(old_time - self.base_time) > 0.25:
                self.control_gen += 1
        self.save_session()          # 播放进度变化 → 缓存（内部节流 3s）

    def apply_lyrics(self, data):
        with self.lock:
            self.base_time = float(data.get('currentTime') or 0)
            self.base_ts = time.time()
            raw = data.get('lyricsData')
            song = data.get('currentSong')
            # ⚠️ 错误串防污染（v1.4.6）：播放器取歌失败时会把错误文案当歌名推来，
            #    此时**整包丢弃**（不覆盖当前有效状态、不写 session）——
            #    否则「获取音乐地址失败」会被当成歌名画在任务栏上（用户截图实锤）。
            if isinstance(song, dict) and is_error_text(song.get('name') or ''):
                log('lyrics blocked: error text in song name %r' % (song.get('name'),))
                return
            changed = False
            if isinstance(song, dict) and song:
                if json.dumps(song, ensure_ascii=False, sort_keys=True) != json.dumps(self.song, ensure_ascii=False, sort_keys=True):
                    self.song = song
                    self.song_gen += 1
                    self.control_gen += 1
                    changed = True
                    # ⚠️ v1.7.22：歌真的换了 → **旧歌词已失效**。本包若没带新歌词
                    #    （raw 为空），旧 lines 必须丢弃——否则显示层拿旧歌词 +
                    #    新进度（≈0）会匹配出上一首第 0 句（切歌「多跳一次」的
                    #    第二形态：无歌词/慢歌词歌曲）。同时解冻持有。
                    if not (isinstance(raw, str) and raw.strip()):
                        self.lines = []
                        self.has_lyrics = False
                    self.lyric_hold = False
            if isinstance(raw, str) and raw.strip():
                # 翻译始终解析出来，「是否显示」由绘制时决定（切换开关无需等下次推送）
                self.lines = parse_krc(raw, translation=True)
                self.has_lyrics = bool(self.lines)
                self.control_gen += 1
                changed = True
                self.lyric_hold = False      # v1.7.22：新歌词到手 → 解冻
            elif isinstance(raw, list) and not raw:
                self.lines = []
                self.has_lyrics = False
                self.lyric_hold = False      # v1.7.22：明确无歌词 → 解冻（显示歌名）
            if changed:
                n = len(self.lines)
                if n != getattr(self, '_logged_n', -1):
                    self._logged_n = n
                    log('lyrics applied: lines=%d' % n)
        self.save_session()          # 有新数据就顺手存一份（内部节流）

STATE = PlayerState()
CFG = load_cfg()
STATE.restore_session()          # ⭐ 启动即回放上次的歌曲/歌词（避免首屏「未知歌曲」）

# ---------------- KRC 解析 ----------------
def parse_krc(text, translation=True):
    lines_out = []
    translations = []
    if translation:
        m = re.search(r'\[language:([^\]]*)\]', text)
        if m:
            try:
                b64 = re.sub(r'[^A-Za-z0-9+/=]', '', m.group(1))
                b64 = b64 + '=' * ((4 - len(b64) % 4) % 4)
                lang = json.loads(base64.b64decode(b64).decode('utf-8', 'replace'))
                for sec in lang.get('content', []):
                    if sec.get('type') == 1:
                        translations = sec.get('lyricContent') or []
                        break
            except Exception:
                translations = []
    char_re = re.compile(r'<(\d+),(\d+),\d+>([^<]+)')
    for line in text.splitlines():
        lm = re.match(r'^\[(\d+),(\d+)\](.*)$', line)
        if not lm:
            continue
        start = int(lm.group(1))
        dur = int(lm.group(2))
        content = lm.group(3)
        matches = list(char_re.finditer(content))
        if not matches:
            body = re.sub(r'<[^>]*>', '', content)
            if body.strip():
                lines_out.append((start, start + dur, body, '', []))
            continue
        body = ''.join(m3.group(3) for m3 in matches)
        if not body.strip():
            continue
        chars = []
        t0 = start
        for m3 in matches:
            cs, cd, ch = int(m3.group(1)), int(m3.group(2)), m3.group(3)
            chars.append((t0, t0 + max(cd, 1), ch))
            t0 += cd
        trans = ''
        idx = len(lines_out)
        if idx < len(translations) and translations[idx]:
            t = translations[idx]
            trans = t[0] if isinstance(t, (list, tuple)) else str(t)
        lines_out.append((start, start + max(dur, 1), body, trans, chars))
    lines_out.sort(key=lambda x: x[0])
    return lines_out

def current_line(lines, t_ms):
    if not lines:
        return -1, None, None
    for i, ln in enumerate(lines):
        if ln[0] <= t_ms < ln[1]:
            return i, ln, lines[i + 1] if i + 1 < len(lines) else None
    prev = None
    for i, ln in enumerate(lines):
        if ln[1] <= t_ms:
            prev = i
        else:
            break
    if prev is not None and prev + 1 < len(lines):
        return prev, lines[prev], lines[prev + 1]
    if prev is not None:
        return prev, lines[prev], None
    return -1, None, lines[0] if lines else None

# ---------------- WS 客户端 ----------------
class WSClient(threading.Thread):
    daemon = True
    def run(self):
        while True:
            try:
                self._session()
            except Exception as e:
                log('ws session end: %r' % e)
            STATE.connected = False
            time.sleep(3)

    def _connect(self):
        s = socket.create_connection((WS_HOST, WS_PORT), timeout=5)
        key = base64.b64encode(os.urandom(16)).decode()
        req = ("GET / HTTP/1.1\r\nHost: %s:%d\r\nUpgrade: websocket\r\n"
               "Connection: Upgrade\r\nSec-WebSocket-Key: %s\r\n"
               "Sec-WebSocket-Version: 13\r\n\r\n" % (WS_HOST, WS_PORT, key))
        s.sendall(req.encode())
        resp = b''
        while b'\r\n\r\n' not in resp:
            d = s.recv(4096)
            if not d:
                raise RuntimeError('handshake closed')
            resp += d
        return s, resp.split(b'\r\n\r\n', 1)[1]

    def _session(self):
        s, leftover = self._connect()
        s.settimeout(2.0)
        STATE.connected = True
        log('ws connected')
        self._buf = leftover
        last_ping = time.time()
        while True:
            try:
                msg = self._read_frame(s)
            except socket.timeout:
                if time.time() - last_ping > 20:
                    try:
                        s.sendall(bytes(bytearray([0x89, 0x80]) + b'\x00' * 4))
                        last_ping = time.time()
                    except Exception:
                        raise RuntimeError('ping failed')
                continue
            if msg is None:
                continue
            try:
                j = json.loads(msg)
            except Exception:
                continue
            t = j.get('type')
            if t == 'playerState':
                d = j.get('data') or {}
                STATE.apply_state(d.get('isPlaying'), d.get('currentTime'))
            elif t == 'lyrics':
                STATE.apply_lyrics(j.get('data') or {})
            elif t == 'error':
                log('server error: %r' % (j.get('data'),))

    def _read_frame(self, s):
        buf = self._buf
        need = 2
        while len(buf) < need:
            d = s.recv(65536)
            if not d: raise EOFError
            buf += d
        b1, b2 = buf[0], buf[1]
        opcode = b1 & 0x0F
        ln = b2 & 0x7F
        off = 2
        if ln == 126:
            need = 4
            while len(buf) < need:
                d = s.recv(65536)
                if not d: raise EOFError
                buf += d
            ln = int.from_bytes(buf[2:4], 'big'); off = 4
        elif ln == 127:
            need = 10
            while len(buf) < need:
                d = s.recv(65536)
                if not d: raise EOFError
                buf += d
            ln = int.from_bytes(buf[2:10], 'big'); off = 10
        if b2 & 0x80:
            off += 4
        need = off + ln
        while len(buf) < need:
            d = s.recv(65536)
            if not d: raise EOFError
            buf += d
        payload = buf[off:off + ln]
        self._buf = buf[off + ln:]
        if opcode == 8:
            raise EOFError('close frame')
        if opcode in (9, 10):
            return None
        if opcode in (1, 2):
            return payload.decode('utf-8', 'replace')
        return None

def _ws_text_frame(payload):
    data = payload.encode('utf-8') if isinstance(payload, str) else bytes(payload)
    h = bytearray([0x81])
    n = len(data)
    if n < 126:
        h.append(0x80 | n)
    elif n < 65536:
        h.append(0x80 | 126)
        h += n.to_bytes(2, 'big')
    else:
        h.append(0x80 | 127)
        h += n.to_bytes(8, 'big')
    mask = os.urandom(4)
    h += mask
    return bytes(h) + bytes(b ^ mask[i % 4] for i, b in enumerate(data))

def _read_ws_text_frame(sock, buf=b''):
    while len(buf) < 2:
        d = sock.recv(65536)
        if not d:
            raise EOFError
        buf += d
    b1, b2 = buf[0], buf[1]
    opcode = b1 & 0x0F
    ln = b2 & 0x7F
    off = 2
    if ln == 126:
        while len(buf) < 4:
            d = sock.recv(65536)
            if not d:
                raise EOFError
            buf += d
        ln = int.from_bytes(buf[2:4], 'big')
        off = 4
    elif ln == 127:
        while len(buf) < 10:
            d = sock.recv(65536)
            if not d:
                raise EOFError
            buf += d
        ln = int.from_bytes(buf[2:10], 'big')
        off = 10
    masked = bool(b2 & 0x80)
    mask = b''
    if masked:
        while len(buf) < off + 4:
            d = sock.recv(65536)
            if not d:
                raise EOFError
            buf += d
        mask = buf[off:off + 4]
        off += 4
    while len(buf) < off + ln:
        d = sock.recv(65536)
        if not d:
            raise EOFError
        buf += d
    payload = buf[off:off + ln]
    rest = buf[off + ln:]
    if masked and mask:
        payload = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
    if opcode == 8:
        raise EOFError('close frame')
    if opcode in (9, 10):
        return None, rest
    if opcode in (1, 2):
        return payload.decode('utf-8', 'replace'), rest
    return None, rest

def _apply_ws_message(msg):
    try:
        j = json.loads(msg)
    except Exception:
        return None
    t = j.get('type')
    if t == 'playerState':
        d = j.get('data') or {}
        STATE.apply_state(d.get('isPlaying'), d.get('currentTime'))
    elif t == 'lyrics':
        STATE.apply_lyrics(j.get('data') or {})
    elif t == 'error':
        log('server error: %r' % (j.get('data'),))
    return t

def _control_snapshot():
    with STATE.lock:
        return (bool(STATE.is_playing),
                int(getattr(STATE, 'song_gen', 0)),
                int(getattr(STATE, 'control_gen', 0)),
                float(getattr(STATE, 'base_time', 0.0) or 0.0))

def _control_changed(cmd, before, after):
    bp, bs, bg, bt = before
    ap, a_s, ag, at = after
    if cmd == 'toggle':
        return ap != bp
    if cmd in ('prev', 'next'):
        return a_s != bs or ag != bg or abs(at - bt) > 1.0
    return ag != bg

def _wait_control_change(cmd, before, timeout=1.15):
    deadline = time.time() + timeout
    while time.time() < deadline:
        after = _control_snapshot()
        if _control_changed(cmd, before, after):
            return True
        time.sleep(0.05)
    return False

def moekoe_control(cmd, timeout=1.25):
    """MoeKoe Music 专用控制接口：握手 → 监听状态 → 发命令 → 观察变化。

    这条路径对齐 MoeKoe 主程序的 control 接口，不依赖系统媒体会话是否已经
    注册，也不要求播放器已经出过声，专门解决“第一次打开主程序三键没反应”。
    """
    if cmd not in ('toggle', 'next', 'prev'):
        return False
    before = _control_snapshot()
    sock = None
    buf = b''
    try:
        sock, leftover = WSClient()._connect()
        sock.settimeout(0.18)
        buf = leftover or b''

        # 先吃几帧初始状态，确认对端不是只有端口而没有播放器监听。
        warm_until = time.time() + 0.35
        got_state = False
        while time.time() < warm_until:
            try:
                msg, buf = _read_ws_text_frame(sock, buf)
            except socket.timeout:
                break
            if msg:
                got_state = _apply_ws_message(msg) in ('playerState', 'lyrics') or got_state

        payload = json.dumps({'type': 'control',
                              'data': {'command': cmd}},
                             ensure_ascii=False)
        sock.sendall(_ws_text_frame(payload))
        log('moekoe control %s -> sent (warm_state=%s)' % (cmd, got_state))

        deadline = time.time() + timeout
        sock.settimeout(0.12)
        while time.time() < deadline:
            if _wait_control_change(cmd, before, timeout=0.05):
                log('moekoe control %s -> observed state change' % cmd)
                return True
            try:
                msg, buf = _read_ws_text_frame(sock, buf)
            except socket.timeout:
                continue
            if msg:
                _apply_ws_message(msg)
                if _control_changed(cmd, before, _control_snapshot()):
                    log('moekoe control %s -> observed ws frame' % cmd)
                    return True
        log('moekoe control %s -> no observed change' % cmd)
        return False
    except Exception as e:
        log('moekoe control %s fail: %r' % (cmd, e))
        return False
    finally:
        try:
            if sock:
                sock.close()
        except Exception:
            pass

# ---------------- SMTC（系统媒体控制）----------------
# ⚠️ 真机教训（debug.log 实证，v1.4.5）：
#     旧实现每次调用都 `asyncio.new_event_loop()` + `run_until_complete()`。
#     实测在灵动岛跑了一会儿、且**别的线程也碰过 winrt** 之后，就会开始报
#         RuntimeError('Cannot run the event loop while another loop is running')
#     于是 smtc_control 永远返回 False，所有控制都退回 WS。
#     症状正是用户说的「第一次打开 MoeKoe 时按任务栏三键按不动」。
#     根因：winrt 的 WinRT/COM 异步设施第一次使用时会绑定到当时的线程/loop，
#     之后每次新建 loop 去驱动它就会打架。
#     修法：**常驻一个 worker 线程 + 一个长生命周期的 event loop**，
#     所有 SMTC 调用都投递到这个 loop 上执行（串行化，天然无竞态）。
_SMTC_LOCK = threading.Lock()
_SMTC_LOOP = None
_SMTC_READY = threading.Event()
_SMTC_IMPORT_FAIL = None


def _smtc_worker():
    """常驻 worker：一个 loop 跑到底，所有 SMTC 请求都在这里执行。"""
    global _SMTC_LOOP
    try:
        lp = asyncio.new_event_loop()
    except Exception as e:                       # pragma: no cover
        log('smtc worker loop fail: %r' % e)
        _SMTC_READY.set()
        return
    _SMTC_LOOP = lp
    asyncio.set_event_loop(lp)
    _SMTC_READY.set()
    try:
        lp.run_forever()
    except Exception as e:                       # pragma: no cover
        log('smtc worker crashed: %r' % e)


def _smtc_ensure_worker():
    """惰性启动 worker（首次用到才起，别拖慢启动）。"""
    with _SMTC_LOCK:
        if _SMTC_LOOP is not None and _SMTC_LOOP.is_running():
            return True
        if _SMTC_READY.is_set() and _SMTC_LOOP is None:
            return False                         # 起过了但失败了，别反复起
        threading.Thread(target=_smtc_worker, name='smtc-worker',
                         daemon=True).start()
    return _SMTC_READY.wait(5.0)


def _smtc_import():
    """惰性 import winrt；失败缓存结果，不要每次都抛。"""
    global _SMTC_IMPORT_FAIL
    if _SMTC_IMPORT_FAIL is not None:
        return None
    try:
        from winrt.windows.media.control import (
            GlobalSystemMediaTransportControlsSessionManager as _Mgr)
        return _Mgr
    except Exception as e:
        _SMTC_IMPORT_FAIL = e
        log('smtc import fail: %r' % e)
        return None


def smtc_control(cmd, timeout=3.0):
    """用 Windows SMTC（系统媒体控制）遥控播放器。

    MoeKoe Music 会在 SMTC 注册会话（app id = cn.MoeKoe.Music），
    但**只在它真的出过声之后**才注册；刚启动/没播放过时 sessions 为空，
    这时本函数返回 False，由 ws_control 继续走 WS 兜底——这是设计，不是故障。

    返回 True = 命令已被 SMTC 接受；False = 没有可用会话或执行失败。
    """
    _Mgr = _smtc_import()
    if _Mgr is None:
        return False
    if not _smtc_ensure_worker():
        log('smtc worker not ready')
        return False

    async def _run():
        mgr = await _Mgr.request_async()
        sessions = mgr.get_sessions()
        target = None
        for s in sessions:                       # 优先精确匹配 MoeKoe
            try:
                aid = (s.source_app_user_model_id or '')
            except Exception:
                aid = ''
            if 'moekoe' in aid.lower():
                target = s
                break
        if target is None and sessions.size:
            target = sessions[0]                 # 只有一个播放器时直接用
        if target is None:
            return False
        if cmd == 'toggle':
            return await target.try_toggle_play_pause_async()
        if cmd == 'next':
            return await target.try_skip_next_async()
        if cmd == 'prev':
            return await target.try_skip_previous_async()
        return False

    box = {}
    done = threading.Event()

    def _submit():
        try:
            fut = _SMTC_LOOP.create_task(_run())
        except Exception as e:                   # loop 已关 / 线程没了
            box['err'] = e
            done.set()
            return

        def _fin(f):
            try:
                box['ok'] = f.result()
            except Exception as e:
                box['err'] = e
            done.set()
        fut.add_done_callback(_fin)

    try:
        _SMTC_LOOP.call_soon_threadsafe(_submit)
    except Exception as e:
        log('smtc submit fail: %r' % e)
        return False

    if not done.wait(timeout):
        log('smtc control timeout (%s)' % cmd)
        return False
    if 'err' in box:
        log('smtc control fail: %r' % box['err'])
        return False
    return bool(box.get('ok'))

def send_media_key(cmd):
    """最后兜底：模拟系统媒体键（VK_MEDIA_*），走 Windows 媒体键链"""
    vk = {'prev': 0xB1, 'toggle': 0xB3, 'next': 0xB0}.get(cmd)
    if vk is None:
        return False
    try:
        u = ctypes.windll.user32
        u.keybd_event(vk, 0, 0, 0)
        u.keybd_event(vk, 0, 0x0002, 0)          # KEYEVENTF_KEYUP
        return True
    except Exception as e:
        log('media key fail: %r' % e)
        return False

def ws_control(cmd):
    """播放控制：MoeKoe 专用控制接口 → SMTC → 系统媒体键（逐级兜底）

    v1.6.8 起，先走 MoeKoe Music 的本地播放器控制接口：完整 WebSocket
    握手、监听 playerState/lyrics、发送 control，并观察状态是否变化。
    这样首次打开 MoeKoe Music、SMTC 尚未注册时，三键也能直接对齐主程序。
    """
    def _do():
        if moekoe_control(cmd):
            log('control %s -> MoeKoe interface ok' % cmd)
            return
        if smtc_control(cmd):
            log('control %s -> SMTC ok' % cmd)
            return
        if send_media_key(cmd):
            log('control %s -> media key' % cmd)
    threading.Thread(target=_do, daemon=True).start()

def taskbar_button_control(cmd):
    """任务栏三键专用：MoeKoe 接口优先，若状态没变化再逐级兜底。

    v1.6.8：任务栏按钮不再先模拟媒体键，而是先对齐 MoeKoe Music 主程序
    的播放/上一曲/下一曲接口，并用监听到的状态变化确认成功。失败时才
    走 SMTC / 媒体键。
    """
    def _do():
        if moekoe_control(cmd):
            log('tb control %s -> MoeKoe interface ok' % cmd)
            return
        before = _control_snapshot()
        if smtc_control(cmd) and _wait_control_change(cmd, before, timeout=0.75):
            log('tb control %s -> SMTC observed state change' % cmd)
            return
        if send_media_key(cmd):
            log('tb control %s -> media key fallback' % cmd)
    threading.Thread(target=_do, daemon=True).start()

# ---------------- 封面 ----------------
COVER_CACHE = {}
def load_cover_pixmap(song):
    if not isinstance(song, dict):
        return None
    url = None
    for k in ('cover', 'img', 'albumPic', 'pic', 'image'):
        v = song.get(k)
        if isinstance(v, str) and v.startswith('http'):
            url = v; break
        if isinstance(v, dict):
            v = v.get('url') or v.get('img')
            if isinstance(v, str) and v.startswith('http'):
                url = v; break
    if not url:
        imgs = song.get('images')
        if isinstance(imgs, list) and imgs:
            cand = imgs[-1]
            if isinstance(cand, str): url = cand
            elif isinstance(cand, dict): url = cand.get('url')
    if not url:
        return None
    if url in COVER_CACHE:
        return COVER_CACHE[url]
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        data = urllib.request.urlopen(req, timeout=10).read()
        pm = QPixmap()
        pm.loadFromData(data)
        if not pm.isNull():
            COVER_CACHE[url] = pm
            if len(COVER_CACHE) > 30:
                COVER_CACHE.pop(next(iter(COVER_CACHE)))
            return pm
    except Exception as e:
        log('cover fetch fail: %r' % e)
    return None

def song_name_singer(song):
    """返回 (歌名, 歌手串)"""
    if not isinstance(song, dict):
        return None, None
    name = None
    for k in ('name', 'songName', 'filename', 'title', 'audioName'):
        v = song.get(k)
        if isinstance(v, str) and v.strip():
            name = v.strip(); break
    singer = None
    for k in ('author', 'singerName', 'author_name', 'singer', 'SingerName', 'artists'):
        v = song.get(k)
        if isinstance(v, str) and v.strip():
            singer = v.strip(); break
        if isinstance(v, list) and v:
            names = []
            for it in v:
                if isinstance(it, str): names.append(it)
                elif isinstance(it, dict):
                    n = it.get('name') or it.get('author_name')
                    if n: names.append(n)
            if names:
                singer = ' / '.join(names); break
    # 多歌手统一成「A / B / C」排布（MoeKoe 常见 "A/B/C" 紧贴写法）
    if singer and ' / ' not in singer:
        for sep in ('/', '、', '&', ';'):
            if sep in singer:
                ps = [x.strip() for x in singer.split(sep) if x.strip()]
                if len(ps) > 1:
                    singer = ' / '.join(ps)
                break
    return name, singer

def song_text(song):
    name, singer = song_name_singer(song)
    if name and singer:
        return '%s - %s' % (name, singer)
    return name or singer or 'MoeKoe Music'

def make_default_cover(size):
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    p.setBrush(QColor('#222222'))
    p.setPen(Qt.NoPen)
    p.drawEllipse(2, 2, size - 4, size - 4)
    p.setBrush(QColor('#3a7bd5'))
    p.drawEllipse(size // 2 - size // 5, size // 2 - size // 5, int(size / 2.5), int(size / 2.5))
    p.setBrush(QColor('#101010'))
    p.drawEllipse(size // 2 - 3, size // 2 - 3, 6, 6)
    p.end()
    return pm

def _global_mouse():
    """返回 (x, y, 左键按下, 右键按下)——不依赖 Qt 事件分发"""
    u = ctypes.windll.user32
    pt = wt.POINT()
    u.GetCursorPos(ctypes.byref(pt))
    return (pt.x, pt.y,
            bool(u.GetAsyncKeyState(0x01) & 0x8000),
            bool(u.GetAsyncKeyState(0x02) & 0x8000))

def make_default_square(size):
    """默认方形封面（深色渐变 + 唱片纹），用于没有封面时"""
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    grad = QLinearGradient(0, 0, size, size)
    grad.setColorAt(0.0, QColor('#3a3f4b'))
    grad.setColorAt(1.0, QColor('#1b1e26'))
    p.setPen(Qt.NoPen)
    p.setBrush(QBrush(grad))
    p.drawRoundedRect(QRectF(0, 0, size, size), size * 0.22, size * 0.22)
    p.setBrush(QColor(255, 255, 255, 42))
    p.drawEllipse(QPointF(size / 2, size / 2), size * 0.17, size * 0.17)
    p.setBrush(QColor(255, 255, 255, 70))
    p.drawEllipse(QPointF(size / 2, size / 2), size * 0.05, size * 0.05)
    p.end()
    return pm

def rounded_cover(cover_pm, size, radius):
    """圆角方形封面图"""
    key = ('rounded', id(cover_pm), size, radius)
    cached = COVER_CACHE.get(key)
    if cached is not None:
        return cached
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    p.setRenderHint(QPainter.SmoothPixmapTransform)
    path = QPainterPath()
    path.addRoundedRect(0.5, 0.5, size - 1, size - 1, radius, radius)
    p.setClipPath(path)
    scaled = cover_pm.scaled(size, size, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
    p.drawPixmap(0, 0, scaled)
    p.setClipping(False)
    pen = QPen(QColor(0, 0, 0, 60)); pen.setWidthF(1.0)
    p.setPen(pen); p.setBrush(Qt.NoBrush)
    p.drawRoundedRect(QRectF(0.5, 0.5, size - 1, size - 1), radius, radius)
    p.end()
    COVER_CACHE[key] = pm
    return pm

# ---------------- 共享绘制 ----------------
def draw_pill(p, rect, radius, bg1=None, bg2=None, border=None):
    if bg1 is None or bg2 is None:
        c = island_colors()
        bg1, bg2 = c['bg1'], c['bg2']
    if border is None:
        border = QColor(255, 255, 255, 30)
    path = QPainterPath()
    path.addRoundedRect(rect, radius, radius)
    grad = QLinearGradient(rect.topLeft(), rect.bottomLeft())
    grad.setColorAt(0.0, bg1)
    grad.setColorAt(1.0, bg2)
    p.fillPath(path, QBrush(grad))
    # 顶部一道内高光（SPlayer 同款手法）：让深色胶囊有「玻璃/曲面」的立体感，
    # 避免纯色平面看起来像贴纸。用 clipPath 把高光限制在圆角内。
    p.save()
    p.setClipPath(path)
    hl = QLinearGradient(rect.topLeft(), QPointF(rect.left(), rect.top() + rect.height() * 0.55))
    hl.setColorAt(0.0, QColor(255, 255, 255, 26))
    hl.setColorAt(1.0, QColor(255, 255, 255, 0))
    p.fillRect(QRectF(rect.left(), rect.top(), rect.width(), rect.height() * 0.55), QBrush(hl))
    p.restore()
    pen = QPen(border); pen.setWidthF(1.0)
    p.setPen(pen); p.setBrush(Qt.NoBrush)
    p.drawPath(path)

def draw_soft_shadow(p, rect, radius):
    """分层圆角矩形近似柔和投影（避免 QGraphicsEffect 的稳定性问题）。"""
    p.setPen(Qt.NoPen)
    steps = ((16, 10), (12, 15), (9, 20), (6, 25), (4, 28), (2, 30))
    for inset, alpha in steps:
        r = rect.adjusted(inset - 2, inset, -(inset - 2), -inset + 3)
        path = QPainterPath()
        path.addRoundedRect(r, max(6, radius - inset), max(6, radius - inset))
        p.fillPath(path, QColor(0, 0, 0, alpha))

def draw_disc(p, center_x, center_y, size, angle, cover_pm):
    disc = QPixmap(size, size)
    disc.fill(Qt.transparent)
    dp = QPainter(disc)
    dp.setRenderHint(QPainter.Antialiasing)
    dp.setRenderHint(QPainter.SmoothPixmapTransform)
    clip = QPainterPath()
    clip.addEllipse(1, 1, size - 2, size - 2)
    dp.setClipPath(clip)
    t = QTransform()
    t.translate(size / 2, size / 2)
    t.rotate(angle)
    t.translate(-size / 2, -size / 2)
    scaled = cover_pm.scaled(size, size, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
    dp.setTransform(t, True)
    dp.drawPixmap(0, 0, scaled)
    dp.setClipping(False)
    pen = QPen(QColor(0, 0, 0, 200)); pen.setWidthF(2.0)
    dp.setPen(pen); dp.setBrush(Qt.NoBrush)
    dp.drawEllipse(QPointF(size / 2, size / 2), size / 2 - 1, size / 2 - 1)
    pen2 = QPen(QColor(255, 255, 255, 46)); pen2.setWidthF(1.6)
    dp.setPen(pen2)
    dp.drawArc(QRectF(3, 3, size - 6, size - 6), 30 * 16, 80 * 16)
    dp.end()
    p.drawPixmap(int(center_x - size / 2), int(center_y - size / 2), disc)
    p.setBrush(QColor(10, 10, 12, 235)); p.setPen(Qt.NoPen)
    p.drawEllipse(QPointF(center_x, center_y), 3.0, 3.0)

def draw_play_icons(p, i, r, col, playing, s=7.0):
    """i: 0=prev 1=play/pause 2=next"""
    p.setPen(Qt.NoPen)
    p.setBrush(col)
    cx, cy = r.center().x(), r.center().y()
    if i == 0:
        p.drawRect(QRectF(cx - s, cy - s, 2.4, s * 2))
        p.drawPolygon(QPolygonF([QPointF(cx + s, cy - s * 0.82),
                                 QPointF(cx - s + 3.0, cy),
                                 QPointF(cx + s, cy + s * 0.82)]))
    elif i == 1:
        if playing:
            p.drawRect(QRectF(cx - s * 0.62, cy - s, 3.2, s * 2))
            p.drawRect(QRectF(cx + s * 0.22, cy - s, 3.2, s * 2))
        else:
            p.drawPolygon(QPolygonF([QPointF(cx - s * 0.6, cy - s * 0.95),
                                     QPointF(cx + s * 0.95, cy),
                                     QPointF(cx - s * 0.6, cy + s * 0.95)]))
    else:
        p.drawRect(QRectF(cx + s - 2.4, cy - s, 2.4, s * 2))
        p.drawPolygon(QPolygonF([QPointF(cx - s, cy - s * 0.82),
                                 QPointF(cx + s - 3.0, cy),
                                 QPointF(cx - s, cy + s * 0.82)]))

# ================================================================
# 灵动岛
# ================================================================
class Island(QWidget):
    # compact 版式：紧凑单行（当前句有译文时自动撑成 DUAL 的两行）
    # 参数对标 SPlayer Next：圆角取高度一半（真胶囊）、封面缩小、左右留白加大
    INFO  = dict(H=50, DISC=34, TEXT_W=330, PAD=16, RADIUS=25)
    # dual 版式：双行（歌词 + 翻译/下一句）
    DUAL  = dict(H=66, DISC=42, TEXT_W=340, PAD=17, RADIUS=33)
    # 宽度自适应区间（对标 SPlayer：岛会随歌词长短伸缩，短句收窄、长句展开）
    TEXT_W_MIN, TEXT_W_MAX = 120, 720

    # ============ v1.7.20：「抖动」的**结构性**根治 —— 窗口几何刚性化 ============
    #   ⚠️⚠️ 需求原文（2026-10-10 第三次反馈）：
    #        「灵动岛歌词展开的时候歌词依然还是会有抖动，要做到无抖动」⚠️⚠️
    #
    #   【前三次为什么都没治好】
    #     v1.7.17 改展开曲线（治「震动」）→ 引入「闪动」；
    #     v1.7.18 改曲线形状（治「闪动」）→ 抖动仍在；
    #     v1.7.19 把文字原点改成「屏幕绝对坐标下取整一次」→ **仍然抖，而且更明显**。
    #     原因是 v1.7.19 的验收脚本本身是**同义反复**：它记录的是 `round(abs_x)`
    #     （解析上恒定的目标值），又把 `self.x()` 加回去再减掉 —— 等于自己把
    #     「窗口真实位置」这个唯一变量消掉了，所以它永远 PASS。
    #
    #   【真凶（probe_desync.py 真屏取证，2026-10-10）】
    #     每帧取两次真屏截图：`tick()` 之后立刻抓（重绘尚未提交）vs 强制
    #     `repaint()` 之后再抓，求两者 ink 掩码的最佳配准位移：
    #         Δgx = -36 → 配准 -36      Δgx = +55 → 配准 +55
    #         Δgx = -25 → 配准 -25      Δgx = +36 → 配准 +36
    #         Δgx = -17 → 配准 -17      Δgx = +22 → 配准 +22   …（38/73 帧非零）
    #     **配准位移恰好 = 本帧窗口位移 Δgx**。也就是说：
    #       `move()` 是**立即**生效的（SetWindowPos 同步改窗口矩形），
    #       而重绘要等事件循环、且本身要 5~15ms 才能提交（CJK 冷栅格化很贵）——
    #       于是每帧都有一段时间：**窗口已经跳到位、画布还是上一帧的内容**，
    #       整块文字被顶偏 Δgx（实测单帧最大 55px）。60fps 下这就是肉眼看到的「抖动」。
    #     （已被独立证据交叉验证：618/618 帧 `Qt.x/y` == Win32 `GetWindowRect`，
    #      说明窗口位置本身是准的，问题只在「移动」与「重绘」的时序。）
    #
    #     而 v1.7.19 恰好把这件事**放大**了：它让文字去反向补偿窗口位移，
    #     于是「陈旧帧」的偏移量从「半个宽度差」变成了「整个窗口位移」。
    #
    #   【修法】不再让窗口在动画里移动 —— **窗口几何全程刚性**
    #     · 窗口宽度恒按**最大槽宽**（TEXT_W_MAX）预留，位置恒为其中心，
    #       换句伸缩期间**一次** `setFixedSize/move` 都不发生；
    #     · 胶囊在窗口内**居中绘制**（`_pill_left_local()`），窗口不动、胶囊照样
    #       左右对称生长 —— 屏幕上的观感与之前完全一致；
    #     · 于是「重绘迟交」的最坏后果退化为「屏幕上重复了上一帧」——
    #       而重复上一帧是**任何一帧都合法的连续画面**，不可能产生位移 → 抖动消失。
    #       （这同时干掉了动画中「窗口移动」「窗口改尺寸」两条时序路径。）
    #     · 多出来的透明区域本来是「会吃掉点击」的，因此配套加 `WM_NCHITTEST`
    #       逐点命中（`nativeEvent`）：只有**胶囊实心区**收点击，其余一律
    #       `HTTRANSPARENT` 穿透 —— 与任务栏组件同一套成熟做法。
    #
    #   【回退】把 `RIGID_WIN` 置 False 即完整恢复 v1.7.19 行为
    #     （窗口贴住胶囊、每帧 move；那段代码路径原样保留）。
    RIGID_WIN = True

    # ============ v1.7.21：暂停 = **全静止**（用户 2026-10-10 第四次暂停反馈）============
    #   「这个灵动岛暂停的时候它会跳一下才静止，暂停的时候灵动岛要做到全静止状态」
    #   `probe_pause.py` 六场景取证，暂停瞬间的跳变源共 **4 个**（都已消除）：
    #     ① 普通歌词行的 '‖ ' 前缀注入（paintEvent）—— 一帧 625px 像素突跳；
    #     ② 无歌词兜底标题的 '‖ ' 前缀（_want_texts）—— 一帧 4850px（整句文本变化）；
    #     ③ 收缩中途暂停 → 「立刻落位」—— 槽宽 88→259 一帧突跳 170.8px；
    #     ④ 跑马灯滚动中暂停 → 偏移瞬间跳到 travel（v1.4.3 的「暂停整句可见」特判）。
    #   新语义：
    #     · 暂停不注入任何前缀、不落位、不跳 travel；卡拉OK高亮/滚动位置原位冻结；
    #     · 正在飞的收缩/展开自然跑完（连续运动、跑完即静止）；
    #     · 暂停中空闲态下文本真的变了（暂停中拖进度/换歌）→ 仍落位（唯一例外）。
    #   【回退】逐处还原即可：①② 恢复 `'‖ '` 拼接、③ 恢复
    #     `if not playing and (shrink or changed): _settle_swap(...)`、
    #     ④ 恢复 `_marq_off` 里的 `if not STATE.is_playing: return travel`。

    def __init__(self):
        super().__init__()
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint |
                            Qt.Tool | Qt.NoDropShadowWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.drag_pos = None
        self.angle = 0
        # SPlayer 式跑马灯时钟（与播放进度解耦）
        self._marq_t = 0.0       # 当前行已滚动时长（ms）
        self._marq_last = time.time()
        self._marq_sig = None    # 相位失效标识
        self._marq_body = None   # 当前滚动正文
        self.cover_pm = None
        self.cover_gen = -1
        self.default_cover = make_default_cover(92)
        self.default_square = make_default_square(96)
        self.COVER_R = 10        # 方形封面圆角
        # ---- SPlayer 式换句伸缩（v1.7.7）----
        #   phase: 'idle' | 'shrink'（宽度 → 0，同步淡出）| 'expand'（0 → 新宽度，回弹过冲）
        #   ⚠️ 必须在 _apply_metrics() 之前初始化 —— 那里会读 _swap_phase/_slot_*
        self._swap_phase = 'idle'
        self._swap_t0 = 0.0
        self._swap_from = 0.0          # 收缩起点宽度
        self._slot_w = 0.0             # 当前渲染的歌词槽宽度（动画量）
        self._slot_target = 0.0        # 目标歌词槽宽度
        self._disp_main = None         # 屏上正在显示的主行文本
        self._disp_sub = ''            # 屏上正在显示的副行文本
        self._disp_line = None         # 屏上正在显示的歌词行对象（卡拉OK用）
        self._swap_pending = None      # 收缩期间记下的「最新目标文本」
        # 兼容旧测试/旧代码引用的字段（已不再驱动动画）
        self._stretch_t0 = 0.0
        self._stretch_from = None
        self._stretch_to = None
        self._target_text_w = None
        self._build_menu()
        self._apply_metrics()
        # 原生输入轮询（不依赖 Qt 事件分发）
        self.ndrag = None          # (gx, gy) 拖动中
        self._prev_l = False
        self._prev_r = False
        self.spin_timer = QTimer(self, interval=16, timeout=self.tick)
        self.spin_timer.start()
        self.input_timer = QTimer(self, interval=16, timeout=self._poll_input)
        self.input_timer.start()
        # 后台设置面板 / 托盘 / 插件下发的指令（跨线程安全：只往列表里塞字符串）
        self.cmd_timer = QTimer(self, interval=400, timeout=self._drain_commands)
        self.cmd_timer.start()
        # config.json 被外部改动时自动重新加载（手改配置 / 另一个进程写入都能生效）
        self._cfg_mtime = None
        self.cfg_timer = QTimer(self, interval=2000, timeout=self._watch_cfg_file)
        self.cfg_timer.start()

    def _metrics(self):
        return dict(self.DUAL if self._two_lines() else self.INFO)

    def _two_lines(self):
        """当前是否需要「双行高度」。
        - dual  版式：恒双行（第二行 = 翻译，没翻译时预看下一句）
        - compact 版式：只要开了翻译、且当前这句有译文，就自动撑成双行；
          否则保持紧凑单行。这样「紧凑」也不会漏掉翻译，
          无需用户手动去切版式（之前 compact 直接丢弃译文 = 不同步的根因）。"""
        if CFG.get('island_layout') == 'dual':
            return True
        if not CFG.get('show_translation', True):
            return False
        try:
            if not STATE.connected:
                return False
            with STATE.lock:
                lines = list(STATE.lines)
            if not lines:
                return False
            _, cur, _n = current_line(lines, STATE.now() * 1000.0)
        except Exception:
            return False
        return bool(cur is not None and (cur[3] or '').strip())

    def _font_size(self, delta=0):
        return max(7, int(CFG.get('island_font', 11)) + delta)

    def _slot_w_for(self, main, sub):
        """按**指定文本**实测歌词槽宽度（不含封面/左右留白）。

        为什么要把文本当参数传进来：换句动画期间 `STATE` 已经指向新的一句，
        而屏幕上还在显示旧的一句 —— 收缩阶段必须用「正在显示的那句」的宽度，
        否则收缩起点会瞬间跳到新宽度（就是用户看到的「硬跳」）。"""
        try:
            f_main = QFont('Microsoft YaHei UI', self._font_size(0))
            f_main.setWeight(QFont.DemiBold)
            f_sub = QFont('Microsoft YaHei UI', self._font_size(-3))
            widest = QFontMetrics(f_main).horizontalAdvance(main or '')
            if (sub or '').strip():
                widest = max(widest, QFontMetrics(f_sub).horizontalAdvance(sub))
            if widest <= 0:
                return float(self.INFO['TEXT_W'])
            # +6 余量避免贴边（省略/滚动判定留出呼吸）
            return float(max(self.TEXT_W_MIN, min(self.TEXT_W_MAX, widest + 6)))
        except Exception:
            return float(self.INFO['TEXT_W'])

    def _want_texts(self):
        """从 STATE 取出「此刻应该显示」的两行文本与行对象。"""
        try:
            with STATE.lock:
                playing = STATE.is_playing
                connected = STATE.connected
                lines = list(STATE.lines)
                song = dict(STATE.song) if STATE.song else {}
            cur = nxt = None
            if connected and lines:
                _, cur, nxt = current_line(lines, STATE.now() * 1000.0)
            if connected and cur is not None and (cur[2] or '').strip():
                main = cur[2]
                sub = self._sub_of(cur, nxt, CFG.get('island_layout') == 'dual')
                return main, sub, cur, playing
            # 无歌词 → 「歌名 - 歌手」；未连接 → 提示文案
            if not connected:
                txt = '未连接 MoeKoe Music · 请检查播放器'
            else:
                name = song.get('name') or ''
                singer = song.get('author') or ''
                txt = ('%s - %s' % (name, singer)) if (name and singer) \
                    else (name or singer or 'MoeKoe Music')
            # ⚠️ v1.7.21：去掉 '‖ ' 前缀（暂停全静止，同 paintEvent 处注释）——
            #    有前缀时暂停瞬间 `_want_texts` 的返回变化会触发落位，
            #    `_probe_pause.py` 实测标题兜底场景一帧 4850px 的像素突跳。
            return txt, '', None, playing
        except Exception:
            return 'MoeKoe Music', '', None, False

    def _auto_text_w(self):
        """当前状态下的目标歌词槽宽度（兼容旧调用点）。"""
        main, sub, _line, _p = self._want_texts()
        return int(self._slot_w_for(main, sub))

    def _apply_metrics(self, animated=False):
        m = self._metrics()
        self.H, self.DISC, self.PAD = m['H'], m['DISC'], m['PAD']
        self.RADIUS = int(max(6, min(CFG.get('island_radius', m['RADIUS']), self.H // 2 + 8)))
        # 高度变化（compact 遇到译文临时撑成双行）不打断正在进行的伸缩：
        # 只有「空闲态」才顺手把宽度重新对到目标，动画中让状态机继续收敛。
        if self._swap_phase == 'idle' or self._slot_target <= 0:
            main, sub = self._disp_main, self._disp_sub
            if main is None:
                main, sub, self._disp_line, _p = self._want_texts()
                self._disp_main, self._disp_sub = main, sub
            self._slot_target = self._slot_w_for(main, sub)
            self._slot_w = self._slot_target
        self.TEXT_W = int(round(self._slot_w))
        # ★ v1.7.24：空闲态下（字体/布局变更等）按当前槽宽预夹一次，
        #   防止配置变更把胶囊顶出屏幕；动画中不介入（状态机收敛时再夹）。
        if self._swap_phase == 'idle':
            self._reclamp_for_slot(self._slot_target)
        self._apply_current_size(animated=animated)

    def _apply_current_size(self, animated=False):
        """按 **窗口预算宽度** 与高度应用窗口几何。

        ⚠️ v1.7.20：换句伸缩期间**不再**每帧调用本函数（见 `_advance_swap`）。
        每帧 `setFixedSize()` + `move()` 会让「窗口已移动、画布仍是上一帧」的
        中间态反复出现，实测每帧偏多达 55px（`probe_desync.py`）—— 那就是抖动。
        现在窗口宽度由 `win_content_w()` 决定，而它在动画中是**常数**，
        因此本函数在动画期间根本不会产生任何几何变化。"""
        cw = self.win_content_w()
        ch = self.H
        nw, nh = cw + MARGIN * 2, ch + MARGIN * 2
        if self.width() != nw or self.height() != nh:
            self.setFixedSize(nw, nh)
            # 尺寸真的变了 → **立刻同步重绘一次**，把「已改尺寸、画布仍旧」的
            # 中间态压到微秒级（只有配置变更/双行高度切换这类离散场合才会走到）。
            self.repaint()
        if animated:
            # 宽度变化时平滑过渡（水平居中）：直接 move 会「一跳一跳」
            self.animate_to_target()
        else:
            self.move(*self.target_pos())
        self.update()

    def apply_cfg(self):
        """配置变更（托盘/设置面板/插件）后重新应用：尺寸、颜色、可见性"""
        try:
            self._apply_metrics()
            self.setVisible(bool(CFG.get('show_island', True)))
            self.update()
        except Exception as e:
            log('island apply_cfg fail: %r' % e)


    def content_size(self):
        # PAD + 封面 + 间距(18) + 文字 + PAD + 余量
        # ⚠️ 这是**胶囊本身**的尺寸（会随槽宽动画变化），不是窗口尺寸！
        #   窗口尺寸一律走 `win_content_w()`（v1.7.20 起为刚性常数）。
        return (self.PAD + self.DISC + 18 + self.TEXT_W + self.PAD + 4, self.H)

    # ---------- v1.7.20：窗口刚性化 + 胶囊在窗口内居中 ----------

    def win_content_w(self):
        """**窗口内容宽度**（不含 MARGIN 边距）—— v1.7.20 起与槽宽解耦。

        `RIGID_WIN=True` 时恒按最大槽宽预留，于是换句伸缩期间窗口
        **不移动、不改尺寸**，从根上消掉「移动/重绘不同步」造成的抖动。
        置 False 即回退成「窗口贴住胶囊」（v1.7.19 行为，会抖）。"""
        if self.RIGID_WIN:
            return self.PAD + self.DISC + 18 + self.TEXT_W_MAX + self.PAD + 4
        return self.PAD + self.DISC + 18 + int(self.TEXT_W) + self.PAD + 4

    def _pill_left_local(self):
        """胶囊在**窗口局部坐标系**下的左缘 x（浮点）。

        两种锚定（都在动画期间恒定，故屏幕位置恒定）：
          · 顶格居中（`CFG['x']` is None）：窗口宽度固定 → 胶囊在窗口内居中
            → 左缘 = MARGIN + (窗宽 − 胶囊宽)/2。槽宽变化只改胶囊宽，
            胶囊中心始终 = 窗口中心 = 屏幕中心 → **对称生长**，与旧观感一致。
          · 用户拖动过（`CFG['x']` 有值）：胶囊恒贴窗口左缘（= MARGIN），
            向右生长 —— 与 v1.7.19 及更早的行为完全一致。"""
        cw_win = self.win_content_w()
        cw = self.content_size()[0]
        if CFG.get('x') is None and cw_win > cw:
            return MARGIN + (cw_win - cw) / 2.0
        return float(MARGIN)

    def target_pos(self):
        """窗口左上角的目标位置。

        v1.7.20：窗口宽度取**刚性预算宽** `win_content_w()`，位置由
        「胶囊左缘的目标 x − 胶囊在窗口内的左缘」反推。于是：
          · 顶格居中时窗口 x 与槽宽**无关**（常数）→ 换句动画期间窗口纹丝不动；
          · 拖动过（`CFG['x']` 有值）时胶囊左缘恒落在 `CFG['x']`。"""
        scr = QApplication.primaryScreen().availableGeometry()
        # ⚠️ v1.7.23：拖动期间一律「原地不动」——否则换句收尾/高度切换走的
        #    `_apply_current_size → move(target_pos())` 会把窗口拽回
        #    `CFG['y']` 旧值 / 屏幕中心，肉眼即「拖动时岛（歌词）跳走」。
        if getattr(self, '_dragging', False):
            return self.x(), self.y()
        pl = self._pill_left_local()
        cw = self.content_size()[0]
        x = int(round(self._cap_left_ideal() - pl))
        y = int(CFG['y']) - MARGIN
        if CFG.get('x') is None:
            # 顶格居中：窗口刚性、x 与槽宽无关（常数），按窗口右缘夹只是兜底
            x = max(-MARGIN + 2, min(x, scr.width() - self.width() + MARGIN - 2))
        else:
            # 拖动锚定：胶囊恒贴窗口左缘 → 只需保证**胶囊**右缘不出屏。
            #   ⚠️ 不能按刚性宽窗的右缘夹（窗口比胶囊宽 ~600px），否则可拖
            #   行程会被压缩（实测 2560 屏上 2350 → 1750）。
            x = max(-MARGIN + 2, min(x, scr.width() - cw - 2 - MARGIN))
        y = max(-MARGIN, min(y, scr.height() - self.height() + MARGIN - 2))
        return x, y

    def _reclamp_for_slot(self, slot_target):
        """**v1.7.24：换句瞬间按「目标宽度」预夹窗口位置**（右缘溢出根治）。

        根因（用户：「拖到右侧的时候右边直接陷进去了」）：锚定态
        （`CFG['x']` 有值）胶囊贴窗口左缘、向右生长；而 v1.7.20 起换句
        动画期间窗口「只重绘、绝不动」（`RIGID_WIN`）——于是岛停在屏幕
        右侧、下一句歌词更长时，胶囊右缘直接长出屏幕外且**永不回夹**
        （实测溢出 406px，上限 ≈ TEXT_W_MAX − 旧槽宽 ≈ 600px）。

        处置：在「收缩→展开」的交界帧（槽宽已收到 0、透明度 0 ——
        **屏幕上没有胶囊**）把窗口一次性移到「目标宽度也放得下」的位置，
        锚定态同步修正 `CFG['x']`。一次性移动发生在空帧上 = 肉眼不可见；
        其后的展开过程窗口照旧纹丝不动（**不回退** v1.7.20 的零抖动）。
        `RIGID_WIN=False`（回退老路）时不介入——那条路每帧经
        `_apply_current_size → target_pos()` 自带夹取。"""
        if not self.RIGID_WIN:
            return
        try:
            scr = QApplication.primaryScreen().availableGeometry()
            cw_final = (self.PAD + self.DISC + 18 +
                        int(round(slot_target)) + self.PAD + 4)
            pl = self._pill_left_local()
            pill_left = self.x() + pl
            allowed = max(float(MARGIN), scr.width() - cw_final - MARGIN)
            if pill_left <= allowed:
                return
            self.move(int(round(self.x() - (pill_left - allowed))), self.y())
            self.repaint()
            if CFG.get('x') is not None:
                CFG['x'] = int(round(allowed))
        except Exception as e:
            log('island reclamp fail: %r' % e)

    # ---------- 「胶囊左缘的理想屏幕坐标」—— 取整只做一次 ----------
    #   ⚠️ v1.7.19 曾以为「抖动」是两次独立取整（窗口 floor + 局部 round）拍频导致的，
    #     于是把文字原点改成「屏幕绝对坐标取整一次」。**实测无效**（用户第三次反馈）。
    #     真相见类常量 `RIGID_WIN` 上方：窗口移动与重绘提交之间存在中间态，
    #     每帧把画面顶偏 Δgx（最大 55px）。本函数只是「理想坐标」的提供者，
    #     配合 v1.7.20 的刚性窗口（`self.x()` 在动画中恒定）才真正稳定。
    #   v1.7.20 起本值 = 胶囊左缘的屏幕理想 x（浮点、未取整）。

    def _cap_left_ideal(self):
        """胶囊左缘在**屏幕绝对坐标**下的理想 x（浮点、平滑、未取整）。

        顶格居中 → 屏幕中心对称；拖动过 → `CFG['x']`（即胶囊左缘）。
        取整统一交给 `_px_abs()` 做一次。

        ⚠️⚠️【v1.7.23 修复「拖动时歌词偏向一边」】⚠️⚠️
          顶格居中态（`CFG['x']` 尚为 None —— 只在松手 `_snap_now` 才写入）
          下**按住拖动**时，本值若仍按「屏幕中心对称」计算，就会出现：
          胶囊（封面/背景/按钮，paintEvent 按 `self.x()+pl` 画）**跟鼠标走**，
          而歌词文字（`_draw_text/_draw_karaoke` 按 `base_abs = 本值 + …` 画）
          被**钉在屏幕中心** —— 相对岛偏向一边，拖多远偏多远
          （用户描述「拖动的时候歌词不固定，会偏向左边或者右边」）。
          处置：拖动期间（`_dragging`）本值改取**窗口实际位置** `self.x()+pl`
          —— 文字与胶囊同源，拖动全程相对关系恒定。"""
        try:
            if getattr(self, '_dragging', False):
                return float(self.x()) + self._pill_left_local()
            scr = QApplication.primaryScreen().availableGeometry()
            cw = self.content_size()[0]
            if CFG.get('x') is None:
                v = (scr.width() - cw) / 2.0
            else:
                v = float(int(CFG['x']))
            return max(2.0, min(v, float(scr.width() - cw - 2)))
        except Exception:
            return float(self.x() + self._pill_left_local())

    def _px_abs(self, abs_x):
        """屏幕绝对坐标 → **取整一次** → 折回窗口局部坐标。

        与 `_px()` 的区别：`_px()` 在局部坐标取整，会把窗口位置里那 0~0.5px 的
        量化误差原样带进文字（就是抖动源）；本函数先在绝对坐标取整，
        误差被彻底吸收在窗口位置上，文字恒定。"""
        return float(round(abs_x)) - self.x()

    # 位移动画（自绘定时器，见 animate_to_target）
    _anim_timer = None

    def animate_to_target(self):
        """平滑移动到目标位置。
        不用 QPropertyAnimation——它作为局部变量会被 Python GC 回收，
        动画静默失效（窗口停在原地或乱跳 = 用户说的「弹开」）。"""
        tx, ty = self.target_pos()
        self._anim_from = (self.x(), self.y())
        self._anim_to = (int(tx), int(ty))
        self._anim_t = 0.0
        if self._anim_from == self._anim_to:
            return
        if self._anim_timer is None:
            self._anim_timer = QTimer(self, interval=16, timeout=self._anim_step)
        else:
            self._anim_timer.stop()
        self._anim_timer.start()

    def _anim_step(self):
        self._anim_t += 16.0 / 200.0
        x0, y0 = self._anim_from
        x1, y1 = self._anim_to
        if self._anim_t >= 1.0:
            self.move(x1, y1)
            self._anim_timer.stop()
            log('island anim done pos=(%d,%d)' % (x1, y1))
            return
        e = 1.0 - (1.0 - self._anim_t) ** 3          # OutCubic
        self.move(int(x0 + (x1 - x0) * e), int(y0 + (y1 - y0) * e))

    # ---------- 岛内滚动时钟（与任务栏同模型：滑入一次后停住，不循环） ----------
    # 详见 TaskbarWidget._marq_off 的模型注释（v1.4.3 连续位移修复）。
    # 同样：时钟只由 tick 推进，paintEvent 只读。
    MARQ_SPEED = 110.0 / 1000.0    # px/ms ≈ 110px/s
    MARQ_DUR_MAX = 1000.0          # 长句用「变速」而非「跳变」（见 _marq_dur）
    MARQ_TAIL = 6.0

    def _marq_travel(self, tw, w):
        # 参数约定同 TaskbarWidget：调用方传 (文字宽, 可视宽)，
        # 故本函数内 tw=文字宽、w=可视宽 → 需左移 tw - w。
        return max(0.0, tw - w + self.MARQ_TAIL)

    def _marq_dur(self, tw, w):
        travel = self._marq_travel(tw, w)
        if travel <= 0:
            return 0.0
        # 时长上限只用来「提速」，位移在 dur 时刻恰好 = travel（不跳变）
        return min(self.MARQ_DUR_MAX, travel / self.MARQ_SPEED)

    def _marq_off(self, tw, w):
        """SPlayer 式「滑入 → 停住」相位（岛内版，纯读）。参数：(文字宽, 可视宽)。

        ⚠️ v1.4.3：位移改**线性插值** `travel × (t/dur)`，t=0→0（从句首）、
        t=dur→travel，全程连续、绝不跳变（旧版长句会在 t 撞上限时瞬间跳到底）。
        ⚠️⚠️ v1.7.21：暂停 = **冻结在当前位置**（用户「暂停全静止」）。
        旧版「未滑完也落到 travel（暂停整句可见，v1.4.3 语义）」本身就是一个
        瞬时跳变 —— `probe_pause.py` 实测暂停在滚动中途时偏移一帧跳
        几十~上百 px。现废除该特判：`_marq_t` 由 tick 只在播放中推进
        → 暂停时 t 停走，这里**自然冻结**；恢复播放后从冻结处继续滑完。
        （SPlayer 同语义：暂停冻结在当前位置。）"""
        if tw <= w:
            return 0.0
        travel = self._marq_travel(tw, w)
        if travel <= 0:
            return 0.0
        dur = self._marq_dur(tw, w)
        t = float(getattr(self, '_marq_t', 0.0))
        if dur <= 0:
            return travel
        if t >= dur:
            return travel
        return travel * (t / dur)          # ✅ 线性插值，无跳变；暂停自然冻结

    def _marq_set_text(self, text):
        """换句 → 相位归零（从句首重新滑入）。"""
        if text != getattr(self, '_marq_text', None):
            self._marq_text = text
            self._marq_t = 0.0

    def tick(self):
        self._fcount = getattr(self, '_fcount', 0) + 1
        if self._fcount % 120 == 0:
            # 周期性重新声明置顶，防止被其他窗口压住
            ctypes.windll.user32.SetWindowPos(int(self.winId()), -1, 0, 0, 0, 0,
                                              0x0001 | 0x0002 | 0x0010)
        # 滚动时钟：只在播放中按真实 dt 推进（暂停冻结），每刻仅一次
        _now = time.time()
        _dt = (_now - getattr(self, '_marq_last', _now)) * 1000.0
        self._marq_last = _now
        if not (0 <= _dt <= 400):
            _dt = 0.0
        try:
            with STATE.lock:
                _ls = list(STATE.lines)
            _c = current_line(_ls, STATE.now() * 1000.0)[1] if _ls else None
        except Exception:
            _c = None
        self._marq_set_text(_c[2] if _c else None)   # 换句 → 相位归零
        if STATE.is_playing:
            self._marq_t = getattr(self, '_marq_t', 0.0) + _dt
        # 周期性把「上次播放会话」落盘（每 ~16s 一次，独立于退出路径——
        # 强杀/看门狗重启/断电都不会丢缓存）。内部还有 3s 节流。
        if self._fcount % 480 == 0:
            if STATE.is_playing:
                STATE.save_session(force=True)   # 播放中：进度一直在动，强制存
            else:
                STATE.save_session()
        if STATE.is_playing:
            # 封面旋转角：按真实 dt 推进（33ms 时代写死 +1.2°，改 16ms 会快一倍）
            self.angle = (self.angle + 1.2 * (_dt / 33.0)) % 360
        if STATE.song_gen != self.cover_gen:
            self.cover_gen = STATE.song_gen
            self.cover_pm = load_cover_pixmap(STATE.song)   # 无封面时回退默认图
        # 高度自适应：compact 遇到「有翻译」的行会临时撑成双行（否则译文会被裁掉）
        want2 = self._two_lines()
        height_changed = want2 != getattr(self, '_two_state', None)
        if height_changed:
            self._two_state = want2
            self._apply_metrics()
        # ---- SPlayer 式换句伸缩（v1.7.7，权威实现见 windows/dynamic-island/App.vue）----
        #   1) 收缩：宽度 from → 0，250ms ease-in，同步淡出（旧句被两侧对称裁掉）
        #   2) 换文本（发生在宽度为 0 的那一刻，用户看不到替换过程）
        #   3) 展开：宽度 0 → 新宽度，500ms cubic-bezier(.34,1.56,.64,1)，先过冲再回落
        self._advance_swap(_now)
        self.update()
        # 任务栏组件有自己的 33ms tick（按钮动画 + 卡拉OK重绘），这里不再代劳

    # ---------- SPlayer 式换句伸缩状态机 ----------
    SH_SHRINK_MS = 250.0    # .lyric.is-shrinking → width .25s ease-in
    SH_EXPAND_MS = 500.0    # .lyric            → width .5s（见下面 EXPAND_BOUNCE 说明）
    SH_FADE_MS = 250.0      # opacity：收缩 ease-in 淡出 / 展开淡入

    # ---------- v1.7.17/v1.7.18：展开是否保留「回弹过冲」（用户 2026-10-10 选择去掉） ----------
    #   需求①：「跳转歌词伸缩的时候会"震动"一下，把"震动"去掉」→ v1.7.17 去了过冲；
    #   需求②：「你改了之后，歌词闪动变得更加严重了」→ v1.7.18 把展开曲线的「形状」回调。
    #   实测（probe_flash.py，逐帧量 ink/slot/op）：
    #     v1.7.16 = `back_out`（有过冲=震动，但起步快、窄槽一闪而过）
    #     v1.7.17 = Material（无过冲，但起步太慢 → 窄槽停留 ~90ms = 闪动）
    #     v1.7.18 = `sp_expand_fast`（**起步快 + 零过冲**，两头都要）
    #   `EXPAND_BOUNCE=False` → 用 `sp_expand_fast`；置 True 即完整恢复
    #   v1.7.7~v1.7.16 的 SPlayer 原味回弹（`sp_back_out` 与其调用路径原样保留）。
    EXPAND_BOUNCE = False

    def _advance_swap(self, now):
        """推进「收缩 → 换文本 → 展开」状态机（每帧只由 tick 调用一次）。"""
        want_main, want_sub, want_line, playing = self._want_texts()
        changed = (want_main != self._disp_main) or (want_sub != self._disp_sub)

        # ⚠️⚠️【v1.7.12 修复「暂停时把上一句又伸缩一遍」】⚠️⚠️
        #   用户反馈：暂停时，在歌词较快的歌里，灵动岛还会把**上一句**的歌词再
        #   伸缩一遍。
        #   机理：这套「收缩 250ms → 换文本 → 展开 500ms」是**播放中的转场**，
        #   一轮 750ms。快歌每句只有几百 ms，岛本来就有一大半时间停在动画中途
        #   （实测 400ms/句时，2.3s 里只走完 3 轮）。此刻用户一按暂停：
        #     · 若正处「收缩」阶段 —— 屏幕上还是**上一句**，旧代码会把这轮跑完；
        #     · 暂停带来的进度重同步还可能让目标句来回翻（见 `apply_state` 的注释），
        #       于是「上一句」被来回收缩/展开一遍又一遍。
        #   处置：**暂停时一律不播换句伸缩**。只要屏上的字 ≠ 此刻该显示的字
        #   （或正处于收缩中途）→ 立刻落到目标句（等价 SPlayer 的 `applyImmediate()`，
        #   它在「不适合播动画」的场合也是直接到位，不收缩）。
        #   文本已经一致、只是正在「展开」收尾时**不打断** —— 屏幕上已经是正确那一句，
        #   让宽度自然长完即可；也避免把展开卡在半路（相位推进在下面）。
        # ⚠️⚠️【v1.7.21 修复「暂停时跳一下才静止」—— 暂停 = 全静止】⚠️⚠️
        #   用户反馈（2026-10-10）：「暂停的时候它会跳一下才静止，
        #   暂停的时候灵动岛要做到全静止状态」。
        #   旧处置（v1.7.12）：暂停时只要屏上的字 ≠ 目标字、或正处于收缩中途
        #   → **立刻落位**（applyImmediate）。`probe_pause.py` 实测这就是
        #   「跳一下」本身：暂停落在收缩中途时，槽宽 88 → 259、透明度
        #   0.73 → 1.00 **一帧内完成**（单帧 |Δslot| = 170.8px 的突跳）。
        #   新处置：
        #     · **不再立刻落位**。正在飞的收缩/展开让它**自然跑完**
        #       （连续运动，任何一帧都与上一帧连续；跑完即静止）。
        #       v1.7.12 当年担心「目标句来回翻」——那已被同版的
        #       「歌词时钟只前不后」进度守卫根治，且这里不循环、只收尾一次。
        #     · 暂停中**空闲态**下文本真的变了（暂停中拖进度/换歌）→ 仍落位
        #       （内容必须更新，这是唯一允许的一次性落位）。
        if not playing and changed and self._swap_phase == 'idle':
            self._settle_swap(want_main, want_sub, want_line)
            return

        if changed:
            if self._swap_phase == 'idle':
                if self._disp_main is None or self._slot_w <= 1.0:
                    # 首次显示 / 上一帧宽度已是 0 → 直接到位（SPlayer 的 applyImmediate）
                    self._settle_swap(want_main, want_sub, want_line)
                    return
                else:
                    self._swap_phase = 'shrink'
                    self._swap_t0 = now
                    self._swap_from = float(self._slot_w)
                    self._swap_pending = (want_main, want_sub, want_line)
            else:
                # 动画中又换句 → 记住最新目标，本轮收敛后再判定
                self._swap_pending = (want_main, want_sub, want_line)

        if self._swap_phase == 'shrink':
            k = (now - self._swap_t0) * 1000.0 / self.SH_SHRINK_MS
            k = 0.0 if k < 0 else (1.0 if k > 1 else k)
            self._slot_w = self._swap_from * (1.0 - sp_ease_in(k))
            if k >= 1.0:
                pend = self._swap_pending or (want_main, want_sub, want_line)
                self._swap_pending = None
                self._set_display(*pend)
                self._slot_w = 0.0
                self._slot_target = self._slot_w_for(self._disp_main, self._disp_sub)
                self._swap_phase = 'expand'
                self._swap_t0 = now
                # ★ v1.7.24：此帧槽宽=0、透明度=0（屏幕上没有胶囊）——
                #   借这个「空帧」按目标宽度预夹窗口，右侧锚定不再长出屏外。
                self._reclamp_for_slot(self._slot_target)
        elif self._swap_phase == 'expand':
            k = (now - self._swap_t0) * 1000.0 / self.SH_EXPAND_MS
            k = 0.0 if k < 0 else (1.0 if k > 1 else k)
            # v1.7.18：默认走 `sp_expand_fast`（`cubic-bezier(.25,.9,.25,1)`）
            #   —— 起步与 v1.7.16 一样快（窄槽一闪而过 → 不闪），
            #   但控制点 y ≤ 1 → 峰值 1.0000、零过冲（→ 不震）。
            #   置 EXPAND_BOUNCE=True 恢复旧回弹曲线（两条路径都在）。
            _ez = sp_back_out if self.EXPAND_BOUNCE else sp_expand_fast
            self._slot_w = self._slot_target * _ez(k)
            if k >= 1.0:
                self._slot_w = self._slot_target
                self._swap_phase = 'idle'

        if self._swap_phase != 'idle' or changed:
            new_w = int(round(self._slot_w))
            if new_w != self.TEXT_W:
                self.TEXT_W = new_w
                # ★ v1.7.20：动画期间**只重绘、绝不动窗口几何**。
                #   窗口宽度由 `win_content_w()` 给出（刚性常数），胶囊在窗口内
                #   居中绘制 → 屏幕上的胶囊照旧左右对称生长，但窗口本身不动。
                #   这样「某一帧重绘迟交」的最坏结果只是屏幕上重复上一帧
                #   （任何一帧都是合法连续画面）→ 不再有 Δgx 那么大（最大 55px）
                #   的位置顶偏，也就没有抖动。
                #   `RIGID_WIN=False` 时走回 v1.7.19 的老路（每帧 move，会抖）——
                #   保留它只为可回退与 A/B 对照。
                if self.RIGID_WIN:
                    self.update()
                else:
                    self._apply_current_size(animated=False)

    def _settle_swap(self, main, sub, line):
        """**立刻**落到目标文本 + 目标宽度，不播收缩/展开（v1.7.12）。

        三个调用场合（语义都是 SPlayer 的 `applyImmediate()`）：
          ① 首次显示（`_disp_main is None`）；
          ② 上一帧宽度已经收到 0（收缩刚好走完，没必要再来一轮）；
          ③ **暂停**时文本需要变（≤ 用户反馈的「暂停还伸缩上一句」）。
        ③ 之前旧代码在 ② 之后会继续跑到 `_swap_pending`，而 `_swap_pending`
        是动画中途记下的**旧目标**，暂停时就可能落到上一句、还配一整轮展开动画。
        这里把「相位、挂起目标、槽宽」一次性清干净，并且**只在宽度真的变了**才
        调 `_apply_current_size`（避免无谓的 move/setFixedSize）。
        """
        self._swap_phase = 'idle'
        self._swap_pending = None
        self._swap_t0 = 0.0
        self._swap_from = 0.0
        self._set_display(main, sub, line)
        self._slot_target = self._slot_w_for(main, sub)
        self._slot_w = self._slot_target
        self._reclamp_for_slot(self._slot_target)   # ★ v1.7.24：落位前预夹（含 CFG['x'] 修正）
        new_w = int(round(self._slot_w))
        if new_w != self.TEXT_W:
            self.TEXT_W = new_w
            self._apply_current_size(animated=False)

    def _set_display(self, main, sub, line):
        self._disp_main, self._disp_sub, self._disp_line = main, sub, line
        # 换句 → 跑马灯相位归零（与滚动时钟共用 `_marq_set_text` 的语义）
        self._marq_set_text(main)

    def _swap_opacity(self):
        """当前文字不透明度（0..1），复刻 SPlayer 的 .lyric opacity 过渡。"""
        ph = getattr(self, '_swap_phase', 'idle')
        if ph == 'shrink':
            k = (time.time() - self._swap_t0) * 1000.0 / self.SH_FADE_MS
            k = 0.0 if k < 0 else (1.0 if k > 1 else k)
            return max(0.0, 1.0 - sp_ease_in(k))
        if ph == 'expand':
            k = (time.time() - self._swap_t0) * 1000.0 / self.SH_FADE_MS
            k = 0.0 if k < 0 else (1.0 if k > 1 else k)
            # v1.7.18：**还原成 SPlayer 原版 ease-out**（前快后慢）。
            #   v1.7.17 曾把这里也换成 Material 慢起曲线（想让淡入与宽度同步），
            #   结果「文字亮起来更晚」→ 空窗变长 → 用户看到的「闪动」加剧。
            #   实测这条 ease-out 与 500ms 的 `sp_expand_fast` 宽度曲线时间轴天然同步：
            #     64ms  → 宽 45.0% / 透明 38.6%
            #     160ms → 宽 84.6% / 透明 82.1%
            return sp_ease_out(k)
        return 1.0

    # ---------- 渲染 ----------
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        # ★ v1.7.20：胶囊在**窗口内**的落点由 `_pill_left_local()` 给出
        #   （刚性窗口下它随槽宽内缩 → 胶囊在屏幕上保持「以屏幕中心对称生长」）。
        #   取整只做一次，且取在**屏幕绝对坐标**上（见 `_px_abs`）。
        oy = MARGIN
        pl = self._pill_left_local()            # 浮点：胶囊在窗口内的左缘
        ox = self._px_abs(self.x() + pl)        # 实绘左缘（局部、屏幕绝对坐标下取整一次）
        cw, ch = self.content_size()
        col = island_colors()
        dual = CFG.get('island_layout') == 'dual'

        draw_soft_shadow(p, QRectF(ox, oy + 2, cw, ch), self.RADIUS)
        draw_pill(p, QRectF(ox + 0.5, oy + 0.5, cw - 1, ch - 1), self.RADIUS,
                  col['bg1'], col['bg2'], col['border'])

        cy = oy + ch / 2
        # 连接状态点
        p.setBrush(col['dot_ok'] if STATE.connected else col['dot_bad'])
        p.setPen(Qt.NoPen)
        p.drawEllipse(QPointF(ox + cw - 12, oy + 10), 2.6, 2.6)

        # 圆形封面（对标 SPlayer）：取方形缩略图再蒙成圆
        cover = self.cover_pm if self.cover_pm is not None else self.default_square
        p.drawPixmap(int(ox + self.PAD), int(cy - self.DISC / 2),
                     rounded_cover(cover, self.DISC, self.DISC / 2.0))

        # ---- 文本 ----
        #   compact: 单行（卡拉OK歌词 / 歌名-歌手）
        #   dual   : 两行（第一行歌词，第二行翻译，无翻译时预看下一句）
        # ★ 这里传**浮点**的窗口局部左缘（pl + 文字区偏移），不是取整后的 ox：
        #   `_draw_text` 内部要把它换算成「屏幕绝对坐标」再一次性取整，
        #   而那条路径必须用**解析理想值**才能保证换句伸缩全程恒定（见 `_px_abs`）。
        #   裁剪矩形（clip）内部另用 `_px(x)` 取整，保证切口锐利。
        tx = pl + self.PAD + self.DISC + 18
        maxw = pl + cw - tx - self.PAD - 2
        f_big = QFont('Microsoft YaHei UI', self._font_size(0)); f_big.setWeight(QFont.DemiBold)
        f_sub = QFont('Microsoft YaHei UI', self._font_size(-3))

        with STATE.lock:
            playing = STATE.is_playing
        t_ms = STATE.now() * 1000.0

        # ⚠️ 一律画「显示态」（_disp_*），不要画 STATE 当前句：
        #    换句动画的收缩阶段屏幕上要留着**旧句**，而 STATE 早已指向新句。
        body = self._disp_main or ''
        sub = self._disp_sub or ''
        dline = self._disp_line
        opacity = self._swap_opacity()
        # 注：不再需要 `swapping` 标志来切换绘制路径 —— 动画态与静止态已统一
        #     （v1.7.8）。换句动画仍由 `_swap_phase` 驱动**窗口宽度**。
        slot_w = float(max(1, self.TEXT_W))
        # 仅**静止态**才允许走「文字超宽 → 跑马灯」分支；换句动画期间槽宽本来
        # 就比文字窄（那正是收缩本身），必须一律走居中裁切，否则位置会乱跳。
        _idle = getattr(self, '_swap_phase', 'idle') == 'idle'

        if (body or '').strip():
            if (sub or '').strip():
                # 行距随字号缩放：字号调大时两行不会叠在一起（SPlayer 的呼吸感）
                fs = self._font_size(0)
                gap = max(24.0, fs * 2.05)
                main_cy, sub_cy = cy - gap / 2.0 + 1.0, cy + gap / 2.0 + 1.0
            else:
                main_cy, sub_cy = cy, None
            # ⚠️ 对齐方式**全程唯一**（v1.7.8）：不再区分「换句动画态」与「静止态」。
            #    SPlayer 的 `.lyric` 恒为 `justify-content:center; overflow:hidden`，
            #    动画前后一致；早期只在动画态居中、静止态左对齐 → 切换那一帧横跳。
            #    现在两态都走槽内居中。
            #    `allow_scroll` 只在**静止态**才允许为真：收缩/展开期间槽宽本来就
            #    比文字窄（那正是动画本身），绝不能因此切去跑马灯分支。
            if dline is not None and dline[4]:
                self._draw_karaoke(p, dline, t_ms, tx, main_cy, maxw, f_big, playing,
                                   col['accent'], col['text'],
                                   slot_w=slot_w, opacity=opacity, allow_scroll=_idle)
            else:
                # ⚠️ v1.7.21：去掉暂停时的 '‖ ' 前缀（用户「暂停全静止」）。
                #    前缀会在暂停瞬间改变文本内容 → 槽内居中位置平移 +
                #    宽度观感变化，`probe_pause.py` 实测一帧 625px 的像素突跳
                #    （无歌词的兜底标题更狠：4850px）。暂停态改由
                #    「卡拉OK高亮冻结 / 封面停转」表达，文字保持原样。
                self._draw_text(p, body,
                                tx, main_cy, maxw, f_big, col['text'],
                                slot_w=slot_w, opacity=opacity, allow_scroll=_idle)
            if sub_cy is not None:
                self._draw_text(p, sub, tx, sub_cy, maxw, f_sub, col['sub'],
                                slot_w=slot_w, opacity=opacity, allow_scroll=_idle)
        else:
            self._draw_text(p, body or 'MoeKoe Music', tx, cy, maxw, f_big, col['text'],
                            slot_w=slot_w, opacity=opacity, allow_scroll=_idle)
        p.end()

    @staticmethod
    def _sub_of(cur, nxt, dual=False):
        """第二行内容：翻译（若开启且有）→ 否则仅在双行版式里预看下一句歌词。
        compact 版式传 dual=False：没翻译就不占第二行，保持紧凑。"""
        if cur is None:
            return ''
        if cur[3] and CFG.get('show_translation', True):
            return cur[3]
        if dual and nxt:
            return nxt[2]
        return ''

    def _draw_text(self, p, text, x, cy, maxw, font, color, speed=42.0,
                   slot_w=None, opacity=1.0, allow_scroll=False):
        """单行文本。`slot_w` 非 None 时走 SPlayer 的「槽内居中 + 裁切」模式。

        · slot_w=W：文字在 [x, x+W] 内**水平居中**并被裁切 ——
          等价 CSS `.lyric { justify-content:center; overflow:hidden; white-space:nowrap }`，
          所以槽比文字窄时两端会被对称裁掉。**动画态与静止态都走这条**。
        · allow_scroll=True（静止态才传）：文字真的超过槽宽（被 TEXT_W_MAX
          夹紧的长句）才退回跑马灯，否则一律居中。

        ⚠️ 【v1.7.8 修复】对齐方式必须**全程唯一**。
          SPlayer 的 `.lyric` 是恒定的 `justify-content:center`，动画前后一致；
          本组件早期只在「换句动画态」居中、静止态改回**左对齐** —— 于是
          动画开始那一帧（以及展开结束那一帧）文字会水平横跳
          `(slot_w - text_w) / 2`。槽被 TEXT_W_MIN=120 夹紧而文本只有 69px 时
          实测跳 **25.5px**，肉眼就是「卡一下才能对齐」。现在两态统一居中。

        ⚠️ 跑马灯相位必须用**独立滚动时钟** `_marq_off()`（由 tick 用真实 dt 推进），
        不能用 `time.time()` 直接算 —— 那等于「不看播放状态一直滚」：
          ① 暂停时停不下来（用户明确要求「暂停不滚动」）；
          ② 换句时相位不归零 → 弹跳；
          ③ 重绘次数变化会改速度。

        ⚠️⚠️【v1.7.10 修复「跳转歌词时有震动」】所有**随动画变化**的坐标
          必须 `_px()` 吸附到整数像素。根因见 `_px` 的模块级注释：
          槽宽每帧变化会让「居中」算出的原点在 `.0 / .5` 之间逐帧翻转
          （实测 89.00 → 88.50 → 86.50 → 83.50 → 80.00 …），
          Qt 对小数原点走子像素定位 → 字形每帧换一份位图 → 视觉上抖动发虚。"""
        if not text:
            return
        p.setFont(font)
        fm = QFontMetrics(font)
        y = _px(cy + fm.ascent() / 2)      # 基线吸附（cy 变化时不再逐帧换相位）
        w = fm.horizontalAdvance(text)
        op = 1.0 if opacity is None else max(0.0, min(1.0, opacity))
        if op < 0.999:
            color = QColor(color)
            color.setAlpha(int(color.alpha() * op))
        if slot_w is not None:
            sw = max(1.0, float(slot_w))
            # ★ 文字原点的**屏幕绝对** x —— 用「解析理想值」推导，只 round 一次：
            #     base_abs = 胶囊理想屏幕左缘 + 文字区在胶囊内的偏移（= x − pl，恰好是常数）
            #   于是 `round(base_abs + (sw-w)/2)` 在换句伸缩全程是**恒定的整数**
            #   （因为 sw 与 _cap_left_ideal() 里 cw 的 T/2 项互相抵消），
            #   文字在屏幕上纹丝不动，槽只负责对称地露出/盖住它。
            #   ⚠️ 不能用「已取整的 ox」来推 base_abs：那会引入第二次取整，
            #     两条 0.5px 台阶相位不同 → 残留 ±1px 拍频（v1.7.19 的老毛病）。
            base_abs = self._cap_left_ideal() + (x - self._pill_left_local())
            if allow_scroll and w > sw:
                # 静止态且文字确实超过槽宽 → 跑马灯（与旧的静止态滚动同一模型）
                off = self._marq_off(w, sw)     # 纯读相位；时钟由 tick 推进
                p.save()
                p.setClipRect(QRectF(_px(x), cy - 17, sw, 34))
                p.setPen(color)
                p.drawText(QPointF(self._px_abs(base_abs - off), y), text)
                p.restore()
                return
            p.save()
            p.setClipRect(QRectF(_px(x), 0, sw, self.height()))
            p.setPen(color)
            # 居中 → 两端对称裁切。绝对坐标取整后该值是**常数**：文字纹丝不动，
            # 由槽的两侧对称地露出/盖住（SPlayer 的 overflow:hidden 行为）。
            p.drawText(QPointF(self._px_abs(base_abs + (sw - w) / 2.0), y), text)
            p.restore()
            return
        if w <= maxw:
            p.setPen(color)
            p.drawText(QPointF(_px(x), y), text)
            return
        off = self._marq_off(w, maxw)      # 纯读相位；时钟由 tick 推进
        p.save()
        p.setClipRect(QRectF(x, cy - 17, maxw, 34))
        p.setPen(color)
        p.drawText(QPointF(_px(x - off), y), text)
        p.restore()

    def _draw_karaoke(self, p, line, t_ms, x, cy, maxw, font, playing,
                      accent=None, base=None, speed=42.0, slot_w=None, opacity=1.0,
                      allow_scroll=False):
        """卡拉OK逐字高亮；行宽超出时整体跑马灯滚动。

        accent = 高亮色（已唱），base = 未唱文字色（默认取主题）。

        ⚠️ 两条时间轴解耦（同任务栏，见 `TaskbarWidget._marq_advance`）：
          · 高亮相位 = `t_ms`（播放进度）→ **暂停时冻结在当前位置**
            （用户要求「暂停时固定高亮跟踪」，早期代码 `if playing and frac>0`
             会在暂停时把高亮全抹掉，那是错的）。
          · 滚动相位 = 独立滚动时钟（匀速、换句不弹跳、暂停冻结）。"""
        start, end, body, trans, chars = line
        if accent is None or base is None:
            c = island_colors()
            accent = accent or c['accent']
            base = base or c['text']
        unsung = QColor(base)
        unsung.setAlpha(165)
        p.setFont(font)
        fm = QFontMetrics(font)
        y = _px(cy + fm.ascent() / 2)      # 基线吸附（v1.7.10，见 _px 注释）
        body_w = fm.horizontalAdvance(body)
        op = 1.0 if opacity is None else max(0.0, min(1.0, opacity))
        p.save()
        if slot_w is not None:
            # 槽内居中 + 裁切（SPlayer 的 .lyric）——**动画态与静止态共用**，
            #   对齐方式全程唯一，换句前后不会横跳（见 `_draw_text` 的长注释）
            sw = max(1.0, float(slot_w))
            # ★ 与 `_draw_text` 同法：起点用**解析理想值**（胶囊理想屏幕左缘 +
            #   文字区偏移），只 round 一次 → 逐字 advance 的整数起点在换句
            #   伸缩全程恒定，逐字高亮（卡拉OK路径）同样不抖。
            base_abs = self._cap_left_ideal() + (x - self._pill_left_local())
            if allow_scroll and body_w > sw:
                # 静止态且整句确实超过槽宽（TEXT_W_MAX 夹紧）→ 保留跑马灯
                p.setClipRect(QRectF(_px(x), cy - 17, sw, 34))
                cx = self._px_abs(base_abs - self._marq_off(body_w, sw))
            else:
                p.setClipRect(QRectF(_px(x), 0, sw, self.height()))
                # 居中 → 两端对称裁切（绝对坐标取整 → 起点恒定，逐字不再抖）
                cx = self._px_abs(base_abs + (sw - body_w) / 2.0)
        elif body_w > maxw:
            # 滚动用独立时钟（`_marq_t` 节拍由主 tick 提供）
            p.setClipRect(QRectF(_px(x), cy - 17, maxw, 34))
            cx = _px(x - self._marq_off(body_w, maxw))
        else:
            cx = _px(x)
        for cs, ce, ch in chars:
            cw = fm.horizontalAdvance(ch)
            if t_ms >= ce: frac = 1.0
            elif t_ms <= cs: frac = 0.0
            else: frac = (t_ms - cs) / max(1.0, (ce - cs))
            if frac > 0:
                col = QColor(
                    int(unsung.red() + (accent.red() - unsung.red()) * frac),
                    int(unsung.green() + (accent.green() - unsung.green()) * frac),
                    int(unsung.blue() + (accent.blue() - unsung.blue()) * frac),
                    int(unsung.alpha() + (255 - unsung.alpha()) * frac))
            else:
                col = unsung
            if op < 0.999:
                col = QColor(col)
                col.setAlpha(int(col.alpha() * op))
            p.setPen(col)
            p.drawText(QPointF(cx, y), ch)
            cx += cw
        p.restore()

    # ---------- 原生输入：拖动 + 吸附 + 右键菜单 ----------
    #
    # ⚠️ v1.7.20：窗口宽度是**刚性预算**（TEXT_W_MAX），胶囊只在窗口内居中绘制，
    #   所以「内容区」不再是「窗口内边距」——必须用 `_pill_left_local()` 定位。
    def _pill_rect_local(self):
        """胶囊在窗口局部坐标下的矩形 (x, y, w, h)（浮点）。"""
        cw, ch = self.content_size()
        return (self._pill_left_local(), float(MARGIN), float(cw), float(ch))

    def _hit_content(self, gx, gy):
        """全局坐标（Qt 逻辑坐标）是否落在**胶囊**内容区（组件隐藏时不算命中）"""
        if not self.isVisible():
            return False
        px, py, cw, ch = self._pill_rect_local()
        x0, y0 = self.x() + px, self.y() + py
        return x0 <= gx <= x0 + cw and y0 <= gy <= y0 + ch

    def _native_rect(self):
        """本窗口的 Win32 物理坐标矩形 (l, t, r, b)——与 GetCursorPos 同坐标系。

        ⚠️ 150% 缩放下 Qt 的 x()/y() 是逻辑坐标，差 1.5 倍，命中判定绝不能混用。"""
        try:
            r = wt.RECT()
            if not ctypes.windll.user32.GetWindowRect(int(self.winId()), ctypes.byref(r)):
                return None
            return (r.left, r.top, r.right, r.bottom)
        except Exception:
            return None

    def _logical_scale(self):
        """物理→逻辑换算系数 (sx, sy)"""
        nr = self._native_rect()
        if nr is None:
            return (1.0, 1.0)
        pw, ph = nr[2] - nr[0], nr[3] - nr[1]
        sx = (self.width() / float(pw)) if pw else 1.0
        sy = (self.height() / float(ph)) if ph else 1.0
        return (sx, sy)

    def _poll_input(self):
        try:
            gx, gy, lbtn, rbtn = _global_mouse()
            tw = Island._btn_strip
            pressed = lbtn and not self._prev_l
            released = (not lbtn) and self._prev_l
            self._prev_l = lbtn

            # 悬停跟踪：任务栏组件的 hover 高亮 + 三键「回收/展开」都靠它
            # （必须在按住鼠标之外也持续更新，否则按钮永远不展开）
            if tw is not None:
                tw.native_hover(gx, gy)

            # ⚠️ 任务栏三键的按下/松手统一由 TaskbarWidget 内部锁存去重
            #    （`tw.poll_buttons(gx, gy, lbtn)`）——本组件不再自己判沿，
            #    否则和 TaskbarWidget 自己的兜底轮询会各发一次命令（翻两倍）。
            tb_took = False
            if tw is not None:
                tb_took = tw.poll_buttons(gx, gy, lbtn)

            if pressed:
                if not tb_took and self._hit_content(gx, gy):
                    self.ndrag = (gx, gy)
                    self._dragging = True            # v1.7.23：文字/几何跟手（见 _cap_left_ideal）
                    self._drag_home = (self.x(), self.y())
                    if self._anim_timer is not None:
                        self._anim_timer.stop()          # 拖动优先，打断回弹动画
                    log('island drag start (%d,%d) win=(%d,%d)' % (gx, gy, self.x(), self.y()))
            if lbtn:
                if self.ndrag is not None:
                    dx, dy = gx - self.ndrag[0], gy - self.ndrag[1]
                    if dx or dy:
                        scr = QApplication.primaryScreen().availableGeometry()
                        # v1.7.20：以**胶囊**（而非窗口）为准做移动与夹取 ——
                        #   窗口现在是刚性宽窗，直接拿 self.x() 加位移会让胶囊
                        #   相对光标错位。先把位移换算到「胶囊左缘」，再折回窗口位置。
                        pl = self._pill_left_local()
                        cw, ch = self.content_size()
                        # 物理位移 → 逻辑位移（150% 缩放下差 1.5 倍，不折算会「拖不动/飞出去」）
                        dpr = self._dpr()
                        px = self.x() + pl
                        nx = max(MARGIN, min(px + int(round(dx / dpr)),
                                             scr.width() - cw - MARGIN))
                        ny = max(MARGIN, min(self.y() + MARGIN + int(round(dy / dpr)),
                                             scr.height() - ch - MARGIN))
                        self.move(int(round(nx - pl)), int(round(ny - MARGIN)))
                        self.ndrag = (gx, gy)
            if released:
                # v1.7.23：先复位拖动态（snap / animate_to_target 重新用「理想位置」）
                self._dragging = False
                if self.ndrag is not None:
                    self.ndrag = None
                    hx, hy = getattr(self, '_drag_home', (self.x(), self.y()))
                    log('island drag release (%d,%d) win=(%d,%d) from=(%d,%d)'
                        % (gx, gy, self.x(), self.y(), hx, hy))
                    self._snap_now()

            if rbtn and not self._prev_r:
                # 右键菜单用 Qt 坐标弹出：gx/gy 是物理像素，需按 dpr 折回逻辑坐标
                dpr = self._dpr()
                if self._hit_content_phys(gx, gy):
                    self.menu.exec_(QPoint(int(gx / dpr), int(gy / dpr)))
            self._prev_r = rbtn
        except Exception as e:
            log('poll_input fail: %r' % e)

    def _dpr(self):
        """物理像素 / 逻辑像素（本机 150% 缩放 → 1.5）"""
        try:
            r = float(self.devicePixelRatioF()) or 1.0
        except Exception:
            r = 1.0
        if r <= 0:
            r = 1.0
        # 兜底：Qt 报 1.0 但实际缩放时，用原生 rect / 逻辑尺寸反推
        if abs(r - 1.0) < 1e-6:
            nr = self._native_rect()
            if nr:
                pw = nr[2] - nr[0]
                if pw > 0 and self.width() > 0:
                    r2 = pw / float(self.width())
                    if 1.05 < r2 < 4.0:
                        return r2
        return r

    def _hit_content_phys(self, gx, gy):
        """内容区命中：gx/gy 为物理像素（GetCursorPos），用原生 rect 对齐。

        不能用 self.x()/width()（逻辑坐标）——150% 缩放下会整体偏移。
        ⚠️ v1.7.20：窗口是刚性宽窗，胶囊在窗口内居中 → 命中矩形必须按
        `_pill_left_local()` 定位，不能再拿「窗口内边距」当内容区。"""
        if not self.isVisible():
            return False
        nr = self._native_rect()
        if nr is None:
            return False
        nl, nt, nr_r, nb = nr
        s = self._logical_scale()
        if s[0] <= 0 or s[1] <= 0:
            return False
        px, py, cw, ch = self._pill_rect_local()
        # 逻辑 → 物理：缩放系数 s 已在逻辑尺寸与物理 rect 之间反推得到
        x0 = nl + int(round(px * s[0]))
        y0 = nt + int(round(py * s[1]))
        x1 = nl + int(round((px + cw) * s[0]))
        y1 = nt + int(round((py + ch) * s[1]))
        return x0 <= gx <= x1 and y0 <= gy <= y1

    # ---------- ★v1.7.20：WM_NCHITTEST —— 刚性宽窗的「逐点命中」★ ----------
    #   窗口现在按**最大槽宽**预留（见类常量 `RIGID_WIN`），多出来的透明区域若
    #   照常吃掉点击，就会在屏幕顶部留下一条「看不见但点不穿」的带子
    #   （顶格居中时正好压住最大化窗口的标题栏/浏览器标签区）。
    #   因此照任务栏组件（`TaskbarWidget.nativeEvent`）同一套成熟做法，
    #   把命中测试交还给操作系统 —— 它是**每一次鼠标消息**上同步询问，
    #   精确、零延迟、无采样竞态：
    #     胶囊实心区       → HTCLIENT（本窗口收下，拖动/右键菜单照常）
    #     其余（含窗口外） → HTTRANSPARENT（此处穿透给下面的窗口）
    #   `WM_NCHITTEST = 0x0084`；lParam 低 16 位 x、高 16 位 y，
    #   是**物理像素**屏幕坐标（有符号，多屏负坐标也要对）。
    #   注意：本组件的输入（拖动/悬停/菜单）本来就走 `_poll_input` 的
    #   `GetCursorPos` + `GetAsyncKeyState` 全局轮询，所以「窗口收不收点击」
    #   对功能零影响 —— 这里纯粹是把**不属于胶囊的那部分屏幕还给系统**。
    def nativeEvent(self, eventType, message):
        try:
            if eventType != b'windows_generic_MSG':
                return super().nativeEvent(eventType, message)
            msg = ctypes.cast(int(message), ctypes.POINTER(wt.MSG)).contents
            if msg.message != 0x0084:            # WM_NCHITTEST
                return super().nativeEvent(eventType, message)
            lp = msg.lParam
            gx = lp & 0xFFFF
            gy = (lp >> 16) & 0xFFFF
            if gx >= 0x8000:
                gx -= 0x10000
            if gy >= 0x8000:
                gy -= 0x10000
            if self._hit_content_phys(gx, gy):
                return True, HTCLIENT
            return True, HTTRANSPARENT
        except Exception as e:
            log('island nativeEvent fail: %r' % e)
            return super().nativeEvent(eventType, message)

    def _drain_commands(self):
        """处理跨线程下发（托盘/设置面板/插件 native host）的指令"""
        while PENDING_CMDS:
            try:
                cmd = PENDING_CMDS.pop(0)
            except IndexError:
                break
            try:
                if cmd == 'open_settings':
                    open_settings_dialog()
                elif cmd in ('cfg_changed', 'show_island', 'show_taskbar', 'translation'):
                    apply_cfg_everywhere(reason=cmd)
                elif cmd == 'center_island':
                    self.reset_pos()
                elif cmd == 'quit_app':
                    request_quit('plugin-bridge')
            except Exception as e:
                log('pending cmd %r fail: %r' % (cmd, e))

    def _watch_cfg_file(self):
        """config.json 被外部改动（手改 / 另一个进程写入）时自动重新加载并生效"""
        try:
            m = os.path.getmtime(CONFIG_F)
        except OSError:
            return
        if self._cfg_mtime is None:
            self._cfg_mtime = m
            return
        if m != self._cfg_mtime:
            self._cfg_mtime = m
            fresh = load_cfg()
            changed = [k for k, v in fresh.items() if CFG.get(k, object()) != v]
            if changed:
                CFG.update(fresh)
                log('config.json changed on disk -> reload (%s)' % ','.join(changed[:8]))
                apply_cfg_everywhere('file')

    def _snap_now(self):
        """松手：拖到屏幕顶部附近 → 吸附并水平居中；否则停在当前位置（不再「弹开」）

        ⚠️ v1.7.20：`CFG['x']` 的语义恒为**胶囊左缘的屏幕 x**，因此要先把窗口
        局部量换成胶囊量（窗口是刚性宽窗，胶囊在窗口内居中/内缩）。"""
        scr = QApplication.primaryScreen().availableGeometry()
        pl = self._pill_left_local()
        cw, ch = self.content_size()
        top_gap = self.y() + MARGIN                 # 内容区距屏幕顶部
        if CFG.get('snap_top', True) and top_gap <= 90:
            CFG['x'] = None
            CFG['y'] = 0
            CFG['island_top_profile'] = 'splayer-top'
            log('snap -> top edge center')
            save_cfg(CFG)
            self.animate_to_target()
        else:
            CFG['x'] = int(max(MARGIN, min(self.x() + pl, scr.width() - cw - MARGIN)))
            CFG['y'] = int(max(MARGIN, min(self.y() + MARGIN, scr.height() - ch - MARGIN)))
            log('snap -> stay (%d,%d)' % (CFG['x'], CFG['y']))
            save_cfg(CFG)
            # ⚠️ v1.7.24：stay 落位**瞬时完成**，不走 200ms 动画 ——
            #   `CFG['x']` 一写入，`_pill_left_local()` 就从「窗口内居中」切到
            #   「贴左」，若让动画慢慢把窗口扫到新位置，胶囊会先左跳
            #   (cw_win−cw)/2 再滑回（实测 231px，松手「弹一下」）。
            #   瞬时 move 后胶囊左缘恰好 = CFG['x'] = 松手位置 → 肉眼零移动；
            #   repaint() 同步重绘，把「已移动、画布仍旧」的中间态压到微秒级。
            self.move(*self.target_pos())
            self.repaint()
            self.update()

    # ---------- 菜单 ----------
    def _build_menu(self):
        self.menu = QMenu()
        self.act_toggle = QAction('播放 / 暂停', self, triggered=lambda: ws_control('toggle'))
        self.act_next = QAction('下一首', self, triggered=lambda: ws_control('next'))
        self.act_prev = QAction('上一首', self, triggered=lambda: ws_control('prev'))
        for a in (self.act_toggle, self.act_prev, self.act_next):
            self.menu.addAction(a)
        self.menu.addSeparator()

        # 显示开关（与托盘菜单同一份状态）
        self.act_sh_island = QAction('显示灵动岛', self, checkable=True,
                                     triggered=lambda c: set_flag('show_island', bool(c)))
        self.act_sh_tb = QAction('显示任务栏歌词', self, checkable=True,
                                 triggered=lambda c: set_flag('show_taskbar', bool(c)))
        self.act_trans = QAction('显示歌词翻译', self, checkable=True,
                                 triggered=lambda c: set_flag('show_translation', bool(c)))
        for a in (self.act_sh_island, self.act_sh_tb, self.act_trans):
            self.menu.addAction(a)
        self.menu.addSeparator()

        self.act_snap = QAction('自动吸附顶部中央', self, checkable=True,
                                triggered=self.toggle_snap)
        self.act_topcenter = QAction('回到顶部居中', self, triggered=self.reset_pos)
        for a in (self.act_snap, self.act_topcenter):
            self.menu.addAction(a)
        self.menu.addSeparator()

        self.act_settings = QAction('外观与设置…', self, triggered=open_settings_dialog)
        self.act_cfgdir = QAction('打开配置目录', self, triggered=self.open_cfg_dir)
        self.act_auto = QAction('开机自启动', self, checkable=True, triggered=self.toggle_autostart)
        for a in (self.act_settings, self.act_cfgdir, self.act_auto):
            self.menu.addAction(a)
        self.menu.addSeparator()
        self.act_quit = QAction('退出', self,
                                triggered=lambda *_: request_quit('island-menu'))
        self.menu.addAction(self.act_quit)
        self.sync_menu()

    def sync_menu(self):
        try:
            self.act_snap.setChecked(bool(CFG.get('snap_top', True)))
            self.act_auto.setChecked(bool(CFG.get('autostart')))
            self.act_sh_island.setChecked(bool(CFG.get('show_island', True)))
            self.act_sh_tb.setChecked(bool(CFG.get('show_taskbar', True)))
            self.act_trans.setChecked(bool(CFG.get('show_translation', True)))
        except Exception:
            pass

    def open_cfg_dir(self):
        try:
            os.makedirs(APP_DIR, exist_ok=True)
            os.startfile(APP_DIR)
        except Exception as e:
            log('open cfg dir fail: %r' % e)

    def contextMenuEvent(self, ev):
        ev.accept()      # 右键菜单改由原生轮询弹出（_poll_input）

    def toggle_snap(self, checked):
        set_flag('snap_top', bool(checked))
        if checked:
            self.reset_pos()

    def reset_pos(self):
        CFG['x'] = None
        CFG['y'] = 0
        CFG['island_top_profile'] = 'splayer-top'
        save_cfg(CFG)
        self._apply_metrics()
        self.animate_to_target()

    def toggle_autostart(self, checked):
        set_flag('autostart', bool(checked))
        set_autostart(checked)

    _btn_strip = None

# ================================================================
# 任务栏组件（扁平融入任务栏，对标截图样式）
# ================================================================
class TaskbarWidget(QWidget):
    # 内容区（宽度上限受任务栏「开始按钮」位置约束，右缘 ~600 附近）
    #
    # CH 64（本机实测）：任务栏 Shell_TrayWnd 真实高 **72px**（系统 DPI 144/150%）。
    # 双行（歌词+翻译 / 歌名+作者）的真实字高 = 2 × 27px(@10pt，150% 缩放下
    # 1pt=2px) + 呼吸 ≈ 56px。原先 40/44 装不下 → 行距被压到 0、
    # 一行顶边一行被裁（用户说的「黏在一起」）。
    CW = 400                       # v1.5.0 对齐 SPlayer maxWidth
    CH = 64                    # 运行时会被 _fit_tray_height() 按真实任务栏高度夹紧
    CH_MIN = 40                # 兜底最小高度（小任务栏机器）
    CH_MAX = 72                # 本机任务栏 72px → 最多占满
    COVER = 40                 # 封面（CH=64 下比原来 32 放大，视觉更平衡）
    BTN = 32                   # 三键按钮直径
    R_COVER = 10
    BTNSPAN = BTN * 3 + 2 * 2  # 三键区总宽（含间隔）
    GAP = 12                   # 三键区与文字区的间距
    M = 2                     # 窗口内边距（留点击余量）
    COVER_GAP = 10             # 封面与文字之间的留白（SPlayer 参照：贴太紧会「黏」在一起）
    LINE_GAP = 13.0            # 双行**行心**距下限（紧致字形高≈20px，13 是「再挤也不重叠」的兜底）

    # ---------- v1.7.13：**不滚动**版式（用户要求「直接显示两行歌词」） ----------
    # ⚠️⚠️ 需求（2026-10-09）：任务栏播放时**歌词不要滚动**，直接静态显示两行。
    #   历史：v1.4.9 起照抄 SPlayer 的 getScrollTransform 做了「演唱进度驱动的滑入」——
    #   超宽行会随该句演唱进度**横向左移**，直到句尾前 2s 刚好露出句尾。
    #   用户现在明确不要这个动效（"不要搞滚动"）。
    #   处置：所有超宽行**一律不再位移**，改为**右端省略号（…）**：
    #     · 静止态 `_line()` / `_line_fx()` → `QFontMetrics.elidedText(…, ElideRight, w)`
    #     · 逐字卡拉OK `_draw_karaoke_line()` → 逐字累加选出放得下的前缀，尾补 `…`
    #     · 换句放大 `_draw_prom()` → **先在主行字号下省略到 w** 再栅格化，
    #       这样贴图宽 = 省略宽 × s ≤ w（s ≤ 1），动画期无需裁切/位移，
    #       且 s=1.0 那一帧与静止态 `_line()` 的省略结果**逐像素一致**。
    #   附带：`_marquee_active()` 恒 False —— 位置不再逐帧变化 → 不需要为跑马灯
    #   持续 60fps 重绘（省 CPU）。逐字卡拉OK / 换句放大各自另有驱动，不受影响。
    #
    # ---------- v1.7.16：**回退** —— 横向推进补回来（用户改主意） ----------
    # ⚠️⚠️【v1.7.16 用户 2026-10-10】原话：「任务栏长歌词往后推动的画面你删除了，请你补回来」。
    #   ⇒ 上面 v1.7.13 删掉的那套**演唱进度驱动的横向推进**（`getScrollTransform` 语义）
    #   全部恢复启用。此开关控制的就是它，一共 5 个落点：
    #     · `_line()`            → 超宽行按进度左移（否则右端省略号）
    #     · `_line_fx()`         → 同上（局部坐标 lw 版）
    #     · `_draw_karaoke_line()`→ 逐字卡拉OK 的滚动
    #     · `_draw_prom()`       → 换句放大的贴图按进度左移（s≤1，宽度自适应）
    #     · `_marquee_active()`  → 超宽且播放中 → tick 持续 repaint（≈60fps）
    #   行为细节（全部沿用 v1.4.9~v1.7.12 已验证的旧逻辑，未改动）：
    #     句首贴左 → 唱到本句 `_marq_profile()` 算出的起滚点后开始推进 →
    #     句尾前 END_MARGIN_MS 处刚好露出句尾；**暂停冻结且整句可见**（v1.4.3 语义）。
    #   ⚠️ 与**竖向**开关**正交**，互不影响 —— 本版只翻这一行：
    #     · `SWAP_SLIDE = False` → 换句**仍不竖向位移**（v1.7.15 决定，保留）；
    #     · `SWAP_ANIM  = True`  → 换句**仍原地放大** 0.82×→1.00×（v1.7.15，保留）；
    #     · 暂停仍保留两行（v1.7.14 决定，保留）。
    #   想再关掉横向推进 → 改回 True（右端省略号版式随之回来，两版都能随时切）。
    NO_SCROLL = False

    # ---------- v1.7.15：换句**原地放大**（不要位移，但放大要保留） ----------
    # ⚠️⚠️ 需求演进（务必按时间线读，别只看最新那条）：
    #   v1.7.14 用户说「歌词不要做滚动，直接显示两行」→ 我把 `SWAP_ANIM` 关掉，
    #     换句变成**完全静止**（不滑动、不淡入淡出、不做字号过渡）。
    #   v1.7.15 用户说「你把任务栏那个『放大』的效果给删去了，请你补回来」
    #     —— 也就是说：上一版**多杀了一个东西**。「位移」和「放大」虽然在代码里
    #     出自同一段过渡，但它们是**两件独立的事**，可以只留一件。
    #
    #   真机探针（`probe_branch.py`，真实歌曲《白色风车》句 [41]→[42] 边界）实测
    #   换句期间 `_draw_prom` 的参数轨迹：
    #       cy = 48.00 → 46.33 → 44.89 → 37.22 → 29.34 → 23.79 → 21.17 → 20.04 (→20.00)
    #       s  = 0.800 → 0.812 → 0.822 → 0.877 → 0.933 → 0.973 → 0.992 → 1.000
    #     ⇒ **cy 从 48（次行槽位）滑到 20（主行槽位）= 用户说的「滚动」**；
    #       **s 从 0.80 长到 1.00 = 用户要的「放大」**。两者在同一次调用里。
    #
    #   处置（两个开关，正交）：
    #     · `SWAP_ANIM  = True`  —— 创建 0.4s 过渡（放大需要它；关掉 = v1.7.14 全静止）
    #     · `SWAP_SLIDE = False` —— **所有竖向位移一律归零**：
    #         主行/新主行 固定在 `main_cy`（最终槽位）**原地**把字号从 `f_sub` 长到 `f_main`；
    #         第二行 固定在 `sub_cy` 静态绘制；离场旧行**不再绘制**（它原来就是靠位移让位的，
    #         位置冻结后若还画就会和新行叠在同一处糊成一团）。
    #       ⇒ 换句那一帧「文本直接换掉 + 新句由 0.82× 长到 1.00×」，**零位移、零裁切**。
    #     · `SWAP_SLIDE = True` 即完整恢复 v1.7.9~v1.7.13 的「下行顶上来 + 放大」。
    #     · `SWAP_ANIM  = False` 即完整恢复 v1.7.14 的「完全静止」。
    SWAP_ANIM = True

    # ---------- v1.7.14：换句**完全静止**（用户 2026-10-09 明确选择；已被 v1.7.15 细分） ----------
    #   实测定位（真机抓屏 + 离屏渲染双证）：用户口中的「滚动」**不是**横向跑马灯
    #   （v1.7.13 已删），而是**换句时「下行顶上来」的竖向滑动** —— 旧句向上滑出、
    #   还会被控件上沿裁掉半截（0.4s；`see_tb_filmstrip.png` 的 f10/f11 可见残影）。
    #   v1.7.14 当时的处置是 `SWAP_ANIM=False` → `paintEvent` 里**永不**创建 `_fade_from`，
    #   于是 `fade is None`，直接走末尾的「静止态」分支，位置与颜色都与静止态逐像素一致。
    #   ⚠️ 但那一刀把**放大**也一起杀了（用户 v1.7.15 要求补回），故现在默认改为
    #   `SWAP_ANIM=True` + `SWAP_SLIDE=False`；这条常量仍保留作「全静止」档位。
    SWAP_SLIDE = False

    # ---------- 三键点击的「去抖动」参数（v1.4.4） ----------
    # ⚠️ 问题现场（真机 debug.log 18:59:13–15）：
    #    同一坐标 (317,1564) 在 2 秒内打出了 **15 次** `tb press hit=1` →
    #    `tb button toggle` → `control toggle -> WS sent`。
    #    机制：微动开关的机械抖动（或用户「按住不放」时的手部微颤）会让
    #    `GetAsyncKeyState(0x01)` 在 1ms 量级上 True/False 反复跳变。
    #    旧代码把**每一对 press→release 都当成一次完整点击**，
    #    而 `toggle` 是翻转语义 → N 次翻转 = 播放/暂停来回切，
    #    用户看到的就是「按不动 / 按了没反应」。
    #    （已用 diag_jitter.py 逻辑复现：15 组 press/release → 15 条 toggle）
    #
    # 四道闸门，全部幂等、互不依赖：
    #   ① 只在「松手沿」派发（老逻辑，保留）
    #   ② 最短按住时长：抖动是 1–5ms 级，人手最快也 ~40ms → 太短的丢弃
    #   ③ 松开去抖：真实抖动「松手」只维持几毫秒就又按上（按键根本没抬起）；
    #      若一次新按下距上次松手 < BTN_RELEASE_MIN，视为**同一次按住**（不算新点击）
    #   ④ 同键冷却：即使真有第二对 press/release 穿过来，同键 N ms 内不再派发
    #
    # ⚠️ 真机实测（verify_launch_and_test.py，真实 mouse_event）教训：
    #    `time.sleep(0.002)` 造出来的「抖动」经 OS 输入队列后实际 hold 高达 13~17ms，
    #    **不是**微动开关那种 1~2ms 的抖动 → 只靠 ② 挡不住。
    #    闸门 ③ 才是对付真机的关键：它不关心单次按住多久，
    #    只看「松手后立刻又按上」这个抖动指纹。
    #    实测抖动簇里偶尔会夹一次 >40ms 的「休息」→ 若 RELEASE_MIN 太小，
    #    那次休息会被误判成「簇结束」而重开新簇。取 80ms：
    #    人手一次点击的抬起时长最少也有 ~80ms（否则就是没真的松手）。
    BTN_MIN_HOLD = 50.0        # ms：簇总时长短于此值视为抖动，丢弃
    BTN_RELEASE_MIN = 80.0     # ms：松手→再按短于此值视为「没真抬起」，并入同簇
    # v1.4.6 冷却闸从 300ms 降到 100ms（真机 debug.log 19:51 实锤）：
    #   300ms 会吞掉**人类的刻意快速连点**——真人连点间隔普遍在 140~290ms
    #   （日志里 cooldown 143/145/160/176/191/224/240/289ms 的 DROPPED 全是真人），
    #   用户感知就是「按不动」。而「抖动残余」早被闸门②③拦死（能走到闸门④的
    #   必然是「松手≥80ms 后的真实新按」）。100ms 只挡极端机器级重放，
    #   人手极限连点（~5 次/秒 = 200ms 间隔）也绝不会误杀。
    BTN_COOLDOWN = 100.0       # ms：同一按钮两次成功派发的最小间隔（仅极端重放兜底）

    def __init__(self):
        super().__init__()
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint |
                            Qt.Tool | Qt.NoDropShadowWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.hover_btn = -1
        self.press_btn = -1
        self.hover_inside = False       # 鼠标是否在组件上（决定三键展开）
        self.hover_alpha = 0.0          # v1.5.0 hover 过渡：0=歌词, 1=歌名/作者
        self.btns_span = 0.0 if CFG.get('tb_btns_auto_hide', True) else 1.0
        self.drag_pos = None
        self.ndrag = None
        self._press_at = None       # 按下点（物理像素）——拖动阈值判定的基准
        self._drag_armed = True     # 本次按下是否允许转成拖动（按钮按下时为 False）
        self._btn_latch = False     # 三键按键沿锁存（两个轮询路共用，防重复触发）
        # v1.4.4 去抖动状态：按下时刻（毫秒）+ 每键上次成功派发的时刻
        self._btn_down_ms = None    # 本次按下的 monotonic 毫秒（None = 未按）
        self._btn_up_ms = None      # 上次松手的 monotonic 毫秒（松开去抖用）
        self._btn_cluster_ms = None  # **本簇首次按下的时刻**——跨松手存活，
                                     # 只有「松手持续 ≥ BTN_RELEASE_MIN」才清零
        self._btn_fire_ms = [0.0, 0.0, 0.0]   # 三键各自上次成功派发的时刻
        self._btn_drop = 0          # 被丢弃的抖动次数（诊断用）
        self.dark_text = True
        self.cover_pm = None
        self.cover_gen = -1
        self.default_cover = make_default_cover(64)
        self._tick = 0
        # SPlayer 式跑马灯：独立滚动时钟（与播放进度解耦）
        self._marq_t = 0.0       # 当前行已滚动时长（ms，由 tick 推进）
        self._marq_dt = 0.0      # 本拍真实间隔（暂停时为 0）
        self._marq_last = time.time()
        self._marq_sig = None    # 相位失效标识（换句/换宽度 → 归零重滚）
        self._w_cur = float(self.CW)     # v1.4.2：悬停看歌名时窗口会动态加宽
        self.hwnd = 0            # 原生句柄
        self.owned = False       # 是否已把 Shell_TrayWnd 设为 owner
        self._fit_tray_height()          # 按真实任务栏高度定 CH（双行排版靠它才装得下）
        self.setFixedSize(self.CW + self.M * 2, self.CH + self.M * 2)
        self.poll = QTimer(self, interval=500, timeout=self.follow)
        self.poll.start()
        # 16ms（≈60fps）：三键回收/展开动画 + 卡拉OK逐字高亮 + 跑马灯重绘。
        # ⚠️ 原来 33ms（≈30fps）→ 跑马灯每帧位移 1px 左右看起来「一格一格跳」，
        #    用户反馈「没有 SPlayer 流畅」。SPlayer 是 60fps 逐帧推进的，
        #    所以这里提到 16ms；相位本身是**连续函数**（按真实 dt 算），
        #    帧率越高越顺滑。相位推进放在 tick 里、纯读放在 paintEvent 里，
        #    所以提高帧率不会导致速度漂移。
        self.tick_timer = QTimer(self, interval=16, timeout=self.tick)
        self.tick_timer.start()
        # ⚠️⚠️ 三键可点的**生命线**（v1.4.2 加固）⚠️⚠️
        #   三键的命中完全依赖 `Island._poll_input` 这个 16ms 轮询——
        #   它同时驱动 hover 展开 / 按下 / 松手三条链路。可它是挂在 **Island 窗口**
        #   上的定时器：只要 Island 那边出任何岔子（窗口未创建、被 hide、
        #   事件循环卡住、或用户把灵动岛关了导致某条路径提前 return），
        #   任务栏三键就**整个失联**——而且窗口照常在画，用户看到的就是
        #   「三键按不动」。本组件**自己也要有一路轮询**做兜底：
        #   与 Island 那路并存，两边都调 native_*（幂等，重复调用无害）。
        self.input_timer = QTimer(self, interval=16, timeout=self._poll_input_self)
        self.input_timer.start()

    def poll_buttons(self, gx, gy, lbtn):
        """三键输入的**统一入口**（幂等、沿锁存 + 抖动簇合并）。

        两个调用方（Island 主轮询 + 本组件兜底轮询）都走这里，都调 native_*
        （幂等，重复调用无害），所以两路并存也绝不会把一条命令发两遍。
        返回 True 表示「本次按下被任务栏组件接管」。

        ⚠️ 为什么必须这么设计：三键的命中链路原本独占挂在 Island 的定时器上；
        一旦那路失效（窗口未建/隐藏/卡顿/提前 return），三键就整个失灵——
        而窗口照常在画，用户看到的就是「按不动」。现在本组件有自己的兜底轮询，
        即使 Island 那路完全停摆，三键依然可点。

        ⚠️ v1.4.4 抖动簇模型（真机 15 连击的根治）：
        把「松手时长 < BTN_RELEASE_MIN 的连续按下」视为**同一个簇**（按键根本没抬起）。
        `_btn_cluster_ms` 记住**本簇首次按下**的时刻，且**跨松手存活**——
        只有「松手已经持续 ≥ BTN_RELEASE_MIN」才说明簇真的结束了，
        此时才会在下次按下时清零重开。派发只发生在簇结束时，
        并用「簇总时长」过闸门 ②（≥ BTN_MIN_HOLD）与闸门 ④（同键冷却）。
        这样一次物理点击（无论如何抖动）= 恰好一条命令。

        ⚠️ 为什么不能用 `_btn_down_ms`：它会被 `native_release` 清零（那是「当前是否按住」
        的语义）。簇起点必须活到「确认松手够久」为止，所以必须独立一个字段。"""
        if not self.isVisible() or not CFG.get('show_taskbar', True):
            return False
        took = False
        now_ms = time.monotonic() * 1000.0
        if lbtn:
            if not self._btn_latch:
                # ---- 按下 ----
                gap = (now_ms - self._btn_up_ms) if self._btn_up_ms is not None else 1e9
                if self._btn_cluster_ms is not None and gap < self.BTN_RELEASE_MIN:
                    # 仍在同一抖动簇内：不重开簇（不重置簇起点）
                    self._btn_drop += 1
                    log('tb bounce gap=%.1fms < %.0fms -> same cluster (%.0fms)'
                        % (gap, self.BTN_RELEASE_MIN, now_ms - self._btn_cluster_ms))
                    self._btn_latch = True
                    self._btn_down_ms = now_ms
                    # ⚠️ v1.4.7：bounce 时 press_btn 已被上一簇 release 清成 -1。
                    #    不恢复的话，真实松手落点稍偏（h=-1）→ 无回退 → 静默丢弃，
                    #    表现就是「连点第二下没反应」（v1.4.6 真机 D1 实锤根因）。
                    try:
                        hb = self._hit_global(gx, gy, force=True)
                        if hb >= 0:
                            self.press_btn = hb
                    except Exception:
                        pass
                    return True
                # 真实的「新一次按下」→ 开新簇
                self._btn_latch = True
                self._btn_down_ms = now_ms
                self._btn_cluster_ms = now_ms
                took = self.native_press(gx, gy)
            else:
                # ---- 持续按住 ----
                self.native_move(gx, gy)
                took = (self.press_btn >= 0) or (self.ndrag is not None)
        else:
            if self._btn_latch:
                # ---- 松手：派发在 native_release 内完成（用 _btn_cluster_ms 算时长）----
                self._btn_latch = False
                self._btn_up_ms = now_ms
                self.native_release(gx, gy)
        return took

    def _poll_input_self(self):
        """兜底轮询：不依赖 Island。"""
        try:
            if not self.isVisible() or not CFG.get('show_taskbar', True):
                return
            gx, gy, lbtn, _rbtn = _global_mouse()
            self.native_hover(gx, gy)
            self.poll_buttons(gx, gy, lbtn)
        except Exception as e:
            log('tb poll fail: %r' % e)

    def _fit_tray_height(self):
        """按真实任务栏高度决定内容区高度 CH（双行排版的硬约束）。

        任务栏高度随 DPI/缩放大改（本机 150% → 72px，100% → 48px）。
        写字号 10pt 时双行需要 ~56px，任务栏只有 48px 就必须降到 9pt 或缩行距；
        所以这里把 CH 夹在 [CH_MIN, CH_MAX] 且留 8px 上下边距。
        返回实际采用的 CH。"""
        tray = self._tray_rect()
        th = (tray[3] - tray[1]) if tray else 48
        want = int(min(self.CH_MAX, max(self.CH_MIN, th - 8)))
        self.CH = want
        return want

    def apply_cfg(self):
        """外观/显示配置变更后立即生效"""
        try:
            if not CFG.get('tb_show_btns', True):
                self.btns_span = 0.0
            elif not CFG.get('tb_btns_auto_hide', True):
                self.btns_span = 1.0
            self._fit_tray_height()
            self.setFixedSize(int(round(self._cw())) + self.M * 2,
                              self.CH + self.M * 2)
            self.update()
            self.follow()
        except Exception as e:
            log('tb apply_cfg fail: %r' % e)


    # ---------- 挂在任务栏名下（owner，不改窗口类型） ----------
    def _ensure_owned(self, tray):
        """把 Shell_TrayWnd 设为本窗口的 owner。
        owner 恒在本窗口之下 → 点任务栏也不会被盖住；
        同时窗口仍是普通顶层窗口，能正常渲染（SetParent 成子窗口在
        Win11 XAML 任务栏下会被 DWM 压住，不显示）。"""
        u = ctypes.windll.user32
        tray_h = u.FindWindowW('Shell_TrayWnd', None)
        if not tray_h:
            return False
        hwnd = int(self.winId())
        if not u.IsWindow(hwnd):
            # explorer 重启等导致句柄失效 → 强制 Qt 重建
            self.hide()
            self.show()
            hwnd = int(self.winId())
            if not u.IsWindow(hwnd):
                return False
        GWLP_HWNDPARENT = -8
        try:
            get_ = u.GetWindowLongPtrW
            set_ = u.SetWindowLongPtrW
        except AttributeError:                    # 32 位 Python 兜底
            get_ = u.GetWindowLongW
            set_ = u.SetWindowLongW
        self._apply_click_through(hwnd, u)
        if get_(hwnd, GWLP_HWNDPARENT) == tray_h:
            self.hwnd = hwnd
            self.owned = True
            return True
        prev = set_(hwnd, GWLP_HWNDPARENT, tray_h)
        self.hwnd = hwnd
        self.owned = True
        log('tb widget owned by Shell_TrayWnd hwnd=0x%x (prev=0x%x)' % (hwnd, prev or 0))
        log('tb input mode: WM_NCHITTEST (buttons=HTCLIENT, blank=HTTRANSPARENT)')
        return True

    def _apply_click_through(self, hwnd, u):
        """⚠️ v1.4.9 语义**反转**：这里现在**确保移除** `WS_EX_TRANSPARENT`。

        【旧做法（v1.4.0~v1.4.8）】整窗加 `WS_EX_TRANSPARENT` → 窗口整体穿透，
        再用 16ms 轮询 GetCursorPos/GetAsyncKeyState 把点击「猜」回来。
        这导致按钮自己也穿透了，所有点击都得靠采样恢复 → 「按不动 / 连点丢 /
        误拖动」层出不穷（详见 `nativeEvent` 上方长注释）。

        【新做法（v1.4.9，对标 SPlayer-Next）】整窗**不穿透**，
        改由 `WM_NCHITTEST` **逐点**回答：
          · 按钮区 → HTCLIENT（本窗口收下，系统级精确命中，零竞态）
          · 其余区 → HTTRANSPARENT（此处穿透，任务栏照常可用）
        这正是 SPlayer 把窗口嵌进任务栏后依托 OS 命中测试的等价做法。

        保留本函数名与调用点（`_ensure_owned` 里），只是把语义从
        「加上穿透位」改成「确保没有穿透位」——因为 `WS_EX_TRANSPARENT`
        一旦存在会**优先于** WM_NCHITTEST 生效，令我们的判定失效。"""
        GWL_EXSTYLE, WS_EX_TRANSPARENT = -20, 0x00000020
        try:
            ex = u.GetWindowLongW(hwnd, GWL_EXSTYLE) & 0xFFFFFFFF
            if not (ex & WS_EX_TRANSPARENT):
                return
            new_ex = (ex & ~WS_EX_TRANSPARENT) & 0xFFFFFFFF
            if new_ex >= 0x80000000:              # 转回有符号 32 位
                new_ex -= 0x100000000
            u.SetWindowLongW(hwnd, GWL_EXSTYLE, new_ex)
            log('tb widget ex -> 移除 WS_EX_TRANSPARENT（改用 WM_NCHITTEST 逐点命中）')
        except Exception as e:
            log('tb click-through fail: %r' % e)

    def _move_to(self, gx, gy):
        self.move(gx, gy)

    def _screen_pos(self):
        return self.x(), self.y()

    # ---------- 定位 ----------
    def _tray_rect(self):
        user32 = ctypes.windll.user32
        hwnd = user32.FindWindowW('Shell_TrayWnd', None)
        if not hwnd or not user32.IsWindow(hwnd):
            return None
        r = wt.RECT()
        if not user32.GetWindowRect(hwnd, ctypes.byref(r)):
            return None
        if r.bottom - r.top < 30:   # 自动隐藏等异常态
            return None
        return (r.left, r.top, r.right, r.bottom)

    def follow(self):
        try:
            if not CFG.get('show_taskbar', True):
                if self.isVisible():
                    self.hide()
                return
            tray = self._tray_rect()
            if tray is None:
                if self.isVisible():
                    self.hide()
                return
            tl, tt, tr, tb = tray
            # 任务栏高度变了（换显示器/改缩放）→ 重算 CH 与窗口尺寸
            if abs((tb - tt - 8) - self.CH) > 2:
                old = self.CH
                if self._fit_tray_height() != old:
                    self.setFixedSize(int(round(self._cw())) + self.M * 2,
                                      self.CH + self.M * 2)
                    log('tb auto-height: %d -> %d (tray %dpx)' % (old, self.CH, tb - tt))
            # 每第 6 次（约3s）采样一次任务栏亮度，决定文字黑/白
            self._tick += 1
            if self._tick % 6 == 1:
                self._sample_luminance(tl, tt, tr, tb)
            # v1.4.2：悬停展开时窗口变宽 → 左缘会顶到系统托盘左缘，把 tb_x 往回夹，
            # 保证「加宽」永远落在可用区内，而不是压住时钟/托盘图标。
            tb_x = int(CFG.get('tb_x', 100))
            max_x = max(4, (self._tray_free_right() or tr) - tl
                        - int(round(self._cw())) - self.M * 2 - 2)
            if tb_x > max_x:
                tb_x = max_x
            gx = tl + tb_x - self.M
            gy = tt + (tb - tt - self.CH) // 2 - self.M
            if not self.isVisible():
                self.show()
            self._ensure_owned(tray)
            if self.x() != gx or self.y() != gy:
                self.move(gx, gy)
            # 周期重申置顶：owner 关系保证不被任务栏盖住
            ctypes.windll.user32.SetWindowPos(int(self.winId()), -1, 0, 0, 0, 0,
                                              0x0001 | 0x0002 | 0x0010)
        except Exception as e:
            log('tb follow fail: %r' % e)

    def _sample_luminance(self, tl, tt, tr, tb):
        try:
            from PIL import ImageGrab
            # 采样任务栏上缘一条空带（图标都垂直居中，上缘是纯背景色）
            img = ImageGrab.grab(bbox=(tl + 8, tt + 3, min(tl + 300, tr - 8), tt + 7)).convert('RGB')
            px = list(img.getdata())
            if not px:
                return
            n = len(px)
            lum = sum(0.299 * r + 0.587 * g + 0.114 * b for r, g, b in px) / n
            self.dark_text = lum >= 128
        except Exception:
            pass

    # ---------- 布局几何（三键回收/展开靠 span 缩放） ----------
    def _cover_w(self):
        # 封面占位 = 封面宽 + 右侧留白（SPlayer 参照：封面与文字之间要有呼吸感）
        return (self.COVER + self.COVER_GAP) if CFG.get('tb_show_cover', True) else 0

    def _btn_x0(self):
        return self.M + self._cover_w()

    def _span(self):
        if not CFG.get('tb_show_btns', True):
            return 0.0
        return max(0.0, min(1.0, float(self.btns_span)))

    def _btn_rects(self):
        x0 = self._btn_x0()
        y0 = self.M + (self.CH - self.BTN) / 2.0
        return [QRectF(x0 + i * (self.BTN + 2), y0, self.BTN, self.BTN) for i in range(3)]

    def _text_rect(self):
        tx = self._btn_x0() + (self.BTNSPAN + self.GAP) * self._span() + 2
        return tx, self.M, self._cw() + self.M - tx - 6

    # ---------- 悬停时「给歌名/作者让位」（v1.4.2） ----------
    # ⚠️ 问题现场：三键展开把文字区从 372px 挤到 260px，而歌名
    #    'Airplane Mode (Radio Edit)' = 285px → 被 setClipRect 硬裁成
    #    'Airplane Mode (Radio |'。用户明确要求「歌名在上、作者在下时**能完全显示**，
    #    不要部分隐藏」。
    #
    # 解法（两级，都不动用户的 CW 配置）：
    #   ① 悬停看歌名/作者时 → **让整个组件向右「长」出去**，宽度按内容动态加宽，
    #      给两行腾出足够空间（上限到任务栏可用区右缘 / 硬上限 TB_W_MAX）。
    #   ② 宽到上限仍放不下（超长歌名/一长串作者）→ 该行走「滑入 → 停住」滚动，
    #      保证**从头开始显示**且最终整句可见（这就是 v1.4.2 的新滚动模型）。
    # 两种情况的共同结果都是「能完全显示」，不会出现只露左半截。
    TB_W_MAX = 560.0               # 悬停展开时的硬上限（别把任务栏挤爆）
    TB_W_STEP = 1.0                # 目标宽度变化 > 1px 才改窗口（避免每帧抖动）

    def _tb_right_limit(self):
        """组件左缘到「任务栏可用区右缘」之间的最大逻辑宽度。

        任务栏右侧有系统托盘（时钟/网络/音量）与「显示桌面」条，
        不能压过去。可用上界用 `_tray_right_limit_native()`（见下）拿物理坐标，
        再按缩放折回逻辑坐标。"""
        try:
            tray = self._tray_rect()
            if not tray:
                return self.CW
            nl = self._native_rect()[0] if self._native_rect() else None
            if nl is None:
                return self.CW
            lim = self._tray_free_right()
            if lim is None:
                return self.CW
            s = self._logical_scale()[0] or 1.0
            return max(self.CW, (lim - nl) * s)
        except Exception:
            return self.CW

    def _tray_free_right(self):
        """任务栏上「本组件可用」的物理右缘 = 系统托盘区左缘（拿不到则退任务栏右缘）。"""
        try:
            u = ctypes.windll.user32
            tray = u.FindWindowW('Shell_TrayWnd', None)
            if not tray:
                return None
            # Win11: 托盘在 TrayNotifyWnd 子窗口里；拿不到就退任务栏右缘
            r = wt.RECT()
            child = u.FindWindowExW(tray, 0, 'TrayNotifyWnd', None)
            if child and u.GetWindowRect(child, ctypes.byref(r)):
                return int(r.left) - 6
            if u.GetWindowRect(tray, ctypes.byref(r)):
                return int(r.right) - 6
        except Exception:
            pass
        return None

    def _hover_needed_w(self):
        """悬停看歌名/作者时，把两行都完整显示所需的**逻辑宽度**。"""
        name, singer = song_name_singer(STATE.song)
        fs = max(8, int(CFG.get('tb_font', 10)))
        # v1.6.9：按 4.mp4 校准任务栏字体。视频里主行不是重粗体，
        # 更接近 Windows 任务栏的中等字重；副行中文略小但不瘦。
        f_main = QFont('Segoe UI', fs)
        f_main.setWeight(QFont.Medium)
        f_sub = QFont('Microsoft YaHei UI', max(8, int(round(fs * 0.88))))
        f_sub.setWeight(QFont.Normal)
        w_main = QFontMetrics(f_main).horizontalAdvance(name or '未知歌曲')
        w_sub = QFontMetrics(f_sub).horizontalAdvance(singer or '')
        need_text = max(w_main, w_sub) + 4
        tx0 = self._btn_x0() + (self.BTNSPAN + self.GAP) + 2   # 三键全展开时的文字起始 x
        return float(tx0 + need_text + 6 + self.M)

    def _sync_width(self):
        """按「当前是否悬停」把窗口宽度动态调到刚好够用（上限 TB_W_MAX / 任务栏可用右缘）。

        只在变化 > TB_W_STEP 时才 setFixedSize（否则每帧改窗口尺寸会闪）。"""
        if CFG.get('tb_auto_width', True) and self.hover_inside and STATE.connected:
            want = min(self._hover_needed_w(), self.TB_W_MAX, self._tb_right_limit())
            want = max(self.CW, want)
        else:
            want = float(self.CW)
        cur = float(self._w_cur)
        if abs(want - cur) > self.TB_W_STEP:
            self._w_cur = want
            self.setFixedSize(int(round(want)) + self.M * 2, self.CH + self.M * 2)
            self.follow()          # 右缘变化 → 立即重定位（左缘不动）

    def _cw(self):
        """当前实际内容宽（默认 CW；悬停时按内容加宽）。"""
        return float(getattr(self, '_w_cur', self.CW))

    def _text_w(self):
        """当前文字区可用宽度（用实际内容宽算，供绘制与滚动判宽共用）。"""
        tx = self._btn_x0() + (self.BTNSPAN + self.GAP) * self._span() + 2
        return self._cw() + self.M - tx - 6

    def _hit(self, pos, force=False):
        """命中三键。force=True（鼠标已按下）时忽略「展开进度」阈值。

        为什么需要 force：三键是「鼠标悬停才展开」的，展开由 33ms tick 渐进完成
        （约 100ms 才到 0.6）。用户「鼠标快速移过去立刻点」时会撞上这段空窗，
        点到的是「还没展开」的状态 → 按不动（这就是「第一次打开按不了」的根因之一）。
        按下瞬间只要落点在按钮几何范围内就命中，和 SPlayer 的即时可点一致。"""
        if not force and self._span() < 0.6:
            return -1
        for i, r in enumerate(self._btn_rects()):
            if r.contains(QPointF(pos.x(), pos.y())):
                return i
        return -1

    def mousePressEvent(self, ev):
        ev.accept()      # 交互全部由原生轮询处理（_poll_input）

    def mouseMoveEvent(self, ev):
        ev.accept()

    def mouseReleaseEvent(self, ev):
        ev.accept()

    # ---------- ★v1.4.9：WM_NCHITTEST —— 把命中测试交还给操作系统 ★ ----------
    #
    # ⚠️⚠️ 为什么这是「三键能按动」的结构性根治 ⚠️⚠️
    #
    #   我此前（v1.4.0 ~ v1.4.8）的做法是：
    #     ① 整窗加 `WS_EX_TRANSPARENT` → 窗口**整体**鼠标穿透（保住任务栏被点）；
    #     ② 再用 16ms 定时轮询 `GetCursorPos` + `GetAsyncKeyState` 把点击**猜回来**；
    #     ③ 加 4 道闸门（松手沿 / 最短按住 / 松手去抖 / 同键冷却）去滤抖动。
    #   这套组合的每一个 bug（「按不动」「连点丢」「误拖动」「冷启动失灵」）
    #   都不是实现瑕疵，而是**架构上的将错就错**：
    #     · 整窗穿透 → 按钮自己也穿透了 → 必须靠全局钩子捡回来；
    #     · 轮询是**采样**，按下的瞬间边沿可能整帧丢在两次轮询之间；
    #     · 采样噪声（坏坐标瞬移）会污染拖动判定 → 组件被拽走。
    #
    #   SPlayer-Next 怎么做（读它的原生模块 `resources/native/taskbar-lyric.node`
    #   + `out/main/index.js` 得到）：
    #     · 它**没有一行手工轮询**；
    #     · 它把窗口嵌进任务栏层级后，**命中测试完全由 Windows 做**——
    #       鼠标落在实心像素上就是按钮，落在透明像素上系统自动穿透给任务栏。
    #
    #   Windows 上做「局部可点、其余穿透」的**标准且唯一正确**的 API 就是
    #   `WM_NCHITTEST`：
    #     · 返回 `HTTRANSPARENT` → 这一点的**所有鼠标消息**转交给下面的窗口
    #       （等于此处穿透，任务栏照常被点）；
    #     · 返回 `HTCLIENT`     → 本窗口接收（按钮点击）。
    #   它由 OS 在**每一次鼠标消息**上同步询问（不是采样、不是轮询），
    #   命中是精确的、无竞态的、零延迟的。
    #
    #   于是本类现在的输入架构变为：
    #     · 去掉整窗 `WS_EX_TRANSPARENT`（见 `_apply_click_through`）；
    #     · `nativeEvent` 拦 `WM_NCHITTEST`，按**逐点**命中回答 HTCLIENT /
    #       HTTRANSPARENT —— 按钮区可点、歌词区穿透、拖动区给 HTCAPTION；
    #     · 老的四道闸门 + 轮询**保留不动**（作为兼容层：它们仍驱动
    #       hover 展开/高亮与拖动，且在新的「按钮已经能真正收到点击」前提下，
    #       两条路都指向同一个 `native_*` 入口，幂等、不会重复派发）。
    #
    #   `WM_NCHITTEST` = 0x0084；HTTRANSPARENT = -1；HTCLIENT = 1；HTCAPTION = 2。

    def nativeEvent(self, eventType, message):
        """拦截 WM_NCHITTEST：逐点决定「本窗口吃点击」还是「穿透给任务栏」。

        `message` 是 sip.voidptr（PyQt5）→ 需要 `int(message)` 拿到地址，
        再把它 cast 成 `MSG*`（ctypes）读取 lParam。

        lParam 是 **物理像素**的屏幕坐标（低 16 位 x、高 16 位 y，有符号），
        与 `_hit_global` 的坐标系一致 → 直接复用既有命中逻辑。

        ⚠️ 返回值契约（PyQt5）：(handled: bool, result: int)
          · handled=True  → 用 result 作为窗口过程返回值（**必须**这样返回
            结果，否则 Qt 会去调默认处理，我们的判定就丢了）；
          · 这里恒返回 (True, hit_code)，因为 WM_NCHITTEST 永远由我们回答。"""
        try:
            if eventType != b'windows_generic_MSG':
                return super().nativeEvent(eventType, message)
            msg = ctypes.cast(int(message), ctypes.POINTER(wt.MSG)).contents
            if msg.message != 0x0084:            # WM_NCHITTEST
                return super().nativeEvent(eventType, message)
            lp = msg.lParam
            # lParam 低/高 16 位是**有符号**屏幕坐标（多屏负坐标也要对）
            gx = lp & 0xFFFF
            gy = (lp >> 16) & 0xFFFF
            if gx >= 0x8000:
                gx -= 0x10000
            if gy >= 0x8000:
                gy -= 0x10000
            if not (self.isVisible() and CFG.get('show_taskbar', True)):
                return True, HTTRANSPARENT
            h = self._hit_global(gx, gy, force=True)
            if h >= 0:
                # 落在三键上 → 本窗口收下这次点击（按钮才真正「按得动」）
                return True, HTCLIENT
            if h == -1:
                # 落在组件内的空白/文字区：默认穿透，让任务栏照常可用。
                # 只有用户**明确按住空白区拖动**时才由轮询路径处理拖动
                # （拖动靠 native_move 的位移阈值，不靠 HTCAPTION，
                #   否则单击空白区会被系统当成窗口拖动而吃掉任务栏点击）。
                return True, HTTRANSPARENT
            # 窗口外（含边距外）：穿透
            return True, HTTRANSPARENT
        except Exception as e:
            log('tb nativeEvent fail: %r' % e)
            return super().nativeEvent(eventType, message)

    # ---------- 原生输入（由 Island._poll_input 调用） ----------
    #
    # ⚠️⚠️ 坐标基准铁律（2026-10-07 实机踩坑，三键「第一次按不动」的真根因）⚠️⚠️
    #   本机系统 DPI = 144（150% 缩放）。`GetCursorPos` / `GetAsyncKeyState` 走的是
    #   Win32 **物理像素**；而 Qt 的 `self.x()/self.y()` 是 **逻辑像素**。
    #   两者实测差 (893, -800)（Qt x=170 vs 原生 left=1063）。
    #   → 早期 `_hit_global` 写 `gx - self.x()`，等于「物理坐标 减 逻辑坐标」，
    #     结果必然落在窗口外 → 返回 -2 → `native_press` 直接 False → 三键永远点不动。
    #   修法：**命中判定一律用 GetWindowRect 的物理坐标**（与 GetCursorPos 同坐标系），
    #   绝不用 Qt 的 x()/y()/width()/height()。
    def _native_rect(self):
        """Win32 物理坐标矩形 (l, t, r, b)——与 GetCursorPos 同一坐标系。

        不用 Qt 的 self.x()/width()：150% 缩放下 Qt 给的是逻辑坐标，混用必失配。"""
        try:
            r = wt.RECT()
            hwnd = int(self.winId())
            if not ctypes.windll.user32.GetWindowRect(hwnd, ctypes.byref(r)):
                return None
            return (r.left, r.top, r.right, r.bottom)
        except Exception:
            return None

    def _hit_global(self, gx, gy, force=False):
        """全局坐标命中：-1 窗口内空白区（可拖动）/ -2 窗口外 / >=0 按钮索引

        gx/gy 来自 `GetCursorPos` = **物理像素** → 基准必须用 `_native_rect()`。
        逻辑尺寸 (width/height) 与物理尺寸在 150% 下差 1.5 倍，因此临时按
        dpr 折算"物理尺寸"再判窗口边界。"""
        if not self.isVisible():
            return -2
        nr = self._native_rect()
        if nr is None:
            return -2
        nl, nt, nr_r, nb = nr
        # 物理尺寸下的「窗口内」判据（比逻辑宽度大 dpr 倍，需按实际 rect 反推）
        pw, ph = nr_r - nl, nb - nt
        lx, ly = gx - nl, gy - nt
        if not (0 <= lx < pw and 0 <= ly < ph):
            return -2
        # 逻辑坐标（Qt 绘制坐标系）下做按钮命中，需把物理偏移按比例折回
        sx = (self.width() / float(pw)) if pw else 1.0
        sy = (self.height() / float(ph)) if ph else 1.0
        return self._hit(QPoint(int(lx * sx), int(ly * sy)), force=force)

    def native_hover(self, gx, gy):
        """鼠标悬停跟踪（16ms 一次）。它决定三件事：
        ①三键是否展开 ②按钮 hover 高亮 ③**文字是否切为「歌名 / 作者」**
        （③ 对标 SPlayer：鼠标移进感应区看歌名，移开恢复歌词 → 必须立即重绘）"""
        vis = self.isVisible() and bool(CFG.get('show_taskbar', True))
        nr = self._native_rect() if vis else None
        if nr is None:
            inside = False
        else:
            nl, nt, nr_r, nb = nr
            # 同样用物理 rect（GetCursorPos 同坐标系）
            inside = (nl - 4 <= gx <= nr_r + 4 and nt - 4 <= gy <= nb + 4)
        inside = bool(vis and inside)
        if inside != self.hover_inside:
            self.hover_inside = inside
            self._sync_width()     # 悬停进出 → 给歌名/作者腾地方（或收回）
            self.update()          # 悬停进出 → 歌名/歌词 切换要立刻可见
        # force=True：悬停就已展开，按钮紧接着的高亮不该等动画跑完才出现
        h = self._hit_global(gx, gy, force=True) if vis else -2
        hb = h if h >= 0 else -1
        if hb != self.hover_btn:
            self.hover_btn = hb
            self.update()

    def native_press(self, gx, gy):
        # force=True：按下瞬间忽略展开进度阈值 → 快速移过去直接点也能命中三键
        h = self._hit_global(gx, gy, force=True)
        if h == -2:
            return False
        if h >= 0:
            self.press_btn = h
            self._press_at = (gx, gy)      # 记住按下点：用于「位移阈值」判定
            self._drag_armed = False       # 按钮按下 → 本次绝不允许转成拖动
            self.ndrag = None
            # 命中按钮时立即把三键区展开到位，视觉上不会「点了才慢慢滑出来」
            if CFG.get('tb_btns_auto_hide', True):
                self.btns_span = 1.0
        else:
            # ⚠️ 空白区按下 ≠ 立刻开始拖动。用户想点的按钮如果因为
            #    hover 展开动画还没到位（span<1）而落在「按钮矩形之外」，
            #    这里会返回 -1 → 旧代码直接进拖动分支 → 松手时
            #    `native_release` 走拖动路径 → **把 tb_x 改掉、组件被拽走**。
            #    实测踩到：debug.log 出现 `tb drag release -> tb_x=182`，
            #    组件位置被写坏，之后按钮再也点不到（命中区跟着窗口跑偏）。
            #    修法：先记住「疑似拖动起点」，等移动超过阈值才真正开始拖。
            self.ndrag = None
            self._press_at = (gx, gy)
            self._drag_armed = True        # 允许拖动（但还要过 native_move 的阈值）
            self._drag_moved = False       # 本次按下「是否真的拖动过」
        log('tb press hit=%d at (%d,%d)' % (h, gx, gy))
        self.update()
        return True

    def native_move(self, gx, gy):
        """拖动：gx/gy 是物理像素，而 Qt 的 move() 吃逻辑坐标 → 位移量必须折算。

        位移差分其实是缩放无关的（dx 物理 × 1/dpr = dx 逻辑），所以直接除 dpr。

        ⚠️ 拖动必须过「启动阈值」（见 native_press）：空白区按下后手指/鼠标抖动
        几像素不应把组件拖走 —— 那会把 CFG['tb_x'] 写坏、组件跑偏，
        表现就是「三键突然全都点不动」（命中区跟着窗口跑了）。
        ⚠️ 三键按下期间**绝不允许**拖动：否则「按住按钮手一抖」= 组件被拽走，
        松手时按钮早就跑出光标位置 → 点了没反应。"""
        if self.press_btn >= 0:
            return                         # 有按钮在按 → 这不是拖动
        if not getattr(self, '_drag_armed', False):
            return                         # 本次按下不允许拖动（按钮态）
        pa = getattr(self, '_press_at', None)
        if pa is None:
            return
        dx, dy = gx - pa[0], gy - pa[1]
        # ⚠️ v1.4.7 坏样本防御：单 tick 光标瞬移 >60px 不是人手拖动。
        #    实测（v1.4.6 验收 E1）：press 采样到瞬时坏坐标，下一 tick 读回
        #    真实位置 → dx=83px 直接触发开拖 → 组件被拽走、tb_x 写坏，
        #    之后按钮命中区跟着窗口跑偏 → 三键全点不动。
        #    60px/16ms tick = 3750px/s，人手快速甩动不受影响。
        if self.ndrag is None and (abs(dx) > 60 or abs(dy) > 60):
            self._press_at = (gx, gy)
            return
        # 阈值按物理像素：moved 超过 6px 才算「真的要拖」
        if self.ndrag is None:
            if abs(dx) < 6 and abs(dy) < 6:
                return
            # 首次越过阈值 → 正式开始拖动（以按下点为基准，避免起步跳一下）
            self.ndrag = (pa[0], pa[1])
        dx, dy = gx - self.ndrag[0], gy - self.ndrag[1]
        if dx or dy:
            s = self._logical_scale()
            self.move(self.x() + int(round(dx * s[0])),
                      self.y() + int(round(dy * s[1])))
            self.ndrag = (gx, gy)
            self._drag_moved = True        # 标记「确实拖动过」（release 据此决定是否写 tb_x）

    def _logical_scale(self):
        """物理→逻辑的换算系数 (sx, sy)。150% 缩放下 ≈ (1/1.5, 1/1.5)。"""
        nr = self._native_rect()
        if nr is None:
            return (1.0, 1.0)
        pw, ph = nr[2] - nr[0], nr[3] - nr[1]
        sx = (self.width() / float(pw)) if pw else 1.0
        sy = (self.height() / float(ph)) if ph else 1.0
        return (sx, sy)

    def native_release(self, gx, gy):
        if self.ndrag is not None:
            self.ndrag = None
            self._drag_armed = False
            self._press_at = None
            # ⚠️⚠️ 绝对保险（v1.4.3）：本次按下如果是「按钮态」（press_btn >= 0），
            #   就**绝不能**写 tb_x —— 哪怕 ndrag 被误置。
            #   实机日志抓到的灾难序列（旧版）：
            #     tb press hit=-1 at (493,1561)
            #     tb drag release -> tb_x=282      ← 组件被拖走
            #     tb press hit=-1 at (309,1565)    ← 位置变了 → 全点空
            #     tb drag release -> tb_x=218
            #   一连 5 次把组件拖来拖去 → 用户看到的就是「三键完全按不动」。
            if self.press_btn >= 0:
                log('tb release (was button press) -> keep tb_x=%s' % CFG.get('tb_x'))
                self._drag_moved = False
                self._btn_down_ms = None
                self.follow()
                return
            # 只有「确实拖动过」才写回 tb_x（v1.4.2 加固）：
            #   native_press 空白分支 _drag_moved=False，真正的移动才置 True。
            if not getattr(self, '_drag_moved', False):
                log('tb release (armed but never moved) -> keep tb_x=%s' % CFG.get('tb_x'))
                self._drag_moved = False
                self._btn_down_ms = None
                self.follow()
                return
            self._drag_moved = False
            tray = self._tray_rect()
            if tray and self._native_rect():
                # tb_x 是「相对任务栏左缘的逻辑偏移」→ 用物理 rect 算再折回逻辑
                s = self._logical_scale()[0]
                nl = self._native_rect()[0]
                # 与 follow() 同一套右缘夹取：别让条子压住时钟/系统托盘
                mx = max(4, (self._tray_free_right() or tray[2]) - tray[0]
                         - int(round(self._cw())) - self.M * 2 - 2)
                CFG['tb_x'] = min(mx, max(4, int(round((nl - tray[0]) * s)) + self.M))
                save_cfg(CFG)
            log('tb drag release -> tb_x=%s' % CFG['tb_x'])
            self.follow()
            return
        # ⚠️ 松手判据（v1.4.2 加固）：
        #   旧代码要求 `h >= 0 and h == self.press_btn`（按下/松手索引必须完全一致）。
        #   问题：按下后『三键展开动画』会让文字区变窄、按钮随之整体左移
        #   （span 0→1 时 bx 不变，但宽度自适应会改窗口），落点可能从一个按钮
        #   偏移到相邻按钮 → 索引不等 → **一次都不触发**。用户感觉就是「按不动」。
        #   改为：只要松手时**仍落在某个按钮上**就触发它（这才是用户的人眼预期）；
        #   只有在完全没命中按钮时才丢弃。
        h = self._hit_global(gx, gy, force=True)
        if h < 0 and self.press_btn >= 0:
            # 落点漂出按钮外一点点（手抖/动画位移）→ 回退用按下时的按钮，
            # 但要确认光标仍在该按钮附近（±BTN 容差），避免「按住拖走又松手」误触发。
            br = self._btn_rects()[self.press_btn]
            nr = self._native_rect()
            if nr is not None:
                s = self._logical_scale()
                lx = (gx - nr[0]) * s[0]
                ly = (gy - nr[1]) * s[1]
                if (br.left() - self.BTN) <= lx <= (br.right() + self.BTN) \
                   and (br.top() - self.BTN) <= ly <= (br.bottom() + self.BTN):
                    h = self.press_btn
        if h >= 0:
            cmd = ('prev', 'toggle', 'next')[h]
            # ---------- v1.4.4 闸门：一次物理点击 = 恰好一条命令 ----------
            # `hold` = **整个抖动簇**的总时长（取 `_btn_cluster_ms`，它跨松手存活），
            # 不是最后一次按下的时长 —— 所以「按住 600ms 手抖」不会被误判成抖动。
            now_ms = time.monotonic() * 1000.0
            start = self._btn_cluster_ms if self._btn_cluster_ms is not None \
                else self._btn_down_ms
            hold = (now_ms - start) if start is not None else 1e9
            since = now_ms - self._btn_fire_ms[h]
            if hold < self.BTN_MIN_HOLD:
                # 闸门 ② 太短：整簇都没到人手最快点击时长 → 抖动，丢弃
                self._btn_drop += 1
                log('tb button %s DROPPED (cluster=%.1fms < %.0fms, jitter)'
                    % (cmd, hold, self.BTN_MIN_HOLD))
            elif since < self.BTN_COOLDOWN:
                # 闸门 ④ 冷却：同键上一次派发还太近 → 同一次点击的重放，丢弃
                self._btn_drop += 1
                log('tb button %s DROPPED (cooldown %.1fms < %.0fms)'
                    % (cmd, since, self.BTN_COOLDOWN))
            else:
                self._btn_fire_ms[h] = now_ms
                log('tb button %s (cluster=%.0fms)' % (cmd, hold))
                taskbar_button_control(cmd)
        else:
            # v1.4.7 可观测性：松手既没落在按钮上、也没有可回退的按下按钮
            log('tb release miss (h=-1, press_btn=%s)' % self.press_btn)
        self.press_btn = -1
        self._drag_armed = False
        self._press_at = None
        self._btn_down_ms = None      # 「当前是否按住」= 否
        # ⚠️ `_btn_cluster_ms` **故意不清**：簇是否结束要等下次按下的间隔来判断
        self.update()

    def leaveEvent(self, ev):
        ev.accept()

    # ---------- 16ms tick（≈60fps）：三键回收/展开动画 + 卡拉OK重绘 ----------
    def tick(self):
        try:
            # v1.4.2：宽度自适应（悬停看歌名/作者时加宽，保证两行完全显示）
            self._sync_width()
            # SPlayer 式滚动（v1.4.9 = 歌词进度驱动）：**不需要在这里推进任何时钟**——
            #   偏移量的自变量是 `STATE.now()`（播放进度），由 `_marq_off` 现算。
            #   这里只负责把「当前句的正文 + start/end 时间轴」告诉滚动逻辑。
            now = time.time()
            dt = (now - getattr(self, '_marq_last', now)) * 1000.0
            self._marq_last = now
            if dt < 0 or dt > 400:      # 时钟跳变/长时间挂起 → 丢弃这一拍
                dt = 0.0
            self._marq_dt = dt if STATE.is_playing else 0.0
            cur, _ = self._cur_line()
            self._marq_set_text((cur[2] if cur else None), line=cur)
            show = bool(CFG.get('tb_show_btns', True))
            if not show:
                target = 0.0
            elif CFG.get('tb_btns_auto_hide', True):
                # 鼠标移到组件上（或正在按/拖）→ 展开，否则回收，给歌词让位
                target = 1.0 if (self.hover_inside or self.ndrag is not None
                                 or self.press_btn >= 0) else 0.0
            else:
                target = 1.0
            # 时间常数 100ms 的指数逼近（与帧率无关）。
            # ⚠️ 原来写死 `* 0.30` 是按 33ms 调的；tick 改 16ms 后就会「快一倍」。
            #    改成 1 - exp(-dt/tau)，帧率怎么变，展开时长都稳定（且 60fps 下更顺）。
            # ⚠️ dt 退化保护：单测里连调 tick() 无间隔，dt≈0 → k 会塌到 0，永远展不开。
            #    把「dt 不合理地小」视为 1 帧（16ms），保证任何调用节奏下行为一致。
            if abs(self.btns_span - target) > 0.004:
                tau = 100.0
                d = dt if dt >= 1.0 else 16.0
                k = 1.0 - pow(2.718281828, -d / tau)
                self.btns_span += (target - self.btns_span) * min(1.0, max(0.01, k))
                self.update()
            elif self.btns_span != target:
                self.btns_span = target
                self.update()
            # v1.5.0 hover 淡入淡出：歌词列 ↔ 歌名/作者（400ms 对齐 SPlayer）
            hover_target = 1.0 if self.hover_inside else 0.0
            if abs(self.hover_alpha - hover_target) > 0.004:
                tau = 160.0                    # ≈400ms 完成 95%
                d = dt if dt >= 1.0 else 16.0
                k = 1.0 - pow(2.718281828, -d / tau)
                self.hover_alpha += (hover_target - self.hover_alpha) * min(1.0, max(0.01, k))
                self.update()
            elif self.hover_alpha != hover_target:
                self.hover_alpha = hover_target
                self.update()
            # ⚠️⚠️【v1.7.11 关键】换句「放大」动画必须**自己**保证帧投递。
            #   动画的时间轴在 paintEvent 里（`time.time() - _fade_t0`），但
            #   **谁负责在这 0.4s 内反复 repaint？** 原先只有下面三个条件：
            #   「逐字高亮」要求本句带字级时间戳、「跑马灯」要求整句超宽、
            #   `maybe_refresh()` 的 key 在动画期间根本不变。于是**纯 LRC 歌词**
            #   （无字级时间戳、句子又放得下）时，换句那 0.4s 里**一帧都不重绘**。
            #   实测（flow_probe.py，3.85s 连续采样）：总共只有 5 次 paintEvent，
            #   每个换句窗口**跨度 0.0ms / 只有 1 帧**，主行字号序列全是 10.00
            #   —— 也就是这个「放大」根本没播出来，只有一次生硬跳变。
            #   对标 SPlayer：那边只改一次 class 列表，**浏览器自己**保证过渡期间
            #   每一帧都合成。这里做等价动作 —— 动画窗口内无条件 update()。
            if self._swap_active():
                self.update()          # 换句放大动画：必须每帧重绘（≈60fps）
            elif self._karaoke_active():
                self.update()          # 逐字高亮：需要持续重绘
            elif self._marquee_active():
                self.update()          # 文本超宽 → 跑马灯需要持续重绘
            else:
                self.maybe_refresh()
        except Exception as e:
            log('tb tick fail: %r' % e)

    def _cur_line(self):
        if not STATE.connected:
            return None, None
        with STATE.lock:
            lines = list(STATE.lines)
        if not lines:
            return None, None
        _, cur, nxt = current_line(lines, STATE.now() * 1000.0)
        return cur, nxt

    def _karaoke_active(self):
        cur, _ = self._cur_line()
        return bool(cur is not None and cur[4] and STATE.is_playing)

    def _swap_active(self):
        """换句「放大」动画是否还在进行（窗口 = 0.40s，见 paintEvent 的 `fdt < 0.40`）。

        ⚠️ 这里用 `_fade_t0` 而不是 `_fade_from`：后者在**动画结束那一帧**会被
        paintEvent 清掉（`fdt >= 0.40 → self._fade_from = None`），而那一帧恰恰是
        必须画出来的最后一帧（否则最后会少一帧、结尾位置就停在半路）。
        多留 50ms 余量把它兜住。前 0.45s 之外一律返回 False（不浪费重绘）。
        """
        t0 = float(getattr(self, '_fade_t0', 0.0) or 0.0)
        if not t0:
            return False
        return (time.time() - t0) < 0.45

    # ---------- SPlayer 式滚动（v1.4.9 重写：**由歌词演唱进度驱动**） ----------
    #
    # ⚠️⚠️ 模型定稿依据（2026-10-07 第四轮）⚠️⚠️
    #   前三轮的模型（v1.4.6 匀速循环 / v1.4.8 固定 900ms ease-out）**都是错的**，
    #   用户两次反馈「不一致、显得任务栏很乱」。本轮不再靠 4.mp4 抽帧反推
    #   （2fps/10fps 抽帧会把缓动尾段误读成匀速、把停住误读成还在动），
    #   而是**直接读 SPlayer-Next 的安装文件**，拿到权威实现。
    #
    #   权威源码：E:\NetMusic\SPlayer-Next\resources\app.asar
    #             → out/renderer/assets/taskbar-lyric-BNn4HZI5.js
    #   逆向记录：E:\workbuddy\2026-10-04-19-30-25\moekoe_island\SPLAYER_REFERENCE.md
    #
    #   SPlayer 的 getScrollTransform（原始语义）：
    #     SCROLL_START_AT = 0.3    // 唱到该句 30% 才开始滚
    #     END_MARGIN_MS   = 2000   // 句尾**前 2 秒**必须已经滑完
    #     end      = max(start+1, endTime - 2000)
    #     progress = clamp01((cur - start) / (end - start))
    #     progress <= 0.3 → offset = 0
    #     否则 → offset = overflow * (progress - 0.3) / 0.7      ← **纯线性！**
    #
    #   ★核心：滚动的自变量是**该句歌词的播放进度**，不是独立时钟。
    #     · 什么速度滚 → 由「这句话演唱多久」决定（长句慢、短句快，自然）
    #     · 何时开始滚 → 唱到 30%
    #     · 滚到何时   → 句尾前 2 秒刚好到位
    #     · 没有 easing → 线性（我前几轮反推出来的「ease-out」是抽帧误判）
    #     · 暂停 → cur 不变 → progress 不变 → **位置天然冻结**
    #     · 换句 → progress 重新从 0 起算 → **天然从句首重新开始**
    #
    #   v1.6.7 在此基础上加“每句节奏自适应”：同样按 `STATE.lines` 的
    #   (start, end) 算，但不再让所有歌曲固定 30% 起滚 / 提前 2s 结束。
    #   快歌短句更早滚、尾部少预留；慢歌长句保留更久，滚动更稳。
    #
    # ⚠️ 旧常量 MARQ_SPEED / MARQ_GAP / MARQ_SLIDE_MS / MARQ_EASE_POW / MARQ_TAIL
    #    已全部不再参与相位计算。MARQ_TAIL 保留为**绘制收尾呼吸**（句尾不贴边），
    #    MARQ_SLIDE_MS / MARQ_EASE_POW 保留常量以免旧测试 import 报错。
    SCROLL_START_AT = 0.30         # 默认起滚点；实际由 _marq_profile 按本句节奏调整
    END_MARGIN_MS = 2000.0         # 默认句尾预留；实际由 _marq_profile 按本句节奏调整
    MARQ_TAIL = 6.0                # 到位后句尾再留 6px 呼吸（避免贴边裁字）
    MARQ_SLIDE_MS = 900.0          # 【已废弃】仅保留供旧测试引用
    MARQ_EASE_POW = 2.6            # 【已废弃】仅保留供旧测试引用
    MARQ_SPEED = 110.0 / 1000.0    # 【已废弃】仅保留供旧测试引用
    MARQ_GAP = 60.0                # 【已废弃】仅保留供旧测试引用

    def _marq_set_text(self, text, line=None):
        """tick 里告知当前要滚的正文（+ 该句的 start/end 时间轴）。

        换句 → 记录新的 (text, start, end)。相位不再需要「归零」——
        因为偏移量每次都由**当前播放进度**现算（见 `_marq_off`），
        换句后 progress 自然回到 0 → 天然从句首开始。"""
        if text != getattr(self, '_marq_text', None):
            self._marq_text = text
            self._marq_t = 0.0            # 兼容旧字段（诊断用）
        if line is not None and len(line) >= 2:
            self._marq_start = float(line[0] or 0)
            self._marq_end = float(line[1] or 0)
        elif text is None:
            self._marq_start = 0.0
            self._marq_end = 0.0

    def _marq_travel(self, tw, w):
        """从「句首贴左」滑到「句尾刚好露出」需要左移的像素数。

        ⚠️ 参数约定（**务必看清**）：调用方一律传 `(文字宽, 可视宽)`
        （如 `_marq_off(w, maxw)`，w=文本宽度、maxw=文字区宽度）。
        因此本函数内 **tw = 文字宽、w = 可视宽**，需要左移的量就是
        `tw - w`（文字超出可视区多少），再 +TAIL 收尾。
        """
        return max(0.0, tw - w + self.MARQ_TAIL)

    def _marq_dur(self, tw, w):
        """（兼容保留）放不下才滚。真实时长由「歌词演唱进度」决定，
        这里只回答「需不需要滚」：需要 → >0，不需要 → 0。"""
        if tw <= w:
            return 0.0
        return max(1.0, self._marq_travel(tw, w))

    def _marq_profile(self, tw, w, line_ms):
        """按“这一句自己的节奏”决定横向滚动窗口。

        固定参数会让不同语言/不同 BPM 的歌显得不贴合：快歌来不及滚完，
        慢歌又过早把尾巴露出来。这里用两个信号做自适应：
          · line_ms：这一句持续多久，越短说明节奏越快；
          · overflow_ratio：文字超出可视区多少，越长越需要早滚。
        返回：(start_at, end_margin_ms)。"""
        if tw <= w:
            return self.SCROLL_START_AT, self.END_MARGIN_MS
        line_ms = max(800.0, float(line_ms or 0.0))
        overflow_ratio = max(0.0, (tw - w) / max(1.0, w))

        if line_ms < 2400.0:
            start_at = 0.10
        elif line_ms < 4200.0:
            start_at = 0.16
        elif line_ms < 7000.0:
            start_at = 0.24
        else:
            start_at = 0.32
        start_at -= min(0.10, overflow_ratio * 0.08)
        start_at = max(0.06, min(0.36, start_at))

        # 尾部预留不能比整句还长。短句/快歌少留，长句/慢歌多留。
        end_margin = min(2200.0, max(350.0, line_ms * 0.22))
        if overflow_ratio > 0.45:
            end_margin *= 0.75
        end_margin = min(end_margin, max(250.0, line_ms * 0.38))
        return start_at, end_margin

    def _marq_off(self, tw, w):
        """读当前滚动偏移（纯函数、无状态推进）。参数：(文字宽, 可视宽)。

        v1.6.7 模型 = **歌词进度驱动 + 每句节奏自适应**：
          overflow = travel；profile = _marq_profile(文字宽、可视宽、本句时长)
          progress <= profile.start  → 0
          progress  > profile.start  → 线性滚向 overflow
          progress 到 1              → overflow（到位后停住）

        行为推论（全部与 SPlayer 一致）：
          · 长句滚得慢、短句滚得快（由该句演唱时长决定）
          · 暂停 → cur 不变 → 位置冻结（自然满足「暂停不滚」）
          · 换句 → progress 归 0 → 从句首重新开始
          · 到位后停住，不回绕、不倒退、不循环
          · 中止于 `travel`（< tw）→ **只需画一份文本**，不会整体出画

        ⚠️ 暂停特例（v1.4.3 用户历轮要求的「暂停整句可见」）：
          SPlayer 暂停时是「冻结在当前位置」（可能只露半句）。我们的用户
          明确要求暂停时**整句看得全**，所以暂停且尚未滑完时直接给 travel
          （句尾露出位）。这是与 SPlayer 唯一的**有意**差异，已保留。"""
        if tw <= w:
            return 0.0                     # 放得下 → 不动
        travel = self._marq_travel(tw, w)
        if travel <= 0:
            return 0.0
        start = float(getattr(self, '_marq_start', 0.0) or 0.0)
        end = float(getattr(self, '_marq_end', 0.0) or 0.0)
        if not STATE.is_playing:
            # 暂停：不滚。整句可见（句尾露出位）—— v1.4.3 语义保留。
            return travel
        if end <= start:
            # 没有时间轴（无逐句时间 / 纯文本歌词）→ 退化为「匀速滑完」
            # 以免完全不滚。用播放位置兜底，速度固定 = overflow / 6s。
            cur = STATE.now() * 1000.0
            prog = min(1.0, max(0.0, (cur - start) / 6000.0))
            p = 1.0 - (1.0 - prog) ** 2.0     # 无时间轴时略作缓出（无实测约束）
            return travel * p
        line_ms = max(1.0, end - start)
        start_at, end_margin = self._marq_profile(tw, w, line_ms)
        end2 = max(start + 1.0, end - end_margin)
        dur = end2 - start
        if dur <= 0:
            return 0.0
        cur = STATE.now() * 1000.0
        progress = max(0.0, min(1.0, (cur - start) / dur))
        if progress <= start_at:
            return 0.0
        ratio = (progress - start_at) / max(0.01, (1.0 - start_at))
        return travel * ratio

    def _marq_advance(self, dt_ms, text, w, font):
        """（兼容保留的测试入口）按 dt 推进时间轴并返回偏移。

        v1.4.9 起滚动由「歌词进度」决定，相位不再是独立时钟；
        本函数改为：把 `_marq_start/_marq_end` 当作时间轴、dt 累加播放位置。
        生产路径请用 `_marq_set_text()` + tick。"""
        self._marq_set_text(text)
        fm = QFontMetrics(font)
        tw = fm.horizontalAdvance(text or '')
        if not text or tw <= w:
            return 0.0
        self._marq_t = getattr(self, '_marq_t', 0.0) + max(0.0, dt_ms)
        # 用 `_marq_t` 冒充「已播放毫秒」，无时间轴时走退化分支
        st, en = getattr(self, '_marq_start', 0.0), getattr(self, '_marq_end', 0.0)
        if en <= st:
            self._marq_start, self._marq_end = 0.0, 0.0
        return self._marq_off(tw, w)

    def _marquee_active(self):
        """是否需要为「跑马灯」持续重绘。

        ⚠️⚠️【v1.7.13】**恒返回 False**：任务栏已改为不滚动（见 `NO_SCROLL`）——
        超宽行一律右端省略号、文本位置恒定，没有任何逐帧位移，自然不需要 60fps 重绘。
        （逐字卡拉OK 由 `_karaoke_active()` 驱动、换句放大由 `_swap_active()` 驱动，
        两者与跑马灯无关，不受本次改动影响。）"""
        if self.NO_SCROLL:
            return False
        return bool(getattr(self, '_marquee', False)) and bool(STATE.is_playing)

    def _colors(self):
        """返回 (主文字色, 次要文字色, 高亮色, 是否深色文字)。

        ⚠️ 主题语义容易写反：组件是**透明**的，文字直接画在任务栏背景上，所以
        「浅色任务栏」需要**深色文字**，「深色任务栏」需要**浅色文字**。
        即 tb_theme 描述的是「**任务栏**的底色」，不是「文字颜色」：
          light  = 浅色任务栏 → 深色文字
          dark   = 深色任务栏 → 浅色文字
          custom = 用户指定文字色（tb_text）
          auto   = 按实测任务栏亮度自动选（dark_text=True 表示任务栏亮 → 深色字）
        """
        theme = CFG.get('tb_theme', 'auto')
        if theme == 'light':
            base = QColor(24, 24, 26)          # 浅底 → 深字
        elif theme == 'dark':
            base = QColor(246, 246, 248)       # 深底 → 亮字
        elif theme == 'custom':
            base = qcol(CFG.get('tb_text'), fallback='#1a1a1a')
        else:
            base = QColor(24, 24, 26) if self.dark_text else QColor(246, 246, 248)
        sub = QColor(base)
        sub.setAlpha(153)                     # 次要行（翻译）淡一点
        accent = qcol(CFG.get('tb_accent'), fallback='#2F80ED')
        return base, sub, accent, (base.lightness() < 128)

    # ---------- 渲染 ----------
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        with STATE.lock:
            playing = STATE.is_playing
            connected = STATE.connected

        base, sub_col, accent, is_dark_text = self._colors()
        span = self._span()

        # 封面（圆角方形，静态；可在设置里关闭）
        if CFG.get('tb_show_cover', True):
            if STATE.song_gen != self.cover_gen:
                self.cover_gen = STATE.song_gen
                self.cover_pm = load_cover_pixmap(STATE.song)
            cover = self.cover_pm if self.cover_pm is not None else self.default_cover
            p.drawPixmap(self.M, self.M + (self.CH - self.COVER) // 2,
                         rounded_cover(cover, self.COVER, self.R_COVER))

        # 三键：宽度方向「卷出/卷回」+ 透明度渐变（回收时给歌词让出空间）
        if span > 0.01:
            p.save()
            p.setClipRect(QRectF(self._btn_x0(), 0, self.BTNSPAN * span, self.height()))
            hov = QColor(0, 0, 0, 28) if is_dark_text else QColor(255, 255, 255, 36)
            col_n = QColor(base); col_n.setAlpha(int(255 * span))
            for i, r in enumerate(self._btn_rects()):
                pressed = (i == self.press_btn)
                hovered = (i == self.hover_btn)
                if hovered and span > 0.6:
                    p.setBrush(hov); p.setPen(Qt.NoPen)
                    p.drawEllipse(r.adjusted(1, 1, -1, -1))
                if pressed:
                    # v1.5.0 更强的按下反馈：实心反差圆底
                    pb = QColor(0, 0, 0, 110) if is_dark_text else QColor(255, 255, 255, 140)
                    p.setBrush(pb); p.setPen(Qt.NoPen)
                    p.drawEllipse(r.adjusted(2, 2, -2, -2))
                col = col_n
                if pressed:
                    col = QColor(255, 255, 255, 230) if is_dark_text else QColor(24, 24, 26, 230)
                draw_play_icons(p, i, r, col, playing, s=8.0)
            p.restore()

        # ---- 文字 ----
        #   第一行 = 当前歌词（播放中且有字级时间戳 → 逐字卡拉OK高亮）
        #   第二行 = 翻译（无翻译时预看下一句）；没有歌词时回退「歌名 - 歌手」
        #   两行超宽都会跑马灯滚动（对标 SPlayer：宁可滚动也不要省略号切半句）
        tx, ty, tw = self._text_rect()
        fs = max(8, int(CFG.get('tb_font', 10)))
        f_main = QFont('Microsoft YaHei UI', fs); f_main.setWeight(QFont.DemiBold)
        f_sub = QFont('Microsoft YaHei UI', max(7, int(round(fs * 0.82))))  # v1.5.0 对齐 SPlayer

        cur = nxt = None
        if connected:
            cur, nxt = self._cur_line()
        t_ms = STATE.now() * 1000.0

        # v1.5.0 悬停过渡：歌词列淡出 / 歌名+作者延迟淡入（对齐 SPlayer）
        show_song = bool(self.hover_inside and connected)
        lyric_alpha = max(0.0, 1.0 - self.hover_alpha)
        # song info 延迟 80ms 开始淡入（400ms 总过渡）
        song_alpha = max(0.0, min(1.0, (self.hover_alpha - 0.20) / 0.80))

        # ---- 分别计算「歌词」和「歌名/作者」两套文本 ----
        lyric_main = lyric_sub = ''
        song_main = song_sub = ''
        if not connected:
            lyric_main = '未连接 MoeKoe Music'
        elif cur is not None and (cur[2] or '').strip():
            lyric_main = cur[2]
            lyric_sub = Island._sub_of(cur, nxt, dual=True)
        else:
            name, singer = song_name_singer(STATE.song)
            if name and singer:
                lyric_main = name
                lyric_sub = singer
            else:
                lyric_main = name or singer or 'MoeKoe Music'
        # ⚠️⚠️【v1.7.14】暂停时**不再清掉第二行**（用户选择「暂停也保留两行」）。
        #   旧代码是 `if not playing and lyric_main and not show_song: lyric_sub = ''`
        #   —— 一按暂停就只剩一行。真机抓屏实测（2026-10-09 23:08，用户正开着播放器）：
        #   控件里只有**一行**墨迹、行心落在控件垂直中心（物理 1565 / 控件内 35.5），
        #   而两行静止时行心是 1541.8 / 1562.3 —— 正是「单行版式」的指纹。
        #   现在暂停照旧显示「当前句 + 下一句」，两行始终都在。
        #   （主行暂停时仍带 `‖ ` 前缀，见末尾静止态绘制分支 —— 那是既有的暂停指示。）

        if connected:
            name, singer = song_name_singer(STATE.song)
            song_main = name or '未知歌曲'
            song_sub = singer or ''

        # 布局仍按「当前应占主导」的文本算（悬停时按歌名/作者，否则按歌词）
        main_text, sub_text = (song_main, song_sub) if show_song else (lyric_main, lyric_sub)

        dual = bool((sub_text or '').strip())
        if dual:
            # 双行：两行**整体**在内容区垂直居中。
            #
            # 排版模型（对齐 SPlayer）：
            #   ① line_h 取主/次行**较大**的行高 —— 主行 DemiBold 比次行高，
            #      只看主行会把次行挤出下边界（实测「全挤在上半部」根因）。
            #   ② 行距 gap = 相邻两行**行心**距离，下限 line_h + 2，保证不黏连。
            #   ③ 块高 = gap + line_h；块在 [M+V_PAD, M+CH-V_PAD] 里居中。
            #      ⚠️ 之前用 cy_c = ty + CH/2 且 avail = CH-4：上边距只剩 2、
            #      下边距被 gap 吃掉 → 视觉永远「偏上」。必须用真实可用区算中心。
            # ⚠️ 关键坑：QFontMetrics.height() 在 10pt 微软雅黑下 ≈ 27px —— 它是
            #    「单行独占高度」（含 Qt 为该字号预留的行距），不是字形实际占用！
            #    拿它当行心距下限 → gap 被顶到 28、块高 55 > 可用 42，必然溢出/贴边。
            #    行心距必须用**紧致字形高** ascent+descent（≈20px）来算。
            fm_m = QFontMetrics(f_main)
            fm_s = QFontMetrics(f_sub)
            tight_m = fm_m.ascent() + fm_m.descent()
            tight_s = fm_s.ascent() + fm_s.descent()
            line_h = max(tight_m, tight_s)             # 单行紧致高（≈20px @10pt）
            v_pad = 1.0                                # 上下各留 1px 呼吸，避免贴边
            top = ty + v_pad
            bottom = ty + self.CH - v_pad
            avail = bottom - top
            gap = max(self.LINE_GAP, line_h + 1.0)     # 行距：紧致高 + 1px 呼吸即不黏
            if gap + line_h > avail:                   # 放不下 → 压缩行距（不重叠优先）
                gap = max(line_h + 0.5, avail - line_h)
            block = gap + line_h
            cy_c = (top + bottom) / 2.0                # 可用区的真实中心
            main_cy = cy_c - block / 2.0 + line_h / 2.0
            sub_cy = main_cy + gap
        else:
            # 单行：同样在 [M, M+CH] 的真实垂直中心
            main_cy, sub_cy = ty + self.CH / 2.0, None

        # 记录「有没有哪一行超宽需要滚动」→ tick 据此决定是否持续重绘。
        # ⚠️ v1.4.2 修正：**悬停看歌名/作者时同样允许滚动**。
        #    旧版写 `not show_song and ...` → 悬停时轨道直接关掉，长歌名既不滚也放不下
        #    （实测 'Airplane Mode (Radio Edit)'=285px > 悬停时文字区 260px）
        #    → 被 setClipRect 硬裁成 'Airplane Mode (Radio |'，正是用户说的
        #    「歌名/作者部分隐藏」。现在悬停时也走「滑入 → 停住」，
        #    句子一定从头显示、且最终整句可见。
        fm_main = QFontMetrics(f_main)
        fm_sub2 = QFontMetrics(f_sub)
        def _over(main, sub):
            return (fm_main.horizontalAdvance(main or '') > tw
                    or ((sub or '').strip()
                        and fm_sub2.horizontalAdvance(sub) > tw))
        self._marquee = bool(_over(lyric_main, lyric_sub) or _over(song_main, song_sub))

        # v1.6.7 歌词换句队列动画（仅歌词层；歌名/作者层独立）
        karaoke = bool(connected and playing
                       and cur is not None and cur[4] and (cur[2] or '').strip())
        # ⚠️⚠️【v1.7.12 修复「跳转时黑白闪一下」】⚠️⚠️
        #   用户反馈：任务栏放大歌词跳转时会「黑白」闪一下，希望「让蓝字自由过渡」。
        #   根因：这个 0.4s 的换句过渡**整段用 `base` 上色**（= 任务栏主题的
        #   黑/白主文字色），而静止态的逐字卡拉OK用的是 `accent`（蓝 #2F80ED）。
        #   于是换句那一帧，**整行刚刚唱完的蓝字唰地变成黑/白**，动画末尾新行又从
        #   满不透明掉回卡拉OK的「未唱」暗色 —— 一头一尾两次颜色跳变 = 「黑白闪」。
        #   修法：过渡期沿用**两端各自的真实颜色**：
        #     · 离场旧行 ← 它上一帧静止时怎么画的（卡拉OK唱满 = accent），就还怎么画；
        #     · 顶上来/新进的主行 ← 最终落到**卡拉OK的「未唱」色**（base@0.55），
        #       而不是满不透明的 base，这样 0.4s 结束时与 `_draw_karaoke_line`
        #       严丝合缝，不会有「亮一下再变暗」的跳变。
        #   为此要在换句那一刻记住「上一帧主行是不是卡拉OK」—— 用上一帧的值而不是
        #   本帧：本帧的 `cur` 已经是新句，而离场的是旧句。
        prev_karaoke = bool(getattr(self, '_karaoke_prev', False))
        self._karaoke_prev = karaoke
        lyric_sig = (lyric_main, lyric_sub)
        if lyric_sig != getattr(self, '_txt_sig', None):
            prev = getattr(self, '_txt_sig', None)
            self._txt_sig = lyric_sig
            # v1.7.14：`SWAP_ANIM=False` → **永不**建过渡（换句完全静止，见类常量注释）
            if (self.SWAP_ANIM and prev is not None and playing
                    and lyric_main and prev[0]):
                self._fade_from = prev
                self._fade_t0 = time.time()
                self._fade_prev_karaoke = prev_karaoke
            else:
                self._fade_from = None
                # 关键：`_fade_t0` 归零 → `_swap_active()` 恒 False → tick 不再为过渡重绘
                self._fade_t0 = 0.0
                self._fade_prev_karaoke = False
        fade = None
        # v1.7.14：SWAP_ANIM=False 时连读都不读，双保险
        f0 = (getattr(self, '_fade_from', None) if self.SWAP_ANIM else None)
        if f0 is not None and playing:
            fdt = time.time() - getattr(self, '_fade_t0', 0.0)
            if fdt < 0.40:
                fade = (fdt / 0.40, f0)
            else:
                self._fade_from = None

        # ---- 绘制歌词层（受 hover_alpha 调制）----
        if lyric_alpha > 0.0:
            if fade is not None:
                k, (om, osub) = fade
                # v1.7.3：SPlayer Next 风格“下行顶上行”。
                # 没有翻译时第二行就是下一句预览；当前句播完后，旧第二行应自然顶到
                # 第一行。顶上来的主行一步到位地进入清晰的轻微放大显示状态；
                # 只有旧行快速虚化离场，避免拖影。
                ease = _splayer_line_ease(k)
                lift = math.sin(k * math.pi)
                # ---------- v1.7.15：位移总闸 ----------
                # `SWAP_SLIDE=False`（默认）→ 下面三条分支里**所有竖向位移项一律归零**：
                #   · 主行/新主行 钉在最终槽位 `main_cy`，只把字号 `f_sub → f_main` 长上去；
                #   · 第二行钉在 `sub_cy` 静态绘制（与静止态同一 `_line()` 调用，逐像素一致）；
                #   · **离场旧行不再绘制** —— 它原来就是靠"向上滑出"来给新行让位的，
                #     位置一冻结就会和新行叠在同一个 `main_cy` 上糊成一团。
                # 想恢复 v1.7.9~v1.7.13 的「下行顶上来」→ `SWAP_SLIDE=True`。
                slide = bool(self.SWAP_SLIDE)
                # v1.7.12：过渡期的配色（消除「黑白闪」，见 lyric_sig 处的长注释）
                #   · 离场旧行：`old_a0` 必须等于它上一帧静止态的**不透明度**
                #     （卡拉OK唱满 = 255；普通主行也是 255），否则动画第一帧就
                #     「暗一下」。颜色取 `accent`（旧行是卡拉OK时）或 `base`。
                #   · 即将成为主行的那一行：`prom_a1` 是它落定后的**目标不透明度**：
                #     卡拉OK → 未唱色 0.55×alpha；普通 → 满 alpha。
                _was_karaoke = bool(getattr(self, '_fade_prev_karaoke', False))
                old_col_base = accent if _was_karaoke else base
                old_a0 = int(old_col_base.alpha())
                # 与 `_draw_karaoke_line` 的 unsung 完全同一公式（含 alpha=1 的极限）
                prom_a1 = (min(255, int(base.alpha() * 0.55)) if karaoke
                           else int(base.alpha()))
                # ⚠️【v1.7.9 / 关键】顶上来的主行要做「放大」，但**不能**用恒定 scale。
                #
                #   历史：v1.7.7 给它恒定 `scale=1.045`，动画结束由 `_line_fx`
                #   切回 `_line`（scale=1.0）时那一帧**突缩 4.5%** → 用户说
                #   「还要缩小一下字体才能正常播放」。v1.7.8 于是干脆把 scale
                #   归 1.0 —— 却把「放大」整个删掉了（本轮用户要求补回来）。
                #
                #   正确做法（照 SPlayer `taskbar-lyric/App.vue`）：
                #   `.lyric-line[data-role=secondary] { font-size: 0.82× }`，
                #   `.lyric-line[data-role=primary]   { font-size: 1.00× }`，
                #   而 `.line-move / .line-enter-active / .line-leave-active`
                #   过渡 `transform / opacity / font-size / color`。
                #   被提升的那一行是**同一个 key** → Vue 走 `line-move`（移动而非替换）
                #   → 它在"上移一格"的同时把 **font-size 从 0.82× 平滑长到 1.00×**
                #   （+22%），用的正是 `cubic-bezier(0.4,0,0.2,1)` / 0.4s ——
                #   与位移**同一条曲线、同一个进度**。这就是那个「放大」。
                #
                #   所以这里让顶上来的主行**字号连续地从 f_sub 长到 f_main**，
                #   并且两端**精确落在静止态的取值上**，于是既不突缩也不失放大：
                #     ease=0 → 字号 = f_sub 点数、颜色 = sub_col 的 alpha(153)
                #              （= 上一帧「次行静止」的渲染，严丝合缝）
                #     ease=1 → 字号 = f_main 点数、颜色 = base 的 alpha(255)
                #              （= 下一帧「主行静止」的渲染，严丝合缝）
                #   `color` 也要跟着渐变：SPlayer 的 `.line-move` 同样过渡 color
                #   （次行 rgba(.5) → 主行 #fff）；不插值的话换句首帧会"突然变亮"。
                #
                # ⚠️【v1.7.11 修正上面这段的最后一环】「字号连续变化」不能靠**逐帧
                #   setPointSizeF** 实现 —— 实测 Qt 的 grid-fit 会把字形量化成极少数
                #   几档（25 帧里 21 帧墨迹不变、行宽按 7px 跳），看起来仍是「卡顿」，
                #   而且每帧冷栅格化整串 CJK（p90 5.6ms）。改法见 `_draw_prom`：
                #   按主行字号**预栅格化一次**，动画期整幅缩放（s=0.8→1.0）。
                #   这里的 `prom_pt` 仍然是那个「当前插值字号」——它现在只作为
                #   缩放比例 s = prom_pt / 主行字号 交给 `_draw_prom`。
                focus_pt_sub = float(f_sub.pointSizeF())
                focus_pt_main = float(f_main.pointSizeF())
                line_gap = (sub_cy - main_cy) if sub_cy is not None else 0.0
                can_queue = bool(sub_cy is not None
                                 and (osub or '').strip()
                                 and (lyric_main or '').strip()
                                 and (osub or '').strip() == (lyric_main or '').strip())
                bilingual_bridge = bool(sub_cy is not None
                                        and (osub or '').strip()
                                        and (lyric_main or '').strip()
                                        and not can_queue)
                if can_queue:
                    if slide:
                        old_main_y = main_cy - line_gap * ease
                        promoted_y = sub_cy - line_gap * ease
                        incoming_y = sub_cy + line_gap * (1.0 - ease)
                    else:
                        # v1.7.15：冻结 —— 主行在最终槽位原地放大，第二行原地不动
                        old_main_y = main_cy
                        promoted_y = main_cy
                        incoming_y = sub_cy

                    old_col = QColor(old_col_base)
                    old_col.setAlpha(int(old_a0 * max(0.0, 1.0 - ease)))
                    next_col = QColor(sub_col); next_col.setAlpha(int(153 * max(0.0, min(1.0, ease))))

                    # 「放大」的主角：字号 f_sub → f_main、颜色 次行 → 主行（见上方长注释）
                    # v1.7.11：不再构造逐帧字号字体，只算「当前插值字号」，
                    #   真正的绘制交给 _draw_prom（预栅格化 + 整幅缩放）。
                    prom_pt = focus_pt_sub + (focus_pt_main - focus_pt_sub) * ease
                    # v1.7.12：终点从 `base.alpha()` 改成 `prom_a1`
                    #   —— 卡拉OK歌落定后是「未唱暗色」(0.55×alpha)，不是满不透明。
                    #   不这么改的话，0.4s 结束那一帧会「亮着突然变暗」（黑白闪的后半段）。
                    main_col = QColor(base)
                    main_col.setAlpha(int(round(sub_col.alpha()
                                                + (prom_a1 - sub_col.alpha()) * ease)))

                    # ⚠️【v1.7.10 修复「放大效果卡顿」】这三行**一律不再传 scale**。
                    #   实测（exp_fix.py，同一段歌词重复测）：只要 `_line_fx` 里
                    #   走了 `p.scale()`，单帧绘制耗时 p90 从 **0.48ms 飙到 7.22ms**
                    #   （max 10.19ms；整段合计 17.2ms → 87.2ms，5 倍）。
                    #   原因：Qt 一旦遇到非恒等变换就放弃**hinted 字形缓存**，
                    #   对整串 CJK 逐字做变换栅格化；而换句放大期间每帧都要重画
                    #   2~3 行，16ms 预算直接被吃穿 → 掉帧 = 肉眼「卡顿」。
                    #   代价还完全不值：旧行的放大只有 **2.5%**（1.045 的十分之一
                    #   量级），肉眼不可辨。
                    #   顺带这也是**更贴 SPlayer** 的做法：`.line-leave` 只过渡
                    #   `transform`(translateY) / `opacity` / `font-size` / `color`，
                    #   离场行并不做 scale 放大（那是本项目早期自己加的）。
                    #   虚化（blur）保留 —— 实测它几乎不花钱（noblur 17.1ms vs
                    #   noscale 17.2ms），而「旧行虚化离场」是既定的观感。
                    # v1.7.15：`slide=False` 时不画离场旧行（见 `slide` 处注释）。
                    if slide:
                        self._line_fx(p, om, tx, old_main_y, tw, f_main, old_col,
                                      scale=1.0, blur=0.55 * lift,
                                      playing=playing, alpha=lyric_alpha)
                    # v1.7.11：顶上来的主行改走「预栅格化 + 整幅缩放」。
                    #   alpha 传**总**透明度：颜色 153→255 的渐变 × 悬停淡出。
                    self._draw_prom(p, lyric_main, tx, promoted_y, tw, f_main, prom_pt,
                                    main_col, (main_col.alpha() / 255.0) * lyric_alpha)
                    if (lyric_sub or '').strip():
                        if slide:
                            self._line_fx(p, lyric_sub, tx, incoming_y, tw, f_sub, next_col,
                                          scale=1.0, blur=0.0,
                                          playing=playing, alpha=lyric_alpha)
                        else:
                            # v1.7.15：第二行原地、静态绘制 —— 与末尾静止态分支
                            #   **同一调用**（同 `sub_cy` / `f_sub` / `sub_col`），逐像素一致。
                            self._line(p, lyric_sub, tx, sub_cy, tw, f_sub, sub_col,
                                       playing=playing, alpha=lyric_alpha)
                elif bilingual_bridge:
                    if slide:
                        old_main_y = main_cy - line_gap * ease
                        old_sub_y = sub_cy - line_gap * ease
                        new_main_y = sub_cy - line_gap * ease
                        new_sub_y = sub_cy + line_gap * (1.0 - ease)
                    else:
                        # v1.7.15：冻结（同 can_queue 分支的注释）
                        old_main_y = main_cy
                        old_sub_y = sub_cy
                        new_main_y = main_cy
                        new_sub_y = sub_cy

                    old_col = QColor(old_col_base)
                    old_col.setAlpha(int(old_a0 * max(0.0, 1.0 - ease)))
                    old_sub_col = QColor(sub_col)
                    old_sub_col.setAlpha(int(125 * max(0.0, 1.0 - ease)))
                    new_sub_col = QColor(sub_col)
                    new_sub_col.setAlpha(int(153 * max(0.0, min(1.0, ease))))

                    # ⚠️【v1.7.9】第二行是**翻译**时（与队列分支的"下一句预览"不同），
                    #   SPlayer 那边新主行是"全新 key"→ 走 enter（以 primary 字号直接进入），
                    #   并没有 font-size 放大。但这里新主行同样是**从次行槽位升上来**的
                    #   （`new_main_y` 由 sub_cy 插值到 main_cy），若不做放大，
                    #   有翻译的歌曲就完全看不到这个效果。故两分支统一放大，
                    #   保证"不看有没有翻译都能看到同一手感"。
                    # v1.7.11：同上，改交 _draw_prom（预栅格化 + 整幅缩放）
                    prom_pt = focus_pt_sub + (focus_pt_main - focus_pt_sub) * ease
                    # v1.7.12：终点同 can_queue 分支（卡拉OK → 未唱暗色）
                    new_main_col = QColor(base)
                    new_main_col.setAlpha(int(round(prom_a1 * max(0.0, min(1.0, ease)))))

                    # scale 一律归 1.0：同 can_queue 分支的 v1.7.10 修复
                    # （`p.scale()` 会让 Qt 放弃 hinted 字形缓存 → 单帧 7~10ms）
                    # v1.7.15：`slide=False` 时旧行（主行 + 旧译文行）都不画。
                    if slide:
                        self._line_fx(p, om, tx, old_main_y, tw, f_main, old_col,
                                      scale=1.0, blur=0.6 * lift,
                                      playing=playing, alpha=lyric_alpha)
                        self._line_fx(p, osub, tx, old_sub_y, tw, f_sub, old_sub_col,
                                      scale=1.0, blur=0.45 * lift,
                                      playing=playing, alpha=lyric_alpha)
                    # v1.7.11：同上
                    self._draw_prom(p, lyric_main, tx, new_main_y, tw, f_main, prom_pt,
                                    new_main_col,
                                    (new_main_col.alpha() / 255.0) * lyric_alpha)
                    if (lyric_sub or '').strip():
                        if slide:
                            self._line_fx(p, lyric_sub, tx, new_sub_y, tw, f_sub, new_sub_col,
                                          scale=1.0, blur=0.0,
                                          playing=playing, alpha=lyric_alpha)
                        else:
                            # v1.7.15：第二行原地、静态绘制（同 can_queue 分支）
                            self._line(p, lyric_sub, tx, sub_cy, tw, f_sub, sub_col,
                                       playing=playing, alpha=lyric_alpha)
                else:
                    # 单行或无法形成队列时，也保持竖向换行，避免任何原地闪烁。
                    # ⚠️⚠️【v1.7.12 关键】这条**才是本机最常见的一条**：compact 版式
                    #   + 当前句没有译文 → 没有第二行槽位 → 上面两个「双行」分支都进不去，
                    #   换句必然落到这里。旧代码 `_ca = base@210` 会把上一帧还**整行蓝**
                    #   的唱满句在换句第一帧刷成黑/白 —— 用户看到的「黑白闪一下」就是它。
                    #   现在：旧行沿用 `old_col_base`（卡拉OK歌 = accent 蓝）与
                    #   `old_a0`（= 它上一帧的不透明度），新行淡入到 `prom_a1`
                    #   （卡拉OK = 未唱的 base@0.55）→ 两端都与静止态严丝合缝。
                    fallback_gap = max(18.0, QFontMetrics(f_main).height() * 0.95)
                    if slide:
                        old_y = main_cy - fallback_gap * ease
                        new_y = main_cy + fallback_gap * (1.0 - ease)
                    else:
                        # v1.7.15：冻结 —— 新主行就在 `main_cy` 淡入（无位移、无放大，
                        #   本分支历史上也没有"可提升的次行"，故不引入字号过渡）
                        old_y = main_cy
                        new_y = main_cy
                    _ca = QColor(old_col_base); _ca.setAlpha(int(old_a0 * (1.0 - ease)))
                    _na = QColor(base); _na.setAlpha(int(round(prom_a1 * ease)))
                    if slide:
                        self._line(p, om, tx, old_y, tw, f_main, _ca,
                                   playing=playing, alpha=lyric_alpha)
                    self._line(p, lyric_main, tx, new_y, tw, f_main, _na,
                               playing=playing, alpha=lyric_alpha)
                    if sub_cy is not None:
                        if slide:
                            old_sub_y = sub_cy - fallback_gap * ease
                            new_sub_y = sub_cy + fallback_gap * (1.0 - ease)
                            _sa = QColor(sub_col); _sa.setAlpha(int(135 * (1.0 - ease)))
                            _nsa = QColor(sub_col); _nsa.setAlpha(int(153 * ease))
                            if (osub or '').strip():
                                self._line(p, osub, tx, old_sub_y, tw, f_sub, _sa,
                                           playing=playing, alpha=lyric_alpha)
                            if (lyric_sub or '').strip():
                                self._line(p, lyric_sub, tx, new_sub_y, tw, f_sub, _nsa,
                                           playing=playing, alpha=lyric_alpha)
                        elif (lyric_sub or '').strip():
                            # v1.7.15：冻结时第二行静态绘制（与静止态同一调用）
                            self._line(p, lyric_sub, tx, sub_cy, tw, f_sub, sub_col,
                                       playing=playing, alpha=lyric_alpha)
            elif karaoke:
                self._draw_karaoke_line(p, cur, t_ms, tx, main_cy, tw, f_main, accent, base, alpha=lyric_alpha)
            else:
                self._line(p, ('‖ ' + lyric_main) if (not playing and lyric_main) else lyric_main,
                           tx, main_cy, tw, f_main, base, playing=playing, alpha=lyric_alpha)
            if sub_cy is not None and fade is None:
                self._line(p, lyric_sub, tx, sub_cy, tw, f_sub, sub_col, playing=playing, alpha=lyric_alpha)

        # ---- 绘制歌名/作者层（悬停时延迟淡入）----
        if song_alpha > 0.0 and (song_main or song_sub):
            self._line(p, song_main, tx, main_cy, tw, f_main, base, playing=playing, alpha=song_alpha)
            if sub_cy is not None and song_sub:
                self._line(p, song_sub, tx, sub_cy, tw, f_sub, sub_col, playing=playing, alpha=song_alpha)

        p.end()

    def _draw_karaoke_line(self, p, line, t_ms, x, cy, w, font, accent, base, speed=42.0, alpha=1.0):
        """任务栏版卡拉OK：逐字高亮（v1.7.13 起**不再横向滚动**）。

        ⚠️ **两条时间轴必须解耦**（这是「滚动形式比较差」的核心）：
          · 高亮相位 = `t_ms`（播放进度）→ 决定「唱到哪个字」，暂停时冻结。
          · ~~滚动相位~~ = v1.7.13 起**已移除**：文本位置恒定在 `x`，
            超宽时逐字截断 + 右端 `…`（见 `NO_SCROLL`）。
        早期把两者都绑在 `t_ms` 上：一换句 t_ms 跳到新句起点 → 滚动位置突变，
        看起来就是「一顿一顿地弹」。"""
        start, end, body, trans, chars = line
        if alpha <= 0.0:
            return
        unsung = QColor(base)
        unsung.setAlpha(min(255, int(base.alpha() * 0.55 * alpha)))
        accent_a = QColor(accent)
        accent_a.setAlpha(min(255, int(accent.alpha() * alpha)))
        p.setFont(font)
        fm = QFontMetrics(font)
        # 与 _line() 保持同一基线修正（-1.5），否则卡拉OK行会比翻译行整体低约 1.5px，
        # 双行时叠在一起就是用户看到的「黏在一起」。
        # v1.7.10：y 吸附整数（同 _line，见那里的注释）
        y = _px(cy + fm.ascent() / 2.0 - 1.5)
        body_w = fm.horizontalAdvance(body)
        p.save()
        p.setClipRect(QRectF(x, cy - fm.height(), max(1.0, w), fm.height() * 2))
        # v1.7.10：起始 x 吸附整数 → 逐字 advance 本身是整数，起点整则整行都整。
        x0 = _px(float(x))
        tail = ''
        if body_w > w:
            if self.NO_SCROLL:
                # ⚠️⚠️【v1.7.13】不滚动：逐字累加、选出「加上省略号仍放得下」的前缀，
                #   尾部补一个 `…`。「高亮相位」（t_ms）依旧逐字正常，只是不再有横向位移。
                ell_w = fm.horizontalAdvance('…')
                limit = max(0.0, float(w) - ell_w)
                used = 0.0
                shown = []
                for cs, ce, ch in chars:
                    cw = fm.horizontalAdvance(ch)
                    if used + cw > limit:
                        break
                    shown.append((cs, ce, ch))
                    used += cw
                chars = shown
                tail = '…'
            else:
                # v1.4.7 旧行为：slide-in then hold（按演唱进度左移，只画一份）
                x0 = _px(float(x) - self._marq_off(body_w, w))
        cx = x0
        for cs, ce, ch in chars:
            cw = fm.horizontalAdvance(ch)
            if t_ms >= ce: frac = 1.0
            elif t_ms <= cs: frac = 0.0
            else: frac = (t_ms - cs) / max(1.0, (ce - cs))
            if frac > 0:
                col = QColor(
                    int(unsung.red() + (accent_a.red() - unsung.red()) * frac),
                    int(unsung.green() + (accent_a.green() - unsung.green()) * frac),
                    int(unsung.blue() + (accent_a.blue() - unsung.blue()) * frac),
                    int(unsung.alpha() + (accent_a.alpha() - unsung.alpha()) * frac))
            else:
                col = unsung
            p.setPen(col)
            p.drawText(QPointF(cx, y), ch)
            cx += cw
        if tail:
            # 省略号用「未唱色」：中性、不抢逐字高亮，也不误导为已唱
            p.setPen(unsung)
            p.drawText(QPointF(cx, y), tail)
        p.restore()

    def maybe_refresh(self):
        """内容（歌词/翻译/播放态/悬停态）变化时才重绘——卡拉OK另由 tick 强制重绘。
        key 里带 hover_inside：鼠标进出感应区要在「歌名/作者 ↔ 歌词」间切换。"""
        try:
            hover = bool(self.hover_inside)
            if not STATE.connected:
                key = ('__disconnected__', hover)
            else:
                cur, nxt = self._cur_line()
                with STATE.lock:
                    playing = STATE.is_playing
                    gen = STATE.song_gen
                if cur is not None:
                    key = (gen, playing, cur[2], Island._sub_of(cur, nxt, dual=True),
                           self._span() > 0.5, hover)
                else:
                    key = (gen, playing, None, None, self._span() > 0.5, hover)
            if key != getattr(self, '_last_key', None):
                self._last_key = key
                self.update()
        except Exception as e:
            log('tb refresh fail: %r' % e)

    # ---------- v1.7.13：超宽行 → 右端省略号（**替代滚动**） ----------
    def _elide_text(self, fm, text, w):
        """把 `text` 裁到宽度 `w` 内、右端补 `…`。返回 `(绘制文本, 是否被省略)`。

        ⚠️ v1.7.13 起任务栏**不滚动**（`NO_SCROLL`，用户要求「直接显示两行歌词」），
        超宽行一律走这里。`w` 传**该行实际可用的像素宽**：
          · 静止态 = 文字区宽（`_text_rect()` 的第三项）；
          · `_line_fx` 在**局部坐标**下绘制 → 传 `w / scale`（见那里的注释）。
        放得下就原样返回，不动。"""
        if not text:
            return text, False
        if fm.horizontalAdvance(text) <= w:
            return text, False
        return fm.elidedText(text, Qt.ElideRight, max(1, int(w))), True

    def _line(self, p, text, x, cy, w, font, color, speed=38.0, playing=True, alpha=1.0):
        """一行文本，垂直居中于 cy。
        放得下 → 直接画；放不下 → **右端省略号**（v1.7.13 起不再滚动）。

        ⚠️ v1.4.9 曾按 `_marq_off` 做「歌词演唱进度驱动的滑入」；
        v1.7.13 用户要求「不要搞滚动」，故改为 `elidedText(…, ElideRight, w)`：
        文本位置**恒定在 x**，超宽部分以 `…` 收尾。`_marq_off` 仍保留（供旧测试
        与 `_marq_advance` 引用），但绘制路径已不再调用它。"""
        if not text:
            return
        if alpha <= 0.0:
            return
        p.setFont(font)
        fm = QFontMetrics(font)
        tw = fm.horizontalAdvance(text)
        # ⚠️ v1.7.10：基线 y 吸附整数。换句放大时主行的 cy 是**连续插值**的
        #   （48.00 → 47.72 → 46.84 → …），小数相位每帧都变 → Qt 走子像素定位、
        #   每帧重新栅格化整串 CJK 字形（既吃帧预算又发虚）。
        #   取整后 cy 等价于「在像素网格上动画」，字形命中同一份缓存位图。
        y = _px(cy + fm.ascent() / 2.0 - 1.5)
        col = QColor(color)
        if alpha < 1.0:
            col.setAlpha(int(col.alpha() * alpha))
        if tw <= w:
            p.setPen(col)
            p.drawText(QPointF(x, y), text)
            return
        if self.NO_SCROLL:
            # ⚠️⚠️【v1.7.13】不滚动 → 右端省略号（详见 `NO_SCROLL` 的长注释）。
            #   位置恒定在 x（不再按演唱进度左移）；裁到 w 后必然放得下。
            disp, off = self._elide_text(fm, text, w)[0], 0.0
        else:
            # v1.4.9 旧行为：按该句演唱进度左移（用户已不要，仅留 NO_SCROLL=False 时可用）
            disp, off = text, self._marq_off(tw, w)
        p.save()
        p.setClipRect(QRectF(x, cy - fm.height(), max(1.0, w), fm.height() * 2))
        p.setPen(col)
        p.drawText(QPointF(_px(x - off), y), disp)
        p.restore()

    def _line_fx(self, p, text, x, cy, w, font, color, scale=1.0, blur=0.0,
                 speed=38.0, playing=True, alpha=1.0):
        """换句专用文本：支持轻微放大和虚化。

        不用 QGraphicsEffect，直接用几次低透明偏移绘制模拟短暂虚化；
        这样在任务栏贴边窗口里更稳定，也不会拖慢普通歌词绘制。"""
        if not text or alpha <= 0.0:
            return
        scale = max(0.92, min(1.18, float(scale or 1.0)))
        blur = max(0.0, float(blur or 0.0))
        p.save()
        p.translate(QPointF(x, cy))
        p.scale(scale, scale)
        lx = 0.0
        ly = 0.0
        lw = max(1.0, w / scale)
        if blur <= 0.05 and abs(scale - 1.0) < 0.01:
            p.restore()
            self._line(p, text, x, cy, w, font, color, speed=speed,
                       playing=playing, alpha=alpha)
            return

        p.setFont(font)
        fm = QFontMetrics(font)
        tw = fm.horizontalAdvance(text)
        if self.NO_SCROLL:
            # ⚠️⚠️【v1.7.13】不滚动：这里是 `p.translate(x, cy)` + `p.scale(scale)` 之后的
            #   **局部坐标**，所以按 `lw`（= w / scale）省略 —— 局部宽 lw 经 scale 放大
            #   后在设备坐标下正好 = w，省略结果必然 ≤ w。
            disp, off = self._elide_text(fm, text, lw)[0], 0.0
        else:
            disp = text
            off = self._marq_off(tw, lw) if tw > lw else 0.0
        p.setClipRect(QRectF(lx, ly - fm.height(), lw, fm.height() * 2.2))

        # ⚠️⚠️【v1.7.10 关键】这里画的是 `translate(x, cy)` 之后的**局部坐标**，
        #   所以必须对**设备坐标**（局部 × scale + 平移量）取整，再折回局部 ——
        #   只把局部坐标取整是没有意义的（cy 仍是小数）。
        #   不做这一步的后果（实测）：换句放大期间 cy 连续插值
        #   （48.00 → 47.72 → 46.84 → …），小数相位每帧都不同 → Qt 走子像素
        #   定位、**每帧重新栅格化整串 CJK 字形**；而且 `p.scale()` 一出现，
        #   Qt 直接放弃 hinted 字形缓存 → 单帧绘制 7~10ms（16ms 预算被吃穿）。
        s = scale if abs(scale) > 1e-6 else 1.0
        g_x = lx - off
        g_y = ly + fm.ascent() / 2.0 - 1.5
        bo_x = (_px(x + s * g_x) - x) / s
        bo_y = (_px(cy + s * g_y) - cy) / s

        base_col = QColor(color)
        if alpha < 1.0:
            base_col.setAlpha(int(base_col.alpha() * alpha))
        if blur > 0.05:
            soft = QColor(base_col)
            soft.setAlpha(int(base_col.alpha() * min(0.36, 0.18 + blur * 0.10)))
            r = min(1.7, blur)
            for dx, dy in ((-r, 0), (r, 0), (0, -r), (0, r)):
                p.setPen(soft)
                p.drawText(QPointF(bo_x + dx, bo_y + dy), disp)
        crisp = QColor(base_col)
        if blur > 0.05:
            crisp.setAlpha(int(base_col.alpha() * max(0.45, 1.0 - blur * 0.24)))
        p.setPen(crisp)
        p.drawText(QPointF(bo_x, bo_y), disp)
        p.restore()

    # ---------- 换句「放大」：预栅格化 + 整幅缩放（v1.7.11） ----------
    #
    # ⚠️⚠️ 为什么不再逐帧 `setPointSizeF`（v1.7.9/v1.7.10 的写法）⚠️⚠️
    #   实测（probe_grow.py，真实动画字号序列 8.0→10.0 / 26 帧）：
    #   · Qt 的 grid-fit hinting 会把同一串文字的字形**量化成极少数几档**：
    #       行宽按 7px 整数台阶跳（119→126→133→140→147，= 7 个字 × 每字 1px），
    #       墨迹在 25 帧里**有 21 帧完全不变** —— 放大过程实际是「几下猛跳 + 后面静止」。
    #       这就是肉眼看出来的「卡顿 / 不够流畅」（而**不是**掉帧：帧投递实测满 16ms）。
    #   · 而且每帧都是新字号 ⇒ 每帧**冷栅格化**整串 CJK：单帧 p90 5.60ms，
    #       叠上分层透明窗的合成开销后就顶到 16.6ms 预算。
    #   ⚠️ 试过「关掉 hinting」（`QFont.PreferNoHinting`）——**无效**：本机 Qt 的
    #       字体引擎不理会它，量化依旧（实测零变化帧数同为 21，行宽仍按 7px 跳）。
    #
    # ✅ 改法：照 SPlayer `taskbar-lyric/App.vue` 的 `.line-move` 语义
    #   （那一行的 `font-size` 是**连续过渡**的，浏览器靠连续轮廓缩放实现）——
    #   把主行按**主行字号**栅格化成一张小位图（每次换句只做一次），
    #   动画期按 `s = 当前字号 / 主行字号`（0.8 → 1.0）整幅缩放贴图。
    #   实测结果（probe_raster.py）：
    #     · 逐帧连续：零变化帧数 21 → **0**；Δ墨迹变异系数 2.43 → 0.79；
    #       内容宽 177→220 走 **1px 台阶**（不再 7px 一跳）
    #     · 单帧耗时 p90 **5.60ms → 0.28ms**
    #     · s=1.0 时是 1:1 贴图 ⇒ 与静止态 `_line()` 渲染**逐设备像素相同**
    #       （实测 9 个不同 cy：20.0 / 20.2 / 20.4 / 20.5 / 20.8 / 21.0 / 30.0 /
    #        47.9 / 48.0 全部 0 差异）⇒ 动画结尾**不会**「突然变清晰 / 抽一下」。
    #
    # 坐标锚点（三个点都取整到设备像素网格，见 `_px`）：
    #   · 位图内：笔原点在设备 (pen_x, base_y)，内容中心在 base_y − (asc−desc)/2·dpr
    #   · 静止态：笔原点在设备 (_px(x), _px(cy + ascent/2 − 1.5))  —— 同 `_line()`
    #   · 贴图：左缘 = 笔原点 − pen_x·s（水平锚左 ＝ `transform-origin` 的 left）
    #           上缘 = 目标内容中心 − 框内内容中心偏移·s（垂直锚中心 ＝ center）
    def _prom_raster(self, text, font, color, dpr):
        """按 `font`（＝主行字号）把 `text` 栅格化成一张小位图。

        位图用 base 色 + alpha 255 画，透明度由动画期 `setOpacity` 统一调制
        （等价于 `_line()` 的 `color.setAlpha(...)`）。
        缓存键 = (文本, 字号, 字重, 颜色, DPR)：换句时重建一次（~0.3ms），
        窗口里后续 25 帧全部命中缓存。
        """
        if not text:
            return None
        try:
            dpr = float(dpr or 1.0)
        except Exception:
            dpr = 1.0
        dpr = max(1.0, dpr)
        key = (text, font.pointSizeF(), int(font.weight()), color.rgb(),
               round(dpr, 3))
        if getattr(self, '_prom_key', None) == key:
            return getattr(self, '_prom_data', None)
        fm = QFontMetricsF(font)
        adv, asc, desc = (fm.horizontalAdvance(text), fm.ascent(), fm.descent())
        if adv <= 0.5:
            return None
        pad = 3.0
        wdev = int(math.ceil((adv + pad * 2) * dpr)) + 1
        hdev = int(math.ceil((asc + desc + pad * 2) * dpr)) + 1
        pm = QPixmap(max(2, wdev), max(2, hdev))
        pm.setDevicePixelRatio(dpr)
        pm.fill(Qt.transparent)
        pp = QPainter(pm)
        pp.setRenderHint(QPainter.Antialiasing, True)
        pp.setFont(font)
        pp.setPen(QColor(color.red(), color.green(), color.blue(), 255))
        pen_x = int(round(pad * dpr))                  # 笔原点 x（设备像素）
        base_y = int(round((pad + asc) * dpr))         # 基线 y（设备像素）
        pp.drawText(QPointF(pen_x / dpr, base_y / dpr), text)
        pp.end()
        data = dict(pm=pm, pen_x=float(pen_x), base_y=float(base_y),
                    adv=float(adv), asc=float(asc), desc=float(desc),
                    # 内容中心在框内的设备 y（用 metrics 紧致高算，不扫位图）
                    cx=base_y - (asc - desc) / 2.0 * dpr,
                    w=float(wdev) / dpr, h=float(hdev) / dpr, dpr=dpr)
        self._prom_key = key
        self._prom_data = data
        return data

    def _draw_prom(self, p, text, x, cy, w, font, pt, color, alpha):
        """把预栅格化的主行按 `s = pt / 主行字号` 缩放贴到 (x, cy)。

        换句放大动画专用。`pt` 是当前插值字号，`alpha` 是**总**透明度
        （颜色 alpha 渐变 × 悬停淡出），取值 0~1。
        """
        if not text or alpha <= 0.0:
            return
        # 设备像素比必须与绘制上下文一致，否则位图会被放大/缩小贴出去。
        # 本机实测 devicePixelRatio() = 1.0（Qt 未启用高 DPI 缩放，逻辑像素 = 物理像素），
        # 但仍然照实读它 —— 换台开了缩放的机器就自动正确。
        try:
            dpr = float(self.devicePixelRatioF() or 1.0)
        except Exception:
            dpr = 1.0
        # ⚠️⚠️【v1.7.13】不滚动：**先在主行字号下把文本省略到 w** 再栅格化。
        #   于是贴图宽 = 省略宽 × s ≤ w（s ≤ 1），动画全程无需裁切/位移；
        #   且 s=1.0 那一帧与静止态 `_line()` 的省略结果**逐像素一致**（不会结尾抽一下）。
        if self.NO_SCROLL:
            _fm_full = QFontMetrics(font)
            if _fm_full.horizontalAdvance(text) > w:
                _elided, _cut = self._elide_text(_fm_full, text, w)
                if _cut:
                    text = _elided
        d = self._prom_raster(text, font, color, max(1.0, dpr))
        if not d:
            # 兜底：位图不可用时退回原生绘制（行为与 v1.7.10 一致）
            self._line(p, text, x, cy, w, font, color, playing=True, alpha=alpha)
            return
        dpr = d['dpr']
        s = max(0.05, min(1.0, float(pt) / max(1.0, font.pointSizeF())))
        fm = QFontMetricsF(font)
        # 静止态笔原点基线（设备像素）—— 与 `_line()` 完全同一公式
        base_t = _px(float(cy) + fm.ascent() / 2.0 - 1.5) * dpr
        center_t = d['cx'] + (base_t - d['base_y'])      # 目标内容中心（设备像素）
        left = round(_px(float(x)) * dpr - d['pen_x'] * s)
        top = round(center_t - d['cx'] * s)
        dw, dh, tw = d['w'] * s, d['h'] * s, d['adv'] * s
        p.save()
        if tw > w:
            # 兜底（省略后理论不会走到）：只裁切；NO_SCROLL=False 时退回旧滚动
            p.setClipRect(QRectF(x, cy - fm.height(), max(1.0, w), fm.height() * 2))
            if not self.NO_SCROLL:
                left = round(left - self._marq_off(tw, w) * dpr)
        p.setRenderHint(QPainter.SmoothPixmapTransform, True)
        p.setOpacity(max(0.0, min(1.0, alpha)))
        p.drawPixmap(QRectF(left / dpr, top / dpr, dw, dh),
                     d['pm'], QRectF(0, 0, d['pm'].width(), d['pm'].height()))
        p.restore()

# ================================================================
# 系统托盘（后台设置入口）
# ================================================================
def make_tray_icon():
    """托盘/窗口图标：深色圆角块 + 律动条（颜色跟着高亮色走）"""
    pm = QPixmap(64, 64)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    path = QPainterPath()
    path.addRoundedRect(QRectF(3, 3, 58, 58), 18, 18)
    g = QLinearGradient(0, 0, 0, 64)
    g.setColorAt(0.0, QColor('#2c3140'))
    g.setColorAt(1.0, QColor('#0c0e13'))
    p.fillPath(path, QBrush(g))
    accent = qcol(CFG.get('island_accent'), fallback='#4CC2FF')
    p.setPen(Qt.NoPen)
    for i, (x, h) in enumerate(((17, 18), (27, 30), (37, 22), (47, 34))):
        c = QColor(accent)
        c.setAlpha(140 + i * 35)
        p.setBrush(c)
        p.drawRoundedRect(QRectF(x, 32 - h / 2.0, 5, h), 2.5, 2.5)
    p.end()
    return QIcon(pm)

class Tray:
    """托盘图标 + 菜单：显示开关 / 翻译 / 吸附 / 外观设置 / 自启 / 退出"""

    def __init__(self, island, strip):
        self.island = island
        self.strip = strip
        self.icon = QSystemTrayIcon(make_tray_icon())
        self.icon.setToolTip('MoeKoeIsland · 灵动岛 / 任务栏歌词')
        m = QMenu()

        self.a_island = QAction('显示灵动岛', m, checkable=True,
                                triggered=lambda c: set_flag('show_island', bool(c)))
        self.a_tb = QAction('显示任务栏歌词', m, checkable=True,
                            triggered=lambda c: set_flag('show_taskbar', bool(c)))
        self.a_trans = QAction('显示歌词翻译', m, checkable=True,
                               triggered=lambda c: set_flag('show_translation', bool(c)))
        for a in (self.a_island, self.a_tb, self.a_trans):
            m.addAction(a)
        m.addSeparator()

        self.a_snap = QAction('自动吸附顶部中央', m, checkable=True,
                              triggered=lambda c: set_flag('snap_top', bool(c)))
        a_center = QAction('灵动岛回到顶部居中', m,
                           triggered=lambda: PENDING_CMDS.append('center_island'))
        m.addAction(self.a_snap)
        m.addAction(a_center)
        m.addSeparator()

        a_set = QAction('外观与设置…', m, triggered=lambda: PENDING_CMDS.append('open_settings'))
        a_dir = QAction('打开配置目录', m, triggered=self._open_dir)
        self.a_auto = QAction('开机自启动', m, checkable=True, triggered=self._set_autostart)
        m.addAction(a_set)
        m.addAction(a_dir)
        m.addAction(self.a_auto)
        m.addSeparator()

        m.addAction(QAction('退出 MoeKoeIsland', m,
                            triggered=lambda *_: request_quit('tray-menu')))
        self.menu = m
        self.icon.setContextMenu(m)
        self.icon.activated.connect(self._on_activated)
        self.icon.show()
        self.sync()

    def _open_dir(self):
        try:
            os.makedirs(APP_DIR, exist_ok=True)
            os.startfile(APP_DIR)
        except Exception as e:
            log('open dir fail: %r' % e)

    def _set_autostart(self, checked):
        set_flag('autostart', bool(checked))
        set_autostart(checked)

    def _on_activated(self, reason):
        if reason == QSystemTrayIcon.DoubleClick:
            PENDING_CMDS.append('open_settings')

    def sync(self):
        try:
            self.a_island.setChecked(bool(CFG.get('show_island', True)))
            self.a_tb.setChecked(bool(CFG.get('show_taskbar', True)))
            self.a_trans.setChecked(bool(CFG.get('show_translation', True)))
            self.a_snap.setChecked(bool(CFG.get('snap_top', True)))
            self.a_auto.setChecked(bool(CFG.get('autostart')))
            self.icon.setIcon(make_tray_icon())
            if self.island is not None:
                self.island.sync_menu()
        except Exception as e:
            log('tray sync fail: %r' % e)

    def notify(self, title, text):
        try:
            self.icon.showMessage(title, text, QSystemTrayIcon.Information, 4000)
        except Exception:
            pass

# ================================================================
# 设置面板
# ================================================================
class SettingsDialog(QDialog):
    """图形化设置：显示开关 + 灵动岛外观 + 任务栏外观 + 歌词翻译"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle('MoeKoeIsland 外观与设置')
        self.setWindowFlags(Qt.Window | Qt.WindowStaysOnTopHint)
        self.setMinimumWidth(520)
        self._colors = {}
        root = QVBoxLayout(self)
        root.setContentsMargins(16, 14, 16, 12)
        root.setSpacing(10)

        # ---- 显示组件 ----
        g1 = QGroupBox('显示组件（可以只留一个，也可以两个都要）')
        f1 = QVBoxLayout(g1)
        self.cb_island = QCheckBox('灵动岛')
        self.cb_tb = QCheckBox('任务栏歌词组件')
        self.cb_trans = QCheckBox('显示歌词翻译（两个组件都生效；无翻译时第二行预看下一句）')
        row = QHBoxLayout()
        row.addWidget(self.cb_island); row.addWidget(self.cb_tb); row.addStretch(1)
        f1.addLayout(row)
        f1.addWidget(self.cb_trans)
        root.addWidget(g1)

        # ---- 灵动岛外观 ----
        g2 = QGroupBox('灵动岛外观')
        f2 = QGridLayout(g2)
        f2.setHorizontalSpacing(10); f2.setVerticalSpacing(6)
        self.cmb_layout = QComboBox()
        self.cmb_layout.addItem('紧凑单行（有翻译时自动展开）', 'compact')
        self.cmb_layout.addItem('双行（歌词 + 翻译/预看下一句）', 'dual')
        self.sp_radius = QSpinBox(); self.sp_radius.setRange(6, 40)
        self.sp_ifont = QSpinBox(); self.sp_ifont.setRange(8, 22)
        self.sp_alpha = QSpinBox(); self.sp_alpha.setRange(60, 255)
        self.sp_alpha.setSuffix(' / 255')
        f2.addWidget(QLabel('版式'), 0, 0); f2.addWidget(self.cmb_layout, 0, 1, 1, 3)
        f2.addWidget(QLabel('圆角'), 1, 0); f2.addWidget(self.sp_radius, 1, 1)
        f2.addWidget(QLabel('字号'), 1, 2); f2.addWidget(self.sp_ifont, 1, 3)
        f2.addWidget(QLabel('不透明度'), 2, 0); f2.addWidget(self.sp_alpha, 2, 1)
        self._add_color(f2, 3, '胶囊底色', 'island_bg')
        self._add_color(f2, 4, '渐变底色', 'island_bg2')
        self._add_color(f2, 5, '歌词文字', 'island_text')
        self._add_color(f2, 6, '翻译文字', 'island_sub')
        self._add_color(f2, 7, '卡拉OK高亮', 'island_accent')
        root.addWidget(g2)

        # ---- 任务栏组件外观 ----
        g3 = QGroupBox('任务栏组件外观')
        f3 = QGridLayout(g3)
        f3.setHorizontalSpacing(10); f3.setVerticalSpacing(6)
        self.cmb_theme = QComboBox()
        for t, label in (('auto', '自动跟随任务栏明暗'),
                         ('light', '始终浅色文字（深色任务栏）'),
                         ('dark', '始终深色文字（浅色任务栏）'),
                         ('custom', '自定义颜色')):
            self.cmb_theme.addItem(label, t)
        f3.addWidget(QLabel('文字主题'), 0, 0); f3.addWidget(self.cmb_theme, 0, 1, 1, 3)
        self.sp_tfont = QSpinBox(); self.sp_tfont.setRange(8, 18)
        f3.addWidget(QLabel('字号'), 1, 0); f3.addWidget(self.sp_tfont, 1, 1)
        self._add_color(f3, 2, '自定义文字色', 'tb_text')
        self._add_color(f3, 3, '卡拉OK高亮', 'tb_accent')
        self.cb_cover = QCheckBox('显示封面')
        self.cb_btns = QCheckBox('显示 ⏮ ⏯ ⏭ 三个按钮')
        self.cb_autohide = QCheckBox('三键自动回收/展开（鼠标移到组件上才展开，腾出空间给歌词）')
        f3.addWidget(self.cb_cover, 4, 0, 1, 2)
        f3.addWidget(self.cb_btns, 4, 2, 1, 2)
        f3.addWidget(self.cb_autohide, 5, 0, 1, 4)
        root.addWidget(g3)

        # ---- 按钮 ----
        btns = QHBoxLayout()
        self.btn_reset = QPushButton('恢复默认外观')
        self.btn_reset.clicked.connect(self._reset)
        self.btn_cancel = QPushButton('取消')
        self.btn_cancel.clicked.connect(self.close)
        self.btn_apply = QPushButton('应用')
        self.btn_apply.setDefault(True)
        self.btn_apply.clicked.connect(self._apply)
        btns.addWidget(self.btn_reset)
        btns.addStretch(1)
        btns.addWidget(self.btn_cancel)
        btns.addWidget(self.btn_apply)
        root.addLayout(btns)

        self.hint = QLabel('改动点「应用」后立即生效并写入 config.json；双击托盘图标可随时打开本面板。')
        self.hint.setStyleSheet('color:#888888;')
        root.addWidget(self.hint)

    def _add_color(self, grid, row, label, key):
        btn = QPushButton('—')
        btn.setMinimumWidth(110)
        btn.setFixedHeight(24)
        self._colors[key] = btn
        btn.clicked.connect(lambda _, k=key: self._pick(k))
        grid.addWidget(QLabel(label), row, 0)
        grid.addWidget(btn, row, 1)

    def _pick(self, key):
        cur = qcol(self._colors[key].property('hexval') or '#ffffff', fallback='#ffffff')
        c = QColorDialog.getColor(cur, self, '选择颜色')
        if c.isValid():
            self._colors[key].setProperty('hexval', c.name())
            self._style_color(key)

    def _style_color(self, key):
        btn = self._colors[key]
        v = btn.property('hexval') or '#ffffff'
        c = qcol(v, fallback='#ffffff')
        btn.setText(c.name().upper())
        fg = '#ffffff' if c.lightness() < 140 else '#111111'
        btn.setStyleSheet('QPushButton{background:%s;color:%s;'
                          'border:1px solid rgba(128,128,128,0.55);border-radius:4px;}'
                          % (c.name(), fg))

    def reload(self):
        """把 CFG 读进控件"""
        self.cb_island.setChecked(bool(CFG.get('show_island', True)))
        self.cb_tb.setChecked(bool(CFG.get('show_taskbar', True)))
        self.cb_trans.setChecked(bool(CFG.get('show_translation', True)))
        idx = self.cmb_layout.findData(CFG.get('island_layout', 'compact'))
        self.cmb_layout.setCurrentIndex(max(0, idx))
        self.sp_radius.setValue(int(CFG.get('island_radius', 24)))
        self.sp_ifont.setValue(int(CFG.get('island_font', 11)))
        self.sp_alpha.setValue(int(CFG.get('island_alpha', 246)))
        tidx = self.cmb_theme.findData(CFG.get('tb_theme', 'auto'))
        self.cmb_theme.setCurrentIndex(max(0, tidx))
        self.sp_tfont.setValue(int(CFG.get('tb_font', 10)))
        self.cb_cover.setChecked(bool(CFG.get('tb_show_cover', True)))
        self.cb_btns.setChecked(bool(CFG.get('tb_show_btns', True)))
        self.cb_autohide.setChecked(bool(CFG.get('tb_btns_auto_hide', True)))
        for k, btn in self._colors.items():
            btn.setProperty('hexval', CFG.get(k) or DEFAULT_CFG.get(k) or '#ffffff')
            self._style_color(k)

    def _apply(self):
        CFG['show_island'] = self.cb_island.isChecked()
        CFG['show_taskbar'] = self.cb_tb.isChecked()
        CFG['show_translation'] = self.cb_trans.isChecked()
        CFG['island_layout'] = self.cmb_layout.currentData() or 'compact'
        CFG['island_radius'] = self.sp_radius.value()
        CFG['island_font'] = self.sp_ifont.value()
        CFG['island_alpha'] = self.sp_alpha.value()
        for k, btn in self._colors.items():
            v = btn.property('hexval')
            if isinstance(v, str) and v:
                CFG[k] = v
        CFG['tb_theme'] = self.cmb_theme.currentData() or 'auto'
        CFG['tb_font'] = self.sp_tfont.value()
        CFG['tb_show_cover'] = self.cb_cover.isChecked()
        CFG['tb_show_btns'] = self.cb_btns.isChecked()
        CFG['tb_btns_auto_hide'] = self.cb_autohide.isChecked()
        save_cfg(CFG)
        PENDING_CMDS.append('cfg_changed')
        log('settings dialog applied')

    def _reset(self):
        """恢复默认外观（只重置外观相关键，不动位置/自启/翻译开关）"""
        for k in ('island_layout', 'island_bg', 'island_bg2', 'island_text', 'island_sub',
                  'island_accent', 'island_radius', 'island_font', 'island_alpha',
                  'tb_theme', 'tb_text', 'tb_accent', 'tb_font',
                  'tb_show_cover', 'tb_show_btns', 'tb_btns_auto_hide'):
            CFG[k] = DEFAULT_CFG[k]
        save_cfg(CFG)
        self.reload()
        PENDING_CMDS.append('cfg_changed')

# ================================================================
# 开机自启动
# ================================================================
RUN_KEY = r'Software\Microsoft\Windows\CurrentVersion\Run'
PYW = os.path.join(os.path.dirname(sys.executable), 'pythonw.exe')

def launch_command():
    """开机自启动命令行：打包成 exe 后直接指向自身（不带参数 = 走看门狗，可自愈）"""
    if IS_FROZEN:
        return '"%s"' % os.path.abspath(sys.executable)
    return '"%s" "%s"' % (PYW, os.path.abspath(__file__))

def set_autostart(on):
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
            if on:
                winreg.SetValueEx(k, 'MoeKoeIsland', 0, winreg.REG_SZ, launch_command())
            else:
                try: winreg.DeleteValue(k, 'MoeKoeIsland')
                except FileNotFoundError: pass
        return True
    except Exception as e:
        log('autostart fail: %r' % e)
        return False

# ================================================================
# Native Host —— 作为 MoeKoe Music 插件 native 组件被拉起时的协议通道
#
#   MoeKoe 用管道连接 stdin/stdout：
#     输入：{"type":"message","payload":{...}}  /  {"type":"shutdown"}
#     输出：{"type":"pong","time":...} 等，一行一个 JSON
#   独立运行（双击）时 stdout/stdin 不可用 → 全部安全降级，不影响 GUI。
# ================================================================
def _open_stdin():
    try:
        if sys.stdin is not None and sys.stdin.fileno() >= 0:
            return getattr(sys.stdin, 'buffer', sys.stdin)
    except Exception:
        pass
    try:
        return os.fdopen(0, 'rb', 0)
    except Exception:
        return None

def _open_stdout():
    try:
        if sys.stdout is not None and sys.stdout.fileno() >= 0:
            return getattr(sys.stdout, 'buffer', sys.stdout)
    except Exception:
        pass
    try:
        return os.fdopen(1, 'wb', 0)
    except Exception:
        return None

class NativeHostLink(threading.Thread):
    """读 stdin 的 JSON Lines、按需回 stdout；收到 shutdown 即退出进程"""

    def __init__(self):
        super().__init__(daemon=True)
        self._in = _open_stdin()
        self._out = _open_stdout()
        self.active = self._in is not None
        self._send_ok = self._out is not None
        self._ui_ready = False

    def send(self, obj):
        if self._out is None:
            return False
        try:
            self._out.write((json.dumps(obj, ensure_ascii=False) + '\n').encode('utf-8'))
            self._out.flush()
            return True
        except Exception:
            self._out = None
            return False

    def set_ui_ready(self, ready):
        self._ui_ready = bool(ready)

    def _status(self):
        try:
            autostart = bool(load_cfg().get('autostart'))
        except Exception:
            autostart = False
        return {
            'version': APP_VERSION,
            'ui': self._ui_ready,
            'connected': bool(STATE.connected),
            'playing': bool(STATE.is_playing),
            'song': (STATE.song or {}).get('name') or '',
            'artist': (STATE.song or {}).get('author') or '',
            'autostart': autostart,
            'settings': settings_view(),
        }

    def _dispatch(self, msg):
        if not isinstance(msg, dict):
            return
        mtype = msg.get('type')
        if mtype == 'shutdown':
            log('native host: shutdown received -> exit')
            self.send({'type': 'bye'})
            try:
                os._exit(EXIT_SHUTDOWN if os.environ.get('MOEKOE_SUPERVISED') else 0)
            except Exception:
                sys.exit(0)
        elif mtype == 'message':
            payload = msg.get('payload') or {}
            action = payload.get('action') if isinstance(payload, dict) else None
            # 本进程不是「画界面的那个实例」（插件另拉起了一个）时，把查询/设置类请求
            # 转发给 UI 实例处理——否则弹窗读到的是本进程的空状态
            # （典型症状：组件明明在跑，弹窗却显示"未连接"）。
            if not self._ui_ready and action in (
                    'status', 'get_settings', 'set_settings', 'open_settings',
                    'center_island', 'open_config_dir', 'quit'):
                req = dict(payload)
                req['action'] = action
                resp = bridge_request(req)
                if resp is not None:
                    log('native host: forwarded %r to UI instance -> %r'
                        % (action, resp.get('type')))
                    self.send(resp)
                    if action == 'quit':
                        time.sleep(0.2)
                        os._exit(EXIT_SHUTDOWN if os.environ.get('MOEKOE_SUPERVISED') else 0)
                    return
            if action == 'ping':
                self.send({'type': 'pong', 'time': int(time.time() * 1000)})
            elif action == 'status':
                self.send({'type': 'status', 'data': self._status()})
            elif action == 'get_settings':
                self.send({'type': 'settings', 'data': settings_view()})
            elif action == 'set_settings':
                ok = apply_settings_patch(payload.get('settings') or {})
                self.send({'type': 'ack', 'action': action, 'ok': bool(ok),
                           'data': settings_view()})
            elif action == 'open_settings':
                PENDING_CMDS.append('open_settings')
                self.send({'type': 'ack', 'action': action, 'ok': True})
            elif action == 'center_island':
                PENDING_CMDS.append('center_island')
                self.send({'type': 'ack', 'action': action, 'ok': True})
            elif action == 'control':
                cmd = payload.get('command')
                if cmd in ('toggle', 'next', 'prev'):
                    threading.Thread(target=ws_control, args=(cmd,), daemon=True).start()
                    self.send({'type': 'ack', 'command': cmd})
            elif action == 'open_config_dir':
                try:
                    os.makedirs(APP_DIR, exist_ok=True)
                    os.startfile(APP_DIR)
                    self.send({'type': 'ack', 'action': action, 'ok': True})
                except Exception as e:
                    self.send({'type': 'ack', 'action': action, 'ok': False, 'error': str(e)})
            elif action == 'autostart':
                ok = set_autostart(bool(payload.get('on')))
                self.send({'type': 'ack', 'action': action, 'ok': ok})
            elif action == 'quit':
                log('native host: quit requested via plugin')
                self.send({'type': 'ack', 'action': action})
                time.sleep(0.2)
                os._exit(EXIT_SHUTDOWN if os.environ.get('MOEKOE_SUPERVISED') else 0)
            else:
                self.send({'type': 'echo', 'payload': payload})

    def run(self):
        if not self.active:
            return
        started = time.time()
        saw_traffic = False
        log('native host: protocol link up (host=%s, stdout=%s)' % (HOST_ID, self._send_ok))
        self.send({'type': 'ready', 'host': HOST_ID, 'version': APP_VERSION})
        try:
            while True:
                raw = self._in.readline()
                if not raw:
                    break
                line = raw.decode('utf-8', 'replace').strip()
                if not line:
                    continue
                saw_traffic = True
                try:
                    self._dispatch(json.loads(line))
                except Exception as e:
                    log('native host: bad message %r (%r)' % (line[:200], e))
        except Exception as e:
            log('native host: stdin ended %r' % e)
        log('native host: protocol link down (traffic=%s)' % saw_traffic)

        # 读到 EOF 有两种可能：
        #   a) 宿主（MoeKoe）关闭了管道 → 跟随退出，避免留下孤儿进程
        #   b) stdin 本来就不是活管道（宿主用了 null 设备）→ 绝不能退出，
        #      否则组件会在启动瞬间自杀、看起来"完全没反应"
        if saw_traffic or (time.time() - started) > 5:
            log('native host: host link closed -> exit')
            os._exit(EXIT_SHUTDOWN if os.environ.get('MOEKOE_SUPERVISED') else 0)
        log('native host: stdin is not a live pipe -> keep GUI running')

# ---------------- main ----------------
SINGLE_LOCK = None

def _acquire_single_instance(quiet=False):
    """单实例锁：已有组件在画 UI（无论看门狗拉的、开机自启拉的还是插件拉的）就不抢"""
    global SINGLE_LOCK
    import socket as _s
    lk = _s.socket(_s.AF_INET, _s.SOCK_STREAM)
    try:
        lk.bind(('127.0.0.1', 65433))
    except OSError:
        try:
            lk.close()               # 不关会漏 socket（等待接管时会反复调用）
        except Exception:
            pass
        if not quiet:
            log('another island instance already running -> exit')
        return False
    lk.listen(1)
    SINGLE_LOCK = lk
    clear_quit_flag()      # 本进程已成为 UI 实例 → 上一次留下的「主动退出」标记作废
    return True

def supervise():
    """看门狗：持续拉起 GUI 工作进程（--run），异常退出 3 秒后自动重启。
    子进程因插件 shutdown 退出（码 42）时父进程同步退出；连崩 5 次休眠 10 分钟。
    打包成 exe 后，双击 exe 即走这条路径（进程数：1 看门狗 + 1 GUI）。"""
    import subprocess
    if IS_FROZEN:
        child = [os.path.abspath(sys.executable), '--run']
    else:
        child = [sys.executable, os.path.abspath(__file__), '--run']
    env = dict(os.environ, MOEKOE_SUPERVISED='1')
    log('supervisor: start child=%r' % (child,))
    fails = 0
    while True:
        t0 = time.time()
        try:
            rc = subprocess.call(child, env=env)
        except Exception as e:
            log('supervisor: spawn failed %r' % e)
            rc = -1
        if rc in (EXIT_SHUTDOWN, EXIT_ANOTHER_INSTANCE):
            log('supervisor: child exit code %r -> stop watchdog' % rc)
            return
        alive = time.time() - t0
        fails = 0 if alive > 30 else fails + 1
        log('supervisor: child exited rc=%r after %.1fs (fail streak=%d)' % (rc, alive, fails))
        if fails >= 5:
            log('supervisor: crash loop -> sleep 600s')
            time.sleep(600)
            fails = 0
        else:
            time.sleep(3)

def main():
    global ISLAND, STRIP, TRAY
    args = list(sys.argv[1:])
    native_host = '--native-host' in args      # 由 MoeKoe 插件拉起
    is_worker   = '--run' in args              # 实际渲染 GUI 的工作进程

    if native_host:
        is_worker = True                       # 生命周期由 MoeKoe 管理，不再套看门狗
    elif not is_worker:
        supervise()                            # 双击 exe 的默认路径：带崩溃自愈
        return

    link = NativeHostLink() if native_host else None
    if link is not None:
        link.start()

    if not _acquire_single_instance():
        if link is not None:
            # 已有实例在画 UI：本进程不重复渲染，只应答协议并等待接管
            # （原 UI 实例退出后自动接手，避免「插件说在运行但屏幕上看不到」）
            log('native host: UI owned by another instance -> standby, waiting to take over')
            while not _acquire_single_instance(quiet=True):
                if quit_flag_set():
                    # 用户是「主动退出」的 → 不要接管，否则窗口消失几秒又冒出来
                    clear_quit_flag()
                    log('native host: user quit detected -> standby exits too (no take-over)')
                    os._exit(0)
                time.sleep(3)
            log('native host: took over the UI')
        else:
            sys.exit(EXIT_ANOTHER_INSTANCE)
    try:
        import traceback as _tb
        def _excepthook(t, v, tb):
            log('UNCAUGHT %s:\n%s' % (t.__name__, ''.join(_tb.format_exception(t, v, tb))))
            sys.__excepthook__(t, v, tb)
        sys.excepthook = _excepthook
        from PyQt5.QtCore import qInstallMessageHandler
        def _qtmsg(msg_type, ctx, message):
            log('QT: %s' % message)
        qInstallMessageHandler(_qtmsg)

        log('island v%s starting (frozen=%s, native_host=%s)'
            % (APP_VERSION, IS_FROZEN, native_host))
        try:
            import faulthandler
            fh = open(DEBUG_F, 'a', encoding='utf-8')
            faulthandler.enable(fh)
        except Exception:
            pass
        os.makedirs(APP_DIR, exist_ok=True)
        app = QApplication(sys.argv)
        app.setQuitOnLastWindowClosed(False)
        app.setWindowIcon(make_tray_icon())

        win = Island()
        ISLAND = win
        strip = TaskbarWidget()
        STRIP = strip
        Island._btn_strip = strip
        LocalBridge().start()        # 供插件拉起的 standby 进程转发请求

        # 按配置决定初始可见性：灵动岛 / 任务栏组件 可单独显示，也可同时显示
        win.setVisible(bool(CFG.get('show_island', True)))
        strip.follow()
        TRAY = Tray(win, strip)
        apply_cfg_everywhere()
        WSClient().start()
        if link is not None:
            link.set_ui_ready(True)
        log('island v%s entering loop win=(%d,%d) island=%s tb=%s'
            % (APP_VERSION, win.x(), win.y(), win.isVisible(), strip.isVisible()))

        if not CFG.get('tray_hint_shown'):
            CFG['tray_hint_shown'] = True
            save_cfg(CFG)
            QTimer.singleShot(1500, lambda: TRAY and TRAY.notify(
                'MoeKoeIsland 已在后台运行',
                '双击托盘图标（或右键 → 外观与设置）可切换灵动岛 / 任务栏显示、改颜色与样式。'))

        def _hb():
            log('heartbeat pos=(%d,%d) tb=%s' % (win.x(), win.y(), strip.isVisible()))
        hb = QTimer(win, interval=10000, timeout=_hb)
        hb.start()
        log('heartbeat #0 pos=(%d,%d)' % (win.x(), win.y()))

        rc = app.exec_()
        log('island v%s loop exited rc=%r' % (APP_VERSION, rc))
        # 兜底：万一还有别的路径调了 QApplication.quit()，退出码 0 会被看门狗当成
        # 「崩溃」而重启。这里强制转成「真正退出」的语义（supervised → 42 → 父进程一起退）
        os._exit(EXIT_SHUTDOWN if os.environ.get('MOEKOE_SUPERVISED') else 0)
    except Exception:
        import traceback
        log('FATAL:\n' + traceback.format_exc())
        raise

if __name__ == '__main__':
    main()
