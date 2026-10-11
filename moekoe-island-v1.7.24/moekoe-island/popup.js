// MoeKoeIsland - 插件控制台
//
// 弹窗只负责展示状态、切换显示模式、发送播放控制和打开设置。
// 歌词数据与任务栏/灵动岛窗口仍由 MoeKoeIsland.exe 独立处理。

const ICON_PLAY = '<path d="M8 5.2v13.6L19 12z"/>';
const ICON_PAUSE = '<path d="M8 5.4h3.3v13.2H8zM12.7 5.4H16v13.2h-3.3z"/>';

const $ = (id) => document.getElementById(id);
const $$ = (selector) => Array.from(document.querySelectorAll(selector));

const state = {
  authorized: false,
  running: false,
  connected: null,
  playing: false,
  version: '',
  song: '',
  autostart: false,
  handshake: false,
  settings: null,
};

function hint(text, kind) {
  const el = $('hint');
  if (!text) {
    el.classList.add('hide');
    return;
  }
  el.classList.remove('hide');
  el.classList.toggle('err', kind === 'err');
  el.innerHTML = text;
}

function currentMode() {
  const s = state.settings || {};
  const showIsland = s.show_island !== false;
  const showTaskbar = s.show_taskbar === true;
  if (showIsland && showTaskbar) return 'both';
  if (showTaskbar) return 'taskbar';
  return 'island';
}

function setText(id, value, title) {
  const el = $(id);
  if (!el) return;
  el.textContent = value;
  if (title !== undefined) el.title = title;
}

function renderMode() {
  const mode = currentMode();
  const label = mode === 'both' ? '双显示'
    : mode === 'taskbar' ? '仅任务栏'
    : '仅灵动岛';

  setText('modeLabel', label);
  $$('[data-mode]').forEach((button) => {
    button.classList.toggle('active', button.dataset.mode === mode);
  });

  if (state.settings) {
    $('swIsland').checked = state.settings.show_island !== false;
    $('swTaskbar').checked = state.settings.show_taskbar === true;
    if (typeof state.settings.show_translation === 'boolean') {
      $('swTrans').checked = state.settings.show_translation;
    }
  }
}

function renderPreview() {
  const song = state.song || '';
  const main = song || (state.connected === false ? '未连接 MoeKoe Music' : '正在等待 MoeKoe Music');
  const sub = state.connected
    ? (state.playing ? '歌词将跟随播放逐字高亮' : '已连接，播放时开始同步')
    : '连接后显示当前歌词与翻译';

  setText('previewLyric', main, main);
  setText('previewSub', sub, sub);
  setText('taskbarMain', song || '任务栏歌词预览', song || '');
  setText('taskbarSub', state.playing ? 'hover 展开上一曲 / 播放 / 下一曲' : 'hover 展开控制键');
}

function render() {
  const dot = $('hostDot');
  if (!state.authorized) dot.className = 'dot warn';
  else if (state.running) dot.className = 'dot on';
  else dot.className = 'dot off';

  const hostText = !state.authorized ? '未授权' : state.running ? '运行中' : '未运行';
  setText('hostState', hostText);
  setText('bridgeState', hostText);
  setText('ver', state.version ? `组件版本 ${state.version}` : '组件版本 —');

  const connText = state.connected === null ? '等待连接'
    : state.connected ? '播放器已连接' : '播放器未连接';
  setText('connState', connText);
  setText('playerState', state.connected === null ? '未知'
    : state.connected ? (state.playing ? '播放中' : '已暂停') : '未连接');

  const songText = state.song || '—';
  setText('songName', songText, state.song || '');
  $('toggleIcon').innerHTML = state.playing ? ICON_PAUSE : ICON_PLAY;
  $('autostart').checked = state.autostart;

  renderMode();
  renderPreview();

  if (!state.authorized) {
    hint('首次使用请在 MoeKoe 的「插件管理」中<b>授权本地组件</b>，灵动岛与任务栏歌词才会出现。');
  } else if (!state.running) {
    hint('本地组件未在运行。可以在插件管理中重新启用，或直接启动插件目录里的 <b>MoeKoeIsland.exe</b>。');
  } else if (state.connected === false) {
    hint('组件已运行，但还没连上播放器。请确认 MoeKoe 正在播放，并在设置里开启 <b>API 模式</b>。', 'err');
  } else {
    hint('');
  }
}

function bg(msg) {
  return new Promise((resolve) => {
    try {
      chrome.runtime.sendMessage(msg, (r) => {
        if (chrome.runtime.lastError) resolve(null);
        else resolve(r);
      });
    } catch (e) {
      resolve(null);
    }
  });
}

function applyHostStatus(res) {
  if (!res) return false;
  const host = res.host || {};
  state.authorized = host.authorized === true;
  state.running = host.running === true || host.started === true
    || host.pid != null || host.status === 'running';
  return true;
}

function applyExeStatus(data) {
  if (!data || typeof data !== 'object') return;
  state.connected = !!data.connected;
  state.playing = !!data.playing;
  state.version = data.version || state.version;
  state.song = data.artist ? `${data.song} - ${data.artist}` : (data.song || '');
  if (typeof data.autostart === 'boolean') state.autostart = data.autostart;
  if (data.settings && typeof data.settings === 'object') state.settings = data.settings;
  state.handshake = true;
}

chrome.runtime.onMessage.addListener((msg) => {
  if (!msg || msg.type !== 'host-event') return;
  const payload = msg.payload || {};
  if (payload.type === 'status') applyExeStatus(payload.data);
  else if (payload.type === 'settings') state.settings = payload.data || null;
  else if (payload.type === 'ack') {
    if (payload.action === 'set_settings' && payload.data) state.settings = payload.data;
  } else if (payload.type === 'ready') {
    state.handshake = true;
    state.version = payload.version || state.version;
  }
  render();
});

async function refresh() {
  applyHostStatus(await bg({ type: 'host-status' }));
  render();

  if (state.authorized) {
    await bg({ type: 'host-send', payload: { action: 'status' } });
    await bg({ type: 'host-send', payload: { action: 'get_settings' } });
    setTimeout(render, 400);
  }
}

async function setSetting(key, value) {
  state.settings = Object.assign({}, state.settings, { [key]: value });
  render();
  await bg({ type: 'host-send', payload: { action: 'set_settings', settings: { [key]: value } } });
}

async function setDisplayMode(mode) {
  const next = mode === 'both'
    ? { show_island: true, show_taskbar: true }
    : mode === 'taskbar'
      ? { show_island: false, show_taskbar: true }
      : { show_island: true, show_taskbar: false };

  state.settings = Object.assign({}, state.settings, next);
  render();
  await bg({ type: 'host-send', payload: { action: 'set_settings', settings: next } });
}

async function control(command) {
  await bg({ type: 'host-send', payload: { action: 'control', command } });
  setTimeout(refresh, 500);
}

function bind() {
  $('prev').addEventListener('click', () => control('prev'));
  $('toggle').addEventListener('click', () => control('toggle'));
  $('next').addEventListener('click', () => control('next'));
  $('refresh').addEventListener('click', refresh);

  $$('[data-mode]').forEach((button) => {
    button.addEventListener('click', () => setDisplayMode(button.dataset.mode));
  });

  $('openDir').addEventListener('click', async () => {
    const r = await bg({ type: 'host-send', payload: { action: 'open_config_dir' } });
    if (!r || r.success !== true) hint('无法打开配置目录：本地组件未运行或未授权。', 'err');
  });

  $('autostart').addEventListener('change', async (e) => {
    state.autostart = e.target.checked;
    render();
    await bg({ type: 'host-send', payload: { action: 'autostart', on: state.autostart } });
    setTimeout(refresh, 400);
  });

  $('swIsland').addEventListener('change', (e) => setSetting('show_island', e.target.checked));
  $('swTaskbar').addEventListener('change', (e) => setSetting('show_taskbar', e.target.checked));
  $('swTrans').addEventListener('change', (e) => setSetting('show_translation', e.target.checked));

  $('openSettings').addEventListener('click', async () => {
    const r = await bg({ type: 'host-send', payload: { action: 'open_settings' } });
    if (!r || r.success !== true) hint('无法打开设置面板：本地组件未运行或未授权。', 'err');
  });
}

document.addEventListener('DOMContentLoaded', () => {
  bind();
  refresh();
  setInterval(refresh, 3000);
});
