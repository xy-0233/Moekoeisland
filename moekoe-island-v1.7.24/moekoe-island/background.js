// MoeKoeIsland - Background Service Worker
//
// 职责：把 popup 的请求经 bridge 页转给 MoeKoeIsland.exe（native host），
// 并把 exe 主动上报的事件广播给 popup。
//
// 注意：歌词/播放状态**不走**这条通道 —— MoeKoeIsland.exe 自己连接
// ws://127.0.0.1:6520 读取歌词、并用 SMTC 控制播放，
// 所以即使插件页面从未打开，灵动岛也能正常工作。
// 这条通道只用于「宿主进程状态查询 / 控制 / 配置」。

const HOST_ID = 'moekoe-island-host';
const REQUEST_TIMEOUT = 6000;

let bridgePort = null;
const waiters = new Map();
let seq = 0;

chrome.runtime.onConnect.addListener((port) => {
  if (port.name !== 'moekoe-native-host-bridge') return;
  bridgePort = port;
  console.log('[MoeKoeIsland] bridge connected');

  port.onMessage.addListener((msg) => {
    if (!msg || !msg.type) return;

    if (msg.type === 'native-host:response') {
      const done = waiters.get(msg.requestId);
      if (done) {
        waiters.delete(msg.requestId);
        done(msg.result);
      }
    } else if (msg.type === 'native-host:event') {
      // exe 主动上报（ready / pong / bye）→ 广播给已打开的 popup
      chrome.runtime.sendMessage({ type: 'host-event', payload: msg.payload })
        .catch(() => { /* 没有 popup 在监听，忽略 */ });
    }
  });

  port.onDisconnect.addListener(() => {
    if (bridgePort === port) {
      bridgePort = null;
      console.log('[MoeKoeIsland] bridge disconnected');
    }
  });
});

function request(type, payload) {
  return new Promise((resolve) => {
    if (!bridgePort) {
      resolve({ success: false, message: 'native bridge 尚未就绪' });
      return;
    }
    const id = ++seq;
    waiters.set(id, resolve);
    bridgePort.postMessage({ type, requestId: id, seq: id, payload });
    setTimeout(() => {
      if (waiters.has(id)) {
        waiters.delete(id);
        resolve({ success: false, message: '请求超时' });
      }
    }, REQUEST_TIMEOUT);
  });
}

const getHostStatus = () => request('native-host:status');
const sendToHost = (payload) => request('native-host:send', payload);

chrome.runtime.onMessage.addListener((msg, sender, sendResponse) => {
  if (!msg || !msg.type) return false;

  switch (msg.type) {
    case 'host-status':
      getHostStatus().then(sendResponse);
      return true;
    case 'host-send':
      sendToHost(msg.payload).then(sendResponse);
      return true;
    case 'bridge-state':
      sendResponse({ bridge: !!bridgePort });
      return false;
    default:
      return false;
  }
});

chrome.runtime.onInstalled.addListener(() => {
  console.log('[MoeKoeIsland] installed (host id = %s)', HOST_ID);
});
