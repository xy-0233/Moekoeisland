// MoeKoeIsland - Native Host 桥接页
//
// 通信链路：
//   background(Service Worker) --Port--> bridge --electronAPI.nativeHost--> MoeKoe 主进程 --> exe stdin
//   exe stdout --> MoeKoe 主进程 --> electronAPI.nativeHost.onMessage --> bridge --> Port --> background
//
// 说明：MoeKoeIsland.exe 自己会连 ws://127.0.0.1:6520 拿歌词、用 SMTC 控制播放，
// 这条 native 通道主要用于「宿主进程管理与状态查询」（是否在跑、版本、当前歌曲）。

const HOST_ID = 'moekoe-island-host';

if (!window.electronAPI || !window.electronAPI.nativeHost) {
  console.error('[MoeKoeIsland Bridge] electronAPI.nativeHost 不可用，桥接页无法工作。');
} else {

  const port = chrome.runtime.connect({ name: 'moekoe-native-host-bridge' });
  console.log('[MoeKoeIsland Bridge] connected to background');

  const reply = (requestId, seq, result) => {
    port.postMessage({
      type: 'native-host:response',
      requestId,
      seq,
      result,
    });
  };

  // exe → 插件
  window.electronAPI.nativeHost.onMessage((payload) => {
    if (!payload || payload.hostId !== HOST_ID) return;
    port.postMessage({ type: 'native-host:event', payload: payload.message });
  });

  // 插件 → exe
  port.onMessage.addListener(async (message) => {
    if (!message || !message.type) return;
    try {
      if (message.type === 'native-host:status') {
        reply(message.requestId, message.seq,
              await window.electronAPI.nativeHost.getStatus(HOST_ID));
      } else if (message.type === 'native-host:send') {
        reply(message.requestId, message.seq,
              await window.electronAPI.nativeHost.send(HOST_ID, message.payload));
      } else if (message.type === 'native-host:restart') {
        if (typeof window.electronAPI.nativeHost.restart === 'function') {
          reply(message.requestId, message.seq,
                await window.electronAPI.nativeHost.restart(HOST_ID));
        } else {
          reply(message.requestId, message.seq,
                { success: false, message: '当前版本不支持重启接口' });
        }
      }
    } catch (e) {
      reply(message.requestId, message.seq, { success: false, message: String(e) });
    }
  });
}
