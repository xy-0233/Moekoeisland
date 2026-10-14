# MoeKoeIsland native host 源码

本目录是插件包内 `bin/win32/MoeKoeIsland.exe` 的**完整源码与构建配置**，用于插件上架审核与可复现构建。

## 文件清单

| 文件 | 说明 |
|---|---|
| `MoeKoeIsland_original_ui.py` | 主程序源码，5407 行，`APP_VERSION = '1.7.24'` |
| `MoeKoeIsland.spec` | PyInstaller 打包配置（单文件 / 无控制台 / UPX） |
| `requirements.txt` | 依赖清单（含可选依赖） |

## 与二进制的对应关系

`bin/win32/MoeKoeIsland.exe` 即由本目录源码打包而来，可自行验证：

1. 该 exe 是 PyInstaller onefile 产物，其归档目录（TOC）中的**唯一入口脚本**为
   `MoeKoeIsland_original_ui`，另有 5 个 PyInstaller 自带 runtime hook，无其他自定义脚本。
2. 把 exe 内嵌的该模块字节码反序列化后，与本文件重新 `compile()` 的结果逐项比对
   （`co_code` / 递归 `co_consts` / `co_names` / `co_varnames` / `co_argcount`）**完全一致**。

> 因此本目录源码与仓库中二进制的行为严格一致，不存在源码与产物不符的情况。

## 依赖

- **必需**：Python 3.13 + PyQt5（`PyQt5>=5.15,<6`）
- **可选**（缺失时对应功能自动降级，不影响运行）：
  - `winrt-runtime` + `winrt-Windows.Media.Control` —— SMTC 系统媒体控制通道
  - `Pillow` —— 外观设置中的「从屏幕取色」

## 构建

```bash
pip install -r requirements.txt
pyinstaller MoeKoeIsland.spec --noconfirm --clean
# 产物 dist/MoeKoeIsland.exe 即 native host 二进制
```

## 程序行为说明（供审核参考）

**定位**：MoeKoe Music 的桌面组件（屏幕顶部灵动岛 + 任务栏歌词条），以 native host 形式被插件拉起，
也支持双击独立运行。

**进程与通信**

- 被插件拉起时，通过 stdin/stdout 按「一行一个 JSON」与扩展通信（`{"type":"message",...}` / `{"type":"shutdown"}`），
  并声明 `host id = moekoe-island-host`（与 `manifest.json` 的 `moekoe_native_hosts[].id` 一致）。
- 独立运行时使用**单实例锁**（`127.0.0.1:65433`），避免重复拉起多个 UI。
- 双击启动走**看门狗**模式：父进程守护 GUI 子进程（`--run`），异常退出后 3 秒重启；
  连续崩溃 5 次后休眠 10 分钟；收到插件 shutdown 时以退出码 42 一并退出。

**数据获取**

- 连接本机 `ws://127.0.0.1:6520`（MoeKoe Music 需开启 API 模式）读取播放状态与歌词。
- 专辑封面：仅当播放器下发的曲目信息中带有 `http(s)` 封面地址时，用 `urllib` 下载该图片用于显示，
  并做最多 30 张的内存缓存。**不向任何第三方服务器主动上报数据。**

**播放控制**（按优先级自动降级）

1. SMTC（`winrt.windows.media.control`）
2. WebSocket 插件通道（带回执校验与重试）
3. 系统媒体键（`keybd_event` 发送 `VK_MEDIA_PLAY_PAUSE` / `NEXT` / `PREV`）

**本地读写**

- 配置：`%APPDATA%\MoeKoeIsland\config.json`（读写）
- 日志：`%APPDATA%\MoeKoeIsland\debug.log`（追加写，用于排障）
- 开机自启：仅在用户于设置中显式开启时，写 `HKCU\...\CurrentVersion\Run` 下的 `MoeKoeIsland` 项；
  关闭时删除该项。

**窗口技术点**

- 无边框置顶窗口，通过 `WM_NCHITTEST` 返回 `HTTRANSPARENT` 实现「胶囊可点、其余区域鼠标穿透」，
  任务栏在非胶囊区域照常可用。
- 不注入、不挂钩任何第三方进程；不使用 `subprocess` 执行外部命令（仅用于自启自身的看门狗）。
