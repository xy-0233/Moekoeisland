# -*- mode: python ; coding: utf-8 -*-
#
# MoeKoeIsland native host —— PyInstaller 打包配置
#
# 与 bin/win32/MoeKoeIsland.exe（v1.7.24）一致的构建方式：
#   单文件（onefile）、无控制台（windowed）、UPX 压缩。
#
# 用法（在本目录下执行）：
#   pyinstaller MoeKoeIsland.spec --noconfirm --clean
# 产物：dist/MoeKoeIsland.exe  →  拷贝为 ../../bin/win32/MoeKoeIsland.exe

a = Analysis(
    ['MoeKoeIsland_original_ui.py'],
    pathex=[],
    binaries=[],
    datas=[],
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='MoeKoeIsland',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)
