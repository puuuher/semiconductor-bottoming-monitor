#!/bin/zsh
# 双击此文件：下载已收盘日线、更新回测、打开中文状态页。
cd "$(dirname "$0")" || exit 1

if ! python3 semiconductor_bottoming_backtest.py; then
  echo "\n更新失败；错误信息见上方。按任意键关闭窗口。"
  read -k 1
  exit 1
fi

open backtest_output/latest_status.html
