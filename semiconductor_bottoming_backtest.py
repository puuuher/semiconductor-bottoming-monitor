#!/usr/bin/env python3
"""Semiconductor pullback-stabilisation signals and a no-look-ahead backtest.

Default provider is Yahoo Finance's public chart endpoint (no third-party Python
packages).  It can also read exported IBKR/Yahoo CSV files with Date, Open,
High, Low, Close, Volume columns.  This is research software, not advice.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import html
import json
import math
import shutil
import statistics
import ssl
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from zoneinfo import ZoneInfo

TICKERS = ("SOXX", "LRCX", "MU", "SMH", "SPY")
HORIZONS = (5, 20, 60)
SCRIPT_DIR = Path(__file__).resolve().parent
US_EASTERN = ZoneInfo("America/New_York")


@dataclass
class Bar:
    date: dt.date
    open: float
    high: float
    low: float
    close: float
    volume: float


def mean(values): return sum(values) / len(values) if values else None
def percentile(values, p):
    if not values: return None
    xs = sorted(values); k = (len(xs) - 1) * p; lo = int(k); hi = math.ceil(k)
    return xs[lo] if lo == hi else xs[lo] + (xs[hi] - xs[lo]) * (k - lo)
def fmt(x): return "n/a" if x is None else f"{x * 100:.2f}%"
def med(values): return statistics.median(values) if values else None


def validate_bars(bars, label):
    if len({b.date for b in bars}) != len(bars):
        raise ValueError(f"Duplicate daily dates in {label}")
    if any(not all(math.isfinite(x) for x in (b.open, b.high, b.low, b.close, b.volume))
           or not (0 < b.low <= b.open <= b.high and b.low <= b.close <= b.high and b.volume >= 0)
           for b in bars):
        raise ValueError(f"Invalid OHLCV values in {label}")
    return sorted(bars, key=lambda b: b.date)


def last_completed_us_date(now: dt.datetime | None = None) -> dt.date:
    """Allow an hour after 16:00 New York time for daily bars to settle."""
    current = (now or dt.datetime.now(dt.timezone.utc)).astimezone(US_EASTERN)
    date = current.date() if current.time() >= dt.time(17) else current.date() - dt.timedelta(days=1)
    while date.weekday() >= 5:
        date -= dt.timedelta(days=1)
    return date


def previous_weekday(date: dt.date) -> dt.date:
    while date.weekday() >= 5:
        date -= dt.timedelta(days=1)
    return date


def public_json(url: str, insecure: bool = False):
    """Use macOS curl's system trust store when Python's CA file is missing."""
    if sys.platform == "darwin" and shutil.which("curl") and not insecure:
        process = subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                                  "--max-time", "35", "--retry", "2", "--retry-delay", "1",
                                  "--header", "User-Agent: Mozilla/5.0 research-script", url],
                                 capture_output=True, timeout=45)
        if process.returncode:
            raise ValueError(process.stderr.decode("utf-8", "replace").strip())
        return json.loads(process.stdout)
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 research-script"})
    context = ssl._create_unverified_context() if insecure else None
    with urllib.request.urlopen(request, timeout=35, context=context) as response:
        return json.load(response)


def yahoo_bars(ticker: str, start: dt.date, end: dt.date, insecure: bool = False) -> list[Bar]:
    """Download Yahoo chart OHLCV, which may reflect historical stock splits.

    Adjusted close (which includes dividends) is deliberately not mixed with
    OHLC trade entry and exit prices.
    """
    path = "/v8/finance/chart/" + urllib.parse.quote(ticker)
    query = urllib.parse.urlencode({"period1": int(dt.datetime.combine(start, dt.time(), dt.timezone.utc).timestamp()),
                                   "period2": int(dt.datetime.combine(end + dt.timedelta(days=1), dt.time(), dt.timezone.utc).timestamp()),
                                   "interval": "1d", "events": "history"})
    # Query2 is a public mirror used only if query1 is unavailable/rate-limited.
    errors = []
    for host in ("query1.finance.yahoo.com", "query2.finance.yahoo.com"):
        try:
            payload = public_json(f"https://{host}{path}?{query}", insecure)
            if payload.get("chart", {}).get("error"):
                raise ValueError(str(payload["chart"]["error"]))
            break
        except (urllib.error.URLError, ValueError, subprocess.TimeoutExpired, json.JSONDecodeError) as exc:
            errors.append(f"{host}: {exc}")
    else:
        raise ValueError("; ".join(errors))
    result = payload["chart"]["result"][0]; q = result["indicators"]["quote"][0]
    output = []
    for i, stamp in enumerate(result["timestamp"]):
        fields = [q[x][i] for x in ("open", "high", "low", "close", "volume")]
        if any(x is None for x in fields) or min(fields[:4]) <= 0: continue
        date = dt.datetime.fromtimestamp(stamp, dt.timezone.utc).date()
        if start <= date <= end:
            output.append(Bar(date, *map(float, fields)))
    return validate_bars(output, ticker)


def csv_bars(path: Path) -> list[Bar]:
    rows = []
    with path.open(newline="", encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            lower = {str(k).lower().strip(): v for k, v in row.items()}
            try:
                date = dt.date.fromisoformat(lower["date"][:10])
                rows.append(Bar(date, *(float(lower[x].replace(",", "")) for x in ("open", "high", "low", "close", "volume"))))
            except (KeyError, ValueError, AttributeError):
                continue
    if not rows: raise ValueError(f"No usable OHLCV rows in {path}")
    return validate_bars(rows, path)


def sma(bars, i, n): return mean([b.close for b in bars[i-n+1:i+1]]) if i >= n - 1 else None
def true_range(bars, i):
    if i == 0: return bars[i].high - bars[i].low
    return max(bars[i].high-bars[i].low, abs(bars[i].high-bars[i-1].close), abs(bars[i].low-bars[i-1].close))
def atr(bars, i, n=14): return mean([true_range(bars, j) for j in range(i-n+1, i+1)]) if i >= n else None


def align(asset: list[Bar], market: list[Bar]):
    market_by_date = {b.date: b for b in market}
    return [(a, market_by_date[a.date]) for a in asset if a.date in market_by_date]


def signal_rows(asset: list[Bar], market: list[Bar]):
    """All tests use information available at the signal-day close.

    Mandatory: a >=6% 20-day pullback and recovery above yesterday's high OR
    SMA5.  At least 3 of 4 confirmations are needed: normalising volume,
    no extreme true range, 5-day relative strength not worse than -4%, and
    a non-broken market (SPY above SMA20 or not making a 5-day closing low).
    """
    pairs = align(asset, market); a = [x[0] for x in pairs]; m = [x[1] for x in pairs]
    results = []
    for i in range(20, len(a)):
        peak = max(b.high for b in a[i-20:i])
        drawdown = a[i].low / peak - 1
        recovery = a[i].close > a[i-1].high or a[i].close > sma(a, i, 5)
        vol_base = med([b.volume for b in a[i-20:i]])
        volume_ok = a[i].volume >= vol_base
        atr14 = atr(a, i); range_ok = true_range(a, i) <= 1.75 * atr14
        rs5 = (a[i].close / a[i-5].close - 1) - (m[i].close / m[i-5].close - 1)
        rs_ok = rs5 >= -0.04
        market_sma = sma(m, i, 20)
        market_ok = m[i].close > market_sma or m[i].close > min(b.close for b in m[i-5:i])
        confirms = sum((volume_ok, range_ok, rs_ok, market_ok))
        trigger = drawdown <= -0.06 and recovery and confirms >= 3
        results.append({"i": i, "date": a[i].date.isoformat(), "trigger": trigger, "drawdown": drawdown,
                        "recovery": recovery, "volume_ok": volume_ok, "range_ok": range_ok, "rs5": rs5,
                        "rs_ok": rs_ok, "market_ok": market_ok, "confirmations": confirms})
    return results, a


def dedupe(rows, gap):
    selected = []; last = -10**9
    for r in rows:
        if r["trigger"] and r["i"] - last >= gap:
            selected.append(r); last = r["i"]
    return selected


def dip_rows(asset):
    # Baseline: buy the next open after a single-day -5% close-to-close fall.
    return [{"i": i, "date": asset[i].date.isoformat(), "trigger": asset[i].close / asset[i-1].close - 1 <= -0.05}
            for i in range(1, len(asset))]


def event_stats(events, bars, horizon, cost_one_way):
    outcomes = []
    for e in events:
        i = e["i"]
        if i + horizon >= len(bars): continue
        entry = bars[i+1].open
        # A conservative proportional model: pay cost on purchase and sale.
        ret = bars[i+horizon].close * (1 - cost_one_way) / (entry * (1 + cost_one_way)) - 1
        mae = min(b.low for b in bars[i+1:i+horizon+1]) / entry - 1
        outcomes.append({**e, "entry_date": bars[i+1].date.isoformat(), "entry": entry,
                         "exit_date": bars[i+horizon].date.isoformat(), "return": ret, "mae": mae})
    rs = [x["return"] for x in outcomes]; maes = [x["mae"] for x in outcomes]
    return outcomes, {"n": len(rs), "win_rate": mean([x > 0 for x in rs]), "mean": mean(rs),
                      "p25": percentile(rs,.25), "median": percentile(rs,.5), "p75": percentile(rs,.75),
                      "mean_mae": mean(maes), "worst_mae": min(maes) if maes else None}


def write_csv(path, rows):
    if not rows: path.write_text("\n", encoding="utf-8"); return
    columns = list(rows[0])
    with path.open("w", newline="", encoding="utf-8") as f:
        out = csv.DictWriter(f, fieldnames=columns); out.writeheader(); out.writerows(rows)


def line(name, s):
    return f"| {name} | {s['n']} | {fmt(s['win_rate'])} | {fmt(s['mean'])} | {fmt(s['p25'])} | {fmt(s['median'])} | {fmt(s['p75'])} | {fmt(s['mean_mae'])} | {fmt(s['worst_mae'])} |"


def run_one(ticker, asset, market, out, asof, analysis_start, event_gap, oos_split, cost_one_way):
    signals, aligned = signal_rows(asset, market)
    if len(aligned) < 90 or not signals:
        raise ValueError(f"{ticker}: fewer than 90 common daily bars with SPY")
    study = [x for x in signals if x["date"] >= analysis_start.isoformat()]
    if not study:
        raise ValueError(f"{ticker}: no data in the requested study period")
    # The 60-day study events have disjoint holding windows.
    raw = [x for x in study if x["trigger"]]
    independent = dedupe(study, event_gap)
    dip = dedupe([x for x in dip_rows(aligned) if x["date"] >= analysis_start.isoformat()], event_gap)
    cutoff = study[int(len(study) * oos_split)]["i"]
    # Select OOS events independently so a training-period event cannot suppress one.
    oos = dedupe([x for x in study if x["i"] >= cutoff], event_gap)
    unconditional = [{"i": i, "date": aligned[i].date.isoformat()}
                     for i in range(study[0]["i"], len(aligned) - 1, event_gap)]
    all_events = []
    report = [f"# {ticker} 止跌信号回测", "", f"研究区间：{analysis_start} 至 {asof}；数据实际截至：{aligned[-1].date}。", "",
              f"交易假设：信号在 T 日收盘后生成，T+1 开盘买入，T+h 日收盘卖出；未计税。每次买入和卖出各计 {cost_one_way*10000:.1f} bp 的成本。",
              f"主样本事件间隔 {event_gap} 个交易日，消除最长 60 日持有期的样本重叠。原始触发 {len(raw)} 次；逐日规则状态见 signals.csv。", "",
              "| 策略 / 持有期 | n | 胜率 | 均值 | P25 | 中位数 | P75 | 平均MAE | 最差MAE |",
              "|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    result = {"ticker": ticker, "as_of_data": aligned[-1].date.isoformat(), "last_signal": signals[-1],
              "rule_events_raw": len(raw), "rule_events_independent": len(independent),
              "oos_start": aligned[cutoff].date.isoformat(), "horizons": {}}
    for h in HORIZONS:
        ev, st = event_stats(independent, aligned, h, cost_one_way)
        _, base_st = event_stats(dip, aligned, h, cost_one_way)
        _, oos_st = event_stats(oos, aligned, h, cost_one_way)
        _, uncond_st = event_stats(unconditional, aligned, h, cost_one_way)
        all_events.extend([{**x, "strategy": "bottom_signal", "horizon": h} for x in ev])
        report.extend([line(f"止跌规则 / {h}日", st), line(f"大跌次日买 / {h}日", base_st),
                       line(f"无条件定期买 / {h}日", uncond_st), line(f"止跌规则 OOS / {h}日", oos_st)])
        result["horizons"][str(h)] = {"bottom_signal": st, "dip_buy": base_st,
                                      "unconditional": uncond_st, "oos": oos_st}
    first_study_bar = next(b for b in aligned if b.date >= analysis_start)
    hold = aligned[-1].close / first_study_bar.close - 1
    report += ["", f"无条件全期持有（研究区间首个收盘至末日收盘，未计分红和成本）：{fmt(hold)}。定期买入基准每隔 {event_gap} 个交易日开始一笔；其日期与信号事件未匹配，比较仅供参考。",
               f"样本外阶段自 {aligned[cutoff].date} 起；规则参数在全期固定，样本外统计属于时间后验检验。", "",
               "## 当日状态", "", "最后一个可用交易日的规则明细见 signals.csv 最后一行。只有 `trigger=True` 才是规则触发；若数据最后日期早于请求日期，结论是“未能确认”，不是“未触发”。"]
    write_csv(out / f"{ticker}_signals.csv", signals)
    write_csv(out / f"{ticker}_events.csv", all_events)
    (out / f"{ticker}_report.md").write_text("\n".join(report) + "\n", encoding="utf-8")
    return result


def latest_status(summary, asof, out, source):
    """Write a human-readable one-page answer, with freshness checked per ticker."""
    checked_at = dt.datetime.now(ZoneInfo("Asia/Hong_Kong")).strftime("%Y-%m-%d %H:%M 香港时间")
    records = []
    for ticker, result in summary.items():
        signal = result["last_signal"]
        fresh = result["as_of_data"] == asof.isoformat()
        if not fresh:
            state = "数据待更新"
            action = "无法判断目标日期；可能休市或数据延迟。"
        elif signal["trigger"]:
            state = "止跌候选已触发"
            action = "已满足规则；如执行，最早下一交易日开盘，并先核对仓位风险。"
        else:
            state = "未触发"
            missing = []
            if signal["drawdown"] > -0.06: missing.append("回撤不足 6%")
            if not signal["recovery"]: missing.append("未收复前高或 5 日均线")
            if signal["confirmations"] < 3: missing.append("辅助条件少于 3 项")
            action = "；".join(missing) + "。"
        records.append({"ticker": ticker, "date": result["as_of_data"], "state": state,
                        "drawdown": fmt(signal["drawdown"]), "confirmations": signal["confirmations"],
                        "recovery": signal["recovery"], "action": action,
                        "volume_ok": signal["volume_ok"], "range_ok": signal["range_ok"],
                        "rs_ok": signal["rs_ok"], "market_ok": signal["market_ok"]})

    heading = f"半导体止跌监测｜目标收盘日 {asof}｜检查于 {checked_at}"
    columns = "| 标的 | 数据日期 | 状态 | 回撤 | 收复 | 辅助条件 | 说明 |"
    markdown = [f"# {heading}", "", "只有完整的美股日线才用于判断。", "", columns,
                "|---|---|---|---:|---|---:|---|"]
    for r in records:
        markdown.append(f"| {r['ticker']} | {r['date']} | {r['state']} | {r['drawdown']} | "
                        f"{'是' if r['recovery'] else '否'} | {r['confirmations']}/4 | {r['action']} |")
    markdown += ["", "辅助条件：成交量、ATR 波幅、相对 SPY 强度、SPY 市场状态，须满足至少三项。",
                 "详细历史统计见各标的 report.md；当前状态不等于未来上涨概率。",
                 "", f"本次数据源：{source}；仅供研究。"]
    (out / "latest_status.md").write_text("\n".join(markdown) + "\n", encoding="utf-8")

    def cell(value): return html.escape(str(value))
    html_rows = []
    for r in records:
        badge = "yes" if r["state"] == "止跌候选已触发" else "wait" if r["state"] == "数据待更新" else "no"
        html_rows.append("<tr>" + "".join([
            f"<th>{cell(r['ticker'])}</th>", f"<td>{cell(r['date'])}</td>",
            f"<td><span class='badge {badge}'>{cell(r['state'])}</span></td>",
            f"<td>{cell(r['drawdown'])}</td>", f"<td>{'是' if r['recovery'] else '否'}</td>",
            f"<td>{r['confirmations']}/4</td>", f"<td>{cell(r['action'])}</td>"]) + "</tr>")
    document = f"""<!doctype html><html lang="zh-Hans"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>半导体止跌监测</title>
<style>body{{font:16px/1.55 -apple-system,BlinkMacSystemFont,Arial,sans-serif;background:#f4f7fa;color:#17222d;margin:0}}
main{{max-width:1060px;margin:48px auto;padding:0 22px}}h1{{font-size:28px;margin:0 0 8px}}
.muted{{color:#5b6b7b}}.card{{background:white;border-radius:15px;padding:24px;margin:26px 0;box-shadow:0 3px 14px #142b4012;overflow:auto}}
table{{width:100%;border-collapse:collapse;min-width:820px;text-align:left}}th,td{{padding:13px 10px;border-bottom:1px solid #e7edf2;vertical-align:top}}
.badge{{display:inline-block;border-radius:6px;padding:2px 8px;white-space:nowrap;font-weight:600}}.yes{{background:#d8f2e3;color:#076436}}
.no{{background:#edf1f4;color:#435364}}.wait{{background:#fff0cb;color:#805400}}a{{color:#245ba8}}</style></head>
<body><main><h1>半导体止跌监测</h1><p class="muted">目标收盘日 {cell(asof)} · 检查于 {cell(checked_at)}</p>
<div class="card"><table><thead><tr><th>标的</th><th>数据日期</th><th>状态</th><th>回撤</th><th>收复</th><th>辅助条件</th><th>说明</th></tr></thead>
<tbody>{''.join(html_rows)}</tbody></table></div>
<p>辅助条件包括成交量、ATR 波幅、相对 SPY 强度、SPY 市场状态，至少须满足三项。</p>
<p class="muted">本次数据源：{cell(source)}。只使用完整的美股日线。信号是规则判定，并非未来上涨概率。详细统计请查看同目录的各标的回测报告。</p>
</main></body></html>"""
    (out / "latest_status.html").write_text(document, encoding="utf-8")
    return records


def main():
    p = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    p.add_argument("--tickers", default="SOXX,LRCX,MU,SMH")
    p.add_argument("--start", help="Study start; default is five years before the latest completed US session")
    p.add_argument("--end", help="Requested end date; automatically capped at the latest completed US session")
    p.add_argument("--out", default=str(SCRIPT_DIR / "backtest_output"))
    p.add_argument("--event-gap", type=int, default=60)
    p.add_argument("--oos-split", type=float, default=.60)
    p.add_argument("--cost-bps-one-way", type=float, default=5.0, help="Cost/slippage per buy or sell, deducted from all event returns")
    p.add_argument("--csv-dir", help="Optional folder: SOXX.csv, LRCX.csv, MU.csv, SMH.csv, SPY.csv")
    p.add_argument("--insecure-public-data", action="store_true", help="Only if this Python lacks CA certificates; disables TLS certificate verification for Yahoo public data")
    args = p.parse_args()
    completed = last_completed_us_date()
    requested_end = dt.date.fromisoformat(args.end) if args.end else completed
    end = previous_weekday(min(requested_end, completed))
    analysis_start = dt.date.fromisoformat(args.start) if args.start else end - dt.timedelta(days=365*5)
    fetch_start = analysis_start - dt.timedelta(days=45)
    if analysis_start >= end: p.error("study start must be before the last completed US trading day")
    if args.event_gap < max(HORIZONS) or not 0 < args.oos_split < 1 or not 0 <= args.cost_bps_one_way < 10000:
        p.error("event-gap must be >=60; oos-split must be 0..1; cost must be 0..9999 bps")
    if args.end and requested_end != end:
        print(f"请求截止 {requested_end}；为避免未收盘日线，仅计算至 {end}。")
    output = Path(args.out); output.mkdir(parents=True, exist_ok=True); data = {}
    tickers = list(dict.fromkeys(t.strip().upper() for t in args.tickers.split(",") if t.strip()))
    if not tickers: p.error("at least one ticker is required")
    for ticker in list(dict.fromkeys([*tickers, "SPY"])):
        try:
            bars = csv_bars(Path(args.csv_dir) / f"{ticker}.csv") if args.csv_dir else yahoo_bars(ticker, fetch_start, end, args.insecure_public_data)
            data[ticker] = [b for b in bars if fetch_start <= b.date <= end]
            if len(data[ticker]) < 90:
                raise ValueError("fewer than 90 usable daily bars")
        except (OSError, urllib.error.URLError, KeyError, ValueError) as e:
            sys.exit(f"无法获取 {ticker} 数据：{e}。可用 --csv-dir 指向 IBKR 日线导出文件夹。")
        if not args.csv_dir: time.sleep(.25)
    cost = args.cost_bps_one_way / 10000
    try:
        summary = {t: run_one(t, data[t], data["SPY"], output, end, analysis_start,
                              args.event_gap, args.oos_split, cost) for t in tickers}
    except ValueError as exc:
        sys.exit(str(exc))
    (output / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    records = latest_status(summary, end, output, "IBKR CSV" if args.csv_dir else "Yahoo Finance 公共日线")
    print(f"\n止跌监测（目标收盘日 {end}）：")
    for r in records:
        print(f"  {r['ticker']:4s} {r['date']}  {r['state']}  — {r['action']}")
    print(f"\n可直接打开：{(output / 'latest_status.html').resolve()}")

if __name__ == "__main__": main()
