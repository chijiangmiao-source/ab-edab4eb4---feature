#!/usr/bin/env python3
"""API/HTTP 冒烟验证。

默认自起一个真实 HTTP 服务 (子进程, 临时 SQLite), 经真实网络接口验证:

1. 健康检查反映接口可用性;
2. 编辑规程 (唯一事实标识 + 无变量正向规则), 非法规则 (悬空引用/闭环) 被拒绝;
3. 撤回一条原始事实后, 结论凭剩余完整依据保持有效;
4. 撤回最后一条支持事实后, 该结论及仅依赖它的下游结论失效, 且返回传播链;
5. 重复撤回幂等返回既有裁决;
6. 重启服务后结论与依据状态仍保留;
7. 独立依据容量审计: 同一读取快照内精确最大化互不相交依据套数并给出
   唯一裁决序列; 失效/未知目标与超上限规模明确报错; 审计不改动规程,
   修改规程后再次审计只反映新快照。

设置 BASE_URL 时只对既有服务做在线冒烟 (不做重启项, 也不做依赖服务端
环境变量上限的审计上限项)。
退出码: 0 全部通过, 1 有断言失败。
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from typing import Any, Dict, List, Optional

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class Failure(AssertionError):
    pass


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise Failure(msg)
    print(f"  ✓ {msg}")


def request(base: str, method: str, path: str, payload: Optional[dict] = None,
            expect_error: Optional[str] = None) -> Dict[str, Any]:
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(base + path, data=data, method=method,
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            body = json.loads(resp.read().decode("utf-8"))
            if expect_error:
                raise Failure(f"{path} 应被拒绝 ({expect_error}), 但成功了")
            return body
    except urllib.error.HTTPError as e:
        body = json.loads(e.read().decode("utf-8"))
        if expect_error:
            check(body.get("error") == expect_error,
                  f"{path} 返回预期错误码 {expect_error} (实际 {body.get('error')})")
            return body
        raise Failure(f"{path} 意外失败 HTTP {e.code}: {body}") from None


def wait_ready(base: str, timeout: float = 15.0) -> None:
    deadline = time.time() + timeout
    last = ""
    while time.time() < deadline:
        try:
            with urllib.request.urlopen(base + "/api/health", timeout=2) as resp:
                if json.loads(resp.read())["status"] == "ok":
                    return
        except Exception as e:  # noqa: BLE001
            last = str(e)
            time.sleep(0.3)
    raise Failure(f"服务在 {timeout}s 内未就绪: {last}")


def conclusions_map(state: dict) -> Dict[str, dict]:
    return {c["id"]: c for c in state["conclusions"]}


def run_scenario(base: str, check_audit_limit: bool = False) -> None:
    print("[smoke] 1) 健康检查")
    h = request(base, "GET", "/api/health")
    check(h["status"] == "ok" and h["database"] == "ok", "健康检查报告接口与持久层可用")

    print("[smoke] 2) 编辑规程: 两条独立支持路径 + 一个仅依赖结论的下游")
    for f in ("f1", "f2", "f3"):
        request(base, "POST", "/api/facts", {"id": f})
    request(base, "POST", "/api/rules",
            {"id": "r1", "conclusion": "c", "antecedents": ["f1"]})
    request(base, "POST", "/api/rules",
            {"id": "r2", "conclusion": "c", "antecedents": ["f2", "f3"]})
    request(base, "POST", "/api/rules",
            {"id": "r3", "conclusion": "d", "antecedents": ["c"]})

    state = request(base, "GET", "/api/state")
    cs = conclusions_map(state)
    check(cs["c"]["status"] == "active", "初始: 结论 c 有效")
    check({s["rule_id"] for s in cs["c"]["supports"]} == {"r1", "r2"},
          "c 的每次规则触发都保存了完整前提集合 (两条支持)")
    check(cs["d"]["status"] == "active", "初始: 下游 d 有效")

    print("[smoke] 2b) 非法规则必须被拒绝且不污染规程")
    request(base, "POST", "/api/rules",
            {"id": "bad1", "conclusion": "q", "antecedents": ["f1", "ghost"]},
            expect_error="dangling_reference")
    request(base, "POST", "/api/rules",
            {"id": "bad2", "conclusion": "f1", "antecedents": ["f1"]},
            expect_error="invalid_procedure")  # 结论与事实同名
    request(base, "POST", "/api/rules",
            {"id": "r2", "conclusion": "x", "antecedents": ["f1"]},
            expect_error="duplicate_id")
    state = request(base, "GET", "/api/state")
    check(all(c["id"] != "q" for c in state["conclusions"]),
          "被拒绝的悬空规则未污染规程")
    request(base, "POST", "/api/retract", {"fact_id": "ghost"},
            expect_error="unknown_fact")
    # 闭环: e 已由事实 f3 直接/间接定义后再制造环
    request(base, "POST", "/api/rules",
            {"id": "r4", "conclusion": "e", "antecedents": ["f3"]})
    request(base, "POST", "/api/rules",
            {"id": "r5", "conclusion": "g", "antecedents": ["e"]})
    request(base, "POST", "/api/rules",
            {"id": "r6", "conclusion": "e", "antecedents": ["g"]},
            expect_error="cyclic_rule")

    print("[smoke] 2c) 独立依据容量审计: 同一快照精确最大化互不相交依据套数")
    before = request(base, "GET", "/api/state")
    ac = request(base, "POST", "/api/audit", {"conclusion": "c"})["audit"]
    check(ac["conclusion"] == "c" and ac["capacity"] == 2,
          "c 的独立依据容量为 2 (两条支持路径原始事实互不相交)")
    check(ac["total_bases"] == 2, "c 当前完整依据共 2 套")
    check([b["facts"] for b in ac["bases"]] == [["f1"], ["f2", "f3"]],
          "裁决出的一组依据含每套原始事实")
    check([b["rules"] for b in ac["bases"]] == [["r1"], ["r2"]],
          "每套依据含完整规则链")
    check(ac["basis_ids"] == sorted(ac["basis_ids"]) and
          ac["basis_ids"] == [b["id"] for b in ac["bases"]],
          "依据标识序列有序且唯一标识每套依据")
    ad = request(base, "POST", "/api/audit", {"conclusion": "d"})["audit"]
    check(ad["capacity"] == 2 and
          [b["rules"] for b in ad["bases"]] == [["r1", "r3"], ["r2", "r3"]],
          "下游 d 容量为 2: 共享中间结论/规则不计入, 结论标识不是独立事实")
    request(base, "POST", "/api/audit", {"conclusion": "ghost"},
            expect_error="unknown_conclusion")
    request(base, "POST", "/api/audit", {"conclusion": "f1"},
            expect_error="unknown_conclusion")  # 事实不是结论
    after = request(base, "GET", "/api/state")
    check(after["conclusions"] == before["conclusions"] and
          after["facts"] == before["facts"] and
          after["last_verdict"] == before["last_verdict"],
          "审计只读: 不改动规程, 不覆盖已有结论与裁决")

    print("[smoke] 2d) 共享前提与汇合下游的精确容量")
    request(base, "POST", "/api/facts", {"id": "s1"})
    request(base, "POST", "/api/facts", {"id": "s2"})
    request(base, "POST", "/api/facts", {"id": "s3"})
    request(base, "POST", "/api/rules",
            {"id": "rs1", "conclusion": "shared", "antecedents": ["s1", "s2"]})
    request(base, "POST", "/api/rules",
            {"id": "rs2", "conclusion": "shared", "antecedents": ["s1", "s3"]})
    ash = request(base, "POST", "/api/audit", {"conclusion": "shared"})["audit"]
    check(ash["capacity"] == 1 and ash["total_bases"] == 2,
          "两套依据共享原始事实 s1 -> 容量精确为 1 (而非按条数贪心)")
    request(base, "POST", "/api/rules",
            {"id": "rm", "conclusion": "m", "antecedents": ["s2"]})
    request(base, "POST", "/api/rules",
            {"id": "rn", "conclusion": "n", "antecedents": ["s2"]})
    request(base, "POST", "/api/rules",
            {"id": "rz", "conclusion": "z", "antecedents": ["m", "n"]})
    az = request(base, "POST", "/api/audit", {"conclusion": "z"})["audit"]
    check(az["capacity"] == 1 and az["bases"][0]["facts"] == ["s2"],
          "汇合下游 (菱形) 共享同一原始事实 -> 容量为 1, 依据汇合为 {s2}")
    check(az["bases"][0]["rules"] == ["rm", "rn", "rz"],
          "汇合依据的规则链完整记录三条规则")

    print("[smoke] 3) 撤回一条原始事实 -> 结论凭替代依据保留")
    out = request(base, "POST", "/api/retract", {"fact_id": "f1"})
    v = out["verdict"]
    cs = conclusions_map(out["state"])
    check(cs["c"]["status"] == "active", "撤回 f1 后 c 仍有效 (替代依据)")
    check(cs["d"]["status"] == "active", "撤回 f1 后下游 d 仍有效")
    check(v["survived"] == ["c"], "裁决列出靠替代依据保留的结论 c")
    remaining = cs["c"]["supports"]
    check(len(remaining) == 1 and remaining[0]["rule_id"] == "r2",
          "页面/接口列出剩余的完整支持 r2")
    check(remaining[0]["basis"] == ["f2", "f3"],
          "剩余依据完整可复算: {f2, f3}")
    check(cs["d"]["supports"][0]["basis"] == ["f2", "f3"],
          "下游 d 的展开依据同步刷新为 {f2, f3}")
    ac2 = request(base, "POST", "/api/audit", {"conclusion": "c"})["audit"]
    check(ac2["capacity"] == 1 and [b["facts"] for b in ac2["bases"]] == [["f2", "f3"]],
          "修改规程后再次审计: 只显示新快照结果 (容量降为 1, 仅剩 {f2, f3})")

    print("[smoke] 4) 撤回最后一条支持事实 -> 结论与唯一下游失效 + 传播链")
    out = request(base, "POST", "/api/retract", {"fact_id": "f2"})
    v = out["verdict"]
    cs = conclusions_map(out["state"])
    check(cs["c"]["status"] == "inactive", "撤回 f2 后 c 失效 (支持耗尽)")
    check(cs["d"]["status"] == "inactive", "仅依赖 c 的下游 d 同步失效")
    check([a["node_id"] for a in v["affected"]] == ["f2", "c", "d"],
          "裁决依次列出被撤回事实与受影响结论")
    affected_c = next(a for a in v["affected"] if a["node_id"] == "c")
    check(affected_c["complete_basis"] == ["f2", "f3"],
          "受影响结论 c 附带失效前的完整依据")
    chain = [(s["node_id"], s["triggered_by"], s["rule_id"])
             for s in v["propagation_chain"]]
    check(chain == [("c", "f2", "r2"), ("d", "c", "r3")],
          "展示支持耗尽形成的传播链 f2→c→d")
    check(not cs["c"]["supports"] and not cs["d"]["supports"],
          "失效结论不再有任何当前完整支持")
    check({s["rule_id"] for s in cs["c"]["retired_supports"]} == {"r1", "r2"},
          "两条历史依据均留痕可复算")

    print("[smoke] 4b) 失效结论的容量审计被明确拒绝且不改动规程")
    err = request(base, "POST", "/api/audit", {"conclusion": "c"},
                  expect_error="conclusion_inactive")
    check("已失效" in err["message"], "失效结论审计返回明确原因")
    request(base, "POST", "/api/audit", {"conclusion": "d"},
            expect_error="conclusion_inactive")
    stable = request(base, "GET", "/api/state")
    check(conclusions_map(stable)["c"]["status"] == "inactive",
          "失败的审计不改动规程状态")

    print("[smoke] 5) 重复撤回已失效事实 -> 稳定返回既有裁决")
    again = request(base, "POST", "/api/retract", {"fact_id": "f2"})
    check(again["verdict"]["already_retracted"] is True, "标记为重复撤回 (幂等)")
    chain2 = [(s["node_id"], s["triggered_by"])
              for s in again["verdict"]["propagation_chain"]]
    check(chain2 == [("c", "f2"), ("d", "c")], "稳定返回既有传播链裁决")

    print("[smoke] 6) 页面与单项结论依据接口可经 HTTP 访问")
    with urllib.request.urlopen(base + "/", timeout=5) as resp:
        html = resp.read().decode("utf-8")
    check("安全规程" in html, "GET / 返回页面 HTML")
    detail = request(base, "GET", "/api/conclusions/c")
    check(detail["status"] == "inactive" and not detail["supports"],
          "GET /api/conclusions/c 返回该结论的完整依据状态")

    if check_audit_limit:
        print("[smoke] 6b) 依据规模超出审计上限 -> 明确报错且不改动规程")
        # m 三条支持 × n 三条支持 -> big 有 9 套完整依据, 超出冒烟上限 8
        for i in range(3):
            request(base, "POST", "/api/facts", {"id": f"ba{i}"})
            request(base, "POST", "/api/facts", {"id": f"bb{i}"})
            request(base, "POST", "/api/rules",
                    {"id": f"rbm{i}", "conclusion": "bm", "antecedents": [f"ba{i}"]})
            request(base, "POST", "/api/rules",
                    {"id": f"rbn{i}", "conclusion": "bn", "antecedents": [f"bb{i}"]})
        request(base, "POST", "/api/rules",
                {"id": "rbb", "conclusion": "big", "antecedents": ["bm", "bn"]})
        err = request(base, "POST", "/api/audit", {"conclusion": "big"},
                      expect_error="audit_limit_exceeded")
        check("max_bases=8" in err["message"],
              "超上限审计明确说明原因 (依据规模 > max_bases=8)")
        stable = request(base, "GET", "/api/state")
        check(conclusions_map(stable)["big"]["status"] == "active",
              "超上限审计失败后规程与结论状态保持不变")


def run_restart_check(port: int, db_path: str) -> None:
    print("[smoke] 7) 重启后查询仍保留结论与依据状态")
    proc, base = start_server(port, db_path)
    try:
        wait_ready(base)
        state = request(base, "GET", "/api/state")
        cs = conclusions_map(state)
        check(cs["c"]["status"] == "inactive" and cs["d"]["status"] == "inactive",
              "重启后 c/d 仍为失效")
        check({s["rule_id"] for s in cs["c"]["retired_supports"]} == {"r1", "r2"},
              "重启后历史完整依据仍保留")
        facts = {f["id"]: f["active"] for f in state["facts"]}
        check(facts["f1"] is False and facts["f2"] is False and facts["f3"] is True,
              "重启后事实撤回状态保留, f3 仍有效")
        again = request(base, "POST", "/api/retract", {"fact_id": "f1"})
        check(again["verdict"]["already_retracted"] is True,
              "重启后重复撤回仍稳定返回既有裁决")
    finally:
        proc.terminate()
        proc.wait(timeout=10)


def start_server(port: int, db_path: str):
    env = dict(os.environ, PORT=str(port), HOST="127.0.0.1",
               DB_PATH=db_path, PYTHONPATH=ROOT, PYTHONUNBUFFERED="1")
    proc = subprocess.Popen(
        [sys.executable, "-m", "app.server"],
        cwd=ROOT, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return proc, f"http://127.0.0.1:{port}"


def main() -> int:
    base_url = os.environ.get("BASE_URL")
    try:
        if base_url:
            print(f"[smoke] 在线模式: {base_url} (要求服务为干净初始状态)")
            wait_ready(base_url)
            run_scenario(base_url)
        else:
            tmp = tempfile.TemporaryDirectory()
            db_path = os.path.join(tmp.name, "smoke.db")
            port = int(os.environ.get("SMOKE_PORT", "8099"))
            # 自起服务时收紧审计上限, 以便冒烟覆盖 "依据规模超出审计上限" 分支
            os.environ["AUDIT_MAX_BASES"] = "8"
            proc, base = start_server(port, db_path)
            try:
                wait_ready(base)
                run_scenario(base, check_audit_limit=True)
            finally:
                proc.terminate()
                proc.wait(timeout=10)
            run_restart_check(port + 1, db_path)
            tmp.cleanup()
    except Failure as e:
        print(f"\n[smoke] 失败: {e}", file=sys.stderr)
        return 1
    except Exception as e:  # noqa: BLE001
        print(f"\n[smoke] 异常: {type(e).__name__}: {e}", file=sys.stderr)
        return 1
    print("\n[smoke] 全部冒烟断言通过 ✔")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
