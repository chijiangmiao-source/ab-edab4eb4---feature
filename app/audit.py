"""独立依据容量审计 (Independent Basis Capacity Audit)。

安全员对一个 *当前仍有效* 的结论发起审计时, 系统在 **同一读取快照** 上:

1. 枚举该结论当前有效的全部 **完整复算依据** —— 每套依据是一棵展开到
   事实层的推导树, 记录其所含 **原始事实集合** 与 **规则链**
   (结论标识只是中间节点, 绝不当作独立事实计入);
2. **精确** 求解最多有多少套依据两两不共享原始事实 (最大不交集族,
   maximum set packing) —— 共享前提、汇合下游与多条替代支持同时存在时
   也不退化为按单条依据贪心挑选;
3. 按稳定规则 (依据规范序 + 字典序最小标识序列) 裁决出 **唯一** 一组依据,
   连同容量、每套依据的事实与规则链一并返回.

审计是只读的: 不改动规程、不写库、不覆盖页面已有结论; 目标不存在、
已失效或当前依据规模超出审计上限时, 明确说明原因并拒绝.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple

from .tms import TMS

#: 审计上限默认值: 任一节点可枚举的不同完整依据套数 (可用 AUDIT_MAX_BASES 覆盖)
DEFAULT_MAX_BASES = 256


class AuditError(ValueError):
    """审计无法进行的基类 (只读, 不产生任何副作用)。"""


class UnknownConclusionError(AuditError):
    """审计目标不存在 (或不是规则结论)。"""


class ConclusionInactiveError(AuditError):
    """审计目标当前已失效, 不存在有效依据可审计。"""


class AuditLimitExceededError(AuditError):
    """当前依据规模超出审计上限, 拒绝给出不精确的结果。"""


@dataclass(frozen=True)
class Basis:
    """一套完整复算依据: 原始事实集合 + 规则链 (推导树上全部规则)。"""

    facts: Tuple[str, ...]            # 排序后的原始事实标识
    rules: Tuple[str, ...]            # 排序后的规则标识
    steps: Tuple[Tuple[str, str, Tuple[str, ...]], ...]
    # steps: (rule_id, conclusion, antecedents) 按 rule_id 排序, 完整描述推导树


# --------------------------------------------------------------------------- #
# 枚举: 同一快照上当前有效的全部完整复算依据
# --------------------------------------------------------------------------- #
def _enumerate_bases(tms: TMS, target: str, max_bases: int) -> List["Basis"]:
    nodes = tms.nodes

    def valid(n: str) -> bool:
        st = nodes[n]
        return st.fact_active if st.is_fact else st.status == "active"

    # 1) 从目标沿 *当前有效* 的支持边反向收集相关节点 (只看有效子图)
    reachable: Set[str] = set()
    stack = [target]
    while stack:
        n = stack.pop()
        if n in reachable:
            continue
        reachable.add(n)
        st = nodes[n]
        if st.is_fact:
            continue
        for rid in st.supporting_rules:
            r = tms.rules[rid]
            if all(valid(a) for a in r.antecedents):
                stack.extend(a for a in r.antecedents if a not in reachable)

    # 2) 拓扑序: 事实在前, 结论等待其全部有效前提 (规则图无环, 必然终止)
    preds: Dict[str, Set[str]] = {n: set() for n in reachable}
    for n in reachable:
        st = nodes[n]
        if st.is_fact:
            continue
        for rid in st.supporting_rules:
            r = tms.rules[rid]
            if all(valid(a) for a in r.antecedents):
                preds[n].update(r.antecedents)

    done: Set[str] = set()
    order: List[str] = []
    ready = sorted(n for n in reachable if nodes[n].is_fact)
    while ready:
        n = ready.pop(0)
        if n in done:
            continue
        done.add(n)
        order.append(n)
        for m in sorted(reachable):
            if m not in done and preds[m] <= done:
                ready.append(m)
        ready = sorted(set(ready))
    if len(order) != len(reachable):  # 防御: 依赖图无环, 不应发生
        raise AuditError("依赖图无法拓扑排序, 审计中止")

    # 3) 自底向上枚举每个节点的不同完整依据 (按 (事实集, 规则集) 去重),
    #    任一节点超出审计上限即整体拒绝 —— 截断会使容量不精确.
    bases_by_node: Dict[str, List[Basis]] = {}
    for n in order:
        st = nodes[n]
        if st.is_fact:
            bases_by_node[n] = [Basis(facts=(n,), rules=(), steps=())]
            continue
        seen: Dict[Tuple[Tuple[str, ...], Tuple[str, ...]], Basis] = {}
        for rid in sorted(st.supporting_rules):
            r = tms.rules[rid]
            if not all(valid(a) for a in r.antecedents):
                continue
            # 笛卡尔积组合各前提的依据, 边组合边去边重并检查上限
            combos: Dict[Tuple[Tuple[str, ...], Tuple[str, ...]], Basis] = {
                ((), ()): Basis((), (), ())
            }
            for a in r.antecedents:
                merged: Dict[Tuple[Tuple[str, ...], Tuple[str, ...]], Basis] = {}
                for c in combos.values():
                    for b in bases_by_node[a]:
                        cand = Basis(
                            facts=tuple(sorted(set(c.facts) | set(b.facts))),
                            rules=tuple(sorted(set(c.rules) | set(b.rules))),
                            steps=tuple(sorted(set(c.steps) | set(b.steps))),
                        )
                        sig = (cand.facts, cand.rules)
                        if sig not in merged:
                            merged[sig] = cand
                            if len(merged) > max_bases:
                                raise AuditLimitExceededError(
                                    f"结论 {target!r} 的当前依据规模超出审计上限 "
                                    f"{max_bases}: 枚举中间节点 {a!r} 时已超限, "
                                    "无法给出精确容量"
                                )
                combos = merged
            for b in combos.values():
                cand = Basis(
                    facts=b.facts,
                    rules=tuple(sorted(set(b.rules) | {rid})),
                    steps=tuple(sorted(
                        set(b.steps) | {(rid, r.conclusion, tuple(r.antecedents))}
                    )),
                )
                sig = (cand.facts, cand.rules)
                if sig not in seen:
                    seen[sig] = cand
                    if len(seen) > max_bases:
                        raise AuditLimitExceededError(
                            f"结论 {target!r} 的当前依据规模超出审计上限 "
                            f"{max_bases}: 节点 {n!r} 的不同完整依据已超限, "
                            "无法给出精确容量"
                        )
        bases_by_node[n] = list(seen.values())
    return bases_by_node[target]


# --------------------------------------------------------------------------- #
# 精确求解: 两两不共享原始事实的最大依据套数 (非贪心)
# --------------------------------------------------------------------------- #
def _exact_max_disjoint(bases: List[Basis]) -> Tuple[int, List[int]]:
    """返回 (容量, 字典序最小的下标序列)。

    冲突图: 两套依据共享至少一个原始事实即相邻; 求其补图 (互不相交图) 的
    最大团 (Tomita 分支限界 + 贪心着色上界), 再在全部最优解中按
    "排序后下标序列字典序最小" 这条稳定规则裁决出唯一解.
    """
    k = len(bases)
    if k == 0:
        return 0, []

    conflict = [0] * k
    fact_sets = [set(b.facts) for b in bases]
    for i in range(k):
        for j in range(i + 1, k):
            if fact_sets[i] & fact_sets[j]:
                conflict[i] |= 1 << j
                conflict[j] |= 1 << i
    full = (1 << k) - 1
    disjoint_adj = [full & ~conflict[i] & ~(1 << i) for i in range(k)]

    def color_sort(p: int) -> Tuple[List[int], List[int]]:
        """对互不相交图的诱导子图做贪心着色, 返回顶点序与各色上界。"""
        order: List[int] = []
        bounds: List[int] = []
        uncolored = p
        color = 0
        while uncolored:
            color += 1
            avail = uncolored
            while avail:
                bit = avail & -avail
                v = bit.bit_length() - 1
                order.append(v)
                bounds.append(color)
                uncolored &= ~bit
                avail &= ~bit
                avail &= ~disjoint_adj[v]
        return order, bounds

    cache: Dict[int, int] = {}

    def max_clique(p: int) -> int:
        """p 诱导子图中的最大团大小 = 该子集上的最大不交集族容量。"""
        if p in cache:
            return cache[p]
        best = 0

        def expand(r_size: int, cand: int) -> None:
            nonlocal best
            if not cand:
                if r_size > best:
                    best = r_size
                return
            order, bounds = color_sort(cand)
            for idx in range(len(order) - 1, -1, -1):
                if r_size + bounds[idx] <= best:
                    return
                v = order[idx]
                expand(r_size + 1, cand & disjoint_adj[v])
                cand &= ~(1 << v)

        expand(0, p)
        cache[p] = best
        return best

    capacity = max_clique(full)

    # 稳定裁决: 逐位贪心构造字典序最小的下标序列, 每位都验证仍可补全到
    # 最优容量 —— 这是确定性规则, 与枚举顺序无关.
    chosen: List[int] = []
    allowed = full
    lo = 0
    for pos in range(capacity):
        need = capacity - pos
        for v in range(lo, k):
            if not (allowed >> v) & 1:
                continue
            sub = allowed & disjoint_adj[v] & ~((1 << (v + 1)) - 1)
            if max_clique(sub) >= need - 1:
                chosen.append(v)
                allowed = sub
                lo = v + 1
                break
    return capacity, chosen


# --------------------------------------------------------------------------- #
# 入口
# --------------------------------------------------------------------------- #
def run_audit(tms: TMS, target: str, max_bases: Optional[int] = None) -> dict:
    """在同一读取快照上审计 ``target`` 结论的独立依据容量 (只读)。

    返回容量、按稳定规则裁决的唯一一组依据 (含每套事实与规则链);
    目标不存在/已失效/依据规模超限时抛出对应 AuditError 子类.
    """
    max_bases = max(1, int(max_bases)) if max_bases else DEFAULT_MAX_BASES

    st = tms.nodes.get(target)
    if st is None:
        raise UnknownConclusionError(
            f"审计目标 {target!r} 不存在: 规程中没有该结论"
        )
    if st.is_fact:
        raise UnknownConclusionError(
            f"审计目标 {target!r} 是事实而非规则结论, 审计只面向规则结论"
        )
    if st.status != "active":
        raise ConclusionInactiveError(
            f"结论 {target!r} 当前已失效 ({st.reason or '无完整支持'}), "
            "不存在可审计的有效依据"
        )

    bases = _enumerate_bases(tms, target, max_bases)
    # 稳定规范序: (事实集, 规则集) 字典序 -> 依据标识 B1..Bk
    ordered = sorted(bases, key=lambda b: (b.facts, b.rules))
    id_of = {b: f"B{i + 1}" for i, b in enumerate(ordered)}

    capacity, chosen = _exact_max_disjoint(ordered)
    picked = [ordered[i] for i in chosen]

    return {
        "conclusion": target,
        "capacity": capacity,
        "total_bases": len(ordered),
        "limit": max_bases,
        "basis_ids": [id_of[b] for b in picked],
        "bases": [
            {
                "id": id_of[b],
                "facts": list(b.facts),
                "rule_chain": [
                    {"rule_id": rid, "conclusion": concl,
                     "antecedents": list(ants)}
                    for rid, concl, ants in b.steps
                ],
            }
            for b in picked
        ],
    }
