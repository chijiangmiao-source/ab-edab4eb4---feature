"""独立依据容量审计 (independent basis capacity audit).

安全员对一个 *当前仍有效* 的结论发起审计时, 本模块在 **同一读取快照** 内
(由 store 层持锁保证) 完成三件事:

1. **提取当前有效的完整依据**: 沿规则依赖自底向上枚举该结论此刻成立的
   所有完整复算依据 —— 每套依据 = (原始事实集合, 规则链). 只含事实标识,
   结论标识绝不作为独立事实计入 (两套依据可以经过同一个中间结论 / 同一条
   下游规则, 只要原始事实不相交就算彼此独立).
2. **精确最大化互不相交的依据套数**: 在共享前提、汇合下游 (菱形依赖) 与
   多条替代支持同时存在时, 用对事实子集的动态规划求 **最大套装填**
   (maximum set packing) 的精确解 —— 不按单条依据贪心挑选.
3. **稳定裁决唯一结果**: 事实集相同的依据只保留标识最小的一套; 在所有
   达到最大套数的方案中, 取按依据标识排序后字典序最小的一组, 并以
   依据标识序列给出唯一结果.

审计上限: 完整依据套数超过 ``max_bases`` 或涉及的原始事实数超过
``max_facts`` 时, 抛出 :class:`AuditLimitExceededError`, 明确说明原因.
审计全程只读, 不改动规程, 也不触碰页面已有结论与裁决展示.
"""

from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Tuple

from .tms import TMS

# 审计上限默认值 (可被 Store/环境变量覆盖): 保证精确求解始终有界
DEFAULT_MAX_BASES = 128
DEFAULT_MAX_FACTS = 16


# --------------------------------------------------------------------------- #
# 错误类型
# --------------------------------------------------------------------------- #
class AuditError(ValueError):
    """审计请求的基类错误 (目标非法或规模超限)。"""


class UnknownConclusionError(AuditError):
    """审计目标不存在 (或目标是事实而非规则结论)。"""


class InactiveConclusionError(AuditError):
    """审计目标已失效: 只有当前有效的结论才能发起容量审计。"""


class AuditLimitExceededError(AuditError):
    """当前依据规模超出审计上限, 无法在有界时间内给出精确结果。"""


# --------------------------------------------------------------------------- #
# 数据结构
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class Basis:
    """一套完整复算依据: 原始事实集合 + 推出结论所用的规则链。"""

    basis_id: str               # 稳定唯一标识 (由事实集与规则链导出)
    facts: Tuple[str, ...]      # 排序后的原始事实标识
    rules: Tuple[str, ...]      # 排序后的规则链标识


def _basis_id(facts: FrozenSet[str], rules: FrozenSet[str]) -> str:
    """由 (事实集, 规则链) 导出稳定且唯一的依据标识。

    两侧分别用 JSON 数组序列化 (字符串被转义/引用), 即使标识本身含有
    分隔字符也不会发生碰撞; 字典序即稳定裁决顺序。
    """
    def dump(xs: FrozenSet[str]) -> str:
        return json.dumps(sorted(xs), ensure_ascii=False, separators=(",", ":"))
    return f"{dump(facts)}#{dump(rules)}"


# --------------------------------------------------------------------------- #
# 审计主流程
# --------------------------------------------------------------------------- #
def audit_basis_capacity(
    tms: TMS,
    conclusion: str,
    *,
    max_bases: int = DEFAULT_MAX_BASES,
    max_facts: int = DEFAULT_MAX_FACTS,
) -> dict:
    """对当前有效的结论做独立依据容量审计 (纯只读, 不修改引擎状态)。

    返回字典包含: 目标结论、容量 (互不相交依据的最大套数)、按稳定规则
    裁决出的一组依据 (每套含事实与规则链)、依据标识序列、当前完整依据
    总套数与审计上限。
    """
    node = (conclusion or "").strip()
    st = tms.nodes.get(node)
    if not node or st is None or st.is_fact:
        raise UnknownConclusionError(
            f"审计目标 {node or '(空)'!r} 不存在: 它不是当前规程中的规则结论")
    if st.status != "active" or not st.supports:
        raise InactiveConclusionError(
            f"结论 {node!r} 已失效 ({st.reason or '无当前完整支持'}), "
            "只有仍有效的结论才能发起独立依据容量审计")

    raw = _enumerate_bases(tms, node, max_bases)

    # 稳定裁决第一步: 事实集相同的依据等价 (对容量而言), 只保留标识最小的一套
    best_by_facts: Dict[FrozenSet[str], Tuple[str, FrozenSet[str]]] = {}
    for facts, rules in raw:
        bid = _basis_id(facts, rules)
        kept = best_by_facts.get(facts)
        if kept is None or bid < kept[0]:
            best_by_facts[facts] = (bid, rules)

    bases: List[Basis] = sorted(
        (Basis(bid, tuple(sorted(facts)), tuple(sorted(rules)))
         for facts, (bid, rules) in best_by_facts.items()),
        key=lambda b: b.basis_id,
    )

    all_facts = sorted({f for b in bases for f in b.facts})
    if len(all_facts) > max_facts:
        raise AuditLimitExceededError(
            f"结论 {node!r} 的完整依据涉及 {len(all_facts)} 个原始事实, "
            f"超出审计上限 max_facts={max_facts}, 无法给出精确容量")

    chosen = _max_disjoint_packing(bases, all_facts)
    return {
        "conclusion": node,
        "status": "active",
        "capacity": len(chosen),
        "total_bases": len(bases),
        "enumerated_bases": len(raw),
        "bases": [
            {"id": b.basis_id, "facts": list(b.facts), "rules": list(b.rules)}
            for b in chosen
        ],
        "basis_ids": [b.basis_id for b in chosen],
        "limits": {"max_bases": max_bases, "max_facts": max_facts},
    }


# --------------------------------------------------------------------------- #
# 1) 枚举当前有效的完整依据 (事实集 + 规则链)
# --------------------------------------------------------------------------- #
def _enumerate_bases(
    tms: TMS, target: str, max_bases: int
) -> List[Tuple[FrozenSet[str], FrozenSet[str]]]:
    """自底向上枚举目标结论此刻成立的全部完整依据。

    只沿 *当前全部前提有效* 的规则递归; 事实贡献其自身, 结论贡献其各条
    有效规则前提依据的笛卡尔组合. 规则图无环 (加入时已校验), 递归必终止;
    沿有效路径中间节点的依据数不超过目标结论, 故按节点截断即等价于
    按目标结论的依据规模截断。
    """
    memo: Dict[str, List[Tuple[FrozenSet[str], FrozenSet[str]]]] = {}

    def enum(node: str) -> List[Tuple[FrozenSet[str], FrozenSet[str]]]:
        if node in memo:
            return memo[node]
        st = tms.nodes[node]
        if st.is_fact:
            memo[node] = [(frozenset((node,)), frozenset())]
            return memo[node]
        out: List[Tuple[FrozenSet[str], FrozenSet[str]]] = []
        for rule_id in st.supporting_rules:
            rule = tms.rules[rule_id]
            if not all(tms._is_active_now(a) for a in rule.antecedents):
                continue  # 该规则当前未触发, 不贡献依据
            per_ant = [enum(a) for a in rule.antecedents]
            for combo in itertools.product(*per_ant):
                facts = frozenset().union(*(c[0] for c in combo))
                rules = frozenset((rule_id,)).union(*(c[1] for c in combo))
                out.append((facts, rules))
                if len(out) > max_bases:
                    raise AuditLimitExceededError(
                        f"结论 {target!r} 的当前完整依据超过审计上限 "
                        f"max_bases={max_bases} 套, 无法给出精确容量")
        memo[node] = out
        return out

    return enum(target)


# --------------------------------------------------------------------------- #
# 2)+3) 精确最大套装填 + 稳定裁决唯一结果
# --------------------------------------------------------------------------- #
def _max_disjoint_packing(bases: List[Basis], all_facts: List[str]) -> List[Basis]:
    """求互不相交 (事实集两两不交) 依据的最大套数, 并给出唯一裁决。

    对事实子集做动态规划 (精确解, 非贪心): ``best[mask]`` 是在 mask 内
    能选出的 (最大套数, 字典序最小的标识序列). 标识序列按升序保存,
    逐位比较即稳定裁决规则; 可以证明局部最优合成全局最优 (若存在标识
    序列更小的同规模方案, 归并后必得到更小的整体序列, 矛盾)。
    """
    bit = {f: i for i, f in enumerate(all_facts)}
    masks = [sum(1 << bit[f] for f in b.facts) for b in bases]
    ids = [b.basis_id for b in bases]

    best: List[Tuple[int, Tuple[str, ...]]] = [(0, ())] * (1 << len(all_facts))
    for mask in range(1, 1 << len(all_facts)):
        top_count, top_ids = 0, ()
        for bmask, bid in zip(masks, ids):
            if mask & bmask != bmask:
                continue
            prev_count, prev_ids = best[mask ^ bmask]
            cand_ids = tuple(sorted(prev_ids + (bid,)))
            cand_count = prev_count + 1
            if cand_count > top_count or (cand_count == top_count and cand_ids < top_ids):
                top_count, top_ids = cand_count, cand_ids
        best[mask] = (top_count, top_ids)

    chosen_ids = set(best[(1 << len(all_facts)) - 1][1])
    return [b for b in bases if b.basis_id in chosen_ids]
