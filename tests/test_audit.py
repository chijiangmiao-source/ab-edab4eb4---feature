"""独立依据容量审计 (app/audit.py) 测试 —— 精确最大化、稳定裁决、只读语义。"""

import os
import tempfile
import unittest

from app.audit import (
    AuditLimitExceededError,
    ConclusionInactiveError,
    UnknownConclusionError,
    run_audit,
)
from app.store import Store
from app.tms import TMS


def integrated_tms():
    """共享前提 + 汇合下游 + 多条替代支持同时存在的规程。

    m :- a (rm1) | m :- b (rm2)   多条替代支持
    n :- s (rn)                   共享前提源
    c :- m, n (rc1)               汇合下游
    c :- p, q (rc2)               替代路径
    """
    t = TMS()
    for f in ("a", "b", "s", "p", "q"):
        t.add_fact(f)
    t.add_rule("rm1", "m", ["a"])
    t.add_rule("rm2", "m", ["b"])
    t.add_rule("rn", "n", ["s"])
    t.add_rule("rc1", "c", ["m", "n"])
    t.add_rule("rc2", "c", ["p", "q"])
    return t


class EnumerationTests(unittest.TestCase):
    def test_converging_downstream_single_basis(self):
        # 汇合下游: m 与 n 都由同一事实 a 推出, c 只有一套依据 {a}
        t = TMS()
        t.add_fact("a")
        t.add_rule("r1", "m", ["a"])
        t.add_rule("r2", "n", ["a"])
        t.add_rule("r3", "c", ["m", "n"])
        rep = run_audit(t, "c")
        self.assertEqual(rep["total_bases"], 1)
        self.assertEqual(rep["capacity"], 1)
        self.assertEqual(rep["bases"][0]["facts"], ["a"])
        self.assertEqual(
            [s["rule_id"] for s in rep["bases"][0]["rule_chain"]],
            ["r1", "r2", "r3"],
        )

    def test_conclusion_ids_never_treated_as_facts(self):
        # 多跳推导: 依据只含原始事实, 中间/目标结论标识不得计入
        t = TMS()
        t.add_fact("f3")
        t.add_rule("r4", "e", ["f3"])
        t.add_rule("r5", "g", ["e"])
        rep = run_audit(t, "g")
        self.assertEqual(rep["bases"][0]["facts"], ["f3"])
        self.assertNotIn("e", rep["bases"][0]["facts"])
        self.assertNotIn("g", rep["bases"][0]["facts"])
        self.assertEqual(
            [s["rule_id"] for s in rep["bases"][0]["rule_chain"]], ["r4", "r5"])

    def test_alternative_supports_multiply_bases(self):
        t = TMS()
        for f in ("a", "b"):
            t.add_fact(f)
        t.add_rule("r1", "m", ["a"])
        t.add_rule("r2", "m", ["b"])
        t.add_rule("r3", "c", ["m"])
        rep = run_audit(t, "c")
        self.assertEqual(rep["total_bases"], 2)
        self.assertEqual(rep["capacity"], 2)  # {a} 与 {b} 不共享事实


class SolverTests(unittest.TestCase):
    def test_shared_premises_conflict(self):
        # 共享前提: {a,b} 与 {b,d} 共享 b, 最多再配 {e,g}
        t = TMS()
        for f in ("a", "b", "d", "e", "g"):
            t.add_fact(f)
        t.add_rule("r1", "c", ["a", "b"])
        t.add_rule("r2", "c", ["b", "d"])
        t.add_rule("r3", "c", ["e", "g"])
        rep = run_audit(t, "c")
        self.assertEqual(rep["total_bases"], 3)
        self.assertEqual(rep["capacity"], 2)
        # 规范序: ('a','b')<('b','d')<('e','g') -> B1,B2,B3; 最优 {B1,B3}/{B2,B3}
        self.assertEqual(rep["basis_ids"], ["B1", "B3"])
        self.assertEqual([b["facts"] for b in rep["bases"]],
                         [["a", "b"], ["e", "g"]])

    def test_exact_maximum_not_single_basis_greedy(self):
        # 依据枚举序第一套是 {a,b}; 按单条依据贪心会得容量 1, 精确解为 2
        t = TMS()
        for f in ("a", "b"):
            t.add_fact(f)
        t.add_rule("r1", "c", ["a", "b"])
        t.add_rule("r2", "c", ["a"])
        t.add_rule("r3", "c", ["b"])
        rep = run_audit(t, "c")
        self.assertEqual(rep["capacity"], 2)
        self.assertEqual(rep["basis_ids"], ["B1", "B3"])  # B1={a}, B2={a,b}, B3={b}
        self.assertEqual([b["facts"] for b in rep["bases"]], [["a"], ["b"]])

    def test_integrated_shared_converged_alternative(self):
        rep = run_audit(integrated_tms(), "c")
        self.assertEqual(rep["total_bases"], 3)
        self.assertEqual(rep["capacity"], 2)
        self.assertEqual(rep["basis_ids"], ["B1", "B3"])
        b1, b3 = rep["bases"]
        self.assertEqual(b1["facts"], ["a", "s"])
        self.assertEqual([s["rule_id"] for s in b1["rule_chain"]],
                         ["rc1", "rm1", "rn"])
        self.assertEqual(b3["facts"], ["p", "q"])
        self.assertEqual([s["rule_id"] for s in b3["rule_chain"]], ["rc2"])

    def test_cycle_of_conflicts_exact(self):
        # 冲突环 {f1,f2}-{f2,f3}-{f3,f4}-{f4,f1}: 最大不交集族为 2
        t = TMS()
        for f in ("f1", "f2", "f3", "f4"):
            t.add_fact(f)
        t.add_rule("r1", "c", ["f1", "f2"])
        t.add_rule("r2", "c", ["f2", "f3"])
        t.add_rule("r3", "c", ["f3", "f4"])
        t.add_rule("r4", "c", ["f4", "f1"])
        rep = run_audit(t, "c")
        self.assertEqual(rep["capacity"], 2)
        # 规范序 B1={f1,f2} B2={f1,f4} B3={f2,f3} B4={f3,f4};
        # 最优族 {B1,B4} 与 {B2,B3}, 字典序最小为 (B1,B4)
        self.assertEqual(rep["basis_ids"], ["B1", "B4"])

    def test_stable_unique_adjudication(self):
        # 同一规程按不同规则加入顺序重建, 裁决结果必须完全一致
        rep1 = run_audit(integrated_tms(), "c")
        t2 = TMS()
        for f in ("q", "p", "s", "b", "a"):
            t2.add_fact(f)
        t2.add_rule("rc2", "c", ["p", "q"])
        t2.add_rule("rn", "n", ["s"])
        t2.add_rule("rm2", "m", ["b"])
        t2.add_rule("rm1", "m", ["a"])
        t2.add_rule("rc1", "c", ["m", "n"])
        rep2 = run_audit(t2, "c")
        self.assertEqual(rep1, rep2)
        # 重复审计结果一致
        self.assertEqual(run_audit(integrated_tms(), "c"), rep1)


class RefusalTests(unittest.TestCase):
    def test_unknown_or_fact_target_rejected(self):
        t = integrated_tms()
        with self.assertRaises(UnknownConclusionError):
            run_audit(t, "ghost")
        with self.assertRaises(UnknownConclusionError):
            run_audit(t, "a")  # 事实不是结论

    def test_inactive_conclusion_rejected_and_state_untouched(self):
        t = integrated_tms()
        t.retract("s")
        t.retract("p")
        self.assertEqual(t.nodes["c"].status, "inactive")
        before = t.snapshot()
        with self.assertRaises(ConclusionInactiveError):
            run_audit(t, "c")
        self.assertEqual(t.snapshot(), before)  # 不改动规程

    def test_limit_exceeded_and_state_untouched(self):
        t = TMS()
        for f in ("x1", "x2", "x3", "x4"):
            t.add_fact(f)
        for i, f in enumerate(("x1", "x2", "x3", "x4")):
            t.add_rule(f"r{i}", "c", [f])
        before = t.snapshot()
        with self.assertRaises(AuditLimitExceededError):
            run_audit(t, "c", max_bases=3)
        self.assertEqual(t.snapshot(), before)  # 超限拒绝不改动规程
        rep = run_audit(t, "c", max_bases=4)    # 上限恰好够用则正常
        self.assertEqual((rep["capacity"], rep["total_bases"]), (4, 4))


class SnapshotTests(unittest.TestCase):
    def test_audit_readonly_and_reflects_only_fresh_snapshot(self):
        t = integrated_tms()
        before = t.snapshot()
        rep1 = run_audit(t, "c")
        self.assertEqual(t.snapshot(), before)  # 审计只读
        self.assertEqual(rep1["capacity"], 2)

        # 修改规程后再次审计: 只显示新快照的结果
        t.add_fact("g2")
        t.add_rule("rc3", "c", ["g2"])
        rep2 = run_audit(t, "c")
        self.assertEqual((rep2["capacity"], rep2["total_bases"]), (3, 4))
        self.assertEqual(rep2["basis_ids"], ["B1", "B3", "B4"])

        # 撤回后再次审计: 同样只反映最新快照
        t.retract("g2")
        rep3 = run_audit(t, "c")
        self.assertEqual((rep3["capacity"], rep3["total_bases"]), (2, 3))
        self.assertEqual(rep3["basis_ids"], ["B1", "B3"])


class StoreAuditTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.db = os.path.join(self.tmp.name, "audit.db")

    def tearDown(self):
        self.tmp.cleanup()

    def _build(self, store: Store):
        for f in ("a", "b", "s", "p", "q"):
            store.add_fact(f)
        store.add_rule("rm1", "m", ["a"])
        store.add_rule("rm2", "m", ["b"])
        store.add_rule("rn", "n", ["s"])
        store.add_rule("rc1", "c", ["m", "n"])
        store.add_rule("rc2", "c", ["p", "q"])

    def test_audit_readonly_and_restart_deterministic(self):
        store = Store(self.db)
        self._build(store)
        rep = store.audit_conclusion("c")
        self.assertEqual((rep["capacity"], rep["total_bases"]), (2, 3))
        self.assertEqual(rep["basis_ids"], ["B1", "B3"])
        # 审计不产生裁决、不改变状态
        self.assertIsNone(store.latest_verdict())
        snap = store.snapshot()
        store.audit_conclusion("c")
        self.assertEqual(store.snapshot(), snap)

        # 审计后撤回行为不变, 再次审计只反映新快照
        rec = store.retract_fact("p")
        self.assertEqual(rec.survived, ["c"])
        rep2 = store.audit_conclusion("c")
        self.assertEqual((rep2["capacity"], rep2["total_bases"]), (1, 2))
        self.assertEqual(rep2["basis_ids"], ["B1"])
        store.close()

        # 重启后审计结果确定一致, 重复撤回仍幂等
        store2 = Store(self.db)
        self.assertEqual(store2.audit_conclusion("c"), rep2)
        again = store2.retract_fact("p")
        self.assertTrue(again.already_retracted)
        store2.close()

    def test_store_limit_and_inactive(self):
        store = Store(self.db)
        self._build(store)
        with self.assertRaises(AuditLimitExceededError):
            store.audit_conclusion("c", max_bases=2)
        store.retract_fact("s")
        store.retract_fact("p")
        with self.assertRaises(ConclusionInactiveError):
            store.audit_conclusion("c")
        store.close()


if __name__ == "__main__":
    unittest.main(verbosity=2)
