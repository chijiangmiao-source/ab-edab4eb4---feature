"""独立依据容量审计 (app/audit.py) 测试。

覆盖: 共享前提 / 汇合下游 / 多条替代支持并存时的精确最大化、
结论标识不被当作独立事实、稳定裁决唯一结果、审计上限、失效/未知目标、
审计只读不改规程, 以及与暴力枚举对照的随机化精确性验证。
"""

import itertools
import os
import random
import tempfile
import unittest

from app import audit
from app.audit import (
    AuditLimitExceededError,
    InactiveConclusionError,
    UnknownConclusionError,
)
from app.store import Store
from app.tms import TMS


def build(rules, facts):
    t = TMS()
    for f in facts:
        t.add_fact(f)
    for rid, concl, ants in rules:
        t.add_rule(rid, concl, ants)
    return t


def brute_force_best(bases):
    """暴力枚举所有依据子集, 返回 (最大套数, 字典序最小标识序列)。"""
    best_count, best_ids = 0, ()
    for r in range(len(bases) + 1):
        for combo in itertools.combinations(bases, r):
            seen = set()
            ok = True
            for b in combo:
                if seen & set(b.facts):
                    ok = False
                    break
                seen |= set(b.facts)
            if not ok:
                continue
            ids = tuple(sorted(b.basis_id for b in combo))
            if r > best_count or (r == best_count and (not best_ids or ids < best_ids)):
                best_count, best_ids = r, ids
    return best_count, best_ids


class CapacityTests(unittest.TestCase):
    def test_two_independent_paths_give_capacity_two(self):
        t = build([
            ("r1", "c", ["f1"]),
            ("r2", "c", ["f2", "f3"]),
            ("r3", "d", ["c"]),
        ], ["f1", "f2", "f3"])
        res = audit.audit_basis_capacity(t, "c")
        self.assertEqual(res["capacity"], 2)
        self.assertEqual(res["total_bases"], 2)
        self.assertEqual([b["facts"] for b in res["bases"]], [["f1"], ["f2", "f3"]])
        self.assertEqual([b["rules"] for b in res["bases"]], [["r1"], ["r2"]])
        # 依据标识序列稳定唯一
        self.assertEqual(res["basis_ids"], [b["id"] for b in res["bases"]])
        self.assertEqual(res["basis_ids"], sorted(res["basis_ids"]))
        # 下游结论同样精确: 两套依据共享规则 r3 与中间结论 c, 但原始事实不相交
        res_d = audit.audit_basis_capacity(t, "d")
        self.assertEqual(res_d["capacity"], 2)
        self.assertEqual([b["rules"] for b in res_d["bases"]],
                         [["r1", "r3"], ["r2", "r3"]])

    def test_shared_premise_means_not_disjoint(self):
        t = build([
            ("r1", "c", ["f1", "f2"]),
            ("r2", "c", ["f1", "f3"]),
        ], ["f1", "f2", "f3"])
        res = audit.audit_basis_capacity(t, "c")
        self.assertEqual(res["capacity"], 1)  # 两套依据共享原始事实 f1
        self.assertEqual(res["total_bases"], 2)
        # 稳定裁决: 取标识最小的一套
        self.assertEqual(res["bases"][0]["facts"], ["f1", "f2"])

    def test_converging_downstream_shares_original_fact(self):
        # 汇合下游: m 与 n 都由同一事实 a 推出, z 的依据汇合后只有 {a}
        t = build([
            ("r1", "m", ["a"]),
            ("r2", "n", ["a"]),
            ("r3", "z", ["m", "n"]),
            ("r4", "z", ["b"]),
        ], ["a", "b"])
        res = audit.audit_basis_capacity(t, "z")
        self.assertEqual(res["capacity"], 2)  # {a} 与 {b} 互不相交
        self.assertEqual(sorted(b["facts"] for b in res["bases"]),
                         [["a"], ["b"]])
        # 汇合依据 {a} 的规则链完整记录三条规则
        basis_a = next(b for b in res["bases"] if b["facts"] == ["a"])
        self.assertEqual(basis_a["rules"], ["r1", "r2", "r3"])

    def test_conclusion_id_is_not_treated_as_fact(self):
        # z 的两套依据经过同一个中间结论 m / 同一条规则 r3:
        # 若把结论标识当作独立事实, 容量会被错算为 1
        t = build([
            ("r1", "m", ["a"]),
            ("r2", "m", ["b"]),
            ("r3", "z", ["m"]),
        ], ["a", "b"])
        res = audit.audit_basis_capacity(t, "z")
        self.assertEqual(res["capacity"], 2)
        self.assertEqual(sorted(b["facts"] for b in res["bases"]),
                         [["a"], ["b"]])
        for b in res["bases"]:
            self.assertNotIn("m", b["facts"])
            self.assertNotIn("z", b["facts"])

    def test_exact_maximization_not_greedy(self):
        # 依据 {f2,f3} 会同时堵住 {f1,f2} 与 {f3,f4}: 先挑它只得 1 套,
        # 精确解必须选出 2 套互不相交依据
        t = build([
            ("r1", "c", ["f1", "f2"]),
            ("r2", "c", ["f3", "f4"]),
            ("r3", "c", ["f2", "f3"]),
        ], ["f1", "f2", "f3", "f4"])
        res = audit.audit_basis_capacity(t, "c")
        self.assertEqual(res["capacity"], 2)
        self.assertEqual(sorted(tuple(b["facts"]) for b in res["bases"]),
                         [("f1", "f2"), ("f3", "f4")])

    def test_stable_unique_adjudication_among_tied_optima(self):
        # 两个并列最优: {f1,f2}+{f3,f4} 与 {f1,f4}+{f2,f3};
        # 必须按依据标识序列稳定裁决出唯一结果
        t = build([
            ("r1", "c", ["f1", "f2"]),
            ("r2", "c", ["f2", "f3"]),
            ("r3", "c", ["f3", "f4"]),
            ("r4", "c", ["f1", "f4"]),
        ], ["f1", "f2", "f3", "f4"])
        res1 = audit.audit_basis_capacity(t, "c")
        res2 = audit.audit_basis_capacity(t, "c")
        self.assertEqual(res1["capacity"], 2)
        self.assertEqual(res1["basis_ids"], res2["basis_ids"])  # 唯一稳定
        self.assertEqual(sorted(tuple(b["facts"]) for b in res1["bases"]),
                         [("f1", "f2"), ("f3", "f4")])

    def test_same_facts_different_rule_chains_deduplicated(self):
        # 同一事实集的两条规则链: 对容量等价, 稳定保留标识最小的一套
        t = build([
            ("r1", "c", ["f1"]),
            ("r2", "c", ["f1"]),
            ("r3", "c", ["f2"]),
        ], ["f1", "f2"])
        res = audit.audit_basis_capacity(t, "c")
        self.assertEqual(res["total_bases"], 2)  # 按事实集去重
        self.assertEqual(res["capacity"], 2)
        basis_f1 = next(b for b in res["bases"] if b["facts"] == ["f1"])
        self.assertEqual(basis_f1["rules"], ["r1"])

    def test_product_bases_capacity(self):
        # m 三条支持, n 三条支持, z :- m, n -> 9 套组合依据, 容量 3
        rules = [(f"rm{i}", "m", [f"a{i}"]) for i in range(3)]
        rules += [(f"rn{i}", "n", [f"b{i}"]) for i in range(3)]
        rules += [("rz", "z", ["m", "n"])]
        facts = [f"a{i}" for i in range(3)] + [f"b{i}" for i in range(3)]
        t = build(rules, facts)
        res = audit.audit_basis_capacity(t, "z")
        self.assertEqual(res["total_bases"], 9)
        self.assertEqual(res["capacity"], 3)
        for b in res["bases"]:
            self.assertEqual(len(b["rules"]), 3)  # rm? + rn? + rz
            self.assertEqual(b["rules"], sorted(b["rules"]))
            self.assertIn("rz", b["rules"])


class LimitTests(unittest.TestCase):
    def _product_tms(self, k):
        rules = [(f"rm{i}", "m", [f"a{i}"]) for i in range(k)]
        rules += [(f"rn{i}", "n", [f"b{i}"]) for i in range(k)]
        rules += [("rz", "z", ["m", "n"])]
        facts = [f"a{i}" for i in range(k)] + [f"b{i}" for i in range(k)]
        return build(rules, facts)

    def test_bases_limit_exceeded(self):
        t = self._product_tms(3)  # z 有 9 套完整依据
        with self.assertRaises(AuditLimitExceededError) as ctx:
            audit.audit_basis_capacity(t, "z", max_bases=8)
        self.assertIn("max_bases=8", str(ctx.exception))
        # 放宽上限则精确求解成功
        res = audit.audit_basis_capacity(t, "z", max_bases=16)
        self.assertEqual(res["capacity"], 3)

    def test_facts_limit_exceeded(self):
        t = build([("r1", "c", ["f1"]), ("r2", "c", ["f2"]), ("r3", "c", ["f3"])],
                  ["f1", "f2", "f3"])
        with self.assertRaises(AuditLimitExceededError) as ctx:
            audit.audit_basis_capacity(t, "c", max_facts=2)
        self.assertIn("max_facts=2", str(ctx.exception))


class TargetValidationTests(unittest.TestCase):
    def test_unknown_conclusion_rejected(self):
        t = build([("r1", "c", ["f1"])], ["f1"])
        with self.assertRaises(UnknownConclusionError):
            audit.audit_basis_capacity(t, "ghost")
        with self.assertRaises(UnknownConclusionError):
            audit.audit_basis_capacity(t, "")
        # 事实标识不是结论, 不能作为审计目标
        with self.assertRaises(UnknownConclusionError):
            audit.audit_basis_capacity(t, "f1")

    def test_inactive_conclusion_rejected(self):
        t = build([("r1", "c", ["f1"]), ("r2", "d", ["c"])], ["f1"])
        t.retract("f1")
        with self.assertRaises(InactiveConclusionError) as ctx:
            audit.audit_basis_capacity(t, "c")
        self.assertIn("已失效", str(ctx.exception))
        with self.assertRaises(InactiveConclusionError):
            audit.audit_basis_capacity(t, "d")


class ReadOnlyTests(unittest.TestCase):
    def test_audit_does_not_mutate_procedure(self):
        t = build([
            ("r1", "c", ["f1"]),
            ("r2", "c", ["f2", "f3"]),
            ("r3", "d", ["c"]),
        ], ["f1", "f2", "f3"])
        before = t.snapshot()
        audit.audit_basis_capacity(t, "c")
        audit.audit_basis_capacity(t, "d")
        self.assertEqual(t.snapshot(), before)
        # 失败的审计同样不改动规程
        t.retract("f1")
        before = t.snapshot()
        with self.assertRaises(AuditLimitExceededError):
            audit.audit_basis_capacity(t, "c", max_bases=0)
        self.assertEqual(t.snapshot(), before)

    def test_reaudit_after_modification_reflects_new_snapshot(self):
        t = build([
            ("r1", "c", ["f1"]),
            ("r2", "c", ["f2", "f3"]),
        ], ["f1", "f2", "f3"])
        self.assertEqual(audit.audit_basis_capacity(t, "c")["capacity"], 2)
        t.retract("f1")  # 修改规程后再次审计: 只反映新快照
        res = audit.audit_basis_capacity(t, "c")
        self.assertEqual(res["capacity"], 1)
        self.assertEqual([b["facts"] for b in res["bases"]], [["f2", "f3"]])
        t.retract("f2")
        with self.assertRaises(InactiveConclusionError):
            audit.audit_basis_capacity(t, "c")


class StoreIntegrationTests(unittest.TestCase):
    def test_store_audit_is_read_only_and_survives_restart(self):
        tmp = tempfile.TemporaryDirectory()
        db = os.path.join(tmp.name, "audit.db")
        store = Store(db)
        for f in ("f1", "f2", "f3"):
            store.add_fact(f)
        store.add_rule("r1", "c", ["f1"])
        store.add_rule("r2", "c", ["f2", "f3"])
        res = store.audit_conclusion("c")
        self.assertEqual(res["capacity"], 2)
        self.assertEqual(res["limits"]["max_bases"], audit.DEFAULT_MAX_BASES)
        snap_before = store.snapshot()
        store.audit_conclusion("c")
        self.assertEqual(store.snapshot(), snap_before)  # 审计不落盘
        store.close()

        # 重启后审计按新快照即时重算 (审计结果本身不持久化)
        store2 = Store(db)
        self.assertEqual(store2.audit_conclusion("c")["capacity"], 2)
        store2.retract_fact("f1")
        res2 = store2.audit_conclusion("c")
        self.assertEqual(res2["capacity"], 1)
        store2.close()
        tmp.cleanup()

    def test_store_custom_limits(self):
        tmp = tempfile.TemporaryDirectory()
        store = Store(os.path.join(tmp.name, "x.db"), audit_max_bases=1)
        store.add_fact("f1")
        store.add_fact("f2")
        store.add_rule("r1", "c", ["f1"])
        store.add_rule("r2", "c", ["f2"])
        with self.assertRaises(AuditLimitExceededError):
            store.audit_conclusion("c")
        store.close()
        tmp.cleanup()


class ExactnessPropertyTests(unittest.TestCase):
    """随机无环规程上, 与暴力枚举对照精确容量与唯一裁决序列。"""

    def _random_procedure(self, rng):
        facts = [f"f{i}" for i in range(rng.randint(2, 5))]
        t = TMS()
        for f in facts:
            t.add_fact(f)
        available = list(facts)
        for i in range(rng.randint(1, 7)):
            arity = rng.randint(1, min(3, len(available)))
            ants = rng.sample(available, arity)
            concl = f"c{i}"
            t.add_rule(f"r{i}", concl, ants)
            available.append(concl)
        # 随机撤回部分事实, 制造失效支持与替代路径
        for f in facts:
            if rng.random() < 0.25:
                t.retract(f)
        return t

    def test_matches_brute_force(self):
        rng = random.Random(20260925)
        checked = 0
        for _ in range(60):
            t = self._random_procedure(rng)
            for node, st in t.nodes.items():
                if st.is_fact or st.status != "active":
                    continue
                res = audit.audit_basis_capacity(t, node)
                raw = audit._enumerate_bases(t, node, audit.DEFAULT_MAX_BASES)
                dedup = {}
                for facts, rules in raw:
                    bid = audit._basis_id(facts, rules)
                    if facts not in dedup or bid < dedup[facts][0]:
                        dedup[facts] = (bid, rules)
                bases = [audit.Basis(bid, tuple(sorted(facts)), tuple(sorted(rules)))
                         for facts, (bid, rules) in dedup.items()]
                exp_count, exp_ids = brute_force_best(bases)
                self.assertEqual(res["capacity"], exp_count,
                                 f"容量不一致: {node}")
                self.assertEqual(tuple(res["basis_ids"]), exp_ids,
                                 f"裁决序列不唯一/不稳定: {node}")
                checked += 1
        self.assertGreater(checked, 30)  # 确保真的覆盖了足够多的有效结论


if __name__ == "__main__":
    unittest.main(verbosity=2)
