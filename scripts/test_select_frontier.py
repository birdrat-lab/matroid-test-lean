#!/usr/bin/env python3
"""Sanity tests against the checked-in repository ledgers.

Run: python3 -m unittest discover -s scripts -p 'test_select_frontier.py'
"""
import unittest
from pathlib import Path
from select_frontier import Planner

ROOT = Path(__file__).resolve().parent.parent


class SchedulerRepositoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.planner = Planner(ROOT, ROOT / 'Matroid/SCHEDULER_ESTIMATES.csv', True)

    def test_graph_acyclic_and_topological(self):
        p = self.planner
        self.assertEqual(len(p.order), len(p.nodes))
        ranks = {n:i for i,n in enumerate(p.order)}
        for a in p.nodes:
            for b in p.succs[a]:
                self.assertLess(ranks[a], ranks[b], (a,b))

    def test_cited_available_not_kernel_proved(self):
        p = self.planner
        for nid in p.cited:
            self.assertIn(nid, p.ready)
            self.assertEqual(p.nodes[nid].proof_status, 'CITED_ASSUMPTION')
        self.assertTrue(p.cited.isdisjoint({n for n in p.ready if p.nodes[n].proof_status == 'KERNEL_PROVED'}))

    def test_dynamic_frontier_not_limited_by_minimum_depth(self):
        p = self.planner
        elig = p.eligible(p.ready)
        for nid in elig:
            self.assertTrue(p.preds[nid] <= p.ready)
        # Eligibility is a property of the prerequisites, not of global depth.
        for nid in p.remaining:
            self.assertEqual(nid in elig, p.preds[nid] <= p.ready)
        if 'N138' in p.remaining and p.preds['N138'] <= p.ready:
            self.assertIn('N138', elig)
            if 'N139' in p.remaining:
                self.assertEqual('N139' in p.eligible(p.ready | {'N138'}),
                                 p.preds['N139'] <= p.ready | {'N138'})

    def test_legal_selected_batches(self):
        p = self.planner
        for size in (1,2,3):
            batch = p.rank_batch(size=size, beam_width=40, top=5)
            self.assertTrue(batch)
            for seq, metrics in batch:
                available = set(p.ready)
                for nid in seq:
                    self.assertNotIn(nid, available)
                    self.assertTrue(p.preds[nid] <= available, (nid,seq))
                    available.add(nid)
                self.assertGreater(metrics['score'], 0)

    def test_word_count_is_only_attached_to_located_proofs(self):
        p = self.planner
        self.assertIn('N139', p.word_counts)
        self.assertGreater(p.word_counts['N139'], 20)
        self.assertNotIn('N138', p.word_counts)

    def test_no_snapshot_warnings(self):
        self.assertFalse(self.planner.warnings, self.planner.warnings)


if __name__ == '__main__':
    unittest.main()
