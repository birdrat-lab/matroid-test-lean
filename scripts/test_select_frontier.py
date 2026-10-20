#!/usr/bin/env python3
"""Sanity tests against the checked-in repository ledgers.

Run: python3 -m unittest discover -s scripts -p 'test_select_frontier.py'
"""
import unittest
import csv
import tempfile
from pathlib import Path
from select_frontier import Planner, ATTEMPT_FIELDS, load_attempts

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

    def test_run_local_defer_excludes_node_without_completing_it(self):
        p = self.planner
        first = p.rank_batch(size=2, beam_width=40, top=1)
        self.assertTrue(first)
        blocked = first[0][0][0]
        self.assertIn(blocked, p.remaining)
        filtered = p.rank_batch(size=2, beam_width=40, top=5, deferred={blocked})
        self.assertTrue(filtered)
        for seq, metrics in filtered:
            self.assertNotIn(blocked, seq)
            available = set(p.ready)
            for nid in seq:
                self.assertTrue(p.preds[nid] <= available)
                available.add(nid)
        self.assertIn(blocked, p.remaining)
        self.assertIn(blocked, p.eligible(p.ready))

    def test_run_local_defer_validates_node_ids(self):
        with self.assertRaisesRegex(ValueError, "Unknown deferred node"):
            self.planner.rank_batch(size=2, deferred={"N9999"})

    def test_word_count_is_only_attached_to_located_proofs(self):
        p = self.planner
        self.assertIn('N139', p.word_counts)
        self.assertGreater(p.word_counts['N139'], 20)
        self.assertNotIn('N138', p.word_counts)

    def test_no_snapshot_warnings(self):
        self.assertFalse(self.planner.warnings, self.planner.warnings)


class PersistentAttemptFixtureTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'Matroid').mkdir()
        (self.root / 'Manuscript').mkdir()
        (self.root / 'Manuscript/main.tex').write_text('')
        rows = [
            ('N001', 0, 'COMPLETE', 'KERNEL_PROVED'),
            ('N002', 1, 'PENDING', 'UNRESOLVED'),
            ('N003', 2, 'PENDING', 'UNRESOLVED'),
            ('N004', 1, 'PENDING', 'UNRESOLVED'),
        ]
        ledger = ['| id | group | name | requirement | at | x | scope | provenance | y | status | z |']
        for nid, _, status, _ in rows:
            ledger.append(f'| {nid} | test | {nid} | fixture | `fixture:{nid}` | - | CORE_MATROID | MANUSCRIPT_PROVED | - | {status} | - |')
        (self.root / 'Matroid/LEDGER.md').write_text('\n'.join(ledger) + '\n')
        self.csv('DEPTHS.csv', ['id', 'name', 'depth', 'scope', 'status'],
                 [[nid, nid, depth, 'CORE_MATROID', status] for nid, depth, status, _ in rows])
        self.csv('PROOF_STATUS.csv', ['id', 'trust_status', 'proof_declaration'],
                 [[nid, proof, ''] for nid, _, _, proof in rows])
        self.csv('DEPENDENCY_EDGES.csv', ['source_id', 'target_id'],
                 [['N001', 'N002'], ['N002', 'N003'], ['N001', 'N004']])
        self.csv('SCHEDULER_ESTIMATES.csv', ['id', 'residual_cost', 'confidence', 'reason'], [])
        self.attempts = []
        self.write_attempts()

    def csv(self, name, fields, rows):
        with (self.root / 'Matroid' / name).open('w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(fields)
            writer.writerows(rows)

    def write_attempts(self):
        with (self.root / 'Matroid/SCHEDULER_ATTEMPTS.csv').open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=ATTEMPT_FIELDS)
            writer.writeheader()
            writer.writerows(self.attempts)

    def add(self, batch, node='N002', outcome='SUPPORT_ONLY', blocker='MISSING_CORE',
            kind='ATTEMPT', delta='helper'):
        self.attempts.append(dict(event_id=len(self.attempts)+1, batch_index=batch,
            node_id=node, event_kind=kind, outcome=outcome, blocker_key=blocker,
            blocker_evidence='fixture core goal persists', proof_delta=delta,
            edit_check_groups='0' if kind == 'WAKE' else '1',
            log_reference=f'fixture batch {batch}'))
        self.write_attempts()

    def planner(self):
        return Planner(self.root, self.root / 'Matroid/SCHEDULER_ESTIMATES.csv', False)

    def test_same_blocker_persists_across_restart_and_preserves_math(self):
        self.add(1)
        self.add(2)
        first = self.planner()
        second = self.planner()
        for p in (first, second):
            self.assertEqual(p.cooldowns['N002'].retry_after_batch, 8)
            self.assertIn('N002', p.eligible(p.ready))
            self.assertIn('N002', p.remaining)
            self.assertEqual(p.nodes['N002'].proof_status, 'UNRESOLVED')
            for seq, _ in p.rank_batch(size=2):
                self.assertNotIn('N002', seq)
                ready = set(p.ready)
                for node in seq:
                    self.assertTrue(p.preds[node] <= ready)
                    ready.add(node)
        self.assertNotIn('N003', first.eligible(first.ready))

    def test_support_only_counts_but_core_progress_resets(self):
        self.add(1)
        self.add(2, outcome='CORE_PROGRESS', delta='core goal proved')
        self.add(3)
        self.assertFalse(self.planner().cooldowns)
        self.add(4, outcome='NO_PROGRESS')
        self.assertEqual(self.planner().cooldowns['N002'].retry_after_batch, 10)

    def test_batch_expiry_and_escalating_windows(self):
        self.add(1)
        self.add(2)
        for batch in range(3, 8):
            self.add(batch, node='N004', outcome='CORE_PROGRESS', delta='other goal')
        p = self.planner()
        self.assertEqual(p.last_batch_index, 7)
        self.assertNotIn('N002', p.cooldowns)
        self.assertIn('N002', p.expired_cooldowns)
        self.add(8, outcome='NO_PROGRESS')
        self.assertEqual(self.planner().cooldowns['N002'].retry_after_batch, 19)
        for batch in range(9, 19):
            self.add(batch, node='N004', outcome='CORE_PROGRESS', delta='other goal')
        self.assertNotIn('N002', self.planner().cooldowns)
        self.add(19, outcome='NO_PROGRESS')
        self.assertEqual(self.planner().cooldowns['N002'].retry_after_batch, 35)

    def test_evidence_wake_preserves_history(self):
        self.add(1)
        self.add(2)
        self.add(2, kind='WAKE', outcome='BLOCKER_REMOVED', delta='N001.new_core_route')
        p = self.planner()
        self.assertFalse(p.cooldowns)
        self.assertEqual(len(p.wakes), 1)
        self.assertIn('N002', p.eligible(p.ready))
        self.add(3, outcome='NO_PROGRESS')
        self.assertEqual(self.planner().cooldowns['N002'].retry_after_batch, 14)

    def test_all_cooled_fallback_and_run_local_stop(self):
        self.add(1)
        self.add(1, node='N004')
        self.add(2)
        self.add(2, node='N004')
        p = self.planner()
        ranked = p.rank_batch(size=2)
        self.assertEqual(len(ranked), 1)
        self.assertEqual(ranked[0][0], ('N002',))
        self.assertIn('cooldown_fallback', ranked[0][1])
        self.assertEqual(p.rank_batch(size=2, deferred={'N002', 'N004'}), [])

    def test_malformed_and_contradictory_events(self):
        self.add(1)
        self.attempts[0]['edit_check_groups'] = 'fabricated'
        self.write_attempts()
        with self.assertRaisesRegex(ValueError, 'edit/check'):
            load_attempts(self.root / 'Matroid/SCHEDULER_ATTEMPTS.csv')
        self.attempts[0]['edit_check_groups'] = '1'
        self.add(1, kind='WAKE', outcome='BLOCKER_REMOVED', delta='N001.unrelated')
        with self.assertRaisesRegex(ValueError, 'Contradictory WAKE'):
            self.planner()

    def test_missing_batch_index_rejected(self):
        self.add(1)
        self.add(3, node='N004')
        with self.assertRaisesRegex(ValueError, 'Missing attempted batch'):
            self.planner()


if __name__ == '__main__':
    unittest.main()
