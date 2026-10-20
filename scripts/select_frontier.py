#!/usr/bin/env python3
"""Dependency-aware next-batch scheduler for the matroid formalization.

Standard library only. Reads canonical repository data without modifying it.
All costs/weights are heuristic estimates, not observations of token usage.

Use from repository root:
    python3 scripts/select_frontier.py --write Matroid/NEXT_BATCH.md
    python3 scripts/select_frontier.py --json Matroid/NEXT_BATCH.json
"""
from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from collections import defaultdict, deque
import json
import math
from pathlib import Path
import re
import sys

ACTIVE_SCOPES = {"CORE_MATROID", "MATROID_INTERFACE"}
AVAILABLE_TRUST = {"KERNEL_PROVED", "CITED_ASSUMPTION", "CONDITIONAL_PROOF"}
UNSUCCESSFUL_OUTCOMES = {"SUPPORT_ONLY", "NO_PROGRESS"}
ATTEMPT_OUTCOMES = UNSUCCESSFUL_OUTCOMES | {"CLOSED", "CORE_PROGRESS", "INVALID_INTERFACE"}
ATTEMPT_FIELDS = (
    "event_id", "batch_index", "node_id", "event_kind", "outcome",
    "blocker_key", "blocker_evidence", "proof_delta", "edit_check_groups",
    "log_reference",
)
PROVENANCE_VALUE = {
    "MANUSCRIPT_PROVED": 8.0,
    "MANUSCRIPT_DEFINITION": 4.5,
    "MANUSCRIPT_SKETCH": 6.0,
    "MANUSCRIPT_STATEMENT_ONLY": 6.0,
    "CERTIFICATE_DERIVED": 4.5,
    "EXTERNAL_CITED": 1.7,
    "EXTERNAL_UNCITED_STANDARD": 2.5,
    "PROVENANCE_UNRESOLVED": 1.5,
}
BASE_COST = {
    "MANUSCRIPT_PROVED": 3.0,
    "MANUSCRIPT_DEFINITION": 2.0,
    "MANUSCRIPT_SKETCH": 3.0,
    "MANUSCRIPT_STATEMENT_ONLY": 3.0,
    "CERTIFICATE_DERIVED": 3.0,
    "EXTERNAL_CITED": 2.4,  # source verification/label interface; not automatically admitted
    "EXTERNAL_UNCITED_STANDARD": 2.2,
    "PROVENANCE_UNRESOLVED": 3.5,
}


@dataclass(frozen=True)
class Node:
    id: str
    name: str
    depth: int
    scope: str
    ledger_status: str
    provenance: str
    at_label: str
    proof_status: str
    proof_decl: str


@dataclass(frozen=True)
class AttemptEvent:
    event_id: int
    batch_index: int
    node_id: str
    event_kind: str
    outcome: str
    blocker_key: str
    blocker_evidence: str
    proof_delta: str
    edit_check_groups: str
    log_reference: str


@dataclass(frozen=True)
class Cooldown:
    node_id: str
    blocker_key: str
    blocker_evidence: str
    last_attempt_batch: int
    retry_after_batch: int
    level: int
    log_reference: str

    def as_dict(self):
        return {
            "node_id": self.node_id, "blocker_key": self.blocker_key,
            "blocker_evidence": self.blocker_evidence,
            "last_attempt_batch": self.last_attempt_batch,
            "retry_after_batch": self.retry_after_batch,
            "cooldown_batches": min(5 * self.level, 15),
            "log_reference": self.log_reference,
        }


def csv_rows(path: Path):
    with path.open(encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))


def parse_ledger(path: Path):
    rows = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not re.match(r"^\| N\d{3} \|", line):
            continue
        cells = [x.strip() for x in line.strip().strip("|").split("|")]
        if len(cells) < 11:
            raise ValueError(f"Malformed ledger row: {line[:110]}")
        if cells[0] in rows:
            raise ValueError(f"Duplicate ledger ID {cells[0]}")
        rows[cells[0]] = {
            "id": cells[0], "name": cells[2], "requirement": cells[3],
            "at": cells[4], "scope": cells[6], "provenance": cells[7],
            "ledger_status": cells[9],
        }
    if not rows:
        raise ValueError("No N### ledger rows found")
    return rows


def infer_proof_lengths(tex: str, labels: set[str]) -> dict[str, int]:
    """Conservatively pair a labeled theorem-like environment and its adjacent proof.

    Omit labels without an immediately following proof environment. Count TeX
    lexical tokens *approximately*; never use these counts as measurements of
    actual proving cost. We deliberately don't assign the next unrelated proof.
    """
    lengths = {}
    pat = re.compile(r"\\begin\{(theorem|proposition|lemma|corollary)\}(?:\[[^\]]*\])?(.*?)\\end\{\1\}", re.S)
    for m in pat.finditer(tex):
        found = re.findall(r"\\label\{([^}]+)\}", m.group(2))
        matched = [x for x in found if x in labels]
        if not matched:
            continue
        suffix = tex[m.end():m.end()+300]
        # only comments/whitespace between assertion and its proof
        gap = re.match(r"((?:\s|%[^\n]*\n)*)(\\begin\{proof\}(?:\[[^\]]*\])?)", suffix)
        if not gap:
            continue
        start = m.end() + gap.end()
        end = tex.find(r"\end{proof}", start)
        if end < 0:
            continue
        proof = tex[start:end]
        # Strip TeX command names and count words/identifiers; formula tokens
        # are included only as coarse proxies, not an actual semantic parse.
        proof = re.sub(r"(?m)%[^\n]*", " ", proof)
        proof = re.sub(r"\\[a-zA-Z]+\*?", " ", proof)
        count = len(re.findall(r"[\w]+", proof, re.UNICODE))
        for x in matched:
            lengths[x] = count
    return lengths


def load_overrides(path: Path):
    if not path.exists():
        return {}
    result = {}
    for row in csv_rows(path):
        nid = row["id"].strip()
        if nid in result:
            raise ValueError(f"Duplicate estimate override: {nid}")
        cost_s = row.get("residual_cost", "").strip()
        if cost_s:
            cost = float(cost_s)
            if not (cost > 0 and math.isfinite(cost)):
                raise ValueError(f"Bad residual cost override for {nid}")
        else:
            cost = None
        result[nid] = {
            "cost": cost,
            "confidence": row.get("confidence", "unknown").strip(),
            "reason": row.get("reason", "").strip(),
        }
    return result


def load_attempts(path: Path) -> list[AttemptEvent]:
    """Read an append-only, ordered event stream; reject ambiguous histories."""
    if not path.exists():
        return []
    with path.open(encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        if tuple(reader.fieldnames or ()) != ATTEMPT_FIELDS:
            raise ValueError(f"Malformed attempt header in {path}")
        rows = list(reader)
    events = []
    last_id = last_batch = 0
    seen_attempts = set()
    for line, row in enumerate(rows, 2):
        if None in row or any(value is None for value in row.values()):
            raise ValueError(f"Malformed attempt row {line}")
        try:
            event_id = int(row["event_id"])
            batch_index = int(row["batch_index"])
        except ValueError as exc:
            raise ValueError(f"Noninteger attempt event/batch at row {line}") from exc
        if event_id <= last_id or batch_index < 1 or batch_index < last_batch:
            raise ValueError(f"Nonmonotone attempt event/batch at row {line}")
        last_id = event_id
        kind, outcome = row["event_kind"], row["outcome"]
        if kind not in {"ATTEMPT", "WAKE"}:
            raise ValueError(f"Invalid attempt event kind at row {line}")
        groups = row["edit_check_groups"]
        if groups != "UNKNOWN" and not groups.isdecimal():
            raise ValueError(f"Invalid edit/check groups at row {line}")
        if not row["node_id"] or not row["log_reference"]:
            raise ValueError(f"Missing attempt node or evidence link at row {line}")
        if kind == "ATTEMPT":
            if outcome not in ATTEMPT_OUTCOMES:
                raise ValueError(f"Invalid attempt outcome at row {line}")
            if batch_index > last_batch + 1:
                raise ValueError(f"Missing attempted batch index before row {line}")
            key = (batch_index, row["node_id"])
            if key in seen_attempts:
                raise ValueError(f"Duplicate node attempt in batch at row {line}")
            seen_attempts.add(key)
            if outcome != "CLOSED" and not all(
                row[k] for k in ("blocker_key", "blocker_evidence", "proof_delta")
            ):
                raise ValueError(f"Unresolved attempt lacks blocker evidence at row {line}")
            last_batch = batch_index
        else:
            if outcome != "BLOCKER_REMOVED" or groups != "0":
                raise ValueError(f"Invalid WAKE outcome or groups at row {line}")
            if batch_index != last_batch or not all(
                row[k] for k in ("blocker_key", "blocker_evidence", "proof_delta")
            ) or row["proof_delta"] in {"UNKNOWN", row["node_id"]}:
                raise ValueError(f"WAKE lacks independent change evidence at row {line}")
        events.append(AttemptEvent(event_id, batch_index, row["node_id"], kind,
                                   outcome, row["blocker_key"], row["blocker_evidence"],
                                   row["proof_delta"], groups, row["log_reference"]))
    return events


def derive_cooldowns(events: list[AttemptEvent]):
    """Derive cooldowns from events, never from mutable status or cost fields.

    A trigger at batch b with duration d cools batches b+1,...,b+d;
    `retry_after_batch` is b+d+1. Same-blocker failed retries escalate
    from five to ten to at most fifteen subsequent batches.
    """
    state = defaultdict(lambda: {"key": "", "streak": 0, "level": 0,
                                 "cooldown": None, "last_event": None})
    wakes = []
    batch_index = 0
    for e in events:
        st = state[e.node_id]
        if e.event_kind == "WAKE":
            cd = st["cooldown"]
            if (cd is None or cd.blocker_key != e.blocker_key or
                    e.batch_index + 1 >= cd.retry_after_batch):
                raise ValueError(f"Contradictory WAKE event {e.event_id}")
            st["cooldown"] = None
            wakes.append(e)
        else:
            batch_index = max(batch_index, e.batch_index)
            if e.outcome in {"CLOSED", "CORE_PROGRESS", "INVALID_INTERFACE"}:
                st["key"] = e.blocker_key if e.outcome == "INVALID_INTERFACE" else ""
                st["streak"] = 0
                st["level"] = 0
                st["cooldown"] = None
            else:
                if e.blocker_key != st["key"]:
                    st["key"] = e.blocker_key
                    st["streak"] = 0
                    st["level"] = 0
                    st["cooldown"] = None
                st["streak"] += 1
                if st["level"] or st["streak"] >= 2:
                    st["level"] = min(st["level"] + 1, 3)
                    duration = 5 * st["level"]
                    st["cooldown"] = Cooldown(
                        e.node_id, e.blocker_key, e.blocker_evidence,
                        e.batch_index, e.batch_index + duration + 1,
                        st["level"], e.log_reference)
        st["last_event"] = e
    all_cooldowns = {nid: st["cooldown"] for nid, st in state.items()
                     if st["cooldown"] is not None}
    active = {nid: cd for nid, cd in all_cooldowns.items()
              if batch_index + 1 < cd.retry_after_batch}
    return batch_index, active, all_cooldowns, wakes, state


class Planner:
    def __init__(self, root: Path, overrides: Path, word_counts: bool,
                 attempts: Path | None = None):
        self.root = root
        ledger = parse_ledger(root / "Matroid/LEDGER.md")
        depth_rows = csv_rows(root / "Matroid/DEPTHS.csv")
        proof_rows = {r["id"]: r for r in csv_rows(root / "Matroid/PROOF_STATUS.csv")}
        self.nodes = {}
        self.warnings = []
        for r in depth_rows:
            nid = r["id"]
            if r["scope"] not in ACTIVE_SCOPES:
                continue
            if nid not in ledger:
                raise ValueError(f"Active {nid} missing in ledger")
            l = ledger[nid]
            if l["scope"] != r["scope"]:
                self.warnings.append(f"{nid}: ledger/depth scope mismatch")
            if l["ledger_status"] != r["status"]:
                self.warnings.append(f"{nid}: ledger/depth completion mismatch")
            p = proof_rows.get(nid, {})
            ps = p.get("trust_status", "").strip()
            if ps and ps not in AVAILABLE_TRUST | {"UNRESOLVED"}:
                raise ValueError(f"Unexpected proof status {nid}: {ps}")
            if ps == "CITED_ASSUMPTION" and l["ledger_status"] == "COMPLETE":
                self.warnings.append(f"{nid}: cited admission incorrectly ledger COMPLETE")
            if ps == "UNRESOLVED" and l["ledger_status"] == "COMPLETE":
                self.warnings.append(f"{nid}: unresolved proof status conflicts with COMPLETE")
            self.nodes[nid] = Node(
                nid, r["name"], int(r["depth"]), r["scope"],
                r["status"], l["provenance"], l["at"], ps,
                p.get("proof_declaration", ""),
            )
        if len(self.nodes) == 0:
            raise ValueError("No active nodes")
        self.preds = {nid: set() for nid in self.nodes}
        self.succs = {nid: set() for nid in self.nodes}
        for r in csv_rows(root / "Matroid/DEPENDENCY_EDGES.csv"):
            a, b = r["source_id"], r["target_id"]
            if a in self.nodes and b in self.nodes:
                self.preds[b].add(a)
                self.succs[a].add(b)
        self.order = self._topological_order()
        calculated_depth = {}
        for nid in self.order:
            calculated_depth[nid] = max((calculated_depth[p] + 1 for p in self.preds[nid]), default=0)
            if calculated_depth[nid] != self.nodes[nid].depth:
                self.warnings.append(f"{nid}: recorded depth {self.nodes[nid].depth} != calculated {calculated_depth[nid]}")
        self.ready = {
            nid for nid, n in self.nodes.items()
            if (n.proof_status in AVAILABLE_TRUST or
                (not n.proof_status and n.ledger_status == "COMPLETE"))
        }
        # A conflict must not be mistaken for available proof.
        self.ready -= {nid for nid, n in self.nodes.items() if n.proof_status == "UNRESOLVED"}
        self.cited = {nid for nid, n in self.nodes.items() if n.proof_status == "CITED_ASSUMPTION"}
        self.remaining = set(self.nodes) - self.ready
        self.events = load_attempts(attempts or root / "Matroid/SCHEDULER_ATTEMPTS.csv")
        unknown_events = {e.node_id for e in self.events} - set(self.nodes)
        if unknown_events:
            raise ValueError(f"Attempt history has unknown active nodes: {sorted(unknown_events)}")
        (self.last_batch_index, active, self.all_cooldowns,
         self.wakes, history) = derive_cooldowns(self.events)
        self.cooldowns = {nid: cd for nid, cd in active.items() if nid in self.remaining}
        self.expired_cooldowns = {
            nid: cd for nid, cd in self.all_cooldowns.items()
            if nid in self.remaining and nid not in self.cooldowns
        }
        for nid, state in history.items():
            event = state["last_event"]
            if event.event_kind != "ATTEMPT":
                continue
            if event.outcome == "CLOSED" and nid not in self.ready:
                self.warnings.append(f"{nid}: CLOSED attempt contradicts unresolved proof status")
            if event.outcome != "CLOSED" and nid in self.ready:
                self.warnings.append(f"{nid}: unresolved last attempt contradicts available proof status")
        self.overrides = load_overrides(overrides)
        for nid in self.overrides:
            if nid not in self.nodes:
                self.warnings.append(f"estimate override {nid} is not an active node")
        self.word_counts = {}
        if word_counts:
            text = (root / "Manuscript/main.tex").read_text(encoding="utf-8")
            labels = {m.group(1) for n in self.nodes.values() for m in re.finditer(r"`([^`]+)`", n.at_label)}
            by_label = infer_proof_lengths(text, labels)
            for nid, n in self.nodes.items():
                matches = re.findall(r"`([^`]+)`", n.at_label)
                if len(matches) == 1 and matches[0] in by_label:
                    self.word_counts[nid] = by_label[matches[0]]
        self.distance_cache = {}

    def _topological_order(self):
        indeg = {n: len(self.preds[n]) for n in self.nodes}
        q = deque(sorted(n for n in self.nodes if indeg[n] == 0))
        output = []
        while q:
            n = q.popleft()
            output.append(n)
            for t in sorted(self.succs[n]):
                indeg[t] -= 1
                if indeg[t] == 0:
                    q.append(t)
        if len(output) != len(self.nodes):
            raise ValueError("Active dependency graph has a directed cycle")
        return output

    def eligible(self, available):
        return {v for v in self.nodes if v not in available and self.preds[v] <= available}

    def downstream_distances(self, nid):
        if nid not in self.distance_cache:
            d = {nid: 0}
            q = deque([nid])
            while q:
                u = q.popleft()
                for v in self.succs[u]:
                    if v not in d:
                        d[v] = d[u] + 1
                        q.append(v)
            d.pop(nid)
            self.distance_cache[nid] = d
        return self.distance_cache[nid]

    def value(self, nid):
        n = self.nodes[nid]
        return PROVENANCE_VALUE.get(n.provenance, 2.0)

    def cost(self, nid):
        n = self.nodes[nid]
        override = self.overrides.get(nid, {})
        if override.get("cost") is not None:
            return override["cost"], "manual", override.get("confidence", "unknown")
        c = BASE_COST.get(n.provenance, 3.0)
        if n.ledger_status == "STATEMENT_DESIGN":
            c += 1.0
        # Small, low-confidence manuscript proof length effect (no false certainty).
        # This never changes an explicit manual estimate or an externally cited cost.
        wordcount = self.word_counts.get(nid)
        if wordcount is not None and n.provenance.startswith("MANUSCRIPT_PROVED"):
            c += min(1.0, max(0, math.log2(1 + wordcount / 70)) * 0.4)
        return round(c, 2), "heuristic", "low"

    def batch_metrics(self, seq, *, unlock_weight=1.0, future_weight=0.10):
        selected = set(seq)
        available = self.ready | selected
        new_eligible = self.eligible(available) - self.eligible(self.ready)
        new_eligible -= selected
        completed = sum(self.value(nid) for nid in selected)
        unlocked = sum(self.value(nid) for nid in new_eligible)
        dist = {}
        for nid in selected:
            for descendant, d in self.downstream_distances(nid).items():
                if descendant in self.remaining and descendant not in selected and descendant not in new_eligible:
                    dist[descendant] = min(dist.get(descendant, 999), d)
        potential = sum(self.value(nid) / (1 + d) for nid, d in dist.items())
        cost = sum(self.cost(nid)[0] for nid in selected)
        score = (completed + unlock_weight * unlocked + future_weight * potential) / cost
        return dict(score=round(score, 4), estimated_cost=round(cost, 2),
                    completed_value=round(completed, 2), unlock_value=round(unlocked, 2),
                    future_value=round(potential, 2),
                    new_eligible=sorted(new_eligible),
                    remaining_descendants=len(dist))

    def rank_batch(self, size=3, beam_width=100, top=8, deferred=None):
        if size < 1 or beam_width < 1:
            raise ValueError("size and beam width must be positive")
        deferred = set(deferred or ())
        unknown = deferred - set(self.nodes)
        if unknown:
            raise ValueError(f"Unknown deferred node(s): {sorted(unknown)}")
        excluded = deferred | set(self.cooldowns)
        states = [()]
        for _ in range(size):
            generated = {}
            for seq in states:
                available = self.ready | set(seq)
                for nid in self.eligible(available) - excluded:
                    s2 = seq + (nid,)
                    key = frozenset(s2)
                    if key not in generated:
                        generated[key] = s2
            if not generated:
                if states == [()]:
                    states = []
                break
            ranked = sorted(generated.values(), key=lambda seq: (-self.batch_metrics(seq)["score"], seq))
            states = ranked[:beam_width]
        if states:
            return [(seq, self.batch_metrics(seq)) for seq in states[:top]]
        # A controlled one-node retry is allowed only if cooldown alone
        # excludes every otherwise selectable mathematical task.
        candidates = self.eligible(self.ready) - deferred
        if candidates and candidates <= set(self.cooldowns):
            nid = min(candidates, key=lambda n: (self.cooldowns[n].retry_after_batch, n))
            metrics = self.batch_metrics((nid,))
            metrics["cooldown_fallback"] = {
                "reason": "all nondeferred mathematically eligible tasks are cooling",
                **self.cooldowns[nid].as_dict(),
            }
            return [((nid,), metrics)]
        return []

    def report(self, ranks, size, deferred=None):
        eligible = sorted(self.eligible(self.ready))
        deferred = set(deferred or ())
        selectable = sorted(set(eligible) - set(self.cooldowns) - deferred)
        proof_counts = defaultdict(int)
        for nid in self.nodes:
            n = self.nodes[nid]
            if nid in self.ready:
                proof_counts[n.proof_status or "LEGACY_COMPLETE"] += 1
        lines = ["# Next proof batch — dependency-aware scheduler", "",
                 "_Generated proposal; not a mathematical certification or an authorization to admit a theorem._", "",
                 "## Snapshot", "",
                 f"- Active nodes: **{len(self.nodes)}**; active edges: **{sum(map(len, self.preds.values()))}**.",
                 f"- Available: **{len(self.ready)}** (including **{len(self.cited)}** directly cited assumptions); unresolved: **{len(self.remaining)}**.",
                 f"- Eligible unresolved nodes: **{len(eligible)}**; structural depths are **not** scheduling restrictions.",
                 f"- Ordinarily selectable now: **{len(selectable)}**; next attempted batch index: **{self.last_batch_index + 1}**.",
                 f"- Proposed batch size: **{size}**; cost estimates are ordinal proxies, **not token/time forecasts**.",
                 "- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.", ""]
        if deferred:
            lines += [f"- Run-local deferred unresolved nodes: **{', '.join(sorted(deferred))}** (remain unresolved and eligible in the canonical DAG).", ""]
        lines += ["## Persistent cooldowns", ""]
        if self.cooldowns:
            lines += ["| Node | Blocker | Last attempt | Retry after batch | Evidence |",
                      "|---|---|---:|---:|---|"]
            for nid, cd in sorted(self.cooldowns.items()):
                lines.append(f"| {nid} | {cd.blocker_key} | {cd.last_attempt_batch} | "
                             f"{cd.retry_after_batch} | {cd.log_reference} — {cd.blocker_evidence} |")
        else:
            lines.append("No active persistent cooldowns.")
        if self.expired_cooldowns:
            lines.append("")
            lines.append("Expired cooldowns, now selectable when prerequisites permit: " +
                         ", ".join(f"{nid} (retry batch {cd.retry_after_batch})"
                                   for nid, cd in sorted(self.expired_cooldowns.items())) + ".")
        if self.wakes:
            lines.append("")
            lines.append("Recorded evidence-based wakes: " +
                         ", ".join(f"{e.node_id} at batch {e.batch_index}: {e.proof_delta}"
                                   for e in self.wakes) + ".")
        lines.append("")
        if self.warnings:
            lines += ["## Metadata warnings — review before editing", ""]
            lines += [f"- {x}" for x in self.warnings]
            lines.append("")
        lines += ["## Recommended batch", ""]
        if ranks:
            seq, m = ranks[0]
            lines.append(f"**Sequence:** {' → '.join(seq)}")
            lines.append("")
            if "cooldown_fallback" in m:
                fb = m["cooldown_fallback"]
                lines.append(f"**Controlled cooldown fallback:** {fb['reason']}; "
                             f"{fb['node_id']} would ordinarily retry at batch {fb['retry_after_batch']}. "
                             "Do not repeat a failed early retry in this invocation.")
                lines.append("")
            lines.append(f"Score **{m['score']:.3f}** (heuristic); sum of residual-cost scores **{m['estimated_cost']}**; "
                         f"**{len(m['new_eligible'])}** additional nodes become eligible after the batch.")
            lines.append("")
            lines += ["| Task | Depth | Provenance | Est. residual cost | Evidence | Immediate descendants |",
                      "|---|---:|---|---:|---|---:|"]
            for nid in seq:
                n=self.nodes[nid]
                cost, method, conf=self.cost(nid)
                label = self.overrides.get(nid, {}).get("reason", "") if method == "manual" else method + "; " + conf
                lines.append(f"| {nid} — {n.name.replace('|','/')} | {n.depth} | {n.provenance} | {cost} | {label.replace('|','/')} | {len(self.succs[nid])} |")
            lines.append("")
            if m["new_eligible"]:
                lines.append("**Newly eligible after batch:** " + ", ".join(m["new_eligible"]) + ".")
                lines.append("")
        else:
            lines.append("No selectable tasks remain after run-local deferrals and persistent cooldowns; review the auditable blocked frontier. No proof statuses were changed.")
            lines.append("")
        lines += ["## Alternative ranked batches", "",
                  "| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |",
                  "|---:|---|---:|---:|---:|"]
        for i,(seq,m) in enumerate(ranks,1):
            lines.append(f"| {i} | {' → '.join(seq)} | {m['score']:.3f} | {m['estimated_cost']} | {len(m['new_eligible'])} |")
        lines += ["", "## Highest-leverage currently eligible tasks", "",
                  "| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance | Selection state |",
                  "|---|---|---:|---:|---:|---|---|"]
        elig_rank = sorted(eligible, key=lambda nid: (-len(set(self.downstream_distances(nid)) & self.remaining),nid))
        for nid in elig_rank[:20]:
            n=self.nodes[nid]
            status = "cooling" if nid in self.cooldowns else "deferred" if nid in deferred else "selectable"
            lines.append(f"| {nid} | {n.name.replace('|','/')} | {n.depth} | {len(set(self.downstream_distances(nid)) & self.remaining)} | {self.cost(nid)[0]} | {n.provenance} | {status} |")
        lines += ["", "## Operating constraints", "",
                  "1. Confirm selected tasks against the **exact** manuscript statements and ledger provenance; do not let a score override mathematical dependencies.",
                  "2. External-cited status means **verify the exact published theorem**, then use mathlib if exact or isolate an admitted, sourced Lean premise. **Do not auto-admit based on metadata alone.**",
                  "3. Manuscript results and finite certificate claims require substantive proofs; track transitive cited assumptions separately from kernel success.",
                  "4. After a short batch, update graph/status/cost estimates and rerun this scheduler; retain completed proof code and historical attempts.",
                  "5. A new necessary edge requires recomputing topological depths before selecting the next batch.", ""]
        return "\n".join(lines).rstrip()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--estimates", type=Path, default=Path("Matroid/SCHEDULER_ESTIMATES.csv"), help="relative to --root unless absolute")
    parser.add_argument("--attempts", type=Path, default=Path("Matroid/SCHEDULER_ATTEMPTS.csv"), help="append-only event log, relative to --root unless absolute")
    parser.add_argument("--batch-size", type=int, default=2)
    parser.add_argument("--beam-width", type=int, default=120)
    parser.add_argument("--top", type=int, default=8)
    parser.add_argument("--defer-node", action="append", default=[], metavar="N###",
                        help="skip this unresolved node in the current scheduling invocation; may repeat; does not change proof status")
    parser.add_argument("--word-counts", action="store_true", help="use conservative proof-env approximate lexical token count")
    parser.add_argument("--write", type=Path, help="write Markdown report (otherwise stdout)")
    parser.add_argument("--json", type=Path, help="also write machine-readable status and candidate batch metrics")
    parser.add_argument("--strict", action="store_true", help="fail if recorded depth/status metadata are inconsistent")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    estimates = args.estimates if args.estimates.is_absolute() else root / args.estimates
    attempts = args.attempts if args.attempts.is_absolute() else root / args.attempts
    try:
        planner = Planner(root, estimates, args.word_counts, attempts)
    except ValueError as e:
        print(f"INCONSISTENCY: {e}", file=sys.stderr)
        return 2
    if args.strict and planner.warnings:
        for w in planner.warnings: print("INCONSISTENCY:",w,file=sys.stderr)
        return 2
    try:
        ranks = planner.rank_batch(args.batch_size, args.beam_width, args.top, deferred=args.defer_node)
    except ValueError as e:
        print(f"INVALID DEFERRAL: {e}", file=sys.stderr)
        return 2
    report = planner.report(ranks, args.batch_size, deferred=args.defer_node)
    if args.write:
        dst=args.write if args.write.is_absolute() else root/args.write
        dst.parent.mkdir(parents=True,exist_ok=True)
        dst.write_text(report+"\n",encoding="utf-8")
        print(f"Wrote {dst}")
    else:
        print(report)
    if args.json:
        dst=args.json if args.json.is_absolute() else root/args.json
        dst.parent.mkdir(parents=True,exist_ok=True)
        payload = {
            "active":len(planner.nodes),"available":len(planner.ready),
            "cited_premises":sorted(planner.cited),"eligible":sorted(planner.eligible(planner.ready)),
            "selectable":sorted(planner.eligible(planner.ready) - set(planner.cooldowns) - set(args.defer_node)),
            "last_attempted_batch_index":planner.last_batch_index,
            "next_batch_index":planner.last_batch_index + 1,
            "persistent_cooldowns":[cd.as_dict() for _, cd in sorted(planner.cooldowns.items())],
            "expired_cooldowns":[cd.as_dict() for _, cd in sorted(planner.expired_cooldowns.items())],
            "wakes":[{"event_id":e.event_id,"batch_index":e.batch_index,
                       "node_id":e.node_id,"proof_delta":e.proof_delta,
                       "blocker_evidence":e.blocker_evidence,"log_reference":e.log_reference}
                      for e in planner.wakes],
            "warnings":planner.warnings,
            "run_deferred":sorted(set(args.defer_node)),
            "candidates":[{"sequence":list(seq),**m} for seq,m in ranks]
        }
        dst.write_text(json.dumps(payload,indent=2)+"\n",encoding="utf-8")
        print(f"Wrote {dst}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
