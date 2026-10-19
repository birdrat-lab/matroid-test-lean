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


class Planner:
    def __init__(self, root: Path, overrides: Path, word_counts: bool):
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

    def rank_batch(self, size=3, beam_width=100, top=8):
        if size < 1 or beam_width < 1:
            raise ValueError("size and beam width must be positive")
        states = [()]
        for _ in range(size):
            generated = {}
            for seq in states:
                available = self.ready | set(seq)
                for nid in self.eligible(available):
                    s2 = seq + (nid,)
                    key = frozenset(s2)
                    if key not in generated:
                        generated[key] = s2
            if not generated:
                break
            ranked = sorted(generated.values(), key=lambda seq: (-self.batch_metrics(seq)["score"], seq))
            states = ranked[:beam_width]
        return [(seq, self.batch_metrics(seq)) for seq in states[:top]]

    def report(self, ranks, size):
        eligible = sorted(self.eligible(self.ready))
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
                 f"- Proposed batch size: **{size}**; cost estimates are ordinal proxies, **not token/time forecasts**.",
                 "- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.", ""]
        if self.warnings:
            lines += ["## Metadata warnings — review before editing", ""]
            lines += [f"- {x}" for x in self.warnings]
            lines.append("")
        lines += ["## Recommended batch", ""]
        if ranks:
            seq, m = ranks[0]
            lines.append(f"**Sequence:** {' → '.join(seq)}")
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
            lines.append("No eligible tasks available; investigate missing/incorrect dependencies.")
            lines.append("")
        lines += ["## Alternative ranked batches", "",
                  "| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |",
                  "|---:|---|---:|---:|---:|"]
        for i,(seq,m) in enumerate(ranks,1):
            lines.append(f"| {i} | {' → '.join(seq)} | {m['score']:.3f} | {m['estimated_cost']} | {len(m['new_eligible'])} |")
        lines += ["", "## Highest-leverage currently eligible tasks", "",
                  "| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance |",
                  "|---|---|---:|---:|---:|---|"]
        elig_rank = sorted(eligible, key=lambda nid: (-len(set(self.downstream_distances(nid)) & self.remaining),nid))
        for nid in elig_rank[:20]:
            n=self.nodes[nid]
            lines.append(f"| {nid} | {n.name.replace('|','/')} | {n.depth} | {len(set(self.downstream_distances(nid)) & self.remaining)} | {self.cost(nid)[0]} | {n.provenance} |")
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
    parser.add_argument("--batch-size", type=int, default=2)
    parser.add_argument("--beam-width", type=int, default=120)
    parser.add_argument("--top", type=int, default=8)
    parser.add_argument("--word-counts", action="store_true", help="use conservative proof-env approximate lexical token count")
    parser.add_argument("--write", type=Path, help="write Markdown report (otherwise stdout)")
    parser.add_argument("--json", type=Path, help="also write machine-readable status and candidate batch metrics")
    parser.add_argument("--strict", action="store_true", help="fail if recorded depth/status metadata are inconsistent")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    estimates = args.estimates if args.estimates.is_absolute() else root / args.estimates
    planner = Planner(root, estimates, args.word_counts)
    if args.strict and planner.warnings:
        for w in planner.warnings: print("INCONSISTENCY:",w,file=sys.stderr)
        return 2
    ranks = planner.rank_batch(args.batch_size, args.beam_width,args.top)
    report=planner.report(ranks,args.batch_size)
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
            "warnings":planner.warnings,
            "candidates":[{"sequence":list(seq),**m} for seq,m in ranks]
        }
        dst.write_text(json.dumps(payload,indent=2)+"\n",encoding="utf-8")
        print(f"Wrote {dst}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
