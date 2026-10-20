# Dependency-aware formalization scheduler

The executable `scripts/select_frontier.py` reads the **current** `Matroid/LEDGER.md`, `DEPENDENCY_EDGES.csv`, `DEPTHS.csv`, `PROOF_STATUS.csv`, and optional `Matroid/SCHEDULER_ESTIMATES.csv`. It is a read-only planner over the authoritative mathematics/proof ledger; it never edits proof statuses or admits theorems. It recomputes active-DAG topological order, checks stored depths and ledger completion consistency, and determines eligible unresolved tasks using **direct prerequisites**, with cited assumptions treated as conditionally available.

Run from the repo root:

```sh
python3 -m unittest discover -s scripts -p 'test_select_frontier.py'
python3 scripts/select_frontier.py --strict --word-counts \
  --write Matroid/NEXT_BATCH.md --json Matroid/NEXT_BATCH.json
```

The default **individual batch** size is two; explore alternatives with `--batch-size 3 --top 12`. Root `AGENTS.md` directs Codex to execute **five consecutive batches per run**, automatically reranking after each. Thus the scheduler chooses task sequences, while the Codex invocation executes a bounded multi-batch loop. Under `--strict`, any recorded depth/status mismatch is a blocking error: repair the canonical records, don't edit the scheduler to silence it. Do **not** mechanically mark suggested nodes completed. Re-run after every small proof pass and any dependency-edge correction. Keep generated `NEXT_BATCH` reports as snapshots of what the program recommended, not independent mathematical conclusions.

If a selected task has received a documented serious attempt during the **current Codex invocation** and remains stalled, pass `--defer-node N###` (repeatable) for subsequent rerankings in that invocation. It temporarily excludes the node from selection but does **not** alter canonical status, eligibility, direct edges, or future invocations. At the end of the run regenerate the reports **without** `--defer-node` so the next invocation starts with the full frontier. This option is not permission to skip difficult tasks before attempting them.

## Objective and assumptions

The planner performs a beam search over prerequisite-valid task **sequences**, rather than choosing the highest-degree node or forcing ascending depth. At each step, a candidate is selectable only if all its recorded active mathematical prerequisites are available, either from the ledger or earlier in its proposed sequence. Thus it can recommend a depth-8 result whose specific ancestors are all complete even while unrelated depth-7 results remain unfinished.

It scores a batch by

\[
\frac{\text{value of completed tasks} + \text{value of newly eligible tasks}
      + 0.10\,\text{discounted unresolved descendant value}}
     {\text{sum of estimated residual cost scores}}.
\]

The score is **not** a proven approximation ratio and does not optimize a measured number of tokens. Source-specific values and default costs are explicit constants in the script. `SCHEDULER_ESTIMATES.csv` provides transparent *overrides* for cases supported by the proof log (e.g. an existing partial proof). Weights, cost classes, batch size, and beam width are research/engineering choices and should be recalibrated as real effort data become available. The dependency graph itself may change upon discovering genuine missing premises.

## What cost estimates mean

`residual_cost` is a strictly positive **ordinal score**, roughly 1=small, 2=moderate, 3=large, 4=research-scale. It is not a time/token measurement. Any historical `UNKNOWN` time/token entries remain unknown. For a new override, state the provenance, partial-proof status, confirmed library support, failed route, or statement-design obstacle in the `reason` field, and label its confidence. Do not apply a numeric correction using guessed token use.

With `--word-counts`, the scheduler tries to pair a theorem's **exact TeX label** to an immediately following `proof` environment. An approximate LaTeX lexical-token count modestly influences the default cost of manuscript-proved results. It is omitted when such a match is missing (especially for definitions, unlabeled requirements, or prose/certificate claims). These counts should not be treated as informal-paper formalization effort predictions without validation.

## Trust and citation semantics

- `KERNEL_PROVED` nodes and older genuinely `COMPLETE` nodes are available unconditionally. `CITED_ASSUMPTION` and `CONDITIONAL_PROOF` nodes are available only **relative to stated external premises**. `UNRESOLVED` nodes are unavailable regardless of their depth.
- The scheduler does not establish whether an `EXTERNAL_CITED` row has an exact citation. **Codex must check the actual reference and hypotheses before using a `sorry`**. Use exact already-trusted library results if available; otherwise isolate the minimal cited theorem in `Matroid/External/` and record the transitive `sorryAx`.
- Manuscript-local results and finite certificate claims require complete actual Lean proofs (possibly conditional on **separately sourced** external theorems). Definitions must remain faithful to the manuscript's mathematical language and are not admitted as axioms merely because similar definitions appear in references.
- A passing `lake build` is not proof of citation-free status. Inspect declarations and `#print axioms` for target-facing results.

See root `AGENTS.md` for proof execution, matroid-first and ledger update rules.
