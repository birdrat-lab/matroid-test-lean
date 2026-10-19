# AGENTS.md — Automated Matroid Formalization

## Mission

Continue the Lean 4 formalization of `Manuscript/main.tex`.

The project uses a dependency-aware scheduler to select formalization tasks. The scheduler, not the agent, determines the next proof batch.

The objective is to advance the manuscript's formalization efficiently while maintaining exact mathematical correspondence, transparent external citations, and reproducible Lean verification.

**Do not impose a global depth-by-depth execution order. Do not manually select preferred theorems.**

Topological depth remains useful for auditing the dependency graph, but it does not determine execution priority.

## 1. Authoritative project files

The manuscript is the mathematical source of truth:

- `Manuscript/main.tex`

Formalization and dependency records:

- `Matroid/LEDGER.md`
- `Matroid/DEPENDENCY_EDGES.csv`
- `Matroid/DEPTHS.csv`
- `Matroid/PROOF_STATUS.csv`
- `Matroid/PROOF_BUDGET.md`
- `Matroid/FORMALIZATION_LOG.md`
- `Matroid/SOURCES.md`
- `Matroid/FRONTIER.md`

Scheduler inputs and outputs:

- `scripts/select_frontier.py`
- `scripts/test_select_frontier.py`
- `Matroid/SCHEDULER.md`
- `Matroid/SCHEDULER_ESTIMATES.csv`
- `Matroid/NEXT_BATCH.md`
- `Matroid/NEXT_BATCH.json`

Preserve historical proof logs, partial proofs, and mathematical provenance.

Do not alter mathematical requirements merely to improve scheduler scores or make an inconvenient task disappear.

## 2. Automatic scheduler invocation

At the beginning of every formalization pass, run from the repository root:

```bash
python3 -m unittest discover \
  -s scripts -p 'test_select_frontier.py'

python3 scripts/select_frontier.py \
  --strict --word-counts \
  --write Matroid/NEXT_BATCH.md \
  --json Matroid/NEXT_BATCH.json
```

The scheduler must use the current dependency graph and proof records, not a previously generated report.

If validation fails, repair the inconsistent records before continuing.

Read `Matroid/NEXT_BATCH.json` and execute the **highest-ranked prerequisite-valid batch**.

Do not substitute a manually preferred theorem, a lower-depth theorem, or a previously hardcoded target.

The scheduler may select results from different topological depths. This is intentional.

## 3. Scheduler authority and exceptions

The scheduler determines the execution order. Codex determines how to discharge the selected mathematical obligations.

Before attempting a selected task, verify:

1. The exact manuscript statement and its provenance.
2. The recorded direct prerequisites.
3. Availability of all required mathematical premises.
4. Existing partial Lean proofs and reusable infrastructure.
5. Whether the proposed task is a definition, manuscript result, finite certificate, or externally established theorem.

A scheduler recommendation can be rejected only for a concrete correctness or feasibility issue, such as:

- An incorrect or missing mathematical dependency.
- An invalid or mismatched literature citation.
- An incorrect provenance classification.
- A stale proof-status record.
- A substantially inaccurate remaining-cost estimate.
- An already documented blocking condition that makes the task currently infeasible.

**Do not override a recommendation merely because another theorem seems more interesting or easier.**

When an exception occurs:

1. Record the exact reason.
2. Correct the underlying ledger, dependency, provenance, or cost data.
3. Recompute topological depths if dependencies changed.
4. Rerun the scheduler.
5. Execute its newly selected batch.

Never silently substitute another task.

If a blocked task remains repeatedly selected despite documented infeasibility, identify the scheduling deficiency. A temporary deferral mechanism may be added to the scheduler, but it must be explicit, auditable, and covered by tests.

## 4. Mathematical proof policy

### 4.1 Foundational definitions

Formalize definitions explicitly and faithfully.

Use existing mathlib structures when appropriate, but preserve the manuscript's conventions concerning:

- Matroid independence, bases, rank, closure, and circuits.
- Indexed elements, loops, and parallel elements.
- Deletion, contraction, duality, and matroid sums.
- Targets, response labels, and available sets.
- Representations and weighted basis sums.

A definition may reference existing mathematical objects. It must not conceal an unproved existence or characterization theorem.

If a nominal definition includes a substantive mathematical assertion, track that assertion as a separate proof obligation.

### 4.2 Manuscript-local mathematics

Every manuscript-local mathematical result requires a genuine Lean proof.

Do not use `sorry`, `admit`, or a new axiom to establish the manuscript's own claims.

A manuscript result may depend on a separately verified and explicitly admitted external theorem. In that case, its local Lean argument must still be complete, and its status must reflect the transitive admitted premise.

Finite computations and manuscript-specific certificates also require kernel-checked proofs or verified certificate checkers.

### 4.3 Externally cited mathematics

For a result classified `EXTERNAL_CITED`:

1. Locate the precise external theorem.
2. Verify that its hypotheses and conclusion establish the required statement.
3. Check for an exact trusted mathlib implementation.
4. If available, reuse that implementation.
5. Otherwise, isolate the precise theorem as a cited `sorry` under `Matroid/External/`.

**Do not spend a substantial proof-development budget reproving an externally cited theorem once its exact correspondence has been established.**

Record the author, reference, theorem number or page, mathematical statement, and any translation into project-specific notation.

Do not admit a theorem merely because the ledger labels it `EXTERNAL_CITED`.

For uncited standard results, first search mathlib and assess whether the result is an immediate consequence of available lemmas. If it requires nontrivial external theory, establish an authoritative citation before applying the citation policy.

Existing completed external proofs must be retained.

### 4.4 Matroid-first proofs

For structural claims, prefer arguments using abstract matroid data:

- Bases and independent sets.
- Circuits and cycles.
- Rank and closure.
- Duality, deletion, and contraction.
- Flats and modular structure.
- Weighted basis sums and boundary signatures.

Graphical and matrix representations are appropriate when mathematically required, particularly for TU results and explicit finite certificates.

Do not replace a general matroid theorem with a result proved only for graphic or representable special cases.

When switching to a representation-level argument, record why the abstraction is necessary and provide the bridge back to the required matroidal statement.

## 5. Proof-status semantics

Use the existing trust-status system consistently.

| Status | Meaning |
|---|---|
| `KERNEL_PROVED` | Complete Lean proof without admitted mathematical premises |
| `CITED_ASSUMPTION` | Exact externally established theorem admitted through a documented `sorry` |
| `CONDITIONAL_PROOF` | Complete local Lean proof transitively depending on admitted external mathematics |
| `UNRESOLVED` | Mathematical obligation not yet discharged |

The scheduler may treat the first three states as available prerequisites, but must preserve their different trust levels.

A successful `lake build` does not establish unconditional certification when `sorryAx` occurs.

Reserve the ledger's legacy `COMPLETE` status for genuinely admission-free results unless the ledger schema is explicitly migrated and all associated checks updated.

Never erase admitted-premise dependencies when updating a downstream theorem's status.

## 6. Proof-cost estimation

The scheduler estimates **remaining formalization cost**, not total historical cost.

Its cost inputs include:

- Manuscript proof length, where a reliable proof environment is available.
- Mathematical provenance.
- Existing mathlib coverage.
- Previously completed intermediate lemmas.
- Recorded proof attempts and failures.
- Representation or infrastructure requirements.
- Manually documented residual-cost estimates.

`Matroid/SCHEDULER_ESTIMATES.csv` contains heuristic cost scores, not measured token or wall-clock consumption.

Use the `--word-counts` option consistently.

Manual estimates must have a reason and confidence level. They may override the manuscript-length heuristic when supported by actual formalization evidence.

After attempting a task:

1. Record the actual proof route and outcome.
2. Preserve new reusable intermediate lemmas.
3. Record substantive edit/check cycles.
4. Record measured time or token use when available.
5. Keep unavailable measurements explicitly `UNKNOWN`.
6. Update the estimated **remaining** cost.

Do not manipulate estimates to force a desired scheduling order.

A failed proof attempt is useful evidence for future cost estimation, but does not count as completing a mathematical requirement.

## 7. Executing a selected batch

The default scheduler batch contains two tasks, potentially with an internal dependency.

Execute them in the order specified by `NEXT_BATCH.json`.

For each task:

**A. Establish mathematical correspondence.**

Read the exact manuscript passage, theorem statement, proof, and required context. Record any mismatch between the manuscript and the proposed Lean interface.

**B. Inspect existing infrastructure.**

Locate existing declarations, partial proofs, cited premises, and relevant mathlib APIs.

Avoid duplicating established functionality.

**C. Execute the appropriate proof policy.**

Formalize manuscript mathematics completely, reuse trusted library results, or isolate verified external citations.

**D. Verify the result.**

Run the relevant Lean checks. Compare the final declaration's full hypotheses and conclusion against the manuscript requirement.

Inspect its transitive axioms using `#print axioms`.

**E. Update project records.**

Record the outcome, exact declarations, admitted premises, proof routes, resource use, and any new dependencies.

If a task becomes blocked, preserve the partial work, record the blocker and updated residual cost, and proceed according to the scheduler's next valid selection.

Do not continue indefinitely on a blocked theorem.

## 8. Automatic rescheduling

After each completed or exhausted batch:

1. Update all mathematical and proof-status records.
2. Run the scheduler tests.
3. Regenerate `NEXT_BATCH.md` and `NEXT_BATCH.json`.
4. Verify that the newly selected batch is prerequisite-valid.
5. Report the next automatically selected batch.

**Never manually choose the next batch in the completion report.**

The default unit of work is one scheduled batch per invocation. Completing a batch automatically triggers rescheduling, but not an unbounded additional proof campaign.

If explicitly instructed to execute multiple batches autonomously, repeat the same cycle without requesting approval between valid selections, within the specified execution budget.

Do not continue if the mathematical records are inconsistent or source validation exposes an unresolved correctness issue.

## 9. Dependency maintenance

The dependency DAG records genuine direct mathematical prerequisites, not chronology or proof-development convenience.

When a proof reveals a missing prerequisite:

1. Verify that the dependency is mathematically necessary for the recorded statement or adopted proof route.
2. Add the evidenced direct edge.
3. Recompute the complete topological-depth table.
4. Check for cycles.
5. Rerun the scheduler.

Do not insert edges merely because a convenient Lean helper uses an additional theorem, unless the mathematical requirement genuinely depends on it under the adopted proof interface.

Do not retain incorrect depths or omit dependencies to preserve a chosen schedule.

Topological depths remain structural metadata and must not be used as execution barriers.

## 10. Verification and correspondence audit

Before marking any result available:

1. Check the exact manuscript/Lean statement correspondence.
2. Check all hypotheses, including finite-set assumptions, field conditions, index types, target membership, and exceptional cases.
3. Verify that a general matroid result has not been weakened to a representable or graphic special case.
4. Run the relevant Lean build and, when possible, full `lake build`.
5. Check and record the declaration's transitive axioms.
6. Record whether the result is unconditional or conditional on cited mathematics.

Maintain reproducible tracked axiom-audit files.

A result is not established merely because the ledger says it is complete or the code compiles with an admitted theorem.

## 11. Required output after each pass

Produce a compact report containing:

- Scheduler-selected batch and initial heuristic scores.
- Completed, admitted, conditional, and unresolved requirements.
- Exact Lean declarations and manuscript correspondence findings.
- Any citations introduced or checked.
- Newly discovered or corrected dependencies.
- Actual resource observations and updated remaining-cost estimates.
- Verification commands executed and their results.
- Newly available requirements.
- The next automatically selected batch.

Update the canonical files and generated scheduler reports.

Preserve chronological logs and partial proofs.

**The formalization is scheduler-directed, mathematically audited, and resource-aware. The scheduler selects the work; Codex proves or validates it; the resulting evidence updates the next scheduling decision.**