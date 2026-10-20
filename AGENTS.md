# AGENTS.md — Automated Matroid Formalization

## Mission

Continue the Lean 4 formalization of `Manuscript/main.tex`.

The project uses a dependency-aware scheduler to select formalization tasks. The scheduler, not the agent, determines the next proof batch.

The objective is to advance the manuscript's formalization efficiently while maintaining exact mathematical correspondence, transparent external citations, and reproducible Lean verification.

**Do not impose a global depth-by-depth execution order. Do not manually select preferred theorems.**

**New requirement: evidence-based persistent cooldowns.** A theorem that has repeatedly stalled on the same core obstruction must not receive the highest priority again at the beginning of every invocation merely because of its downstream leverage. Cooldowns are scheduling metadata, **not** changes to mathematical truth, proof status, dependencies, or estimated proof difficulty. The current script supports only run-local deferral; the first continuation pass must implement the persistent mechanism described in §8.1 before depending on it.

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
- `Matroid/SCHEDULER_ATTEMPTS.csv` (append-only, persistent attempt events; add this file in the first pass)
- `Matroid/NEXT_BATCH.md`
- `Matroid/NEXT_BATCH.json`

Preserve historical proof logs, partial proofs, and mathematical provenance.

Do not alter mathematical requirements merely to improve scheduler scores or make an inconvenient task disappear.

## 2. Scheduler setup and invocation

### 2.1 First run under this revised policy

Before beginning new theorem work, inspect the current scheduler. As of the October 19 snapshot, `scripts/select_frontier.py` supports `--defer-node` only **within one invocation** and does not read a persistent attempt/cooldown history.

**Implement the durable attempt log and deterministic cooldown logic specified in §8.1, then update `scripts/test_select_frontier.py` and `Matroid/SCHEDULER.md`.** Use the existing graph, status, and cost APIs. The script, not the agent's memory, must determine which nodes are cooling down. Do not assume this feature exists merely because it appears in `AGENTS.md`.

Do not hardcode any node ID, rewrite completed mathematical proofs, or overwrite historical data. Import old attempts only when a specific log or budget entry supports the event. Unknown historical attempts remain unknown.

### 2.2 Standard scheduler invocation

At the beginning of every formalization pass and after every batch, run from the repository root:

```bash
python3 -m unittest discover \
  -s scripts -p 'test_select_frontier.py'

python3 scripts/select_frontier.py \
  --strict --word-counts \
  --write Matroid/NEXT_BATCH.md \
  --json Matroid/NEXT_BATCH.json
```

The scheduler must load **current** proof records and **persistent** attempt/cooldown records. It must automatically exclude actively cooling tasks from ordinary batch selection, including when a new Codex session begins. `--defer-node` remains available only for a new, documented stall during the **current** run.

If validation fails, repair the inconsistent records from evidence before continuing. Read the new `Matroid/NEXT_BATCH.json` and execute the highest-ranked prerequisite-valid batch. Repeat automatically within the five-batch loop (§8.2). Do not stop solely because the first batch finished.

The scheduler may select nodes from different structural depths. This is intentional.

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

A valid, active **persistent cooldown** is not a manual override. It is a consequence of previously recorded attempts and the deterministic rules in §8.1. The scheduler must make cooldowns and their expiration visible in its generated output. Never hide an otherwise mathematically eligible node from the DAG or mark it `UNAVAILABLE` to implement cooldown.

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

Do not manipulate estimates to force a desired scheduling order. **In particular, do not inflate residual cost to simulate a cooldown.** Historical edit/check effort and proof progress can support an independent cost revision; cooldown activation alone cannot.

A failed proof attempt is useful evidence for future cost estimation, but does not count as completing a mathematical requirement.

### 6.1 Persistent attempt records

Append one `ATTEMPT` record for each **substantively attempted** node in every scheduler batch. Give every attempted batch a globally increasing `batch_index` that persists across Codex sessions. When an independent change removes an existing blocker, record a separate `WAKE` event for the cooled node, without inventing a proof attempt. Keep the event log append-only, and derive the cooldown state from it on each scheduler run; do not maintain an inconsistent second source of truth.

Create `Matroid/SCHEDULER_ATTEMPTS.csv` with at least:

`event_id,batch_index,node_id,event_kind,outcome,blocker_key,blocker_evidence,proof_delta,edit_check_groups,log_reference`.

`event_id` is a globally unique, monotonically increasing integer for deterministic ordering. `event_kind` is `ATTEMPT` or `WAKE`. For a `WAKE` event, `outcome` is `BLOCKER_REMOVED`, `edit_check_groups` is zero, and `proof_delta` identifies the **other** changed declaration or evidence that removes the obstacle. `WAKE` events do not advance batch counters and never count as theorem attempts.

Use stable outcomes:

- `CLOSED`: result became `KERNEL_PROVED`, `CONDITIONAL_PROOF`, or an exactly verified `CITED_ASSUMPTION`.
- `CORE_PROGRESS`: a previously blocking central goal was discharged, a necessary mathematical obstacle changed, or a confirmed new proof route now closes an essential gap.
- `SUPPORT_ONLY`: useful helpers were proved but the **same core obstacle** remains.
- `NO_PROGRESS`: a serious attempt did not materially change the available route.
- `INVALID_INTERFACE`: mathematical provenance, statement, or dependencies must be repaired before proof search resumes.

Each unresolved `ATTEMPT` event must have a concise **stable blocker key** and a reference to specific proof/log evidence. A qualifying unsuccessful attempt must contain an actually executed proof route or an evidenced, independently verified feasibility blocker; a quick retry or repeated reading of the same file is not a second substantive attempt. `SUPPORT_ONLY` is genuine progress and must be preserved, but **does not reset** the same-blocker stall counter. A `CORE_PROGRESS` classification requires identifying the prior blocker and demonstrating how it was removed or materially changed—not simply pointing to more lines of compiling Lean code.

Do not fabricate token use, elapsed time, attempts, or progress. Missing fields remain explicitly unknown where the schema permits. Mark an unattempted dependent second task as skipped in the batch report; do not record it as a failed proof attempt.


## 7. Executing a selected batch

Each scheduler-selected batch contains two tasks by default, potentially with an internal dependency. **A Codex invocation must attempt multiple batches**, as described in §8; a single batch is not the default stopping point.

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

## 8. Persistent blocker-aware scheduling and the multi-batch loop

### 8.1 Persistent cooldown: implement and enforce

The scheduler must compute cooldowns **from the persistent attempt log** every time it starts. Continue using its existing scoring function and prerequisite-closed beam search. Persistent cooldown affects *selection eligibility only*, not theorem eligibility in the mathematical DAG or the numerator/denominator of the heuristic score.

**Trigger.** When a node receives **two substantive unsuccessful attempts against the same documented blocker**, with outcomes `SUPPORT_ONLY` or `NO_PROGRESS` and no intervening `CORE_PROGRESS`, place it on cooldown. This count is cumulative across Codex invocations, not reset each run. Evidence must identify a common obstruction; unrelated failures should not be conflated. Past work may count only if its attempt and blocker are recoverable from the logs; do not invent history.

**Duration.** The initial cooldown lasts **five subsequent attempted scheduler batches** (counted by globally increasing batch index, not by elapsed wall-clock time or Codex sessions). After it expires, the task is again considered normally. If a retry encounters the same unresolved obstruction, use **ten subsequent batches** for the next cooldown, then cap later cooldowns at **fifteen batches**. Store enough event evidence to recompute this escalating schedule deterministically.

**Early wake-up.** Cancel a cooldown only when there is verifiable new evidence that the original blocker has materially changed: for example, its missing prerequisite is now available, a theorem needed for the core route has been proved, the invalid statement has been repaired, or a genuinely different route is now feasible. Record a `WAKE` event with the specific declaration/change and why it affects the blocker. Do not reset the original failed-attempt history; preserve it for audits. A regenerated schedule, another auxiliary lemma, or a revised cost score alone is **not** an early-wake event.

**Selection and transparency.** Do not select an actively cooled node in ordinary beam-search batches. Report each cooled node's blocker, last attempt, retry-after batch, and evidence link in both `NEXT_BATCH.md` and `NEXT_BATCH.json`. The scheduler must preserve the distinction between mathematically eligible nodes and selectable nodes. It must never edit `PROOF_STATUS.csv`, `LEDGER.md`, or `DEPENDENCY_EDGES.csv` to implement a cooldown.

**No deadlock or starvation.** If all mathematically eligible unresolved nodes are cooling down, the scheduler must report that condition explicitly. It may propose **one controlled early retry** of the node whose cooldown expires soonest, with a visible `cooldown_fallback` reason; it must not silently treat the cooldown as expired. If that attempt produces no core progress, do not repeatedly retry the same node in the same invocation. Otherwise stop with an auditable report of the blocked frontier. Previously cooled nodes must return to the candidate pool at expiration, without manual intervention.

**Testing.** Add synthetic fixture-based tests in `scripts/test_select_frontier.py` for: persistence across scheduler restarts; two same-blocker stalls triggering cooldown; `SUPPORT_ONLY` versus `CORE_PROGRESS`; global batch-count expiry; escalating retry windows; legitimate evidence-based early wake-up; preservation of proof status and mathematical eligibility; dependency-valid batches after exclusion; all-candidates-cooled fallback without infinite retry; and detection of malformed or contradictory attempt rows. Keep the existing tests passing. Update `Matroid/SCHEDULER.md` to document the format, thresholds, and precise semantics.

Run-local `--defer-node` remains a short-term control for the rest of the **current** invocation after a newly failed serious attempt. It is separate from the persistent mechanism; the scheduler must apply both exclusions without confusing them.

### 8.2 Five-batch autonomous loop (default)

**Default execution target: five consecutive scheduler-selected batches per Codex invocation**, generally up to ten selected task opportunities. Do not stop after the first batch or request approval between valid selections.

For each batch:

1. Run the scheduler against the latest graph, statuses, estimates, and persistent attempt log. Execute its highest-scoring valid sequence, never a hardcoded theorem ID.
2. Confirm source correspondence, provenance, and direct prerequisites. Repair a proven graph/statement mismatch before attempting the theorem and rerun scheduling.
3. Attempt selected tasks in dependency order under the matroid-first and citation policies. If the first task remains unavailable and the second depends on it, do **not** pretend the second was attempted.
4. Use focused Lean checks during the pass. Record `CLOSED`, `CORE_PROGRESS`, `SUPPORT_ONLY`, `NO_PROGRESS`, or `INVALID_INTERFACE` for each actual attempt; give the batch its persistent index; update relevant formalization logs and estimates. Apply run-local deferral when justified by a serious unresolved attempt (typically up to six substantive edit/check groups), preserving all partial results.
5. Recompute persistent cooldowns, update the report, and **rerun the scheduler automatically**. Continue to the next batch until five have been attempted or a genuine stopping condition applies.

At the end, run a full `lake build`, the tracked `#print axioms` audits, the correspondence checks, and the scheduler test suite. Rectify any status contradicted by verification. Regenerate `NEXT_BATCH.md` and `NEXT_BATCH.json` **without run-local deferrals**, but **with the persistent cooldown state still applied**, for the next invocation.

### 8.3 Stopping conditions

Stop after five attempted batches. Stop earlier only when:

- No sound task can be selected after the explicit cooldown fallback and run-local deferral rules.
- The manuscript, dependency records, or trust statuses are inconsistent and cannot be repaired from source evidence.
- A reproducible Lean/toolchain failure blocks sound verification.
- Available context or execution resources prevent further reliable work.

If fewer than three batches are attempted, state the exact reason. Do not stop merely because a task remains difficult, a cited theorem has been admitted, or one batch completed.

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

## 11. Required output after each multi-batch run

Produce a compact report containing:

- Number of scheduler-selected batches attempted (default target five), with their sequences and initial heuristic scores.
- Completed, admitted, conditional, and unresolved requirements.
- Exact Lean declarations and manuscript correspondence findings.
- Any citations introduced or checked.
- Newly discovered or corrected dependencies.
- Actual resource observations and updated remaining-cost estimates, **separately** from cooldowns.
- The append-only attempt events and their stable blocker keys; active persistent cooldowns, expiry batch numbers, and any evidence-based early wake-ups.
- Verification commands executed and their results.
- Newly available requirements.
- The next automatically selected batch, computed **without run-local deferrals but with persistent cooldowns** after the run ends (for the next invocation).

Update the canonical files and generated scheduler reports. At the end, clear run-local `--defer-node` options and regenerate `NEXT_BATCH.md` and `NEXT_BATCH.json`. **Do not clear the persistent attempt/cooldown history.** Unresolved mathematical requirements remain unresolved. Preserve the log needed for automatic cooldown expiration.

Preserve chronological logs and partial proofs.

**The formalization is scheduler-directed, mathematically audited, resource-aware, and multi-batch by default. A recurring mathematical blocker now incurs an automatic, auditable cooldown across invocations; neither proof status nor estimated difficulty is altered merely to change selection.**