# Depth 5: Resource-Aware Matroid Formalization

## Objective and scope

The manuscript-facing Matroid library is complete through structural topological depth 4 in the current repository snapshot. This task performs **one depth-5 pass only**, while introducing a resource-aware policy for established external mathematics.

The standing objective remains to **prove every requirement in Lean whenever practical**. Manuscript-local mathematical claims must receive actual Lean proofs. Established external results may, after a bounded good-faith attempt and source verification, be carried as **explicitly cited admissions**. Such admissions are not kernel proofs and must never be counted as such.

Workflow: verify depth 4 → freeze depth-5 targets → manuscript and proof-plan audit → mathlib search → bounded proof attempts → prove or carefully admit eligible external facts → build and axiom audit → update ledger/depth report → **STOP before depth 6**.

## 1. Canonical sources and invariants

Read these before any new proofs:

- `Manuscript/main.tex` — mathematical statement and actual manuscript proof/citations.
- `Matroid/LEDGER.md` — canonical requirements, classification, provenance, status.
- `Matroid/DEPENDENCY_EDGES.csv` — direct prerequisite DAG.
- `Matroid/DEPTHS.csv` and `Matroid/FRONTIER.md` — regenerated depth and status views.
- `Matroid/FORMALIZATION_LOG.md` and `Matroid/SOURCES.md` — proof and external-source records.

Recompute longest-path depths from the active DAG: roots have depth 0; otherwise `depth(v) = 1 + max(depth(u))` over active edges `u → v`. Active scopes are `CORE_MATROID` and `MATROID_INTERFACE`.

Preflight: run `lake build`; verify no outstanding active requirements through depth 4, and confirm previously proved N268/N176 are unchanged and have no project-local `sorryAx`. Do not reopen these results unless a genuine regression appears.

## 2. Freeze the current depth-5 layer

The **expected** 14 unresolved nodes in the 2026-10-11 archive are:

| ID | Mathematical requirement | Manuscript provenance |
|---|---|---|
| N026 | Minor (deletions and contractions) | Definition |
| N028 | Contraction composition | External standard |
| N029 | Deletion–contraction commutation | External standard |
| N041 | Closure/rank compatibility in a single-element extension | External standard |
| N045 | Represented closure | External standard |
| N049 | Represented contraction (including dependent contracted sets) | **Manuscript proved:** `prop:represented-minors` |
| N053 | TU matrices represent the same column matroid over every field | External standard; partial minor bridge exists |
| N125 | Weighted TU determinant equals weighted basis sum | **Externally cited:** Cauchy–Binet + TU; partial minor lemma exists |
| N131 | Rank-one uniform target closure | External standard |
| N134 | Duality interchanges deletion and contraction | External standard |
| N137 | Target ratio under one-sum | **Manuscript proved:** `prop:seymour-one-sum` |
| N143 | Nonspanned target becomes coloop in restriction | **Manuscript proved:** `prop:seymour-two-sum-input-minors` |
| N262 | Dependent-row removal preserves column matroid and reconstruction equations | External standard |
| N264 | Graphic closure characterized by paths between endpoints | External standard |

**Recompute and freeze**, do not force this list if the actual DAG differs. Record ID, prerequisites, provenance, initial status and depth in `Matroid/FRONTIER.md`. Do not pull in newly exposed depth-6 requirements. Nodes may be attempted independently within depth 5.

## 3. Proof classification: not all completions are equal

First classify the **mathematical source**, separately from the **formal trust state**.

Mathematical sources:
- `MANUSCRIPT_DEFINITION`, `MANUSCRIPT_PROVED`, `MANUSCRIPT_SKETCH`, `MANUSCRIPT_STATEMENT_ONLY` for work belonging to the manuscript; determine whether the claim is original/manuscript-local or a restated standard fact before choosing a policy.
- `EXTERNAL_CITED`, `EXTERNAL_UNCITED_STANDARD` for results originating in established literature. An uncited standard result requires finding and recording a precise reputable mathematical source before admission.

Trust statuses (add these distinctions without erasing existing provenance or history):

- `KERNEL_PROVED`: requirement discharged using Lean proofs with no admitted external axioms among its transitive dependencies. Record `COMPLETE` in the existing ledger only when this is true.
- `CITED_ASSUMPTION`: exact externally established theorem is isolated as a named admitted Lean declaration; **not** `COMPLETE`.
- `CONDITIONAL_PROOF`: the manuscript-facing Lean proof is finished but transitively depends on one or more `CITED_ASSUMPTION` declarations; **not** unconditionally `COMPLETE`.
- `UNRESOLVED`: still missing an adequate proof, exact source, or statement design.

If adding a new ledger status column would disrupt current tooling, keep the original columns intact and maintain `Matroid/PROOF_STATUS.csv` with `id`, `mathematical_source`, `trust_status`, `admitted_premises`, `proof_declaration`, `reference`, `budget_record`. Make ledger status and the new file agree explicitly. Never set a row to `COMPLETE` simply because it builds with `sorry`.

**Two depth reports are mandatory:** (a) unconditional kernel-certified depth, and (b) depth completed *relative to cited assumptions*. For citation-relative frontier calculations only, `KERNEL_PROVED`, `CITED_ASSUMPTION`, and `CONDITIONAL_PROOF` may count as available premises; for unconditional certification only `KERNEL_PROVED` counts. Do not obscure this difference under one `COMPLETE` flag.

## 4. Proof attempt order, for every node

1. Read the exact ledger entry and manuscript location or semantic use; inspect the actual proof if present.
2. Fix the mathematical statement and hypotheses **before** looking for library lemmas. Record a short mathematical proof/construction plan.
3. Search the project's pinned mathlib and already imported proved dependencies. Reuse exact results first; add manuscript-facing bridges if needed.
4. Implement and test a precise Lean signature. Compare indexed elements, finite sets, loops, contractions, ground sets, dimensions, and positivity assumptions with the manuscript.
5. Prove the statement locally, or apply the external-result policy below if—and only if—the obligation is eligible.
6. Update proof provenance, status, import tree and any justified direct dependency edges. Run `lake build` and validate final axioms.

Do not silently weaken a theorem to match available library infrastructure. A narrower lemma is useful as partial progress but is not closure of the canonical requirement.

## 5. Resource threshold for established external results

**Default cumulative budget per external mathematical theorem, across all Codex sessions/passes:**

- Up to **10 minutes** of focused manuscript/literature/mathlib reconnaissance.
- Up to **20 minutes** for a first serious mathematical Lean proof route.
- One further **20-minute** attempt only if it has a distinct concrete route or demonstrable progress.
- **Stop at approximately 50 minutes total** (or sooner after two unsuccessful proof routes); do not reset the budget on a new run or after discovering a helper lemma.
- Secondary safeguard: at most **12 substantive Lean edit–check/debug cycles** in total for that external theorem, whichever cutoff is reached first. A cycle includes a meaningful attempted proof change followed by Lean feedback; do not artificially split cycles.

These are policy budgets, not promises that an autonomous model can enforce accurate wall-clock/token limits. Log real elapsed time and token figures **only if accessible**; do not fabricate them. Codex session usage may be available via its CLI interface, but individual theorem token accounting is not guaranteed. If time measurements are unavailable, use the **two-attempt / twelve-cycle** safeguards, with recorded checkpoints. A hard clock or token cutoff requires an external runner, not merely `AGENTS.md`.

Record in `Matroid/PROOF_BUDGET.md` per external theorem: ledger ID, source, first-attempt date, accumulated verified time (or `UNKNOWN`), observed tokens if available (or `UNKNOWN`), attempt count, check/debug cycles, proved intermediates, precise remaining goal, and final disposition. Never silently restart the cumulative budget. N268 is the motivating historical example, **not** a precedent requiring future standard topology to be rebuilt.

A meaningful exception requires explicit user authorization. If a cited external result is one small lemma away from closing, record that fact, preserve the buildable partial work, and request a decision in the end-of-pass report rather than automatically spending another unbounded run.

### Admission gate (all required)

`CITED_ASSUMPTION` is permitted only if:

1. The requirement is genuinely established external mathematics; **no manuscript-local/original result** is being admitted.
2. A specific source, theorem/section or exact proof location, and its relevant hypotheses have been inspected. `EXTERNAL_UNCITED_STANDARD` alone does not suffice.
3. The Lean statement is checked against that source and the manuscript use: no stronger conclusion or missing hypotheses; graph/matroid indexing conventions are reconciled.
4. A good-faith mathlib/proof search and the bounded attempt budget are logged, including the precise remaining obligation.
5. The admission is **one narrow theorem**, not an entire module, blanket assumption, or downstream manuscript theorem.
6. The admitted theorem is isolated in a mathematically named file under `Matroid/External/`, with a nearby source citation, ledger ID, explicit admission comment and `sorry`. Do not write `axiom`, do not hide the admission with a helper alias, and do not scatter `sorry` in ordinary mathematical files.
7. Transitive dependents are marked `CONDITIONAL_PROOF` and their `#print axioms` result is recorded.

If exact citation/assumptions are uncertain, leave the node `UNRESOLVED` rather than asserting a source supports it.

### Manuscript results: no admission

N049, N137, and N143 are explicitly manuscript-proved. Their mathematical claims must be formally proved in Lean. They may rely on a precisely documented admitted **external** theorem, but then they are `CONDITIONAL_PROOF`, not unconditionally certified. Never place `sorry` in a manuscript result or treat an external citation as a substitute for its project-specific argument.

## 6. Mathematical priorities within depth 5

Work on the exact/easier structural facts first: N026, N028, N029, N045, N131, N134, N264. Then tackle the manuscript proofs N049, N137, N143 and the extension/row bridge facts N041/N262. Treat N053 and N125 as the main candidates for bounded external proof effort, **not** automatic admissions.

- **N049:** use the manuscript's quotient-by-span proof for arbitrary, possibly dependent contraction sets. Do not prove only independent-set contraction.
- **N137:** use basis factorization and the existing weighted-basis sums; preserve the target-free factor and zero-denominator conventions from the manuscript.
- **N143:** prove the nonspanning-target / coloop equivalence in the specified restriction; do not admit the local zero-case argument.
- **N053:** build from the already-checked TU minor nonvanishing bridge and N044 represented rank. Check the arbitrary-field quantifier, including characteristic 2, before concluding regularity.
- **N125:** isolate precisely what rectangular weighted Cauchy–Binet is missing; prefer proving/admitting *that exact standard identity* and proving the TU basis-indicator filtering locally. Do not admit the entire manuscript-use weighted-basis theorem when a smaller external prerequisite suffices.
- **N262:** check that row deletion preserves the claimed **reconstruction equations**, not merely rank or the represented matroid.
- **N264:** handle loops and parallel labeled graph edges consistently with N061; include the loop convention in the path criterion.

Maintain topical Lean source files (`Matroid/Minors.lean`, `Matroid/Representation.lean`, `Matroid/TotallyUnimodular.lean`, `Matroid/Graphic.lean`, etc.). Avoid `Depth5.lean`, `Frontier5.lean`, and other chronological code files.

## 7. Build, axiom audit, and stop

After meaningful groups of targets and once at the end, run `lake build`. Do not leave failed/unfinished proof code in live modules. Source-scan the entire project for `sorry`, `admit`, and `axiom`: any `sorry` must correspond **exactly** to an approved, indexed `Matroid/External/` declaration; any other occurrence is a blocker. Run `#print axioms` for each new project-facing depth-5 theorem, paying attention to `sorryAx`; imported trusted foundational axioms such as `propext`, `Classical.choice`, `Quot.sound` are not cited admissions.

For each target, update `FORMALIZATION_LOG.md` with manuscript evidence, proof plan, Lean declaration, exact formal dependencies, proof route, budget, trust status, and build/axiom outcome. Record all external sources in `SOURCES.md`. Recompute the DAG and depth table after justified graph corrections, preserving direct edges only and explaining every change. Retain the original mathematical provenance; do not rewrite the manuscript to accommodate a convenient Lean proof.

Final report must include:

- the 14-node frozen snapshot and result for each node;
- which are `KERNEL_PROVED`, `CITED_ASSUMPTION`, `CONDITIONAL_PROOF`, or `UNRESOLVED`;
- an exact list of the cited admitted theorems and their literature references;
- cumulative proof effort and the concrete unresolved obstruction for each admission/blocker;
- the kernel-certified depth, the citation-relative depth, any DAG repairs, and the next mathematical frontier.

**Stop after this one depth-5 attempt. Do not start depth 6**, even if depth 5 is citation-relatively clear. No automatic multi-depth or perpetual loop.
