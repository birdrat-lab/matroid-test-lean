# AGENTS.md — Depth-7 Matroid-First Formalization Pass

## Mission and certified baseline

Work only on the currently active **structural depth 7** of the formalization of `Manuscript/main.tex`. The current source archive (2026-10-13) has 197 active requirements, 448 active direct dependency edges, and maximum recorded structural depth 12. Depths 0–5 are kernel-certified. At depth 6, **21 of 22 requirements are kernel-proved**; **N052** is available only as an explicitly cited, admitted external premise. Citation-relative certification reaches depth 6; unconditional kernel certification reaches depth 5. There are 89 kernel-proved active nodes. Do not change these numbers except after recomputation from the current files.

The frozen *candidate* depth-7 set has **34 unresolved IDs**:

`N018 N034 N055 N059 N068 N106 N118 N138 N144 N146 N149 N152 N161 N162 N163 N169 N170 N172 N173 N175 N182 N185 N186 N193 N194 N195 N204 N218 N225 N238 N239 N244 N255 N267`.

Verify this list mechanically against `Matroid/LEDGER.md`, `Matroid/DEPENDENCY_EDGES.csv`, and `Matroid/DEPTHS.csv` before proving anything. All active direct prerequisites of depth-7 nodes are at depths <= 6, hence no depth-7 theorem is an actual prerequisite of another depth-7 theorem in the present DAG. If an *essential mathematical* dependency is missing, record its direct edge, recompute **all** depths, and re-freeze the in-scope layer. Do not hide same-depth dependencies to preserve the schedule. Stop before attempting any depth-8 theorem. A partial depth-7 pass is acceptable if targets exhaust their allotted focused attempts; report the remaining frontier precisely.

## Authoritative material

Read first, in this order:

1. `Manuscript/main.tex` (exact definition/proposition, hypotheses, and proof or cited source).
2. `Matroid/LEDGER.md` (atomic requirement, provenance, scope).
3. `Matroid/DEPENDENCY_EDGES.csv` and `Matroid/DEPTHS.csv` (direct mathematical prerequisites).
4. `Matroid/DEPTH6_AUDIT.md`, `Matroid/Depth6AxiomAudit.lean`, `Matroid/PROOF_STATUS.csv`, `Matroid/PROOF_BUDGET.md`, `Matroid/FORMALIZATION_LOG.md`, `Matroid/SOURCES.md`.
5. Existing proof modules, then pinned mathlib. The project pins Lean/mathlib `v4.35.0-rc3`.

Do not substitute a downstream use for the actual manuscript assertion. Preserve the source's distinction between definitions, proved propositions, externally cited facts, and finite certificate-derived claims. A claimed `COMPLETE` row or a passing `lake build` is not by itself a statement-correspondence audit.

## Mandatory matroid-first proof search

**This is a real proof-search constraint, not a ban on matrices or graphs.**

For *every* target, before implementing a proof, write in the formalization log:

- The **exact manuscript-level statement** and the minimal abstract hypotheses it uses.
- A **matroid-only proof candidate** using bases, circuits/cycles, rank, closure, deletion/contraction, duality, flats, or weighted basis sums. Inspect existing matroid/mathlib APIs first.
- Whether a realization is **logically necessary** (e.g. total unimodularity, projective equivalence, explicit determinant, a particular graphic representation, or finite `R10` certificate) or merely convenient.
- If using a matrix or graph, one sentence stating **which representation-specific step cannot reasonably be avoided**, and a precise bridge returning the result to the general matroid interface.

Preference hierarchy:

1. Prove general matroid statements on arbitrary finite matroids, preferably under the weakest hypotheses supported by the manuscript proof.
2. If the proof needs binary/regular representability, isolate a **single bridge lemma** and carry out the remaining argument with matroid objects; use `[regular]` only where needed.
3. Use concrete graphs and matrices for **explicit** `R10`, `K4`, `K3,3`, TU, and coordinate/determinant calculations, not as replacements for an abstract 2-sum or closure theorem.
4. Budget-admit a precisely identified *external standard theorem* only under the trust rules below. Do not turn the desired manuscript result into a hypothesis or a definition.

No unnecessary graphic specialization of general sums. Do not call a theorem “matroidal” if its interface assumes an arbitrary chosen representation when the manuscript claims it for every matroid in the specified class. Conversely, do not force a purely abstract argument for a genuinely coordinate-based determinant statement; separating representation input from matroid output is the goal.

## Proof/admission and resource policy

- **MANUSCRIPT_PROVED, MANUSCRIPT_DEFINITION, and manuscript-specific CERTIFICATE_DERIVED requirements must never be admitted.** Definitions need exact faithful interfaces; claimed facts need proved consequences. A manuscript proof may depend on a *separately admitted, independently established external theorem*, but then its trust classification is `CONDITIONAL_PROOF`, not `KERNEL_PROVED`.
- For an **EXTERNAL_CITED** or **EXTERNAL_UNCITED_STANDARD** requirement, attempt a real proof first. Default cumulative budget: ~10 minutes reconnaissance plus at most **two focused 20-minute routes**, with up to **12 observed substantive edit/check cycles** over *all* passes. Stop earlier after two unproductive proof routes. Allow at most one documented extra cycle for a nearly closed goal; do not repeatedly extend or reset the budget. If per-node time/tokens are unavailable, record `UNKNOWN`, not invented values. The count of substantive edit-plus-Lean-feedback cycles is the auditable fallback.
- Admit only a **precise literature theorem**, with actual source, location, matching hypotheses, and a minimal theorem signature in `Matroid/External/<Subject>.lean`, after budget exhaustion. Mark it `CITED_ASSUMPTION`; downstream proof is conditional. Never use `sorry` to bypass matrix/graph bridging that is manuscript-local or to suppress a genuine counterexample/statement mismatch.
- N052 remains a **cited premise**, not a kernel theorem: `Matroid.External.regular_ground_exists_realTU` in `External/TutteRegularTU.lean`. You may use `Matroid.Regular.hasLabeledRealTU`, but record the resulting **transitive `sorryAx`** for N055, N059, N118, or anything else that actually imports the premise. Do not attempt to reprove Tutte's full theorem as part of depth 7 unless a short library bridge has genuinely appeared.
- Use four distinct proof states in `PROOF_STATUS.csv`: `KERNEL_PROVED`, `CITED_ASSUMPTION`, `CONDITIONAL_PROOF`, `UNRESOLVED`. `LEDGER.md` `COMPLETE` is reserved for admission-free proofs. Do not reclassify a cited prerequisite as kernel-proved just because downstream Lean code typechecks.
- Manuscript-local work has no admission-based exit. If it stalls after ~12 substantive cycles, preserve compiling intermediate lemmas, the exact remaining goal and hypotheses, record it as unresolved, and move to another **independent** depth-7 target. Do not spend N268-scale resources on a single secondary theory.

## Attack order: abstract structural claims first

### A. Matroidal foundations and short consequences

Attack **N018** (cocircuit = complement of hyperplane), **N034** (modular cut axioms), **N106** (minimal positive support via target circuits), **N144** (contraction makes a spanned element a loop; weight convention), **N149** (proper 2-sum ground cardinality), and **N175** (cographic minor closure).

- Prefer matroid `dual`, hyperplanes, finite closure, `IsCircuitUnion`, and the existing N174 graphic minor theorem. For N175, derive the cographic statement **through duality and N174**, preserving labels, loops and parallel edges. Do not construct another graph contraction theory.
- For N106, include target excluded from availability and the exact `|C|-1` minimum, not merely the existence of a spanning circuit.
- For N144, keep the loop/extended-weight interpretation separate from the elementary matroid lemma.

### B. Matroidal 2-sum and recursive ports

Attack **N138** (proper 2-sum basis correspondence), **N146** (target circuit gluing), **N152** (2-circuit child collapses to a relabeling), **N204** (parallel target copy), **N218** (recursive pointed construction), and **N068** (regularity preservation).

- Start from N065's **abstract, labeled cycle characterization** and the ordinary basis/circuit/duality axioms. The finished N065 uses a binary quotient internally; this does not license expressing every downstream theorem as a matrix calculation.
- Require exact nonloop/noncoloop, shared-port, size, disjointness, and target-retention hypotheses. Record whether `N138` follows directly from circuit/cocircuit exchange. Keep union of *cycles* distinct from a single *circuit*.
- N204 is `STATEMENT_DESIGN`: write its precise source-matched statement before proof; do not manufacture a theorem by defining the answer. Confirm that parallel addition and subsequent 2-sum preserve the intended target label.
- N068 is externally cited regularity of a proper 2-sum. Try an abstract closure route or an existing regular/binary/representability theorem first. If an arbitrary-field representation bridge is required, isolate it; apply the external budget rather than rebuilding Seymour theory.

### C. Triangle identities and positivity (priority manuscript work)

Attack **N162**, **N163** (positivity of the `a` and `c` classes), **N161** (the identity `a*c = p1*p2 + p1*p3 + p2*p3`), and **N267** (five weighted `K4` triangle classes).

- N162/N163 must use the actual coindependent triangle, basis-extension, and **strictly positive weights**; do not silently assume a contributing subset exists. Express the proof in bases/closure if possible.
- For N161, first seek a **basis-generating / matroid polynomial** proof using `weightedTrianglePhi` (N266) and existing weighted-basis identities. The manuscript's determinant/Plücker argument is permitted as an isolated bridge if an intrinsic route is not reasonably available; prove the identity for the manuscript's full coindependent regular-triangle hypotheses, including all zero-class cases. Do not assume all `p_i>0` (that is the later replacement theorem's hypothesis, not this identity's).
- For N267, a concrete `M(K4)` calculation is the stated object, so explicit edge enumeration is appropriate; package the result as the **five matroid closure-class sums** in the manuscript's `(a,p1,p2,p3,c)` order, not just a graph path count.

### D. Quotient, circuit signs, and representation-specific facts

Attack **N244** (fundamental-circuit support of the free relation basis), **N059** (regular free quotient form), **N055** (real projective uniqueness of regular representations), and **N118** (signed TU circuit dependency).

- N244 is a **matroid basis/fundamental circuit** claim; use N243, then relate the nonzero response coordinates to the represented dependence. Include zero coefficient response labels and the positive relation label itself.
- N059 is manuscript-proved: formalize **both** directions, including finite disjoint relation labels, deletion giving the *free* matroid, regularity of the extension, and contraction giving the original matroid with identity on `E`. Use N052's admitted regular→TU **only at the exact point the manuscript does**. Its final result is `CONDITIONAL_PROOF` if that premise is transitive, regardless of a completed local proof.
- N055 and N118 are external and potentially expensive. Attempt precise, short proofs using existing APIs; if the source requires a large representation uniqueness or circuit-sign theory, apply the external budget. Do not confuse regularity with arbitrary real representability or assume projective equivalence for general nonregular matroids.

### E. Explicit finite `R10` certificates and applications

Attack **N169** (4-/6-circuit counts), **N170** (no triangles), **N172/N173** (each labeled deletion/contraction is graphic/cographic `K3,3`), **N182** (162 bases), **N185** (automorphism order 720), **N186** (element transitivity), **N193/N194** (pointed determinant and cofactor), **N195** (six matchings plus nine double-star minimal supports), **N225** (neither graphic nor cographic), **N238** (256/256 closure balance), **N239** (two five-sensitive witnesses), and **N255** (connectedness).

- First derive **matroid-level finite predicates** from the already verified **exact N070 5x10 TU matrix**. Reuse a kernel-proved circuit/basis/closure oracle or a sound finite certificate checker; avoid duplicating determinant enumeration for every invariant. All element labels and relabeling/isomorphism witnesses must be explicit.
- For N172/N173, exhibit a labeled isomorphism (or an explicitly proved equivariant relabeling) with `M(K3,3)` / its dual. A mere rank/circuit-count match is not sufficient. Explicit graph/matrix witnesses are legitimate *only here*.
- For N185/N186, prove automorphism completeness and the group order/transitivity, not just 720 exhibited permutations or one element orbit. If cost grows, build sound finite verification certificates rather than hand-coded permutation case trees.
- For N193/N194, determinants and cofactors are intrinsic to the manuscript assertion; a representation-based proof is appropriate. Preserve the precise pointed basis-polynomial factors and indexed coordinates.
- For N195, distinguish six perfect matchings and nine `R_i∪C_j` supports as **matroid minimal spanning sets**, not just patterns in N207's separate graphic program.
- N255 has `PROVENANCE_UNRESOLVED` in the ledger: audit its actual manuscript role and whether it is a genuine mathematical prerequisite before certifying. Do not claim that a generic matroid connectivity proof automatically yields the R10 fact.
- The `CERTIFICATE_DERIVED` labels do not authorize a `sorry`: these are claims about the manuscript's *specific finite object* and must have a sound, kernel-checked certificate or remain unresolved. External literature may guide construction but cannot replace the promised local verification without explicit reclassification/review.

## Workflow, integrity, and deliverables

For each target:

1. Record the manuscript quote/label and provenance and write a matroid-first proof plan; search existing pinned mathlib/project lemmas.
2. Implement the narrowest faithful public signature in **mathematically named modules** (`Matroid/…`), retaining separate graph/matrix certificates as necessary. Avoid chronological `Depth7Foo.lean` implementations except for the axiom audit.
3. Compile a focused module, run full `lake build` at stable checkpoints, and compare the **exact Lean theorem assumptions/conclusion** with the manuscript. Check degenerate cases (empty sets, loops, coloops, dependent port, zero weight, target exclusion) relevant to that theorem.
4. Add entries to `Matroid/DEPTH7_AUDIT.md` with target ID, exact source, public Lean declaration, dependency list, proof route (matroid-first or justified representation bridge), status, transitive admissions, deviations, and next step.
5. Update `Matroid/PROOF_STATUS.csv`, `Matroid/PROOF_BUDGET.md`, `Matroid/LEDGER.md`, `Matroid/FORMALIZATION_LOG.md`, `Matroid/FRONTIER.md`, `Matroid/DEPTHS.csv`, and `Matroid/DEPENDENCY_EDGES.csv` consistently. Update `SOURCES.md` for cited theorems or new verified external imports.
6. Commit and run `Matroid/Depth7AxiomAudit.lean` containing `#print axioms` for every final public result, its exact external premise, and any imported critical proof. Verify `sorryAx` and its transitive consumers. A project source scan must identify all `sorry`, `admit`, and `axiom`; **do not claim unconditional proof from a passing build**. Run `git diff --check`.
7. Report the **full depth-7 table**, differentiating kernel proofs, cited premises, conditional proofs, and unresolved/statement-design targets; verified budget observations versus unknown time/tokens; newly discovered direct edges; and **both** certified-depth notions. A user-facing source-level correspondence audit is required before moving deeper.

**Stopping rule:** Do no depth-8 proof work. If all depth-7 targets are kernel-proved except exact permitted external citations and conditional descendants, declare only **citation-relative** depth 7 and retain the correct lower unconditional depth. If some manuscript target remains blocked, stop with detailed work-in-progress artifacts rather than admitting it or claiming completion.
