# Matroid Lean Reorganization and High-Leverage Blocker Pass

This repository is formalizing the matroid mathematics required by the manuscript from the bottom of an audited dependency graph upward.

The first foundational Lean boundary has been completed.

A subsequent full-frontier pass completed most of the exposed targets but left several blockers.

This task has exactly two phases:

1. reorganize the existing Lean source tree by mathematical subject;
2. attack the highest-leverage unresolved blockers.

Do not recursively continue into newly exposed frontier nodes during this task.

The intended workflow is:

```text
reorganize existing code without changing mathematics
        ↓
verify build
        ↓
repair blocker-related dependency metadata
        ↓
attack N025, N043, N061, N062
        ↓
update ledger and formalization log
        ↓
recompute resulting frontier
        ↓
report it
        ↓
STOP
```

---

# 1. Mathematical source of truth

The frozen manuscript is:

```text
Manuscript/main.tex
```

The canonical formalization specification is:

```text
Matroid/LEDGER.md
```

The direct internal prerequisite graph is:

```text
Matroid/DEPENDENCY_EDGES.csv
```

The formalization history is recorded in:

```text
Matroid/FORMALIZATION_LOG.md
```

For every theorem or construction implemented in this task:

1. read the canonical ledger entry;
2. inspect the exact manuscript statement and surrounding proof or derivation;
3. determine the manuscript proof plan;
4. only then inspect mathlib;
5. implement a manuscript-faithful Lean statement;
6. document any meaningful deviation in proof route.

Use exact TeX labels for provenance.

Do not silently strengthen, weaken, or replace manuscript statements.

---

# 2. Phase A: reorganize Lean source by mathematics

The current Lean source contains filenames reflecting implementation chronology, such as:

```text
Basic.lean
Frontier2.lean
```

These names should not remain part of the long-term source organization.

Lean files should be organized by mathematical subject, not by formalization pass.

Historical information about when a declaration was implemented belongs in:

```text
Matroid/FORMALIZATION_LOG.md
logs/
```

not in module names.

---

# 3. Remove the chronological `Internal` organization

If the current source tree contains:

```text
Matroid/Internal/Basic.lean
Matroid/Internal/Frontier2.lean
```

move their declarations into mathematically named modules directly under:

```text
Matroid/
```

The desired structure after reorganization is approximately:

```text
Matroid/
├── Matroid.lean
├── RankClosure.lean
├── Representation.lean
├── Cycles.lean
├── Colored.lean
├── Uniform.lean
├── Pointed.lean
├── WeightedBases.lean
├── ThreeSum.lean
├── Minors.lean
├── Graphic.lean
│
├── LEDGER.md
├── DEPENDENCY_EDGES.csv
├── ENTRY_NODES.md
├── FORMALIZATION_LOG.md
└── ...
```

Only create modules that contain actual declarations.

Do not create empty placeholder modules merely to anticipate future work.

If `Matroid/Internal/` becomes empty, remove it.

---

# 4. Expected relocation of existing declarations

Reorganize existing declarations according to mathematical content.

The expected placement is approximately:

## `Matroid/RankClosure.lean`

Existing basis/rank/closure bridges, including declarations corresponding to:

```text
N003
N006
N007
N016
```

and related local helpers.

Examples currently include declarations analogous to:

```text
isBasis_ncard_eq
isBasis_eRk_eq_ncard
indep_ncard_le_isBasis_ncard
mem_closure_iff_eRk_insert_eq
mem_closure_iff_exists_circuit_sdiff
```

---

## `Matroid/Cycles.lean`

Circuit/cycle operations and results such as the existing circuit-union material.

---

## `Matroid/Colored.lean`

The colored-matroid definitions or wrappers introduced for the completed frontier.

---

## `Matroid/Representation.lean`

Representation-related declarations such as:

```text
Represents
RepresentableOver
```

and the new N043 work described below.

---

## `Matroid/Uniform.lean`

Uniform-matroid declarations and bridges.

---

## `Matroid/Pointed.lean`

Pointed-matroid and target-support material, including declarations analogous to:

```text
minimal_spanning_iff_circuit
positiveTargetSupport
```

---

## `Matroid/WeightedBases.lean`

Weighted basis-sum definitions and related elementary API.

---

## `Matroid/ThreeSum.lean`

The five-class triangle/3-sum boundary result corresponding to N158 and its local helpers.

---

## `Matroid/Minors.lean`

Restriction/contraction mathematics, including completed minor-related material and the N025 blocker.

---

## `Matroid/Graphic.lean`

Graphic and cographic matroid constructions corresponding to N061 and N062.

---

# 5. Reorganization must not change mathematics

Phase A is a source-layout refactor only.

During the reorganization:

- preserve declaration names unless a name is genuinely misleading;
- preserve theorem statements;
- preserve proof bodies;
- preserve ledger IDs and manuscript provenance;
- update imports only as necessary;
- do not opportunistically simplify or rewrite proofs.

The objective is to make the source tree mathematically legible without mixing refactoring with theorem changes.

After reorganization, run:

```text
lake build
```

Do not begin Phase B until the reorganized repository builds successfully.

Record the reorganization briefly in `FORMALIZATION_LOG.md`, but do not create fake ledger entries for file moves.

---

# 6. Public import point

`Matroid/Matroid.lean` remains the public umbrella import.

It should import the mathematically named modules needed to expose the current project API.

A downstream user should continue to be able to write:

```lean
import Matroid.Matroid
```

Do not force downstream code to know the historical organization of the formalization.

Avoid unnecessary import cycles.

---

# 7. Phase B: high-leverage blocker pass

After the source reorganization builds, attack these unresolved targets:

```text
N025  Contraction rank
N043  Vector matroid
N061  Graphic matroid
N062  Cographic matroid
```

These are the primary targets of this pass because they block substantial downstream portions of the dependency graph.

Do not automatically attack every newly exposed node after completing them.

---

# 8. Dependency-graph repair: N061 → N062

Before formalizing N062, inspect its manuscript definition.

The manuscript defines the cographic matroid through duality from the graphic matroid.

Therefore verify whether the direct edge:

```text
N061 → N062
```

is absent from:

```text
Matroid/DEPENDENCY_EDGES.csv
```

If absent, add it with the appropriate edge type and manuscript evidence.

The expected type is likely:

```text
DEFINITIONAL
```

because the cographic construction is stated in terms of the graphic matroid and duality.

Do not add the edge mechanically without checking the exact manuscript formulation.

Record the correction in `FORMALIZATION_LOG.md`.

---

# 9. Scope correction: N261

N261 was exposed as a frontier node but the previous pass found that its content is fundamentally a matrix/TU row-restriction statement rather than a reusable matroid API fact.

Reinspect:

```text
N261
```

against `Manuscript/main.tex`.

If that assessment remains correct:

- change its scope so that it is no longer an active Matroid formalization node;
- preserve the ledger entry for provenance;
- record clearly that it belongs to a future matrix/TU formalization layer;
- remove it from active Matroid frontier calculations.

Do not delete the entry.

Do not write Lean for N261 in this pass.

If manuscript inspection instead reveals a distinct pure matroid statement hidden inside N261, extract that fact explicitly rather than forcing the matrix theorem into the Matroid library.

---

# 10. Proof-guided workflow for blockers

For each of N025, N043, N061, and N062, follow:

```text
ledger entry
    ↓
exact manuscript statement
    ↓
manuscript proof / derivation
    ↓
mathematical proof plan
    ↓
mathlib reconnaissance
    ↓
Lean statement
    ↓
proof / construction
    ↓
lake build
    ↓
ledger + log update
```

Do not begin with mathlib search.

The manuscript determines what must be formalized.

---

# 11. Manuscript proof classifications

Use:

```text
MANUSCRIPT_PROOF
MANUSCRIPT_SKETCH
MANUSCRIPT_STATEMENT_ONLY
MANUSCRIPT_DEFINITION
```

as appropriate.

For theorem-like targets, record a mathematical proof plan before implementation.

For construction targets, record:

- the mathematical object being constructed;
- the intended ground type;
- the independence structure;
- why the construction satisfies the matroid axioms;
- how the resulting object corresponds to the manuscript definition.

---

# 12. N025 — contraction rank

N025 is a high-priority blocker.

Formalize the manuscript's contraction-rank requirement faithfully.

Before implementation:

1. inspect the exact manuscript formulation;
2. inspect the existing project definitions and mathlib contraction API;
3. identify whether the desired result is:
   - already exact in mathlib;
   - obtainable by a short rank/cardinality bridge;
   - or requires a local proof.

Prefer:

```text
MATHLIB_EXACT
```

or:

```text
MATHLIB_BRIDGE
```

when possible.

If a local proof is required, follow the manuscript's mathematical derivation where available.

Do not introduce an alternative contraction definition merely to make the theorem easier.

Place project-local declarations in:

```text
Matroid/Minors.lean
```

unless manuscript inspection strongly indicates another mathematical home.

---

# 13. N043 — vector matroid

N043 is the representation-side construction of a matroid from a finite vector configuration.

This is a high-priority blocker.

Use mathlib's existing matroid abstraction and construction machinery.

Do not introduce a competing foundational `Matroid` type.

Before implementation:

1. inspect the manuscript definition;
2. identify the intended ground set/index type;
3. formulate independence as linear independence of the corresponding vectors;
4. inspect mathlib for an existing vector/linear-independence matroid constructor;
5. if no exact constructor is available, use the appropriate general matroid-construction interface rather than rebuilding the whole theory.

The final project-facing object must correspond transparently to the manuscript's vector matroid.

Record precisely how the Lean construction matches the manuscript definition.

Put this work in:

```text
Matroid/Representation.lean
```

---

# 14. N061 — graphic matroid

N061 is the construction of the graphic matroid.

Before implementing it, inspect the manuscript's graph conventions carefully.

In particular determine whether the manuscript requires:

- ordinary graphs;
- multigraphs;
- loops;
- parallel edges;
- a specified edge ground type.

Do not silently replace the manuscript's graph model with a simpler graph type that changes the associated cycle matroid.

Inspect mathlib's graph types only after the manuscript requirements are fixed.

The intended graphic matroid should have:

```text
ground elements = graph edges
independent sets = forests
```

or the exact manuscript-equivalent formulation.

Use existing graph/forest theory from mathlib where possible.

Do not manually reprove large amounts of graph theory if existing definitions suffice.

If no suitable ready-made graphic-matroid constructor exists, construct it using a mathematically appropriate matroid-construction API and prove the required augmentation/exchange property.

Place the resulting code in:

```text
Matroid/Graphic.lean
```

Record any meaningful mismatch between manuscript graph conventions and mathlib graph types.

---

# 15. N062 — cographic matroid

Do not attempt N062 independently of N061.

First complete or adequately establish the graphic matroid construction.

Then implement the manuscript's cographic matroid through matroid duality.

Prefer the conceptual construction:

```text
cographic(G) = (graphic(G))*
```

when this matches the manuscript.

Use mathlib's existing matroid dual operation.

Do not build the cographic matroid from scratch through cut spaces unless the manuscript actually requires a different formulation.

Record the exact dependency on N061.

Place the construction in:

```text
Matroid/Graphic.lean
```

unless the amount of dual-specific material later justifies a separate module.

---

# 16. N080 is not a primary target

N080 remains an unresolved standalone theorem concerning finite closure/exchange representation.

It currently has little or no downstream blocking effect.

Do not prioritize it ahead of N025, N043, N061, or N062.

If all four high-leverage blockers complete cleanly and substantial task budget remains, N080 may be investigated.

However:

- do not allow N080 to delay completion of this pass;
- do not start downstream frontier nodes after resolving it.

If attempted, use the same manuscript → mathlib → Lean discipline.

---

# 17. Blocker outcomes

For each primary blocker, one of the following outcomes is acceptable:

```text
COMPLETE
BLOCKED_MATHLIB_INFRASTRUCTURE
BLOCKED_STATEMENT
BLOCKED_SCOPE
BLOCKED_PROOF
```

A blocker classification must be accompanied by a precise explanation.

Do not use a blocker status merely because the proof is inconvenient.

Continue with independent targets after one target blocks.

---

# 18. Formalization log

Continue:

```text
Matroid/FORMALIZATION_LOG.md
```

For every primary target record:

```text
Ledger ID:
TeX label:
Requirement:
Manuscript proof status:
Manuscript proof plan:
Lean declaration:
Formalization source:
Mathlib declarations used:
Deviation from manuscript proof:
Result:
Downstream effect:
Build status:
Notes:
```

For constructions, adapt the proof-plan field to record the construction plan.

The log should make clear why a blocker was or was not discharged.

---

# 19. Ledger updates

Update the corresponding rows in:

```text
Matroid/LEDGER.md
```

only when justified.

Use formalization sources:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

and statuses consistent with the existing ledger scheme.

Use `COMPLETE` only when:

- the manuscript-facing requirement has been fully discharged;
- provenance is recorded;
- and the repository builds.

For N261, update scope rather than pretending it failed formalization.

---

# 20. No placeholders

Do not use:

```text
sorry
admit
axiom
```

to close a blocker.

If a theorem cannot be completed, leave the repository buildable and document the blocker.

Do not add permanent assumptions merely to expose downstream nodes.

---

# 21. Recompute the frontier once

After:

- the source reorganization is complete;
- N261 has been re-scoped;
- the N061 → N062 edge has been corrected if necessary;
- and all four primary blockers have been attempted;

recompute the active unresolved frontier mechanically from:

```text
Matroid/LEDGER.md
Matroid/DEPENDENCY_EDGES.csv
```

Create or update:

```text
Matroid/FRONTIER.md
```

with:

## Completed blocker results

List the outcome for:

```text
N025
N043
N061
N062
```

## Remaining blockers

List any unresolved primary blockers and the descendants they continue to block.

## Newly exposed frontier

List all active unresolved nodes whose direct internal prerequisites are now complete.

Do not formalize those newly exposed nodes during this task.

---

# 22. Historical pass artifacts

Chronological frontier artifacts such as:

```text
FRONTIER_PASS_2.md
```

should not remain part of the long-term active mathematical API.

Once their information has been incorporated into the formalization log and current frontier state, move them under an appropriate logs directory such as:

```text
logs/formalization/
```

Preserve them for methodological history.

Do not delete historical evidence.

The active `Matroid/` directory should emphasize:

```text
mathematical Lean modules
canonical ledger
dependency graph
current frontier
formalization log
```

rather than past pass numbers.

---

# 23. Files that must remain fixed

Do not modify:

```text
Manuscript/main.tex
logs/dependency_audit/
```

except to read them.

Do not rewrite historical ledgers or audit artifacts.

`Matroid/DEPENDENCY_EDGES.csv` may be modified only for justified graph corrections discovered in this pass, particularly the N061 → N062 issue.

Document every such correction.

---

# 24. Build discipline

Run:

```text
lake build
```

after the source reorganization.

Run it repeatedly during blocker work.

Run it again before finishing.

The repository must finish in a buildable state.

---

# 25. Stop condition

This task is complete when:

1. chronological Lean files have been reorganized into mathematically named modules;
2. the reorganized source tree builds;
3. N261 has been re-adjudicated and re-scoped if appropriate;
4. the N061 → N062 dependency has been checked and corrected if appropriate;
5. N025 has been attempted;
6. N043 has been attempted;
7. N061 has been attempted;
8. N062 has been attempted after N061;
9. every result or blocker is recorded in the ledger and formalization log;
10. `lake build` succeeds;
11. the resulting active frontier has been recomputed and recorded;
12. no newly exposed frontier node has been formalized.

Stop at that point.

Do not begin another general frontier pass.