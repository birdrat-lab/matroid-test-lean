# Complete the Remaining Topological Depth-2 Matroid Formalization

The active Matroid formalization is now complete through structural topological depth 1.

The current depth audit is:

```text
depth 0: complete
depth 1: complete
depth 2: 19 active nodes, 7 complete, 12 unresolved
```

This task attacks the **12 remaining unresolved active depth-2 requirements**.

The governing invariant is:

> **Never perform new formalization work at a greater topological depth while a valid active requirement remains unresolved at a smaller depth.**

For this pass:

```text
verify depths 0 and 1 remain clear
        ↓
freeze the 12 unresolved depth-2 targets
        ↓
attack every target
        ↓
repair missing direct prerequisites if genuinely discovered
        ↓
update Lean / ledger / log / graph
        ↓
recompute structural depths
        ↓
report whether depth 2 is clear
        ↓
STOP
```

Do not begin depth 3.

---

# 1. Canonical sources

The mathematical source of truth is:

```text
Manuscript/main.tex
```

The canonical requirement inventory is:

```text
Matroid/LEDGER.md
```

The direct dependency DAG is:

```text
Matroid/DEPENDENCY_EDGES.csv
```

The mechanically computed depth table is:

```text
Matroid/DEPTHS.csv
```

The current formalization boundary is:

```text
Matroid/FRONTIER.md
```

The formalization/provenance record is:

```text
Matroid/FORMALIZATION_LOG.md
```

The manuscript determines the mathematics.

The ledger determines the accepted formalization obligations.

The DAG determines direct internal prerequisites.

Mathlib determines how much proof infrastructure must be supplied locally.

---

# 2. Verify the breadth-first invariant before beginning

Recompute structural topological depth mechanically.

For an active node `v`:

```text
depth(v) = 0
```

when it has no active internal prerequisites, and otherwise:

```text
depth(v) = 1 + max(depth(u))
```

over direct active prerequisite edges:

```text
u → v.
```

Before doing any depth-2 proof work, verify:

```text
no unresolved active node has depth 0 or depth 1.
```

The expected state is:

```text
depth 0: clear
depth 1: clear
minimum unresolved depth: 2
```

If this is false, stop and investigate the ledger/DAG discrepancy.

Do not silently proceed deeper.

---

# 3. Freeze the depth-2 target set

The expected unresolved active depth-2 targets are exactly:

```text
N024  Deletion
N036  Single-element extension
N046  Represented circuits
N047  Projective equivalence
N051  Regularity
N056  TU pivot and standard form
N057  TU identity augmentation
N062  Cographic matroid
N111  Nonzero column rescaling
N112  Ambient linear isomorphism
N130  Corank-one uniform target circuit
N258  Incidence representation of a graphic matroid
```

Recompute this set mechanically from `DEPTHS.csv`.

Treat the list above as a sanity check, not as authority over the DAG.

Record the verified target snapshot in:

```text
Matroid/FRONTIER.md
```

under:

```text
## Active depth-2 target snapshot
```

Once verified, attack every unresolved node in the snapshot.

Do not add ordinary newly exposed depth-3 nodes to this pass.

---

# 4. Universal formalization workflow

For every target, work in this order:

```text
ledger requirement
        ↓
exact manuscript statement / context
        ↓
manuscript proof or derivation, if any
        ↓
mathematical proof / construction plan
        ↓
inspect pinned mathlib
        ↓
design manuscript-facing Lean statement
        ↓
implement
        ↓
lake build
        ↓
update ledger and formalization log
```

Do **not** begin from mathlib search and then reinterpret the manuscript around what the library happens to contain.

The Lean API should formalize the manuscript requirement.

Mathlib may compress the proof.

---

# 5. Proof-source classification

For every target, use the existing manuscript-source categories:

```text
MANUSCRIPT_DEFINITION
MANUSCRIPT_PROOF
MANUSCRIPT_SKETCH
MANUSCRIPT_STATEMENT_ONLY
EXTERNAL_CITED
EXTERNAL_UNCITED_STANDARD
```

Do not attribute a proof to the manuscript when the manuscript merely states or cites the result.

For project-local formalization source, use:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

as appropriate.

---

# 6. Source organization

Lean files must continue to be organized by mathematics, not by formalization chronology or depth.

Do not create:

```text
Depth2.lean
Frontier6.lean
Pass6.lean
```

Use or create mathematically named modules.

The expected homes for this pass are approximately:

```text
Matroid/Minors.lean
    N024

Matroid/Extensions.lean
    N036

Matroid/Representation.lean
    N046
    N047
    N111
    N112

Matroid/Regular.lean
    N051

Matroid/TotallyUnimodular.lean
    N056
    N057

Matroid/Graphic.lean
    N062
    N258

Matroid/Uniform.lean
    N130
```

This organization is advisory rather than rigid.

Do not create a new file for one trivial declaration if an existing mathematical module is clearly appropriate.

If new modules are created, import them transitively through:

```text
Matroid/Matroid.lean
```

---

# 7. N024 — Deletion

Canonical requirement:

```text
M \ A is M restricted to E(M) \ A.
```

Manuscript provenance:

```text
def:matroid-minors
```

This is a manuscript definition.

Prefer an exact mathlib definition or a transparent bridge.

Do not introduce a competing deletion operation.

The project-facing result should make the manuscript identity explicit if mathlib uses a differently named primitive.

Expected home:

```text
Matroid/Minors.lean
```

---

# 8. N036 — Single-element extension

Canonical requirement:

```text
A matroid on E ∪ {τ} restricting to the given matroid on E.
```

Manuscript provenance:

```text
def:single-element-extension
```

This is a definition, not Crapo's classification theorem.

Formalize only the notion required here.

The definition must preserve both pieces of manuscript data:

```text
ground set = E ∪ {τ}
restriction to E = N
```

Do not prematurely formalize modular-cut classification N037.

If mathlib has no exact predicate, a small project definition is appropriate.

Expected home:

```text
Matroid/Extensions.lean
```

---

# 9. N046 — Represented circuits

Canonical requirement:

> Circuits of a vector matroid are exactly minimally linearly dependent indexed subfamilies.

The manuscript states this immediately after `def:vector-matroid`.

Important:

> preserve the **indexed** formulation.

Distinct ground elements may represent equal vectors.

A loop may be represented by the zero vector.

Do not replace indexed dependence by dependence of the set of vector values.

Build directly on the completed vector-matroid construction N043.

The desired result should connect:

```text
Matroid.IsCircuit
```

to minimal failure of:

```text
LinearIndepOn
```

for the represented indexed family.

Expected home:

```text
Matroid/Representation.lean
```

---

# 10. N047 — Projective equivalence

Manuscript provenance:

```text
def:projective-equivalence
```

The manuscript defines projective equivalence of two representations of the same matroid over the same field by:

```text
an isomorphism between their column spans
+
one nonzero scalar for each nonloop ground element.
```

The definition must respect the manuscript's treatment of loops:

```text
loop columns remain zero;
no nonzero scalar datum is required for loops.
```

Do not replace the span-restricted isomorphism by an unnecessarily stronger isomorphism between arbitrary ambient spaces.

If a convenient equivalent formulation is used internally, expose a manuscript-faithful public definition or equivalence theorem.

Expected home:

```text
Matroid/Representation.lean
```

---

# 11. N051 — Regularity

Manuscript provenance:

```text
def:regular-matroid
```

Canonical requirement:

```text
A matroid is regular iff it is representable over every field.
```

This target is only the definition of regularity.

Do not pull Tutte's characterization or unique representability into N051.

First inspect pinned mathlib for an existing regular-matroid predicate.

If exact, use it.

Otherwise define the narrow manuscript notion in terms of the existing representation API.

Pay particular attention to Lean universe polymorphism when quantifying over fields.

Do not solve universe problems by weakening the mathematical statement to a fixed collection of fields.

Expected home:

```text
Matroid/Regular.lean
```

---

# 12. N056 — TU pivot and standard form

Canonical requirement:

> Pivoting a totally unimodular representation on a basis and permuting columns can put it into standard form `[I D]` without losing total unimodularity.

This is an external uncited standard fact used explicitly in manuscript proofs.

The principal manuscript occurrence is in:

```text
thm:regular-quotient-form
```

where a TU representation is transformed to:

```text
A = ( I_r  D ).
```

Do not prove a much broader matrix-normal-form theorem unless it is genuinely simpler.

The target should be strong enough to justify exactly the standard-form step used by the manuscript.

Separate the mathematical obligations if useful:

```text
row/column permutations preserve TU
pivot/basis normalization preserves TU
resulting representation has identity basis block
```

Use existing mathlib determinant/matrix/TU infrastructure wherever possible.

Expected home:

```text
Matroid/TotallyUnimodular.lean
```

---

# 13. N057 — TU identity augmentation

This target is currently:

```text
STATEMENT_DESIGN
```

Do not begin by inventing a general theorem from the phrase "identity augmentation."

Read the exact matrices used in `thm:regular-quotient-form`.

The manuscript starts from:

```text
A = ( I_r  D )
```

and constructs:

```text
K =
( -D       )
( I_{n-r}  )
```

and then:

```text
Â = ( I_n  K ).
```

The manuscript says:

> Appending identity rows or columns preserves total unimodularity, so both `K` and `Â` are totally unimodular.

The formalization target should justify these concrete steps.

Preferred strategy:

1. formulate the narrow TU lemmas actually required for `K`;
2. formulate the narrow TU lemma required for `Â`;
3. only generalize if the general statement is clearly correct and easier to use.

Do not mark N057 complete merely because "adding some identity matrix sometimes preserves TU."

The resulting formal theorem must actually imply the two manuscript claims.

Once its exact Lean statement is settled, change the ledger status out of:

```text
STATEMENT_DESIGN
```

and record the adopted formulation.

Expected home:

```text
Matroid/TotallyUnimodular.lean
```

---

# 14. N062 — Cographic matroid

Manuscript provenance:

```text
def:graphic-cographic
```

N061 is now complete.

The manuscript requires:

> the cographic matroid `M*(G)` has the same edge ground set and its circuits are the minimal nonempty edge cuts.

Do not merely define:

```text
cographic G := (graphic G)*
```

and stop.

That supplies the abstract dual but does not yet verify the manuscript's circuit characterization.

The target has two obligations:

```text
1. define/identify the cographic matroid as the dual of the completed graphic matroid;
2. prove that its circuits are exactly the minimal nonempty edge cuts/bonds.
```

Reuse the graph-cut infrastructure already developed in:

```text
Matroid/Graphic.lean
```

Do not rebuild the graphic matroid.

Prefer connecting the existing cut construction to matroid cocircuits/dual circuits.

Expected home:

```text
Matroid/Graphic.lean
```

---

# 15. N111 — Nonzero column rescaling

Canonical requirement:

> Independently rescaling represented columns by nonzero scalars preserves the vector matroid.

This is a matroid statement only.

Do not formalize the later energy-scaling claims here.

For an indexed representation `φ`, a scalar function `c` satisfying:

```text
∀ e, c e ≠ 0
```

should give a represented family:

```text
e ↦ c e • φ e
```

with exactly the same independent indexed subsets.

Preserve loops correctly:

```text
c e • 0 = 0.
```

Prove equality of the vector matroids or an equivalent representation-preservation theorem.

Expected home:

```text
Matroid/Representation.lean
```

---

# 16. N112 — Ambient linear isomorphism

Canonical requirement:

> An invertible ambient linear map preserves the represented vector matroid.

Again, this is the matroid statement, not the later energy-invariance proposition.

Given an appropriate linear equivalence `T`, prove that:

```text
φ
```

and:

```text
T ∘ φ
```

have identical indexed independence structure.

Prefer a result stated using Lean's standard linear-equivalence abstraction.

Do not unnecessarily require the represented vectors to span the whole ambient space.

Expected home:

```text
Matroid/Representation.lean
```

---

# 17. N130 — Corank-one uniform target circuit

Canonical requirement:

> In `U_{n,n+1}`, the full ground set is the unique target circuit.

This is an external uncited standard consequence of the already completed uniform-matroid construction N129.

State the theorem carefully enough to preserve the intended distinguished target element.

The core mathematical content is:

```text
every proper subset is independent
the whole ground set is dependent
therefore the whole ground set is the unique circuit
```

Then expose the pointed/target formulation required downstream.

Do not mix in the Grover application itself.

Expected home:

```text
Matroid/Uniform.lean
```

---

# 18. N258 — Incidence representation of the graphic matroid

Canonical requirement:

> A graph's edge-incidence vector configuration has exactly its cycle dependencies and therefore represents its graphic matroid.

This is an externally cited standard fact used in the introduction/discussion.

N043 and N061 are both complete, so the formal target should connect those two completed constructions.

The desirable end result is a theorem of the form:

```text
vectorMatroid (incidenceRepresentation G) = graphic G
```

or an equivalent `Represents` statement.

The manuscript is concerned with real span programs, so do not overgeneralize the coefficient field unless doing so is natural and already supported.

The representation must correctly handle:

```text
ordinary edges
parallel labeled edges
loops
```

For a signed incidence representation:

```text
nonloop edge u—v ↦ basis(u) - basis(v)
loop ↦ 0
```

up to an arbitrary choice of orientation.

The represented matroid must be independent of those orientation choices.

Prefer existing incidence-matrix / finitely-supported-function infrastructure if available.

Do not replace the manuscript's labeled multigraph model by `SimpleGraph`.

This target may require substantial proof engineering. If a reusable graph-linear-algebra prerequisite is discovered, treat it according to the missing-prerequisite rule below.

Expected home:

```text
Matroid/Graphic.lean
```

or a mathematically justified companion module such as:

```text
Matroid/GraphicRepresentation.lean
```

if the development becomes substantial.

---

# 19. Missing-prerequisite rule

Formalization may reveal that the audited DAG omitted a substantive mathematical prerequisite.

Distinguish:

```text
routine Lean helper
```

from:

```text
genuine reusable mathematical requirement.
```

Routine helpers do not become ledger nodes.

If a genuine prerequisite is missing:

1. identify its manuscript evidence or explain why it is logically required to formalize an existing manuscript requirement;
2. add a canonical ledger row;
3. add only the direct dependency edge;
4. recompute topological depths;
5. work on the newly discovered prerequisite before resuming any dependent target if its depth is ≤ 2.

Do not preserve an incorrect graph merely to claim that depth 2 closed.

If a new prerequisite lands at depth 0 or 1, the breadth-first invariant immediately makes it the highest priority.

---

# 20. Same-depth blockers do not stop independent work

All 12 current targets are at the same structural depth.

If one target blocks after a serious attempt, continue attempting the other independent depth-2 targets.

A blocker at depth 2 prevents advancement to depth 3, but does not prevent work on other depth-2 nodes.

Use precise blocker categories:

```text
BLOCKED_STATEMENT
BLOCKED_PROOF
BLOCKED_MATHLIB_INFRASTRUCTURE
BLOCKED_SCOPE
MISSING_PREREQUISITE
```

A blocker report must identify the exact unresolved mathematical step.

---

# 21. Do not force completion

Do not use:

```text
sorry
admit
axiom
```

to close any target.

If a target remains unresolved:

- keep the repository buildable;
- document the exact obstruction;
- leave its ledger status accurate;
- continue with independent depth-2 targets.

---

# 22. Formalization log

For every target, append or update an entry in:

```text
Matroid/FORMALIZATION_LOG.md
```

using:

```text
Ledger ID:
Structural depth:
TeX label / manuscript location:
Requirement:
Manuscript source status:
Mathematical proof or construction plan:
Lean declaration:
Formalization source:
Mathlib declarations used:
Deviation from manuscript route:
Result:
Build status:
Notes:
```

For N057, explicitly record the final statement design.

For N062 and N258, explicitly record how the formal graph model matches the manuscript's finite labeled graph conventions.

---

# 23. Provenance comments in Lean

Project-facing declarations should carry concise manuscript provenance.

For example:

```lean
/-- Manuscript: `def:matroid-minors` (N024). ... -/
```

or, for unlabeled standard facts:

```lean
/-- Manuscript ledger N111; standard represented-matroid fact used in
`prop:representation-scaling`. -/
```

Do not add provenance noise to routine private helper lemmas.

---

# 24. Dependency graph discipline

Modify:

```text
Matroid/DEPENDENCY_EDGES.csv
```

only when formalization demonstrates a genuine error or omitted direct prerequisite.

Edges must point:

```text
prerequisite → dependent
```

and must be direct, not transitive.

Record:

```text
edge_type
tex_evidence
justification
confidence
```

for every added edge.

Document graph changes in the formalization log.

---

# 25. Build discipline

Run:

```text
lake build
```

after meaningful groups of changes.

In particular, build after:

```text
minor/extension targets
representation targets
TU/regular targets
graphic/cographic targets
uniform target
```

as applicable.

Run a final:

```text
lake build
```

before reporting completion.

No target is `COMPLETE` unless the final project builds.

---

# 26. End-of-pass depth audit

After all 12 targets have been attempted, regenerate:

```text
Matroid/DEPTHS.csv
```

from the final ledger and DAG.

Update:

```text
Matroid/FRONTIER.md
```

with:

```text
depth-2 targets completed
depth-2 targets unresolved
new prerequisites discovered
minimum unresolved structural depth
active/complete/unresolved counts by depth
```

If all valid active depth-2 requirements are complete, state explicitly:

```text
The active Matroid formalization is complete through topological depth 2.
```

Then identify the unresolved depth-3 layer.

Do not formalize it.

---

# 27. Stop condition

This pass ends after every current depth-2 target has been seriously attempted and the final depth audit has been performed.

Best-case result:

```text
depth 0: clear
depth 1: clear
depth 2: clear
minimum unresolved depth: 3
```

If one or more depth-2 targets remain unresolved:

```text
depth 0: clear
depth 1: clear
depth 2: incomplete
```

with exact blockers recorded.

Either way:

> **Do not begin depth 3 in this task.**

The goal is to close the current structural layer, not to maximize the total number of formalized downstream nodes.