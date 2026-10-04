# Complete Topological Depth 4

The active Matroid formalization is complete through topological depth 3.

The current depth-4 layer contains six active nodes, of which two are already complete:

```text
N007  Closure             COMPLETE
N025  Contraction rank    COMPLETE
```

The four unresolved depth-4 targets are:

```text
N044  Represented rank
N067  One-sum preserves regularity
N136  Direct-sum bases
N176  Planar graphic-cographic correspondence
```

This task should attack exactly those four unresolved requirements.

The governing rule remains:

> **Do not perform new formalization work at depth 5 while any valid active requirement remains unresolved at depth 4.**

---

## 1. Preflight

Before beginning depth-4 work:

1. run `lake build`;
2. regenerate or verify `Matroid/DEPTHS.csv`;
3. verify every active node of depth ≤ 3 is `COMPLETE`;
4. verify the prior correspondence cleanup is present, especially:
   - N048 has a manuscript-facing arbitrary-`Represents` restriction/deletion interface;
   - N005 provenance has been checked.

If a depth ≤ 3 requirement is genuinely unresolved, repair it first.

Otherwise freeze the four targets above as the depth-4 working set.

Do not attack depth 5.

---

## 2. Sources of truth

Use:

```text
Manuscript/main.tex
Matroid/LEDGER.md
Matroid/DEPENDENCY_EDGES.csv
Matroid/DEPTHS.csv
Matroid/FORMALIZATION_LOG.md
Matroid/FRONTIER.md
```

For every target follow:

```text
ledger requirement
    ↓
exact manuscript statement / cited fact
    ↓
mathematical proof plan
    ↓
inspect pinned mathlib
    ↓
Lean statement
    ↓
proof
    ↓
lake build
    ↓
ledger + log update
```

The manuscript determines the mathematical requirement.

Do not weaken a requirement to match an available library theorem.

---

# 3. N044 — Represented rank

Canonical requirement:

> For a represented matroid, the rank of a set equals the dimension of the span of its represented vectors.

The manuscript states immediately after `def:vector-matroid`:

```text
r_M(A) = dim span φ(A).
```

This is an externally uncited standard fact and is used repeatedly later.

The project already has:

```text
Matroid.Represents
Matroid.vectorMatroid
vectorMatroid_indep_iff
```

and the basis/rank infrastructure from lower depths.

### Desired interface

Prefer a manuscript-facing theorem for an arbitrary representation:

```text
hφ : Represents M φ
```

rather than only for the canonical object `vectorMatroid E φ`.

The conclusion should directly identify the finite matroid rank with the finite dimension / `finrank` of the represented span.

Preserve the indexed semantics of the representation. Equal vectors at different ground elements remain distinct matroid elements, even though the resulting span is naturally the span of the image.

### Proof route

The expected mathematical argument is:

```text
choose a basis B of A
    ↓
φ(B) is linearly independent
    ↓
φ(B) spans the same represented span as φ(A)
    ↓
|B| = dim span φ(A)
    ↓
r_M(A) = dim span φ(A).
```

Use existing mathlib rank/linear-independence lemmas where possible.

Expected home:

```text
Matroid/Representation.lean
```

---

# 4. N067 — One-sum preserves regularity

Canonical requirement:

> A 1-sum of regular matroids is regular.

The manuscript states after `def:regular-matroid-sums`:

```text
Each operation preserves regularity.
```

N067 is only the `1`-sum case.

The completed prerequisites are:

```text
N051  Regularity
N064  One-sum construction
```

### Preferred route

For an arbitrary field `K`:

```text
M regular + N regular
    ↓
choose K-representations φM and φN
    ↓
place the two represented families in independent coordinate summands
    ↓
prove indexed independence is componentwise
    ↓
obtain a representation of oneSum M N
    ↓
conclude oneSum is regular.
```

Before implementing this directly, inspect mathlib for an existing theorem saying representability is preserved by `Matroid.disjointSum`.

If an exact theorem exists, use it.

Otherwise construct the combined representation using an appropriate direct-product/direct-sum vector space.

Do not evade the existing universe issue in `Regular` by weakening the theorem to selected fields.

The resulting theorem should apply directly to the project's:

```text
oneSum M N hdisj hM hN
```

Expected home:

```text
Matroid/Sums.lean
```

with representation helpers placed in `Representation.lean` only if genuinely reusable.

---

# 5. N136 — Direct-sum bases

Canonical requirement:

> Bases of a 1-sum are disjoint unions of bases of its two factors.

The manuscript uses this explicitly in the proof of:

```text
prop:seymour-one-sum
```

to factor the weighted basis sums.

The desired theorem should characterize whole-matroid bases, not merely independent sets.

Conceptually:

```text
B is a basis of M ⊕₁ N
    ↔
∃ BM BN,
    BM is a basis of M
    ∧ BN is a basis of N
    ∧ B = BM ∪ BN.
```

Because the ground sets are disjoint, union and symmetric difference coincide here.

Prefer an existing `disjointSum` basis theorem from mathlib if available.

Otherwise derive the result from:

```text
oneSum_indep_iff
+
maximality / IsBase
```

Do not prove only one direction.

The final statement should be strong enough to support the basis-sum factorization in `prop:seymour-one-sum` without another substantial combinatorial lemma.

Expected home:

```text
Matroid/Sums.lean
```

---

# 6. N176 — Planar graphic-cographic correspondence

Canonical requirement:

> If a graphic matroid has a planar graph representation, then it is also cographic, and dually.

The manuscript uses this in `prop:r10-proper-minors`:

```text
The graph K_{3,3} is minor-minimal nonplanar,
so every proper minor of M(K_{3,3}) is represented by a planar graph.

A graphic matroid represented by a planar graph is also cographic,
and dually.
```

This is an externally cited standard planar-duality fact.

This is likely the hardest target in the layer.

### Required mathematical content

Do not replace the theorem by the tautology:

```text
cographic G = (graphic G)*
```

That is N135 and is already complete.

N176 requires **planar graph duality**: for a planar graph representation there must be a dual graph whose cut/cycle structures identify the graphic and cographic matroids.

Conceptually:

```text
G planar
    ↓
construct / obtain planar dual G*
    ↓
cycles of G ↔ bonds of G*
    ↓
graphic G ≅ cographic G*
```

and dually:

```text
cographic G ≅ graphic G*
```

depending on the chosen labeling/isomorphism formalism.

### First task: inspect infrastructure

After fixing the manuscript statement, inspect pinned mathlib for:

```text
planar graph
plane embedding
dual graph
cycle-cut duality
```

for the graph type compatible with the existing labeled-edge `Graph α β` development.

Do not silently replace the manuscript's finite multigraph semantics with `SimpleGraph` if this loses loops, parallel edges, or edge labels.

### If planar-dual infrastructure is missing

Do **not** define:

```text
"planar" := "its graphic matroid is cographic"
```

or otherwise build the desired conclusion into the hypothesis.

Instead determine the genuine missing mathematical prerequisite.

If a reusable theorem such as:

```text
finite plane graph admits an edge-corresponding dual
```

or:

```text
cycles of a plane graph correspond to bonds of its dual
```

must be formalized first, add it to the ledger and DAG as a substantive prerequisite.

Recompute its structural depth.

Remain at depth ≤ 4 until the prerequisite and N176 are discharged.

Routine embedding helpers need not become ledger nodes.

Expected home:

```text
Matroid/Graphic.lean
```

or a focused companion module such as:

```text
Matroid/PlanarDuality.lean
```

if the development is substantial.

---

# 7. Same-depth work policy

Attempt all four depth-4 targets.

If one blocks, continue with the other independent depth-4 targets.

A blocked depth-4 node prevents advancement to depth 5 but does not prevent other depth-4 work.

Use precise statuses such as:

```text
BLOCKED_PROOF
BLOCKED_MATHLIB_INFRASTRUCTURE
MISSING_PREREQUISITE
BLOCKED_STATEMENT
BLOCKED_SCOPE
```

A blocker report must identify the exact missing mathematical step.

---

# 8. DAG corrections

Formalization may reveal missing dependencies.

If so:

1. distinguish routine Lean helpers from genuine mathematical prerequisites;
2. add only genuine reusable requirements to `LEDGER.md`;
3. add only direct prerequisite edges to `DEPENDENCY_EDGES.csv`;
4. document manuscript evidence and justification;
5. regenerate `DEPTHS.csv`.

Do not preserve an incorrect depth assignment merely to close depth 4.

If a new prerequisite lands at depth ≤ 4, it becomes part of the current breadth-first obligation.

---

# 9. Proof and provenance discipline

For each target record in `FORMALIZATION_LOG.md`:

```text
Ledger ID:
Structural depth:
Manuscript location:
Requirement:
Manuscript source status:
Mathematical proof plan:
Lean declaration:
Formalization source:
Mathlib declarations used:
Deviation from manuscript route:
Result:
Build status:
Notes:
```

Use:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

for formalization source.

Do not use manuscript citations as substitutes for Lean proofs.

No:

```text
sorry
admit
axiom
```

may be used to claim completion.

---

# 10. Lean organization

Keep files organized by mathematics.

Expected modules are:

```text
Matroid/Representation.lean
Matroid/Sums.lean
Matroid/Graphic.lean
```

with `Matroid/PlanarDuality.lean` permitted if N176 warrants a separate development.

Do not create chronological files such as:

```text
Depth4.lean
Pass9.lean
Frontier4.lean
```

`Matroid/Matroid.lean` remains the public umbrella import.

---

# 11. Build discipline

Run:

```text
lake build
```

after meaningful groups of changes and again before marking any target complete.

In particular:

```text
after N044
after the N067/N136 sum work
after N176 or its new prerequisites
final full build
```

The repository must remain buildable even when a target remains blocked.

---

# 12. End-of-pass audit

After all depth-4 targets have been attempted:

1. regenerate `Matroid/DEPTHS.csv`;
2. update `Matroid/FRONTIER.md`;
3. verify every active node of depth ≤ 4;
4. record any new prerequisite nodes or edge corrections.

Best-case result:

```text
depth 0: clear
depth 1: clear
depth 2: clear
depth 3: clear
depth 4: clear

minimum unresolved depth: 5
```

If so, state:

> **The active Matroid formalization is complete through topological depth 4.**

List the resulting depth-5 frontier, but do not attack it.

If one or more valid depth-4 requirements remain unresolved, stay at depth 4 and report the exact blockers.

Do not begin depth 5 in this task.