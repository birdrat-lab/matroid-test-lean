# Close N268 / N176 Using Existing Jordan-Curve Infrastructure

The only remaining depth-4 blocker is the planar-duality branch:

```text
N268  plane embedding → geometric/edge dual with cycle–bond correspondence
  ↓
N176  planar graphic ↔ cographic correspondence
```

Do not begin depth 5.

The goal of this pass is to discharge N268 by importing existing formal planar-topology infrastructure rather than developing Jordan separation from scratch.

---

## 1. Sources

Use:

```text
Manuscript/main.tex
Matroid/LEDGER.md
Matroid/DEPENDENCY_EDGES.csv
Matroid/FORMALIZATION_LOG.md
Matroid/PlanarDuality.lean
```

Preserve the manuscript's finite labeled-multigraph semantics.

Do not replace the graph model by `SimpleGraph` if loops, parallel edges, or edge labels are lost.

---

## 2. Add a pinned Jordan-curve dependency

Investigate and, if compatible, pin the existing `jordan_pick` Lean development at an exact revision compatible with this project's pinned Lean/mathlib version.

Record:

```text
repository
exact commit/revision
license
imported declarations actually used
```

in `Matroid/SOURCES.md`.

Run:

```text
lake build
```

immediately after adding the dependency.

Do not import a theorem as an axiom or copy an unverified statement into the project.

---

## 3. Do not re-prove general planar topology

The current blocker is topological, not matroidal.

Do not continue building an ad hoc general theory of:

```text
Jordan separation
punctured-disk connectivity
face counting
arc density
general plane topology
```

inside this repository if the imported formalization already provides the required separation theorem.

Use the external proved infrastructure and add only the bridges required by the manuscript graph model.

---

## 4. Main proof route for N268

Attack N268 through the following chain:

```text
graph cycle in the PlaneEmbedding
        ↓
concatenate embedded edge paths
        ↓
obtain a Jordan curve
        ↓
apply formal Jordan separation / boundary theorem
        ↓
identify the two sides of the cycle
        ↓
show the cycle is the required minimal face boundary / cut boundary
        ↓
use the existing finite graph/matroid lemmas
        ↓
cycle ↔ bond correspondence
        ↓
construct/identify the geometric dual
        ↓
N268
```

Keep each bridge as narrow as possible.

---

## 5. Graph-cycle → Jordan-curve bridge

The first local obligation is to turn the project's formal graph-cycle object into the continuous injective closed curve required by the imported Jordan theorem.

Use the hypotheses already present in `PlaneEmbedding`, especially:

```text
edge paths have the correct endpoints
edge interiors avoid graph vertices
distinct edge interiors are disjoint
```

Prove only enough to establish:

```text
a simple graph cycle traces an injective continuous S¹-curve
```

or the exact equivalent expected by the imported theorem.

Do not develop a general walk-embedding library unless required.

---

## 6. Use the strongest imported separation theorem available

Prefer an imported theorem that gives not only:

```text
ℝ² \ curve has two components
```

but also useful boundary information, such as:

```text
the Jordan curve is the boundary of each complementary component.
```

That boundary statement is especially useful for translating the topology back into graph cuts/faces.

If `jordan_pick` does not expose enough local separation structure, inspect an existing crosscut/Schoenflies formalization before proving the missing topology locally.

---

## 7. Reuse existing N268 reductions

Do not restart N268 from scratch.

Inspect `Matroid/PlanarDuality.lean` and retain all previously completed graph/matroid reductions.

The intended new work should primarily discharge the missing geometric implication identified by the previous blocker report.

If the existing development already reduces the converse direction to matroid duality once one cycle→bond direction is known, reuse that reduction.

---

## 8. N176 after N268

Once N268 is complete, discharge N176 immediately using the constructed planar dual:

```text
planar graph G
    ↓
N268 gives geometric dual G*
    ↓
M(G*) = M(G)*
    ↓
graphic M(G) is cographic
```

and the dual statement analogously.

Do not add a separate large proof of N176 if it is now a short consequence of N268 plus the already completed graphic/cographic duality API.

---

## 9. Provenance

Treat N268/N176 as standard external planar-duality theory unless manuscript inspection shows a specific citation attached to these claims.

Record clearly:

```text
manuscript provenance
external mathematical source
external Lean source
local bridge lemmas
```

Do not describe imported standard topology as a manuscript proof.

---

## 10. Fallback

If the external Jordan/crosscut infrastructure cannot be composed with the current `PlaneEmbedding` model without substantial new topology:

1. document the exact incompatibility;
2. do not weaken N268 by defining planarity in terms of matroid duality;
3. consider a separate proof of the specific downstream manuscript application using explicit graphic/cographic certificates only as a fallback.

Do not silently replace the general theorem with the special case.

---

## 11. Build and completion

Run:

```text
lake build
```

after:

```text
adding the dependency
graph-cycle → Jordan bridge
N268
N176
```

Update:

```text
Matroid/LEDGER.md
Matroid/FORMALIZATION_LOG.md
Matroid/DEPTHS.csv
Matroid/FRONTIER.md
```

If N268 and N176 close and all other depth-4 nodes remain complete, record:

```text
The active Matroid formalization is complete through topological depth 4.
```

Then identify depth 5 and stop.

Do not begin depth 5 in this pass.