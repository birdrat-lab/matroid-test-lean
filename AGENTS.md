# Clean the Certified Boundary and Begin Topological Depth 3

The active Matroid formalization is complete through structural topological depth 2.

The current mechanically computed state is:

```text
depth 0:  1 active,  1 complete
depth 1:  9 active,  9 complete
depth 2: 19 active, 19 complete
depth 3: 12 active,  1 complete, 11 unresolved
```

The minimum unresolved structural depth is therefore:

```text
3
```

This task has two phases:

```text
Phase A
repair the one statement-interface issue found by the depth-≤2
manuscript/Lean correspondence audit
        ↓
verify depths 0–2 remain complete
        ↓
Phase B
freeze the unresolved depth-3 layer
        ↓
attack every unresolved depth-3 target
        ↓
repair the DAG if formalization reveals a genuine missing prerequisite
        ↓
recompute structural depths
        ↓
STOP
```

Do not begin depth 4.

---

# 1. Governing breadth-first invariant

The repository is formalized in increasing structural topological depth.

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

The governing rule is:

> **Do not perform new work at depth `d + 1` while a valid active requirement remains unresolved at depth `d`.**

Historical results proved ahead of the current boundary remain valid and should not be undone.

Downstream leverage is only a tie-breaker among nodes at the same depth.

---

# 2. Canonical sources

Use:

```text
Manuscript/main.tex
```

as the mathematical source of truth.

Use:

```text
Matroid/LEDGER.md
```

as the canonical requirement inventory.

Use:

```text
Matroid/DEPENDENCY_EDGES.csv
```

as the direct internal prerequisite graph.

Use:

```text
Matroid/DEPTHS.csv
```

as a mechanically generated view of structural depth.

Use:

```text
Matroid/FORMALIZATION_LOG.md
```

for proof/provenance history.

Use:

```text
Matroid/FRONTIER.md
```

for the current formalization boundary.

The manuscript determines what a requirement means.

Mathlib may simplify the proof but must not redefine the requirement.

---

# 3. Phase A — repair N105 before advancing

The correspondence audit through depth 2 found one actual interface issue.

Ledger requirement N105 is:

```text
Positive target support
```

with manuscript provenance:

```text
def:positive-support
```

The manuscript applies the definition to a pointed matroid `(M, τ)` and an availability set satisfying:

```text
A ⊆ E(M) \ {τ}.
```

The current Lean definition instead accepts only:

```lean
A ⊆ M.E
```

and therefore formally permits:

```text
τ ∈ A.
```

That is broader than the manuscript definition and can change the interpretation of positive support.

Repair N105 before beginning new depth-3 work.

The resulting public interface must explicitly encode target exclusion, either directly as:

```lean
hA : A ⊆ M.E \ {τ}
```

or equivalently through separate hypotheses:

```lean
hA : A ⊆ M.E
hτA : τ ∉ A
```

Prefer the formulation that works most naturally with the surrounding pointed-matroid API while remaining transparently equivalent to the manuscript statement.

Update any affected local proofs or uses.

Update:

```text
Matroid/LEDGER.md
Matroid/FORMALIZATION_LOG.md
```

to record the corrected correspondence.

Run:

```text
lake build
```

after this repair.

N105 remains `COMPLETE` only if the corrected manuscript-facing formulation builds.

---

# 4. Do not unnecessarily reopen N051 or N056

The same correspondence audit identified two lesser implementation caveats that are **not** current statement failures.

## N051 — Regularity

The Lean definition uses universe-polymorphic quantification over fields.

This is ordinary Lean universe bookkeeping rather than a mathematical discrepancy.

Record the universe limitation clearly in the formalization log if it is not already recorded.

Do not weaken the mathematical definition.

Do not reopen N051 merely to eliminate universe parameters.

If a depth-3 theorem exposes an actual `ULift` or universe-transport issue, solve that issue locally and document it.

## N056 — TU standard form

The existing Lean development proves the manuscript standard-form step compositionally:

```text
reindex basis columns
+
normalize the basis block to I
+
prove the resulting nonbasis block remains TU
+
prove the indexed column matroid is preserved
```

This is mathematically sufficient for the manuscript.

Do not rewrite N056 merely to obtain one monolithic theorem.

An end-to-end wrapper may be added if a depth-3 proof benefits from one, but only as a convenience theorem over the already verified content.

---

# 5. Revalidate the certified boundary

After the N105 repair, mechanically regenerate:

```text
Matroid/DEPTHS.csv
```

and verify:

```text
all active nodes of depths 0, 1, and 2 are COMPLETE.
```

If any depth ≤ 2 node becomes unresolved:

```text
STOP
```

and repair the shallow boundary before beginning depth 3.

The expected minimum unresolved depth remains:

```text
3.
```

---

# 6. Freeze the unresolved depth-3 layer

The expected active depth-3 nodes are:

```text
N005  Extension to a full basis
N006  Rank                         COMPLETE
N027  Deletion composition
N048  Represented restriction and deletion
N052  Tutte characterization
N053  TU representation over every field
N064  Regular one-sum construction
N070  R10
N125  TU weighted basis determinant
N135  Graphic-cographic duality
N181  Circuit persistence under deletion
N256  Binary cycle symmetric difference
```

Therefore the expected unresolved target set is exactly:

```text
N005
N027
N048
N052
N053
N064
N070
N125
N135
N181
N256
```

Recompute this mechanically.

Record the verified set in:

```text
Matroid/FRONTIER.md
```

under:

```text
## Active depth-3 target snapshot
```

The DAG, not this expected list, is authoritative.

---

# 7. Universal workflow for every depth-3 target

For each target use:

```text
ledger entry
        ↓
exact manuscript location
        ↓
statement / cited fact actually required by the manuscript
        ↓
manuscript proof or surrounding mathematical argument
        ↓
write a mathematical proof/construction plan
        ↓
only then inspect pinned mathlib
        ↓
design manuscript-facing Lean statement
        ↓
implement
        ↓
lake build
        ↓
update ledger + formalization log
```

Do not begin by finding a nearby mathlib theorem and changing the requirement to fit it.

For cited standard facts, formalize only the strength actually required by the manuscript unless a clean general theorem is natural.

---

# 8. N005 — Extension to a full basis

Canonical requirement:

> An independent set extends to a basis of the whole matroid.

This is an external uncited standard fact.

N004 already formalizes extension to a basis inside a prescribed subset.

First inspect whether the existing mathlib basis API gives N005 directly.

Prefer:

```text
MATHLIB_EXACT
```

or a very small:

```text
MATHLIB_BRIDGE.
```

Do not build a new maximality argument if mathlib already packages this result.

Expected mathematical home:

```text
Matroid/RankClosure.lean
```

or another existing basis-oriented module.

---

# 9. N027 — Deletion composition

Canonical requirement:

> For disjoint `A,B`, deleting `A` and then `B` agrees with deleting `A ∪ B`.

This is a standard minor-algebra fact.

The manuscript uses it in later minor manipulations.

Use the existing mathlib restriction/deletion API if possible.

Be careful about whether the library theorem requires explicit disjointness or whether deletion composition is valid without it after set simplification.

The project-facing statement should imply the manuscript formulation directly.

Expected home:

```text
Matroid/Minors.lean
```

---

# 10. N048 — Represented restriction and deletion

Manuscript provenance:

```text
prop:represented-minors
```

The manuscript states:

> If `φ : E → V` represents `M`, restriction and deletion are represented by retaining the corresponding indexed vectors.

The manuscript proof says these two cases are immediate.

Preserve the indexed representation semantics already established in N042/N043.

Do not collapse equal vector values.

The Lean theorem should express that restricting the vector-matroid ground set to the surviving indices agrees with the corresponding matroid restriction/deletion.

This target does **not** include represented contraction; that is separately tracked as N049.

Expected home:

```text
Matroid/Representation.lean
```

or:

```text
Matroid/Minors.lean
```

depending on current import structure.

Avoid import cycles.

---

# 11. N052 — Tutte characterization

Canonical requirement:

> A matroid is regular iff it admits a real totally unimodular coordinate representation.

The manuscript explicitly cites Tutte and Oxley for this characterization.

This is a substantial theorem.

Do not silently replace it by only one implication.

The required equivalence has two directions:

```text
TU real representation
    ⇒ regular

regular
    ⇒ existence of a TU real representation.
```

N053 corresponds closely to the first direction and may provide reusable infrastructure.

However, N052 and N053 are both currently depth 3. Work within the same depth is allowed.

It is acceptable to prove N053 first and use it in N052.

The converse direction may require a substantial external characterization theorem not already present in mathlib.

Search pinned mathlib carefully **after** fixing the manuscript statement and proof plan.

If mathlib lacks the converse and a complete local proof would require formalizing a major portion of Tutte's theorem, report that precisely rather than claiming an incomplete equivalence.

Do not weaken N052 to:

```text
TU representable → regular.
```

That is N053-level content, not Tutte's characterization.

Expected home:

```text
Matroid/Regular.lean
```

and/or:

```text
Matroid/TotallyUnimodular.lean
```

---

# 12. N053 — TU representation over every field

The manuscript explains this fact immediately after the definition of regularity.

Canonical requirement:

> The independent column sets of a totally unimodular matrix are unchanged when its entries are interpreted over another field; therefore its column matroid is regular.

The manuscript's argument is:

```text
a k-column set is independent
        ↕
some k×k minor is nonzero
        ↓
TU means every such determinant is 0, +1, or -1
        ↓
nonzero minors remain nonzero over any field
        ↓
the same indexed column sets are independent.
```

Formalize this argument faithfully.

Take special care in characteristic `2`, where `-1 = 1` but remains nonzero.

Do not rely on real-specific linear algebra after the statement has moved to an arbitrary field.

This theorem should connect naturally to the existing:

```text
Matroid.Regular
```

definition.

Expected home:

```text
Matroid/TotallyUnimodular.lean
```

or `Regular.lean` with supporting TU lemmas elsewhere.

---

# 13. N064 — Regular one-sum construction

Manuscript provenance:

```text
def:regular-matroid-sums
```

For disjoint nonempty ground sets, the manuscript's `1`-sum is the ordinary direct sum.

Its cycles are:

```text
C₁ △ C₂
```

where `Cᵢ` is a cycle of `Mᵢ`.

Because the ground sets are disjoint, this is simply their disjoint union.

Prefer mathlib's existing direct-sum construction if available.

The formalization should expose the manuscript's cycle characterization rather than merely define an unrelated direct-sum object.

Do not formalize the `2`-sum or `3`-sum in N064.

Preserve the disjoint-ground-set condition.

Expected home may be a new mathematically named module such as:

```text
Matroid/Sums.lean
```

if this is the first substantive sum construction.

---

# 14. N070 — `R10`

Manuscript provenance:

```text
def:r10
fig:r10-k33
```

The manuscript defines `R10` as the vector matroid on:

```text
E10 = {0,1,...,9}
```

represented over the reals by the explicit `5 × 10` matrix:

```text
[ 1 0 0 0 0 | -1  1  0  0  1 ]
[ 0 1 0 0 0 |  1 -1  1  0  0 ]
[ 0 0 1 0 0 |  0  1 -1  1  0 ]
[ 0 0 0 1 0 |  0  0  1 -1  1 ]
[ 0 0 0 0 1 |  1  0  0  1 -1 ]
```

with columns indexed left-to-right by `0,...,9`.

Formalize **this exact represented matroid**.

Do not substitute an isomorphic but differently indexed representation unless accompanied by a precise equivalence back to the manuscript indexing.

The definition should make later finite `R10` calculations convenient.

Also establish the elementary metadata asserted directly in `def:r10` where needed:

```text
10-element ground set
rank 5
regularity
```

Do not begin formalizing the later `R10` atlas or finite certificate data in this target.

Expected home:

```text
Matroid/R10.lean
```

This is a sufficiently important mathematical object to justify its own module.

---

# 15. N125 — TU weighted basis determinant

Canonical requirement:

> For a full-row-rank TU representation with positive column weights,
> `det(C W Cᵀ)` equals the weighted basis-generating sum of the represented column matroid.

The manuscript explicitly invokes Cauchy–Binet and total unimodularity.

The mathematical route should remain recognizable:

```text
Cauchy–Binet
    ↓
sum over maximal column subsets
    ↓
each squared maximal minor is 0 or 1 by TU
    ↓
surviving terms are exactly bases
    ↓
each surviving term carries the product of its column weights.
```

Formalize the determinant identity needed by the manuscript.

Do not include the reconstruction-energy ratio itself; that is later application-level mathematics.

Be explicit about:

```text
finite row and column indices
full row rank
diagonal weight matrix
positive/nonzero weights as actually required
the represented column matroid
```

If Cauchy–Binet infrastructure is absent or awkward in pinned mathlib, isolate the missing determinant lemma cleanly.

Expected home:

```text
Matroid/TotallyUnimodular.lean
```

or a focused mathematical module such as:

```text
Matroid/WeightedDeterminants.lean
```

if substantial.

---

# 16. N135 — Graphic-cographic duality

Canonical requirement:

> The cographic matroid of `G` is the dual of its graphic matroid.

N061 and N062 are already complete.

The current cographic construction was intentionally built through duality, so N135 should likely be a small exact theorem or definitional equality.

Do not reprove the bond/cocircuit theory already established for N062.

Expose the manuscript relation directly:

```text
cographic G = (graphic G)✶
```

using the project's actual names for duality.

Expected home:

```text
Matroid/Graphic.lean
```

---

# 17. N181 — Circuit persistence under deletion

Canonical requirement:

> A circuit avoiding a deleted element remains a circuit after deletion.

This is the implicit step used in:

```text
prop:r10-no-three-sum
```

The manuscript argument is:

```text
C circuit of R10
e ∉ C
    ⇒
C remains a circuit of R10 \ e.
```

Formalize the standard deletion-circuit restriction fact.

Prefer an exact mathlib theorem or a short bridge from the restriction API.

Do not involve `R10` in the generic theorem.

Expected home:

```text
Matroid/Minors.lean
```

---

# 18. N256 — Binary cycle symmetric difference

The manuscript states after `def:matroid-cycle`:

> A regular matroid is representable over `𝔽₂`, so the symmetric difference of two cycles is again a cycle.

Formalize precisely that fact.

Do not merely prove symmetric-difference closure for circuits; cycles are disjoint unions of circuits.

The manuscript route should guide the proof:

```text
regular
    ↓
representation over F₂
    ↓
cycles correspond to the binary cycle space
    ↓
addition over F₂ corresponds to symmetric difference
    ↓
cycle closure under △.
```

If mathlib already has binary matroid/cycle-space infrastructure, use it.

If it does not, first determine the minimum local result needed to prove symmetric-difference closure.

Do not build a broad theory of binary matroids unless required.

Expected home:

```text
Matroid/Cycles.lean
```

with supporting representation lemmas where appropriate.

---

# 19. Same-depth dependencies are allowed

The structural DAG only records direct prerequisites known before formalization.

During this pass, one depth-3 theorem may naturally become useful in another depth-3 proof.

For example:

```text
N053 → N052
```

may emerge as a useful direct proof dependency.

If that dependency is mathematically substantive and should have been in the DAG:

1. add the direct edge;
2. record manuscript/log evidence;
3. recompute depths.

This may raise the dependent theorem's structural depth.

That is acceptable.

Do **not** preserve an incorrect depth assignment merely to finish the nominal depth-3 batch.

The graph is allowed to improve through formalization.

---

# 20. Missing-prerequisite rule

If a target exposes a missing theorem, distinguish:

```text
routine Lean helper
```

from:

```text
genuine reusable mathematical requirement.
```

Routine helpers remain implementation details.

A substantive missing prerequisite should receive:

```text
a ledger entry
a direct dependency edge
manuscript/provenance evidence
a recomputed depth
```

If this produces a new unresolved node of depth ≤ 3, the breadth-first invariant requires addressing it before moving deeper.

---

# 21. Same-depth blockers do not halt independent work

If one depth-3 target blocks after serious effort, continue with the other unresolved depth-3 targets.

A blocker prevents advancement to depth 4.

It does not prevent work on independent nodes at depth 3.

Use precise blocker statuses such as:

```text
BLOCKED_PROOF
BLOCKED_MATHLIB_INFRASTRUCTURE
BLOCKED_STATEMENT
BLOCKED_SCOPE
MISSING_PREREQUISITE
```

A blocker report must identify the exact mathematical obstruction.

For large cited results such as N052, explicitly distinguish:

```text
missing theorem in mathlib
```

from:

```text
local proof attempted and failed
```

from:

```text
formalization would require importing a major external theorem not currently developed.
```

---

# 22. No placeholders

Do not use:

```text
sorry
admit
axiom
```

to mark any target complete.

Do not encode a cited theorem as an axiom merely because the manuscript cites it.

A cited theorem must either:

```text
already exist in trusted imported Lean mathematics
```

or:

```text
be formally proved here.
```

Otherwise leave the requirement unresolved and document the blocker.

---

# 23. Formalization-source categories

Continue using:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

For substantial cited theorems unavailable in mathlib, do not misuse `EXTERNAL_CITED` as a Lean completion status.

`EXTERNAL_CITED` describes manuscript provenance.

It does not constitute a formal proof.

---

# 24. Lean source organization

Keep organizing source code by mathematics.

Appropriate existing or anticipated modules include:

```text
Matroid/RankClosure.lean
Matroid/Minors.lean
Matroid/Representation.lean
Matroid/Regular.lean
Matroid/TotallyUnimodular.lean
Matroid/Cycles.lean
Matroid/Graphic.lean
Matroid/Sums.lean
Matroid/R10.lean
```

Do not create:

```text
Depth3.lean
Frontier3.lean
Pass7.lean
```

Chronology belongs in the log.

If a new module is created, import it transitively from:

```text
Matroid/Matroid.lean
```

---

# 25. Manuscript provenance in Lean

Every project-facing declaration should retain concise provenance such as:

```lean
/-- Manuscript: `prop:represented-minors` (N048). -/
```

For unlabeled prose facts:

```lean
/-- Manuscript ledger N053; standard TU/regularity fact stated after
`def:regular-matroid`. -/
```

Do not annotate routine internal helper lemmas unless it materially improves traceability.

---

# 26. Formalization log

For each target record:

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

For N052, record the two directions separately if they use substantially different machinery.

For N070, record the exact relationship between Lean column indices and manuscript indices `0,...,9`.

For N125, record the exact Cauchy–Binet identity used.

For N256, record precisely how symmetric difference is identified with binary addition.

---

# 27. Build discipline

Run:

```text
lake build
```

after the N105 repair.

Then build after meaningful groups of depth-3 work.

Run a final:

```text
lake build
```

before updating any target to `COMPLETE`.

No target is complete merely because an isolated file elaborates.

The full project must build.

---

# 28. End-of-pass depth audit

After all unresolved depth-3 targets have been attempted:

1. regenerate `Matroid/DEPTHS.csv`;
2. update `Matroid/FRONTIER.md`;
3. report all graph corrections;
4. report all new substantive prerequisites;
5. list complete and unresolved depth-3 nodes;
6. identify the new minimum unresolved structural depth.

If every valid active node of depth ≤ 3 is complete, state:

```text
The active Matroid formalization is complete through topological depth 3.
```

Then list the resulting depth-4 frontier.

Do not attack it.

If depth 3 remains incomplete, state the exact remaining blockers.

---

# 29. Stop condition

This task ends after:

```text
N105 correspondence repair
        +
verification that depths 0–2 remain clear
        +
serious attempt on every unresolved depth-3 target
        +
final lake build
        +
depth/DAG recomputation
```

The best-case outcome is:

```text
depth 0: clear
depth 1: clear
depth 2: clear
depth 3: clear
minimum unresolved depth: 4
```

If depth 3 does not fully close, remain at depth 3.

Do not begin depth 4.

The objective is to extend the certified breadth-first formalization boundary by exactly one structural layer while preserving manuscript-to-Lean statement fidelity.