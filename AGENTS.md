# First Lean Formalization Pass

This repository is now beginning the Lean formalization phase of the matroid/span-program project.

The manuscript dependency inventory has already been extracted, audited, adjudicated, and organized into an internal dependency graph.

The canonical mathematical specification is:

```text
Matroid/LEDGER.md
```

The internal prerequisite graph is:

```text
Matroid/DEPENDENCY_EDGES.csv
```

The identified mathematical starting points are summarized in:

```text
Matroid/ENTRY_NODES.md
```

This pass should formalize only the first small basis/rank/closure/circuit boundary described below.

Do not expand into regular matroids, sums, R10, modular cuts, represented matroids, or application-specific material.

---

# 1. Mathematical source of truth

The frozen manuscript is:

```text
Manuscript/main.tex
```

For every ledger requirement implemented in Lean:

1. read the exact manuscript definition, theorem, proposition, or proof location first;
2. preserve the manuscript's mathematical meaning and hypotheses;
3. use the exact TeX label as provenance;
4. inspect the surrounding proof or explanatory prose before choosing a Lean proof strategy.

Do not silently replace the manuscript statement with a stronger, weaker, or merely similar theorem because it is easier to formalize.

If a more general mathlib theorem is used internally, the exported project-facing statement should still match the mathematical requirement recorded in the ledger.

---

# 2. Proof-guided formalization

The Lean development should be informed by the mathematical derivations already present in the manuscript.

Before searching mathlib for a theorem, determine the manuscript proof status of the target.

Use one of:

```text
MANUSCRIPT_PROOF
MANUSCRIPT_SKETCH
MANUSCRIPT_STATEMENT_ONLY
```

## `MANUSCRIPT_PROOF`

The manuscript contains a substantive proof.

First summarize the proof into its mathematical steps.

Prefer a Lean proof whose structure follows those steps.

Mathlib lemmas may discharge individual steps.

If the final Lean proof follows a materially different route, record the deviation and why it was preferable.

## `MANUSCRIPT_SKETCH`

The manuscript gives a derivation, named principle, or compressed argument but not a complete proof.

Treat the manuscript derivation as the preferred proof plan.

Fill missing routine details using standard mathematics or mathlib.

Record what had to be supplied beyond the manuscript.

## `MANUSCRIPT_STATEMENT_ONLY`

The manuscript states the result but provides no real derivation.

Do not invent a manuscript proof.

Use standard mathematics and mathlib as appropriate, while recording that the formal proof is additional proof engineering rather than a transcription of an existing manuscript proof.

---

# 3. Read manuscript before mathlib

For every theorem-like target, follow this order:

```text
1. identify ledger entry
2. read exact manuscript statement
3. read manuscript proof / surrounding derivation
4. write a short proof plan
5. only then inspect mathlib
6. design Lean statement
7. implement
8. compare Lean proof with manuscript proof plan
9. build
10. update provenance/status
```

Do not begin by searching mathlib for a theorem with a similar name.

This ordering is intentional.

The objective is to formalize the mathematics of the manuscript, not to reverse-engineer a manuscript interpretation from whatever declarations happen to exist in mathlib.

---

# 4. Use mathlib rather than redefining mathematics

After the manuscript proof plan is understood, inspect the pinned version of mathlib.

Use existing definitions and results whenever they faithfully represent the manuscript mathematics.

In particular, continue to use mathlib's existing `Matroid` abstraction.

Do not define a competing matroid structure corresponding literally to the manuscript's `(E, I)` presentation.

The manuscript's finite independent-set definition is mathematical provenance, not a requirement to duplicate mathlib's foundational representation.

A target may therefore be discharged by:

```text
MATHLIB_EXACT
```

when an existing theorem is exactly the required result, or by:

```text
MATHLIB_BRIDGE
```

when a short local theorem translates between the manuscript formulation and mathlib's interface.

Use:

```text
LOCAL_PROOF
```

only when a suitable mathlib result is not available or when the required manuscript-facing result genuinely needs additional proof.

---

# 5. Proof fidelity versus library reuse

Do not reproduce a long proof manually merely to imitate the manuscript when mathlib already proves exactly the same mathematical theorem.

Conversely, do not hide a substantive manuscript argument behind a vaguely related powerful theorem without documenting the change of proof route.

The desired principle is:

> preserve the manuscript's mathematical decomposition while allowing mathlib to discharge standard subarguments.

For every theorem-like target, the formalization record should make it possible to answer:

- What does the manuscript claim?
- How does the manuscript justify it?
- What Lean/mathlib facts implement those steps?
- Did the formal proof materially deviate from the manuscript route?

---

# 6. Formalization log

Create:

```text
Matroid/FORMALIZATION_LOG.md
```

For each target attempted in this pass, record:

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
Build status:
Notes:
```

`Manuscript proof plan` should be mathematical prose, not Lean tactics.

Keep it concise but substantive enough to recover the intended argument.

If the manuscript contains no proof, say so explicitly.

Do not retroactively describe the Lean proof as though it appeared in the manuscript.

---

# 7. Code provenance

Every project-facing definition or theorem introduced for a ledger entry should contain concise manuscript provenance in its docstring or immediately adjacent comment.

For example:

```text
Manuscript: `prop:closure-circuit` (N016).
```

For theorem-like declarations, also indicate the proof-source category when useful:

```text
Proof source: MANUSCRIPT_STATEMENT_ONLY.
```

Do not clutter every internal helper lemma with manuscript metadata.

Provenance is required on the project-facing declarations corresponding to ledger nodes.

---

# 8. First formalization boundary

This pass should implement the smallest coherent basis/rank/closure/circuit boundary identified in `ENTRY_NODES.md`.

Target these ledger requirements:

```text
N001  Finite matroid
N002  Basis
N015  Circuit
N003  Equal basis cardinalities
N006  Rank
N007  Closure
N016  Circuit characterization of closure
```

The intended mathematical dependency shape is:

```text
N001
 ├── N002
 └── N015

N002
 └── N003
      └── N006
           └── N007

N007 + N015
 └── N016
```

Use `DEPENDENCY_EDGES.csv` as the authoritative internal dependency record if it contains additional direct edges relevant to these nodes.

Do not expand the pass merely because adjacent facts are easy.

---

# 9. N001 does not require a new Matroid structure

For N001, establish the project's connection to mathlib's existing `Matroid` abstraction.

Do not recreate the independent-set axioms as a new structure unless direct inspection of mathlib proves that such a bridge is genuinely necessary.

The goal is for all downstream work to use mathlib's `Matroid`.

Record how the manuscript's finite independent-set presentation corresponds to the mathlib object.

---

# 10. Definitions versus theorems

For manuscript definitions such as basis, rank, closure, or circuit:

- first determine whether the concept already exists directly in mathlib;
- prefer the existing mathlib object;
- introduce manuscript-facing notation or wrapper definitions only when they materially improve statement fidelity or downstream usability.

Do not create redundant aliases merely so every ledger row produces a new Lean constant.

A ledger requirement may be marked complete by documenting an exact existing formal definition.

---

# 11. Statement first

For every theorem-like target:

1. formulate or identify the exact Lean statement;
2. confirm that it expresses the ledger requirement;
3. make the statement elaborate;
4. only then complete the proof.

Do not weaken hypotheses merely to make elaboration easier.

Do not strengthen the conclusion unless the manuscript-facing theorem is still explicitly exposed.

---

# 12. First-boundary proof guidance

## N003 — Equal basis cardinalities

Manuscript location:

```text
def:matroid-basis
```

The manuscript states that the exchange axiom implies that all bases of a fixed subset have equal cardinality.

Treat this as:

```text
MANUSCRIPT_SKETCH
```

The proof should be conceptually tied to basis exchange, even if mathlib already packages the result.

Record the exact mathlib result used if the proof collapses to a library theorem.

---

## N016 — Circuit characterization of closure

Manuscript label:

```text
prop:closure-circuit
```

The manuscript states:

```text
for e ∉ A,
e ∈ cl(A)
iff
there exists a circuit C containing e with C \ {e} ⊆ A.
```

The manuscript does not provide a detailed proof.

Treat this as:

```text
MANUSCRIPT_STATEMENT_ONLY
```

Preserve the exact manuscript hypotheses and conclusion in the project-facing statement.

If mathlib already contains an equivalent theorem, identify the exact theorem and prove the manuscript-facing formulation by a transparent bridge if necessary.

Do not substitute a related circuit/closure characterization with materially different side conditions.

---

# 13. N080 and N261 are not targets of this pass

Do not formalize N080 in this pass.

It belongs to an independent closure-axiom characterization branch and can be addressed after the basic manuscript-facing matroid vocabulary is stable.

Do not formalize N261 in this pass.

`ENTRY_NODES.md` explicitly records a scope question about whether N261 is properly a matroid requirement or an external matrix/TU lemma.

Leave that question for the later regular-matroid branch.

---

# 14. Permitted files

This pass may modify:

```text
Matroid/Internal/Basic.lean
Matroid/Matroid.lean
Matroid/LEDGER.md
Matroid/FORMALIZATION_LOG.md
Matroid/SOURCES.md
```

Modify `Matroid/Matroid.lean` only if an import change is genuinely required.

Do not modify:

```text
Manuscript/main.tex
Matroid/DEPENDENCY_EDGES.csv
Matroid/ENTRY_NODES.md
logs/dependency_audit/
```

The manuscript and dependency-analysis artifacts are frozen provenance.

---

# 15. Ledger updates

After a target is successfully formalized, update only that row of:

```text
Matroid/LEDGER.md
```

Set `Formalization source` appropriately:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

Update `Status` only when justified.

Use:

```text
LEAN_STATED
```

when the statement exists and elaborates but is not yet discharged.

Use:

```text
MATHLIB_MATCH
```

when an exact library result has been identified and recorded.

Use:

```text
BRIDGE_PROVED
```

when the manuscript-facing theorem is proved by a local bridge to mathlib.

Use:

```text
PROVED_LOCAL
```

when a genuinely local proof is supplied.

Use:

```text
COMPLETE
```

only when the manuscript-facing requirement has been fully discharged and provenance has been recorded.

Do not mark a ledger row complete merely because a similar theorem exists.

---

# 16. No placeholders in completed work

Do not use:

```text
sorry
admit
axiom
```

for completed declarations.

If a target cannot yet be discharged, leave it at `LEAN_STATED`, document the blocker in `FORMALIZATION_LOG.md`, and keep the repository buildable without claiming completion.

Prefer partial completion of the target set over introducing unproved assumptions.

---

# 17. Build discipline

Run:

```text
lake build
```

after meaningful changes and before finishing.

The final repository must build successfully.

Do not consider successful elaboration of one scratch theorem sufficient if the library target fails.

---

# 18. Completion criteria

This pass is complete when:

1. N001, N002, N015, N003, N006, N007, and N016 have each been reconciled with Lean/mathlib;
2. every project-facing declaration is traced to its ledger ID and manuscript label;
3. theorem-like targets have a recorded manuscript proof status and proof plan;
4. every material deviation from a manuscript proof route is documented;
5. the corresponding ledger rows accurately record their formalization source and status;
6. `Matroid/FORMALIZATION_LOG.md` records the work;
7. no unrelated ledger nodes were formalized;
8. `lake build` succeeds.

Stop after this boundary.

Do not continue automatically to the next dependency layer.