# Single-Frontier Lean Formalization Pass

This repository is formalizing the matroid mathematics required by the manuscript from the bottom of its audited dependency graph upward.

The dependency-analysis phase is complete.

The canonical mathematical specification is:

```text
Matroid/LEDGER.md
```

The direct internal prerequisite graph is:

```text
Matroid/DEPENDENCY_EDGES.csv
```

The previous Lean pass successfully completed the first foundational boundary.

This task performs **exactly one additional frontier depth**.

The procedure is:

```text
compute current frontier
        ↓
freeze that target set
        ↓
formalize every node in that frontier
        ↓
update ledger and formalization log
        ↓
compute the newly exposed frontier
        ↓
report it
        ↓
STOP
```

Do not begin formalizing the newly exposed frontier during this task.

---

# 1. Mathematical source of truth

The frozen manuscript is:

```text
Manuscript/main.tex
```

For every target:

1. read its canonical entry in `Matroid/LEDGER.md`;
2. locate the exact manuscript statement, definition, proof, or proof context;
3. understand the manuscript's mathematical derivation before searching mathlib;
4. preserve the manuscript's hypotheses and intended conclusion.

The manuscript determines the mathematics being formalized.

Mathlib determines how much of that mathematics must be implemented locally.

Do not silently strengthen, weaken, or replace a manuscript requirement merely because a nearby library theorem is convenient.

Use exact TeX labels for provenance.

Do not fabricate labels.

---

# 2. Compute the current frontier mechanically

At the beginning of this task, compute the current unresolved frontier from:

```text
Matroid/LEDGER.md
Matroid/DEPENDENCY_EDGES.csv
```

An active ledger node belongs to the current frontier precisely when:

1. it is an active formalization node;
2. it is not already `COMPLETE`;
3. every direct internal prerequisite appearing in `DEPENDENCY_EDGES.csv` is `COMPLETE`.

Use the ledger's active matroid scopes.

Do not include rows that are only:

```text
APPLICATION_CONTEXT
OUT_OF_SCOPE_CONTEXT
```

unless the canonical ledger explicitly marks them as active formalization requirements.

Do not choose the frontier manually by manuscript section or perceived importance.

---

# 3. Expected current frontier

From the repository state immediately after the first successful Lean pass, the expected frontier is:

```text
N004  Extension within a subset

N008  Closure extensivity
N009  Closure monotonicity
N010  Closure idempotence
N011  Steinitz closure exchange
N012  Flat

N020  Free matroid
N021  Loop
N022  Coloop
N023  Restriction
N025  Contraction rank
N031  Fundamental circuit

N042  Matroid representation
N043  Vector matroid

N061  Graphic matroid
N062  Cographic matroid

N063  Regular-matroid cycle

N073  Colored matroid
N080  Finite closure-exchange representation
N081  Pointed matroid port
N105  Positive target support

N122  Weighted target basis sums

N129  Uniform matroid
N132  Dual matroid bases

N158  Five 3-sum boundary classes

N261  TU row restriction
```

This list is a sanity check, not a substitute for recomputation.

If the mechanically computed frontier differs, investigate why before starting formalization.

Possible legitimate causes include:

- a ledger status changed after the previous pass;
- an edge was corrected;
- a scope classification changed.

Record any discrepancy.

Do not silently force the graph to reproduce this expected list.

---

# 4. Freeze the frontier snapshot

Once computed and validated, create:

```text
Matroid/FRONTIER_PASS_2.md
```

Record:

- date/pass identifier;
- all frontier node IDs;
- names;
- direct internal prerequisites;
- current statuses;
- scope;
- manuscript TeX provenance.

State explicitly:

> This target set is frozen for the duration of this pass.

If completing one frontier node exposes additional nodes during the task, do not add those newly exposed nodes to the target set.

They belong to the next pass.

---

# 5. Attack the entire frozen frontier

Attempt every node in the frozen frontier.

Do not manually narrow the batch by branch.

The dependency graph has already established that all of these nodes are mathematically available from the completed lower layer.

However:

> attempt does not mean force completion.

If one node encounters a genuine blocker, document the blocker and continue with the independent frontier nodes.

A blocked node must not prevent work on unrelated targets.

---

# 6. Required workflow for every target

For every frontier node, use this order:

```text
ledger requirement
        ↓
manuscript statement / definition
        ↓
manuscript proof or surrounding derivation
        ↓
mathematical proof plan
        ↓
inspect pinned mathlib
        ↓
design manuscript-facing Lean statement
        ↓
implement
        ↓
lake build
        ↓
update ledger and log
```

Do not begin by searching mathlib.

The manuscript-derived mathematical interpretation must be fixed first.

---

# 7. Manuscript proof classification

For every theorem-like target, classify the manuscript evidence as one of:

```text
MANUSCRIPT_PROOF
MANUSCRIPT_SKETCH
MANUSCRIPT_STATEMENT_ONLY
```

## `MANUSCRIPT_PROOF`

The manuscript contains a substantive proof.

Extract its mathematical structure before implementation.

Prefer a Lean proof following that structure, while allowing mathlib to discharge standard substeps.

If Lean follows a materially different route, document the deviation.

## `MANUSCRIPT_SKETCH`

The manuscript gives the essential argument or invokes a specific standard principle but omits routine details.

Use that argument as the preferred proof plan.

Record what Lean/mathlib had to supply.

## `MANUSCRIPT_STATEMENT_ONLY`

The manuscript states the result but supplies no substantive derivation.

Do not invent a manuscript proof.

Use an appropriate standard/mathlib proof and record that the formal proof is additional proof engineering.

For definitions, record:

```text
MANUSCRIPT_DEFINITION
```

rather than a proof category.

---

# 8. Mathlib reconciliation

Only after understanding the manuscript requirement and proof plan, inspect the pinned mathlib version.

Classify the formalization route as one of:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

## `MATHLIB_EXACT`

An existing mathlib definition or theorem already expresses the manuscript requirement exactly enough that no project-facing proof is required.

Document the fully qualified declaration.

Do not create a redundant wrapper solely so the ledger node has a new Lean name.

## `MATHLIB_BRIDGE`

Mathlib contains the essential mathematics but its formulation differs from the manuscript.

Create a small manuscript-facing declaration that bridges the formulations.

Prefer transparent bridges.

## `LOCAL_PROOF`

The required result is not adequately supplied by mathlib.

Implement the mathematical argument locally.

When the manuscript contains a proof, preserve its structure when practical.

---

# 9. Statement fidelity

Before proving a theorem-like target:

1. determine the intended manuscript-facing Lean statement;
2. make the statement elaborate;
3. compare it explicitly with the canonical ledger requirement;
4. only then prove it.

Do not weaken hypotheses merely to get a theorem through Lean.

Do not silently strengthen the target and then fail to expose the manuscript formulation.

A stronger internal theorem is acceptable if the manuscript-facing requirement remains available and clearly traced.

---

# 10. Definitions and existing structures

Do not redefine standard mathematical structures unnecessarily.

Continue using mathlib's existing `Matroid` abstraction.

Likewise, if notions such as:

- flat;
- loop;
- coloop;
- restriction;
- contraction;
- dual;
- uniform matroid;
- graphic matroid;

already have faithful mathlib definitions, use those definitions rather than creating competing versions.

The manuscript's formulation supplies mathematical provenance; it does not require duplicating mathlib's representation.

A definition node may become `COMPLETE` by identifying and documenting an exact existing formal object.

---

# 11. Heterogeneous frontier branches

This frontier contains several different mathematical branches.

That is intentional.

Examples include:

```text
basic closure/circuit structure
minor operations
representation
graphic/cographic matroids
regular/binary structure
colored and pointed matroids
weighted basis expressions
duality and uniform matroids
3-sum boundary structure
TU/matrix structure
```

Apply the same manuscript → mathlib → Lean discipline to all of them.

Do not expand sideways into downstream nodes merely because a branch is easy.

Do not abandon independent branches because another frontier node is difficult.

---

# 12. Special handling of N261

N261 previously carried a scope/statement-design concern concerning whether it is fundamentally a matroid requirement or a matrix/TU lemma.

Attempt to resolve its precise statement using:

```text
Matroid/LEDGER.md
Manuscript/main.tex
```

before implementation.

If it is correctly an active ledger node and its mathematical statement is clear, formalize it.

If the analysis reveals that its scope or statement is still genuinely unresolved, do not force a Lean theorem.

Record:

```text
BLOCKED_SCOPE
```

or:

```text
BLOCKED_STATEMENT
```

in the formalization log with a precise explanation.

Continue with all other frontier targets.

Do not modify the dependency graph merely to make N261 disappear.

---

# 13. Formalization log

Continue using:

```text
Matroid/FORMALIZATION_LOG.md
```

For every attempted frontier target, record:

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
Build status:
Notes:
```

For definitions, replace the proof-plan fields appropriately.

The proof plan should describe mathematics, not tactics.

Examples of useful descriptions:

```text
Use basis exchange to compare finite cardinalities.
```

```text
Apply the circuit characterization of closure to obtain the required circuit.
```

Not:

```text
simp; aesop
```

---

# 14. Project-facing provenance

Every project-facing declaration corresponding to a ledger requirement should carry concise provenance in a docstring or adjacent comment.

For example:

```text
Manuscript: `prop:...` (N031).
```

When useful, include the proof-source category.

Do not clutter purely internal helper lemmas with manuscript metadata.

---

# 15. Permitted code organization

Use the existing repository architecture.

Modify existing internal files or introduce a new internal file only when mathematical organization genuinely warrants it.

Do not redesign the entire module hierarchy during this pass.

The public import point remains:

```text
Matroid/Matroid.lean
```

Any new internal module required by this frontier must be imported transitively from the public entry point.

Do not expose unnecessary implementation details as public API.

---

# 16. Ledger status updates

Update only the rows corresponding to targets attempted in this pass.

Use formalization-source values consistently:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

Use statuses:

```text
LEAN_STATED
MATHLIB_MATCH
BRIDGE_PROVED
PROVED_LOCAL
COMPLETE
```

as appropriate.

Use `COMPLETE` only when:

- the correct manuscript-facing requirement has been discharged;
- provenance is recorded;
- and the repository builds.

For blocked targets, do not falsely mark them complete.

Record the blocker explicitly in the log.

---

# 17. No placeholders

Do not use:

```text
sorry
admit
axiom
```

to claim completion.

If a target cannot be completed during this pass:

- preserve a buildable repository;
- document the blocker;
- leave the ledger status accurate;
- continue with independent targets.

Partial frontier completion is preferable to unsupported assumptions.

---

# 18. Build discipline

Run:

```text
lake build
```

throughout the pass after meaningful groups of changes.

Run it again before finishing.

The final repository state must build successfully.

If one unfinished theorem would prevent a build, do not leave an unproved theorem declaration in active source.

Record it in the log instead.

---

# 19. Recompute the next frontier after formalization

After every node in the frozen frontier has either:

- become `COMPLETE`; or
- received an explicit blocker status in the formalization log,

recompute the unresolved frontier from the updated ledger and unchanged dependency graph.

The new frontier consists of unresolved active nodes whose direct internal prerequisites are now all `COMPLETE`.

Do not count a blocked node as complete.

Therefore any descendants of a blocked node remain unavailable.

---

# 20. Record but do not attack the new frontier

Append to:

```text
Matroid/FRONTIER_PASS_2.md
```

a section:

```text
## Resulting frontier
```

containing:

- all newly available node IDs;
- names;
- direct prerequisites;
- reason each became exposed;
- any branch still blocked by incomplete frontier nodes.

Also report:

- number of targets attempted;
- number completed;
- number blocked;
- frontier size before the pass;
- frontier size after the pass.

This is informational only.

Do not formalize any node that was not in the frozen initial target set.

---

# 21. Do not recurse

This task performs one frontier depth only.

Even if the resulting frontier contains trivial definitions or obvious exact mathlib matches:

**stop.**

Do not:

- start another frontier pass;
- recursively peel the graph;
- select another layer;
- formalize newly exposed nodes.

The next frontier will be reviewed separately.

---

# 22. Files that must remain fixed

Do not modify:

```text
Manuscript/main.tex
Matroid/DEPENDENCY_EDGES.csv
Matroid/ENTRY_NODES.md
logs/dependency_audit/
```

unless an actual contradiction or corrupt artifact makes continuation impossible.

If such a problem is found, document it rather than silently repairing the dependency analysis.

---

# 23. Completion criteria

This pass is complete when:

1. the current frontier has been mechanically recomputed;
2. the frontier snapshot has been frozen in `Matroid/FRONTIER_PASS_2.md`;
3. every node in that snapshot has been attempted;
4. every completed node follows the manuscript → proof plan → mathlib → Lean workflow;
5. every blocker is explicitly documented;
6. the ledger accurately reflects formalization source and status;
7. `FORMALIZATION_LOG.md` records the proof provenance for every attempted theorem-like target;
8. `lake build` succeeds;
9. the resulting frontier has been mechanically recomputed and recorded;
10. no newly exposed node has been formalized.

Stop at that point.