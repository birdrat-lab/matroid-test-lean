# Complete the Matroid Formalization Through Topological Depth 2

This repository formalizes the matroid mathematics required by the manuscript using an audited internal dependency DAG.

The governing policy is now:

> **Always prioritize smaller topological dependency depth. Do not begin new work at depth `d + 1` while an active unresolved requirement remains at depth `d`.**

This task should clear the remaining shallow layer and, if successful, formalize the complete active depth-2 layer.

The procedure is:

```text
recompute structural depths
        ↓
clear all unresolved depth-1 nodes
        ↓
recompute / validate depths
        ↓
if and only if depth 1 is clear:
freeze the unresolved depth-2 target set
        ↓
attack all depth-2 targets
        ↓
update ledger / log / graph if justified
        ↓
recompute minimum unresolved depth
        ↓
STOP
```

Do not proceed to depth 3 during this task.

---

# 1. Sources of truth

The mathematical source is:

```text
Manuscript/main.tex
```

The canonical requirement inventory is:

```text
Matroid/LEDGER.md
```

The direct internal prerequisite graph is:

```text
Matroid/DEPENDENCY_EDGES.csv
```

The formalization record is:

```text
Matroid/FORMALIZATION_LOG.md
```

The manuscript determines what mathematics must be formalized.

The ledger determines the currently accepted requirement set.

The edge table determines direct internal prerequisites.

Lean/mathlib determine how those requirements are discharged, but not what they mean.

---

# 2. Structural topological depth

Compute the topological depth of every active Matroid requirement mechanically from `DEPENDENCY_EDGES.csv`.

For active node `v`, define:

```text
depth(v) = 0
```

when `v` has no active internal prerequisites.

Otherwise:

```text
depth(v) = 1 + max(depth(u))
```

over all active direct prerequisites:

```text
u → v
```

Only active Matroid requirements count.

Rows scoped only as:

```text
APPLICATION_CONTEXT
OUT_OF_SCOPE_CONTEXT
```

do not participate in the active DAG.

Do not use:

- manuscript section number;
- formalization pass number;
- chronological frontier number;
- shortest distance from a root;
- downstream count

as substitutes for topological depth.

The relevant depth is the **longest direct-prerequisite-chain depth** defined above.

---

# 3. Depth takes priority over leverage

The ordering policy is lexicographic:

```text
1. smaller topological depth
2. only then downstream leverage or convenience
```

A low-leverage depth-1 theorem must be addressed before an attractive depth-2 theorem.

Do not bypass a shallow unresolved node because:

- it has no descendants;
- it is difficult;
- a deeper branch is easier;
- a deeper branch has more downstream nodes.

This policy is intended to eliminate foundational debt.

---

# 4. Historical deeper completions remain valid

Earlier passes completed some nodes at depths greater than the current minimum unresolved depth.

Do not undo those results.

However, do not use their existence as justification for performing **new** work deeper than the current minimum unresolved depth.

The invariant is:

> new formalization work always begins at the minimum unresolved active structural depth.

---

# 5. Produce a depth table

At the beginning of this task, create or update:

```text
Matroid/DEPTHS.csv
```

with at least:

```text
id
name
scope
status
depth
direct_prerequisites
complete_prerequisites
incomplete_prerequisites
```

Compute this mechanically from the canonical ledger and edge table.

Also record in:

```text
Matroid/FRONTIER.md
```

the current minimum unresolved structural depth and all unresolved nodes at that depth.

Do not manually assign depths.

---

# 6. Expected current minimum unresolved depth

For the current repository state, the expected minimum unresolved depth is:

```text
depth 1
```

with:

```text
N061  Graphic matroid
N080  Finite closure-exchange representation
```

This is a sanity check only.

Recompute it.

If the computed result differs, investigate the ledger and edge table before doing proof work.

Do not alter the graph merely to reproduce this expected result.

---

# 7. Phase A — clear depth 1 completely

Before touching any unresolved depth-2 node, attempt to discharge:

```text
N061  Graphic matroid
N080  Finite closure-exchange representation
```

Both must receive serious focused treatment.

Do not treat previous blocker reports as final conclusions.

The earlier attempts identified where the missing work lies; this pass should now attack that work directly.

---

# 8. Universal proof workflow

For every theorem or construction target, use this order:

```text
ledger entry
    ↓
exact manuscript statement / definition
    ↓
manuscript proof or surrounding derivation
    ↓
mathematical proof/construction plan
    ↓
inspect pinned mathlib
    ↓
Lean design
    ↓
implementation
    ↓
lake build
    ↓
ledger and formalization-log update
```

Do not begin from mathlib theorem search.

First fix the mathematical requirement from the manuscript.

---

# 9. Manuscript proof classifications

Use:

```text
MANUSCRIPT_DEFINITION
MANUSCRIPT_PROOF
MANUSCRIPT_SKETCH
MANUSCRIPT_STATEMENT_ONLY
```

For each theorem-like target, record a concise mathematical proof plan before Lean implementation.

When the manuscript has no proof, say so.

Do not retroactively describe a Lean proof as though it were present in the manuscript.

---

# 10. N061 — Graphic matroid

N061 states:

> A graph's graphic matroid has forests as independent sets.

The manuscript provenance is:

```text
def:graphic-cographic
```

Previous work established that the pinned mathlib does not provide a ready-made graphic-matroid constructor for the manuscript's general graph model.

The previous blocker analysis also found that:

- the manuscript graph model must not be silently replaced by a simple graph if loops or parallel edges matter;
- mathlib's general `Graph α β` type can represent labeled edges, loops, and parallel edges;
- the missing infrastructure is primarily the forest/cycle independence theory and augmentation needed to construct the matroid.

This pass should attack that infrastructure directly.

## Requirements

First determine exactly what graph generality `def:graphic-cographic` requires.

Then construct or recover a mathematically faithful graphic matroid.

The intended interface is:

```text
ground elements = graph edges
independent sets = forests
```

or the exact equivalent supported by the manuscript.

Prefer existing graph theory from mathlib where available.

If an appropriate matroid constructor from an independence predicate is useful, use the existing mathlib Matroid construction infrastructure rather than defining a competing matroid structure.

The central mathematical obligation is the augmentation/exchange property for forests.

## Missing-prerequisite rule

If resolving N061 reveals a **substantive reusable mathematical theorem** that is genuinely missing from `LEDGER.md`, do not hide it inside an opaque local helper.

Instead:

1. determine whether it is truly a manuscript/formalization requirement;
2. add a canonical ledger entry if justified;
3. add the direct dependency edge;
4. recompute structural depths.

If the new prerequisite lies at depth 1 or lower, it becomes part of the current shallow layer and must be addressed before depth 2.

Routine implementation lemmas need not become ledger nodes.

Document the distinction.

---

# 11. N080 — Finite closure-exchange representation

N080 states:

> A finite extensive, monotone, idempotent closure satisfying Steinitz exchange is the closure of a matroid.

Its manuscript context is associated with:

```text
def:matroidal-query-system
```

The manuscript treats this as standard but does not provide a proof.

The previous pass found no exact mathlib constructor from these closure axioms.

Therefore treat N080 as a real local theorem-construction problem, not merely a theorem-search problem.

## Preferred mathematical route

Begin from the supplied finite closure operator and define the corresponding independence notion in a mathematically standard way.

Possible proof routes should be evaluated from the closure axioms themselves, for example through exchange-compatible independent sets or bases.

The required result is not merely:

> some matroid exists.

The resulting matroid must have **the supplied closure operator**.

Therefore the proof has two essential obligations:

```text
1. construct a matroid satisfying augmentation;
2. prove its matroid closure equals the original closure.
```

Do not mark N080 complete after proving only the first.

Use manuscript terminology and the existing project conventions.

Record clearly which standard theorem or argument supplies the missing implication.

---

# 12. No depth-2 work while depth 1 remains active and unresolved

After serious attempts on N061 and N080, recompute the active minimum unresolved depth.

Proceed to Phase B only if there is **no active unresolved depth-1 node**.

Acceptable reasons for a former depth-1 row to leave the active unresolved set are:

```text
COMPLETE
```

or a justified specification correction such as:

```text
re-scoped out of the active Matroid graph
```

or:

```text
replaced by newly identified more primitive ledger requirements
```

In the latter case, formalize those newly identified shallow requirements first.

A blocker status by itself does **not** authorize moving deeper.

If either N061 or N080 remains a valid active unresolved depth-1 requirement at the end of the attempt:

```text
STOP
```

Do not attack depth 2.

Produce a focused blocker report instead.

---

# 13. Phase B — validate the depth-2 layer

If depth 1 has been completely cleared, recompute structural depths before continuing.

The expected unresolved active depth-2 nodes are:

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

This list is a sanity check.

The mechanically recomputed DAG is authoritative.

If the set differs, document why.

---

# 14. Freeze depth 2 before formalizing it

Once depth 1 is clear and depth 2 has been recomputed, freeze the target set in:

```text
Matroid/FRONTIER.md
```

under:

```text
## Depth-2 target snapshot
```

Record for every target:

```text
ID
name
direct prerequisites
manuscript provenance
current status
```

Do not add newly exposed depth-2 nodes later in the same pass without first determining whether the graph changed because of a legitimate specification repair.

---

# 15. Attack the entire depth-2 layer

Attempt every unresolved active node at structural depth 2.

Do not prioritize one mathematical branch over another by downstream count until all depth-2 nodes have at least been seriously attempted.

Within depth 2, downstream leverage may determine ordering, but not inclusion.

The target is to **clear the depth**, not merely maximize descendant release.

---

# 16. Depth-2 targets: expected mathematical character

The expected depth-2 set contains several different categories.

## Elementary definitions / constructions

```text
N024  Deletion
N036  Single-element extension
N051  Regularity
```

Prefer exact existing mathlib concepts when they faithfully match the manuscript.

Do not introduce redundant project definitions unnecessarily.

## Representation facts

```text
N046  Represented circuits
N047  Projective equivalence
N111  Nonzero column rescaling
N112  Ambient linear isomorphism
```

These should build on the already completed vector-matroid/representation foundations.

Preserve indexed-element multiplicity where the manuscript requires it.

## Totally unimodular facts

```text
N056  TU pivot and standard form
N057  TU identity augmentation
```

Treat these as exact matrix claims.

For N057 especially, the ledger currently records:

```text
STATEMENT_DESIGN
```

Do not formalize an unnecessarily broad theorem merely because the prose says "identity augmentation."

Read the displayed block matrices actually used by the manuscript and formalize the narrow statement required there unless a clean general theorem is both correct and useful.

## Graphic/cographic facts

```text
N062  Cographic matroid
N258  Incidence representation of a graphic matroid
```

These are only available once N061 is complete.

For N062, use the manuscript definition through duality and verify the minimal-cut circuit characterization rather than merely defining an abstract dual.

For N258, prove that the edge-incidence vector configuration realizes the same cycle dependencies as the newly established graphic matroid.

## Uniform-matroid fact

```text
N130  Corank-one uniform target circuit
```

Preserve the indexed target/ground-set formulation used by the manuscript.

---

# 17. Use the established formalization-source categories

For every completed target record one of:

```text
MATHLIB_EXACT
MATHLIB_BRIDGE
LOCAL_PROOF
```

Use `MATHLIB_EXACT` only when the existing formal object or theorem really matches the manuscript requirement.

Use `MATHLIB_BRIDGE` when a local manuscript-facing statement translates from an existing theorem.

Use `LOCAL_PROOF` when substantive proof work is supplied here.

---

# 18. Do not force completion

No use of:

```text
sorry
admit
axiom
```

is permitted to claim a target complete.

If a depth-2 target fails after a serious attempt, record the precise failure.

Possible blocker categories include:

```text
BLOCKED_STATEMENT
BLOCKED_MATHLIB_INFRASTRUCTURE
BLOCKED_PROOF
BLOCKED_SCOPE
MISSING_PREREQUISITE
```

However, because this task is enforcing strict breadth-first depth completion, an unresolved valid depth-2 requirement means:

> depth 2 is not complete.

Do not move to depth 3.

---

# 19. Missing prerequisite discovery

Formalization may reveal that the current DAG omitted a direct prerequisite.

If so:

1. distinguish a routine implementation helper from a substantive mathematical requirement;
2. if substantive, add or refine the ledger entry;
3. add the direct dependency edge;
4. record manuscript evidence;
5. recompute depths.

Do not preserve an incorrect depth assignment merely to finish the planned pass.

If a new node is inserted at depth less than or equal to the current working depth, it must be handled before the project advances beyond that depth.

This rule is essential.

Formalization is allowed to correct the dependency model.

---

# 20. Dependency-edge discipline

When modifying:

```text
Matroid/DEPENDENCY_EDGES.csv
```

add only direct prerequisites.

The direction is:

```text
prerequisite → dependent
```

Do not add transitive edges.

Every new edge must record:

```text
edge_type
tex_evidence
justification
confidence
```

Use:

```text
DEFINITIONAL
PROOF
```

as the primary edge types.

Document every graph correction in `FORMALIZATION_LOG.md`.

---

# 21. Lean source organization

Continue organizing Lean files by mathematical subject, not by pass number or frontier depth.

Do not create files named:

```text
Depth1.lean
Depth2.lean
Frontier3.lean
Pass4.lean
```

Put declarations into mathematically appropriate modules such as:

```text
RankClosure.lean
Minors.lean
Representation.lean
Graphic.lean
Regular.lean
Uniform.lean
```

Create a new mathematical module only when the content warrants it.

Chronology belongs in logs, not filenames.

---

# 22. Formalization log

Continue:

```text
Matroid/FORMALIZATION_LOG.md
```

For each target record:

```text
Ledger ID:
Structural depth:
TeX label:
Requirement:
Manuscript proof status:
Manuscript proof/construction plan:
Lean declaration:
Formalization source:
Mathlib declarations used:
Deviation from manuscript route:
Result:
Build status:
Notes:
```

For blocked targets, explain the exact missing mathematical step.

For graph corrections, record:

```text
old prerequisite structure
new prerequisite structure
reason
manuscript evidence
```

---

# 23. Ledger updates

Update:

```text
Matroid/LEDGER.md
```

only for targets actually investigated in this task or for justified specification corrections.

Use `COMPLETE` only when:

- the exact manuscript-facing requirement has been discharged;
- provenance is recorded;
- the formalization source is known;
- and `lake build` succeeds.

Do not mark a row complete merely because a related stronger or weaker theorem exists.

---

# 24. Build discipline

Run:

```text
lake build
```

after meaningful groups of changes.

Run it after finishing the depth-1 work.

If Phase B begins, run it repeatedly during depth-2 work.

Run it once more before finishing.

The repository must remain buildable.

---

# 25. End-of-pass depth audit

At the end, regenerate `Matroid/DEPTHS.csv` from the final ledger and edge table.

Then report in `Matroid/FRONTIER.md`:

```text
minimum unresolved structural depth
unresolved nodes at that depth
number of active nodes by depth
number complete by depth
number unresolved by depth
```

If depth 2 has been completely cleared, identify the resulting depth-3 target set.

Do not formalize any depth-3 node.

If depth 1 or depth 2 remains unresolved, state that explicitly.

---

# 26. Stop conditions

There are two possible successful stopping modes.

## A. Depth 1 does not clear

If N061, N080, or a newly discovered shallower prerequisite remains a valid active unresolved node:

- document the blocker precisely;
- keep the repository buildable;
- recompute depths;
- stop.

Do not perform depth-2 work.

## B. Depth 1 clears

Then attempt the complete unresolved depth-2 layer.

After every depth-2 target has been attempted:

- update ledger and log;
- recompute depths;
- report whether depth 2 is fully clear;
- identify the next minimum unresolved depth;
- stop.

Do not begin depth 3.

---

# 27. Completion objective

The desired outcome of this task is:

```text
all active depths < 2 complete
        +
all active depth-2 nodes attempted
```

The strongest successful outcome is:

```text
depth 0: clear
depth 1: clear
depth 2: clear
```

with the next unresolved structural depth identified but untouched.

The purpose of this pass is to establish and test strict breadth-first formalization by dependency depth.