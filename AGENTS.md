# Final Matroid Ledger and Entry-Node Analysis

This repository is currently completing the **mathematical specification phase** of the matroid formalization project.

The previous passes have already:

- extracted matroid requirements from the manuscript;
- normalized those requirements;
- compared the normalized ledger against an independent raw dependency graph;
- and identified a small number of local corrections and additions.

This pass has two objectives only:

1. produce one canonical adjudicated matroid ledger;
2. determine the internal matroid dependency graph and identify the entry nodes from which Lean formalization should begin.

This pass must **not write Lean**.

Do not inspect mathlib.

Do not attempt proofs.

Do not edit any `.lean` file.

Do not design implementation modules.

Stop once the final ledger, dependency edge table, and entry-node report have been produced and validated.

---

# 1. Source of mathematical authority

The frozen manuscript is:

```text
Manuscript/main.tex
```

The manuscript is the final authority for:

- mathematical statements;
- hypotheses;
- proof dependencies;
- and the intended scope of the results.

The historical ledgers and dependency audits are evidence about the manuscript, not substitutes for it.

When a discrepancy remains between historical artifacts, inspect `Manuscript/main.tex`.

Use exact TeX labels whenever possible.

Do not fabricate labels.

Do not silently strengthen, weaken, or generalize a manuscript claim.

---

# 2. Archive the completed audit process

The repository currently contains several artifacts from earlier dependency-analysis stages.

These should no longer remain active working specifications.

Move them into:

```text
logs/dependency_audit/
```

Preserve their contents.

Use `git mv` when possible so history remains easy to follow.

The desired organization is:

```text
logs/dependency_audit/
├── README.md
├── blind/
│   ├── LEDGER_BLIND.md
│   └── BLIND_EXTRACTION_REPORT.md
├── normalization/
│   ├── LEDGER_NORMALIZED.md
│   └── NORMALIZATION_FROZEN
├── comparison/
│   ├── NORMALIZED_VS_RAW_COMPARISON.md
│   └── NORMALIZED_VS_RAW_MAPPING.csv
└── raw_graph/
    ├── dependency_graph_raw.csv
    └── dependency_graph_raw_edges.csv
```

Specifically:

```text
Matroid/LEDGER.md
    → logs/dependency_audit/blind/LEDGER_BLIND.md

Matroid/BLIND_EXTRACTION_REPORT.md
    → logs/dependency_audit/blind/BLIND_EXTRACTION_REPORT.md

Matroid/LEDGER_NORMALIZED.md
    → logs/dependency_audit/normalization/LEDGER_NORMALIZED.md

Matroid/NORMALIZATION_FROZEN
    → logs/dependency_audit/normalization/NORMALIZATION_FROZEN

Matroid/NORMALIZED_VS_RAW_COMPARISON.md
    → logs/dependency_audit/comparison/NORMALIZED_VS_RAW_COMPARISON.md

Matroid/NORMALIZED_VS_RAW_MAPPING.csv
    → logs/dependency_audit/comparison/NORMALIZED_VS_RAW_MAPPING.csv

Audit/dependency_graph_raw.csv
    → logs/dependency_audit/raw_graph/dependency_graph_raw.csv

Audit/dependency_graph_raw_edges.csv
    → logs/dependency_audit/raw_graph/dependency_graph_raw_edges.csv
```

If `Audit/` becomes empty after these moves, remove the empty directory.

Create:

```text
logs/dependency_audit/README.md
```

explaining briefly that these files record the blind extraction, normalization, and independent normalized-vs-raw validation that preceded the canonical ledger.

Do not rewrite the historical artifacts during the move.

---

# 3. Canonical final ledger

After archiving the historical files, create:

```text
Matroid/LEDGER.md
```

This becomes the **only active matroid requirement ledger**.

It should be derived from the normalized ledger together with the adjudication recorded in the normalized-vs-raw comparison.

Do not perform another manuscript-wide extraction.

The node inventory has already been extensively audited.

This pass should make only corrections justified by the completed comparison or by direct manuscript inspection required to adjudicate those corrections.

---

# 4. Required adjudications

Apply the following conclusions from the completed comparison.

## N098

Re-scope N098 from:

```text
CORE_MATROID
```

to:

```text
APPLICATION_CONTEXT
```

The agreement-projection composition depends on query-partition semantics.

The pure matroid flat-join content is already represented separately.

---

## Triangle signature

Add a new atomic ledger entry for the weighted triangle-signature interface used in the 3-sum calculation.

It should record the manuscript's weighted class sums and the tuple:

```text
(a, p₁, p₂, p₃, c)
```

with exact provenance to the relevant TeX labels, including the displayed triangle-signature equations and the results that use them.

Assign this the next unused normalized identifier:

```text
N266
```

unless direct inspection reveals that identifier is already occupied.

---

## K4 signature

Add a new atomic ledger entry for the weighted `M(K₄)` five-term signature used in the 3-sum theorem.

It should record the five displayed weighted class sums with exact manuscript provenance.

Assign:

```text
N267
```

unless direct inspection reveals that identifier is already occupied.

---

## N206

Retain N206.

Clarify in its notes that the normalized ledger records the closure-union property of the shared-target construction, whereas the raw graph recorded the construction more coarsely.

Do not treat this as a mathematical contradiction.

---

## Normalized-only requirements

Retain the normalized-only mathematical requirements identified by the comparison unless manuscript inspection shows that one is genuinely spurious.

Their absence from the older raw graph is not evidence for deletion.

---

## Recursive sensitivity

Do not add `prop:recursive-r10-sensitivity` as an active Matroid-library requirement merely because it appeared as a raw-only node.

Its stated conclusion concerns Boolean sensitivity.

The matroid-side closure and pointed-R10 ingredients used by its proof are already represented separately.

It may be mentioned in provenance notes if useful, but it should not become an active matroid dependency node unless manuscript inspection exposes a distinct pure matroid theorem that is currently missing.

---

# 5. Stable identifiers

Preserve the existing normalized identifiers `N001`, `N002`, ... wherever possible.

Do not renumber the existing ledger merely to obtain a prettier sequence.

The comparison artifacts already refer to these IDs.

New adjudicated entries should receive new IDs after the existing range.

The final ledger should preserve traceability back to blind `M###` identifiers where that information already exists.

---

# 6. Scope of the dependency graph

After `Matroid/LEDGER.md` has been finalized, construct the dependency relation **among the active matroid requirements in that ledger**.

Do not reuse the old raw dependency graph as the final graph.

The raw graph was manuscript-wide and used a different granularity.

It may be consulted as historical evidence, but the new dependency graph must be derived from the final ledger and the manuscript.

The active formalization graph should normally include entries whose scope is:

```text
CORE_MATROID
MATROID_INTERFACE
```

Do not include `APPLICATION_CONTEXT` or `OUT_OF_SCOPE_CONTEXT` as formalization nodes merely because they remain in the ledger for provenance.

If an application-context row contains a genuinely reusable matroid obligation, that obligation should already exist as a separate active ledger row.

If scope remains unresolved for an entry, record that explicitly rather than silently inserting or deleting it from the graph.

---

# 7. Meaning of a dependency edge

For active ledger entries `A` and `B`, add an edge:

```text
A → B
```

only when `A` is genuinely required in order to define, state, or prove `B`.

An edge is not merely conceptual similarity.

Do not add an edge because two results concern the same mathematical topic.

Do not add an edge merely because `A` appears earlier in the manuscript.

Do not infer dependencies from chapter order.

The direction is always:

```text
prerequisite → dependent
```

---

# 8. Edge types

Use exactly these primary edge types unless a genuinely necessary distinction arises.

## `DEFINITIONAL`

Use when the target cannot be formulated in the project's mathematical vocabulary without the source definition, construction, or interface.

Examples include a theorem stated in terms of closure depending definitionally on the closure object it uses.

## `PROOF`

Use when the target can be stated independently of the source, but the manuscript proof or intended mathematical derivation uses the source result.

A theorem may have both definitional and proof prerequisites.

Do not encode transitive conceptual relationships as direct proof edges.

---

# 9. Prefer direct prerequisites

The new graph should record **direct mathematical prerequisites**, not every transitive ancestor.

Suppose:

```text
A → B
B → C
```

and the proof of `C` only needs the result `B`.

Do not also add:

```text
A → C
```

merely because `A` is transitively required through `B`.

Add `A → C` only if `C` independently uses `A`.

This keeps the graph operational and makes its frontier meaningful.

---

# 10. Dependency evidence

Every edge must be auditable.

Create:

```text
Matroid/DEPENDENCY_EDGES.csv
```

with at least these columns:

```text
source_id
source_name
target_id
target_name
edge_type
tex_evidence
justification
confidence
```

`tex_evidence` should contain exact TeX labels or a concise manuscript location.

`justification` should explain why the source is a direct prerequisite of the target.

Use confidence values such as:

```text
HIGH
MEDIUM
LOW
```

Do not use `LOW` confidence to conceal an unresolved mathematical question.

If a dependency cannot be determined, document it explicitly in the entry-node report.

---

# 11. External foundations are not internal edges

The objective is to identify roots of the **matroid requirement graph**.

A ledger node may depend on mathematics outside this graph, for example:

- finite sets;
- elementary logic;
- graph theory;
- linear algebra;
- matrices;
- fields;
- arithmetic.

Do not invent artificial ledger nodes for all such external foundations during this pass.

Do not inspect mathlib to determine whether those foundations are already formalized.

Instead, record important external prerequisites in the ledger notes or entry-node report when they affect interpretation.

An internal entry node means:

> no prerequisite among the other active matroid ledger requirements.

It does **not** mean mathematically assumption-free.

---

# 12. Strict entry nodes

After constructing `Matroid/DEPENDENCY_EDGES.csv`, compute the indegree of every active matroid node.

A **strict entry node** is an active formalization node with:

```text
internal indegree = 0
```

where only active matroid requirements count toward indegree.

Identify all strict entry nodes.

Do not choose them manually.

They must follow from the final ledger and dependency edge table.

---

# 13. First theorem frontier

Strict roots may include mostly definitions or primitive constructions.

To identify where theorem proving should begin, also compute a **first theorem frontier**.

A theorem-like entry belongs to the first theorem frontier when all of its internal prerequisites are either:

- strict entry definitions/constructions; or
- absent because it has no internal matroid theorem prerequisite.

This is not a ranking of importance.

It identifies theorem-like statements that become available immediately after the foundational vocabulary is formalized.

Keep strict entry nodes and the first theorem frontier separate.

---

# 14. Entry-node report

Create:

```text
Matroid/ENTRY_NODES.md
```

The report should contain:

## Final graph summary

Report:

- number of active ledger nodes;
- number of dependency edges;
- number of `DEFINITIONAL` edges;
- number of `PROOF` edges;
- number of strict entry nodes;
- number of first-frontier theorem-like nodes;
- any entries excluded from the active graph because of scope.

## Strict entry nodes

For every strict entry node, give:

- ledger ID;
- name;
- concise mathematical role;
- manuscript provenance;
- scope;
- whether it is primarily a definition, construction, or theorem;
- any obvious external non-matroid foundations it relies on.

Do not discuss Lean implementation.

## First theorem frontier

List theorem-like nodes that can be approached after the strict foundational definitions/constructions.

For each, record its direct internal prerequisites.

Again, do not discuss Lean implementation.

## Ambiguities or blockers

Record:

- unresolved statement-design questions;
- uncertain edges;
- scope ambiguities;
- cases where the manuscript does not determine a unique dependency structure.

Do not resolve such issues by consulting mathlib or writing code.

## Suggested starting boundary

Conclude with a purely mathematical description of the smallest coherent initial formalization boundary.

This should mean something like:

> formalize these definitions/constructions and these immediately exposed theorem nodes first.

Do not provide Lean code.

Do not select modules or filenames.

---

# 15. Validation checks

Before finishing, verify mechanically that:

- every active `source_id` and `target_id` in `DEPENDENCY_EDGES.csv` exists in the final ledger;
- no edge is a self-loop;
- duplicate edges with the same source, target, and type do not exist;
- all strict entry nodes actually have indegree zero;
- every non-entry active node has at least one incoming internal edge, unless explicitly documented as a graph-construction anomaly;
- application-context rows are not accidentally treated as formalization roots;
- N098 has the corrected scope;
- the triangle-signature and K4-signature entries are present;
- the historical audit files have been moved under `logs/dependency_audit/`;
- historical artifacts were not rewritten during archival.

If cycles occur, do not simply break them arbitrarily.

Inspect whether the cycle is caused by:

- an overly broad ledger entry;
- confusion between definition and theorem;
- a transitive edge;
- or a genuine mutually defined construction.

Document and resolve the issue mathematically.

The intended dependency graph should be suitable for bottom-up formalization.

---

# 16. Prohibited work

During this pass, do not:

- edit `.lean` files;
- create new `.lean` files;
- inspect mathlib;
- search for Lean theorem names;
- prove any ledger statement;
- write theorem skeletons;
- use `sorry`, `axiom`, or `admit`;
- redesign the future Lean module hierarchy;
- begin formalization of entry nodes.

The output of this pass is only the mathematical starting specification.

---

# 17. Required active outputs

When finished, the active dependency-analysis artifacts should be:

```text
Matroid/LEDGER.md
Matroid/DEPENDENCY_EDGES.csv
Matroid/ENTRY_NODES.md
```

The previous extraction, normalization, comparison, and raw-graph artifacts should live under:

```text
logs/dependency_audit/
```

The next project phase will begin from `ENTRY_NODES.md`.

That later phase, not this one, will determine how the entry nodes should be expressed and discharged in Lean.