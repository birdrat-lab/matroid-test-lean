# Normalized vs. Raw Dependency Comparison

This repository is currently performing a **dependency-analysis comparison pass** for the matroid/span-program manuscript.

The purpose of this pass is to compare two independently produced descriptions of the manuscript's matroid dependencies:

1. the normalized matroid dependency ledger;
2. the older raw manuscript-wide dependency graph.

This pass is analytical only.

Do not write Lean.

Do not inspect mathlib.

Do not design or modify the future Matroid library.

Do not attempt proofs.

Do not compute the final entry-node graph yet.

The only objective is to compare the two dependency analyses faithfully and identify discrepancies that require manuscript adjudication.

---

# 1. Source of authority

The frozen manuscript is:

    Manuscript/main.tex

The manuscript is the final authority for determining:

- what mathematical facts are stated;
- what facts proofs actually use;
- whether a claimed dependency is real;
- and how discrepancies between the two analyses should be interpreted.

Neither the normalized ledger nor the raw dependency graph is ground truth.

Do not alter manuscript mathematics to make the two analyses agree.

Use exact TeX labels whenever possible.

Do not fabricate labels.

For an unlabeled dependency used inside a proof, record the TeX label of the result whose proof uses it and enough context to recover the relevant step from `Manuscript/main.tex`.

---

# 2. Artifacts being compared

## 2.1 Normalized ledger

The normalized matroid dependency specification is:

    Matroid/LEDGER_NORMALIZED.md

It contains normalized `N###` entries.

These entries were produced by:

- first extracting manuscript-wide matroid requirements blindly;
- then splitting compound obligations;
- merging genuine duplicates;
- separating application context from reusable matroid mathematics;
- and clarifying provenance and scope.

Treat `LEDGER_NORMALIZED.md` as frozen during this pass.

Do not modify it.

The earlier blind extraction:

    Matroid/LEDGER.md

is preserved for provenance and may be consulted when necessary to understand how a normalized entry arose, but it is not the primary object being compared.

---

## 2.2 Raw dependency graph

The older independent dependency analysis is represented by:

    Audit/dependency_graph_raw.csv
    Audit/dependency_graph_raw_edges.csv

`dependency_graph_raw.csv` is the primary node table.

It contains one row per raw dependency node.

Its fields include:

- `raw_node_id`
- `raw_node_name`
- `raw_node_type`
- `raw_cluster`
- `tex_label`
- `display_number`
- `raw_description`
- `indegree`
- `outdegree`
- `incoming_raw_node_ids`
- `incoming_dependency_types`
- `outgoing_raw_node_ids`
- `outgoing_dependency_types`

`dependency_graph_raw_edges.csv` is the companion edge table.

It contains one row per dependency arrow and preserves the full raw graph structure.

Its fields include:

- `raw_edge_id`
- source node metadata;
- target node metadata;
- `dependency_type`

Use the node table for semantic matching.

Use the edge table when the surrounding dependency structure helps interpret a node.

The raw graph is manuscript-wide, not matroid-only.

It therefore contains:

- matroid facts;
- non-matroid mathematics;
- definitions;
- manuscript results;
- external obligations;
- certificate/data nodes;
- and other formalization-oriented interfaces.

Do not assume every raw node should have a normalized matroid counterpart.

---

# 3. Meaning of "raw"

The term **raw dependency graph** means:

> the older independent manuscript-wide dependency analysis before the present normalized matroid-ledger process.

"Raw" does not mean naive or purely syntactic.

The raw graph may already contain:

- semantic proof dependencies;
- manually reviewed edges;
- bundled external facts;
- inferred dependencies;
- certificate nodes;
- and other interpretation.

Preserve its structure as an independent historical analysis.

Do not rewrite raw nodes to resemble normalized entries.

---

# 4. Purpose of the comparison

The comparison asks:

> Does the normalized matroid dependency ledger account for the matroid dependencies independently visible in the raw manuscript-wide graph?

This is a validation and discrepancy-discovery exercise.

It is not an attempt to maximize numerical agreement.

Agreement increases confidence that a requirement was independently recovered.

Disagreement identifies manuscript locations that require closer inspection.

The manuscript determines the resolution.

---

# 5. Comparison must be semantic

Do not compare only names, labels, or strings.

Compare mathematical content.

A normalized entry may correspond to:

    one raw node
    several raw nodes
    part of one raw node
    several parts of several raw nodes
    no raw node

Likewise, one raw node may correspond to several normalized entries.

Many such cases are granularity differences, not errors.

Compare:

- hypotheses;
- conclusions;
- mathematical objects involved;
- manuscript proof role;
- and exact TeX evidence.

---

# 6. Comparison classifications

Use the following classifications.

## `AGREEMENT`

The normalized entry and raw node or nodes identify substantially the same mathematical obligation at compatible granularity.

## `GRANULARITY_MISMATCH`

Both analyses identify the same underlying mathematics, but one bundles facts that the other splits.

This is not automatically an error.

## `NORMALIZED_ONLY_CANDIDATE`

A normalized entry has no clear raw counterpart.

Possible explanations include:

- the normalized extraction found a dependency the raw graph missed;
- the normalized ledger over-extracted context;
- the raw graph encoded the dependency only indirectly;
- or the match has not yet been found.

Check the manuscript before drawing a conclusion.

## `RAW_ONLY_CANDIDATE`

A raw matroid-relevant node has no clear normalized counterpart.

Possible explanations include:

- a missing normalized requirement;
- a coarse raw external bundle;
- an obsolete or unnecessary dependency;
- an implementation-oriented raw node rather than a mathematical obligation;
- or a missed match.

Check the manuscript before proposing a correction.

## `SCOPE_MISMATCH`

The two analyses identify related material but disagree about whether it belongs in the matroid dependency specification.

## `FORMULATION_MISMATCH`

Both analyses appear to refer to the same manuscript dependency but extract materially different mathematical statements.

These cases require manuscript inspection.

## `DUPLICATE_OR_EQUIVALENT`

The apparent discrepancy is caused by equivalent formulations or duplicated obligations.

Explain the claimed equivalence.

Do not merely assert it.

## `NON_MATROID_RAW_NODE`

The raw node is outside the scope of the normalized matroid ledger.

Examples may include:

- adversary-bound facts;
- general optimization;
- ordinary linear algebra;
- quantum-query statements;
- certificate data;
- application-specific definitions.

## `UNRESOLVED`

The relationship cannot be determined confidently.

Preserve the uncertainty.

---

# 7. Required comparison procedure

Perform the comparison in both directions.

## Pass A: normalized to raw

For every `N###` entry in:

    Matroid/LEDGER_NORMALIZED.md

determine:

1. whether a corresponding raw node or node group exists;
2. which `raw_node_id` values correspond;
3. the comparison classification;
4. the exact manuscript evidence;
5. whether the difference is substantive or merely structural.

Every normalized entry must appear in the final mapping, including entries with no raw match.

---

## Pass B: raw to normalized

Inspect every raw node that is plausibly matroid-related.

Determine whether it:

- matches a normalized entry;
- participates in a granularity mismatch;
- is non-matroid;
- is merely an implementation/certificate/context node;
- or represents a possible omission from the normalized ledger.

Do not limit this pass to raw nodes that already have obvious normalized matches.

The purpose of the reverse pass is to detect things the normalized extraction may have missed.

---

# 8. Manuscript adjudication

For every nontrivial discrepancy, inspect `Manuscript/main.tex`.

Record:

- the relevant TeX label or labels;
- the proof or statement location;
- whether the dependency is explicit or inferred semantically;
- what mathematical fact the manuscript actually requires;
- whether the normalized ledger represents it;
- whether the raw graph represents it;
- and which interpretation appears better supported.

Do not silently modify either source artifact.

If the manuscript does not clearly resolve the issue, classify it as `UNRESOLVED`.

---

# 9. Required output files

Do not modify:

    Matroid/LEDGER.md
    Matroid/LEDGER_NORMALIZED.md
    Audit/dependency_graph_raw.csv
    Audit/dependency_graph_raw_edges.csv
    Manuscript/main.tex

Create exactly these primary comparison artifacts:

    Matroid/NORMALIZED_VS_RAW_MAPPING.csv
    Matroid/NORMALIZED_VS_RAW_COMPARISON.md

---

# 10. Mapping CSV

`Matroid/NORMALIZED_VS_RAW_MAPPING.csv` should support many-to-many relationships.

Use one row per normalized/raw relationship.

Recommended columns:

    normalized_id
    normalized_name
    raw_node_id
    raw_node_name
    classification
    tex_labels
    use_type
    semantic_comparison
    manuscript_adjudication
    proposed_action
    confidence

If a normalized entry has no raw counterpart, include a row with an empty `raw_node_id`.

If a raw matroid-relevant node has no normalized counterpart, include a row with an empty `normalized_id`.

Do not discard unmatched items.

---

# 11. Comparison report

`Matroid/NORMALIZED_VS_RAW_COMPARISON.md` should contain the following sections.

## Method

Describe:

- which files were compared;
- that the analyses were independently produced;
- that matching was semantic rather than textual;
- and that `Manuscript/main.tex` was used for adjudication.

## Summary

Report:

- total normalized entries examined;
- total raw nodes examined;
- number of raw nodes judged matroid-relevant;
- clear agreements;
- granularity mismatches;
- normalized-only candidates;
- raw-only candidates;
- scope mismatches;
- formulation mismatches;
- duplicate/equivalent cases;
- unresolved cases;
- non-matroid raw nodes.

Do not call these accuracy scores.

There is no independent gold-standard dependency graph.

## Major discrepancy families

Group related discrepancies.

Examples may include:

- closure/circuit facts;
- represented matroid facts;
- minor operations;
- duality;
- regular matroids;
- totally unimodular representation facts;
- 1-, 2-, or 3-sum structure;
- R10-specific facts;
- graphic/cographic facts;
- source-matroid constructions.

Use whatever families actually arise from the comparison.

## Systematic methodological differences

Identify patterns in how the two analyses behaved.

For example:

- one analysis bundled standard external mathematics more aggressively;
- one extracted more implicit proof obligations;
- one preserved more application context;
- one produced finer atomic statements;
- one represented definitions separately while the other folded them into theorem nodes.

This section is important.

## Proposed corrections

List possible changes to the normalized ledger, but do not apply them.

Separate:

- clear corrections;
- likely corrections;
- optional granularity refinements;
- unresolved issues requiring human review.

For each proposed correction, cite the normalized ID, raw node ID where relevant, and manuscript TeX evidence.

---

# 12. No downstream work in this pass

Do not proceed beyond the comparison.

In particular, do not:

- edit the normalized ledger;
- create an adjudicated ledger;
- construct a new dependency graph;
- compute indegree-zero entry nodes;
- inspect mathlib;
- write Lean statements;
- write Lean proofs;
- alter module structure;
- propose implementation files;
- or begin formalization.

Those are separate later phases.

The output of this task is the comparison itself.

Stop after producing and validating:

    Matroid/NORMALIZED_VS_RAW_MAPPING.csv
    Matroid/NORMALIZED_VS_RAW_COMPARISON.md

---

# 13. Quality standard

The comparison should be auditable.

A reviewer should be able to start from any row in the mapping and answer:

1. what normalized requirement is being discussed;
2. what raw graph node or nodes it was compared against;
3. what manuscript text supports the relationship;
4. why the classification was chosen;
5. and whether any correction is being proposed.

Prefer explicit uncertainty to forced agreement.

The purpose of this pass is to discover where the two independent dependency analyses agree and disagree before any further formalization work begins.