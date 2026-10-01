# Matroid Formalization Pilot

This repository develops a reusable Lean library for the matroid theory required by the matroid/span-program manuscript.

The immediate objective is methodological: construct an auditable manuscript-to-Lean dependency pipeline before attempting substantial formal proofs.

The Matroid library should ultimately provide the complete matroid-facing API required by the manuscript, including matroid facts first used outside the manuscript's background section.

## 1. Sources of authority

`Manuscript/main.tex` is the frozen manuscript snapshot for this repository.

Do not modify files under `Manuscript/`.

The manuscript is the authority for determining what mathematical statements and dependencies the formalization must support. External audits, previous ledgers, and dependency graphs are evidence for comparison, not ground truth.

Use exact TeX labels whenever possible. Displayed numbering may be recorded for readability, but TeX labels are the stable manuscript identifiers.

When a required fact has no TeX label of its own, record the exact TeX label of each result whose statement or proof uses it, together with enough local context to recover the use from `Manuscript/main.tex`.

Do not fabricate labels. Do not silently strengthen, weaken, generalize, or replace manuscript statements.

## 2. Scope of the Matroid library

`Matroid/` is intended to become the reusable matroid library required by the full manuscript.

A definition, theorem, construction, or auxiliary fact belongs in this library when its mathematical content is matroid-theoretic independently of span programs, adversary bounds, quantum query complexity, witness energies, or application-specific optimization.

Facts may belong in this library even if they first appear much later in the manuscript.

`Matroid/` may depend on mathlib. It must not depend on span-program, adversary-bound, quantum-query, or application-specific definitions.

Use mathlib's `Matroid` type as the foundational matroid object. Do not introduce a competing foundational matroid structure.

`Matroid/Matroid.lean` is the public import point. Internal implementation may be divided under `Matroid/Internal/`.

## 3. What counts as a dependency

The ledger is a mathematical dependency ledger, not an inventory of labeled manuscript statements.

Include every distinct matroid-theoretic fact, construction, or object on which a manuscript argument materially relies, whether or not that fact:

- has its own theorem, proposition, lemma, or definition environment;
- has a TeX label;
- is stated in the matroid-background section;
- is explicitly cited;
- is described as standard or well known;
- appears only inside prose or a proof;
- is imported from external matroid literature;
- or is used implicitly without being named.

For every proof, ask: if all external matroid knowledge were removed, what matroid facts would be needed to justify the proof?

During dependency extraction, record the theorem actually required by the manuscript. Do not recursively reconstruct the entire literature proof behind an imported theorem. Its prerequisites can be refined later if it must be proved locally.

## 4. Preserve the blind baseline

`Matroid/LEDGER.md` is the raw blind extraction produced before consulting any external dependency audit.

Once the blind extraction has been accepted as a baseline, **do not edit it to improve agreement with later analyses**.

Methodological repairs belong in a new file:

    Matroid/LEDGER_NORMALIZED.md

The normalized ledger may split, merge, re-scope, or clarify blind entries, but every normalized row must record which blind IDs it came from.

Use normalized IDs `N001`, `N002`, ... rather than reusing or renumbering the blind `M###` IDs.

If blind entries are merged, list all source IDs. If a blind entry is split, each child row should cite the same source ID and explain the split.

## 5. Normalize granularity before external comparison

A normalized ledger entry should be close to an atomic mathematical declaration that could reasonably become one Lean theorem, definition, or structure interface.

Split a blind entry when it bundles logically independent facts that may have different hypotheses, different downstream uses, or different formal-library provenance. Examples include bundles such as closure extensivity/monotonicity/idempotence/exchange or represented rank/closure/circuit characterizations.

Do not split merely for cosmetic reasons. Closely coupled equivalent formulations may remain together when one Lean declaration can naturally expose them.

Merge entries only when they are genuinely the same mathematical obligation. Preserve all manuscript uses and all original blind IDs in the merged row.

When equivalence is plausible but not established, keep the entries separate and mark the relationship for review.

## 6. Scope classification

Every normalized entry must have a `Scope` field with one of:

- `CORE_MATROID`: a purely matroid-theoretic object or fact suitable for the reusable Matroid library;
- `MATROID_INTERFACE`: a purely matroid-theoretic lemma or reformulation introduced because an application needs it, but stated without span-program, adversary, quantum, or optimization-specific objects;
- `APPLICATION_CONTEXT`: a manuscript claim whose full statement belongs outside the Matroid library, but which contains or motivates a matroid obligation that should be extracted separately;
- `OUT_OF_SCOPE_CONTEXT`: contextual material that does not itself belong in the Matroid library and yields no additional matroid API obligation;
- `SCOPE_UNRESOLVED`: boundary unclear and requires human review.

Do not place an adversary-value, witness-energy, or span-program optimization theorem in the Matroid public API merely because its proof uses matroid facts. Extract the matroid-side obligation into its own `CORE_MATROID` or `MATROID_INTERFACE` row and classify the full application theorem as context.

## 7. Separate mathematical provenance from formalization source

Do not use `MATHLIB_CANDIDATE` as mathematical provenance.

Each normalized entry must have two separate fields.

### Mathematical provenance

Use one of:

- `MANUSCRIPT_DEFINITION`
- `MANUSCRIPT_PROVED`
- `EXTERNAL_CITED`
- `EXTERNAL_UNCITED_STANDARD`
- `CERTIFICATE_DERIVED`
- `PROVENANCE_UNRESOLVED`

This field answers: where does the mathematics come from in the manuscript's epistemic structure?

### Formalization source

Use one of:

- `NOT_CHECKED`
- `MATHLIB_EXACT`
- `MATHLIB_BRIDGE`
- `LOCAL_PROOF`
- `LOCAL_CERTIFICATE`
- `FORMALIZATION_SOURCE_UNRESOLVED`

This field answers: how will the Lean project obtain the result?

During normalization before mathlib reconnaissance, the normal value is `NOT_CHECKED`.

Do not mark `MATHLIB_EXACT` or `MATHLIB_BRIDGE` without identifying the exact fully qualified declaration(s).

## 8. Normalized ledger schema

Each normalized row should record at least:

- normalized ID `N###`;
- blind source ID(s) `M###`;
- concise name;
- atomic mathematical requirement;
- exact TeX label where stated/defined, if any;
- exact TeX labels of material uses;
- use type: explicit reference/invocation or semantic inference;
- scope classification;
- mathematical provenance;
- formalization source;
- formalization status;
- notes on hypotheses, equivalences, splits/merges, ambiguity, and manuscript context.

Recommended formalization statuses:

- `IDENTIFIED`
- `STATEMENT_DESIGN`
- `LEAN_STATED`
- `MATHLIB_MATCH`
- `BRIDGE_PROVED`
- `PROVED_LOCAL`
- `COMPLETE`

## 9. Freeze normalization before revealing held-out audits

The normalization pass must be performed without consulting Astra or any other previous dependency audit.

During normalization, do not inspect directories designated as held-out audit material.

After the normalized ledger has been reviewed and committed, create a marker file:

    Matroid/NORMALIZATION_FROZEN

The marker should record the Git commit hash containing the frozen normalized ledger.

Do not consult held-out audit artifacts unless:

1. `Matroid/NORMALIZATION_FROZEN` exists; and
2. the current task explicitly requests an external-audit comparison.

This separation is intentional and part of the experiment.

## 10. Astra comparison methodology

Held-out Astra artifacts, when supplied, should live under a clearly separated path such as:

    Audit/AstraHeldout/

Treat them as an independent prior analysis, not as truth.

The comparison must be semantic. Do not compare only names or IDs.

For each normalized matroid requirement, determine whether Astra contains the same mathematical obligation, a coarser bundle containing it, a finer decomposition of it, or no corresponding obligation.

For Astra nodes not matched to a normalized entry, determine whether they represent:

- a genuinely missed matroid dependency;
- non-matroid context;
- a certificate/data node;
- an implementation/interface node;
- a duplicate or equivalent formulation;
- or a granularity difference.

Use these comparison categories:

- `AGREEMENT`
- `CODEX_ONLY_CANDIDATE`
- `ASTRA_ONLY_CANDIDATE`
- `GRANULARITY_MISMATCH`
- `SCOPE_MISMATCH`
- `FORMULATION_MISMATCH`
- `DUPLICATE_OR_EQUIVALENT`
- `UNRESOLVED`

A comparison category is not an adjudication. Every nontrivial discrepancy must be checked against `Manuscript/main.tex`.

## 11. Comparison outputs

Do not overwrite `LEDGER.md` or `LEDGER_NORMALIZED.md` during the Astra comparison.

Write comparison results separately, preferably:

    Matroid/ASTRA_COMPARISON.md
    Matroid/ASTRA_MAPPING.csv

`ASTRA_COMPARISON.md` should summarize methodology, counts, major discrepancy families, and human-review items.

`ASTRA_MAPPING.csv` should provide a row-level crosswalk between normalized IDs and Astra node IDs, including comparison category and manuscript evidence.

If the comparison reveals a likely omission or error in the normalized ledger, record a proposed correction in the report. Do not silently edit the frozen ledger.

After human adjudication, a later task may create a new version of the working ledger.

## 12. Reproducibility

Every dependency claim should be recoverable from the frozen manuscript.

The desired chain is:

    frozen manuscript
        ↓
    exact TeX label / proof location
        ↓
    blind ledger
        ↓
    normalized ledger
        ↓
    external-audit comparison
        ↓
    human adjudication
        ↓
    Lean declaration
        ↓
    kernel-checked proof

Preserve uncertainty and provenance at each stage.

## 13. Lean workflow and trust boundary

Do not begin proofs merely because a fact has been identified.

The intended progression is:

    IDENTIFIED
        ↓
    mathematical statement fixed
        ↓
    Lean statement elaborates
        ↓
    formal-library support investigated
        ↓
    bridge or proof supplied
        ↓
    COMPLETE

Do not introduce `axiom`, `sorry`, or `admit` unless explicitly requested for a temporary conditional interface.

Do not change the public API merely to make a proof easier without documenting the discrepancy.

Before declaring Lean implementation work complete, run:

    lake build

Computational evidence is not itself proof. If finite certificates are used later, distinguish certificate data, verified checker, checker soundness, and final mathematical theorem.

## 14. Working style

Favor small, auditable changes.

Do not perform large architectural rewrites unless requested.

Do not modify unrelated files.

Do not silently broaden the scope of a task.

If manuscript evidence is insufficient, record uncertainty rather than guessing.

The purpose of this pilot is not merely to obtain Lean code. It is to construct a reproducible process connecting manuscript mathematics, dependency discovery, independent audit comparison, formal-library reconciliation, and machine-checked proof.