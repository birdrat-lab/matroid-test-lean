# Normalized ledger versus raw dependency graph

## Method

I compared the frozen [`LEDGER_NORMALIZED.md`](LEDGER_NORMALIZED.md) with the independently produced `Audit/dependency_graph_raw.csv` in both directions, then audited the matches against its companion `Audit/dependency_graph_raw_edges.csv`. The raw graph is manuscript-wide; a raw node was matched only when its hypotheses, conclusion, and proof role overlapped a normalized requirement. Exact TeX labels established direct candidates, while raw descriptions and dependency arrows guided semantic matches to unlabeled requirements. The frozen `Manuscript/main.tex` was used to adjudicate discrepancies. Neither source analysis was edited.

The edge table has 635 arrows (`E0001`–`E0635`): 252 `DEFINITIONAL`, 161 `EXTERNAL_IMPORT`, 131 `SEMANTIC_USES`, 73 `PROOF_USES`, 14 `CERTIFICATE_USES`, 3 `SPECIALIZES`, and 1 `COROLLARY_OF`. Every endpoint resolves to one of the 266 raw nodes. Source and target metadata, degrees, neighbor IDs, and dependency types agree with the node table for every arrow; there are no duplicate typed arrows or self-loops. The edge-file SHA-256 is `8634d3f329121cac64f938bd2f132569dcec7a6b2389121883308c196c77dea8`.

The edge audit supported the existing classifications and changed no category counts. An arrow records the raw analysis's claimed relation; manuscript text, rather than graph reachability alone, determines whether it is a mathematical dependency.

## Summary

The mapping has 456 relationship rows. Both passes cover all 265 normalized entries and all 266 raw nodes. Of the raw nodes, 142 were judged matroid-relevant or directly comparable to a normalized context row; 124 were classified as non-matroid raw nodes. Direct `At`-label matching located 148 normalized rows across 92 raw nodes. Semantic matching accounts for the remaining matches. These counts are coverage descriptions, not accuracy scores; there is no independent gold standard.

| Classification | Mapping rows | Distinct normalized IDs | Distinct raw IDs |
| --- | ---: | ---: | ---: |
| `AGREEMENT` | 56 | 56 | 56 |
| `GRANULARITY_MISMATCH` | 257 | 199 | 87 |
| `NORMALIZED_ONLY_CANDIDATE` | 14 | 14 | 0 |
| `RAW_ONLY_CANDIDATE` | 3 | 0 | 3 |
| `SCOPE_MISMATCH` | 1 | 1 | 1 |
| `FORMULATION_MISMATCH` | 1 | 1 | 1 |
| `DUPLICATE_OR_EQUIVALENT` | 0 | 0 | 0 |
| `UNRESOLVED` | 0 | 0 | 0 |
| `NON_MATROID_RAW_NODE` | 124 | 0 | 124 |

A normalized entry may have several relationships, and two of the raw-only candidate nodes also have links to related normalized rows. Thus category totals are relationship counts and should not be added to obtain an entry count. In all, 251 normalized rows have at least one raw link; 14 have none. The row-level evidence and proposed action for each relationship are in [`NORMALIZED_VS_RAW_MAPPING.csv`](NORMALIZED_VS_RAW_MAPPING.csv).

## Major discrepancy families

### Basic matroids, represented matroids, and minors

The raw `ext:matroid_basic` node bundles closure, exchange, rank, bases, duality, and hyperplanes. The normalized ledger splits these into separate obligations, for example N003–N005, N008–N014, and N132–N135. The raw `ext:represented_closure` similarly covers the distinct represented-rank, represented-closure, and represented-circuit requirements N044–N046. The prose after `def:vector-matroid` states each characterization. These are mostly granularity differences.

N027–N029 have no raw node stating deletion composition, contraction composition, or their disjoint commutation. `def:matroid-minors` defines the operations, and proofs such as `prop:r10-proper-minors` use successive minors; the raw graph does not record the algebra separately. N041 is another unlabeled step: the proof of `prop:target-extension-criterion` uses equality of the ranks of an availability set and its non-target closure in a single-element extension. Its absence from the raw graph is a plausible raw coverage gap. N058, Higgs's quotient construction, is contextual material before `thm:regular-quotient-form`; its raw absence does not create a Matroid API omission.

### Weighted regular matroids and sums

`ext:tu_standard_form`, `ext:tutte_tu`, `ext:sum_bases`, and `ext:three_sum_binary` are broad raw obligations. Their normalized counterparts separate TU normal forms, regularity, basis correspondences, cycle/cocircuit gluing, and rank/size formulas. The manuscript's `lem:seymour-three-sum-five` distinguishes compatible binary triangle classes from the resulting bilinear weighted-basis expression; N159–N160 preserve that distinction.

Two raw interface nodes contain additional atomic formulas. `interface:triangle_signature` specifies the weighted class sums `Φ_L` and the tuple `(a,p₁,p₂,p₃,c)` defined immediately before `lem:seymour-three-sum-five`. `interface:k4_signature` specifies the five weighted `M(K₄)` class sums displayed in the proof of `thm:seymour-three-sum`. N158–N160 and N165 cover the surrounding class and replacement theorems, but neither formula is an explicit atomic normalized entry. These are the two clearest possible normalized-ledger additions.

The arrows confirm that these signatures are used as distinct interfaces: `E0435` and `E0628` connect the triangle signature to `lem:seymour-three-sum-five` and `thm:seymour-three-sum`; `E0023` connects it to the K4 signature; and `E0444` connects the K4 signature to the theorem. The manuscript supplies exact equation labels `eq:seymour-three-sum-phi`, `eq:seymour-three-sum-five`, and `eq:k4-five-sums`.

N151 records the proper-glue connectedness used in the proof of `prop:recursive-r10-closure`. The proof says connectedness is preserved, ensuring nonloop and noncoloop summing elements, without stating a general theorem or all hypotheses. The raw graph has `ext:r10_connected` for the base R10 and a broad `ext:sum_bases` node, but no separate preservation obligation. The normalized row's `STATEMENT_DESIGN` status remains appropriate.

The new arrows `E0514` (`ext:sum_bases`) and `E0515` (`ext:r10_connected`) both enter `prop:recursive-r10-closure`, confirming that the raw proof context includes the sum machinery and base connectedness. Neither edge states preservation of connectedness under the recursive gluing, so N151 remains a normalized-only candidate.

### R10 geometry and recursive closure

The raw certificate nodes cover the 162 bases, automorphism order, subset orbits, four-state orbits, pointed boundary families, and natural-program incidence data at coarser granularity. The normalized ledger separates the mathematical claims from their reported certificate data. The raw graph has no explicit counterpart for N169 (the two R10 circuit counts) or N171 (absence of triads), both asserted in `app:r10-atlas-geometry`. N170's no-triangle clause does appear through the proof of `prop:r10-no-three-sum`. The R10 determinant and cofactor entries N193–N194 are specializations of raw `ext:determinant_basis`, with the exact specialization in `app:r10-atlas-response`.

The raw `prop:recursive-r10-sensitivity` states `s₀(F_h)=s₁(F_h)=5^h`. Normalized N239 records the base five-sensitive witnesses, and N222 records recursive target-closure composition, but no row states the recursive sensitivity conclusion as a pointed-matroid closure invariant. Whether to extract that conclusion into the Matroid specification, rather than leave it as Boolean-function context, needs human scope review. The proof at `prop:recursive-r10-sensitivity` gives the exact induction.

Its incoming arrows `E0519`–`E0521` are sensitivity, finite induction, and base-certificate dependencies. The theorem's outgoing proof arrows `E0522` and `E0536` lead to query and program cost claims. This makes the raw theorem's application role explicit while leaving its possible matroid-side reformulation a scope question.

### Query, program, and quotient boundaries

N098 is marked `CORE_MATROID`, although its requirement composes agreement projections of query partitions. `prop:mobius-source-potential` uses the flat join together with partition semantics. N097 already records the pure flat-lattice join. The manuscript supports re-scoping N098 as `APPLICATION_CONTEXT`, or splitting off any remaining pure flat fact; the frozen ledger was not changed.

The incoming arrows `E0348`–`E0351` include agreement fibers and partition pinching as well as the agreement-flat fact. They support the scope judgment because the projection identity requires the query partition, not merely the lattice operation.

N206 and raw `interface:r10_alternative_program` describe the same parallel-target construction differently. The raw node records the regular representation and graphic 2-sum construction, while N206 requires the retained target's closure condition to be the union of the two pointed conditions. The unlabeled paragraph before `prop:r10-regular-route-b` states this union rule. This is a likely raw proof-dependency omission, not an assertion that the two constructions contradict each other.

`E0051` imports the broad sum facts into that interface, and `E0507` carries the interface into `prop:r10-regular-route-b`; neither edge or endpoint description states the closure-union rule. The edge table therefore does not resolve the formulation mismatch.

N250 has no matching raw node for the quotient program's target modular cut. The paragraph after `prop:quotient-complementary-rank` explicitly says positive availability flats lie in that cut and negative flats lie outside it. The raw graph records quotient correctness and the general modular-cut theorem separately, but no node connects this specific consequence. N259 similarly records the source matroid `U_{n,n+1}` for OR in the prose at `sec:grover-example`; raw `prop:grover-source-value` records the adversary value, not that matroid identification.

For N250, `E0577`–`E0582` connect quotient correctness to the relation space, quotient construction, computational factorization, linear quotient, represented closure, and negative functional. No direct modular-cut dependency enters that node; the separate modular-cut chain runs through `E0229`–`E0231` and `E0314`. This confirms the structural gap but does not itself prove the raw analysis mathematically incomplete.

## Systematic methodological differences

- The raw graph preserves manuscript-wide theorem, implementation-interface, and certificate nodes. The normalized ledger splits matroid obligations into near-atomic rows and retains some application claims as context. A same-label match therefore often has a granularity mismatch without a mathematical disagreement.
- Raw external nodes often bundle a field of standard mathematics, such as `ext:matroid_basic` or `ext:sum_bases`. The normalized ledger records the particular closure law, minor law, or sum property needed by a manuscript proof.
- The normalized extraction more often records unlabeled proof steps, including N041, N151, N181, N225, N250, and N256. Conversely, the raw graph gives explicit interfaces for the triangle and K4 signatures that the normalized ledger embeds in larger claims.
- The 124 `NON_MATROID_RAW_NODE` rows include adversary, quantum, general optimization, ordinary linear-algebra, and certificate/implementation material. Their absence from the reusable Matroid specification is not by itself a discrepancy. The mapping retains them so reverse-pass coverage is auditable.

## Proposed corrections

### Clear normalized-ledger correction

- **N098 / `prop:mobius-source-potential`:** re-scope the agreement-projection composition from `CORE_MATROID` to `APPLICATION_CONTEXT`. Its operation depends on query partition projections; N097 already isolates the pure flat join. Do this only in a later ledger version.

### Likely normalized-ledger additions

- **`interface:triangle_signature` / N158–N160 / `lem:seymour-three-sum-five`:** add the exact weighted five-class `Φ_L` construction as an atomic matroid requirement, tracing it to blind M110–M111.
- **`interface:k4_signature` / N165 / `thm:seymour-three-sum`:** add the displayed five-term weighted K4 signature as an atomic proof obligation, tracing it to blind M114.

### Raw-graph coverage proposals, without normalized-ledger edits

- Consider explicit raw dependencies for N027–N029 (`def:matroid-minors`, `prop:r10-proper-minors`), N041 (`prop:target-extension-criterion`), N169 and N171 (`app:r10-atlas-geometry`), N181 (`prop:r10-no-three-sum`), N225 (`prop:recursive-r10-closure`), N250 (`prop:quotient-complementary-rank`), N256 (`def:matroid-cycle`), and N259 (`sec:grover-example`). The mapping preserves each as a normalized-only candidate rather than assuming the raw graph is wrong.
- Consider recording the closure-union step N206 separately from raw `interface:r10_alternative_program`, using the paragraph before `prop:r10-regular-route-b`.

### Optional granularity refinements and human review

- **`prop:recursive-r10-sensitivity` / N222, N239:** decide whether the `5^h` conclusion should be an atomic matroid-side target-closure fact. The raw theorem is currently a raw-only candidate.
- **N151 / `prop:recursive-r10-closure`:** fix the connectedness and proper-glue hypotheses before treating the raw absence as an adjudicated omission.
- **N058 / `thm:regular-quotient-form`:** retain the Higgs citation as context unless a later proof actually imports it; the manuscript gives a direct TU construction.
- **N129 / `sec:grover-example`:** decide whether the generic uniform-matroid object needs a standalone raw node. Its two pointed specializations are represented in related raw results.

No `DUPLICATE_OR_EQUIVALENT` or `UNRESOLVED` relationship was forced solely to improve counts. The specific statement-design and scope questions above remain open for human adjudication. The frozen normalized ledger and raw CSV were left unchanged.
