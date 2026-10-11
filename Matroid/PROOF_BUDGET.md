# Cumulative depth-5 external-theorem proof budget

Checkpoint: 2026-10-11. Verified elapsed time and per-theorem token counts were unavailable, so both are `UNKNOWN`; no elapsed or token total is inferred. Counts below are substantive edit–check cycles observed in this pass. Earlier N053/N125 reconnaissance is retained in `FORMALIZATION_LOG.md`; its time and cycle counts were not recorded, so cumulative counts cannot be reconstructed. No theorem has been admitted.

| ID | Source / first recorded attempt | Verified cumulative time | Observed tokens | Attempts / cycles observed this pass | Proved intermediates | Precise remaining goal | Disposition |
| --- | --- | --- | --- | --- | --- | --- | --- |
| N028 | Standard minor algebra; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | `Matroid.contract_contract` bridge | None | KERNEL_PROVED |
| N029 | Standard minor algebra; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Disjoint `contract_delete_comm` bridge | None | KERNEL_PROVED |
| N041 | Standard restriction rank/closure; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 2 | Exact extension closure and rank theorem | None | KERNEL_PROVED |
| N045 | Standard vector-matroid closure; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Indexed span test for arbitrary represented finite matroid | None | KERNEL_PROVED |
| N053 | Manuscript regularity remark; first attempt date UNKNOWN (earlier depth-3 reconnaissance) | UNKNOWN | UNKNOWN | Prior attempt at least 1, this pass reconnaissance / 0 cycles | Integer TU minor nonvanishing bridge, including characteristic 2 | Prove indexed column independence iff some square minor is nonzero for an arbitrary rectangular matrix; transfer that criterion to every field, including the integer lift of a real TU matrix. | UNRESOLVED; no admission |
| N125 | Choe–Oxley–Sokal–Wagner, Theorem 8.1/Corollary 8.2; first attempt date UNKNOWN (earlier depth-3 reconnaissance) | UNKNOWN | UNKNOWN | Prior attempt at least 1, this pass reconnaissance / 0 cycles | TU nonzero minor square equals 1 | Formalize rectangular weighted Cauchy–Binet with finite subset indexing, then identify exactly the full-rank subsets with matroid bases and filter the TU squared minors. | UNRESOLVED; no admission |
| N131 | Standard rank-one uniform matroid; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Nonloop target and closure for every nonempty other set | None | KERNEL_PROVED |
| N134 | Standard matroid duality; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Both dual deletion/contraction identities | None | KERNEL_PROVED |
| N262 | Standard linear row-space compression; 2026-10-11 | UNKNOWN | UNKNOWN | Reconnaissance / 0 cycles | Existing represented-rank theorem N044 | State an exact restricted matrix compression that simultaneously preserves the indexed column matroid and both directions of every target reconstruction equation; a rank-only row-deletion lemma is insufficient. | UNRESOLVED; no admission |
| N264 | Standard graphic closure/path criterion; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 2 | Labeled cut/reachability characterization, including loops | None | KERNEL_PROVED |

The unresolved external results remain within the policy budget. Their missing proof routes were identified without introducing an admission. A future pass must continue these records rather than resetting them.
