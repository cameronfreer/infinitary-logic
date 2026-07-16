# Intentionally retained zero-reference declarations (registry)

Maintained registry of declarations with **no in-tree textual reference** that are kept on
purpose. Future unused-declaration audits should diff against this list and re-flag only *new*
entries. Last full scan: 2026-07-16 (post-v1.4.0, after the depth/constTerm dedup extraction;
2,494 declarations scanned across the default/Everything/WIP roots, 132 zero-reference
candidates, 6 deleted, the rest classified below).

**Scan caveats** (why "zero textual references" ≠ "dead"):
- `@[simp]`/`@[blueprint]` declarations are consumed without being named (`simp` closure,
  blueprint web). Never delete a simp lemma on a zero-reference count alone.
- The CI guards reference names reflectively (`scripts/check_truth_lemma_cone.lean` — including
  its *forbidden* list — `check_morley_hanf_deps.lean`, `check_headline_axioms.sh`), as do
  `blueprint/lean_decls`, `README.md`, and `docs/*.md`.
- Reachability from a headline theorem is not the same as mathematical uselessness
  (maintainer ruling, 2026-07-14).

## R — consumed only reflectively or by guards

- `henkinComplete_univ_of_maximal` (HenkinCompat) — named in the truth-lemma cone guard's
  **forbidden** list; the compatibility adapter's endpoint (see the file's status header).
- `truth_pos` / `truth_neg` (QuotientTruthLemma) — required members of the truth-lemma cone
  guard's *required* list; the split polarities of `truth_both`.

## B — public API awaiting consumers (deliberate library endpoints)

Craig relationalization layer (Units 1–7 surface; consumers arrive with #10/#12-era work):
`reconstruct_relMap_base`, `reconstruct_funMap_graph_iff`, `reconstruct_graphExpansion_relMap`,
`relationalizeFormula_falsum`, `relationalizeFormula_rel` (simp rewrite points, required by the
frozen Unit-4 design), `BoundedFormulaω.functionsIn_and`, `BoundedFormulaω.functionsIn_einf`
(symmetric companions of the consumed `relationsIn_*` calculus), `seed_subset_genU`,
`insepAt_mono_support`, `InsepFamilyMem.support_finite` (legitimate endpoints per maintainer
ruling), `wc_relMap_inl`, `BoundedFormulaω.sentenceJConsts_abstractConst_subset`.

Core/Scott/Karp/Linf/Lomega1omega API:
`mem_def`, `generated_le`, `mem_generatedSentence`, `mem_generatedTheory`,
`generatedSentence_countable`, `generatedTheory_countable`, `toLinf_isCountable`,
`castLE_eq_cast`, `mapLanguage_ex`, `mapLanguage_relabel`, `mapLanguage_subst`,
`realize_emptyiInf`, `realize_emptyiSup`, `realize_forallLastVarInf`, `realize_toSentenceInf`,
`qrank_mapFreeVars`, `exists_isKappa`, `isCountable_iff_isKappa_aleph1`,
`BFEquiv.refl_zero`, `BFEquiv.toOrdinalLift`, `BFEquiv.ofOrdinalLift`,
`BFStrategyOmegaT_implies_BFEquiv_omega`, `BFEquiv_iff_agree_formulas_omega`,
`scottSentence_self`, `scottSentence_of_equiv`, `scottSentence_of_equiv_of`,
`scottSentence_realizes_implies_equiv`, `stabilizationOrdinal_spec`,
`countable_refinement_steps`, `karp_theorem_forward`, `PotentialIso_implies_LinfEquiv`,
`countable_BFEquiv_all_implies_iso`.

ModelTheory/Descriptive endpoints:
`downward_LS_theory` (README-referenced), `downward_LS_theory_with_naming`, `theoryModel_iff`,
`lt_hanfNumber_iff_not_isHanfBound`, `not_hasArbLargeModels_countableSpectrumSentence`,
`not_isLomega1omegaHanfBound_of_le_aleph0`, `idxOf_idxVal`, `idxVal_injective`,
`infinitaryType_mem_realizedInfinitaryTypes`, `exists_realize_isolatingFormula`,
`exists_countable_bfEquiv_of_lomega1omegaSmall`, `realize_inf_iff_of_companion`,
`consistent_theory_has_model_uncountable_language`, `relNbhd_mono`, `isOpen_wordCylinder`,
`length_wordOf`, `isClopen_relHoldsOn`, `ModelSpace`, and the issue-#27/#28 milestone API
(`measurable_id_actionInvariant`, `measurable_id_isoInvariant`,
`MeasurableSpace.measurableSet_smulInvariant`, `actionInvariant_empty`) — terminal leaf API by
design.

## H — historical / research endpoints (kept as the record of the route)

Morley–Hanf conditional bridges (documented in README as retained history):
`morley_hanf_of_pureColoring_and_compact`, `morley_hanf_of_tail_compact`,
`morleyHanfExtractionTail_of_morleyHanfExtraction`, `hasArbLargeModels_of_pureColoring`.

Marker/EM/Skolem/local-tower stage API (off-path since the definitive schema route; CI-checked;
several are interface fields exercised through instances rather than by name):
`MarkerStage` cluster (`MarkerConsistentFamily.mem_not_not`, `.mem_or_not_mem`,
`MarkerHenkinConsistent.ex_witness`, `.imp_choice`, `.neg_imp_left`, `.neg_imp_right`,
`Theoryω.model_reduct_of_model_image`, `exists_maximal_markerConsistent`,
`termValueWith_henkinConst`, `termValueWith_var`), `realize_henkinConst`,
`exists_witness_skolemTerm`, `exists_ΓEnum`, `skWitnessStep_subset_Γstar`, `subset_Γstar`,
`skolemStage_zero`, `skolemStage_succ`, `localStage_zero`, `localStage_succ`, `Llocal_zero`,
`Llocal_succ`, `localSkolem_functions_countable`, `LocalStage.ofSeq_Lang`, `locDeForm_iInf`,
`locDeForm_iSup`, `le_depth_position` (EMTermModel), the `Methods/EM/` family
(`IsLomega1omegaIndiscernible.*`, `morleySeed_zero/_one`, `templateTheoryOn_mono`,
`realizesTemplate_reindex`, `template_eq_templateOfSeq`).

Henkin/maximal-consistency alternates (the one-sided predecessor is **kept by maintainer
ruling** — correct, conceptually useful, WIP-quarantined, documents why Craig required paired
conditions): `ConsistencyPropertyEq.MaximalConsistent.ex_mem`, `.neg_all_mem`,
`termModel_models_maximal`, plus the whole of `HenkinCompat.lean`/`InseparableConsistency.lean`
per their status headers; `FairEnumeration`'s `finite_stage` cluster.

Combinatorics/Barwise: `finiteArityErdosRadoBounded_beth_one`, `finiteERBound_mono`,
`finiteERBound_one`, `orderEmbedding_fin_one_eq'`, `barwise_compactness_of_data`,
`admissibleFragmentOfUniv_formulas`, `eq_continuum_classes_of_perfect_transversal`.

Scott stabilization research record (Scott/Sentence.lean, including two `private` lemmas kept
as the documented record of approaches: `BFEquiv_all_countable_ordinals_implies_all`,
`per_tuple_stabilization_from_extensions`): `StabilizesCompletely.toStrongStabilizesForTuples`,
`StrongStabilizesForTuples.toStabilizesForTuples`, `StabilizesForTuples.downward_propagation`,
`refinement_descent`.

## D — deleted (2026-07-16, this audit)

Genuinely dead plumbing with no reusable statement: `mem_consistentSets_iff` (private
membership-unfolding), `qrank_atomicFormulaInf` + `realize_atomicFormulaInf` (private Karp
leftovers), `term_roundtrip_zero` (private Operations leftover),
`realize_openBounds_subst_name` (private; content available through the public
`Construction`/`Depth` lemmas), `sentenceJConsts_eq_empty_of_insepAt_empty_separator` (public
but trivially `s ⊆ ∅ → s = ∅`, misnamed — never mentioned `InsepAt` — and superseded by
`RootGate`'s inline derivation).
