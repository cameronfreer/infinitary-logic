import InfinitaryLogic.Conditional.MorleyHanfTransfer
import InfinitaryLogic.Conditional.MorleyHanfSchemaDischarge
import InfinitaryLogic.Conditional.SilverBurgess
import InfinitaryLogic.Conditional.GandyHarrington
import InfinitaryLogic.Conditional.SilverAntichain
import InfinitaryLogic.Conditional.MorleyPerfect
import InfinitaryLogic.Conditional.BFScatteredSilver
import InfinitaryLogic.Conditional.MinimallyUncountableHeadline
import InfinitaryLogic.Conditional.SentenceSpectrum
import InfinitaryLogic.Conditional.FragmentSpectrumThin
import InfinitaryLogic.Conditional.SilverCategoryRoute

/-!
# Conditional: historically hypothesis-relative results, now discharged

This bundle historically isolated results relying on external hypotheses or
sorries. Both chains here are now **proved**: the Silver chain is sorry-free,
and the Morley–Hanf theorem is unconditional (`morley_hanf` in
`MorleyHanfSchemaDischarge.lean`). The directory name is retained for
stability; its hypothesis-relative theorems remain as transparent
intermediates and historical statement shapes.

## Contents

- `MorleyHanfTransfer.lean`: the Morley–Hanf reduction chain — the historical
  bundled form (`MorleyHanfTransfer` hypothesis, `morley_hanf_of_transfer`),
  the split bridges through `MorleyHanfExtraction` (a residual since shown
  false in ZFC) and its proved tail weakening `morleyHanfExtractionTail_holds`,
  and the realizability-relative endpoints over
  `MorleySeedTailTemplateRealizable`.
- `MorleyHanfSchemaDischarge.lean`: `MorleySeedTailTemplateRealizable` is
  **PROVED** via the schema-completion construction, and the definitive
  endpoint **`morley_hanf`** — `ℶ_ω₁` is a Hanf bound for every `L_ω₁ω`
  sentence, over an arbitrary language, with no hypotheses.
- `SilverBurgess.lean`: Silver-Burgess splitting lemmas and `silver_core_closed`
  (sorry-free).
- `SilverCategoryRoute.lean`: Miller's classical category route, now **complete**:
  the hypothesis Props are all discharged (`mycielskiCantorHypothesis_holds`,
  `gSGraphHomHypothesis_holds` via the `G₀`-dichotomy fusion in
  `Descriptive/G0Fusion.lean`), so `gandy_harrington_of_gSGraphHom` is fed a proved
  input.
- `GandyHarrington.lean`: Silver-for-Borel, **PROVED** (2026-06-10, sorry-free):
  `gandy_harrington_for_relation`, `silver_core_polish`, `silverBurgessDichotomy`
  all report axioms exactly `[propext, Classical.choice, Quot.sound]`.
- `SilverAntichain.lean`: `silver_core_polish` repackaged for a Borel *subset* of a
  Polish space, returning a Cantor antichain in the **ambient** space rather than
  in the refinement the subtype needed to be Polish.
- `SentenceSpectrum.lean`: **`thin_iff_countable_sentence_spectra`** — a Borel class is thin for
  isomorphism iff every countable list of sentences has countably many realized truth
  sequences; Silver on the kernel of the truth-sequence map one way, invariant analytic
  separation and López–Escobar the other.  Here because it consumes the Silver adapter.
- `FragmentSpectrumThin.lean`: **`thin_iff_countable_fragment_spectra`** — a Borel class is thin
  for isomorphism iff every countable fragment realizes countably many types at every finite
  arity; Silver on the Borel relation "same realized types" (Marker's Corollary 3.3.3 route),
  arity zero through the sentence characterization the other way.
- `MorleyPerfect.lean`: the tiered **`morley_counting_or_perfect`** — Morley counting
  with a perfect set of pairwise non-isomorphic models in place of the bare cardinal
  equation, at the `ℕ` and `Fin n` tiers, with the cardinal form as a corollary.
- `BFScatteredSilver.lean`: **`Sentenceω.bfScattered_of_isThinOnNatModels`** — a thin sentence
  has back-and-forth scattered models (Silver on each level's Borel relation `bfEquivSetoid`),
  with the equivalence `Sentenceω.bfScattered_iff_isThinOnNatModels` and the corollary
  `Sentenceω.bfScattered_modelsOf_of_lt_continuum`; rank-free proof cones (checked), with the
  Scott modules present only in the import closure, and it does not import
  `Descriptive/ScatteredCounting.lean`.  Its per-level Silver step is the one inlined in
  `morley_counting_coded_or_perfect` (`MorleyPerfect.lean`).
- `MinimallyUncountableHeadline.lean`: **`Sentenceω.minimallyUncountable_iff`** — the models of
  a sentence are minimally uncountable iff they are back-and-forth scattered and the sentence is
  minimally unbounded for any isolating rank (the analogue of [Mon, Def XII.4]), with the
  concentrated form `Sentenceω.minimallyUncountable_iff_concentrated`.  Here because the
  scatteredness step consumes the Silver chain (through `BFScatteredSilver.lean`); its proof
  cones also reach López–Escobar (through `MinimallyUncountableOn.isThinOn`).

There are no sorries anywhere in the project; the historical sorry-bearing
`Combinatorics/ErdosRado.lean` exploration is preserved on the
`archive/legacy-erdos-rado` branch, not in the tree.
-/
