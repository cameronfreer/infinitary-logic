-- The old skolemColim EM term model (kept CI-checked; no longer imported by the local stack)
import InfinitaryLogic.Methods.EMTermModel
-- The local EM extraction bridge (its Conditional/MorleyHanfTransfer import stays isolated here)
import InfinitaryLogic.Methods.LocalEMExtraction
-- The pure local stack: semantic layer onward (LocalEMFamily -> LocalColimit -> LocalTower ->
-- LocalSkolem -> LocalEMSupport, plus the explicit Henkin.Construction realize lemmas)
import InfinitaryLogic.Methods.LocalEMContext
-- The local EM truth lemma layer 1: Skolem-witness transport (imports LocalEMContext)
import InfinitaryLogic.Methods.LocalEMTruth
-- The local EM truth lemma layer 2: readiness + the staged truth lemma (imports LocalEMTruth)
import InfinitaryLogic.Methods.LocalEMTruthLemma
-- The template-realization bridge (imports the EM-side template machinery; Conditional-free)
import InfinitaryLogic.Methods.LocalEMTemplateRealization
-- The Conditional-facing Ω-residual bridge (LocalEMOmegaExtraction → TailTemplateRealizable)
import InfinitaryLogic.Methods.LocalEMOmegaResidual

/-!
# WIP: the work-in-progress frontier bundle

Root of the **non-default** `InfinitaryLogicWIP` build target: the in-progress
Ehrenfeucht–Mostowski / Skolem-hull realizability construction aimed at discharging
the Morley–Hanf residual `TailTemplateRealizable`. The frontier has two disjoint roots —
the old `skolemColim` track (`EMTermModel`) and the pure local stack, whose top is the
extraction bridge (`LocalEMExtraction`, isolating the Conditional import); since
`LocalEMExtraction` now imports `LocalEMContext`, that one root already pulls in the whole
local stack. `LocalEMContext` is imported explicitly too, as a manifest anchor. Together
these imports transitively cover:

* `Methods/Skolem.lean` → `SkolemColimit.lean` → `SkolemClosure.lean` — the full
  (uncountable) Skolem tower `skolemStage`/`skolemColim` and the countable staged
  family `Γ*`;
* `Methods/EMTermModel.lean` — the EM term model over `(skolemColim L)[[J]]` with the
  staged truth lemma `truthLemmaStage`;
* `Methods/LocalEMSupport.lean` → `LocalSkolem.lean` → `LocalTower.lean` → `LocalColimit.lean`
  → `LocalEMFamily.lean` → {`LocalEMExtraction.lean`, `LocalEMContext.lean` → `LocalEMTruth.lean`
  → `LocalEMTruthLemma.lean`}
  — the countable family-restricted re-base (shared generic support, `localSkolem`, the mutually
  recursive `Llocal`/`Γlocal` tower with `skolemNeed`, the countable colimit `localColim` with
  cocone and semantic transport, the countable atom/deForm family `ΓEMlocal` with the canonical
  J-free seeds and the `EMContext`-instantiation membership interface, the extraction bridge
  `exists_ΓEMlocal_tail_indiscernible`, the generic deep-interpretation/realize-bridge semantic
  layer, the `LocalEMEq` quotient carrier + `Λ[[J]]`-`Structure`, the local Skolem-witness
  transport `locSkWitnessTerm`/`locDeepInterp_skWitness`/`locSkWitness_universal`, and the
  truth-lemma endpoints: the `OmegaComplete` mixin, `TLReady`/`TLReadyStage` readiness with the
  `DeFormClosedForColim` mixin + `ΓEMlocal` discharger, and the staged truth lemma
  `LocalEMContext.truthLemmaStage` with its stage-`k` lift corollary `truthLemmaStage_of_mem`);
* `Methods/LocalEMTemplateRealization.lean` — the template-realization bridge (imports the
  EM-side template machinery, stays Conditional-free): `LocalStage.ofSeq`, the
  subsequence-preserving Ramsey extraction `exists_orderEmb_tailIndiscernible_ΓEMlocal` +
  `exists_localEMContext_subseq`, template preservation under subsequence, the parameterized EM
  model theorem `LocalEMContext.templateTheoryOn_seed_model`, and the acceptance theorem
  `tailTemplateRealizable_of_localEM` — the `TailTemplateRealizable` conclusion shape modulo the
  single remaining restricted-completeness extraction hypothesis, named
  `LocalEMOmegaExtraction`;
* `Methods/LocalEMOmegaResidual.lean` — the Conditional-facing one-theorem bridge
  `tailTemplateRealizable_of_localEMOmega : LocalEMOmegaExtraction L' → TailTemplateRealizable`
  (modulo the bridge's extra function-symbol countability), isolating the
  `Conditional/MorleyHanfTransfer` import like `LocalEMExtraction`. The project's final frontier
  for the Morley–Hanf residual is now exactly `LocalEMOmegaExtraction`:
  `ΓlocalColim`-restricted witness homogeneity of the subsequence extraction, not global
  `OmegaComplete`.

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
