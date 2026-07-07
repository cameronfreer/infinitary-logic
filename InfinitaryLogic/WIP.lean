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
  model theorem `LocalEMContext.templateTheoryOn_seed_model`, and the per-`s` acceptance lemma
  `tailTemplateRealizable_of_localEM` (hypothesis-relative; its ∀-`s` closure is false-shaped —
  a `{Pᵢ} ∪ {⋀ᵢ Pᵢ}` seed against a height model defeats any extraction — so the named
  residuals are seed-specific and source-aware: `MorleySeedOmegaExtraction` and its cleanest
  form `MorleySeedOmegaHomogeneousExtraction`, both over `morleySeed φ = {φ, x₀ ≠ x₁}` with the
  `ℶ_{ω₁}`/`φ`-realization/pairwise source facts);
* `Methods/LocalEMOmegaResidual.lean` — the Conditional-facing one-theorem bridge
  `morleySeedTailTemplateRealizable_of_localEMOmega : MorleySeedOmegaExtraction L' →
  MorleySeedTailTemplateRealizable` (modulo the bridge's extra function-symbol countability),
  isolating the `Conditional/MorleyHanfTransfer` import like `LocalEMExtraction`. **Audit
  outcome:** both seed Ω-residuals are REFUTED there (`height_no_seed_omega_homogeneous`,
  `not_morleySeedOmegaHomogeneousExtraction_height`, `not_morleySeedOmegaExtraction_height`) —
  the height pattern hides inside the true seed sentence `∃x, ¬⋀ᵢ Pᵢ(x)`, whose subformula
  closure re-imports the divergent conjunction into `ΓlocalColim`, defeating the uniform
  `iInf`-cutoff on every subsequence. The honest route to `MorleySeedTailTemplateRealizable`
  must go below the `OmegaCompleteForColim` bundle: closer to the classical EM/Skolem-hull
  proof, using the truth of `φ` and Skolem closure; the reshape is the next chunk.

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
