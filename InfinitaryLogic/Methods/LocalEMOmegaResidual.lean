/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMTemplateRealization
import InfinitaryLogic.Conditional.MorleyHanfTransfer

/-!
# The Conditional-facing Ω-residual bridge

The one-theorem file connecting the named local-EM residual `LocalEMOmegaExtraction`
(`Methods/LocalEMTemplateRealization.lean`) to the honest Morley–Hanf residual
`TailTemplateRealizable` (`Conditional/MorleyHanfTransfer.lean`):

* `tailTemplateRealizable_of_localEMOmega` — `ΓlocalColim`-restricted witness homogeneity of the
  extraction implies tail-template realizability, **modulo the bridge's extra
  `[Countable (Σ n, L'.Functions n)]`** (`TailTemplateRealizable` itself assumes only countably
  many relation symbols; removing the extra assumption is the planned generated-sublanguage
  cleanup chunk). The `ℶ_{ω₁}` premise of `TailTemplateRealizable` is consumed only to make `M`
  nonempty — the realizing model is the countable-language EM quotient, not a large
  substructure.

This file is deliberately isolated, like `LocalEMExtraction.lean`, because it imports
`Conditional/MorleyHanfTransfer.lean`; the template-realization bridge itself
(`LocalEMTemplateRealization.lean`) stays Conditional-free (guarded by
`scripts/check_local_boundary.sh`). With this bridge in place the project's final frontier for
the Morley–Hanf residual is exactly `LocalEMOmegaExtraction`: not "prove global `OmegaComplete`",
but "prove `ΓlocalColim`-restricted witness homogeneity".
-/

namespace FirstOrder.Language

/-- **The Ω-residual discharges the Morley–Hanf residual**: `ΓlocalColim`-restricted witness
homogeneity of the subsequence extraction (`LocalEMOmegaExtraction`) implies
`TailTemplateRealizable` — modulo this bridge's extra function-symbol countability. The size
premise is consumed only for `Nonempty M` (the Skolem stages interpret by Hilbert choice); the
rest is `tailTemplateRealizable_of_localEMExtraction`. -/
theorem tailTemplateRealizable_of_localEMOmega {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ l, L'.Relations l)]
    (h : LocalEMOmegaExtraction L') : TailTemplateRealizable (L' := L') := by
  intro s M instM a J instJ hSize hTail
  haveI : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  haveI : Nonempty M := ⟨(Infinite.natEmbedding M) 0⟩
  exact tailTemplateRealizable_of_localEMExtraction h s M a J hTail

end FirstOrder.Language
