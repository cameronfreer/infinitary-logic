/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMTemplateRealization
import InfinitaryLogic.Conditional.MorleyHanfTransfer

/-!
# The Conditional-facing Ω-residual bridge

The one-theorem file connecting the named local-EM seed residual `MorleySeedOmegaExtraction`
(`Methods/LocalEMTemplateRealization.lean`) to the honest Morley–Hanf residual
`MorleySeedTailTemplateRealizable` (`Conditional/MorleyHanfTransfer.lean`):

* `morleySeedTailTemplateRealizable_of_localEMOmega` — `ΓlocalColim`-restricted witness
  homogeneity of the seed extraction implies seed-template realizability, **modulo the bridge's
  extra `[Countable (Σ n, L'.Functions n)]`** (`MorleySeedTailTemplateRealizable` itself assumes
  only countably many relation symbols; removing the extra assumption is the planned
  generated-sublanguage cleanup chunk). Both sides carry the full source facts — `φ` holds in
  `M`, `|M| ≥ ℶ_{ω₁}`, pairwise distinctness — and the realizing model is the
  countable-language EM quotient; the broad `TailTemplateRealizable` over arbitrary sequences is
  false-shaped (see its docstring) and is deliberately NOT the target here.

This file is deliberately isolated, like `LocalEMExtraction.lean`, because it imports
`Conditional/MorleyHanfTransfer.lean`; the template-realization bridge itself
(`LocalEMTemplateRealization.lean`) stays Conditional-free (guarded by
`scripts/check_local_boundary.sh`). With this bridge in place the project's final frontier for
the Morley–Hanf residual is exactly `MorleySeedOmegaHomogeneousExtraction` (which implies
`MorleySeedOmegaExtraction`): seed-specific, source-aware `ΓlocalColim`-restricted witness
homogeneity.
-/

namespace FirstOrder.Language

/-- **The seed Ω-residual discharges the Morley–Hanf residual**: `ΓlocalColim`-restricted
witness homogeneity of the seed extraction (`MorleySeedOmegaExtraction`) implies
`MorleySeedTailTemplateRealizable` — modulo this bridge's extra function-symbol countability.
The size premise supplies `Nonempty M` here (the Skolem stages interpret by Hilbert choice) and
is passed through to the extraction hypothesis, which is free to consume it combinatorially;
the rest is the per-seed acceptance `tailTemplateRealizable_of_localEM`. -/
theorem morleySeedTailTemplateRealizable_of_localEMOmega {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ l, L'.Relations l)]
    (h : MorleySeedOmegaExtraction L') : MorleySeedTailTemplateRealizable (L' := L') := by
  intro φ M instM a J instJ hSize hφreal hPair hTail
  haveI : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  haveI : Nonempty M := ⟨(Infinite.natEmbedding M) 0⟩
  exact tailTemplateRealizable_of_localEM (morleySeed φ) M a J hTail
    (h φ M a J hSize hφreal hPair hTail)

end FirstOrder.Language
