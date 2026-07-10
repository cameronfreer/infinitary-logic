/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.MorleyHanfTransfer
import InfinitaryLogic.Methods.SchemaLocalEMSource

/-!
# The Morley–Hanf seed residual, discharged

The honest residual `MorleySeedTailTemplateRealizable` — the sole non-formal input of the
realizability-only Morley–Hanf endpoint `morley_hanf_of_tail_realizable` — is PROVED for
countable-symbol languages by the schema route (`morleySeed_tailTemplate_model_of_schemaSource`):
the ω-stage Marker/Henkin completion of the schema sentence universe, its quotient term model
with the restricted truth lemma, the fully indiscernible sequence `schemaSeq` with pinned
`iSup`/negative-`iInf` witnesses, and the cross-source acceptance through the Skolem-universality
mixin. In fact the schema route consumes strictly LESS than the residual offers: the input
sequence's tail indiscernibility is not used (seed template values are absolute).

The corollary `morley_hanf_countable_symbols` is therefore an UNCONDITIONAL Morley–Hanf bound for
countable-symbol languages: `ℶ_{ω₁}` is a Hanf bound for every `L_{ω₁ω}` sentence. Removing the
symbol-countability hypotheses via the generated-sublanguage reduction is the remaining wrapper.
-/

namespace FirstOrder.Language

open Cardinal

/-- **The honest Morley–Hanf residual holds** (countable-symbol languages): the tail-template
theory of the Morley seed is realizable over every target order — by the schema-route
construction, which does not even consume the sequence's tail indiscernibility. -/
theorem morleySeedTailTemplateRealizable_holds {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ n, L'.Relations n)] :
    MorleySeedTailTemplateRealizable (L' := L') := by
  intro φ M _ a J _ hSize hφ ha _
  exact morleySeed_tailTemplate_model_of_schemaSource φ M a J hSize hφ ha

/-- **The Morley–Hanf theorem, unconditional for countable-symbol languages**: `ℶ_{ω₁}` is a Hanf
bound for every `L_{ω₁ω}` sentence over a language with countably many function and relation
symbols. All inputs are now proved: tail extraction (`morleyHanfExtractionTail_holds`, countable
Ramsey) and seed-template realizability (the schema construction). -/
theorem morley_hanf_countable_symbols {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ n, L'.Relations n)]
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) :=
  morley_hanf_of_tail_realizable morleySeedTailTemplateRealizable_holds φ

end FirstOrder.Language
