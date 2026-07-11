/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.HanfSpectrum.VonNeumannModel
import InfinitaryLogic.ModelTheory.HanfSpectrum.LadderBound
import InfinitaryLogic.ModelTheory.MorleyHanf

/-!
# The beth ladder: sharpness of the Morley–Hanf bound

The assembly of Marker's Exercise 5.3 ladder: for every `α < ω₁` the ladder sentence has the
von Neumann model of size exactly `ℶ_{α+1}` (`VonNeumannModel.lean`) and no larger models
(`LadderBound.lean`), so through the generic bounded-spectrum endpoint each `ℶ_{α+1}` is a
strict lower bound for the global Hanf number; the successor-cofinal supremum
(`CardinalBounds.lean`) then gives `ℶ_{ω₁} ≤ Hanf(L_{ω₁ω})`. Combined with the Morley–Hanf
upper bound `Lomega1omegaHanfNumber_le_beth_omega1`:

* `Lomega1omegaHanfNumber_eq_beth_omega1` — **`Hanf(L_{ω₁ω}) = ℶ_{ω₁}`**, the exact Hanf
  number of `L_{ω₁ω}` over `Language.{0,0}`.

Reference: Marker, *Lectures on Infinitary Model Theory*, Exercise 5.3 and Theorem 5.4.
-/

namespace FirstOrder

namespace Language

open HanfLadder

/-- **The per-stage sharpness step**: for every `α < ω₁`, the ladder sentence has maximal
model size exactly `ℶ_{α+1}`, so `ℶ_{α+1} < Lomega1omegaHanfNumber`. -/
@[blueprint "thm:hanf-ladder-stage"
  (title := /-- Beth-ladder stage witnesses -/)
  (statement := /-- For every $\alpha < \omegaone$ there is an $\Lomegaone$ sentence whose
    models have size exactly $\beth_{\alpha+1}$ at the maximum, so
    $\beth_{\alpha+1} < \mathrm{Hanf}(\Lomegaone)$. -/)
  (proof := /-- Marker's Exercise 5.3 ladder sentence over the level order $(\alpha+2)$:
    countably many constants enumerate the base level, adjacent levels descend along an
    extensional edge relation, and limit levels are covered. The von Neumann stages
    $V_{\omega+\beta}$ (with Mathlib's $|V_o| = \beth^{\mathrm{pre}}_o$) give a model of
    size exactly $\beth_{\alpha+1}$ after `Shrink` transport; conversely a well-founded
    induction on the level order bounds every level of every model by powerset and
    countable-union steps. -/)
  (uses := ["def:arb-large-models", "def:hanf-bound"])]
theorem beth_add_one_lt_Lomega1omegaHanfNumber {α : Ordinal.{0}}
    (hα : α < Ordinal.omega 1) :
    Cardinal.beth (α + 1) < Lomega1omegaHanfNumber := by
  haveI : Countable (Index α) := countable_index_of_lt_omega1 hα
  letI := vStructure α
  refine lt_Lomega1omegaHanfNumber_of_maximal_model
    ⟨VCarrier α, inferInstance,
      realize_ladderSentence_iff.mpr (vStructure_isLadderModel α), (mk_vCarrier α).ge⟩
    (fun M instM hM => mk_le_beth_of_isLadderModel (realize_ladderSentence_iff.mp hM))

/-- The lower half of the Hanf-number computation: `ℶ_{ω₁} ≤ Lomega1omegaHanfNumber`, by the
successor-cofinal supremum over the ladder stages. -/
@[blueprint "thm:hanf-lower-global"
  (title := /-- Global Hanf lower bound -/)
  (statement := /-- $\beth_{\omegaone} \le \mathrm{Hanf}(\Lomegaone)$. -/)
  (proof := /-- The successor ordinals are cofinal in $\omegaone$, so
    $\beth_{\omegaone} = \sup_{\alpha<\omegaone} \beth_{\alpha+1}$, and each
    $\beth_{\alpha+1}$ is a strict lower bound by the ladder-stage witnesses. -/)
  (uses := ["thm:hanf-ladder-stage"])]
theorem beth_omega1_le_Lomega1omegaHanfNumber :
    Cardinal.beth (Ordinal.omega 1) ≤ Lomega1omegaHanfNumber := by
  rw [← FirstOrder.HanfLadder.iSup_beth_add_one_omega1]
  exact ciSup_le' fun α => (beth_add_one_lt_Lomega1omegaHanfNumber α.2).le

/-- **The Hanf number of `L_{ω₁ω}` is exactly `ℶ_{ω₁}`** (Morley; Marker, Theorem 5.4): the
Morley–Hanf upper bound `morley_hanf` is sharp. -/
@[blueprint "thm:hanf-exact"
  (title := /-- The exact Hanf number of L-omega1-omega -/)
  (statement := /-- $\mathrm{Hanf}(\Lomegaone) = \beth_{\omegaone}$: the global Hanf number
    of $\Lomegaone$ over $\mathrm{Type}$-$0$ languages is exactly $\beth_{\omegaone}$. -/)
  (proof := /-- Antisymmetry of the global upper bound (the Morley--Hanf theorem, via bounded
    Erd\H{o}s--Rado and the Marker/schema completion) and the global lower bound (the beth
    ladder: countable-index syntax, von Neumann hierarchy witnesses, bounded spectra at every
    beth successor, and the cofinal supremum). -/)
  (uses := ["thm:hanf-upper-global", "thm:hanf-lower-global"])]
theorem Lomega1omegaHanfNumber_eq_beth_omega1 :
    Lomega1omegaHanfNumber = Cardinal.beth (Ordinal.omega 1) :=
  le_antisymm Lomega1omegaHanfNumber_le_beth_omega1 beth_omega1_le_Lomega1omegaHanfNumber

end Language

end FirstOrder
