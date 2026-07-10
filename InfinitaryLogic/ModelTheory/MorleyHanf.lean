/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.MorleyHanfSchemaDischarge

/-!
# The Morley–Hanf theorem: public facade and corollaries

The stable entry point for the project's headline Hanf-number result. Importing this file (or
any bundle containing it, including the default `import InfinitaryLogic`) exposes

* `morley_hanf : IsHanfBound φ (ℶ_ω₁)` — for every `L_{ω₁ω}` sentence over an arbitrary
  language, with no hypotheses (proved in `Conditional/MorleyHanfSchemaDischarge.lean`);

together with the corollaries packaged here:

* `hanfNumber_le_beth_omega1` — the per-sentence Hanf number is at most `ℶ_{ω₁}`;
* `IsLomega1omegaHanfBound` / `Lomega1omegaHanfNumber` — the GLOBAL Hanf bound/number of the
  logic `L_{ω₁ω}` (over all languages and sentences), with
  `beth_omega1_isLomega1omegaHanfBound` and `Lomega1omegaHanfNumber_le_beth_omega1`. These give
  the upper half of the classical `Hanf(L_{ω₁ω}) = ℶ_{ω₁}`; the lower bound (sharpness) is
  future work;
* `morley_hanf_theory` — every countable `L_{ω₁ω}`-theory with a model of size `≥ ℶ_{ω₁}` has
  arbitrarily large models (via `Theoryω.conjunction`).
-/

namespace FirstOrder

namespace Language

open Cardinal

/-- **The Hanf number of every `L_{ω₁ω}` sentence is at most `ℶ_{ω₁}`** — `morley_hanf` through
the universal property of `HanfNumber`. -/
theorem hanfNumber_le_beth_omega1 {L' : Language.{0, 0}} (φ : L'.Sentenceω) :
    HanfNumber φ ≤ Cardinal.beth (Ordinal.omega 1) :=
  hanfNumber_le_of_isHanfBound (morley_hanf φ)

/-- **A global Hanf bound for the logic `L_{ω₁ω}`**: a cardinal that is a Hanf bound for every
sentence of every language. -/
def IsLomega1omegaHanfBound (κ : Cardinal) : Prop :=
  ∀ (L' : Language.{0, 0}) (φ : L'.Sentenceω), IsHanfBound φ κ

/-- **The Hanf number of the logic `L_{ω₁ω}`**: the least global Hanf bound. -/
noncomputable def Lomega1omegaHanfNumber : Cardinal :=
  sInf {κ : Cardinal | IsLomega1omegaHanfBound κ}

/-- `ℶ_{ω₁}` is a global Hanf bound for `L_{ω₁ω}` — the Morley–Hanf theorem in global form. -/
theorem beth_omega1_isLomega1omegaHanfBound :
    IsLomega1omegaHanfBound (Cardinal.beth (Ordinal.omega 1)) :=
  fun _ φ => morley_hanf φ

/-- **The Hanf number of `L_{ω₁ω}` is at most `ℶ_{ω₁}`** — the upper half of the classical
`Hanf(L_{ω₁ω}) = ℶ_{ω₁}`; the lower bound (sharpness) is future work. -/
theorem Lomega1omegaHanfNumber_le_beth_omega1 :
    Lomega1omegaHanfNumber ≤ Cardinal.beth (Ordinal.omega 1) :=
  csInf_le' beth_omega1_isLomega1omegaHanfBound

/-- **The Morley–Hanf theorem for countable theories**: every countable `L_{ω₁ω}`-theory with a
model of size at least `ℶ_{ω₁}` has models of arbitrarily large cardinality — apply
`morley_hanf` to the theory's conjunction (`Theoryω.conjunction`). -/
theorem morley_hanf_theory {L' : Language.{0, 0}} (T : L'.Theoryω) (hT : T.Countable)
    (hM : ∃ (M : Type) (_ : L'.Structure M), T.Model M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    ∀ κ : Cardinal, ∃ (N : Type) (_ : L'.Structure N), T.Model N ∧ Cardinal.mk N ≥ κ := by
  obtain ⟨M, instM, hTM, hsize⟩ := hM
  have h := morley_hanf (T.conjunction hT)
    ⟨M, instM, (Theoryω.realize_conjunction_iff T hT M).mpr hTM, hsize⟩
  intro κ
  obtain ⟨N, instN, hφN, hκ⟩ := h κ
  exact ⟨N, instN, (Theoryω.realize_conjunction_iff T hT N).mp hφN, hκ⟩

end Language

end FirstOrder
