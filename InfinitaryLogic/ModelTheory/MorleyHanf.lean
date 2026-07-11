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
  `beth_omega1_isLomega1omegaHanfBound` and `Lomega1omegaHanfNumber_le_beth_omega1`. This is
  the upper half of the classical `Hanf(L_{ω₁ω}) = ℶ_{ω₁}`; the matching lower half and the
  exact equality `Lomega1omegaHanfNumber_eq_beth_omega1` are proved by the beth-ladder
  spectrum witnesses in `HanfSpectrum/BethLadder.lean`;
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

/-- A global Hanf bound stays a bound at every larger cardinal. -/
theorem IsLomega1omegaHanfBound.mono {κ μ : Cardinal}
    (hκ : IsLomega1omegaHanfBound κ) (hκμ : κ ≤ μ) : IsLomega1omegaHanfBound μ :=
  fun L' φ => (hκ L' φ).mono hκμ

/-- **The global Hanf number is itself a global Hanf bound**: the set of bounds is nonempty
(`beth_omega1_isLomega1omegaHanfBound`), and an infimum of cardinals is attained. -/
theorem Lomega1omegaHanfNumber_isHanfBound :
    IsLomega1omegaHanfBound Lomega1omegaHanfNumber :=
  show Lomega1omegaHanfNumber ∈ {κ : Cardinal | IsLomega1omegaHanfBound κ} from
    csInf_mem ⟨_, beth_omega1_isLomega1omegaHanfBound⟩

/-- The global Hanf number is the least global Hanf bound. -/
theorem Lomega1omegaHanfNumber_le_of_isHanfBound {κ : Cardinal}
    (hκ : IsLomega1omegaHanfBound κ) : Lomega1omegaHanfNumber ≤ κ :=
  csInf_le' hκ

/-- The universal property of the global Hanf number: `Lomega1omegaHanfNumber ≤ κ` exactly when
`κ` is a global Hanf bound. The strict dual `κ < H ↔ ¬IsBound κ` below is the bounded-spectrum
witness-consumption interface. -/
theorem Lomega1omegaHanfNumber_le_iff_isHanfBound {κ : Cardinal} :
    Lomega1omegaHanfNumber ≤ κ ↔ IsLomega1omegaHanfBound κ :=
  ⟨fun h => Lomega1omegaHanfNumber_isHanfBound.mono h, Lomega1omegaHanfNumber_le_of_isHanfBound⟩

/-- The strict dual of the universal property — the bounded-spectrum witness-consumption
interface: refuting the global bound at `κ` is exactly the strict lower bound
`κ < Lomega1omegaHanfNumber`. -/
theorem lt_Lomega1omegaHanfNumber_iff_not_isHanfBound {κ : Cardinal} :
    κ < Lomega1omegaHanfNumber ↔ ¬IsLomega1omegaHanfBound κ := by
  rw [← not_le, Lomega1omegaHanfNumber_le_iff_isHanfBound]

/-- **The generic bounded-spectrum argument**: a sentence with a model of size `≥ κ` whose every
model has size `≤ κ` is not arbitrarily large, so `κ` is not a global Hanf bound and
`κ < Lomega1omegaHanfNumber`. The common endpoint for the countable witness, the powerset
witness, and every stage of the Marker `ℶ_{α+1}` ladder. -/
theorem lt_Lomega1omegaHanfNumber_of_maximal_model
    {L : Language.{0, 0}} {φ : L.Sentenceω} {κ : Cardinal}
    (hmodel : ∃ (M : Type) (_ : L.Structure M),
      Sentenceω.Realize φ M ∧ κ ≤ Cardinal.mk M)
    (hupper : ∀ (M : Type) (_ : L.Structure M),
      Sentenceω.Realize φ M → Cardinal.mk M ≤ κ) :
    κ < Lomega1omegaHanfNumber := by
  rw [lt_Lomega1omegaHanfNumber_iff_not_isHanfBound]
  intro h
  obtain ⟨M, instM, hφM, hκM⟩ := hmodel
  obtain ⟨N, instN, hφN, hN⟩ := h L φ ⟨M, instM, hφM, hκM⟩ (Order.succ κ)
  exact absurd (le_trans hN (hupper N instN hφN)) (not_le.mpr (Order.lt_succ κ))

/-- **The Hanf number of `L_{ω₁ω}` is at most `ℶ_{ω₁}`** — the upper half of the classical
`Hanf(L_{ω₁ω}) = ℶ_{ω₁}`; the matching lower half and the exact equality
`Lomega1omegaHanfNumber_eq_beth_omega1` are proved in `HanfSpectrum/BethLadder.lean`. -/
@[blueprint "thm:hanf-upper-global"
  (title := /-- Global Hanf upper bound -/)
  (statement := /-- $\mathrm{Hanf}(\Lomegaone) \le \beth_{\omegaone}$: the global Hanf number
    of $\Lomegaone$, over all languages and sentences, is at most $\beth_{\omegaone}$. -/)
  (proof := /-- Immediate from the Morley--Hanf theorem: $\beth_{\omegaone}$ is a Hanf bound
    for every sentence, so it is a global Hanf bound, and the global Hanf number is the least
    such. -/)
  (uses := ["thm:morley-hanf"])]
theorem Lomega1omegaHanfNumber_le_beth_omega1 :
    Lomega1omegaHanfNumber ≤ Cardinal.beth (Ordinal.omega 1) :=
  Lomega1omegaHanfNumber_le_of_isHanfBound beth_omega1_isLomega1omegaHanfBound

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
