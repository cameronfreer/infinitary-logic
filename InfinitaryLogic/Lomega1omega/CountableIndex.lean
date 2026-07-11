/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Countable connectives over arbitrary countable index types

`BoundedFormulaω`'s `iInf`/`iSup` are `ℕ`-indexed. Constructions like the Hanf beth ladder
(clause families over pairs of countable ordinals) and countable fragments quantify over
countable-but-not-`ℕ` index types. This file provides the conjunction/disjunction over any
countable index, in a two-layer API:

* the **explicit-surjection core** `ciInfOfSurjective e φs` / `ciSupOfSurjective e φs` — just
  `iInf`/`iSup` along `e : ℕ → ι`, with trivially-proved realization lemmas given
  `Function.Surjective e`;
* the **`[Countable ι]` wrappers** `ciInf`/`ciSup`, isolating the noncomputable enumeration
  choice (harmless defaults for empty `ι`: the tautology for `ciInf`, `falsum` for `ciSup`).

Only the realization lemmas are provided. No syntactic naturality API is built here: the
enumeration is noncanonical, so definitional commutation statements would be unpleasant —
consumers should work through `realize_ciInf`/`realize_ciSup`.
-/

namespace FirstOrder

namespace Language

namespace BoundedFormulaω

variable {L : Language.{u, v}} {γ : Type} {n : ℕ}

/-- Countable conjunction along an explicit enumeration `e : ℕ → ι`. -/
def ciInfOfSurjective {ι : Type} (e : ℕ → ι) (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  BoundedFormulaω.iInf fun k => φs (e k)

/-- Countable disjunction along an explicit enumeration `e : ℕ → ι`. -/
def ciSupOfSurjective {ι : Type} (e : ℕ → ι) (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  BoundedFormulaω.iSup fun k => φs (e k)

variable {M : Type w} [L.Structure M]

theorem realize_ciInfOfSurjective {ι : Type} {e : ℕ → ι} (he : Function.Surjective e)
    (φs : ι → L.BoundedFormulaω γ n) (v : γ → M) (xs : Fin n → M) :
    (ciInfOfSurjective e φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  rw [ciInfOfSurjective, realize_iInf]
  exact ⟨fun h i => by obtain ⟨k, rfl⟩ := he i; exact h k, fun h k => h (e k)⟩

theorem realize_ciSupOfSurjective {ι : Type} {e : ℕ → ι} (he : Function.Surjective e)
    (φs : ι → L.BoundedFormulaω γ n) (v : γ → M) (xs : Fin n → M) :
    (ciSupOfSurjective e φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  rw [ciSupOfSurjective, realize_iSup]
  exact ⟨fun ⟨k, hk⟩ => ⟨e k, hk⟩, fun ⟨i, hi⟩ => by obtain ⟨k, rfl⟩ := he i; exact ⟨k, hi⟩⟩

open Classical in
/-- **Countable conjunction over a countable index type** (tautology for empty `ι`). -/
noncomputable def ciInf {ι : Type} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  if h : Nonempty ι then
    ciInfOfSurjective (@exists_surjective_nat ι h _).choose φs
  else BoundedFormulaω.imp BoundedFormulaω.falsum BoundedFormulaω.falsum

open Classical in
/-- **Countable disjunction over a countable index type** (`falsum` for empty `ι`). -/
noncomputable def ciSup {ι : Type} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  if h : Nonempty ι then
    ciSupOfSurjective (@exists_surjective_nat ι h _).choose φs
  else BoundedFormulaω.falsum

theorem realize_ciInf {ι : Type} [Countable ι] (φs : ι → L.BoundedFormulaω γ n)
    (v : γ → M) (xs : Fin n → M) :
    (ciInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  classical
  rw [ciInf]
  split_ifs with h
  · exact realize_ciInfOfSurjective (@exists_surjective_nat ι h _).choose_spec φs v xs
  · exact iff_of_true (by rw [realize_imp]; exact fun hf => hf)
      (fun i => absurd ⟨i⟩ h)

theorem realize_ciSup {ι : Type} [Countable ι] (φs : ι → L.BoundedFormulaω γ n)
    (v : γ → M) (xs : Fin n → M) :
    (ciSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  classical
  rw [ciSup]
  split_ifs with h
  · exact realize_ciSupOfSurjective (@exists_surjective_nat ι h _).choose_spec φs v xs
  · exact iff_of_false (fun hf => (realize_falsum (v := v) (xs := xs)).mp hf)
      (fun ⟨i, _⟩ => absurd ⟨i⟩ h)

end BoundedFormulaω

end Language

end FirstOrder
