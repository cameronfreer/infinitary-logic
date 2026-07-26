/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.QuantifierClass
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Preservation of the quantifier classes under embeddings (issue #15, Unit 1)

The semantic content of the signed quantifier traversal of `Lomega1omega/QuantifierClass.lean`:
along an embedding `e : A ↪[L] B`,

* **universal** formulas transport **downwards** — from `B` to `A`, and
* **existential** formulas transport **upwards** — from `A` to `B`.

```
realize_of_embedding_signed e φ v xs :
  (IsUniversal φ   → φ.Realize (e ∘ v) (e ∘ xs) → φ.Realize v xs) ∧
  (IsExistential φ → φ.Realize v xs → φ.Realize (e ∘ v) (e ∘ xs))
```

The statement is **valuation-aware**: it quantifies over free-variable valuations `v : α → A` *and*
bound-variable tuples `xs : Fin n → A`, with the two structures' data related only through `e`.
That is what makes the induction go through — the `all` case instantiates the `B`-side quantifier at
`e a` and must then recognise `Fin.snoc (e ∘ xs) (e a)` as `e ∘ Fin.snoc xs a`, which is a statement
about tuples, not about sentences.

The two directions are proved **simultaneously**, as a conjunction, for the same reason that
`universalSigned` is a single signed recursion: the `imp` case transports the antecedent by the
*other* direction, so neither implication is provable on its own.

`all` is where the sign convention is tested. Its universal half is the substructure argument; its
existential half is discharged because `IsExistential φ.all` is outright false — an existential
quantifier in this syntax is a `.not (.all (.not _))`, so it is handled by the `imp` recursion, and
`isExistential_ex` records that the encoding lands in the right class.

Neither the general theorem nor the sentence corollaries need the carriers to be nonempty; the
`_of_nonempty` corollary carries the instance binders only so it matches the nonempty convention of
`Sentenceω.Entails` and of the relative-preservation statements built on top of it.
-/

namespace FirstOrder.Language

open FirstOrder Structure

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α : Type}

/-- **Preservation of the quantifier classes under embeddings** (the Unit-1 acceptance gate).
Universal formulas reflect from the codomain to the domain; existential formulas transport from the
domain to the codomain.  Both halves are stated for arbitrary valuations and bound-variable tuples,
and are proved by one simultaneous induction. -/
theorem realize_of_embedding_signed {A B : Type} [L.Structure A] [L.Structure B] (e : A ↪[L] B) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → A) (xs : Fin n → A),
      (IsUniversal φ → φ.Realize (⇑e ∘ v) (⇑e ∘ xs) → φ.Realize v xs) ∧
      (IsExistential φ → φ.Realize v xs → φ.Realize (⇑e ∘ v) (⇑e ∘ xs)) := by
  have h_elim : ∀ {m : ℕ} (v : α → A) (xs : Fin m → A),
      Sum.elim (⇑e ∘ v) (⇑e ∘ xs) = ⇑e ∘ Sum.elim v xs := by
    intro m v xs
    funext x
    cases x with
    | inl _ => rfl
    | inr _ => rfl
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => ⟨fun _ h => h, fun _ h => h⟩
  | equal t₁ t₂ =>
    intro v xs
    have key : (t₁.realize (Sum.elim (⇑e ∘ v) (⇑e ∘ xs))
          = t₂.realize (Sum.elim (⇑e ∘ v) (⇑e ∘ xs)))
        ↔ (t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)) := by
      rw [h_elim v xs, HomClass.realize_term, HomClass.realize_term]
      exact e.injective.eq_iff
    exact ⟨fun _ h => key.mp h, fun _ h => key.mpr h⟩
  | rel R ts =>
    intro v xs
    have hts : (fun i => (ts i).realize (Sum.elim (⇑e ∘ v) (⇑e ∘ xs)))
        = fun i => e ((ts i).realize (Sum.elim v xs)) := by
      funext i
      rw [h_elim v xs, HomClass.realize_term]
    have key : (RelMap R fun i => (ts i).realize (Sum.elim (⇑e ∘ v) (⇑e ∘ xs)))
        ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) := by
      rw [hts]
      exact e.map_rel R _
    exact ⟨fun _ h => key.mp h, fun _ h => key.mpr h⟩
  | imp φ ψ ihφ ihψ =>
    intro v xs
    refine ⟨fun h hB hφ => ?_, fun h hA hφ => ?_⟩
    -- the antecedent is transported by the *other* direction
    · exact (ihψ v xs).1 h.2 (hB ((ihφ v xs).2 h.1 hφ))
    · exact (ihψ v xs).2 h.2 (hA ((ihφ v xs).1 h.1 hφ))
  | all φ ih =>
    intro v xs
    refine ⟨fun h hB a => ?_, fun h => absurd h.1 (by simp)⟩
    have hb := hB (e a)
    rw [← Fin.comp_snoc] at hb
    exact (ih v (Fin.snoc xs a)).1 h.2 hb
  | iSup φs ih =>
    intro v xs
    refine ⟨fun h hB => ?_, fun h hA => ?_⟩
    · obtain ⟨i, hi⟩ := hB
      exact ⟨i, (ih i v xs).1 (h i) hi⟩
    · obtain ⟨i, hi⟩ := hA
      exact ⟨i, (ih i v xs).2 (h i) hi⟩
  | iInf φs ih =>
    intro v xs
    exact ⟨fun h hB i => (ih i v xs).1 (h i) (hB i),
      fun h hA i => (ih i v xs).2 (h i) (hA i)⟩

/-- Universal formulas reflect along an embedding. -/
theorem realize_of_embedding_isUniversal {A B : Type} [L.Structure A] [L.Structure B]
    (e : A ↪[L] B) {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → A) (xs : Fin n → A)
    (hφ : IsUniversal φ) (h : φ.Realize (⇑e ∘ v) (⇑e ∘ xs)) : φ.Realize v xs :=
  (realize_of_embedding_signed e φ v xs).1 hφ h

/-- Existential formulas transport along an embedding. -/
theorem realize_of_embedding_isExistential {A B : Type} [L.Structure A] [L.Structure B]
    (e : A ↪[L] B) {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → A) (xs : Fin n → A)
    (hφ : IsExistential φ) (h : φ.Realize v xs) : φ.Realize (⇑e ∘ v) (⇑e ∘ xs) :=
  (realize_of_embedding_signed e φ v xs).2 hφ h

end BoundedFormulaω

namespace Sentenceω

open BoundedFormulaω

variable {L : Language.{0, 0}}

/-- A universal sentence true in an extension is true in the substructure. -/
theorem realize_of_embedding_isUniversal {A B : Type} [L.Structure A] [L.Structure B]
    (e : A ↪[L] B) (σ : L.Sentenceω) (hσ : IsUniversal σ) (h : Sentenceω.Realize σ B) :
    Sentenceω.Realize σ A := by
  have hv : (⇑e ∘ (Empty.elim : Empty → A)) = (Empty.elim : Empty → B) := funext fun x => x.elim
  have hxs : (⇑e ∘ (Fin.elim0 : Fin 0 → A)) = (Fin.elim0 : Fin 0 → B) := funext fun x => x.elim0
  refine BoundedFormulaω.realize_of_embedding_isUniversal e σ Empty.elim Fin.elim0 hσ ?_
  rw [hv, hxs]
  exact h

/-- An existential sentence true in a structure is true in every extension. -/
theorem realize_of_embedding_isExistential {A B : Type} [L.Structure A] [L.Structure B]
    (e : A ↪[L] B) (σ : L.Sentenceω) (hσ : IsExistential σ) (h : Sentenceω.Realize σ A) :
    Sentenceω.Realize σ B := by
  have hv : (⇑e ∘ (Empty.elim : Empty → A)) = (Empty.elim : Empty → B) := funext fun x => x.elim
  have hxs : (⇑e ∘ (Fin.elim0 : Fin 0 → A)) = (Fin.elim0 : Fin 0 → B) := funext fun x => x.elim0
  have := BoundedFormulaω.realize_of_embedding_isExistential e σ Empty.elim Fin.elim0 hσ h
  rwa [hv, hxs] at this

/-- The shape consumed by relative-preservation statements, whose semantics — like that of
`Sentenceω.Entails` — quantifies over **nonempty** structures.  The nonemptiness instances are
carried for interface compatibility only; the proof above does not use them. -/
theorem realize_of_embedding_isExistential_of_nonempty {A B : Type} [L.Structure A] [Nonempty A]
    [L.Structure B] [Nonempty B] (e : A ↪[L] B) (σ : L.Sentenceω) (hσ : IsExistential σ)
    (h : Sentenceω.Realize σ A) : Sentenceω.Realize σ B :=
  realize_of_embedding_isExistential e σ hσ h

end Sentenceω

end FirstOrder.Language
