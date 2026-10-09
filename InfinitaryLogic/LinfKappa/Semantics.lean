/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.LinfKappa.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Infinitary.IndexCoding

/-!
# Semantics of block-quantifier formulas

Realization of `L.BlockFormula ι V α Γ` in an `L`-structure `M`, given a valuation `v : α → M`
of the free variables and a valuation `xs : BlockSlots V Γ → M` of the slots of the context.

The block binder is interpreted by `Sum.elim`: `(allBlock q φ).Realize v xs` holds iff
`φ.Realize v (Sum.elim b xs)` for every block valuation `b : V q → M`.  This is a definitional
equation (`realize_allBlock` is `Iff.rfl`), with no cast.  The equation itself would hold for a
semireducible `BlockSlots` as well; reducibility is what the later `rw` and `simp` steps need,
for instance in `realize_closeAll` here and in the renaming and substitution lemmas of
`LinfKappa/Substitution.lean`.

## Main definitions and results

* `BlockFormula.Realize`, `BlockSentence.Realize`.
* `@[simp]` lemmas for every constructor and derived connective, and `realize_closeAll`.
* `BlockFormula.iInfAlong` and `BlockFormula.iSupAlong`: conjunction and disjunction of a family
  indexed by `κ`, expressed at the carrier `ι` through an `IndexCoding κ ι` and the fork's
  `IndexCoding.pad`, with `realize_iInfAlong` and `realize_iSupAlong`.

## Non-claims

No quantifier rank, back-and-forth relation or Scott rank is defined or related here, and nothing
bounds the size of blocks or conjunctions: the semantics is that of the raw syntax.
-/

set_option autoImplicit false

namespace FirstOrder.Language

namespace BlockFormula

/-- Realization of a block formula, given valuations of the free variables and of the slots of
the context.  A block binder quantifies over all valuations `V q → M` of the block. -/
def Realize.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] :
    ∀ {Γ}, L.BlockFormula ι V α Γ → (α → M) → (BlockSlots V Γ → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs => Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .allBlock q φ, v, xs => ∀ b : V q → M, Realize φ v (Sum.elim b xs)
  | _, .iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, .iInf φs, v, xs => ∀ i, Realize (φs i) v xs

@[simp]
theorem realize_falsum.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {v : α → M} {xs : BlockSlots V Γ → M} :
    (falsum : L.BlockFormula ι V α Γ).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_equal.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {t₁ t₂ : L.Term (α ⊕ BlockSlots V Γ)} {v : α → M} {xs : BlockSlots V Γ → M} :
    (equal t₁ t₂ : L.BlockFormula ι V α Γ).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_rel.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ BlockSlots V Γ)} {v : α → M}
    {xs : BlockSlots V Γ → M} :
    (rel R ts : L.BlockFormula ι V α Γ).Realize v xs ↔
      Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_imp.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {φ ψ : L.BlockFormula ι V α Γ} {v : α → M} {xs : BlockSlots V Γ → M} :
    (φ.imp ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) :=
  Iff.rfl

/-- The block binder is definitional: the block valuation is joined to the outer one by
`Sum.elim`, with no cast. -/
@[simp]
theorem realize_allBlock.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {q : Q} {φ : L.BlockFormula ι V α (q :: Γ)} {v : α → M} {xs : BlockSlots V Γ → M} :
    (allBlock q φ).Realize v xs ↔ ∀ b : V q → M, φ.Realize v (Sum.elim b xs) :=
  Iff.rfl

/-- Realization of a disjunction: one equation, generic in the carrier and its universe. -/
@[simp]
theorem realize_iSup.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {φs : ι → L.BlockFormula ι V α Γ} {v : α → M} {xs : BlockSlots V Γ → M} :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  Iff.rfl

/-- Realization of a conjunction: one equation, generic in the carrier and its universe. -/
@[simp]
theorem realize_iInf.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {φs : ι → L.BlockFormula ι V α Γ} {v : α → M} {xs : BlockSlots V Γ → M} :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_not.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {φ : L.BlockFormula ι V α Γ} {v : α → M} {xs : BlockSlots V Γ → M} :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_top.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {v : α → M} {xs : BlockSlots V Γ → M} :
    (⊤ : L.BlockFormula ι V α Γ).Realize v xs ↔ True := by
  simp [Top.top, BlockFormula.verum, BlockFormula.not, Realize]

@[simp]
theorem realize_bot.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {v : α → M} {xs : BlockSlots V Γ → M} :
    (⊥ : L.BlockFormula ι V α Γ).Realize v xs ↔ False :=
  Iff.rfl

/-- The derived block existential `¬ ∀ (block) ¬ φ` holds iff some valuation of the block
satisfies `φ`. -/
@[simp]
theorem realize_exBlock.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {q : Q} {φ : L.BlockFormula ι V α (q :: Γ)} {v : α → M} {xs : BlockSlots V Γ → M} :
    (BlockFormula.exBlock q φ).Realize v xs ↔ ∃ b : V q → M, φ.Realize v (Sum.elim b xs) := by
  simp only [BlockFormula.exBlock, realize_not, realize_allBlock, not_forall, not_not]

/-- The universal closure holds at the empty slot valuation iff the formula holds at every
valuation of the slots of its context. -/
@[simp]
theorem realize_closeAll.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {φ : L.BlockFormula ι V α Γ} {v : α → M} :
    (closeAll φ).Realize v (PEmpty.elim : BlockSlots V [] → M) ↔
      ∀ xs : BlockSlots V Γ → M, φ.Realize v xs := by
  induction Γ with
  | nil => exact ⟨fun h xs ↦ by rwa [Subsingleton.elim xs PEmpty.elim], fun h ↦ h _⟩
  | cons q Γ ih =>
    rw [closeAll, ih]
    refine ⟨fun h ys ↦ ?_, fun h xs b ↦ h _⟩
    have e : (Sum.elim (fun x ↦ ys (Sum.inl x)) (fun s ↦ ys (Sum.inr s)) :
        BlockSlots V (q :: Γ) → M) = ys := by
      funext s; rcases s with x | s <;> rfl
    have := h (fun s ↦ ys (Sum.inr s)) (fun x ↦ ys (Sum.inl x))
    rwa [e] at this

/-! ### Coded connectives -/

/-- Conjunction of a `κ`-indexed family at the carrier `ι`, along a coding `κ → ι`: indices that
do not decode are padded with `⊤`. -/
def iInfAlong.{u, v, uι, uQ, w, u', uκ} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} {κ : Type uκ} (c : IndexCoding κ ι)
    (φs : κ → L.BlockFormula ι V α Γ) : L.BlockFormula ι V α Γ :=
  .iInf (c.pad ⊤ φs)

/-- Disjunction of a `κ`-indexed family at the carrier `ι`, along a coding `κ → ι`: indices that
do not decode are padded with `⊥`. -/
def iSupAlong.{u, v, uι, uQ, w, u', uκ} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} {κ : Type uκ} (c : IndexCoding κ ι)
    (φs : κ → L.BlockFormula ι V α Γ) : L.BlockFormula ι V α Γ :=
  .iSup (c.pad ⊥ φs)

/-- The coded conjunction holds iff every member of the `κ`-indexed family holds: the padding
`⊤` at undecodable indices is harmless. -/
@[simp]
theorem realize_iInfAlong.{u, v, uι, uQ, w, u', wM, uκ} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {κ : Type uκ} {c : IndexCoding κ ι} {φs : κ → L.BlockFormula ι V α Γ} {v : α → M}
    {xs : BlockSlots V Γ → M} :
    (iInfAlong c φs).Realize v xs ↔ ∀ k, (φs k).Realize v xs := by
  simp only [iInfAlong, realize_iInf]
  refine ⟨fun h k ↦ by simpa using h (c.encode k), fun h i ↦ ?_⟩
  rcases hd : c.decode i with _ | k
  · rw [IndexCoding.pad_of_decode_none c hd]; simp
  · rw [IndexCoding.pad_of_decode_some c hd]; exact h k

/-- The coded disjunction holds iff some member of the `κ`-indexed family holds: the padding
`⊥` at undecodable indices is never satisfied. -/
@[simp]
theorem realize_iSupAlong.{u, v, uι, uQ, w, u', wM, uκ} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q}
    {κ : Type uκ} {c : IndexCoding κ ι} {φs : κ → L.BlockFormula ι V α Γ} {v : α → M}
    {xs : BlockSlots V Γ → M} :
    (iSupAlong c φs).Realize v xs ↔ ∃ k, (φs k).Realize v xs := by
  simp only [iSupAlong, realize_iSup]
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨c.encode k, by simpa using hk⟩⟩
  rcases hd : c.decode i with _ | k
  · rw [IndexCoding.pad_of_decode_none c hd] at hi; exact hi.elim
  · rw [IndexCoding.pad_of_decode_some c hd] at hi; exact ⟨k, hi⟩

end BlockFormula

/-- Realization of a block sentence in a structure: both valuations are empty. -/
def BlockSentence.Realize.{u, v, uι, uQ, w, wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} (φ : L.BlockSentence ι V) (M : Type wM) [L.Structure M] :
    Prop :=
  BlockFormula.Realize φ (Empty.elim : Empty → M) (PEmpty.elim : BlockSlots V [] → M)

end FirstOrder.Language
