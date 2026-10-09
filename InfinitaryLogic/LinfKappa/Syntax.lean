/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Block-quantifier syntax for `L_{∞κ}`

Formulas of the infinitary logic `L_{∞κ}` quantify over whole **blocks** of variables at once:
`∀ (yₓ)_{x ∈ X}` with `X` of size `< κ`.  This file fixes the representation.

* A type `Q` of **block codes** and a family of **shapes** `V : Q → Type w`: the block coded by
  `q` binds the variables `V q`.
* A **context** is a list `Γ : List Q` of codes, head block first (de Bruijn order).  Its
  **variable slots** are `BlockSlots V Γ`, defined by recursion on the list:
  `BlockSlots V [] = PEmpty` and `BlockSlots V (q :: Γ) = V q ⊕ BlockSlots V Γ`.
* `L.BlockFormula ι V α Γ` is the type of formulas with free variables `α`, bound slots
  `BlockSlots V Γ`, and infinitary conjunctions and disjunctions branching over the carrier `ι`.
  Its constructors are `falsum`, `equal`, `rel`, `imp`, the block binder `allBlock q`, and `iSup`
  and `iInf`.  It lives in `Type (max u v uι uQ w u')`: no universe is raised.

A block of any size is one binder, and binding is `Sum.elim` of the block valuation with the
outer one (see `realize_allBlock` in `LinfKappa/Semantics.lean`), definitionally and without
casts.  Reassociating a context `Γ ++ (Δ ++ Ε)` is an equivalence of slots
(`BlockSlots.reassocEquiv`), applied by renaming, never a cast on formulas.

## Transparency

`BlockSlots` is `@[reducible]`.  This is load-bearing: with a semireducible definition, the
binder case of the renaming lemma `realize_mapSlots` fails, because `rw` checks the motive at the
`implicit` transparency level and cannot then see that `Sum.map id ρ`, whose type mentions
`V q ⊕ BlockSlots V Γ`, is a map out of `BlockSlots V (q :: Γ)`.
`scripts/check_linfkappa_syntax_regressions.lean` pins the reducibility status and keeps the
failing `rw` as a regression.

A limit of the reducible definition: the discrimination-tree key of a `simp` lemma whose left
side mentions slots of a concrete context, such as `BlockSlots finShapes [3, 2]`, is computed
from the unfolded sum `Fin 3 ⊕ (Fin 2 ⊕ PEmpty)`, and such a lemma was observed not to fire on
the goals produced by `realize_allBlock`, although `rw` with it works.  State such lemmas at the
formula level (the guard does so for its finite-block test) or use `rw`.

## Main definitions

* `BlockSlots`, `BlockFormula`, `BlockSentence`.
* Derived connectives `BlockFormula.not`, `BlockFormula.verum`, `BlockFormula.exBlock`, the
  instances `Bot`, `Top`, `Inhabited`, and `BlockFormula.closeAll`.
* Slot equivalences `BlockSlots.appendEquiv`, `BlockSlots.inl`, `BlockSlots.inr` and
  `BlockSlots.reassocEquiv`, with component and inverse equations.  The shape family `V` is an
  explicit argument of each, since it cannot be recovered by unification from a reducible
  `BlockSlots V Γ`.
* Canonical shapes: `InitCode κ` and `initSeg κ` (initial segments of `κ.ord.ToType`),
  `finShapes` (the finite blocks `Fin n`) and `unitShape` (singleton blocks).

## Non-claims

* There is no `κ` in the syntax: the datatype is generic in `(Q, V)`.  Nothing here says that a
  formula has fewer than `κ` free variables, that its blocks have size `< κ`, or that its
  conjunctions are small; those are predicates on shapes and formulas, introduced later.
* There is no quantifier rank, no back-and-forth relation, and no relation to the finite-block
  ranks or to any Scott rank.
* The canonical shapes are abbreviations only; no cardinality law about them is proved here.

## References

* M. A. Dickmann, *Larger infinitary languages*, in *Model-Theoretic Logics* (J. Barwise and
  S. Feferman, eds.), Springer-Verlag, 1985, ch. IX, pp. 317–363.  The formation rules of
  `L_{κλ}` are those of §1 (p. 317); here the block bound and the conjunction bound are not part
  of the syntax.
-/

set_option autoImplicit false

namespace FirstOrder.Language

/-- Variable slots of a context of block codes; the head block comes first (de Bruijn).

It is `@[reducible]` so that `Sum.elim b xs` and `Sum.map id ρ` are recognised at the `implicit`
transparency level used by `rw`'s motive check as functions on `BlockSlots V (q :: Γ)`; see the
module docstring. -/
@[reducible] def BlockSlots.{uQ, w} {Q : Type uQ} (V : Q → Type w) : List Q → Type w
  | [] => PEmpty
  | q :: Γ => V q ⊕ BlockSlots V Γ

/-- Infinitary formulas with block quantifiers: free variables `α`, bound slots
`BlockSlots V Γ` for the context `Γ`, and conjunctions and disjunctions branching over `ι`. -/
inductive BlockFormula.{u, v, uι, uQ, w, u'} (L : Language.{u, v}) (ι : Type uι) {Q : Type uQ}
    (V : Q → Type w) (α : Type u') : List Q → Type (max u v uι uQ w u') where
  /-- The false formula. -/
  | falsum {Γ} : BlockFormula L ι V α Γ
  /-- Equality of two terms over the free variables and the slots of the context. -/
  | equal {Γ} (t₁ t₂ : L.Term (α ⊕ BlockSlots V Γ)) : BlockFormula L ι V α Γ
  /-- A relation symbol applied to terms. -/
  | rel {Γ} {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ BlockSlots V Γ)) :
      BlockFormula L ι V α Γ
  /-- Implication. -/
  | imp {Γ} (φ ψ : BlockFormula L ι V α Γ) : BlockFormula L ι V α Γ
  /-- Universal quantification over the whole block `V q`, which becomes the head block. -/
  | allBlock {Γ} (q : Q) (φ : BlockFormula L ι V α (q :: Γ)) : BlockFormula L ι V α Γ
  /-- Disjunction of an `ι`-indexed family. -/
  | iSup {Γ} (φs : ι → BlockFormula L ι V α Γ) : BlockFormula L ι V α Γ
  /-- Conjunction of an `ι`-indexed family. -/
  | iInf {Γ} (φs : ι → BlockFormula L ι V α Γ) : BlockFormula L ι V α Γ

/-- Block sentences: no free variables and the empty context. -/
abbrev BlockSentence.{u, v, uι, uQ, w} (L : Language.{u, v}) (ι : Type uι) {Q : Type uQ}
    (V : Q → Type w) :=
  L.BlockFormula ι V Empty []

namespace BlockFormula

/-- Negation, as implication to `falsum`. -/
@[match_pattern]
protected def not.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} (φ : L.BlockFormula ι V α Γ) :
    L.BlockFormula ι V α Γ :=
  φ.imp .falsum

/-- The true formula. -/
protected def verum.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} : L.BlockFormula ι V α Γ :=
  BlockFormula.falsum.not

instance instBot.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} : Bot (L.BlockFormula ι V α Γ) :=
  ⟨.falsum⟩

instance instTop.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} : Top (L.BlockFormula ι V α Γ) :=
  ⟨BlockFormula.verum⟩

instance instInhabited.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {Γ : List Q} :
    Inhabited (L.BlockFormula ι V α Γ) :=
  ⟨⊥⟩

/-- Existential quantification over the whole block `V q`: `¬ ∀ (block) ¬ φ`. -/
@[match_pattern]
protected def exBlock.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} (q : Q) (φ : L.BlockFormula ι V α (q :: Γ)) :
    L.BlockFormula ι V α Γ :=
  (allBlock q φ.not).not

/-- Universal closure over every block of the context, by recursion on the context: the head
block is bound innermost. -/
def closeAll.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} : ∀ {Γ : List Q}, L.BlockFormula ι V α Γ →
    L.BlockFormula ι V α []
  | [], φ => φ
  | _ :: _, φ => closeAll (allBlock _ φ)

end BlockFormula

namespace BlockSlots

/-- The slots of an appended context split as a sum; the head block of `Γ` stays leftmost. -/
def appendEquiv.{uQ, w} {Q : Type uQ} (V : Q → Type w) :
    ∀ (Γ Δ : List Q), BlockSlots V (Γ ++ Δ) ≃ BlockSlots V Γ ⊕ BlockSlots V Δ
  | [], Δ => (_root_.Equiv.emptySum PEmpty (BlockSlots V Δ)).symm
  | q :: Γ, Δ => (_root_.Equiv.sumCongr (_root_.Equiv.refl (V q)) (appendEquiv V Γ Δ)).trans
      (_root_.Equiv.sumAssoc _ _ _).symm

/-- The left inclusion `BlockSlots V Γ → BlockSlots V (Γ ++ Δ)`. -/
def inl.{uQ, w} {Q : Type uQ} (V : Q → Type w) (Γ Δ : List Q) (s : BlockSlots V Γ) :
    BlockSlots V (Γ ++ Δ) :=
  (appendEquiv V Γ Δ).symm (Sum.inl s)

/-- The right inclusion `BlockSlots V Δ → BlockSlots V (Γ ++ Δ)`. -/
def inr.{uQ, w} {Q : Type uQ} (V : Q → Type w) (Γ Δ : List Q) (s : BlockSlots V Δ) :
    BlockSlots V (Γ ++ Δ) :=
  (appendEquiv V Γ Δ).symm (Sum.inr s)

/-- Structural pin: the head block stays on the left. -/
theorem appendEquiv_cons_inl.{uQ, w} {Q : Type uQ} {V : Q → Type w} (q : Q) (Γ Δ : List Q)
    (x : V q) : appendEquiv V (q :: Γ) Δ (Sum.inl x) = Sum.inl (Sum.inl x) :=
  rfl

/-- Structural pin: a tail slot of `(q :: Γ) ++ Δ` goes where its image under the tail
equivalence says. -/
theorem appendEquiv_cons_inr.{uQ, w} {Q : Type uQ} {V : Q → Type w} (q : Q) (Γ Δ : List Q)
    (s : BlockSlots V (Γ ++ Δ)) :
    appendEquiv V (q :: Γ) Δ (Sum.inr s) =
      (appendEquiv V Γ Δ s).elim (fun t ↦ Sum.inl (Sum.inr t)) Sum.inr := by
  rcases h : appendEquiv V Γ Δ s with t | t <;> simp [appendEquiv, h]

/-- Structural pin: the empty prefix contributes nothing. -/
theorem appendEquiv_nil.{uQ, w} {Q : Type uQ} {V : Q → Type w} (Δ : List Q)
    (s : BlockSlots V ([] ++ Δ)) : appendEquiv V [] Δ s = Sum.inr s :=
  rfl

/-- Three-way reassociation of contexts, as an equivalence of slots. -/
def reassocEquiv.{uQ, w} {Q : Type uQ} (V : Q → Type w) (Γ Δ Ε : List Q) :
    BlockSlots V (Γ ++ (Δ ++ Ε)) ≃ BlockSlots V ((Γ ++ Δ) ++ Ε) :=
  (appendEquiv V Γ (Δ ++ Ε)).trans <|
    (_root_.Equiv.sumCongr (_root_.Equiv.refl _) (appendEquiv V Δ Ε)).trans <|
      (_root_.Equiv.sumAssoc _ _ _).symm.trans <|
        (_root_.Equiv.sumCongr (appendEquiv V Γ Δ).symm (_root_.Equiv.refl _)).trans
          (appendEquiv V (Γ ++ Δ) Ε).symm

/-- Component equation: a slot of `Γ` stays in `Γ`. -/
theorem reassocEquiv_left.{uQ, w} {Q : Type uQ} {V : Q → Type w} (Γ Δ Ε : List Q)
    (s : BlockSlots V Γ) :
    reassocEquiv V Γ Δ Ε (inl V Γ (Δ ++ Ε) s) = inl V (Γ ++ Δ) Ε (inl V Γ Δ s) := by
  simp [reassocEquiv, inl]

/-- Component equation: a slot of `Δ` stays in `Δ`. -/
theorem reassocEquiv_middle.{uQ, w} {Q : Type uQ} {V : Q → Type w} (Γ Δ Ε : List Q)
    (d : BlockSlots V Δ) :
    reassocEquiv V Γ Δ Ε (inr V Γ (Δ ++ Ε) (inl V Δ Ε d)) = inl V (Γ ++ Δ) Ε (inr V Γ Δ d) := by
  simp [reassocEquiv, inl, inr]

/-- Component equation: a slot of `Ε` stays in `Ε`. -/
theorem reassocEquiv_right.{uQ, w} {Q : Type uQ} {V : Q → Type w} (Γ Δ Ε : List Q)
    (e : BlockSlots V Ε) :
    reassocEquiv V Γ Δ Ε (inr V Γ (Δ ++ Ε) (inr V Δ Ε e)) = inr V (Γ ++ Δ) Ε e := by
  simp [reassocEquiv, inr]

/-- Inverse equation: undoing the reassociation. -/
theorem reassocEquiv_symm_apply_apply.{uQ, w} {Q : Type uQ} {V : Q → Type w} (Γ Δ Ε : List Q)
    (s : BlockSlots V (Γ ++ (Δ ++ Ε))) :
    (reassocEquiv V Γ Δ Ε).symm (reassocEquiv V Γ Δ Ε s) = s :=
  (reassocEquiv V Γ Δ Ε).symm_apply_apply s

/-- Inverse equation: redoing the reassociation. -/
theorem reassocEquiv_apply_symm_apply.{uQ, w} {Q : Type uQ} {V : Q → Type w} (Γ Δ Ε : List Q)
    (s : BlockSlots V ((Γ ++ Δ) ++ Ε)) :
    reassocEquiv V Γ Δ Ε ((reassocEquiv V Γ Δ Ε).symm s) = s :=
  (reassocEquiv V Γ Δ Ε).apply_symm_apply s

end BlockSlots

/-! ### Canonical shapes

Abbreviations only; their cardinality laws are not part of this file. -/

/-- Canonical block codes below `κ`: the elements of `κ.ord.ToType`, a type of size `κ`. -/
abbrev InitCode.{w} (κ : Cardinal.{w}) : Type w :=
  κ.ord.ToType

/-- The canonical block coded by `q`: the initial segment below `q`. -/
abbrev initSeg.{w} (κ : Cardinal.{w}) (q : InitCode κ) : Type w :=
  {x : InitCode κ // x < q}

/-- Finite blocks: the code `n` binds `Fin n`. -/
abbrev finShapes : ℕ → Type :=
  Fin

/-- Singleton blocks: one code, binding one variable. -/
abbrev unitShape : Unit → Type :=
  fun _ ↦ PUnit

end FirstOrder.Language
