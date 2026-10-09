/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.LinfKappa.Semantics
import Mathlib.ModelTheory.Infinitary.Semantics

/-!
# The unary syntax as singleton blocks

The fork's unary infinitary syntax `L.BoundedFormulaInf ι α n` quantifies one variable at a time,
with bound variables `Fin n` extended by `Fin.snoc`.  It embeds semantically into block syntax
over any code `one : Q` whose block is a singleton (`[Unique (V one)]`):

* `BlockSlots.finToSlots V one n : Fin n → BlockSlots V (List.replicate n one)` sends the
  **last** unary variable (`Fin.last n`, the `Fin.snoc` position) to the **head** block, the
  others to the tail;
* `BlockFormula.ofInf one` replaces each unary quantifier by a singleton block binder;
* `realize_ofInf`: the translation preserves realization, the slot valuation being read through
  `finToSlots`.

At `ι := ℕ` this accepts `BoundedFormulaω` (a fork `abbrev` for `BoundedFormulaInf ℕ`) with no
cast.

## Non-claims

`ofInf` is a semantic embedding.  Nothing is claimed about a reverse translation (expanding finite
blocks into unary quantifiers), about quantifier rank, or about syntactic injectivity.  The
definition of `BoundedFormulaω`, its facade and its definitional identifications are unchanged.
-/

set_option autoImplicit false

namespace FirstOrder.Language

namespace BlockSlots

/-- The `n` unary bound variables as the slots of `n` singleton blocks.  The last unary
variable (`Fin.last n`, the `Fin.snoc` position) is the head block. -/
def finToSlots.{uQ, w} {Q : Type uQ} (V : Q → Type w) (one : Q) [Unique (V one)] :
    ∀ n, Fin n → BlockSlots V (List.replicate n one)
  | 0, i => i.elim0
  | n + 1, i => Fin.lastCases (Sum.inl default) (fun j ↦ Sum.inr (finToSlots V one n j)) i

/-- Reading a slot valuation of `n + 1` singleton blocks through `finToSlots` is `Fin.snoc` of
the tail reading and the head block's value. -/
theorem comp_finToSlots_succ.{uQ, w, wM} {Q : Type uQ} {V : Q → Type w} {M : Type wM}
    (one : Q) [Unique (V one)] (n : ℕ) (b : V one → M)
    (ys : BlockSlots V (List.replicate n one) → M) :
    (Sum.elim b ys : BlockSlots V (one :: List.replicate n one) → M) ∘ finToSlots V one (n + 1)
      = Fin.snoc (ys ∘ finToSlots V one n) (b default) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Function.comp_apply, finToSlots, Fin.lastCases_last, Fin.snoc_last, Sum.elim_inl]
  · simp only [Function.comp_apply, finToSlots, Fin.lastCases_castSucc, Fin.snoc_castSucc,
      Sum.elim_inr]

end BlockSlots

namespace BlockFormula

/-- The unary syntax as singleton blocks: each unary quantifier becomes a block binder over the
singleton code `one`. -/
def ofInf.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} (one : Q) [Unique (V one)] :
    ∀ {n}, L.BoundedFormulaInf ι α n → L.BlockFormula ι V α (List.replicate n one)
  | _, .falsum => .falsum
  | n, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map id (BlockSlots.finToSlots V one n)))
      (t₂.relabel (Sum.map id (BlockSlots.finToSlots V one n)))
  | n, .rel R ts => .rel R fun i ↦ (ts i).relabel (Sum.map id (BlockSlots.finToSlots V one n))
  | _, .imp φ ψ => (ofInf one φ).imp (ofInf one ψ)
  | _, .all φ => .allBlock one (ofInf one φ)
  | _, .iSup φs => .iSup fun i ↦ ofInf one (φs i)
  | _, .iInf φs => .iInf fun i ↦ ofInf one (φs i)

/-- The singleton-block translation preserves realization. -/
theorem realize_ofInf.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] (one : Q)
    [Unique (V one)] {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (v : α → M)
    (ys : BlockSlots V (List.replicate n one) → M) :
    (ofInf one φ).Realize v ys ↔ φ.Realize v (ys ∘ BlockSlots.finToSlots V one n) := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [ofInf, realize_equal, Term.realize_relabel, BoundedFormulaInf.realize_equal]
    rw [Sum.elim_comp_map]; rfl
  | rel R ts =>
    simp only [ofInf, realize_rel, Term.realize_relabel, BoundedFormulaInf.realize_rel]
    rw [Sum.elim_comp_map]; rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ ys) (ihψ ys)
  | @all n φ ih =>
    simp only [ofInf, realize_allBlock, BoundedFormulaInf.realize_all]
    constructor
    · intro h y
      have := (ih _).mp (h fun _ ↦ y)
      rwa [BlockSlots.comp_finToSlots_succ] at this
    · intro h b
      rw [ih, BlockSlots.comp_finToSlots_succ]
      exact h (b default)
  | iSup φs ih => exact exists_congr fun i ↦ ih i ys
  | iInf φs ih => exact forall_congr' fun i ↦ ih i ys

end BlockFormula

end FirstOrder.Language
