/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.LinfKappa.Semantics

/-!
# Renaming and substitution of slots in block formulas

* `BlockFormula.mapSlots`: renaming along a slot map `BlockSlots V Γ → BlockSlots V Δ`.  Under a
  block binder the map is lifted by `Sum.map id ρ`, definitionally.  `realize_mapSlots`,
  `mapSlots_id`, `mapSlots_mapSlots`.
* `BlockFormula.substSlots`: simultaneous substitution of terms for slots, under nested block
  binders (the substitution is lifted by `BlockFormula.liftSubst`), with `realize_substSlots`.
* `realize_reassoc`: renaming along the three-way reassociation `BlockSlots.reassocEquiv`, so that
  reassociating a context needs no cast on formulas.  Its component and inverse equations
  (`BlockSlots.reassocEquiv_left` and its siblings, in `LinfKappa/Syntax.lean`) show that the map
  is the intended reassociation.

The binder case of `realize_mapSlots` rewrites with the induction hypothesis at the lifted
renaming `Sum.map id ρ` and the slot valuation `Sum.elim b ys`; that `rw` goes through only
because `BlockSlots` is reducible (see `LinfKappa/Syntax.lean`).  `mapSlots_id`,
`mapSlots_mapSlots` and `realize_substSlots` also fail for a semireducible `BlockSlots`.  The
binder case of `realize_substSlots` chains the induction hypothesis with `Iff.trans` rather than
rewriting with it: there `rw [ih]` is rejected ("expected an equality or iff proof") for a reason
unrelated to transparency, even with reducible slots, while `Iff.trans` (or `simp only [ih]`)
works.

## Non-claims

Free-variable substitution, language maps and carrier reindexing are not provided here.
-/

set_option autoImplicit false

namespace FirstOrder.Language

namespace BlockFormula

/-- Renaming of slots along `ρ`; under a block binder the map is lifted by `Sum.map id ρ`. -/
def mapSlots.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} : ∀ {Γ : List Q}, L.BlockFormula ι V α Γ → ∀ {Δ : List Q},
    (BlockSlots V Γ → BlockSlots V Δ) → L.BlockFormula ι V α Δ
  | _, .falsum, _, _ => .falsum
  | _, .equal t₁ t₂, _, ρ => .equal (t₁.relabel (Sum.map id ρ)) (t₂.relabel (Sum.map id ρ))
  | _, .rel R ts, _, ρ => .rel R fun i ↦ (ts i).relabel (Sum.map id ρ)
  | _, .imp φ ψ, _, ρ => (φ.mapSlots ρ).imp (ψ.mapSlots ρ)
  | _, .allBlock q φ, _, ρ => .allBlock q (φ.mapSlots (Sum.map id ρ))
  | _, .iSup φs, _, ρ => .iSup fun i ↦ (φs i).mapSlots ρ
  | _, .iInf φs, _, ρ => .iInf fun i ↦ (φs i).mapSlots ρ

/-- Renaming slots along `ρ` is precomposition of the slot valuation with `ρ`. -/
theorem realize_mapSlots.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M]
    {Γ Δ : List Q} (φ : L.BlockFormula ι V α Γ) (ρ : BlockSlots V Γ → BlockSlots V Δ)
    (v : α → M) (ys : BlockSlots V Δ → M) :
    (φ.mapSlots ρ).Realize v ys ↔ φ.Realize v (ys ∘ ρ) := by
  induction φ generalizing Δ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [mapSlots, realize_equal, Term.realize_relabel]
    rw [Sum.elim_comp_map]; rfl
  | rel R ts =>
    simp only [mapSlots, realize_rel, Term.realize_relabel]
    rw [Sum.elim_comp_map]; rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ ρ ys) (ihψ ρ ys)
  | allBlock q φ ih =>
    refine forall_congr' fun b ↦ ?_
    rw [ih]; rw [Sum.elim_comp_map]; rfl
  | iSup φs ih => exact exists_congr fun i ↦ ih i ρ ys
  | iInf φs ih => exact forall_congr' fun i ↦ ih i ρ ys

/-- Renaming along the identity does nothing. -/
@[simp]
theorem mapSlots_id.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {Γ : List Q} (φ : L.BlockFormula ι V α Γ) :
    φ.mapSlots id = φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [mapSlots, Sum.map_id_id, Term.relabel_id]
  | rel R ts => simp [mapSlots, Sum.map_id_id, Term.relabel_id]
  | imp φ ψ ihφ ihψ => simp [mapSlots, ihφ, ihψ]
  | allBlock q φ ih => simp only [mapSlots, Sum.map_id_id, ih]
  | iSup φs ih => simp [mapSlots, ih]
  | iInf φs ih => simp [mapSlots, ih]

/-- Renamings compose. -/
@[simp]
theorem mapSlots_mapSlots.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {Γ Δ Ε : List Q} (φ : L.BlockFormula ι V α Γ)
    (ρ : BlockSlots V Γ → BlockSlots V Δ) (ρ' : BlockSlots V Δ → BlockSlots V Ε) :
    (φ.mapSlots ρ).mapSlots ρ' = φ.mapSlots (ρ' ∘ ρ) := by
  induction φ generalizing Δ Ε with
  | falsum => rfl
  | equal t₁ t₂ => simp [mapSlots, Term.relabel_relabel, Sum.map_comp_map]
  | rel R ts => simp [mapSlots, Term.relabel_relabel, Sum.map_comp_map]
  | imp φ ψ ihφ ihψ => simp [mapSlots, ihφ, ihψ]
  | allBlock q φ ih => simp only [mapSlots, ih, Sum.map_comp_map, Function.id_comp]
  | iSup φs ih => simp [mapSlots, ih]
  | iInf φs ih => simp [mapSlots, ih]

/-- Lifting a slot substitution under one more block: the new head block is kept, and the old
terms are shifted past it. -/
def liftSubst.{u, v, uQ, w, u'} {L : Language.{u, v}} {Q : Type uQ} {V : Q → Type w}
    {α : Type u'} {Γ Δ : List Q} (q : Q) (σ : BlockSlots V Γ → L.Term (α ⊕ BlockSlots V Δ)) :
    BlockSlots V (q :: Γ) → L.Term (α ⊕ BlockSlots V (q :: Δ)) :=
  Sum.elim (fun x ↦ Term.var (Sum.inr (Sum.inl x)))
    (fun s ↦ (σ s).relabel (Sum.map id Sum.inr))

/-- Simultaneous substitution of terms for slots, under nested block binders. -/
def substSlots.{u, v, uι, uQ, w, u'} {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} : ∀ {Γ : List Q}, L.BlockFormula ι V α Γ → ∀ {Δ : List Q},
    (BlockSlots V Γ → L.Term (α ⊕ BlockSlots V Δ)) → L.BlockFormula ι V α Δ
  | _, .falsum, _, _ => .falsum
  | _, .equal t₁ t₂, _, σ => .equal (t₁.subst (Sum.elim (fun a ↦ Term.var (Sum.inl a)) σ))
      (t₂.subst (Sum.elim (fun a ↦ Term.var (Sum.inl a)) σ))
  | _, .rel R ts, _, σ =>
      .rel R fun i ↦ (ts i).subst (Sum.elim (fun a ↦ Term.var (Sum.inl a)) σ)
  | _, .imp φ ψ, _, σ => (φ.substSlots σ).imp (ψ.substSlots σ)
  | _, .allBlock q φ, _, σ => .allBlock q (φ.substSlots (liftSubst q σ))
  | _, .iSup φs, _, σ => .iSup fun i ↦ (φs i).substSlots σ
  | _, .iInf φs, _, σ => .iInf fun i ↦ (φs i).substSlots σ

/-- Substituting `σ` for the slots is evaluating the slots by `σ`. -/
theorem realize_substSlots.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M]
    {Γ Δ : List Q} (φ : L.BlockFormula ι V α Γ)
    (σ : BlockSlots V Γ → L.Term (α ⊕ BlockSlots V Δ)) (v : α → M) (ys : BlockSlots V Δ → M) :
    (φ.substSlots σ).Realize v ys ↔ φ.Realize v (fun s ↦ (σ s).realize (Sum.elim v ys)) := by
  have key : ∀ {Γ Δ : List Q} (σ : BlockSlots V Γ → L.Term (α ⊕ BlockSlots V Δ))
      (ys : BlockSlots V Δ → M),
      (fun t : α ⊕ BlockSlots V Γ ↦
        (Sum.elim (fun a ↦ Term.var (Sum.inl a)) σ t : L.Term (α ⊕ BlockSlots V Δ)).realize
          (Sum.elim v ys)) = Sum.elim v (fun s ↦ (σ s).realize (Sum.elim v ys)) := by
    intros; funext t; rcases t with a | s <;> rfl
  induction φ generalizing Δ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [substSlots, realize_equal, Term.realize_subst]; rw [key]
  | rel R ts =>
    simp only [substSlots, realize_rel, Term.realize_subst]; rw [key]
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ σ ys) (ihψ σ ys)
  | allBlock q φ ih =>
    refine forall_congr' fun b ↦ (ih _ _).trans ?_
    have : (fun s ↦ (liftSubst q σ s).realize (Sum.elim v (Sum.elim b ys)))
        = Sum.elim b (fun s ↦ (σ s).realize (Sum.elim v ys)) := by
      funext s
      rcases s with x | s
      · rfl
      · simp only [liftSubst, Sum.elim_inr, Term.realize_relabel]
        congr 1; funext t; rcases t with a | s' <;> rfl
    rw [this]
  | iSup φs ih => exact exists_congr fun i ↦ ih i σ ys
  | iInf φs ih => exact forall_congr' fun i ↦ ih i σ ys

/-- Reassociating the context `Γ ++ (Δ ++ Ε)` to `(Γ ++ Δ) ++ Ε` by renaming along
`BlockSlots.reassocEquiv`: no cast on formulas. -/
theorem realize_reassoc.{u, v, uι, uQ, w, u', wM} {L : Language.{u, v}} {ι : Type uι}
    {Q : Type uQ} {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M]
    {Γ Δ Ε : List Q} (φ : L.BlockFormula ι V α (Γ ++ (Δ ++ Ε))) (v : α → M)
    (ys : BlockSlots V ((Γ ++ Δ) ++ Ε) → M) :
    (φ.mapSlots (BlockSlots.reassocEquiv V Γ Δ Ε)).Realize v ys ↔
      φ.Realize v (ys ∘ BlockSlots.reassocEquiv V Γ Δ Ε) :=
  realize_mapSlots φ _ v ys

end BlockFormula

end FirstOrder.Language
