/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberAssembly
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Isomorphism assembly and restriction for row assemblies

Over arbitrary row types and fiber families.  Throughout, `R, S` are row types,
`C : R → Label U → Type`, `D : S → Label U → Type` are fiber families with `Lc`-structures on
every fiber, and the assembled structures are `Carrier R C`, `Carrier S D`
(`ModelTheory/FiberAssembly.lean`).

1. **Exact interpretation on canonical fiber points** (`relMap_lift_pt`, `relMap_own_pt`,
   `relMap_lab_pt`, `relMap_lift0_row`): the lifted symbols evaluated on points of one fiber
   are exactly the component relations there.  Uses only injectivity of the constructors.
2. **Assembly** (`assemble`): a bijection of rows `e : R ≃ S` together with component
   isomorphisms `f r τ : C r τ ≃[Lc] D (e r) τ` for every row and label induces an
   isomorphism `Carrier R C ≃[lang U Lc] Carrier S D`, sending `row r ↦ row (e r)` and
   `pt r τ x ↦ pt (e r) τ (f r τ x)`.  No relationality of `Lc`, no inhabited fibers, and no
   order-preservation of `e` are assumed: the supplied component isomorphisms carry the
   component nullary facts through `map_rel` at arity `0`.
3. **Restriction**: an arbitrary assembled isomorphism `g` sends rows to rows
   (`restrictRows g : R ≃ S`) and the fiber `(r, τ)` onto the fiber `(restrictRows g r, τ)`;
   nullary facts restrict with no fiber point required (`restrict_lift0`).  Neither of these
   needs relationality.  The restriction `restrictFiber g r τ : C r τ ≃[Lc] D (restrictRows g r) τ`
   to a component isomorphism requires `[Lc.IsRelational]`, because the assembly encodes only
   relation symbols; it too needs no fiber point.
4. **Compatibility equations**: `assemble_row`, `assemble_pt` (definitional),
   `restrictRows_apply`, `restrictFiber_apply`, `restrictRows_assemble`, and
   `restrictFiber_assemble_pt`: restricting the assembled isomorphism returns the supplied
   component isomorphism, as an equality of the images in the carrier.

Full-profile bounds, companions, and effective presentations are outside this module.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} {Lc : Language.{v, w}}

/-! ### Constructor injectivity, packaged -/

theorem Carrier.pt_inj {R : Type u} {C : R → Label U → Type u} {r r' : R} {τ τ' : Label U}
    {x : C r τ} {x' : C r' τ'} (h : Carrier.pt r τ x = Carrier.pt r' τ' x') :
    r = r' ∧ τ = τ' ∧ HEq x x' := by
  cases h
  exact ⟨rfl, rfl, HEq.rfl⟩

theorem Carrier.pt_inj_same {R : Type u} {C : R → Label U → Type u} {r : R} {τ : Label U}
    {x x' : C r τ} (h : Carrier.pt r τ x = Carrier.pt r τ x') : x = x' := by
  cases h
  rfl

/-! ### Exact interpretation on canonical fiber points -/

section Exact

variable {R : Type u} {C : R → Label U → Type u} [∀ r τ, Lc.Structure (C r τ)]

/-- A lifted relation on points of one fiber is the component relation there. -/
theorem relMap_lift_pt {l : ℕ} (S : Lc.Relations (l + 1)) (r : R) (τ : Label U)
    (y : Fin (l + 1) → C r τ) :
    Structure.RelMap (L := lang U Lc) (Sym.lift S) (fun i => (Carrier.pt r τ (y i) : Carrier R C))
      ↔ Structure.RelMap S y := by
  constructor
  · rintro ⟨r', τ', y', hy, hS⟩
    obtain ⟨rfl, rfl, -⟩ := Carrier.pt_inj (hy 0)
    have : y' = y := funext fun i => (Carrier.pt_inj_same (hy i)).symm
    subst this
    exact hS
  · intro h
    exact ⟨r, τ, y, fun _ => rfl, h⟩

/-- `own` on a fiber point and a row: the row is the owner. -/
theorem relMap_own_pt (r r' : R) (τ : Label U) (x : C r τ) :
    Structure.RelMap (L := lang U Lc) Sym.own
      ![(Carrier.pt r τ x : Carrier R C), Carrier.row r'] ↔ r' = r := by
  constructor
  · rintro ⟨q, τ', x', h1, h2⟩
    obtain ⟨rfl, -, -⟩ := Carrier.pt_inj h1
    cases h2
    rfl
  · intro h
    subst h
    exact ⟨r', τ, x, rfl, rfl⟩

/-- `lab τ'` on a fiber point with label `τ`: the labels agree. -/
theorem relMap_lab_pt (τ' : Label U) (r : R) (τ : Label U) (x : C r τ) :
    Structure.RelMap (L := lang U Lc) (Sym.lab τ') ![(Carrier.pt r τ x : Carrier R C)] ↔
      τ' = τ := by
  constructor
  · rintro ⟨q, x', h⟩
    obtain ⟨-, rfl, -⟩ := Carrier.pt_inj h
    rfl
  · rintro rfl
    exact ⟨r, x, rfl⟩

/-- `row` holds of every row and of no fiber point. -/
theorem relMap_row_row (r : R) :
    Structure.RelMap (L := lang U Lc) Sym.row ![(Carrier.row r : Carrier R C)] :=
  ⟨r, rfl⟩

theorem not_relMap_row_pt (r : R) (τ : Label U) (x : C r τ) :
    ¬ Structure.RelMap (L := lang U Lc) Sym.row ![(Carrier.pt r τ x : Carrier R C)] := by
  rintro ⟨q, h⟩
  cases h

end Exact

/-! ### Assembly -/

section Assemble

variable {R S : Type u} {C : R → Label U → Type u} {D : S → Label U → Type u}
  [∀ r τ, Lc.Structure (C r τ)] [∀ s τ, Lc.Structure (D s τ)]

/-- The underlying map of the assembled isomorphism. -/
private def assembleFun (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) : Carrier R C → Carrier S D
  | Carrier.row r => Carrier.row (e r)
  | Carrier.pt r τ x => Carrier.pt (e r) τ (f r τ x)

private theorem assembleFun_injective (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) :
    Function.Injective (assembleFun e f) := by
  intro a b h
  cases a <;> cases b <;> simp only [assembleFun] at h
  · rw [e.injective (Carrier.row.inj h)]
  · cases h
  · cases h
  · rename_i r τ x r' τ' x'
    obtain ⟨hr, rfl, hx⟩ := Carrier.pt_inj h
    have hr' : r = r' := e.injective hr
    subst hr'
    rw [(f r τ).injective (eq_of_heq hx)]

private theorem assembleFun_surjective (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) :
    Function.Surjective (assembleFun e f) := by
  rintro (s | ⟨s, τ, y⟩)
  · obtain ⟨r, rfl⟩ := e.surjective s
    exact ⟨Carrier.row r, rfl⟩
  · obtain ⟨r, rfl⟩ := e.surjective s
    refine ⟨Carrier.pt r τ ((f r τ).symm y), ?_⟩
    simp [assembleFun]

/-- Every point of the assembled image is a fiber point of the image row, with the component
element transported by `f`. -/
private theorem assembleFun_eq_pt {e : R ≃ S} {f : ∀ r τ, C r τ ≃[Lc] D (e r) τ}
    {a : Carrier R C} {r : R} {τ : Label U} {y : D (e r) τ}
    (h : assembleFun e f a = Carrier.pt (e r) τ y) :
    ∃ x : C r τ, a = Carrier.pt r τ x ∧ f r τ x = y := by
  cases a with
  | row r₀ => simp [assembleFun] at h
  | pt r₀ τ₀ x₀ =>
    simp only [assembleFun] at h
    obtain ⟨hr, rfl, hx⟩ := Carrier.pt_inj h
    have hr' : r₀ = r := e.injective hr
    subst hr'
    exact ⟨x₀, rfl, eq_of_heq hx⟩

/-- **Assembly of an isomorphism** from a row bijection and component isomorphisms.  No
relationality, no inhabited fibers, no order-preservation. -/
noncomputable def assemble (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) :
    Carrier R C ≃[lang U Lc] Carrier S D where
  toEquiv := Equiv.ofBijective (assembleFun e f)
    ⟨assembleFun_injective e f, assembleFun_surjective e f⟩
  map_fun' := fun {n} F _ => (F : PEmpty).elim
  map_rel' := by
    intro n Sy v
    change Structure.RelMap (L := lang U Lc) Sy (assembleFun e f ∘ v) ↔
      Structure.RelMap (L := lang U Lc) Sy v
    cases Sy with
    | row =>
      constructor
      · rintro ⟨s, hs⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        cases hv : v 0 with
        | row r₀ => exact ⟨r₀, hv⟩
        | pt r₀ τ₀ x₀ =>
          have := hs
          simp only [Function.comp, hv, assembleFun] at this
          cases this
      · rintro ⟨r, hr⟩
        exact ⟨e r, by simp [Function.comp, hr, assembleFun]⟩
    | own =>
      constructor
      · rintro ⟨s, τ, y, h0, h1⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        obtain ⟨x, hx, -⟩ := assembleFun_eq_pt h0
        refine ⟨r, τ, x, hx, ?_⟩
        cases hv : v 1 with
        | row r₁ =>
          have := h1
          simp only [Function.comp, hv, assembleFun] at this
          exact congrArg Carrier.row (e.injective (Carrier.row.inj this))
        | pt r₁ τ₁ x₁ =>
          have := h1
          simp only [Function.comp, hv, assembleFun] at this
          cases this
      · rintro ⟨r, τ, x, h0, h1⟩
        exact ⟨e r, τ, f r τ x, by simp [Function.comp, h0, assembleFun],
          by simp [Function.comp, h1, assembleFun]⟩
    | lab τ =>
      constructor
      · rintro ⟨s, y, h⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        obtain ⟨x, hx, -⟩ := assembleFun_eq_pt h
        exact ⟨r, x, hx⟩
      · rintro ⟨r, x, h⟩
        exact ⟨e r, f r τ x, by simp [Function.comp, h, assembleFun]⟩
    | lift Sy =>
      constructor
      · rintro ⟨s, τ, y', hy, hS⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        have hi : ∀ i, ∃ x : C r τ, v i = Carrier.pt r τ x ∧ f r τ x = y' i := fun i =>
          assembleFun_eq_pt (hy i)
        choose y hy' using hi
        refine ⟨r, τ, y, fun i => (hy' i).1, ?_⟩
        have : y' = ⇑(f r τ) ∘ y := funext fun i => ((hy' i).2).symm
        subst this
        exact ((f r τ).map_rel Sy y).mp hS
      · rintro ⟨r, τ, y, hy, hS⟩
        refine ⟨e r, τ, ⇑(f r τ) ∘ y, fun i => by simp [Function.comp, hy i, assembleFun], ?_⟩
        exact ((f r τ).map_rel Sy y).mpr hS
    | lift0 Sy τ =>
      constructor
      · rintro ⟨s, hs, hS⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        cases hv : v 0 with
        | row r₀ =>
          have := hs
          simp only [Function.comp, hv, assembleFun] at this
          have hr : r₀ = r := e.injective (Carrier.row.inj this)
          subst hr
          refine ⟨r₀, hv, ?_⟩
          have hm := (f r₀ τ).map_rel Sy Fin.elim0
          rw [show ⇑(f r₀ τ) ∘ Fin.elim0 = Fin.elim0 from funext fun i => i.elim0] at hm
          exact hm.mp hS
        | pt r₀ τ₀ x₀ =>
          have := hs
          simp only [Function.comp, hv, assembleFun] at this
          cases this
      · rintro ⟨r, hr, hS⟩
        refine ⟨e r, by simp [Function.comp, hr, assembleFun], ?_⟩
        have hm := (f r τ).map_rel Sy Fin.elim0
        rw [show ⇑(f r τ) ∘ Fin.elim0 = Fin.elim0 from funext fun i => i.elim0] at hm
        exact hm.mpr hS

@[simp] theorem assemble_row (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) (r : R) :
    assemble e f (Carrier.row r) = Carrier.row (e r) := rfl

@[simp] theorem assemble_pt (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) (r : R)
    (τ : Label U) (x : C r τ) :
    assemble e f (Carrier.pt r τ x) = Carrier.pt (e r) τ (f r τ x) := rfl

end Assemble

/-! ### Restriction -/

section Restrict

variable {R S : Type u} {C : R → Label U → Type u} {D : S → Label U → Type u}
  [∀ r τ, Lc.Structure (C r τ)] [∀ s τ, Lc.Structure (D s τ)]

/-- An assembled isomorphism sends rows to rows. -/
private theorem exists_row_eq (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) :
    ∃ s, g (Carrier.row r) = Carrier.row s := by
  have h := (g.map_rel Sym.row ![Carrier.row r]).mpr (relMap_row_row r)
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by simpa [Function.comp] using hs⟩

/-- The row map of an assembled isomorphism. -/
private noncomputable def rowMap (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) : S :=
  (exists_row_eq g r).choose

private theorem rowMap_spec (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) :
    g (Carrier.row r) = Carrier.row (rowMap g r) :=
  (exists_row_eq g r).choose_spec

private theorem rowMap_symm_rowMap (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) :
    rowMap g.symm (rowMap g r) = r := by
  have h1 := rowMap_spec g r
  have h2 := rowMap_spec g.symm (rowMap g r)
  rw [← h1, g.symm_apply_apply] at h2
  exact (Carrier.row.inj h2).symm

/-- **Restriction to rows**: the row bijection of an assembled isomorphism. -/
noncomputable def restrictRows (g : Carrier R C ≃[lang U Lc] Carrier S D) : R ≃ S where
  toFun := rowMap g
  invFun := rowMap g.symm
  left_inv := rowMap_symm_rowMap g
  right_inv := fun s => by
    have := rowMap_symm_rowMap g.symm s
    simpa using this

@[simp] theorem restrictRows_apply (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) :
    g (Carrier.row r) = Carrier.row (restrictRows g r) :=
  rowMap_spec g r

/-- An assembled isomorphism sends the fiber `(r, τ)` into the fiber `(restrictRows g r, τ)`. -/
private theorem exists_pt_eq (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) (τ : Label U)
    (x : C r τ) : ∃ y : D (restrictRows g r) τ, g (Carrier.pt r τ x) = Carrier.pt _ τ y := by
  -- label preservation: the image is a fiber point with label `τ`
  have hlab := (g.map_rel (Sym.lab τ) ![Carrier.pt r τ x]).mpr
    ((relMap_lab_pt τ r τ x).mpr rfl)
  obtain ⟨s, y, hy⟩ := hlab
  simp only [Function.comp, Matrix.cons_val_zero] at hy
  -- ownership: the owner of the image is the image of the owner
  have hown := (g.map_rel Sym.own ![Carrier.pt r τ x, Carrier.row r]).mpr
    ((relMap_own_pt r r τ x).mpr rfl)
  have hown' : Structure.RelMap (L := lang U Lc) Sym.own
      ![(Carrier.pt s τ y : Carrier S D), Carrier.row (restrictRows g r)] := by
    have e2 : ⇑g ∘ ![Carrier.pt r τ x, Carrier.row r] =
        ![Carrier.pt s τ y, Carrier.row (restrictRows g r)] := by
      funext i
      fin_cases i
      · exact hy
      · exact restrictRows_apply g r
    rwa [e2] at hown
  have hs : restrictRows g r = s := (relMap_own_pt s (restrictRows g r) τ y).mp hown'
  subst hs
  exact ⟨y, hy⟩

/-- The fiber map of an assembled isomorphism. -/
private noncomputable def fiberMap (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) (τ : Label U)
    (x : C r τ) : D (restrictRows g r) τ :=
  (exists_pt_eq g r τ x).choose

private theorem fiberMap_spec (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) (τ : Label U)
    (x : C r τ) : g (Carrier.pt r τ x) = Carrier.pt (restrictRows g r) τ (fiberMap g r τ x) :=
  (exists_pt_eq g r τ x).choose_spec

private theorem fiberMap_injective (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R)
    (τ : Label U) :
    Function.Injective (fiberMap g r τ) := by
  intro x x' h
  have : g (Carrier.pt r τ x) = g (Carrier.pt r τ x') := by
    rw [fiberMap_spec g r τ x, fiberMap_spec g r τ x', h]
  exact Carrier.pt_inj_same (g.injective this)

private theorem fiberMap_surjective (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R)
    (τ : Label U) :
    Function.Surjective (fiberMap g r τ) := by
  intro y
  -- pull `y` back along `g`; the preimage is a fiber point of the row `r`, since
  -- `restrictRows g.symm (restrictRows g r) = r`
  have hrr : restrictRows g.symm (restrictRows g r) = r := rowMap_symm_rowMap g r
  obtain ⟨x', hx'⟩ := exists_pt_eq g.symm (restrictRows g r) τ y
  -- transport the preimage's row index along `hrr`
  revert x' hx'
  rw [hrr]
  intro x' hx'
  refine ⟨x', ?_⟩
  have h1 := fiberMap_spec g r τ x'
  rw [← hx', g.apply_symm_apply] at h1
  exact (Carrier.pt_inj_same h1).symm

/-- **Restriction to a labeled fiber**: the component isomorphism induced by an assembled
isomorphism.  This is the one construction needing `[Lc.IsRelational]`, because the assembly
encodes only relation symbols; no fiber point is required. -/
noncomputable def restrictFiber [Lc.IsRelational] (g : Carrier R C ≃[lang U Lc] Carrier S D)
    (r : R) (τ : Label U) : C r τ ≃[Lc] D (restrictRows g r) τ where
  toEquiv := Equiv.ofBijective (fiberMap g r τ)
    ⟨fiberMap_injective g r τ, fiberMap_surjective g r τ⟩
  map_fun' := fun {n} F _ => (IsEmpty.false F).elim
  map_rel' := by
    intro n Sy y
    change Structure.RelMap Sy (fiberMap g r τ ∘ y) ↔ Structure.RelMap Sy y
    cases n with
    | zero =>
      -- nullary facts restrict through the owner-indexed lift on the row
      have h := g.map_rel (Sym.lift0 Sy τ) ![Carrier.row r]
      have e1 : ⇑g ∘ ![(Carrier.row r : Carrier R C)] =
          fun _ : Fin 1 => (Carrier.row (restrictRows g r) : Carrier S D) := by
        funext i; fin_cases i; exact restrictRows_apply g r
      rw [e1, relMap_lift0_row] at h
      have h2 : Structure.RelMap (L := lang U Lc) (Sym.lift0 Sy τ)
          ![(Carrier.row r : Carrier R C)] ↔ Structure.RelMap Sy (Fin.elim0 : Fin 0 → C r τ) :=
        relMap_lift0_row Sy τ r
      rw [h2] at h
      rw [show fiberMap g r τ ∘ y = Fin.elim0 from funext fun i => i.elim0,
        show y = Fin.elim0 from funext fun i => i.elim0]
      exact h
    | succ l =>
      have h := g.map_rel (Sym.lift Sy) (fun i => (Carrier.pt r τ (y i) : Carrier R C))
      have e1 : ⇑g ∘ (fun i => (Carrier.pt r τ (y i) : Carrier R C)) =
          fun i => (Carrier.pt (restrictRows g r) τ (fiberMap g r τ (y i)) : Carrier S D) :=
        funext fun i => fiberMap_spec g r τ (y i)
      rw [e1, relMap_lift_pt, relMap_lift_pt] at h
      exact h

@[simp] theorem restrictFiber_apply [Lc.IsRelational] (g : Carrier R C ≃[lang U Lc] Carrier S D)
    (r : R) (τ : Label U) (x : C r τ) :
    g (Carrier.pt r τ x) = Carrier.pt (restrictRows g r) τ (restrictFiber g r τ x) :=
  fiberMap_spec g r τ x

/-- Nullary facts restrict along an assembled isomorphism, with no fiber point required. -/
theorem restrict_lift0 (g : Carrier R C ≃[lang U Lc] Carrier S D) (r : R) (τ : Label U)
    (Sy : Lc.Relations 0) :
    Structure.RelMap Sy (Fin.elim0 : Fin 0 → C r τ) ↔
      Structure.RelMap Sy (Fin.elim0 : Fin 0 → D (restrictRows g r) τ) := by
  have h := g.map_rel (Sym.lift0 Sy τ) ![Carrier.row r]
  have e1 : ⇑g ∘ ![(Carrier.row r : Carrier R C)] =
      fun _ : Fin 1 => (Carrier.row (restrictRows g r) : Carrier S D) := by
    funext i; fin_cases i; exact restrictRows_apply g r
  rw [e1, relMap_lift0_row] at h
  have h2 : Structure.RelMap (L := lang U Lc) (Sym.lift0 Sy τ)
      ![(Carrier.row r : Carrier R C)] ↔ Structure.RelMap Sy (Fin.elim0 : Fin 0 → C r τ) :=
    relMap_lift0_row Sy τ r
  rw [h2] at h
  exact h.symm

/-! ### Compatibility of restriction with assembly -/

theorem restrictRows_assemble (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) :
    restrictRows (assemble e f) = e := by
  ext r
  have h := restrictRows_apply (assemble e f) r
  rw [assemble_row] at h
  exact (Carrier.row.inj h).symm

/-- Restricting the assembled isomorphism returns the supplied component isomorphism: the two
images of a fiber point in the carrier are equal. -/
theorem restrictFiber_assemble_pt [Lc.IsRelational] (e : R ≃ S)
    (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) (r : R) (τ : Label U) (x : C r τ) :
    Carrier.pt (restrictRows (assemble e f) r) τ (restrictFiber (assemble e f) r τ x) =
      (Carrier.pt (e r) τ (f r τ x) : Carrier S D) := by
  rw [← restrictFiber_apply, assemble_pt]

end Restrict

end FiberAssembly

end FirstOrder.Language
