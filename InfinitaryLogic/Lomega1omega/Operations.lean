/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Util

/-!
# Operations on Lω₁ω Formulas

This file defines operations on Lω₁ω formulas including relabeling, casting, and substitution.

## Main Definitions

- `BoundedFormulaω.relabel`: Relabels free variables.
- `BoundedFormulaω.castLE`: Increases the number of bound variables.
- `BoundedFormulaω.subst`: Substitutes terms for free variables.
- `BoundedFormula.toLω`: Embeds first-order formulas into Lω₁ω.

## Implementation Notes

The operations here closely mirror those in `Linf/Operations.lean`. See that file's
implementation notes for discussion of the duplication.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α β : Type u'} {n m : ℕ}

open FirstOrder Structure Fin

/-- Maps the last variable of `Fin (n+1)` to a bound variable position,
keeping the first `n` as free variables. Used for quantifying over the last position.

This function is used by `openBounds` (for the `all` case) and by `existsLastVar`/`forallLastVar`
in `Scott/Formula.lean`. -/
def insertLastBound {n : ℕ} : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  fun i => if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr 0

namespace BoundedFormulaω

/-- Casts a bounded formula to one with more bound variables. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormulaω α m → L.BoundedFormulaω α n
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, rel R ts => rel R (fun i => (ts i).relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, imp φ ψ => (φ.castLE h).imp (ψ.castLE h)
  | _, _, h, all φ => (φ.castLE (Nat.succ_le_succ h)).all
  | _, _, h, iSup φs => iSup fun i => (φs i).castLE h
  | _, _, h, iInf φs => iInf fun i => (φs i).castLE h

/-- Relabeling a term by the identity function returns the same term. -/
theorem Term.relabel_id' {α : Type*} (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.relabel]
    congr 1
    funext i
    exact ih i

/-- `castLE (le_refl n)` is the identity on formulas. -/
theorem castLE_refl : (φ : L.BoundedFormulaω α n) → φ.castLE (le_refl n) = φ := by
  intro φ
  induction φ with
  | falsum => rfl
  | @equal m t₁ t₂ =>
    simp only [castLE]
    congr 1 <;> {
      have h : Sum.map id (Fin.castLE (le_refl m)) = (id : α ⊕ Fin m → α ⊕ Fin m) := by
        funext x; cases x <;> rfl
      rw [h, Term.relabel_id']
    }
  | @rel m l R ts =>
    simp only [castLE]
    congr 1
    funext i
    have h : Sum.map id (Fin.castLE (le_refl m)) = (id : α ⊕ Fin m → α ⊕ Fin m) := by
      funext x; cases x <;> rfl
    rw [h, Term.relabel_id']
  | imp φ ψ ih_φ ih_ψ =>
    simp only [castLE, ih_φ, ih_ψ]
  | all φ ih =>
    simp only [castLE, ih]
  | iSup φs ih =>
    simp only [castLE]
    congr 1
    funext i
    exact ih i
  | iInf φs ih =>
    simp only [castLE]
    congr 1
    funext i
    exact ih i

variable {M : Type*} [L.Structure M]

/-- `castLE` over a proof of `m ≤ m` preserves semantics.
This is more general than matching on `le_refl` directly, as it works for any
proof `h : m ≤ m` regardless of how it was constructed. -/
theorem realize_castLE_of_eq {m n : ℕ} (φ : L.BoundedFormulaω α m) (h : m ≤ n) (heq : m = n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast heq) := by
  subst heq
  have hcast : Fin.cast (Eq.refl m) = id := funext (fun i => rfl)
  simp only [hcast, Function.comp_id]
  have : h = le_refl m := rfl
  rw [this, castLE_refl]

/-- `castLE (le_refl n)` preserves semantics. -/
theorem realize_castLE_refl {n : ℕ} (φ : L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE (le_refl n)).Realize v xs ↔ φ.Realize v xs := by
  rw [castLE_refl]

/-- `castLE` over any proof `h : n ≤ n` preserves semantics.
This handles the case where the proof term is not definitionally `le_refl`
(e.g., constructed via rewriting or other means). -/
theorem realize_castLE_self {n : ℕ} (φ : L.BoundedFormulaω α n) (h : n ≤ n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v xs :=
  realize_castLE_of_eq φ h rfl v xs

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ Fin n) (k : ℕ) : α ⊕ Fin k → β ⊕ Fin (n + k) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

/-- Relabels a bounded formula's free variables. -/
def relabel (g : α → β ⊕ Fin n) : ∀ {k}, L.BoundedFormulaω α k → L.BoundedFormulaω β (n + k)
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal (t₁.relabel (relabelAux g _)) (t₂.relabel (relabelAux g _))
  | _, rel R ts => rel R fun i => (ts i).relabel (relabelAux g _)
  | _, imp φ ψ => (φ.relabel g).imp (ψ.relabel g)
  | k, all φ => (φ.relabel g).castLE (Nat.add_right_comm n k 1 ▸ le_refl _) |>.all
  | _, iSup φs => iSup fun i => (φs i).relabel g
  | _, iInf φs => iInf fun i => (φs i).relabel g

-- Note: The general realize_relabel lemma is complex due to castLE in the all case.
-- For Scott formulas, we only need specific lemmas for existsLastVar and forallLastVar,
-- which are proved directly in Scott/Formula.lean using a more targeted approach.
-- Below we prove realize_relabel for the specific case g = Sum.inr, needed for the C7 axioms.

/-- Helper: `Sum.elim Empty.elim xs ∘ relabelAux Sum.inr k` maps free variables to the
first bound positions and shifts existing bound variables.

Concretely, for `g = Sum.inr : Fin n → Empty ⊕ Fin n`:
- `Sum.inl (i : Fin n)` maps to `xs (Fin.castAdd k i)` (free var → first n bound positions)
- `Sum.inr (j : Fin k)` maps to `xs (Fin.natAdd n j)` (bound var → shifted positions) -/
private lemma sum_elim_relabelAux_sumInr {n k : ℕ} (xs : Fin (n + k) → M) :
    Sum.elim (Empty.elim : Empty → M) xs ∘ relabelAux (Sum.inr : Fin n → Empty ⊕ Fin n) k =
    Sum.elim (xs ∘ Fin.castAdd k) (xs ∘ Fin.natAdd n) := by
  funext x
  cases x with
  | inl i =>
    simp only [Function.comp_apply, relabelAux, Sum.map_inl, Sum.elim_inl]
    simp only [Equiv.sumAssoc_apply_inl_inr, Sum.map_inr, Sum.elim_inr]
    rfl
  | inr j =>
    simp only [Function.comp_apply, relabelAux, Sum.map_inr, Sum.elim_inr]
    simp only [Equiv.sumAssoc_apply_inr, Sum.map_inr, Sum.elim_inr]
    rfl

/-- Helper: snoc distributes over castAdd/natAdd for the all case. -/
private lemma snoc_comp_castAdd_natAdd {n k : ℕ} (xs : Fin (n + k) → M) (y : M) :
    (Fin.snoc xs y ∘ Fin.castAdd (k + 1)) = (xs ∘ Fin.castAdd k) := by
  funext i
  simp only [Function.comp_apply, Fin.snoc]
  -- For i : Fin n, castAdd (k+1) i has value i.val < n ≤ n + k
  have hlt : (Fin.castAdd (k + 1) i).val < n + k := by
    have hi : i.val < n := i.is_lt
    have cast_val : (Fin.castAdd (k + 1) i).val = i.val := rfl
    simp only [cast_val]
    omega
  -- Both sides apply xs to elements with the same value
  have eq_cast : (Fin.castAdd (k + 1) i).castLT hlt = Fin.castAdd k i := by
    ext
    simp only [Fin.castAdd]
    rfl
  simp only [hlt, dite_true, eq_cast]
  rfl

private lemma snoc_comp_natAdd_succ {n k : ℕ} (xs : Fin (n + k) → M) (y : M) :
    (Fin.snoc xs y ∘ Fin.natAdd n) = Fin.snoc (xs ∘ Fin.natAdd n) y := by
  funext j
  simp only [Function.comp_apply, Fin.snoc]
  by_cases hj : j.val = k
  · -- j is the last element, so natAdd n j has value n + k
    have hj_last : j = Fin.last k := by ext; exact hj
    subst hj_last
    simp only [Fin.natAdd, Fin.last]
    -- Both sides have condition that is false (can't have n+k < n+k or k < k) so return y
    have h1_false : ¬ n + k < n + k := by omega
    have h2_false : ¬ k < k := by omega
    simp only [h1_false, h2_false, dite_false]
  · -- j is not the last element, so natAdd n j has value n + j.val < n + k
    have hjlt : j.val < k := by omega
    have h1_lt : (Fin.natAdd n j).val < n + k := by
      simp only [Fin.natAdd]
      omega
    have h2_lt : j.val < k := hjlt
    simp only [h1_lt, h2_lt, dite_true]
    rfl

/-- Realize commutes with `relabel Sum.inr`: relabeling free variables `Fin n` into
bound positions via `Sum.inr` shifts them into the first `n` bound variable slots.

For `φ : L.BoundedFormulaω (Fin n) k`:
- The relabeled formula `φ.relabel Sum.inr` has type `L.BoundedFormulaω Empty (n + k)`
- Realizing with `Empty.elim` and `xs : Fin (n + k) → M` is equivalent to
  realizing the original formula with `xs ∘ Fin.castAdd k` for free variables
  and `xs ∘ Fin.natAdd n` for bound variables. -/
theorem realize_relabel_sumInr {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω (Fin n) k) (xs : Fin (n + k) → M),
    (φ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).Realize (Empty.elim : Empty → M) xs ↔
    φ.Realize (xs ∘ Fin.castAdd k) (xs ∘ Fin.natAdd n) := by
  intro k φ
  induction φ with
  | falsum => intro xs; simp [relabel, Realize]
  | equal t₁ t₂ =>
    intro xs
    simp only [relabel, realize_equal, Term.realize_relabel, sum_elim_relabelAux_sumInr]
  | rel R ts =>
    intro xs
    simp only [relabel, realize_rel]
    constructor <;> intro h <;> convert h using 1 <;> ext i <;>
      simp [Term.realize_relabel, sum_elim_relabelAux_sumInr]
  | imp φ ψ ih_φ ih_ψ =>
    intro xs; simp only [relabel, realize_imp]; exact Iff.imp (ih_φ xs) (ih_ψ xs)
  | all φ ih =>
    intro xs; simp only [relabel, realize_all]
    constructor <;> intro hall y
    · specialize hall y
      rw [realize_castLE_self] at hall
      rw [ih (Fin.snoc xs y)] at hall
      rw [snoc_comp_castAdd_natAdd, snoc_comp_natAdd_succ] at hall
      exact hall
    · rw [realize_castLE_self, ih (Fin.snoc xs y), snoc_comp_castAdd_natAdd, snoc_comp_natAdd_succ]
      exact hall y
  | iSup φs ih =>
    intro xs; simp only [relabel, realize_iSup]; exact exists_congr (fun i => ih i xs)
  | iInf φs ih =>
    intro xs; simp only [relabel, realize_iInf]; exact forall_congr' (fun i => ih i xs)

/-- Specialization of `realize_relabel_sumInr` for formulas (k = 0 bound variables).

For `φ : L.Formulaω (Fin n)` (a formula with n free variables and 0 bound variables):
- `φ.relabel Sum.inr : L.BoundedFormulaω Empty n` has 0 free vars and n bound vars
- Realizing the relabeled formula with bound assignment `xs : Fin n → M` is equivalent
  to realizing the original formula with free variable assignment `xs`. -/
theorem realize_relabel_sumInr_zero {n : ℕ} (φ : L.Formulaω (Fin n)) (xs : Fin n → M) :
    (φ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).Realize (Empty.elim : Empty → M) xs ↔
    Formulaω.Realize φ xs := by
  have h := realize_relabel_sumInr (k := 0) φ xs
  simp only [Formulaω.Realize] at h ⊢
  rw [h]
  have h1 : xs ∘ Fin.castAdd 0 = xs := by funext i; simp [Fin.castAdd]
  have h2 : (xs ∘ Fin.natAdd n : Fin 0 → M) = Fin.elim0 := Fin.eq_elim0 _
  rw [h1, h2]

/-- Substitutes the free variables in a bounded formula with terms. -/
def subst : ∀ {n : ℕ}, L.BoundedFormulaω α n → (α → L.Term β) → L.BoundedFormulaω β n
  | _, falsum, _ => falsum
  | _, equal t₁ t₂, tf =>
    equal (t₁.subst (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr)))
          (t₂.subst (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr)))
  | _, rel R ts, tf =>
    rel R fun i => (ts i).subst (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr))
  | _, imp φ ψ, tf => (φ.subst tf).imp (ψ.subst tf)
  | _, all φ, tf => (φ.subst tf).all
  | _, iSup φs, tf => iSup fun i => (φs i).subst tf
  | _, iInf φs, tf => iInf fun i => (φs i).subst tf

/-- Renames free variables in a bounded formula using a function f : α → β.

Unlike `relabel`, which can move free variables into bound positions, `mapFreeVars`
simply renames free variables while preserving the bound variable structure. -/
def mapFreeVars (f : α → β) : ∀ {n}, L.BoundedFormulaω α n → L.BoundedFormulaω β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map f id)) (t₂.relabel (Sum.map f id))
  | _, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map f id))
  | _, .imp φ ψ => .imp (φ.mapFreeVars f) (ψ.mapFreeVars f)
  | _, .all φ => .all (φ.mapFreeVars f)
  | _, .iSup φs => .iSup (fun k => (φs k).mapFreeVars f)
  | _, .iInf φs => .iInf (fun k => (φs k).mapFreeVars f)

private theorem sum_elim_comp_sum_map (f : α → β) (v : β → M) (xs : Fin n → M) :
    Sum.elim v xs ∘ Sum.map f id = Sum.elim (v ∘ f) xs := by
  funext x; cases x <;> rfl

/-- Realization commutes with free variable renaming. -/
theorem realize_mapFreeVars {M : Type*} [L.Structure M]
    (f : α → β) (φ : L.BoundedFormulaω α n) (v : β → M) (xs : Fin n → M) :
    (φ.mapFreeVars f).Realize v xs ↔ φ.Realize (v ∘ f) xs := by
  induction φ with
  | falsum => simp [mapFreeVars, Realize]
  | equal t₁ t₂ =>
    simp only [mapFreeVars, realize_equal, Term.realize_relabel, sum_elim_comp_sum_map]
  | rel R ts =>
    simp only [mapFreeVars, realize_rel]
    constructor <;> intro h <;> convert h using 1 <;> ext i <;>
      simp [Term.realize_relabel, sum_elim_comp_sum_map]
  | imp φ ψ ihφ ihψ =>
    simp only [mapFreeVars, realize_imp, ihφ xs, ihψ xs]
  | all φ ih =>
    simp only [mapFreeVars, realize_all]
    exact forall_congr' fun x => ih (Fin.snoc xs x)
  | iSup φs ih =>
    simp only [mapFreeVars, realize_iSup]
    exact exists_congr fun k => ih k xs
  | iInf φs ih =>
    simp only [mapFreeVars, realize_iInf]
    exact forall_congr' fun k => ih k xs

private theorem sum_elim_subst_tf {M : Type*} [L.Structure M]
    (tf : α → L.Term β) (v : β → M) (xs : Fin n → M) :
    (fun a : α ⊕ Fin n =>
      ((Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr) a).realize
        (Sum.elim v xs))) =
    Sum.elim (fun a => (tf a).realize v) xs := by
  funext x
  rcases x with a | j
  · simp [Term.realize_relabel, Sum.elim_comp_inl]
  · simp

/-- Realization commutes with free variable substitution.

This is the Lω₁ω analogue of Mathlib's `BoundedFormula.realize_subst`. -/
@[simp]
theorem realize_subst {M : Type*} [L.Structure M]
    (tf : α → L.Term β) (φ : L.BoundedFormulaω α n) (v : β → M) (xs : Fin n → M) :
    (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).realize v) xs := by
  induction φ with
  | falsum => simp [subst, Realize]
  | equal t₁ t₂ =>
    simp only [subst, realize_equal, Term.realize_subst, sum_elim_subst_tf]
  | rel R ts =>
    simp only [subst, realize_rel]
    constructor <;> intro h <;> convert h using 1 <;> ext i <;>
      simp [Term.realize_subst, sum_elim_subst_tf]
  | imp φ ψ ihφ ihψ =>
    simp only [subst, realize_imp, ihφ xs, ihψ xs]
  | all φ ih =>
    simp only [subst, realize_all]
    exact forall_congr' fun x => ih (Fin.snoc xs x)
  | iSup φs ih =>
    simp only [subst, realize_iSup]
    exact exists_congr fun k => ih k xs
  | iInf φs ih =>
    simp only [subst, realize_iInf]
    exact forall_congr' fun k => ih k xs

/-- Convert a `BoundedFormulaω Empty n` to a `Formulaω (Fin n)` by reinterpreting
bound variables as free variables. Since there are no free variables (`Empty`),
the bound variables `Fin n` become the only variables, now treated as free.

For the `all` case, the last free variable is re-bound using `relabel` with
`insertLastBound`. -/
def openBounds : ∀ {n : ℕ}, L.BoundedFormulaω Empty n → L.Formulaω (Fin n)
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ =>
    .equal (t₁.relabel (Sum.elim Empty.elim Sum.inl))
           (t₂.relabel (Sum.elim Empty.elim Sum.inl))
  | _, .rel R ts =>
    .rel R (fun i => (ts i).relabel (Sum.elim Empty.elim Sum.inl))
  | _, .imp φ ψ => (openBounds φ).imp (openBounds ψ)
  | _, .all φ => ((openBounds φ).relabel insertLastBound).all
  | _, .iSup φs => .iSup (fun i => openBounds (φs i))
  | _, .iInf φs => .iInf (fun i => openBounds (φs i))

/-! ### Language Maps -/

/-- Lifts a bounded Lω₁ω formula along a language homomorphism `L →ᴸ L'`.

This maps function and relation symbols in the formula using the language homomorphism,
while preserving the variable structure. It is the Lω₁ω analogue of Mathlib's
`LHom.onBoundedFormula`. -/
def mapLanguage {L' : Language.{u, v}} (g : L →ᴸ L') :
    ∀ {n}, L.BoundedFormulaω α n → L'.BoundedFormulaω α n
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal (g.onTerm t₁) (g.onTerm t₂)
  | _, rel R ts => rel (g.onRelation R) (fun i => g.onTerm (ts i))
  | _, imp φ ψ => (φ.mapLanguage g).imp (ψ.mapLanguage g)
  | _, all φ => (φ.mapLanguage g).all
  | _, iSup φs => iSup fun i => (φs i).mapLanguage g
  | _, iInf φs => iInf fun i => (φs i).mapLanguage g

/-- Realization of a formula is preserved by language homomorphisms that are expansions.

If `g : L →ᴸ L'` is an expansion on `M` (i.e., `g` maps symbols to the corresponding
symbols in `M`'s `L'`-structure), then `(φ.mapLanguage g).Realize v xs ↔ φ.Realize v xs`
where the left side uses the `L'`-structure and the right side uses the `L`-structure. -/
theorem realize_mapLanguage {L' : Language.{u, v}} (g : L →ᴸ L')
    {M : Type*} [L.Structure M] [L'.Structure M] [g.IsExpansionOn M]
    (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    (φ.mapLanguage g).Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [mapLanguage, realize_equal, LHom.realize_onTerm]
  | rel R ts =>
    simp only [mapLanguage, realize_rel, LHom.map_onRelation, LHom.realize_onTerm]
  | imp φ ψ ihφ ihψ =>
    simp only [mapLanguage, realize_imp, ihφ xs, ihψ xs]
  | all φ ih =>
    simp only [mapLanguage, realize_all]
    exact forall_congr' fun x => ih (Fin.snoc xs x)
  | iSup φs ih =>
    simp only [mapLanguage, realize_iSup]
    exact exists_congr fun k => ih k xs
  | iInf φs ih =>
    simp only [mapLanguage, realize_iInf]
    exact forall_congr' fun k => ih k xs

/-- `mapLanguage` commutes with `not`. -/
@[simp]
theorem mapLanguage_not {L' : Language.{u, v}} (g : L →ᴸ L') (φ : L.BoundedFormulaω α n) :
    (φ.not).mapLanguage g = (φ.mapLanguage g).not := by
  show (φ.imp falsum).mapLanguage g = (φ.mapLanguage g).imp falsum
  rfl

/-- `mapLanguage` commutes with `imp`. -/
@[simp]
theorem mapLanguage_imp {L' : Language.{u, v}} (g : L →ᴸ L')
    (φ ψ : L.BoundedFormulaω α n) :
    (φ.imp ψ).mapLanguage g = (φ.mapLanguage g).imp (ψ.mapLanguage g) := by
  simp only [mapLanguage]

/-- `mapLanguage` commutes with `ex`. -/
@[simp]
theorem mapLanguage_ex {L' : Language.{u, v}} (g : L →ᴸ L')
    (φ : L.BoundedFormulaω α (n + 1)) :
    (φ.ex).mapLanguage g = (φ.mapLanguage g).ex := by
  show (φ.not.all.not).mapLanguage g = (φ.mapLanguage g).not.all.not
  rw [mapLanguage_not, mapLanguage, mapLanguage_not]

/-- `LHom.onTerm` commutes with `Term.relabel`. -/
theorem LHom.onTerm_relabel {L' : Language.{u, v}} (g : L →ᴸ L')
    {γ δ : Type*} (f : γ → δ) (t : L.Term γ) :
    g.onTerm (t.relabel f) = (g.onTerm t).relabel f := by
  induction t with
  | var => simp [Term.relabel, LHom.onTerm]
  | func fn ts ih =>
    simp only [Term.relabel, LHom.onTerm]
    congr 1; funext i; exact ih i

/-- `LHom.onTerm` commutes with `Term.subst`. -/
theorem LHom.onTerm_subst {L' : Language.{u, v}} (g : L →ᴸ L')
    {γ δ : Type*} (tf : γ → L.Term δ) (t : L.Term γ) :
    g.onTerm (t.subst tf) = (g.onTerm t).subst (fun a => g.onTerm (tf a)) := by
  induction t with
  | var => simp [Term.subst, LHom.onTerm]
  | func fn ts ih =>
    simp only [Term.subst, LHom.onTerm]
    congr 1; funext i; exact ih i

/-- `mapLanguage` commutes with `castLE`. -/
theorem mapLanguage_castLE {L' : Language.{u, v}} (g : L →ᴸ L')
    (h : m ≤ n) (φ : L.BoundedFormulaω α m) :
    (φ.castLE h).mapLanguage g = (φ.mapLanguage g).castLE h := by
  induction φ generalizing n with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [castLE, mapLanguage, LHom.onTerm_relabel]
  | rel R ts =>
    simp only [castLE, mapLanguage]
    congr 1; funext i; exact LHom.onTerm_relabel g _ (ts i)
  | imp _ _ ih₁ ih₂ => simp only [castLE, mapLanguage, ih₁ h, ih₂ h]
  | all _ ih =>
    simp only [castLE, mapLanguage, ih (Nat.succ_le_succ h)]
  | iSup _ ih => simp only [castLE, mapLanguage]; congr 1; funext i; exact ih i h
  | iInf _ ih => simp only [castLE, mapLanguage]; congr 1; funext i; exact ih i h

/-- `mapLanguage` commutes with `relabel`. -/
theorem mapLanguage_relabel {L' : Language.{u, v}} (g : L →ᴸ L')
    {γ : Type u'} (f : α → γ ⊕ Fin n) (φ : L.BoundedFormulaω α m) :
    (φ.relabel f).mapLanguage g = (φ.mapLanguage g).relabel f := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormulaω.relabel, mapLanguage, LHom.onTerm_relabel]
  | rel R ts =>
    simp only [BoundedFormulaω.relabel, mapLanguage]
    congr 1; funext i; exact LHom.onTerm_relabel g _ (ts i)
  | imp _ _ ih₁ ih₂ => simp only [BoundedFormulaω.relabel, mapLanguage, ih₁, ih₂]
  | all _ ih =>
    simp only [BoundedFormulaω.relabel, mapLanguage]
    rw [mapLanguage_castLE, ih]
  | iSup _ ih => simp only [BoundedFormulaω.relabel, mapLanguage]; congr 1; funext i; exact ih i
  | iInf _ ih => simp only [BoundedFormulaω.relabel, mapLanguage]; congr 1; funext i; exact ih i

/-- `mapLanguage` commutes with `subst`. -/
theorem mapLanguage_subst {L' : Language.{u, v}} (g : L →ᴸ L')
    (tf : α → L.Term β) (φ : L.BoundedFormulaω α n) :
    (φ.subst tf).mapLanguage g = (φ.mapLanguage g).subst (fun a => g.onTerm (tf a)) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [subst, mapLanguage, LHom.onTerm_subst]
    congr 1 <;> congr 1 <;> funext x <;> cases x with
    | inl a => simp [LHom.onTerm_relabel]
    | inr j => simp [LHom.onTerm]
  | rel R ts =>
    simp only [subst, mapLanguage]
    congr 1; funext i
    rw [LHom.onTerm_subst]
    congr 1; funext x; cases x with
    | inl a => simp [LHom.onTerm_relabel]
    | inr j => simp [LHom.onTerm]
  | imp _ _ ih₁ ih₂ => simp only [subst, mapLanguage, ih₁, ih₂]
  | all _ ih => simp only [subst, mapLanguage, ih]
  | iSup _ ih => simp only [subst, mapLanguage]; congr 1; funext i; exact ih i
  | iInf _ ih => simp only [subst, mapLanguage]; congr 1; funext i; exact ih i

end BoundedFormulaω

namespace Formulaω

/-- Converts a formula with `Fin 0` free variables to a sentence (with `Empty` free variables).

Since both `Fin 0` and `Empty` are empty types, this is a purely type-theoretic conversion
that does not change the semantics of the formula. -/
def toSentenceω (φ : L.Formulaω (Fin 0)) : L.Sentenceω :=
  φ.mapFreeVars Fin.elim0

/-- `toSentenceω` preserves semantics: the sentence realizes in M iff the original
formula realizes with the `Fin.elim0` assignment. -/
theorem realize_toSentenceω {M : Type*} [L.Structure M]
    (φ : L.Formulaω (Fin 0)) :
    Sentenceω.Realize φ.toSentenceω M ↔ Formulaω.Realize φ (Fin.elim0 : Fin 0 → M) := by
  unfold toSentenceω Sentenceω.Realize Formulaω.Realize
  rw [BoundedFormulaω.realize_mapFreeVars]
  simp only [comp_fin_elim0]

end Formulaω

namespace BoundedFormula

/-- Embeds a first-order bounded formula into Lω₁ω. -/
def toLω : ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormulaω α n
  | _, falsum => BoundedFormulaω.falsum
  | _, equal t₁ t₂ => BoundedFormulaω.equal t₁ t₂
  | _, rel R ts => BoundedFormulaω.rel R ts
  | _, imp φ ψ => (φ.toLω).imp (ψ.toLω)
  | _, all φ => φ.toLω.all

variable {M : Type*} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_toLω (φ : L.BoundedFormula α n) :
    φ.toLω.Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih₁ ih₂ =>
    simp only [toLω, BoundedFormulaω.realize_imp, BoundedFormula.realize_imp, ih₁, ih₂]
  | all _ ih =>
    simp only [toLω, BoundedFormulaω.realize_all, BoundedFormula.realize_all, ih]

end BoundedFormula

namespace Formula

/-- Embeds a first-order formula into Lω₁ω. -/
def toLω (φ : L.Formula α) : L.Formulaω α := BoundedFormula.toLω φ

@[simp]
theorem realize_toLω {M : Type*} [L.Structure M] {v : α → M} (φ : L.Formula α) :
    Formulaω.Realize φ.toLω v ↔ φ.Realize v :=
  BoundedFormula.realize_toLω φ

end Formula

namespace Sentence

/-- Embeds a first-order sentence into Lω₁ω. -/
def toLω (φ : L.Sentence) : L.Sentenceω := Formula.toLω φ

@[simp]
theorem realize_toLω {M : Type*} [L.Structure M] [Nonempty M] (φ : L.Sentence) :
    Sentenceω.Realize φ.toLω M ↔ M ⊨ φ := by
  -- M ⊨ φ uses `default : Empty → M`, while Sentenceω.Realize uses `Empty.elim`
  -- These are propositionally equal
  have h : (default : Empty → M) = (fun e : Empty => e.elim) := Empty.eq_elim default
  simp only [Sentenceω.Realize, Sentence.Realize, Formula.Realize, toLω, Formula.toLω, h]
  exact BoundedFormula.realize_toLω φ

end Sentence

end Language

end FirstOrder
