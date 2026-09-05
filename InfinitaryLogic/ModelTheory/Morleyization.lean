/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Canonical definitional expansions (Morleyization) for a formula family

Given an arity-tagged family `Φ` of `L_{ω₁ω}`-formulas over `L`, the language `L.morleyize Φ`
keeps the whole base signature and adds one relation symbol `R_φ` of arity `n` for each
`⟨n, φ⟩ ∈ Φ`.  Every `L`-structure has a **canonical** expansion (`morleyExpansion`) in which
`R_φ(a)` holds iff `φ(a)` holds; nothing is chosen.

* `lhomMorleyize Φ : L →ᴸ L.morleyize Φ`, the inclusion; the canonical expansion is an
  expansion along it, and its reduct is literally the original structure
  (`reduct_morleyExpansion`, by `rfl`).
* `relMap_morleyExpansion_inr`: the truth lemma for each new symbol, definitional.
* `definingAxiom φ`, `definingTheory Φ`: the sentences `∀x̄ (R_φ(x̄) ↔ φ(x̄))`, universally
  closed by `alls`; the canonical expansion is a model (`morleyExpansion_model_definingTheory`),
  and it is the **unique** expansion along `lhomMorleyize Φ` satisfying them
  (`eq_morleyExpansion_of_model_definingTheory`).  Defining one canonical interpretation does
  not by itself establish uniqueness; the axioms do.
* `unMorleyize`: the compositional back-translation of expanded-language formulas into the
  base language, replacing each atom `R_φ(t̄)` by `φ` with `t̄` substituted for its bound
  variable slots (`openBounds`, then `subst`, then `boundify`, which rebinds without any
  cast), and `realize_unMorleyize`: realization over the canonical expansion equals
  realization of the back-translation over the base structure.  This is proved directly from
  the definitions; no back-and-forth machinery enters.
* `morleyEquiv` and `morleyEquivRestrict`: an `L`-isomorphism lifts to an isomorphism of the
  canonical expansions with the given underlying bijection (`morleyEquiv_toEquiv`), and any
  isomorphism of the canonical expansions restricts to an `L`-isomorphism with the same
  bijection (`morleyEquivRestrict_toEquiv`); packaged as
  `nonempty_morleyEquiv_iff : Nonempty (M⁺ ≃ N⁺) ↔ Nonempty (M ≃[L] N)`.

## Universe boundary of the back-translation

`unMorleyize` and `realize_unMorleyize` take their free-variable type in `Type`, not `Type*`:
the substitution API `BoundedFormulaω.subst` shares one universe between its source and target
variable types, and the bound-variable slots being substituted are `Fin n : Type`.  Sentences
and finite tuples are covered; the language and carrier universes stay general.  The rest of
the module is universe-polymorphic in the usual way.

## What the witness-free claim rests on

Function symbols are unchanged and every new relation symbol is interpreted by the complete
satisfaction proposition of its formula, so the canonical expansion selects nothing.  The
isomorphism lift carries the given bijection (`morleyEquiv_toEquiv`); that theorem certifies
that the lift chooses no new bijection, and the construction certifies the rest.

These are **infinitary** definitions when `Φ` contains infinitary formulas; they are not a
first-order presentation with omitted types (Marker, *Lectures on Infinitary Model Theory*,
Cambridge, 2016, Theorem 1.2.1 and Exercise 1.2.2, for that classical construction).  No
closure of `Φ` is assumed: `Φ` is any set of tagged formulas, and no fragment structure is
required merely to name them.  Coded structures, Borelness of the expansion map, and refined
topologies are separate.
-/

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-! ## The expanded language -/

/-- The defined-relation symbols of arity `n`: the members of `Φ` at arity `n`. -/
def DefinedSym (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) (n : ℕ) : Type (max u v) :=
  {φ : L.BoundedFormulaω Empty n // (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Φ}

/-- **The Morleyization** of `L` by `Φ`: the base signature retained, one new relation symbol
per member of `Φ`, at that member's arity. -/
def morleyize (L : Language.{u, v}) (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Language.{u, max u v} where
  Functions := L.Functions
  Relations n := L.Relations n ⊕ DefinedSym Φ n

variable (Φ : Set (Σ n, L.BoundedFormulaω Empty n))

/-- The inclusion of the base language. -/
def lhomMorleyize : L →ᴸ L.morleyize Φ where
  onFunction _ f := f
  onRelation _ R := Sum.inl R

instance morleyize_isRelational [L.IsRelational] : (L.morleyize Φ).IsRelational :=
  fun n => inferInstanceAs (IsEmpty (L.Functions n))

/-! ## The canonical expansion -/

/-- **The canonical expansion**: base symbols as before, `R_φ(a)` iff `φ(a)`. -/
@[instance_reducible] def morleyExpansion (M : Type w) [L.Structure M] :
    (L.morleyize Φ).Structure M where
  funMap f x := Structure.funMap (L := L) f x
  RelMap := fun {_} R x => match R with
    | Sum.inl R => Structure.RelMap (L := L) R x
    | Sum.inr φ => φ.1.Realize (Empty.elim : Empty → M) x

variable {Φ} {M : Type w} [L.Structure M]

theorem relMap_morleyExpansion_inl {n : ℕ} (R : L.Relations n) (x : Fin n → M) :
    @Structure.RelMap (L.morleyize Φ) M (morleyExpansion Φ M) n (Sum.inl R) x =
      Structure.RelMap R x := rfl

/-- **The truth lemma** for a defined symbol, definitional. -/
theorem relMap_morleyExpansion_inr {n : ℕ} (φ : DefinedSym Φ n) (x : Fin n → M) :
    @Structure.RelMap (L.morleyize Φ) M (morleyExpansion Φ M) n (Sum.inr φ) x =
      φ.1.Realize (Empty.elim : Empty → M) x := rfl

/-- The canonical expansion is an expansion along the inclusion. -/
theorem isExpansionOn_morleyExpansion :
    @LHom.IsExpansionOn L (L.morleyize Φ) (lhomMorleyize Φ) M _ (morleyExpansion Φ M) :=
  @LHom.IsExpansionOn.mk L (L.morleyize Φ) (lhomMorleyize Φ) M _ (morleyExpansion Φ M)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Reduct after expansion is the identity**, definitionally. -/
theorem reduct_morleyExpansion :
    @LHom.reduct L (L.morleyize Φ) (lhomMorleyize Φ) M (morleyExpansion Φ M) = ‹L.Structure M› :=
  rfl

/-! ## The defining axioms and uniqueness -/

/-- Universal closure of all bound variables. -/
def alls {L' : Language.{u', v'}} : ∀ {n : ℕ}, L'.BoundedFormulaω Empty n → L'.Sentenceω
  | 0, φ => φ
  | _ + 1, φ => alls φ.all

theorem realize_alls {L' : Language.{u', v'}} {N : Type w'} [L'.Structure N] :
    ∀ {n : ℕ} (φ : L'.BoundedFormulaω Empty n),
      Sentenceω.Realize (alls φ) N ↔ ∀ xs : Fin n → N, φ.Realize (Empty.elim : Empty → N) xs
  | 0, φ => by
    show φ.Realize Empty.elim Fin.elim0 ↔ _
    exact ⟨fun h xs => by rwa [Subsingleton.elim xs Fin.elim0], fun h => h _⟩
  | n + 1, φ => by
    show Sentenceω.Realize (alls φ.all) N ↔ _
    rw [realize_alls φ.all]
    simp only [BoundedFormulaω.realize_all]
    constructor
    · intro h ys
      have := h (Fin.init ys) (ys (Fin.last n))
      rwa [Fin.snoc_init_self] at this
    · intro h xs y
      exact h _

variable (Φ)

/-- Base terms as expanded-language terms: the function symbols are the same. -/
def liftTerm {β : Type*} : L.Term β → (L.morleyize Φ).Term β
  | .var x => .var x
  | .func f ts => .func f fun i => liftTerm (ts i)

/-- Base formulas read in the expanded language: the structural relabelling of symbols along
the inclusion.  (`mapLanguage` is stated for a target in the same universes as `L`; the
expanded language lives in `Language.{u, max u v}`.) -/
def liftMorleyize {α : Type*} :
    ∀ {k : ℕ}, L.BoundedFormulaω α k → (L.morleyize Φ).BoundedFormulaω α k
  | _, .falsum => .falsum
  | _, .equal t u => .equal (liftTerm Φ t) (liftTerm Φ u)
  | _, .rel R ts => .rel (Sum.inl R) fun i => liftTerm Φ (ts i)
  | _, .imp φ ψ => (liftMorleyize φ).imp (liftMorleyize ψ)
  | _, .all φ => (liftMorleyize φ).all
  | _, .iSup φs => .iSup fun i => liftMorleyize (φs i)
  | _, .iInf φs => .iInf fun i => liftMorleyize (φs i)

variable {Φ}

/-- Over any expansion along the inclusion, lifted terms realize as in the base. -/
theorem realize_liftTerm_of_isExpansionOn {S : (L.morleyize Φ).Structure M}
    (hS : @LHom.IsExpansionOn L (L.morleyize Φ) (lhomMorleyize Φ) M _ S) {β : Type*}
    (t : L.Term β) (w : β → M) :
    @Term.realize (L.morleyize Φ) M S β w (liftTerm Φ t) = t.realize w := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    show @Structure.funMap (L.morleyize Φ) M S _ f (fun i => _) = Structure.funMap f _
    rw [show (fun i => @Term.realize (L.morleyize Φ) M S β w (liftTerm Φ (ts i)))
      = fun i => (ts i).realize w from funext ih]
    exact hS.map_onFunction f _

/-- Over any expansion along the inclusion, lifted formulas realize as in the base. -/
theorem realize_liftMorleyize_of_isExpansionOn {S : (L.morleyize Φ).Structure M}
    (hS : @LHom.IsExpansionOn L (L.morleyize Φ) (lhomMorleyize Φ) M _ S) {α : Type*} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k) (v : α → M) (xs : Fin k → M),
      @BoundedFormulaω.Realize (L.morleyize Φ) M S α k (liftMorleyize Φ φ) v xs ↔ φ.Realize v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t u, v, xs => by
    show @Term.realize (L.morleyize Φ) M S _ _ (liftTerm Φ t) = Term.realize _ (liftTerm Φ u) ↔ _
    rw [realize_liftTerm_of_isExpansionOn hS, realize_liftTerm_of_isExpansionOn hS]
    rfl
  | _, .rel R ts, v, xs => by
    show @Structure.RelMap (L.morleyize Φ) M S _ (Sum.inl R)
      (fun i => @Term.realize (L.morleyize Φ) M S _ _ (liftTerm Φ (ts i))) ↔ _
    rw [show (fun i => @Term.realize (L.morleyize Φ) M S _ (Sum.elim v xs) (liftTerm Φ (ts i)))
      = fun i => (ts i).realize (Sum.elim v xs) from
        funext fun i => realize_liftTerm_of_isExpansionOn hS _ _]
    exact Iff.of_eq (hS.map_onRelation R _)
  | _, .imp φ ψ, v, xs => by
    simp only [liftMorleyize, BoundedFormulaω.realize_imp]
    exact Iff.imp (realize_liftMorleyize_of_isExpansionOn hS φ v xs)
      (realize_liftMorleyize_of_isExpansionOn hS ψ v xs)
  | _, .all φ, v, xs => by
    simp only [liftMorleyize, BoundedFormulaω.realize_all]
    exact forall_congr' fun y => realize_liftMorleyize_of_isExpansionOn hS φ v _
  | _, .iSup φs, v, xs => by
    simp only [liftMorleyize, BoundedFormulaω.realize_iSup]
    exact exists_congr fun i => realize_liftMorleyize_of_isExpansionOn hS (φs i) v xs
  | _, .iInf φs, v, xs => by
    simp only [liftMorleyize, BoundedFormulaω.realize_iInf]
    exact forall_congr' fun i => realize_liftMorleyize_of_isExpansionOn hS (φs i) v xs

/-- Over the canonical expansion, lifted formulas realize as in the base. -/
theorem realize_liftMorleyize {α : Type*} {k : ℕ} (φ : L.BoundedFormulaω α k) (v : α → M)
    (xs : Fin k → M) :
    @BoundedFormulaω.Realize (L.morleyize Φ) M (morleyExpansion Φ M) α k (liftMorleyize Φ φ) v xs ↔
      φ.Realize v xs :=
  realize_liftMorleyize_of_isExpansionOn isExpansionOn_morleyExpansion φ v xs

variable (Φ)

/-- The defining axiom of a defined symbol: `∀x̄ (R_φ(x̄) ↔ φ(x̄))`, with `φ` read in the expanded
language along the inclusion. -/
def definingAxiom {n : ℕ} (φ : DefinedSym Φ n) : (L.morleyize Φ).Sentenceω :=
  alls ((BoundedFormulaω.rel (Sum.inr φ : (L.morleyize Φ).Relations n)
      fun i => Term.var (Sum.inr i)).iff (liftMorleyize Φ φ.1))

/-- The defining theory: all defining axioms. -/
def definingTheory : (L.morleyize Φ).Theoryω :=
  {σ | ∃ (n : ℕ) (φ : DefinedSym Φ n), σ = definingAxiom Φ φ}

variable {Φ}

/-- The canonical expansion satisfies the defining theory. -/
theorem morleyExpansion_model_definingTheory :
    @Theoryω.Model (L.morleyize Φ) (definingTheory Φ) M (morleyExpansion Φ M) := by
  rintro _ ⟨n, φ, rfl⟩
  let := morleyExpansion Φ M
  rw [definingAxiom, realize_alls]
  intro xs
  rw [BoundedFormulaω.realize_iff]
  exact (realize_liftMorleyize φ.1 Empty.elim xs).symm

/-- **Uniqueness**: an expansion along the inclusion that satisfies the defining theory is the
canonical expansion. -/
theorem eq_morleyExpansion_of_model_definingTheory (S : (L.morleyize Φ).Structure M)
    (hS : @LHom.IsExpansionOn L (L.morleyize Φ) (lhomMorleyize Φ) M _ S)
    (hax : @Theoryω.Model (L.morleyize Φ) (definingTheory Φ) M S) :
    S = morleyExpansion Φ M := by
  let := S
  refine @Structure.ext (L.morleyize Φ) M S (morleyExpansion Φ M) ?_ ?_
  · funext n f x
    exact hS.map_onFunction f x
  · funext n R x
    rcases R with R | φ
    · exact hS.map_onRelation R x
    · have h := hax _ ⟨n, φ, rfl⟩
      rw [definingAxiom, realize_alls] at h
      have hx := h x
      rw [BoundedFormulaω.realize_iff] at hx
      exact propext (hx.trans (realize_liftMorleyize_of_isExpansionOn hS φ.1 Empty.elim x))

/-! ## Back-translation -/

/-- Terms of the expanded language are terms of the base language: the function symbols are the
same. -/
private def termBack {β : Type*} : (L.morleyize Φ).Term β → L.Term β
  | .var x => .var x
  | .func f ts => .func f fun i => termBack (ts i)

private theorem realize_termBack {β : Type*} (t : (L.morleyize Φ).Term β) (w : β → M) :
    (termBack t).realize w = @Term.realize (L.morleyize Φ) M (morleyExpansion Φ M) β w t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    show @Structure.funMap L M _ _ f (fun i => (termBack (ts i)).realize w) =
      @Structure.funMap (L.morleyize Φ) M (morleyExpansion Φ M) _ f
        (fun i => @Term.realize (L.morleyize Φ) M (morleyExpansion Φ M) β w (ts i))
    congr 1
    funext i
    exact ih i

private def boundifyAux {α : Type*} (n k : ℕ) : (α ⊕ Fin n) ⊕ Fin k → α ⊕ Fin (n + k) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _

/-- Rebinding: `α ⊕ Fin n` free variables become `α` free and `n` extra bound variables, with no
cast in the universal case.  Implementation scaffolding for `unMorleyize`. -/
private def boundify {α : Type*} {n : ℕ} :
    ∀ {k : ℕ}, L.BoundedFormulaω (α ⊕ Fin n) k → L.BoundedFormulaω α (n + k)
  | _, .falsum => .falsum
  | k, .equal t u => .equal (t.relabel (boundifyAux n k)) (u.relabel (boundifyAux n k))
  | k, .rel R ts => .rel R fun i => (ts i).relabel (boundifyAux n k)
  | _, .imp φ ψ => (boundify φ).imp (boundify ψ)
  | _, .all φ => (boundify φ).all
  | _, .iSup φs => .iSup fun i => boundify (φs i)
  | _, .iInf φs => .iInf fun i => boundify (φs i)

private theorem sum_elim_boundifyAux {α : Type*} {n k : ℕ} (v : α → M) (zs : Fin (n + k) → M) :
    Sum.elim v zs ∘ boundifyAux n k =
      Sum.elim (Sum.elim v (zs ∘ Fin.castAdd k)) (zs ∘ Fin.natAdd n) := by
  funext x
  rcases x with (a | i) | j
  · rfl
  · simp [boundifyAux, finSumFinEquiv, Fin.castAdd]
  · simp [boundifyAux, finSumFinEquiv, Fin.natAdd]

private lemma snoc_comp_castAdd_natAdd {n k : ℕ} (xs : Fin (n + k) → M) (y : M) :
    (Fin.snoc xs y ∘ Fin.castAdd (k + 1)) = (xs ∘ Fin.castAdd k) := by
  funext i
  simp only [Function.comp_apply, Fin.snoc]
  have hlt : (Fin.castAdd (k + 1) i).val < n + k := by
    have hi : i.val < n := i.is_lt
    have cast_val : (Fin.castAdd (k + 1) i).val = i.val := rfl
    simp only [cast_val]
    omega
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
  · have hj_last : j = Fin.last k := by ext; exact hj
    subst hj_last
    simp only [Fin.natAdd, Fin.last]
    have h1_false : ¬ n + k < n + k := by omega
    have h2_false : ¬ k < k := by omega
    simp only [h1_false, h2_false, dite_false]
  · have hjlt : j.val < k := by omega
    have h1_lt : (Fin.natAdd n j).val < n + k := by
      simp only [Fin.natAdd]
      omega
    have h2_lt : j.val < k := hjlt
    simp only [h1_lt, h2_lt, dite_true]
    rfl

private theorem realize_boundify {α : Type*} {n : ℕ} (v : α → M) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω (α ⊕ Fin n) k) (zs : Fin (n + k) → M),
      (boundify φ).Realize v zs ↔ φ.Realize (Sum.elim v (zs ∘ Fin.castAdd k)) (zs ∘ Fin.natAdd n)
  | _, .falsum, _ => Iff.rfl
  | _, .equal t u, zs => by
    simp only [boundify, BoundedFormulaω.realize_equal, Term.realize_relabel, sum_elim_boundifyAux]
  | _, .rel R ts, zs => by
    simp only [boundify, BoundedFormulaω.realize_rel, Term.realize_relabel, sum_elim_boundifyAux]
  | _, .imp φ ψ, zs => by
    simp only [boundify, BoundedFormulaω.realize_imp]
    exact Iff.imp (realize_boundify v φ zs) (realize_boundify v ψ zs)
  | _, .all φ, zs => by
    simp only [boundify, BoundedFormulaω.realize_all]
    refine forall_congr' fun y => ?_
    rw [realize_boundify v φ (Fin.snoc zs y), snoc_comp_castAdd_natAdd, snoc_comp_natAdd_succ]
  | _, .iSup φs, zs => by
    simp only [boundify, BoundedFormulaω.realize_iSup]
    exact exists_congr fun i => realize_boundify v (φs i) zs
  | _, .iInf φs, zs => by
    simp only [boundify, BoundedFormulaω.realize_iInf]
    exact forall_congr' fun i => realize_boundify v (φs i) zs

/-- **The back-translation**: each atom `R_φ(t̄)` becomes `φ` with `t̄` substituted for its bound
variable slots; everything else is structural. -/
def unMorleyize {α : Type} : ∀ {k : ℕ}, (L.morleyize Φ).BoundedFormulaω α k → L.BoundedFormulaω α k
  | _, .falsum => .falsum
  | _, .equal t u => .equal (termBack t) (termBack u)
  | _, .rel (Sum.inl R) ts => .rel R fun i => termBack (ts i)
  | _, .rel (Sum.inr φ) ts => boundify (φ.1.openBounds.subst fun i => termBack (ts i))
  | _, .imp φ ψ => (unMorleyize φ).imp (unMorleyize ψ)
  | _, .all φ => (unMorleyize φ).all
  | _, .iSup φs => .iSup fun i => unMorleyize (φs i)
  | _, .iInf φs => .iInf fun i => unMorleyize (φs i)

/-- **Realization equivalence**: over the canonical expansion, a formula and its
back-translation agree. -/
theorem realize_unMorleyize {α : Type} :
    ∀ {k : ℕ} (ψ : (L.morleyize Φ).BoundedFormulaω α k) (v : α → M) (xs : Fin k → M),
      (unMorleyize ψ).Realize v xs ↔
        @BoundedFormulaω.Realize (L.morleyize Φ) M (morleyExpansion Φ M) α k ψ v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t u, v, xs => by
    simp only [unMorleyize, BoundedFormulaω.realize_equal, realize_termBack]
  | _, .rel (Sum.inl R) ts, v, xs => by
    simp only [unMorleyize, BoundedFormulaω.realize_rel, realize_termBack]
    exact Iff.rfl
  | k, .rel (Sum.inr φ) ts, v, xs => by
    show (boundify (φ.1.openBounds.subst fun i => termBack (ts i))).Realize v xs ↔ _
    rw [realize_boundify (n := k) (k := 0) v _ xs, BoundedFormulaω.realize_subst]
    have h0 : (xs ∘ Fin.castAdd 0) = xs := funext fun i => rfl
    have h1 : (xs ∘ Fin.natAdd k : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
    rw [h0, h1]
    refine (realize_openBounds _ _).trans ?_
    simp only [realize_termBack]
    exact Iff.rfl
  | _, .imp φ ψ, v, xs => by
    simp only [unMorleyize, BoundedFormulaω.realize_imp]
    exact Iff.imp (realize_unMorleyize φ v xs) (realize_unMorleyize ψ v xs)
  | _, .all φ, v, xs => by
    simp only [unMorleyize, BoundedFormulaω.realize_all]
    exact forall_congr' fun y => realize_unMorleyize φ v _
  | _, .iSup φs, v, xs => by
    simp only [unMorleyize, BoundedFormulaω.realize_iSup]
    exact exists_congr fun i => realize_unMorleyize (φs i) v xs
  | _, .iInf φs, v, xs => by
    simp only [unMorleyize, BoundedFormulaω.realize_iInf]
    exact forall_congr' fun i => realize_unMorleyize (φs i) v xs

/-! ## Isomorphism transport -/

/-- An `L`-isomorphism lifts to an isomorphism of the canonical expansions; no witnesses are
selected. -/
def morleyEquiv (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) {N : Type w} [L.Structure N]
    (e : M ≃[L] N) :
    @Language.Equiv (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N) :=
  @Language.Equiv.mk (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N) e.toEquiv
    (fun {_} f x => e.map_fun f x)
    (fun {n} R x => by
      rcases R with R | φ
      · exact e.map_rel R x
      · have h := BoundedFormulaω.realize_equiv e φ.1 (Empty.elim : Empty → M) x
        rw [show (⇑e ∘ Empty.elim : Empty → N) = Empty.elim from funext fun z => z.elim] at h
        exact h.symm)

/-- **Restriction**: an isomorphism of the canonical expansions is an `L`-isomorphism with the
same bijection, through the base symbols. -/
def morleyEquivRestrict {N : Type w} [L.Structure N]
    (g : @Language.Equiv (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N)) :
    M ≃[L] N where
  toEquiv := @Language.Equiv.toEquiv (L.morleyize Φ) M N (morleyExpansion Φ M)
    (morleyExpansion Φ N) g
  map_fun' f x := @Language.Equiv.map_fun (L.morleyize Φ) M N (morleyExpansion Φ M)
    (morleyExpansion Φ N) g _ f x
  map_rel' R x := @Language.Equiv.map_rel (L.morleyize Φ) M N (morleyExpansion Φ M)
    (morleyExpansion Φ N) g _ (Sum.inl R) x

theorem morleyEquivRestrict_toEquiv {N : Type w} [L.Structure N]
    (g : @Language.Equiv (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N)) :
    (morleyEquivRestrict g).toEquiv =
      @Language.Equiv.toEquiv (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N) g :=
  rfl

/-- **Isomorphism transport, both directions**: the canonical expansions are isomorphic iff the
base structures are. -/
theorem nonempty_morleyEquiv_iff {N : Type w} [L.Structure N] :
    Nonempty (@Language.Equiv (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N)) ↔
      Nonempty (M ≃[L] N) :=
  ⟨fun ⟨g⟩ => ⟨morleyEquivRestrict g⟩, fun ⟨e⟩ => ⟨morleyEquiv Φ e⟩⟩

/-- The lifted isomorphism has the given underlying bijection. -/
theorem morleyEquiv_toEquiv {N : Type w} [L.Structure N] (e : M ≃[L] N) :
    @Language.Equiv.toEquiv (L.morleyize Φ) M N (morleyExpansion Φ M) (morleyExpansion Φ N)
      (morleyEquiv Φ e) = e.toEquiv := rfl

end FirstOrder.Language
