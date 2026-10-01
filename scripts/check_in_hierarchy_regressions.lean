/-
Regression guard for the ordinal-indexed `Σ^in_α` / `Π^in_α` hierarchy
(`InfinitaryLogic/Lomega1omega/InHierarchy.lean`).

* every public declaration of the module is applied to a term, and a completeness check fails if
  the module gains a public declaration this guard does not list;
* level `0`: equality and relation atoms and a finite Boolean combination are in both classes, and
  `all`, `iSup`, `iInf` are in neither;
* a `Σ^in_1` formula with a genuine countable disjunction, `⋁ₙ ∃y (y = cₙ ∧ x = y)` over countably
  many constants, which is neither `Σ^in_0` nor `Π^in_1`;
* the `Π^in_2` sentence `infiniteAxiom` (the countable conjunction of "at least `n` elements"),
  which is neither `Σ^in_1` nor `Π^in_1`;
* negation duality on the concrete `Σ^in_1` formula;
* the relation to `universalSigned`: agreement on the concrete `Σ^in_1` formula and on first-order
  images (`inSigned_one_toLω_iff`, applied to the finitary existential `∃y x = y` and to every
  `cardGe n`), and disagreement on `⋀ₙ x = cₙ` and on `∃y ⋀ₙ y = cₙ`, both `∃₁` and neither
  `Σ^in_1`;
* quantifier rank: level `0` has rank `0`, and the `Π^in_1` sentence `∀x ⋀ₖ ∀y₁ … yₖ ⊤` has rank
  `ω + 1 > ω · 1`, so no `ω · α` bound holds for the signed classes (and that sentence is not a
  `Π^in_1` normal form);
* normal forms: `⋀ₖ ∀y₁ … yₖ ⊤` is a `Π^in_1` normal form of rank `ω ≤ ω · 1`, a finite `esup` of
  existential blocks is a `Σ^in_1` normal form, `σ1` is one, and `einf` over it is a `Π^in_2`
  normal form of rank at most `ω · 2`; each lies in its signed class;
* closure under `castLE`, `relabel`, `subst`, `mapFreeVars`, `mapLanguage`, `einf` and `all` at
  level `1`, `esup`, `imp`, `⊓`, `⊔`, finite blocks, and a quantifier raising the level, plus one
  universe-polymorphic use;
* standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
* minimal imports: the module's `InfinitaryLogic` import closure reaches no `Scott`, `Karp`,
  `ScottProcess`, `Descriptive`, `Methods` or `ModelTheory` module and is exactly the syntax
  layer listed in `allowedClosure`.

Run with: lake env lean scripts/check_in_hierarchy_regressions.lean
-/
import InfinitaryLogic.Lomega1omega.InHierarchy
import InfinitaryLogic.Lomega1omega.InfiniteAxiom

universe u v u'

open FirstOrder Language BoundedFormulaω

namespace InHierarchyRegressions

/-! ## Languages and terms -/

/-- Countably many constants `cₙ`. -/
abbrev Lc : Language.{0, 0} := constantsOn ℕ

/-- A language with one relation symbol of every arity. -/
abbrev Lr : Language.{0, 0} := ⟨fun _ ↦ Empty, fun _ ↦ Unit⟩

/-- The constant `cₙ` as a term over any variable type. -/
def c {γ : Type} (n : ℕ) : Lc.Term γ := Constants.term (n : Lc.Constants)

/-- The free variable `x`. -/
def x {k : ℕ} : Lc.Term (Unit ⊕ Fin k) := Term.var (Sum.inl ())

/-- The bound variable `y` (the first one). -/
def y {k : ℕ} : Lc.Term (Unit ⊕ Fin (k + 1)) := Term.var (Sum.inr 0)

theorem two : (1 : Ordinal.{0}) + 1 = 2 := one_add_one_eq_two

/-! ## Level `0` -/

/-- `x = c₀ → ¬ x = c₁`: a finitary quantifier-free formula. -/
def θ0 : Lc.Formulaω Unit := (equal x (c 0)).imp (equal x (c 1)).not

theorem isSigmaIn_zero_θ0 : IsSigmaIn 0 θ0 := by simp [θ0]

example : IsPiIn 0 θ0 := (inSigned_zero_iff false true θ0).1 isSigmaIn_zero_θ0

example : θ0.qrank = 0 := qrank_eq_zero_of_inSigned_zero isSigmaIn_zero_θ0

/-- A relation atom. -/
example : IsSigmaIn 0
    (BoundedFormulaω.rel (() : Lr.Relations 2)
      ![Term.var (Sum.inl ()), Term.var (Sum.inl ())] : Lr.Formulaω Unit) :=
  inSigned_rel 0 false _ _

example : IsPiIn 0 (⊥ : Lc.Formulaω Unit) := inSigned_bot 0 true
example : IsPiIn 0 (BoundedFormulaω.falsum : Lc.Formulaω Unit) := inSigned_falsum 0 true
example : IsSigmaIn 0 (equal x (c 3) : Lc.Formulaω Unit) := inSigned_equal 0 false _ _
example : IsSigmaIn 0 (⊤ : Lc.Formulaω Unit) := inSigned_top 0 false

/-- No quantifier at level `0`, at either sign. -/
example : ¬ IsPiIn 0 (all (equal y x) : Lc.Formulaω Unit) := by simp
example : ¬ IsSigmaIn 0 (all (equal y x) : Lc.Formulaω Unit) := by simp

/-- No countable connective at level `0`, at either sign. -/
example : ¬ IsSigmaIn 0 (iSup fun n ↦ equal x (c n) : Lc.Formulaω Unit) := by simp
example : ¬ IsPiIn 0 (iInf fun n ↦ equal x (c n) : Lc.Formulaω Unit) := by simp

/-! ## A `Σ^in_1` formula with a genuine countable disjunction -/

/-- `⋁ₙ ∃y (y = cₙ ∧ x = y)`, i.e. "`x` is one of the constants". -/
def σ1 : Lc.Formulaω Unit := esup fun n : ℕ ↦ ((equal y (c n)).and (equal x y)).ex

theorem isSigmaIn_one_σ1 : IsSigmaIn 1 σ1 :=
  isSigmaIn_esup le_rfl fun _ ↦ isSigmaIn_ex le_rfl (by simp)

theorem not_isPiIn_one_σ1 : ¬ IsPiIn 1 σ1 := by
  rintro ⟨b, hb, hb1, -⟩
  exact (hb1.trans_lt hb).false

example : ¬ IsSigmaIn 0 σ1 := fun h ↦ absurd ((isSigmaIn_esup_iff _).1 h).1 (by simp)

example : IsPiIn 2 σ1 := two ▸ isSigmaIn_one_σ1.isPiIn_add_one

example : IsSigmaIn 2 σ1 := isSigmaIn_one_σ1.mono one_le_two

/-! ## Negation duality on the concrete formula -/

example : IsPiIn 1 σ1.not := isPiIn_not_iff.2 isSigmaIn_one_σ1

example : ¬ IsSigmaIn 1 σ1.not := fun h ↦ not_isPiIn_one_σ1 (isSigmaIn_not_iff.1 h)

example : IsSigmaIn 1 σ1.not.not := isSigmaIn_not_iff.2 (isPiIn_not_iff.2 isSigmaIn_one_σ1)

example : inSigned 1 true σ1.not ↔ inSigned 1 false σ1 := inSigned_not 1 true σ1

/-! ## The relation to `universalSigned` -/

/-- Agreement: the `Σ^in_1` formula with its countable disjunction is `∃₁`. -/
example : IsExistential σ1 := universalSigned_of_inSigned_one isSigmaIn_one_σ1

/-- Disagreement: `⋀ₙ x = cₙ` is `∃₁` (and `∀₁`), `Π^in_1`, and not `Σ^in_1`. -/
def δ : Lc.Formulaω Unit := iInf fun n ↦ equal x (c n)

theorem isPiIn_one_δ : IsPiIn 1 δ := (inSigned_iInf_true 1 _).2 ⟨le_rfl, fun _ ↦ trivial⟩

example : IsExistential δ := by simp [δ]
example : IsUniversal δ := universalSigned_of_inSigned_one isPiIn_one_δ

theorem not_isSigmaIn_one_δ : ¬ IsSigmaIn 1 δ := by
  rintro ⟨b, hb, hb1, -⟩
  exact (hb1.trans_lt hb).false

/-- Disagreement under a quantifier: `∃y ⋀ₙ y = cₙ` is `∃₁` but only `Σ^in_2`. -/
def δ' : Lc.Sentenceω := (iInf fun n ↦ equal (Term.var (Sum.inr 0)) (c n)).ex

example : IsExistential δ' := (isExistential_ex _).2 (by simp)

example : ¬ IsSigmaIn 1 δ' := by
  simp only [δ', IsSigmaIn, inSigned_ex_false, inSigned_iInf_false]
  rintro ⟨-, b, hb, hb1, -⟩
  exact (hb1.trans_lt hb).false

theorem isSigmaIn_two_δ' : IsSigmaIn 2 δ' := by
  have hπ : IsPiIn 1 (iInf fun n ↦ equal (Term.var (Sum.inr 0)) (c n) :
      Lc.BoundedFormulaω Empty 1) :=
    (inSigned_iInf_true 1 _).2 ⟨le_rfl, fun _ ↦ trivial⟩
  exact two ▸ hπ.isSigmaIn_add_one_ex

/-- A finitary existential formula `∃y x = y` is `Σ^in_1` after `toLω` (and not `Π^in_1`). -/
def ε1 : Lc.Formula Unit :=
  ((Term.var (Sum.inl ()) : Lc.Term (Unit ⊕ Fin 1)).bdEqual (Term.var (Sum.inr 0))).ex

theorem isSigmaIn_one_ε1 : IsSigmaIn 1 ε1.toLω :=
  (inSigned_one_toLω_iff false _).2 ((isExistential_ex (L := Lc) _).2 trivial)

example : ¬ IsPiIn 1 ε1.toLω := fun h ↦
  not_isUniversal_ex (L := Lc) _ ((inSigned_one_toLω_iff true ε1).1 h)

/-! ### Agreement on every first-order image -/

section FirstOrderImages

variable {L : Language.{0, 0}} {α : Type}

/-- A first-order conjunction lands at a level and sign when both conjuncts do. -/
theorem inSigned_toLω_inf {k : ℕ} {f g : L.BoundedFormula α k} {a : Ordinal.{0}} {s : Bool}
    (hf : inSigned a s f.toLω) (hg : inSigned a s g.toLω) : inSigned a s (f ⊓ g).toLω :=
  (inSigned_and a s f.toLω g.toLω).2 ⟨hf, hg⟩

/-- An existential block over a `Σ^in_1` first-order image stays `Σ^in_1`. -/
theorem isSigmaIn_one_toLω_exs :
    ∀ {k : ℕ} {ψ : L.BoundedFormula α k}, IsSigmaIn 1 ψ.toLω → IsSigmaIn 1 ψ.exs.toLω
  | 0, _, h => h
  | _ + 1, ψ, h => isSigmaIn_one_toLω_exs (ψ := ψ.ex) (isSigmaIn_ex (φ := ψ.toLω) le_rfl h)

/-- "There are at least `n` elements" is `Σ^in_1`: an existential block over a finite
conjunction of negated equalities. -/
theorem isSigmaIn_one_cardGe (n : ℕ) : IsSigmaIn 1 (Sentence.cardGe L n).toLω := by
  have hfold : ∀ l : List (L.BoundedFormula Empty n), (∀ ψ ∈ l, IsSigmaIn 1 ψ.toLω) →
      IsSigmaIn 1 (l.foldr (· ⊓ ·) ⊤).toLω := by
    intro l hl
    induction l with
    | nil => exact inSigned_top 1 false
    | cons ψ l ih =>
      exact inSigned_toLω_inf (hl ψ (by simp)) (ih fun χ hχ ↦ hl χ (List.mem_cons_of_mem _ hχ))
  refine isSigmaIn_one_toLω_exs (hfold _ ?_)
  intro ψ hψ
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hψ
  exact (inSigned_not 1 false _).2 trivial

/-- The agreement theorem, read on `cardGe`: `Σ^in_1` iff `∃₁`. -/
example (n : ℕ) : IsExistential (Sentence.cardGe L n).toLω :=
  (inSigned_one_toLω_iff false _).1 (isSigmaIn_one_cardGe n)

/-! ## A `Π^in_2` sentence: "infinite" -/

/-- **`infiniteAxiom` is `Π^in_2`**: a countable conjunction of `Σ^in_1` sentences. -/
theorem isPiIn_two_infiniteAxiom : IsPiIn 2 (infiniteAxiom L) :=
  (inSigned_iInf_true 2 _).2 ⟨one_le_two, fun n ↦
    two ▸ (isSigmaIn_one_cardGe (L := L) n).isPiIn_add_one⟩

/-- It is not `Σ^in_1`: a countable conjunction cannot sit at the `Σ` sign of level one. -/
example : ¬ IsSigmaIn 1 (infiniteAxiom L) := by
  rintro ⟨b, hb, hb1, -⟩
  exact (hb1.trans_lt hb).false

/-- It is not `Π^in_1`: its conjunct "at least one element" is an existential. -/
example : ¬ IsPiIn 1 (infiniteAxiom L) := by
  intro h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L.BoundedFormulaω Empty 1, (Sentence.cardGe L 1).toLω = ψ.ex :=
    ⟨_, rfl⟩
  have h1 : IsPiIn 1 (Sentence.cardGe L 1).toLω := h.2 1
  rw [hψ, IsPiIn, inSigned_ex_true] at h1
  obtain ⟨b, hb, hb1, -⟩ := h1
  exact (hb1.trans_lt hb).false

end FirstOrderImages

/-! ## Quantifier rank -/

/-- `forallBlock` adds its length to the rank. -/
theorem qrank_forallBlock {m : ℕ} :
    ∀ {k : ℕ} (φ : Lc.BoundedFormulaω Empty (m + k)), (forallBlock φ).qrank = φ.qrank + k
  | 0, φ => by simp [forallBlock]
  | k + 1, φ => by
    rw [show forallBlock φ = forallBlock (k := k) φ.all from rfl, qrank_forallBlock φ.all,
      qrank_all, add_assoc]
    congr 1
    exact_mod_cast Nat.add_comm 1 k

/-- `∀x ⋀ₖ ∀y₁ … yₖ ⊤`. -/
def τ : Lc.Sentenceω := all (iInf fun k : ℕ ↦ forallBlock (n := 1) (k := k) ⊤)

theorem isPiIn_one_τ : IsPiIn 1 τ :=
  isPiIn_all le_rfl ((inSigned_iInf_true 1 _).2
    ⟨le_rfl, fun _ ↦ (isPiIn_forallBlock_iff le_rfl _).2 (inSigned_top 1 true)⟩)

theorem qrank_τ : τ.qrank = Ordinal.omega0 + 1 := by
  simp [τ, qrank_forallBlock, Ordinal.iSup_natCast]

/-- **No `ω · α` bound for the signed class**: a `Π^in_1` sentence of rank `ω + 1 > ω · 1`. -/
example : ∃ φ : Lc.Sentenceω, IsPiIn 1 φ ∧ Ordinal.omega0 * 1 < φ.qrank :=
  ⟨τ, isPiIn_one_τ, by rw [qrank_τ, mul_one]; exact lt_add_one _⟩

/-- Hence `τ` is not a `Π^in_1` normal form: the normal-form bound would cap its rank at `ω`. -/
example : ¬ IsPiInNF 1 τ := fun h ↦ by
  have h1 : τ.qrank ≤ Ordinal.omega0 * 1 := h.qrank_le
  rw [qrank_τ, mul_one] at h1
  exact not_le.2 (lt_add_one _) h1

/-! ## Normal forms -/

/-- A universal block over a block stays a block. -/
theorem normalFormIn_forallBlock {a : Ordinal.{0}} {m : ℕ} :
    ∀ {k : ℕ} {φ : Lc.BoundedFormulaω Empty (m + k)}, NormalFormIn a true true φ →
      NormalFormIn a true true (forallBlock φ)
  | 0, _, h => h
  | _ + 1, φ, h => normalFormIn_forallBlock (φ := φ.all) (NormalFormIn.all h)

/-- `⋀ₖ ∀y₁ … yₖ ⊤`, the body of `τ` with its outer `∀` dropped, as a sentence. -/
def π1 : Lc.Sentenceω := iInf fun k : ℕ ↦ forallBlock (n := 0) (k := k) ⊤

/-- It is literally a `Π^in_1` normal form: each conjunct is a universal block over `⊤`. -/
theorem isPiInNF_one_π1 : IsPiInNF 1 π1 :=
  NormalFormIn.iInf fun _ ↦ normalFormIn_forallBlock (.base zero_lt_one (.zero ⟨trivial, trivial⟩))

/-- The normal-form bound, applied: rank at most `ω · 1` (it is exactly `ω`). -/
example : π1.qrank ≤ Ordinal.omega0 * 1 := isPiInNF_one_π1.qrank_le

example : π1.qrank = Ordinal.omega0 := by
  simp [π1, qrank_forallBlock, Ordinal.iSup_natCast]

/-- A normal form lies in the signed class. -/
example : IsPiIn 1 π1 := isPiInNF_one_π1.isPiIn

/-- A `Σ^in_1` normal form through `esup`, with its bound and its signed class. -/
theorem isSigmaInNF_one_esup :
    IsSigmaInNF 1 (esup fun n : Fin 4 ↦ (equal y (c n) : Lc.BoundedFormulaω Unit 1).ex) :=
  isSigmaInNF_esup le_rfl fun _ ↦ .ex (.base zero_lt_one (.zero trivial))

example : (esup fun n : Fin 4 ↦ (equal y (c n) : Lc.BoundedFormulaω Unit 1).ex).qrank ≤
    Ordinal.omega0 * 1 :=
  isSigmaInNF_one_esup.qrank_le

example : IsSigmaIn 1 (esup fun n : Fin 4 ↦ (equal y (c n) : Lc.BoundedFormulaω Unit 1).ex) :=
  isSigmaInNF_one_esup.isSigmaIn

/-- The `Σ^in_1` formula `σ1` is literally a normal form. -/
theorem isSigmaInNF_one_σ1 : IsSigmaInNF 1 σ1 :=
  isSigmaInNF_esup le_rfl fun _ ↦ .ex (.base zero_lt_one (.zero (by simp)))

/-- `einf` of empty universal blocks over a `Σ^in_1` normal form is a `Π^in_2` normal form, with
rank at most `ω · 2`. -/
theorem isPiInNF_two_einf : IsPiInNF 2 (einf fun _ : Bool ↦ σ1) :=
  isPiInNF_einf one_le_two fun _ ↦ .base one_lt_two isSigmaInNF_one_σ1

example : (einf fun _ : Bool ↦ σ1).qrank ≤ Ordinal.omega0 * 2 := isPiInNF_two_einf.qrank_le

/-- A block lies in the signed class of its own kind. -/
example {a : Ordinal.{0}} {φ : Lc.Formulaω Unit} (h : NormalFormIn a false true φ) :
    IsSigmaIn a φ :=
  h.inSigned

/-! ## Closure lemmas -/

/-- `castLE` into one more bound variable. -/
example : IsSigmaIn 1 (σ1.castLE (Nat.zero_le 1)) :=
  (inSigned_castLE (Nat.zero_le 1) 1 false σ1).2 isSigmaIn_one_σ1

/-- `relabel` turning `x` into a bound variable. -/
theorem isSigmaIn_one_relabel_σ1 :
    IsSigmaIn 1 (σ1.relabel fun _ : Unit ↦ (Sum.inr 0 : Empty ⊕ Fin 1)) :=
  (inSigned_relabel _ 1 false σ1).2 isSigmaIn_one_σ1

/-- Then `∀`: the level rises by one. -/
def σ1Closed : Lc.Sentenceω :=
  all (σ1.relabel fun _ : Unit ↦ (Sum.inr 0 : Empty ⊕ Fin 1))

example : IsPiIn 2 σ1Closed := two ▸ isSigmaIn_one_relabel_σ1.isPiIn_add_one_all

/-- `all` at the `Σ` sign drops to a lower `Π` level. -/
example : IsSigmaIn 3 σ1Closed :=
  (inSigned_all_false 3 _).2 ⟨2, by exact_mod_cast (show 2 < 3 by decide), one_le_two,
    two ▸ isSigmaIn_one_relabel_σ1.isPiIn_add_one⟩

/-- `subst` of a constant for `x`. -/
example : IsSigmaIn 1 (σ1.subst fun _ ↦ (c 5 : Lc.Term Empty)) :=
  (inSigned_subst _ 1 false σ1).2 isSigmaIn_one_σ1

/-- `mapFreeVars`. -/
example : IsSigmaIn 1 (σ1.mapFreeVars fun _ ↦ (0 : Fin 1)) :=
  (inSigned_mapFreeVars _ 1 false σ1).2 isSigmaIn_one_σ1

/-- `mapLanguage` into the sum with a relational language. -/
example : IsSigmaIn 1 (σ1.mapLanguage (LHom.sumInl : Lc →ᴸ Lc.sum Lr)) :=
  (inSigned_mapLanguage _ 1 false σ1).2 isSigmaIn_one_σ1

/-- `einf` at level `1` over an `Encodable` index, of `Π^in_1` formulas. -/
example : IsPiIn 1 (einf fun p : ℕ × ℕ ↦ (equal x (c p.1)).imp (equal x (c p.2)) :
    Lc.Formulaω Unit) :=
  isPiIn_einf le_rfl fun _ ↦ by simp

/-- `all` at level `1`, over a vacuously quantified `Π^in_1` formula. -/
example : IsPiIn 1 (all (δ.castLE (Nat.zero_le 1))) :=
  isPiIn_all le_rfl ((inSigned_castLE _ 1 true δ).2 isPiIn_one_δ)

/-- `einf` of `Σ^in_1` formulas is `Π^in_2`, read through the exact form. -/
example : IsPiIn 2 (einf fun _ : Fin 3 ↦ σ1) :=
  (isPiIn_einf_iff _).2 ⟨one_le_two, fun _ ↦ two ▸ isSigmaIn_one_σ1.isPiIn_add_one⟩

/-- `esup` of `Π^in_1` formulas is `Σ^in_2`. -/
example : IsSigmaIn 2 (esup fun _ : Bool ↦ δ) :=
  isSigmaIn_esup one_le_two fun _ ↦ two ▸ isPiIn_one_δ.isSigmaIn_add_one

/-- The finite connectives at a positive level. -/
example : IsPiIn 1 (σ1.imp δ) := isPiIn_imp isSigmaIn_one_σ1 isPiIn_one_δ
example : IsSigmaIn 1 (δ.imp σ1) := isSigmaIn_imp isPiIn_one_δ isSigmaIn_one_σ1
example : IsPiIn 1 (δ ⊓ σ1.not) := isPiIn_inf isPiIn_one_δ (isPiIn_not_iff.2 isSigmaIn_one_σ1)
example : IsSigmaIn 1 (σ1 ⊔ δ.not) :=
  isSigmaIn_sup isSigmaIn_one_σ1 (isSigmaIn_not_iff.2 isPiIn_one_δ)

/-- Finite blocks: `∀y₁ y₂ (y₁ = y₂)` and `∃y₁ y₂ (y₁ = y₂ ∧ x = y₁)`. -/
example : IsPiIn 1 (forallBlock (n := 0) (k := 2)
    (equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))) : Lc.Formulaω Unit) :=
  (isPiIn_forallBlock_iff le_rfl _).2 trivial

example : IsSigmaIn 1 (existsBlock (n := 0) (k := 2)
    ((equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).and (equal x (Term.var (Sum.inr 0))))
      : Lc.Formulaω Unit) :=
  (isSigmaIn_existsBlock_iff le_rfl _).2 (by simp)

/-- The constructor equations, each applied. -/
example : IsPiIn 1 (all (equal y x) : Lc.Formulaω Unit) :=
  (inSigned_all_true 1 _).2 ⟨le_rfl, trivial⟩

example : IsSigmaIn 2 (iInf fun n ↦ equal x (c n) : Lc.Formulaω Unit) :=
  (inSigned_iInf_false 2 _).2 ⟨1, one_lt_two, le_rfl, fun _ ↦ trivial⟩

example : IsPiIn 2 (iSup fun n ↦ equal x (c n) : Lc.Formulaω Unit) :=
  (inSigned_iSup_true 2 _).2 ⟨1, one_lt_two, le_rfl, fun _ ↦ trivial⟩

example : IsSigmaIn 1 (iSup fun n ↦ equal x (c n) : Lc.Formulaω Unit) :=
  (inSigned_iSup_false 1 _).2 ⟨le_rfl, fun _ ↦ trivial⟩

example : IsSigmaIn 1 ((equal x (c 0)).imp (equal x (c 1)) : Lc.Formulaω Unit) :=
  (inSigned_imp 1 false _ _).2 ⟨trivial, trivial⟩

example : IsSigmaIn 1 ((equal x (c 0)).and σ1) :=
  (inSigned_and 1 false _ _).2 ⟨trivial, isSigmaIn_one_σ1⟩

example : IsSigmaIn 1 ((equal x (c 0)).or σ1) :=
  (inSigned_or 1 false _ _).2 ⟨trivial, isSigmaIn_one_σ1⟩

example : IsSigmaIn 1 ((equal y x).ex : Lc.Formulaω Unit) :=
  (inSigned_ex_false 1 _).2 ⟨le_rfl, trivial⟩

example : IsPiIn 2 ((equal y x).ex : Lc.Formulaω Unit) :=
  (inSigned_ex_true 2 _).2 ⟨1, one_lt_two, le_rfl, trivial⟩

/-- Monotonicity and the strict step, in every form. -/
example : IsSigmaIn 5 σ1 :=
  inSigned_mono (by exact_mod_cast (show 1 ≤ 5 by decide)) isSigmaIn_one_σ1
example : IsPiIn 7 σ1 :=
  inSigned_of_lt (by exact_mod_cast (show 1 < 7 by decide)) true isSigmaIn_one_σ1
example : IsPiIn 3 δ := isPiIn_one_δ.mono (by exact_mod_cast (show 1 ≤ 3 by decide))
example : IsSigmaIn 2 δ := two ▸ isPiIn_one_δ.isSigmaIn_add_one
example : IsPiIn Ordinal.omega0 σ1 :=
  inSigned_of_lt Ordinal.one_lt_omega0 true isSigmaIn_one_σ1

/-! ## Universe polymorphism -/

example {L : Language.{u, v}} {α : Type u'} {n : ℕ} {a : Ordinal.{0}}
    (φ : L.BoundedFormulaω α (n + 1)) (h : IsPiIn a φ) :
    IsSigmaIn (a + 1) φ.ex ∧ IsPiIn (a + 1) φ.ex.not :=
  ⟨h.isSigmaIn_add_one_ex, isPiIn_not_iff.2 h.isSigmaIn_add_one_ex⟩

/-! ## Axioms -/

/-- Every public declaration of the module. -/
def headline : List Lean.Name :=
  [``inSigned, ``IsPiIn, ``IsSigmaIn,
   ``inSigned_falsum, ``inSigned_bot, ``inSigned_equal, ``inSigned_rel, ``inSigned_imp,
   ``inSigned_all_true, ``inSigned_all_false, ``inSigned_iInf_true, ``inSigned_iInf_false,
   ``inSigned_iSup_true, ``inSigned_iSup_false,
   ``inSigned_not, ``inSigned_top, ``inSigned_and, ``inSigned_or, ``inSigned_ex_false,
   ``inSigned_ex_true,
   ``inSigned_zero_iff, ``qrank_eq_zero_of_inSigned_zero,
   ``inSigned_mono, ``inSigned_of_lt, ``IsSigmaIn.mono, ``IsPiIn.mono,
   ``IsSigmaIn.isPiIn_add_one, ``IsPiIn.isSigmaIn_add_one,
   ``isSigmaIn_not_iff, ``isPiIn_not_iff,
   ``isPiIn_imp, ``isSigmaIn_imp, ``isPiIn_inf, ``isSigmaIn_sup,
   ``isPiIn_all, ``isSigmaIn_ex, ``IsSigmaIn.isPiIn_add_one_all, ``IsPiIn.isSigmaIn_add_one_ex,
   ``isPiIn_forallBlock_iff, ``isSigmaIn_existsBlock_iff,
   ``isPiIn_einf_iff, ``isSigmaIn_esup_iff, ``isPiIn_einf, ``isSigmaIn_esup,
   ``inSigned_castLE, ``inSigned_relabel, ``inSigned_subst, ``inSigned_mapFreeVars,
   ``inSigned_mapLanguage,
   ``NormalFormIn, ``NormalFormIn.zero, ``NormalFormIn.base, ``NormalFormIn.ex,
   ``NormalFormIn.all, ``NormalFormIn.iSup, ``NormalFormIn.iInf, ``IsSigmaInNF, ``IsPiInNF,
   ``NormalFormIn.inSigned, ``IsSigmaInNF.isSigmaIn, ``IsPiInNF.isPiIn, ``IsSigmaInNF.qrank_le,
   ``IsPiInNF.qrank_le, ``isSigmaInNF_esup, ``isPiInNF_einf,
   ``universalSigned_of_inSigned_one, ``inSigned_one_toLω_iff]

/-- The guard's own load-bearing lemmas. -/
def guardLemmas : List Lean.Name :=
  [``isSigmaIn_one_σ1, ``not_isPiIn_one_σ1, ``isPiIn_one_δ, ``not_isSigmaIn_one_δ,
   ``isSigmaIn_two_δ', ``isSigmaIn_one_ε1, ``inSigned_toLω_inf, ``isSigmaIn_one_toLω_exs,
   ``isSigmaIn_one_cardGe, ``isPiIn_two_infiniteAxiom, ``qrank_forallBlock, ``isPiIn_one_τ,
   ``qrank_τ, ``isSigmaIn_one_relabel_σ1, ``normalFormIn_forallBlock, ``isPiInNF_one_π1,
   ``isSigmaInNF_one_esup, ``isSigmaInNF_one_σ1,
   ``isPiInNF_two_einf]

/-- The standard axioms. -/
def standardAxioms : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]

end InHierarchyRegressions

open Lean InHierarchyRegressions

run_cmd do
  let env ← getEnv
  for n in headline ++ guardLemmas do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"

/-! ## Every public declaration is listed -/

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Lomega1omega.InHierarchy
  let some idx := env.getModuleIdx? target | throwError "module {target} is not loaded"
  let names := (env.header.moduleData[idx.toNat]!).constNames.toList
  -- the recursors and `below` machinery generated for the inductive `NormalFormIn`
  let generated := ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow"]
  let pub := names.filter fun n ↦
    !isPrivateName n && !n.isInternalDetail &&
      !(n.components.any fun c ↦ generated.contains c.toString) &&
      !(match n with
        | .str _ s => s.startsWith "match_" || s.startsWith "eq_" || s == "eq_def" ||
            s.startsWith "_"
        | _ => false)
  let unlisted := pub.filter fun n ↦ !headline.contains n
  unless unlisted.isEmpty do
    throwError "[UNLISTED] public declarations of {target} missing from `headline`: {unlisted}"
  let absent := headline.filter fun n ↦ !pub.contains n
  unless absent.isEmpty do
    throwError "[STALE] `headline` names not declared in {target}: {absent}"

/-! ## Minimal imports -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- Substrings no `InfinitaryLogic` module of the closure may contain.  A substring match catches
a module only while its name retains the substring; the guard enforces the present boundary and
does not track renames. -/
def forbiddenModuleSub : List String :=
  ["Scott", "Karp", "ScottProcess", "Descriptive", "Methods", "ModelTheory"]

/-- The exact `InfinitaryLogic` import closure of the module.  Extending it is a deliberate
decision: update this list together with the module docstring. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.QuantifierClass, `InfinitaryLogic.Lomega1omega.QuantifierRank,
   `InfinitaryLogic.Lomega1omega.FiniteQuantification, `InfinitaryLogic.Lomega1omega.InHierarchy]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Lomega1omega.InHierarchy
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦
    forbiddenModuleSub.any fun s ↦ (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  logInfo m!"in-hierarchy regression guard: OK (applied: level 0 on equality and relation atoms \
    and a finite Boolean combination, with quantifiers and countable connectives excluded; the \
    Sigma-in-1 formula `x is one of countably many constants`, not Pi-in-1; infiniteAxiom \
    Pi-in-2 and neither Sigma-in-1 nor Pi-in-1; negation duality; agreement with \
    universalSigned on that formula, on the finitary existential `exists y, x = y` and on every \
    cardGe n, disagreement on a countable conjunction with and without a quantifier over it; \
    rank 0 at level 0 and a Pi-in-1 sentence of rank omega + 1, not a normal form; normal forms \
    at levels 1 and 2 with their omega-multiple rank bounds and their signed classes; closure \
    under castLE, relabel, subst, mapFreeVars, mapLanguage, einf and all at level 1, esup, \
    imp, inf, sup, finite blocks and quantifiers; every public declaration listed; standard \
    axioms; import closure {ilModules})"
