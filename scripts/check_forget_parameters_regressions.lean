/-
Regression guard for forgetting finitely many parameters
(`InfinitaryLogic/Scott/ForgetParameters.lean`).

Every public theorem is *applied*, not only listed for its axioms, and each example checks the
characterization and the bound together, with positive and negative models.

* **Repeated parameters on the pure set.**  Over `c = (1, 1)` in `ℕ`, the pointed sentence of
  the equality patterns characterizes `(ℕ, (1, 1))`.  Its existential closure, through
  `existsTuple_isScott` (the weak hypothesis, from the pointed B2) and through
  `existsTuple_isScott_of_pointed` (the pointed characterization), holds in `ℕ` and `ℤ` and
  fails in `Fin 3`.  The bound: `Σ^in_3` (`isSigmaIn_existsTuple_of_isPiIn` on the `Π^in_2`
  pointed sentence) and **negative**, syntactically: the closure is not in the signed class
  `Σ^in_2` (the pointed sentence under the block is not `Σ^in_2`: its clauses are not
  `Π^in_1`, because of the forth clause `∃y`).
* **The successor graph `(ℕ, S)` with the parameter `0`.**  Over `0`, the element `m` is
  `Σ^in_1`-definable as the `m`-th successor of the parameter
  (`∃y (y = z + m ∧ S(y, x))`, recursively), so the orbits over `0` are `Σ^in_1`-definable
  and `exists_isSigmaIn_three_scottSentence_of_pointed` gives a `Σ^in_3` Scott sentence of
  `(ℕ, S)`; it holds in `ℕ` and fails in `(ℤ, S)` (every point has a predecessor) and in `Fin 3`.
  (Without the parameter, `0` is defined by "no predecessor", a universal formula; that the
  parameter-free orbits are not `Σ^in_1`-definable is not claimed here.)
* **The empty tuple `k = 0`.**  `existsTuple 0 φ` is `φ` (by `rfl`); the block lemma at `k = 0`
  is the identity, and the composite bound turns the `Π^in_2` sentence of the pure set into
  `Σ^in_3`; the semantic closure at `k = 0` of Montalbán's sentence of `ℕ` holds in `ℤ` and
  fails in `Fin 3`.
* **The empty carrier.**  An empty `M` has a parameter tuple only for `k = 0`.  At `k = 0`, the
  closure of the sentence of `Empty` with the nullary `S` true holds in `Fin 0` with `S` true and
  **fails** in `PEmpty` with `S` false (the same-nullary-facts negative of the
  Montalbán-sentence guard) and in the one-point structure; the bound `Σ^in_3` from the
  `Π^in_2` sentence of its atomic diagrams.
* **Explicit carrier universes.**  On `ULift.{1} ℕ` with the parameter `(0)`, the `Σ^in_3`
  Scott sentence from the composition holds in `ULift.{1} ℤ` and fails in `ULift.{1} (Fin 3)`;
  and for a countable pure set in an arbitrary universe `w`.
* **The composition at a general level** (`exists_isSigmaIn_scottSentence_of_pointed`): at
  `α = 1` on the pure set with a parameter, giving `Σ^in_{1+2}`, and at `α = 2` (orbit formulas
  promoted by `IsSigmaIn.mono`), giving `Σ^in_4`; level-`0` equality patterns promoted to
  level `1` give the concrete `Σ^in_3` Scott sentence of `ℕ`.
* **The block lemma both ways** on concrete formulas: `∃x₀ x₁ (x₀ ≠ x₁)` is `Σ^in_1`, and
  `Σ^in_1` of the closure gives back `Σ^in_1` of `x₀ ≠ x₁`.
* **Import closure** of the module: it reaches `Scott/MontalbanComplexity`,
  `Scott/MontalbanSentence` and `Lomega1omega/InHierarchy`, and no Scott-process, descriptive,
  method, model-theory, admissible or conditional module.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_forget_parameters_regressions.lean
-/
import InfinitaryLogic.Scott.ForgetParameters
import InfinitaryLogic.Scott.FiniteMatching

open Lean FirstOrder FirstOrder.Language BoundedFormulaω

universe u v w

noncomputable section

namespace ForgetParametersGuard

attribute [local instance] Language.emptyStructure

/-! ### Finite conjunctions and equality patterns -/

section Patterns

variable {L : Language.{u, v}}

/-- A finite conjunction, as a fold of `⊓`; it stays at level `0`. -/
def finConj {β : Type*} (l : List (L.Formulaω β)) : L.Formulaω β := l.foldr (· ⊓ ·) ⊤

theorem realize_finConj {β : Type*} {M : Type*} [L.Structure M] (l : List (L.Formulaω β))
    (v : β → M) : (finConj l).Realize v ↔ ∀ φ ∈ l, φ.Realize v := by
  induction l with
  | nil => simp [finConj, Formulaω.realize_def]
  | cons φ l ih => simp [finConj, Formulaω.realize_inf, ← ih]

theorem inSigned_finConj {β : Type*} (a : Ordinal.{0}) (s : Bool) (l : List (L.Formulaω β)) :
    inSigned a s (finConj l) ↔ ∀ φ ∈ l, inSigned a s φ := by
  induction l with
  | nil => simp [finConj]
  | cons φ l ih => simp [finConj, ← ih]

/-- The atom `xᵢ = xⱼ`. -/
def eqAtom {n : ℕ} (i j : Fin n) : L.Formulaω (Fin n) :=
  BoundedFormulaω.equal (Term.var (Sum.inl i)) (Term.var (Sum.inl j))

theorem realize_eqAtom {M : Type*} [L.Structure M] {n : ℕ} (i j : Fin n) (b : Fin n → M) :
    (eqAtom (L := L) i j).Realize b ↔ b i = b j := by
  simp [eqAtom, Formulaω.realize_def]

/-- The **equality pattern** of a tuple: the finite conjunction of `xᵢ = xⱼ` or `xᵢ ≠ xⱼ`. -/
def eqPattern {X : Type*} {n : ℕ} (a : Fin n → X) : L.Formulaω (Fin n) := by
  classical
  exact finConj (List.ofFn fun i ↦ finConj (List.ofFn fun j ↦
    if a i = a j then eqAtom i j else (eqAtom i j).not))

theorem realize_eqPattern {X M : Type*} [L.Structure M] {n : ℕ} (a : Fin n → X)
    (b : Fin n → M) : (eqPattern (L := L) a).Realize b ↔ ∀ i j, a i = a j ↔ b i = b j := by
  classical
  simp only [eqPattern, realize_finConj, List.forall_mem_ofFn_iff]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  split_ifs with h
  · simp [realize_eqAtom, h]
  · simp [Formulaω.realize_not, realize_eqAtom, h]

/-- An equality pattern is level `0`, at both signs. -/
theorem inSigned_eqPattern {X : Type*} {n : ℕ} (a : Fin n → X) (s : Bool) :
    inSigned 0 s (eqPattern (L := L) a) := by
  classical
  simp only [eqPattern, inSigned_finConj, List.forall_mem_ofFn_iff]
  intro i j
  split_ifs
  · exact trivial
  · exact (inSigned_not 0 s _).2 trivial

end Patterns

/-! ### Pure sets with parameters -/

section Pure

/-- In the empty language, a common equality pattern is witnessed by a permutation. -/
theorem pure_homogeneous {X : Type w} {n : ℕ} (a b : Fin n → X)
    (h : ∀ i j, a i = a j ↔ b i = b j) : ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  obtain ⟨e, he, -, -⟩ := FiberAssembly.exists_equiv_of_matching
    (E := fun (_ _ : X) ↦ True) ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩ n a b h
    (fun _ ↦ trivial)
  exact ⟨{ toEquiv := e }, funext he⟩

/-- An equivalence of carriers is an isomorphism of pure sets. -/
def pureEquiv {X Y : Type*} (e : X ≃ Y) : X ≃[Language.empty] Y := { toEquiv := e }

/-- The equality pattern of `a` defines its orbit in a pure set. -/
theorem pure_orbit {X : Type w} {n : ℕ} (a b : Fin n → X) :
    (eqPattern (L := Language.empty) a).Realize b ↔
      ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  rw [realize_eqPattern]
  refine ⟨pure_homogeneous a b, fun ⟨e, he⟩ i j ↦ ?_⟩
  subst he
  exact e.injective.eq_iff.symm

/-- Composition commutes with appending. -/
theorem comp_append' {α β : Type*} (f : α → β) {k n : ℕ} (c : Fin k → α) (a : Fin n → α) :
    f ∘ Fin.append c a = Fin.append (f ∘ c) (f ∘ a) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- Equality patterns of `c⌢a`, over the parameters `c`. -/
abbrev pureΦc {X : Type w} {k : ℕ} (c : Fin k → X) :
    ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin (k + n)) :=
  fun _ a ↦ eqPattern (Fin.append c a)

/-- The pointed equality patterns define the orbits over `c`. -/
theorem pure_orbitPointed {X : Type w} {k n : ℕ} (c : Fin k → X) (a b : Fin n → X) :
    (pureΦc c n a).Realize (Fin.append c b) ↔
      ∃ e : X ≃[Language.empty] X, ⇑e ∘ c = c ∧ ⇑e ∘ a = b := by
  rw [pure_orbit]
  refine ⟨fun ⟨e, he⟩ ↦ ⟨e, funext fun j ↦ ?_, funext fun i ↦ ?_⟩, fun ⟨e, hc, ha⟩ ↦
    ⟨e, by rw [comp_append', hc, ha]⟩⟩
  · simpa [comp_append'] using congrFun he (Fin.castAdd n j)
  · simpa [comp_append'] using congrFun he (Fin.natAdd k i)

theorem pureΦc_isSigmaIn {X : Type w} {k : ℕ} (c : Fin k → X) (a : Ordinal.{0}) :
    ∀ n b, IsSigmaIn a (pureΦc c n b) :=
  fun _ _ ↦ IsSigmaIn.mono zero_le (inSigned_eqPattern _ false)

/-- `Fin 3` is not isomorphic to `ℕ` as a pure set (nor as any structure). -/
theorem not_equiv_fin3 {L : Language.{u, v}} [L.Structure ℕ] [L.Structure (Fin 3)] :
    ¬ Nonempty (ℕ ≃[L] Fin 3) := fun ⟨e⟩ ↦
  not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm : Finite ℕ)

/-- The repeated parameters `(1, 1)`. -/
abbrev c11 : Fin 2 → ℕ := ![1, 1]

/-- The pointed sentence over `(1, 1)`. -/
abbrev φ11 : Language.empty.Formulaω (Fin 2) := montalbanSentencePointed c11 (pureΦc c11)

/-- **Semantic closure, weak hypothesis, repeated parameters.**  The pointed sentence holds of
`(1, 1)` (B1) and a realizing tuple gives an isomorphism (B2); the closure holds in `ℕ` and `ℤ`
and fails in `Fin 3`. -/
theorem repeated_semantic :
    (existsTuple 2 φ11).realize_as_sentence ℕ ∧ (existsTuple 2 φ11).realize_as_sentence ℤ ∧
      ¬ (existsTuple 2 φ11).realize_as_sentence (Fin 3) := by
  have hS := existsTuple_isScott c11 φ11
    (montalbanSentencePointed_self fun n a b ↦ pure_orbitPointed c11 a b)
    fun N _ _ d hd ↦ (exists_equiv_of_realize_montalbanSentencePointed c11 _ N d hd).elim
      fun e _ ↦ ⟨e⟩
  exact ⟨hS.1, (hS.2 ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩,
    fun h ↦ not_equiv_fin3 ((hS.2 (Fin 3)).1 h)⟩

/-- **Semantic closure from the pointed characterization**, same example. -/
theorem repeated_semantic_pointed :
    (existsTuple 2 φ11).realize_as_sentence ℕ ∧ (existsTuple 2 φ11).realize_as_sentence ℤ ∧
      ¬ (existsTuple 2 φ11).realize_as_sentence (Fin 3) := by
  have hS := existsTuple_isScott_of_pointed c11 φ11
    (montalbanSentencePointed_characterizes fun n a b ↦ pure_orbitPointed c11 a b)
  exact ⟨hS.1, (hS.2 ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩,
    fun h ↦ not_equiv_fin3 ((hS.2 (Fin 3)).1 h)⟩

/-- **The bound, repeated parameters**: the closure is `Σ^in_3`. -/
theorem repeated_isSigmaIn_three : IsSigmaIn 3 (existsTuple 2 φ11) := by
  have h := isSigmaIn_existsTuple_of_isPiIn (k := 2)
    (isPiIn_montalbanSentencePointed (α := 1) le_rfl c11 (pureΦc_isSigmaIn c11 1))
  have h3 : (1 : Ordinal.{0}) + 2 = 3 := by
    rw [← one_add_one_eq_two, ← add_assoc, one_add_one_eq_two, two_add_one_eq_three]
  rwa [h3] at h

/-- **Negative, syntactic:** the closure is not in the signed class `Σ^in_2`.  Through the block
(`isSigmaIn_existsTuple_iff`, read backwards), the pointed sentence would be `Σ^in_2`, so its
countable conjunction of clauses would be `Π^in_1`; the forth clause at the empty tuple contains
`∃y`, which is `Π^in_1` only through `Σ^in_b` with `1 ≤ b < 1`. -/
theorem repeated_not_isSigmaIn_two : ¬ IsSigmaIn 2 (existsTuple 2 φ11) := by
  let _ : Encodable (Σ n, Fin n → ℕ) := Encodable.ofCountable _
  let _ : Encodable ℕ := Encodable.ofCountable ℕ
  intro h
  have hφ := (isSigmaIn_existsTuple_iff one_le_two 2 φ11).1 h
  obtain ⟨b, hb2, hb1, hcl⟩ := ((inSigned_inf _ _ _ _).1 hφ).2
  have hb : b = 1 := by
    refine le_antisymm ?_ hb1
    rw [← Order.lt_add_one_iff, one_add_one_eq_two]
    exact hb2
  subst hb
  have hcl0 := hcl (Encodable.encode (⟨0, Fin.elim0⟩ : Σ n, Fin n → ℕ))
  simp only [Encodable.encodek] at hcl0
  have hbody := ((inSigned_imp _ _ _ _).1 hcl0).2
  have hforth := ((isPiIn_einf_iff _).1 ((inSigned_inf _ _ _ _).1
    ((inSigned_inf _ _ _ _).1 hbody).1).2).2 0
  obtain ⟨b, hb, hb1, -⟩ := (inSigned_ex_true _ _).1 hforth
  exact absurd (hb1.trans_lt hb) (lt_irrefl 1)

end Pure

/-! ### The successor graph with one parameter -/

section Succ

/-- One binary relation symbol, read as the successor graph. -/
inductive SuccRel : ℕ → Type
  /-- `S(x, y)`: `y` is the successor of `x`. -/
  | S : SuccRel 2

/-- The language of the successor graph. -/
abbrev succLang : Language.{0, 0} := ⟨fun _ ↦ Empty, SuccRel⟩

instance : Countable (Σ l, succLang.Relations l) :=
  Function.Injective.countable (f := Sigma.fst) fun
    | ⟨_, .S⟩, ⟨_, .S⟩, _ => rfl

/-- `(ℕ, S)`. -/
instance succNat : succLang.Structure ℕ where
  funMap f := Empty.elim f
  RelMap | .S, x => x 1 = x 0 + 1

/-- `(ℤ, S)`. -/
instance succInt : succLang.Structure ℤ where
  funMap f := Empty.elim f
  RelMap | .S, x => x 1 = x 0 + 1

/-- `Fin 3` with the empty relation. -/
instance succFin3 : succLang.Structure (Fin 3) where
  funMap f := Empty.elim f
  RelMap | .S, _ => False

/-- The atom `S(xᵢ, xⱼ)`. -/
def sAtom {n : ℕ} (i j : Fin n) : succLang.Formulaω (Fin n) :=
  BoundedFormulaω.rel SuccRel.S ![Term.var (Sum.inl i), Term.var (Sum.inl j)]

/-- `S(xᵢ, xⱼ)` in `ℕ`. -/
theorem realize_sAtom {n : ℕ} (i j : Fin n) (b : Fin n → ℕ) :
    (sAtom i j).Realize b ↔ b j = b i + 1 := by
  simp only [sAtom, Formulaω.realize_def, BoundedFormulaω.realize_rel]
  exact Iff.rfl

/-- `x₁ = x₀ + m`, over the variables `(x₀, x₁)`: recursively `∃y (y = x₀ + m ∧ S(y, x₁))`. -/
def succForm : ℕ → succLang.Formulaω (Fin 2)
  | 0 => BoundedFormulaω.equal (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))
  | m + 1 => existsLastVar ((succForm m).mapFreeVars ![0, 2] ⊓ sAtom 2 1)

/-- `succForm m` defines `x₁ = x₀ + m` in `ℕ`. -/
theorem realize_succForm : ∀ (m : ℕ) (v : Fin 2 → ℕ), (succForm m).Realize v ↔ v 1 = v 0 + m
  | 0, v => by
    simp only [succForm, Formulaω.realize_def, BoundedFormulaω.realize_equal, Term.realize_var,
      Sum.elim_inl, add_zero]
    exact eq_comm
  | m + 1, v => by
    simp only [succForm, realize_existsLastVar, Formulaω.realize_inf, realize_sAtom]
    have ih := realize_succForm m
    simp only [Formulaω.realize_def] at ih
    simp only [Formulaω.realize_def, realize_mapFreeVars]
    have hc : ∀ x : ℕ, (Fin.snoc v x : Fin 3 → ℕ) ∘ ![0, 2] = ![v 0, x] := fun x ↦ by
      funext i; match i with | 0 => rfl | 1 => rfl
    have h1 : ∀ x : ℕ, (Fin.snoc v x : Fin 3 → ℕ) 1 = v 1 := fun _ ↦ rfl
    have h2 : ∀ x : ℕ, (Fin.snoc v x : Fin 3 → ℕ) 2 = x := fun _ ↦ rfl
    simp only [hc, h1, h2, ih, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨x, rfl, h⟩
      omega
    · intro h
      exact ⟨v 0 + m, rfl, by omega⟩

/-- Each `succForm m` is `Σ^in_1`: atoms under `∃` and `⊓`. -/
theorem succForm_isSigmaIn_one : ∀ m, IsSigmaIn 1 (succForm m)
  | 0 => trivial
  | m + 1 => (isSigmaIn_existsLastVar_iff le_rfl).2
      ((inSigned_inf _ _ _ _).2
        ⟨(inSigned_mapFreeVars _ _ _ _).2 (succForm_isSigmaIn_one m), trivial⟩)

/-- The orbit formula of `a` over the parameter `z`: `⋀ᵢ xᵢ = z + aᵢ`. -/
def succΦ : ∀ n, (Fin n → ℕ) → succLang.Formulaω (Fin (1 + n)) := fun n a ↦
  finConj (List.ofFn fun i ↦ (succForm (a i)).mapFreeVars ![Fin.castAdd n 0, Fin.natAdd 1 i])

/-- Over the parameter `0`, `succΦ n a` holds exactly at `a`. -/
theorem realize_succΦ {n : ℕ} (a b : Fin n → ℕ) :
    (succΦ n a).Realize (Fin.append ![0] b) ↔ b = a := by
  simp only [succΦ, realize_finConj, List.forall_mem_ofFn_iff]
  have hv : ∀ i, (Fin.append ![0] b ∘ ![Fin.castAdd n 0, Fin.natAdd 1 i] : Fin 2 → ℕ) = ![0, b i] :=
    fun i ↦ by funext j; match j with | 0 => simp | 1 => simp
  simp only [Formulaω.realize_def, realize_mapFreeVars, hv]
  simp only [← Formulaω.realize_def, realize_succForm, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add]
  exact ⟨fun h ↦ funext h, fun h i ↦ congrFun h i⟩

/-- An automorphism of `(ℕ, S)` fixing `0` is the identity. -/
theorem succ_rigid (e : ℕ ≃[succLang] ℕ) (h0 : e 0 = 0) : ∀ m, e m = m
  | 0 => h0
  | m + 1 => by
    have h := (e.map_rel SuccRel.S ![m, m + 1]).2 (show m + 1 = m + 1 from rfl)
    change e (m + 1) = e m + 1 at h
    rw [h, succ_rigid e h0 m]

/-- The formulas `succΦ` define the orbits over `0` (which are singletons). -/
theorem succ_isOrbit {n : ℕ} (a b : Fin n → ℕ) :
    (succΦ n a).Realize (Fin.append ![0] b) ↔
      ∃ e : ℕ ≃[succLang] ℕ, ⇑e ∘ ![0] = ![0] ∧ ⇑e ∘ a = b := by
  rw [realize_succΦ]
  refine ⟨fun h ↦ ⟨Language.Equiv.refl _ _, rfl, h.symm⟩, fun ⟨e, hc, ha⟩ ↦ ?_⟩
  have h0 : e 0 = 0 := congrFun hc 0
  rw [← ha]
  exact funext fun i ↦ succ_rigid e h0 (a i)

/-- **The successor graph with the parameter `0`**: a `Σ^in_3` Scott sentence of `(ℕ, S)`, from
`Σ^in_1` orbit formulas over `0`.  It holds in `ℕ` and fails in `(ℤ, S)` (the predecessor of the
image of `0` would be carried back to a predecessor of `0`) and in `Fin 3`. -/
theorem succ_scott :
    ∃ σ : succLang.Formulaω (Fin 0), IsSigmaIn 3 σ ∧ σ.realize_as_sentence ℕ ∧
      ¬ σ.realize_as_sentence ℤ ∧ ¬ σ.realize_as_sentence (Fin 3) := by
  obtain ⟨σ, hσ, hN⟩ := exists_isSigmaIn_three_scottSentence_of_pointed (M := ℕ) ![0]
    fun n a ↦ ⟨succΦ n a, (inSigned_finConj _ _ _).2 fun φ hφ ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
      exact (inSigned_mapFreeVars _ _ _ _).2 (succForm_isSigmaIn_one _), succ_isOrbit a⟩
  refine ⟨σ, hσ, (hN ℕ).2 ⟨Language.Equiv.refl _ _⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨e⟩ := (hN ℤ).1 h
    have h1 := (e.map_rel SuccRel.S ![e.symm (e 0 - 1), 0]).1
      (show e 0 = e (e.symm (e 0 - 1)) + 1 by rw [e.apply_symm_apply]; omega)
    change (0 : ℕ) = e.symm (e 0 - 1) + 1 at h1
    omega
  · exact not_equiv_fin3 ((hN (Fin 3)).1 h)

end Succ

/-! ### The empty tuple -/

section EmptyTuple

/-- The equality-pattern family of a pure set, without parameters. -/
abbrev pureΦ (X : Type w) : ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin n) :=
  fun _ a ↦ eqPattern a

/-- **The empty block is the formula itself**, by definition. -/
theorem existsTuple_zero {L : Language.{u, v}} (φ : L.Formulaω (Fin 0)) :
    existsTuple 0 φ = φ :=
  rfl

/-- **Semantic closure at `k = 0`**: the closure of Montalbán's sentence of `ℕ` over the empty
tuple holds in `ℕ` and `ℤ` and fails in `Fin 3`. -/
theorem zero_semantic :
    (existsTuple 0 (montalbanSentence (pureΦ ℕ))).realize_as_sentence ℕ ∧
      (existsTuple 0 (montalbanSentence (pureΦ ℕ))).realize_as_sentence ℤ ∧
      ¬ (existsTuple 0 (montalbanSentence (pureΦ ℕ))).realize_as_sentence (Fin 3) := by
  have hS := existsTuple_isScott (Fin.elim0 : Fin 0 → ℕ) (montalbanSentence (pureΦ ℕ))
    (montalbanSentence_self fun _ a b ↦ pure_orbit a b) fun N _ _ d hd ↦
      nonempty_equiv_of_realize_montalbanSentence _ N (by rwa [Subsingleton.elim d Fin.elim0] at hd)
  exact ⟨hS.1, (hS.2 ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩,
    fun h ↦ not_equiv_fin3 ((hS.2 (Fin 3)).1 h)⟩

/-- **Syntactic closure at `k = 0`**: the block lemma is the identity, and the composite bound
turns the `Π^in_2` sentence of `ℕ` into `Σ^in_3`. -/
theorem zero_syntactic :
    (IsSigmaIn 2 (existsTuple 0 (montalbanSentence (pureΦ ℕ))) ↔
        IsSigmaIn 2 (montalbanSentence (pureΦ ℕ))) ∧
      IsSigmaIn (1 + 2) (existsTuple 0 (montalbanSentence (pureΦ ℕ))) :=
  ⟨isSigmaIn_existsTuple_iff one_le_two 0 _, isSigmaIn_existsTuple_of_isPiIn
    (isPiIn_montalbanSentence le_rfl fun _ a ↦ IsSigmaIn.mono zero_le (inSigned_eqPattern a false))⟩

end EmptyTuple

/-! ### The empty carrier -/

section EmptyCarrier

/-- One nullary relation symbol `S`. -/
inductive NullRel : ℕ → Type
  /-- The nullary symbol. -/
  | S : NullRel 0

/-- The language with one nullary symbol. -/
abbrev nullLang : Language.{0, 0} := ⟨fun _ ↦ Empty, NullRel⟩

instance : Countable (Σ l, nullLang.Relations l) :=
  Function.Injective.countable (f := Sigma.fst) fun
    | ⟨_, .S⟩, ⟨_, .S⟩, _ => rfl

/-- The structure with nullary fact `s`. -/
abbrev nullStr (X : Type*) (s : Prop) : nullLang.Structure X where
  funMap f := Empty.elim f
  RelMap | .S, _ => s

instance : nullLang.Structure Empty := nullStr Empty True
instance : nullLang.Structure (Fin 0) := nullStr (Fin 0) True
instance : nullLang.Structure PEmpty.{1} := nullStr PEmpty False
instance : nullLang.Structure Unit := nullStr Unit True

/-- An empty carrier has a parameter tuple only of length `0`. -/
theorem empty_params {k : ℕ} (c : Fin k → Empty) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k => exact (c 0).elim

/-- The atom `S`, at every tuple length: the orbit formulas of `Empty` (only the empty tuple). -/
abbrev emptyΦ : ∀ n, (Fin n → Empty) → nullLang.Formulaω (Fin n) :=
  fun _ _ ↦ BoundedFormulaω.rel NullRel.S Fin.elim0

theorem empty_isOrbit : IsOrbitFormulaFamily (L := nullLang) emptyΦ := fun n a b ↦ by
  cases n with
  | zero =>
    refine ⟨fun _ ↦ ⟨Language.Equiv.refl _ _, Subsingleton.elim _ _⟩, fun _ ↦ ?_⟩
    simp only [Formulaω.realize_def, BoundedFormulaω.realize_rel]
    exact trivial
  | succ n => exact (a 0).elim

/-- `Empty` and `Fin 0`, both with `S` true, are isomorphic. -/
def emptyFin0 : Empty ≃[nullLang] Fin 0 where
  toEquiv := Equiv.equivOfIsEmpty Empty (Fin 0)
  map_rel' := fun {_} r _ ↦ by cases r; exact Iff.rfl

/-- **Semantic closure on the empty carrier** (`k = 0`): the closure of the sentence of `Empty`
(with `S` true) holds in `Fin 0` (with `S` true) and fails in `PEmpty` (empty, with `S` false)
and in the one-point structure. -/
theorem empty_semantic :
    (existsTuple 0 (montalbanSentence emptyΦ)).realize_as_sentence (Fin 0) ∧
      ¬ (existsTuple 0 (montalbanSentence emptyΦ)).realize_as_sentence PEmpty.{1} ∧
      ¬ (existsTuple 0 (montalbanSentence emptyΦ)).realize_as_sentence Unit := by
  have hS := existsTuple_isScott (Fin.elim0 : Fin 0 → Empty) (montalbanSentence emptyΦ)
    (montalbanSentence_self empty_isOrbit) fun N _ _ d hd ↦
      nonempty_equiv_of_realize_montalbanSentence _ N (by rwa [Subsingleton.elim d Fin.elim0] at hd)
  refine ⟨(hS.2 _).2 ⟨emptyFin0⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨e⟩ := (hS.2 _).1 h
    exact (e.map_rel NullRel.S (Fin.elim0 : Fin 0 → Empty)).2 trivial
  · obtain ⟨e⟩ := (hS.2 _).1 h
    exact (e.symm ()).elim

/-- **The bound on the empty carrier**: the orbit formulas are atoms (level `0`), the sentence is
`Π^in_2`, and the closure over the empty tuple is `Σ^in_3`. -/
theorem empty_isSigmaIn_three : IsSigmaIn (1 + 2) (existsTuple 0 (montalbanSentence emptyΦ)) :=
  isSigmaIn_existsTuple_of_isPiIn (isPiIn_montalbanSentence le_rfl fun _ _ ↦ trivial)

end EmptyCarrier

/-! ### The composition, explicit universes, and the block lemma -/

section Composition

/-- **The composition at a general level** on `ℕ` with the parameter `3`: at `α = 1` it gives
`Σ^in_{1+2}`, at `α = 2` (orbit formulas promoted) `Σ^in_{2+2}`; both sentences hold in `ℤ` and
fail in `Fin 3`. -/
theorem general_levels :
    (∃ σ : Language.empty.Formulaω (Fin 0), IsSigmaIn (1 + 2) σ ∧
      σ.realize_as_sentence ℤ ∧ ¬ σ.realize_as_sentence (Fin 3)) ∧
    ∃ σ : Language.empty.Formulaω (Fin 0), IsSigmaIn (2 + 2) σ ∧
      σ.realize_as_sentence ℤ ∧ ¬ σ.realize_as_sentence (Fin 3) := by
  obtain ⟨σ₁, h₁, hN₁⟩ := exists_isSigmaIn_scottSentence_of_pointed (α := 1) le_rfl
    (![3] : Fin 1 → ℕ) fun n a ↦ ⟨_, pureΦc_isSigmaIn _ 1 n a, pure_orbitPointed _ a⟩
  obtain ⟨σ₂, h₂, hN₂⟩ := exists_isSigmaIn_scottSentence_of_pointed (α := 2) one_le_two
    (![3] : Fin 1 → ℕ) fun n a ↦ ⟨_, pureΦc_isSigmaIn _ 2 n a, pure_orbitPointed _ a⟩
  exact ⟨⟨σ₁, h₁, (hN₁ ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩,
      fun h ↦ not_equiv_fin3 ((hN₁ (Fin 3)).1 h)⟩,
    σ₂, h₂, (hN₂ ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩,
      fun h ↦ not_equiv_fin3 ((hN₂ (Fin 3)).1 h)⟩

/-- **A concrete `Σ^in_3` Scott sentence of `ℕ`** from the equality patterns over the repeated
parameters `(1, 1)`, level `0` promoted to level `1`; it holds in `ℕ` and `ℤ` and fails in
`Fin 3`. -/
theorem nat_sigma_three :
    ∃ σ : Language.empty.Formulaω (Fin 0), IsSigmaIn 3 σ ∧ σ.realize_as_sentence ℕ ∧
      σ.realize_as_sentence ℤ ∧ ¬ σ.realize_as_sentence (Fin 3) := by
  obtain ⟨σ, hσ, hN⟩ := exists_isSigmaIn_three_scottSentence_of_pointed c11
    fun n a ↦ ⟨pureΦc c11 n a, IsSigmaIn.mono zero_le_one (inSigned_eqPattern _ false),
      pure_orbitPointed c11 a⟩
  exact ⟨σ, hσ, (hN ℕ).2 ⟨pureEquiv (Equiv.refl ℕ)⟩, (hN ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩,
    fun h ↦ not_equiv_fin3 ((hN (Fin 3)).1 h)⟩

/-- **`Type 1` carrier, explicit universes**: on `ULift.{1} ℕ` with the parameter `(0)`, the
semantic closure (`existsTuple_isScott.{0, 0, 1}`) and the `Σ^in_3` Scott sentence of the
composition, which holds in `ULift.{1} ℤ` and fails in `ULift.{1} (Fin 3)`. -/
theorem ulift_scott :
    (existsTuple 1 (montalbanSentencePointed (![ULift.up 0] : Fin 1 → ULift.{1} ℕ)
        (pureΦc ![ULift.up 0]))).realize_as_sentence (ULift.{1} ℤ) ∧
      ∃ σ : Language.empty.Formulaω (Fin 0), IsSigmaIn 3 σ ∧
        σ.realize_as_sentence (ULift.{1} ℤ) ∧ ¬ σ.realize_as_sentence (ULift.{1} (Fin 3)) := by
  have hZ : Nonempty (ULift.{1} ℕ ≃[Language.empty] ULift.{1} ℤ) :=
    ⟨pureEquiv (Equiv.ulift.trans (Equiv.intEquivNat.symm.trans Equiv.ulift.symm))⟩
  have hF : ¬ Nonempty (ULift.{1} ℕ ≃[Language.empty] ULift.{1} (Fin 3)) := fun ⟨e⟩ ↦
    not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm : Finite (ULift ℕ))
  have hS := existsTuple_isScott.{0, 0, 1} (![ULift.up 0] : Fin 1 → ULift.{1} ℕ) _
    (montalbanSentencePointed_self fun n a b ↦ pure_orbitPointed _ a b)
    fun N _ _ d hd ↦ (exists_equiv_of_realize_montalbanSentencePointed _ _ N d hd).elim
      fun e _ ↦ ⟨e⟩
  obtain ⟨σ, hσ, hN⟩ := exists_isSigmaIn_three_scottSentence_of_pointed.{0, 0, 1}
    (![ULift.up 0] : Fin 1 → ULift.{1} ℕ) fun n a ↦
      ⟨_, pureΦc_isSigmaIn _ 1 n a, pure_orbitPointed _ a⟩
  exact ⟨(hS.2 _).2 hZ, σ, hσ, (hN _).2 hZ, fun h ↦ hF ((hN _).1 h)⟩

/-- **Universe-polymorphic carrier**: a countable pure set in any universe `w` with one
parameter has a `Σ^in_3` Scott sentence. -/
theorem pure_univ (X : Type w) [Countable X] (x : X) :
    ∃ σ : Language.empty.Formulaω (Fin 0), IsSigmaIn 3 σ ∧
      ∀ (N : Type w) [Language.empty.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (X ≃[Language.empty] N) :=
  exists_isSigmaIn_three_scottSentence_of_pointed (![x] : Fin 1 → X) fun n a ↦
    ⟨_, pureΦc_isSigmaIn _ 1 n a, pure_orbitPointed _ a⟩

/-- `x₀ ≠ x₁`. -/
def neq01 : Language.empty.Formulaω (Fin 2) := (eqAtom 0 1).not

/-- **The block lemma both ways**: `∃x₀ x₁ (x₀ ≠ x₁)` is `Σ^in_1`, and `Σ^in_1` of the closure
gives `Σ^in_1` of `x₀ ≠ x₁` back.  **Negative:** the closure is not level `0`, where no
quantifier is admitted, so the hypothesis `1 ≤ α` of the block lemma cannot be dropped. -/
theorem block_both_ways :
    IsSigmaIn 1 (existsTuple 2 neq01) ∧ (IsSigmaIn 1 (existsTuple 2 neq01) → IsSigmaIn 1 neq01) ∧
      ¬ IsSigmaIn 0 (existsTuple 2 neq01) :=
  ⟨(isSigmaIn_existsTuple_iff le_rfl 2 _).2 ((inSigned_not _ _ _).2 trivial),
    (isSigmaIn_existsTuple_iff le_rfl 2 _).1,
    fun h ↦ absurd ((inSigned_ex_false _ _).1 h).1 (by simp)⟩

end Composition

end ForgetParametersGuard

/-! ### Import closure and axiom audit -/

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

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.ScottProcess, `InfinitaryLogic.Descriptive, `InfinitaryLogic.Methods,
   `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional,
   `InfinitaryLogic.WIP]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.ForgetParameters
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Scott.MontalbanComplexity, `InfinitaryLogic.Scott.MontalbanSentence,
      `InfinitaryLogic.Lomega1omega.InHierarchy] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let hits := cl.toList.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-- The public declarations of the module. -/
def moduleDecls : List Name :=
  [`existsTuple_isScott, `existsTuple_isScott_of_pointed, `isSigmaIn_existsTuple_iff,
   `isSigmaIn_existsTuple_of_isPiIn, `exists_isSigmaIn_scottSentence_of_pointed,
   `exists_isSigmaIn_three_scottSentence_of_pointed].map (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`realize_eqPattern, `inSigned_eqPattern, `pure_orbit, `pure_orbitPointed,
   `repeated_semantic, `repeated_semantic_pointed, `repeated_isSigmaIn_three,
   `repeated_not_isSigmaIn_two, `realize_succForm, `succForm_isSigmaIn_one, `realize_succΦ,
   `succ_rigid, `succ_isOrbit, `succ_scott, `existsTuple_zero, `zero_semantic, `zero_syntactic,
   `empty_params, `empty_isOrbit, `empty_semantic, `empty_isSigmaIn_three, `general_levels,
   `nat_sigma_three, `ulift_scott, `pure_univ, `block_both_ways].map
    (`ForgetParametersGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in moduleDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Forget-parameters regression guard: OK (applied: the semantic closure from the weak \
    hypothesis and from the pointed characterization on the pure set over the repeated \
    parameters (1, 1), holding in N and Z and failing in Fin 3, with the bound Sigma-in 3 and \
    the closure not in the signed class Sigma-in 2; the successor graph on N with the parameter \
    0, Sigma-in 1 orbit formulas over 0 and a Sigma-in 3 Scott sentence holding in N and failing \
    in (Z, S) and Fin 3; the empty tuple, where the closure is the formula itself, in both \
    layers; the empty carrier, parameters only for k = 0, the closure holding in Fin 0 with S \
    true and failing in PEmpty with S false and in one point, bound Sigma-in 3; the composition \
    at alpha = 1 and alpha = 2 and the concrete Sigma-in 3 Scott sentence of N; the Type 1 \
    carrier ULift N with explicit universes, holding in ULift Z and failing in ULift (Fin 3); \
    a pure set in arbitrary universes; the block lemma both ways and not at level 0; import \
    closure without Scott-process, descriptive, method, model-theory, admissible or conditional \
    modules; standard axioms)"
