/-
Regression guard for the complexity bound on Montalbán's explicit Scott sentence
(`InfinitaryLogic/Scott/MontalbanComplexity.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **Components on concrete formulas.**  The atomic diagram of `(0, 1)` in the pure set is
  `Π^in_1` and `Π^in_2`; **negative:** it is not `Π^in_0` (a countable conjunction is never
  level `0`) and not `Σ^in_1`.  The quantifier steps `forallLastVar`/`existsLastVar`, the
  closures `forallTuple`/`forallTupleFrom` and a clause body on `x₀ ≠ x₁`.
* **Equality patterns.**  A finitary equality pattern `eqPattern a` (a finite conjunction, so
  level `0`) defines the orbit of `a` in a pure set, without and with parameters.
* **B3 at `α = 1` on the infinite pure set**: the equality-pattern family is level `0`, hence
  `Σ^in_1` by monotonicity, and the sentence is `Π^in_2`.  **F2, syntactically:** the same
  sentence is *not* in the signed class `Π^in_1` (its forth clause `∃y` is not `Π^in_1`).
  The semantic impossibility of a `Π^in_1` Scott sentence is not claimed.
* **The Scott-sentence corollaries on the pure set**: `ℕ` has a `Π^in_2` Scott sentence, from
  `α = 1` and from the level-`0` lemma; it holds in `ℤ` and fails in `Fin 3`.  The same on the
  `Type 1` carrier `ULift.{1} ℕ`, and for a countable pure set in an arbitrary universe.
* **A genuine countable disjunction at level 1.**  On `ℕ ⊕ ℕ` with countably many unary labels
  `P i`, every `P i` true exactly at the left points: the orbit of a left point is "has some
  label", `⋁ᵢ Pᵢ(x)`, and the orbit formula family carries this countable `esup`.  Its formulas
  are `Σ^in_1` through `isSigmaIn_esup` at level `1`, and **not** level `0`; B3 gives `Π^in_2`
  and the corollary a `Π^in_2` Scott sentence, which fails in `ℕ` with every point labelled.
  (Any countable disjunction defining a single orbit is semantically redundant: each disjunct
  defines an automorphism-invariant subset of the orbit.  The regression is about the syntax the
  classification must traverse, which here contains the `esup`.)
* **Pointed, repeated parameters**: over `c = (1, 1)` in `ℕ`, the pointed sentence of the
  equality patterns is `Π^in_2` (B3, pointed), and the pointed corollary gives a `Π^in_2`
  formula holding at `(4, 4)` and failing at `(4, 5)`.
* **Import closure** of the module: it reaches `Scott/MontalbanSentence` and
  `Lomega1omega/InHierarchy`, and no Scott-process, descriptive, method, model-theory,
  admissible or conditional module.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_montalban_complexity_regressions.lean
-/
import InfinitaryLogic.Scott.MontalbanComplexity
import InfinitaryLogic.Scott.FiniteMatching

open Lean FirstOrder FirstOrder.Language BoundedFormulaω

universe u v w

noncomputable section

namespace MontalbanComplexityGuard

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

/-! ### Pure sets -/

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

/-- The equality-pattern family of a pure set. -/
abbrev pureΦ (X : Type w) : ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin n) :=
  fun _ a ↦ eqPattern a

theorem pureΦ_isSigmaIn_one (X : Type w) : ∀ n a, IsSigmaIn 1 (pureΦ X n a) :=
  fun _ a ↦ IsSigmaIn.mono zero_le_one (inSigned_eqPattern a false)

/-- **B3 at `α = 1`** on the pure set `ℕ`: the sentence is `Π^in_2`. -/
theorem pure_isPiIn_two : IsPiIn 2 (montalbanSentence (pureΦ ℕ)) := by
  have := isPiIn_montalbanSentence le_rfl (pureΦ_isSigmaIn_one ℕ)
  rwa [one_add_one_eq_two] at this

/-- **F2, syntactically**: the same sentence is not in the signed class `Π^in_1`.  Its forth
clause at the empty tuple, `⋀_m ∃y …`, contains an existential quantifier, which is `Π^in_1`
only through `Σ^in_b` with `1 ≤ b < 1`. -/
theorem pure_not_isPiIn_one : ¬ IsPiIn 1 (montalbanSentence (pureΦ ℕ)) := by
  let _ : Encodable (Σ n, Fin n → ℕ) := Encodable.ofCountable _
  let _ : Encodable ℕ := Encodable.ofCountable ℕ
  intro h
  have hcl := ((isPiIn_einf_iff _).1 ((inSigned_inf _ _ _ _).1 h).2).2 ⟨0, Fin.elim0⟩
  have hbody := ((inSigned_imp _ _ _ _).1 hcl).2
  have hforth := ((isPiIn_einf_iff _).1 ((inSigned_inf _ _ _ _).1
    ((inSigned_inf _ _ _ _).1 hbody).1).2).2 0
  obtain ⟨b, hb, hb1, -⟩ := (inSigned_ex_true _ _).1 hforth
  exact absurd (hb1.trans_lt hb) (lt_irrefl 1)

end Pure

/-! ### Components on concrete formulas -/

section Components

/-- `x₀ ≠ x₁`. -/
def neq01 : Language.empty.Formulaω (Fin 2) := (eqAtom 0 1).not

theorem neq01_level (a : Ordinal.{0}) (s : Bool) : inSigned a s neq01 :=
  (inSigned_not a s _).2 trivial

/-- The atomic diagram of `(0, 1)` is `Π^in_1` and `Π^in_2`. -/
theorem atomicDiagram_levels :
    IsPiIn 1 (atomicDiagram (L := Language.empty) (![0, 1] : Fin 2 → ℕ)) ∧
      IsPiIn 2 (atomicDiagram (L := Language.empty) (![0, 1] : Fin 2 → ℕ)) :=
  ⟨isPiIn_atomicDiagram le_rfl _, isPiIn_atomicDiagram one_le_two _⟩

/-- **Negative:** the atomic diagram is not level `0` (a countable conjunction), and not
`Σ^in_1` (a countable conjunction is `Σ^in_b` only through `Π^in_c`, `1 ≤ c < b`). -/
theorem atomicDiagram_not_levels :
    ¬ IsPiIn 0 (atomicDiagram (L := Language.empty) (![0, 1] : Fin 2 → ℕ)) ∧
      ¬ IsSigmaIn 1 (atomicDiagram (L := Language.empty) (![0, 1] : Fin 2 → ℕ)) := by
  let _ : Encodable (Language.empty.AtomicIdx 2) := Encodable.ofCountable _
  unfold atomicDiagram
  refine ⟨fun h ↦ absurd ((isPiIn_einf_iff _).1 h).1 (by simp), fun h ↦ ?_⟩
  obtain ⟨b, hb, hb1, -⟩ := h
  exact absurd (hb1.trans_lt hb) (lt_irrefl 1)

/-- The quantifier steps and the tuple closures on `x₀ ≠ x₁`, in both directions. -/
theorem quantifier_steps :
    IsPiIn 1 (forallLastVar neq01) ∧ IsSigmaIn 1 (existsLastVar neq01) ∧
      IsPiIn 1 (forallTuple 2 neq01) ∧ IsPiIn 1 (forallTupleFrom 1 1 neq01) ∧
      (IsPiIn 1 (forallTuple 2 neq01) → IsPiIn 1 neq01) :=
  ⟨(isPiIn_forallLastVar_iff le_rfl).2 (neq01_level 1 true),
    (isSigmaIn_existsLastVar_iff le_rfl).2 (neq01_level 1 false),
    (isPiIn_forallTuple_iff le_rfl 2 _).2 (neq01_level 1 true),
    (isPiIn_forallTupleFrom_iff le_rfl 1 1 _).2 (neq01_level 1 true),
    (isPiIn_forallTuple_iff le_rfl 2 _).1⟩

/-- A clause body over the pure set `ℕ`: `Σ^in_1` orbit formulas give `Π^in_2`. -/
theorem clauseBody_level :
    IsPiIn (1 + 1) (montalbanClauseBody (eqPattern (L := Language.empty) (![0] : Fin 1 → ℕ))
      (atomicDiagram (L := Language.empty) (![0] : Fin 1 → ℕ))
      fun m : ℕ ↦ eqPattern (L := Language.empty) (Fin.snoc (![0] : Fin 1 → ℕ) m)) :=
  isPiIn_montalbanClauseBody le_rfl (IsSigmaIn.mono zero_le_one (inSigned_eqPattern _ false))
    (isPiIn_atomicDiagram le_add_self _) fun _ ↦
      IsSigmaIn.mono zero_le_one (inSigned_eqPattern _ false)

end Components

/-! ### Scott sentences of pure sets -/

section PureScott

/-- **The corollary at `α = 1`**: `ℕ` has a `Π^in_2` Scott sentence. -/
theorem nat_scott_one :
    ∃ σ : Language.empty.Formulaω (Fin 0), IsPiIn (1 + 1) σ ∧
      ∀ (N : Type) [Language.empty.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (ℕ ≃[Language.empty] N) :=
  exists_isPiIn_scottSentence_of_sigmaIn_orbits le_rfl fun _ a ↦
    ⟨eqPattern a, pureΦ_isSigmaIn_one ℕ _ a, pure_orbit a⟩

/-- **The level-`0` corollary**: the same from quantifier-free orbit formulas, read as `Π^in_2`. -/
theorem nat_scott_zero :
    ∃ σ : Language.empty.Formulaω (Fin 0), IsPiIn 2 σ ∧
      ∀ (N : Type) [Language.empty.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (ℕ ≃[Language.empty] N) :=
  exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits fun _ a ↦
    ⟨eqPattern a, inSigned_eqPattern a false, pure_orbit a⟩

/-- The `Π^in_2` Scott sentence of `ℕ` holds in `ℕ` and `ℤ` and fails in `Fin 3`. -/
theorem nat_scott_uses :
    ∃ σ : Language.empty.Formulaω (Fin 0), IsPiIn 2 σ ∧ σ.realize_as_sentence ℕ ∧
      σ.realize_as_sentence ℤ ∧ ¬ σ.realize_as_sentence (Fin 3) := by
  obtain ⟨σ, hσ, hN⟩ := nat_scott_zero
  refine ⟨σ, hσ, (hN ℕ).2 ⟨pureEquiv (Equiv.refl ℕ)⟩,
    (hN ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩, fun h ↦ ?_⟩
  obtain ⟨e⟩ := (hN (Fin 3)).1 h
  exact not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm : Finite ℕ)

/-- **`Type 1` carrier**: B3 on `ULift.{1} ℕ`, and its `Π^in_2` Scott sentence holds in
`ULift.{1} ℤ` and fails in `ULift.{1} (Fin 3)`. -/
theorem ulift_scott :
    IsPiIn 2 (montalbanSentence (pureΦ (ULift.{1} ℕ))) ∧
      ∃ σ : Language.empty.Formulaω (Fin 0), IsPiIn 2 σ ∧
        σ.realize_as_sentence (ULift.{1} ℤ) ∧ ¬ σ.realize_as_sentence (ULift.{1} (Fin 3)) := by
  refine ⟨?_, ?_⟩
  · have := isPiIn_montalbanSentence le_rfl (pureΦ_isSigmaIn_one (ULift.{1} ℕ))
    rwa [one_add_one_eq_two] at this
  obtain ⟨σ, hσ, hN⟩ := exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits
    (M := ULift.{1} ℕ) fun _ a ↦ ⟨eqPattern a, inSigned_eqPattern a false, pure_orbit a⟩
  refine ⟨σ, hσ, (hN _).2 ⟨pureEquiv (Equiv.ulift.trans
    (Equiv.intEquivNat.symm.trans Equiv.ulift.symm))⟩, fun h ↦ ?_⟩
  obtain ⟨e⟩ := (hN _).1 h
  exact not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm)

/-- **Universe-polymorphic carrier**: B3 and the level-`0` corollary for a countable pure set in
an arbitrary universe `w`. -/
theorem pure_univ (X : Type w) [Countable X] :
    IsPiIn 2 (montalbanSentence (L := Language.empty) fun _ (a : Fin _ → X) ↦
      eqPattern a) ∧
      ∃ σ : Language.empty.Formulaω (Fin 0), IsPiIn 2 σ ∧
        ∀ (N : Type w) [Language.empty.Structure N] [Countable N],
          σ.realize_as_sentence N ↔ Nonempty (X ≃[Language.empty] N) := by
  refine ⟨?_, exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits fun _ a ↦
    ⟨eqPattern a, inSigned_eqPattern a false, fun b ↦ ?_⟩⟩
  · have := isPiIn_montalbanSentence (L := Language.empty) (M := X) le_rfl
      fun _ a ↦ IsSigmaIn.mono zero_le_one (inSigned_eqPattern a false)
    rwa [one_add_one_eq_two] at this
  · rw [realize_eqPattern]
    refine ⟨fun h ↦ ?_, fun ⟨e, he⟩ i j ↦ he ▸ e.injective.eq_iff.symm⟩
    obtain ⟨e, he, -, -⟩ := FiberAssembly.exists_equiv_of_matching
      (E := fun (_ _ : X) ↦ True) ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩ _ a b h
      (fun _ ↦ trivial)
    exact ⟨{ toEquiv := e }, funext he⟩

end PureScott

/-! ### A countable disjunction at level 1 -/

section Labels

/-- Countably many unary relation symbols `P i`. -/
inductive LabelRel : ℕ → Type
  /-- The label `i`. -/
  | P : ℕ → LabelRel 1

/-- The language of countably many labels. -/
abbrev labelLang : Language.{0, 0} := ⟨fun _ ↦ Empty, LabelRel⟩

instance : Countable (Σ l, labelLang.Relations l) :=
  Function.Injective.countable (f := fun p : Σ l, LabelRel l ↦ match p with | ⟨_, .P i⟩ => i)
    fun | ⟨_, .P _⟩, ⟨_, .P _⟩, h => by cases h; rfl

/-- `ℕ ⊕ ℕ`: every label holds at every left point and at no right point. -/
instance sided : labelLang.Structure (ℕ ⊕ ℕ) where
  funMap f := Empty.elim f
  RelMap | .P _, x => (x 0).isLeft

/-- `ℕ` with every label at every point. -/
instance allLabelled : labelLang.Structure ℕ where
  funMap f := Empty.elim f
  RelMap | .P _, _ => True

/-- The atom `P i (x_k)`. -/
def labelAtom {n : ℕ} (i : ℕ) (k : Fin n) : labelLang.Formulaω (Fin n) :=
  BoundedFormulaω.rel (LabelRel.P i) fun _ ↦ Term.var (Sum.inl k)

/-- "`x_k` has some label": the countable disjunction `⋁ᵢ Pᵢ(x_k)`. -/
def hasLabel {n : ℕ} (k : Fin n) : labelLang.Formulaω (Fin n) := esup fun i : ℕ ↦ labelAtom i k

/-- The orbit formula of `a`: its equality pattern, and for each coordinate "has some label" at
a left point and `¬P₀` at a right point. -/
def sidedΦ : ∀ n, (Fin n → ℕ ⊕ ℕ) → labelLang.Formulaω (Fin n) := fun _ a ↦
  eqPattern a ⊓ finConj (List.ofFn fun k ↦
    if (a k).isLeft then hasLabel k else (labelAtom 0 k).not)

theorem realize_labelAtom {n : ℕ} (i : ℕ) (k : Fin n) (b : Fin n → ℕ ⊕ ℕ) :
    (labelAtom i k).Realize b ↔ (b k).isLeft := by
  simp only [labelAtom, Formulaω.realize_def, BoundedFormulaω.realize_rel]
  rfl

theorem realize_sidedΦ {n : ℕ} (a b : Fin n → ℕ ⊕ ℕ) :
    (sidedΦ n a).Realize b ↔ (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ k, (a k).isLeft = (b k).isLeft := by
  simp only [sidedΦ, Formulaω.realize_inf, realize_eqPattern, realize_finConj,
    List.forall_mem_ofFn_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun k ↦ ?_
  split_ifs with h
  · simp [hasLabel, Formulaω.realize_esup, realize_labelAtom, h]
  · simp [Formulaω.realize_not, realize_labelAtom, h]

/-- The orbit formulas define the orbits: automorphisms are the side-preserving permutations. -/
theorem sided_isOrbit {n : ℕ} (a b : Fin n → ℕ ⊕ ℕ) :
    (sidedΦ n a).Realize b ↔ ∃ e : (ℕ ⊕ ℕ) ≃[labelLang] (ℕ ⊕ ℕ), ⇑e ∘ a = b := by
  rw [realize_sidedΦ]
  constructor
  · rintro ⟨hpat, hside⟩
    obtain ⟨e, he, hEe, -⟩ := FiberAssembly.exists_equiv_of_matching
      (E := fun x y : ℕ ⊕ ℕ ↦ x.isLeft = y.isLeft) ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩ n a b hpat
      hside
    refine ⟨{ toEquiv := e, map_rel' := fun {_} r x ↦ ?_ }, funext he⟩
    cases r with
    | P i => exact (Bool.eq_iff_iff.1 (hEe (x 0))).symm
  · rintro ⟨e, rfl⟩
    refine ⟨fun i j ↦ e.injective.eq_iff.symm, fun k ↦ ?_⟩
    have := e.map_rel (LabelRel.P 0) fun _ ↦ a k
    exact Bool.eq_iff_iff.2 this.symm

/-- The orbit formulas are `Σ^in_1`: the countable disjunction is admitted by
`isSigmaIn_esup` at level `1`. -/
theorem sidedΦ_isSigmaIn_one : ∀ n a, IsSigmaIn 1 (sidedΦ n a) := fun n a ↦ by
  refine (inSigned_inf _ _ _ _).2 ⟨IsSigmaIn.mono zero_le_one (inSigned_eqPattern a false), ?_⟩
  refine (inSigned_finConj _ _ _).2 fun φ hφ ↦ ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hφ
  split_ifs
  · exact isSigmaIn_esup le_rfl fun _ ↦ trivial
  · exact (inSigned_not _ _ _).2 trivial

/-- **Negative:** the orbit formula of a left point is not level `0`: the countable
disjunction is genuinely there. -/
theorem sidedΦ_not_zero : ¬ IsSigmaIn 0 (sidedΦ 1 ![Sum.inl 0]) := fun h ↦ by
  have h2 := (inSigned_finConj _ _ _).1 ((inSigned_inf _ _ _ _).1 h).2 (hasLabel 0) (by simp)
  exact absurd ((isSigmaIn_esup_iff _).1 h2).1 (by simp)

/-- **B3 with a countable disjunction inside the orbit formulas**: `Π^in_2`. -/
theorem sided_isPiIn_two : IsPiIn 2 (montalbanSentence sidedΦ) := by
  have := isPiIn_montalbanSentence le_rfl sidedΦ_isSigmaIn_one
  rwa [one_add_one_eq_two] at this

/-- **The corollary**: a `Π^in_2` Scott sentence of `ℕ ⊕ ℕ`, which fails in `ℕ` with every point
labelled (an isomorphism would carry the unlabelled `inr 0` to a labelled point). -/
theorem sided_scott :
    ∃ σ : labelLang.Formulaω (Fin 0), IsPiIn 2 σ ∧ σ.realize_as_sentence (ℕ ⊕ ℕ) ∧
      ¬ σ.realize_as_sentence ℕ := by
  obtain ⟨σ, hσ, hN⟩ := exists_isPiIn_scottSentence_of_sigmaIn_orbits (M := ℕ ⊕ ℕ) le_rfl
    fun n a ↦ ⟨sidedΦ n a, sidedΦ_isSigmaIn_one n a, sided_isOrbit a⟩
  rw [one_add_one_eq_two] at hσ
  refine ⟨σ, hσ, (hN _).2 ⟨Language.Equiv.refl _ _⟩, fun h ↦ ?_⟩
  obtain ⟨e⟩ := (hN ℕ).1 h
  have := (e.map_rel (LabelRel.P 0) fun _ ↦ Sum.inr 0).1 trivial
  change (Sum.inr 0 : ℕ ⊕ ℕ).isLeft = true at this
  simp at this

end Labels

/-! ### The pointed form with a repeated parameter -/

section Pointed

/-- Equality patterns of `c⌢a`, over the parameters `c`. -/
abbrev pureΦc {k : ℕ} (c : Fin k → ℕ) :
    ∀ n, (Fin n → ℕ) → Language.empty.Formulaω (Fin (k + n)) :=
  fun _ a ↦ eqPattern (Fin.append c a)

/-- Composition commutes with appending. -/
theorem comp_append' {α β : Type*} (f : α → β) {k n : ℕ} (c : Fin k → α) (a : Fin n → α) :
    f ∘ Fin.append c a = Fin.append (f ∘ c) (f ∘ a) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- The pointed equality patterns define the orbits over `c`. -/
theorem pure_orbitPointed {k n : ℕ} (c : Fin k → ℕ) (a b : Fin n → ℕ) :
    (pureΦc c n a).Realize (Fin.append c b) ↔
      ∃ e : ℕ ≃[Language.empty] ℕ, ⇑e ∘ c = c ∧ ⇑e ∘ a = b := by
  rw [pure_orbit]
  refine ⟨fun ⟨e, he⟩ ↦ ⟨e, funext fun j ↦ ?_, funext fun i ↦ ?_⟩, fun ⟨e, hc, ha⟩ ↦
    ⟨e, by rw [comp_append', hc, ha]⟩⟩
  · simpa [comp_append'] using congrFun he (Fin.castAdd n j)
  · simpa [comp_append'] using congrFun he (Fin.natAdd k i)

/-- **B3, pointed, repeated parameters**: over `(1, 1)`, the pointed sentence is `Π^in_2`. -/
theorem pointed_repeated_isPiIn_two :
    IsPiIn 2 (montalbanSentencePointed (![1, 1] : Fin 2 → ℕ) (pureΦc ![1, 1])) := by
  have := isPiIn_montalbanSentencePointed (Φ := pureΦc ![1, 1]) le_rfl (![1, 1] : Fin 2 → ℕ)
    fun _ _ ↦ IsSigmaIn.mono zero_le_one (inSigned_eqPattern _ false)
  rwa [one_add_one_eq_two] at this

/-- **The pointed corollary, repeated parameters**: a `Π^in_2` formula that holds at `(4, 4)`
and fails at `(4, 5)`, read off from the isomorphisms it characterizes. -/
theorem pointed_repeated_scott :
    ∃ σ : Language.empty.Formulaω (Fin 2), IsPiIn 2 σ ∧ σ.Realize (![4, 4] : Fin 2 → ℕ) ∧
      ¬ σ.Realize (![4, 5] : Fin 2 → ℕ) := by
  obtain ⟨σ, hσ, hN⟩ := exists_isPiIn_pointed_of_sigmaIn_orbits le_rfl (![1, 1] : Fin 2 → ℕ)
    fun n a ↦ ⟨pureΦc ![1, 1] n a, IsSigmaIn.mono zero_le_one (inSigned_eqPattern _ false),
      pure_orbitPointed _ a⟩
  rw [one_add_one_eq_two] at hσ
  refine ⟨σ, hσ, (hN ℕ _).2 ?_, fun h ↦ ?_⟩
  · obtain ⟨e, he⟩ := pure_homogeneous (![1, 1] : Fin 2 → ℕ) ![4, 4] (by decide)
    exact ⟨e, he⟩
  · obtain ⟨e, he⟩ := (hN ℕ _).1 h
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    omega

end Pointed

end MontalbanComplexityGuard

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
  let target := `InfinitaryLogic.Scott.MontalbanComplexity
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Scott.MontalbanSentence, `InfinitaryLogic.Lomega1omega.InHierarchy] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let hits := cl.toList.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-- The public declarations of the module. -/
def moduleDecls : List Name :=
  [`isPiIn_atomicDiagram, `isPiIn_forallLastVar_iff, `isSigmaIn_existsLastVar_iff,
   `isPiIn_forallTuple_iff, `isPiIn_forallTupleFrom_iff, `isPiIn_montalbanClauseBody,
   `isPiIn_montalbanSentencePointed, `isPiIn_montalbanSentence,
   `exists_isPiIn_scottSentence_of_sigmaIn_orbits, `exists_isPiIn_pointed_of_sigmaIn_orbits,
   `exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits].map (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`realize_eqPattern, `inSigned_eqPattern, `pure_homogeneous, `pure_orbit, `pure_isPiIn_two,
   `pure_not_isPiIn_one, `atomicDiagram_levels, `atomicDiagram_not_levels, `quantifier_steps,
   `clauseBody_level, `nat_scott_one, `nat_scott_zero, `nat_scott_uses, `ulift_scott, `pure_univ,
   `realize_sidedΦ, `sided_isOrbit, `sidedΦ_isSigmaIn_one, `sidedΦ_not_zero,
   `sided_isPiIn_two, `sided_scott, `pure_orbitPointed, `pointed_repeated_isPiIn_two,
   `pointed_repeated_scott].map (`MontalbanComplexityGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in moduleDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Montalban-complexity regression guard: OK (applied: the atomic diagram Pi-in at \
    levels 1 and 2, neither level 0 nor Sigma-in 1; the quantifier steps and tuple closures; a \
    clause body; B3 at alpha = 1 on the level-0 equality patterns of N, giving Pi-in 2, and \
    the same sentence not in the signed class Pi-in 1; Pi-in 2 Scott sentences of N from \
    alpha = 1 and from the level-0 lemma, holding in N and Z and failing in Fin 3, and on the \
    Type 1 carrier ULift N; B3 and the level-0 corollary for a pure set in arbitrary \
    universes; orbit formulas with the countable disjunction 'has some label' on \
    N + N, Sigma-in 1 and not level 0, a Pi-in 2 sentence and a Pi-in 2 Scott sentence failing \
    where every point is labelled; the pointed sentence over the repeated parameters (1, 1) \
    Pi-in 2, and the pointed corollary holding at (4, 4) and failing at (4, 5); import \
    closure without Scott-process, descriptive, method, model-theory, admissible or \
    conditional modules; standard axioms)"
