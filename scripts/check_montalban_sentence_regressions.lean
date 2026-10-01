/-
Regression guard for Montalbán's explicit Scott sentence
(`InfinitaryLogic/Scott/MontalbanSentence.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **Generic orbit families.**  If atomic agreement in `M` is always witnessed by an
  automorphism, the atomic diagrams form an orbit-formula family, unpointed and over any
  parameter tuple.
* **The infinite pure set** `ℕ`: orbit formulas are equality patterns (the atomic diagram in the
  empty language); the sentence holds in `ℤ` and fails in `Fin 3`.  The same on the `Type 1`
  carrier `ULift.{1} ℕ`, against `ULift.{1} ℤ` and `ULift.{1} (Fin 3)`.
* **`(ℚ, <)`.**  Ultrahomogeneity is *derived* from B2 in pointed form: for the family of
  atomic diagrams over parameters `c`, the pointed sentence holds at any `d` of the same order
  type, by the one-point extension property of `ℚ` alone (B2 needs no hypothesis on the
  family), so B2 produces an automorphism carrying `c` to `d`.  The pointed sentence is
  verified by rewriting with the public clause-by-clause characterization
  `realize_montalbanSentencePointed`, without unfolding the definitions.  Then the atomic
  diagrams are orbit formulas, and the sentence of `(ℚ, <)` fails in `(ℕ, <)`.
* **An infinitary orbit formula (semantic).**  Countably many unary predicates `P i` on
  `ℕ ⊕ ℕ`, `P i` true exactly at `inl i`: the orbit formula of an unlabelled point `inr j` is
  `⋀ᵢ ¬P i(x) = ¬⋁ᵢ P i(x)`, the negation of a countable disjunction of atoms.  (An outermost
  countable disjunction is never needed to define a single orbit: each disjunct defines an
  automorphism-invariant subset of the orbit, hence the orbit or nothing.)  The sentence fails in
  `ℕ` with `P i` true exactly at `i`, where every point is labelled.  This is a **semantic**
  regression, not a complexity one: the orbit formula of an unlabelled point is `Π^in_1`, and
  that orbit is not `Σ^in_1`-definable (by the invariance argument, a single disjunct `∃ȳ ψ`
  would define it; `ψ` mentions only some `P 0, …, P N`, and swapping `inr 0` with `inl (N+1)`
  is an automorphism of that reduct, so the disjunct cannot separate the two points).  The spec
  §7 complexity item, a genuine countable `⋁` inside a `Σ^in_1` orbit formula, is deferred to
  the B3 PR, where the back clause `∀y ⋁_{m ∈ M}` exercises A-5 at level 1.
* **A finite structure**: `Bool` with a nullary `S` and a unary `P` true only at `true` is rigid;
  its atomic diagrams are orbit formulas, and B2 shows every countable model of the sentence has
  two elements.
* **The atomic-diagram conjunct is needed.**  On one point, the family `⊤` defines every
  orbit.  The sentence assembled from the same clauses with `⊤` for the atomic diagram
  (built from `montalbanClauseBody` and `forallTuple`) holds both where `P` holds and where it
  fails; `montalbanSentence` separates the two.
* **The empty carrier.**  For `Empty` with the nullary `S` true, B2 proves that every countable
  model of the sentence is empty **and satisfies `S`**; `Fin 0` with `S` true satisfies it.
  **Negative:** `PEmpty` with `S` false does not, although it is also empty; nor does the
  one-point structure; and symmetrically the sentence of `PEmpty` fails in `Empty`.
* **Pointed form** on the pure set: one parameter (`3 ↦ 5`), two parameters (`(1, 2) ↦ (7, 4)`)
  and a repeated parameter (`(1, 1) ↦ (4, 4)`), each time reading off that the isomorphism
  produced by B2 carries the parameters; **negative:** `(1, 1)` is not carried to `(4, 5)`, so
  the pointed sentence fails there (B2 alone, through the equality atoms).
* **`k = 0` compatibility** (`realize_montalbanSentence_iff_pointed`) on the pure set, the
  syntactic equation `montalbanSentence_eq_pointed_elim0` used by rewriting there, and the
  pointed B2 at the empty parameter tuple.
* **The empty tuple**: the seed `Φ 0 Fin.elim0` is a conjunct (the family `⊥` gives a sentence
  true nowhere, read off `realize_montalbanSentence`); the tuple quantifiers at length `0`;
  `existsTuple`, `forallTuple` and `forallTupleFrom` on concrete formulas; and `simp` closing
  `existsTuple`/`forallTuple` goals and a `forallTupleFrom` goal around a clause body.
* **Import closure** of the module: it reaches `Karp/PotentialIso`, `Scott/Sentence` and
  `Lomega1omega/Theory`, and no Scott-process, descriptive, method, model-theory, admissible or
  conditional module.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_montalban_sentence_regressions.lean
-/
import InfinitaryLogic.Scott.MontalbanSentence
import InfinitaryLogic.Scott.FiniteMatching
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.Tactic.Linarith

open Lean FirstOrder FirstOrder.Language

universe u v w

noncomputable section

namespace MontalbanGuard

attribute [local instance] Language.emptyStructure

/-! ### Generic orbit families -/

section Generic

variable {L : Language.{u, v}} [Countable (Σ l, L.Relations l)] {M : Type w} [L.Structure M]

omit [Countable (Σ l, L.Relations l)] in
/-- An automorphism preserves atomic types. -/
theorem sameAtomicType_comp (e : M ≃[L] M) {n : ℕ} (a : Fin n → M) :
    SameAtomicType (L := L) a (⇑e ∘ a) :=
  (SameAtomicType.map_equiv (Language.Equiv.refl L M) e).2 (SameAtomicType.refl a)

/-- Composition commutes with appending. -/
theorem comp_append' {α β : Type*} (f : α → β) {k n : ℕ} (c : Fin k → α) (a : Fin n → α) :
    f ∘ Fin.append c a = Fin.append (f ∘ c) (f ∘ a) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- If atomic agreement is witnessed by automorphisms, the atomic diagrams are orbit formulas. -/
theorem atomicDiagram_isOrbitFormulaFamily
    (hU : ∀ n (a b : Fin n → M), SameAtomicType (L := L) a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    IsOrbitFormulaFamily (L := L) (M := M) fun _ a ↦ atomicDiagram (L := L) a := fun n a b ↦ by
  rw [← sameAtomicType_iff_realize_atomicDiagram]
  exact ⟨hU n a b, fun ⟨e, he⟩ ↦ he ▸ sameAtomicType_comp e a⟩

/-- The pointed form: atomic diagrams of `c⌢a` define the orbits over `c`. -/
theorem atomicDiagram_isOrbitFormulaFamilyPointed
    (hU : ∀ n (a b : Fin n → M), SameAtomicType (L := L) a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b)
    {k : ℕ} (c : Fin k → M) :
    IsOrbitFormulaFamilyPointed (L := L) c fun _ a ↦ atomicDiagram (L := L) (Fin.append c a) :=
  fun n a b ↦ by
    rw [← sameAtomicType_iff_realize_atomicDiagram]
    constructor
    · intro h
      obtain ⟨e, he⟩ := hU _ _ _ h
      rw [comp_append'] at he
      refine ⟨e, funext fun j ↦ ?_, funext fun i ↦ ?_⟩
      · simpa using congrFun he (Fin.castAdd n j)
      · simpa using congrFun he (Fin.natAdd k i)
    · rintro ⟨e, hec, rfl⟩
      have := sameAtomicType_comp e (Fin.append c a)
      rwa [comp_append', hec] at this

end Generic

/-! ### The infinite pure set -/

section Pure

/-- In the empty language, atomic agreement is witnessed by a permutation, on any carrier. -/
theorem pure_homogeneous {X : Type w} {n : ℕ} (a b : Fin n → X)
    (h : SameAtomicType (L := Language.empty) a b) :
    ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  obtain ⟨e, he, -, -⟩ := FiberAssembly.exists_equiv_of_matching
    (E := fun (_ _ : X) ↦ True) ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩ n a b
    (fun i j ↦ h (AtomicIdx.eq i j)) (fun _ ↦ trivial)
  exact ⟨{ toEquiv := e }, funext he⟩

/-- An equivalence of carriers is an isomorphism of pure sets. -/
def pureEquiv {X Y : Type*} (e : X ≃ Y) : X ≃[Language.empty] Y := { toEquiv := e }

/-- The orbit formulas of a pure set: equality patterns, i.e. atomic diagrams. -/
abbrev pureΦ (X : Type w) : ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin n) :=
  fun _ a ↦ atomicDiagram (L := Language.empty) a

theorem pure_isOrbit (X : Type w) : IsOrbitFormulaFamily (L := Language.empty) (pureΦ X) :=
  atomicDiagram_isOrbitFormulaFamily fun _ a b h ↦ pure_homogeneous a b h

/-- **B1** on `ℕ`. -/
theorem nat_self : (montalbanSentence (pureΦ ℕ)).realize_as_sentence ℕ :=
  montalbanSentence_self (pure_isOrbit ℕ)

/-- **The sentence characterizes the countably infinite pure set.** -/
theorem nat_characterizes (N : Type) [Countable N] :
    (montalbanSentence (pureΦ ℕ)).realize_as_sentence N ↔
      Nonempty (ℕ ≃[Language.empty] N) :=
  montalbanSentence_characterizes (pure_isOrbit ℕ) N

/-- `ℤ` satisfies the sentence of `ℕ`, and **B2** returns an isomorphism. -/
theorem int_realizes : (montalbanSentence (pureΦ ℕ)).realize_as_sentence ℤ :=
  (nat_characterizes ℤ).2 ⟨pureEquiv Equiv.intEquivNat.symm⟩

theorem nat_int_equiv : Nonempty (ℕ ≃[Language.empty] ℤ) :=
  nonempty_equiv_of_realize_montalbanSentence (pureΦ ℕ) ℤ int_realizes

/-- **Negative:** the finite `Fin 3` does not satisfy the sentence of `ℕ`. -/
theorem fin3_not_realizes : ¬ (montalbanSentence (pureΦ ℕ)).realize_as_sentence (Fin 3) :=
  fun h ↦ (nonempty_equiv_of_realize_montalbanSentence (pureΦ ℕ) (Fin 3) h).elim fun e ↦
    not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm : Finite ℕ)

/-- **Type 1 carrier**: the sentence of `ULift.{1} ℕ` holds in `ULift.{1} ℤ` and fails in
`ULift.{1} (Fin 3)`. -/
theorem ulift_characterizes :
    (montalbanSentence (pureΦ (ULift.{1} ℕ))).realize_as_sentence (ULift.{1} ℕ) ∧
      (montalbanSentence (pureΦ (ULift.{1} ℕ))).realize_as_sentence (ULift.{1} ℤ) ∧
      ¬ (montalbanSentence (pureΦ (ULift.{1} ℕ))).realize_as_sentence (ULift.{1} (Fin 3)) := by
  refine ⟨montalbanSentence_self (pure_isOrbit _), ?_, fun h ↦ ?_⟩
  · exact (montalbanSentence_characterizes (pure_isOrbit _) _).2
      ⟨pureEquiv (Equiv.ulift.trans (Equiv.intEquivNat.symm.trans Equiv.ulift.symm))⟩
  · obtain ⟨e⟩ := nonempty_equiv_of_realize_montalbanSentence (pureΦ _) _ h
    exact not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm)

end Pure

/-! ### `(ℚ, <)`: ultrahomogeneity from the pointed B2 -/

section Rat

/-- One binary relation symbol, read as `<`. -/
inductive LtRel : ℕ → Type
  /-- The order symbol. -/
  | lt : LtRel 2

/-- The language of strict orders. -/
abbrev ltLang : Language.{0, 0} := ⟨fun _ ↦ Empty, LtRel⟩

instance : Countable (Σ l, ltLang.Relations l) :=
  Function.Injective.countable (f := Sigma.fst) fun
    | ⟨_, .lt⟩, ⟨_, .lt⟩, _ => rfl

/-- `(ℚ, <)`. -/
instance ratLt : ltLang.Structure ℚ where
  funMap f := Empty.elim f
  RelMap | .lt, x => x 0 < x 1

/-- `(ℕ, <)`. -/
instance natLt : ltLang.Structure ℕ where
  funMap f := Empty.elim f
  RelMap | .lt, x => x 0 < x 1

/-- In `(ℚ, <)`, atomic agreement is agreement of all comparisons. -/
theorem rat_sameAtomicType_iff {n : ℕ} (x y : Fin n → ℚ) :
    SameAtomicType (L := ltLang) x y ↔ ∀ i j, cmp (x i) (x j) = cmp (y i) (y j) := by
  constructor
  · intro h i j
    have heq : x i = x j ↔ y i = y j := h (AtomicIdx.eq i j)
    have hlt : ∀ i j, x i < x j ↔ y i < y j := fun i j ↦ h (AtomicIdx.rel LtRel.lt ![i, j])
    rcases lt_trichotomy (x i) (x j) with hx | hx | hx
    · rw [(cmp_eq_lt_iff _ _).2 hx, (cmp_eq_lt_iff _ _).2 ((hlt i j).1 hx)]
    · rw [(cmp_eq_eq_iff _ _).2 hx, (cmp_eq_eq_iff _ _).2 (heq.1 hx)]
    · rw [(cmp_eq_gt_iff _ _).2 hx, (cmp_eq_gt_iff _ _).2 ((hlt j i).1 hx)]
  · intro h idx
    cases idx with
    | eq i j =>
      change x i = x j ↔ y i = y j
      rw [← cmp_eq_eq_iff (x i), h, cmp_eq_eq_iff]
    | rel R f =>
      cases R
      change x (f 0) < x (f 1) ↔ y (f 0) < y (f 1)
      rw [← cmp_eq_lt_iff (x (f 0)), h, cmp_eq_lt_iff]

/-- Strictly between two finite sets of rationals, all of the first below all of the second. -/
theorem rat_exists_between (A B : Finset ℚ) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ z, (∀ a ∈ A, a < z) ∧ ∀ b ∈ B, z < b := by
  by_cases hA : A.Nonempty <;> by_cases hB : B.Nonempty
  · have hab := h _ (A.max'_mem hA) _ (B.min'_mem hB)
    refine ⟨(A.max' hA + B.min' hB) / 2, fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · linarith [A.le_max' a ha]
    · linarith [B.min'_le b hb]
  · refine ⟨A.max' hA + 1, fun a ha ↦ by linarith [A.le_max' a ha], fun b hb ↦ ?_⟩
    exact (hB ⟨b, hb⟩).elim
  · refine ⟨B.min' hB - 1, fun a ha ↦ (hA ⟨a, ha⟩).elim, fun b hb ↦ ?_⟩
    linarith [B.min'_le b hb]
  · exact ⟨0, fun a ha ↦ (hA ⟨a, ha⟩).elim, fun b hb ↦ (hB ⟨b, hb⟩).elim⟩

/-- **The one-point extension property of `(ℚ, <)`.** -/
theorem rat_extend {n : ℕ} (x y : Fin n → ℚ) (h : SameAtomicType (L := ltLang) x y) (m : ℚ) :
    ∃ z, SameAtomicType (L := ltLang) (Fin.snoc x m) (Fin.snoc y z) := by
  classical
  rw [rat_sameAtomicType_iff] at h
  obtain ⟨z, hz⟩ : ∃ z, ∀ i, cmp (x i) m = cmp (y i) z := by
    by_cases hm : ∃ i, x i = m
    · obtain ⟨i₀, rfl⟩ := hm
      exact ⟨y i₀, fun i ↦ h i i₀⟩
    push Not at hm
    obtain ⟨z, hlo, hhi⟩ := rat_exists_between
      ((Finset.univ.filter fun i ↦ x i < m).image y) ((Finset.univ.filter fun i ↦ m < x i).image y)
      (by
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
        rw [← cmp_eq_lt_iff, ← h, cmp_eq_lt_iff]
        exact hi.trans hj)
    have hmem : ∀ {p : Fin n → Prop} [DecidablePred p] {i}, p i →
        y i ∈ (Finset.univ.filter p).image y :=
      fun hi ↦ Finset.mem_image_of_mem y (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    refine ⟨z, fun i ↦ ?_⟩
    rcases (hm i).lt_or_gt with hi | hi
    · rw [(cmp_eq_lt_iff _ _).2 hi, (cmp_eq_lt_iff _ _).2 (hlo _ (hmem hi))]
    · rw [(cmp_eq_gt_iff _ _).2 hi, (cmp_eq_gt_iff _ _).2 (hhi _ (hmem hi))]
  refine ⟨z, (rat_sameAtomicType_iff _ _).2 fun i j ↦ ?_⟩
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [Fin.snoc_last, Fin.snoc_castSucc, cmp_self_eq_eq, h, hz]
  rw [← cmp_swap, hz, cmp_swap]

/-- The family of atomic diagrams over parameters `c`, for `(ℚ, <)`. -/
abbrev ratΦ {k : ℕ} (c : Fin k → ℚ) : ∀ n, (Fin n → ℚ) → ltLang.Formulaω (Fin (k + n)) :=
  fun _ a ↦ atomicDiagram (L := ltLang) (Fin.append c a)

/-- The pointed sentence of the atomic-diagram family holds at every tuple of the same order
type, by the extension property alone (no orbit hypothesis). -/
theorem rat_realize_pointed {k : ℕ} (c d : Fin k → ℚ) (h : SameAtomicType (L := ltLang) c d) :
    (montalbanSentencePointed c (ratΦ c)).Realize d := by
  rw [realize_montalbanSentencePointed]
  simp only [ratΦ, ← sameAtomicType_iff_realize_atomicDiagram, Fin.append_snoc]
  refine ⟨by simpa using h, fun p a b hb ↦ ⟨hb, fun m ↦ ?_, fun y ↦ ?_⟩⟩
  · exact rat_extend _ _ hb m
  · obtain ⟨m, hm⟩ := rat_extend _ _ hb.symm y
    exact ⟨m, hm.symm⟩

/-- **Ultrahomogeneity of `(ℚ, <)`, from the pointed B2.** -/
theorem rat_homogeneous {k : ℕ} (c d : Fin k → ℚ) (h : SameAtomicType (L := ltLang) c d) :
    ∃ e : ℚ ≃[ltLang] ℚ, ⇑e ∘ c = d :=
  exists_equiv_of_realize_montalbanSentencePointed c (ratΦ c) ℚ d (rat_realize_pointed c d h)

/-- The atomic diagrams are orbit formulas of `(ℚ, <)`. -/
theorem rat_isOrbit :
    IsOrbitFormulaFamily (L := ltLang) (M := ℚ) fun _ a ↦ atomicDiagram (L := ltLang) a :=
  atomicDiagram_isOrbitFormulaFamily fun _ a b h ↦ rat_homogeneous a b h

/-- **The sentence of `(ℚ, <)` characterizes it**, and fails in `(ℕ, <)`. -/
theorem rat_characterizes (N : Type) [ltLang.Structure N] [Countable N] :
    (montalbanSentence fun _ a ↦ atomicDiagram (L := ltLang) (M := ℚ) a).realize_as_sentence N ↔
      Nonempty (ℚ ≃[ltLang] N) :=
  montalbanSentence_characterizes rat_isOrbit N

theorem nat_not_realizes_rat :
    ¬ (montalbanSentence fun _ a ↦ atomicDiagram (L := ltLang) (M := ℚ) a).realize_as_sentence
      ℕ := fun h ↦ by
  obtain ⟨e⟩ := (rat_characterizes ℕ).1 h
  have := (e.map_rel LtRel.lt ![e.symm 0 - 1, e.symm 0]).2 (by
    change e.symm 0 - 1 < e.symm 0
    linarith)
  change e (e.symm 0 - 1) < e (e.symm 0) at this
  simp at this

end Rat

/-! ### A genuinely infinitary orbit formula: labelled and unlabelled points -/

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

/-- `ℕ ⊕ ℕ`: the point `inl i` carries the label `i`; the points `inr j` are unlabelled. -/
instance labelled : labelLang.Structure (ℕ ⊕ ℕ) where
  funMap f := Empty.elim f
  RelMap | .P i, x => x 0 = Sum.inl i

/-- `ℕ` with every point labelled: `P i` holds exactly at `i`. -/
instance labelledOnly : labelLang.Structure ℕ where
  funMap f := Empty.elim f
  RelMap | .P i, x => x 0 = i

/-- Same point, or both unlabelled. -/
def SameKind (x y : ℕ ⊕ ℕ) : Prop := x = y ∨ (x.isRight ∧ y.isRight)

theorem sameKind_equivalence : Equivalence SameKind where
  refl _ := Or.inl rfl
  symm := fun | Or.inl h => Or.inl h.symm | Or.inr h => Or.inr h.symm
  trans := fun
    | Or.inl rfl, h => h
    | Or.inr h, Or.inl rfl => Or.inr h
    | Or.inr h, Or.inr h' => Or.inr ⟨h.1, h'.2⟩

/-- Atomic agreement in `ℕ ⊕ ℕ` is witnessed by a permutation of the unlabelled points. -/
theorem labelled_homogeneous {n : ℕ} (a b : Fin n → ℕ ⊕ ℕ)
    (h : SameAtomicType (L := labelLang) a b) : ∃ e : (ℕ ⊕ ℕ) ≃[labelLang] (ℕ ⊕ ℕ), ⇑e ∘ a = b := by
  have hP : ∀ j i, a j = Sum.inl i ↔ b j = Sum.inl i := fun j i ↦
    h (AtomicIdx.rel (LabelRel.P i) fun _ ↦ j)
  have hE : ∀ j, SameKind (a j) (b j) := fun j ↦ by
    rcases ha : a j with i | p
    · exact Or.inl ((hP j i).1 ha).symm
    · rcases hb : b j with i | q
      · exact absurd ((hP j i).2 hb) (by rw [ha]; exact Sum.inr_ne_inl)
      · exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨e, he, hEe, -⟩ := FiberAssembly.exists_equiv_of_matching sameKind_equivalence n a b
    (fun i j ↦ h (AtomicIdx.eq i j)) hE
  refine ⟨{ toEquiv := e, map_rel' := fun {_} r x ↦ ?_ }, funext he⟩
  cases r with
  | P i =>
    change e (x 0) = Sum.inl i ↔ x 0 = Sum.inl i
    rcases hEe (x 0) with hx | ⟨hx, hy⟩
    · rw [← hx]
    · constructor <;> intro hi
      · rw [hi] at hy; exact absurd hy (by simp)
      · rw [hi] at hx; exact absurd hx (by simp)

theorem labelled_isOrbit :
    IsOrbitFormulaFamily (L := labelLang) (M := ℕ ⊕ ℕ) fun _ a ↦ atomicDiagram (L := labelLang) a :=
  atomicDiagram_isOrbitFormulaFamily fun _ a b h ↦ labelled_homogeneous a b h

/-- **Negative:** in `ℕ` every point is labelled, so the sentence of `ℕ ⊕ ℕ` fails there. -/
theorem labelledOnly_not_realizes :
    ¬ (montalbanSentence fun _ a ↦
        atomicDiagram (L := labelLang) (M := ℕ ⊕ ℕ) a).realize_as_sentence ℕ := fun h ↦ by
  obtain ⟨e⟩ := (montalbanSentence_characterizes labelled_isOrbit ℕ).1 h
  have := (e.map_rel (LabelRel.P (e (Sum.inr 0))) ![Sum.inr 0]).1
  change (e (Sum.inr 0) = e (Sum.inr 0) → (Sum.inr 0 : ℕ ⊕ ℕ) = Sum.inl (e (Sum.inr 0))) at this
  exact Sum.inr_ne_inl (this rfl)

end Labels

/-! ### A nullary and a unary symbol: a finite structure, the atomic-diagram conjunct, and the
empty carrier -/

section Tags

/-- A nullary relation symbol `S` and a unary relation symbol `P`. -/
inductive TagRel : ℕ → Type
  /-- The nullary symbol. -/
  | S : TagRel 0
  /-- The unary symbol. -/
  | P : TagRel 1

/-- The language with `S` and `P`. -/
abbrev tagLang : Language.{0, 0} := ⟨fun _ ↦ Empty, TagRel⟩

instance : Countable (Σ l, tagLang.Relations l) :=
  Function.Injective.countable (f := Sigma.fst) fun
    | ⟨_, .S⟩, ⟨_, .S⟩, _ => rfl
    | ⟨_, .P⟩, ⟨_, .P⟩, _ => rfl
    | ⟨_, .S⟩, ⟨_, .P⟩, h => absurd h (by decide)
    | ⟨_, .P⟩, ⟨_, .S⟩, h => absurd h (by decide)

/-- The structure with nullary fact `s` and unary predicate `p`. -/
abbrev tagStr (X : Type*) (s : Prop) (p : X → Prop) : tagLang.Structure X where
  funMap f := Empty.elim f
  RelMap | .S, _ => s | .P, x => p (x 0)

instance : tagLang.Structure Bool := tagStr Bool True (· = true)
instance : tagLang.Structure Unit := tagStr Unit True fun _ ↦ True
instance : tagLang.Structure (Fin 1) := tagStr (Fin 1) True fun _ ↦ False
instance : tagLang.Structure Empty := tagStr Empty True fun _ ↦ False
instance : tagLang.Structure (Fin 0) := tagStr (Fin 0) True fun _ ↦ False
instance : tagLang.Structure PEmpty.{1} := tagStr PEmpty False fun _ ↦ False

/-! #### A finite rigid structure -/

/-- `Bool` with `P` true only at `true` is rigid; atomic agreement is equality. -/
theorem bool_homogeneous {n : ℕ} (a b : Fin n → Bool) (h : SameAtomicType (L := tagLang) a b) :
    ∃ e : Bool ≃[tagLang] Bool, ⇑e ∘ a = b :=
  ⟨Language.Equiv.refl tagLang Bool,
    funext fun i ↦ Bool.eq_iff_iff.2 (h (AtomicIdx.rel TagRel.P fun _ ↦ i))⟩

theorem bool_isOrbit :
    IsOrbitFormulaFamily (L := tagLang) (M := Bool) fun _ a ↦ atomicDiagram (L := tagLang) a :=
  atomicDiagram_isOrbitFormulaFamily fun _ a b h ↦ bool_homogeneous a b h

theorem bool_self :
    (montalbanSentence fun _ a ↦ atomicDiagram (L := tagLang) (M := Bool) a).realize_as_sentence
      Bool :=
  montalbanSentence_self bool_isOrbit

/-- **B2 on a finite structure**: every countable model of the sentence of `Bool` has exactly
two elements, one satisfying `P`. -/
theorem bool_two (N : Type) [tagLang.Structure N] [Countable N]
    (h : (montalbanSentence fun _ a ↦
      atomicDiagram (L := tagLang) (M := Bool) a).realize_as_sentence N) :
    ∃ x y : N, x ≠ y ∧ (∀ z, z = x ∨ z = y) ∧ Structure.RelMap (L := tagLang) TagRel.P ![x] ∧
      ¬ Structure.RelMap (L := tagLang) TagRel.P ![y] := by
  obtain ⟨e⟩ := nonempty_equiv_of_realize_montalbanSentence _ N h
  have hc : ∀ b, ⇑e ∘ ![b] = ![e b] := fun b ↦ funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
  refine ⟨e true, e false, fun h ↦ Bool.noConfusion (e.injective h), fun z ↦ ?_, ?_, ?_⟩
  · rcases hz : e.symm z with _ | _
    · exact Or.inr (by rw [← hz, e.apply_symm_apply])
    · exact Or.inl (by rw [← hz, e.apply_symm_apply])
  · have := (e.map_rel TagRel.P ![true]).2 rfl
    rwa [hc] at this
  · intro hP
    have := (e.map_rel TagRel.P ![false]).1 (by rwa [hc])
    exact Bool.noConfusion this

/-! #### The atomic-diagram conjunct is needed -/

/-- On one point, the formulas `⊤` define every orbit. -/
abbrev topΦ : ∀ n, (Fin n → Unit) → tagLang.Formulaω (Fin n) := fun _ _ ↦ ⊤

theorem top_isOrbit : IsOrbitFormulaFamily (L := tagLang) topΦ := fun _ _ _ ↦
  ⟨fun _ ↦ ⟨Language.Equiv.refl _ _, Subsingleton.elim _ _⟩, fun _ ↦ Formulaω.realize_top.2 trivial⟩

/-- The sentence from the same clauses with `⊤` in place of the atomic diagram. -/
def noDiagramSentence {M : Type} [Countable M] (Φ : ∀ n, (Fin n → M) → tagLang.Formulaω (Fin n)) :
    tagLang.Formulaω (Fin 0) :=
  haveI : Encodable (Σ n, Fin n → M) := Encodable.ofCountable _
  Φ 0 Fin.elim0 ⊓ BoundedFormulaω.einf fun p : Σ n, Fin n → M ↦
    forallTuple p.1 (montalbanClauseBody (Φ p.1 p.2) ⊤ fun m ↦ Φ (p.1 + 1) (Fin.snoc p.2 m))

/-- Without the atomic-diagram conjunct, the clauses for `⊤` hold in every nonempty structure. -/
theorem noDiagram_holds (N : Type) [tagLang.Structure N] [Nonempty N] :
    (noDiagramSentence topΦ).realize_as_sentence N := by
  simp only [noDiagramSentence, Formulaω.realize_as_sentence, Formulaω.realize_inf,
    Formulaω.realize_einf, realize_forallTuple, realize_montalbanClauseBody, Formulaω.realize_top]
  exact ⟨trivial, fun _ _ _ ↦ ⟨trivial, fun _ ↦ ⟨Classical.arbitrary N, trivial⟩,
    fun _ ↦ ⟨(), trivial⟩⟩⟩

/-- **`montalbanSentence` separates `P` true from `P` false on one point**, where the sentence
without the atomic diagram holds in both. -/
theorem atomicDiagram_needed :
    (noDiagramSentence topΦ).realize_as_sentence Unit ∧
      (noDiagramSentence topΦ).realize_as_sentence (Fin 1) ∧
      (montalbanSentence topΦ).realize_as_sentence Unit ∧
      ¬ (montalbanSentence topΦ).realize_as_sentence (Fin 1) := by
  refine ⟨noDiagram_holds Unit, noDiagram_holds (Fin 1), montalbanSentence_self top_isOrbit,
    fun h ↦ ?_⟩
  obtain ⟨e⟩ := (montalbanSentence_characterizes top_isOrbit (Fin 1)).1 h
  exact (e.map_rel TagRel.P ![()]).2 trivial

/-! #### The empty carrier and the nullary facts -/

/-- The atomic diagrams of the empty structure `Empty` (where `S` holds). -/
abbrev emptyΦ : ∀ n, (Fin n → Empty) → tagLang.Formulaω (Fin n) :=
  fun _ a ↦ atomicDiagram (L := tagLang) a

/-- The atomic diagrams of the empty structure `PEmpty` (where `S` fails). -/
abbrev pemptyΦ : ∀ n, (Fin n → PEmpty.{1}) → tagLang.Formulaω (Fin n) :=
  fun _ a ↦ atomicDiagram (L := tagLang) a

theorem empty_isOrbit : IsOrbitFormulaFamily (L := tagLang) emptyΦ :=
  atomicDiagram_isOrbitFormulaFamily fun _ a _ _ ↦
    ⟨Language.Equiv.refl _ _, funext fun i ↦ (a i).elim⟩

theorem pempty_isOrbit : IsOrbitFormulaFamily (L := tagLang) pemptyΦ :=
  atomicDiagram_isOrbitFormulaFamily fun _ a _ _ ↦
    ⟨Language.Equiv.refl _ _, funext fun i ↦ (a i).elim⟩

/-- **B2 on the empty carrier**: a countable model of the sentence of `Empty` is empty and
satisfies the nullary `S`, as `Empty` does. -/
theorem empty_model (N : Type) [tagLang.Structure N] [Countable N]
    (h : (montalbanSentence emptyΦ).realize_as_sentence N) :
    IsEmpty N ∧ Structure.RelMap (L := tagLang) TagRel.S (Fin.elim0 : Fin 0 → N) := by
  obtain ⟨e⟩ := nonempty_equiv_of_realize_montalbanSentence emptyΦ N h
  refine ⟨⟨fun y ↦ (e.symm y).elim⟩, ?_⟩
  have := (e.map_rel TagRel.S (Fin.elim0 : Fin 0 → Empty)).2 trivial
  rwa [comp_fin_elim0] at this

/-- `Fin 0` with `S` true satisfies the sentence of `Empty`. -/
theorem fin0_realizes : (montalbanSentence emptyΦ).realize_as_sentence (Fin 0) :=
  (montalbanSentence_characterizes empty_isOrbit (Fin 0)).2
    ⟨{ toEquiv := Equiv.equivOfIsEmpty Empty (Fin 0)
       map_rel' := fun {_} r _ ↦ by cases r <;> exact Iff.rfl }⟩

/-- **Negative:** `PEmpty`, empty but with `S` false, does not satisfy the sentence of `Empty`. -/
theorem pempty_not_realizes : ¬ (montalbanSentence emptyΦ).realize_as_sentence PEmpty.{1} :=
  fun h ↦ (empty_model PEmpty h).2

/-- **Negative, symmetric:** `Empty`, with `S` true, does not satisfy the sentence of `PEmpty`. -/
theorem empty_not_realizes_pempty : ¬ (montalbanSentence pemptyΦ).realize_as_sentence Empty :=
  fun h ↦ (nonempty_equiv_of_realize_montalbanSentence pemptyΦ Empty h).elim fun e ↦
    (e.map_rel TagRel.S (Fin.elim0 : Fin 0 → PEmpty)).1 (by rw [comp_fin_elim0]; trivial)

/-- **Negative:** the one-point `Unit` does not satisfy the sentence of `Empty`. -/
theorem unit_not_realizes_empty : ¬ (montalbanSentence emptyΦ).realize_as_sentence Unit :=
  fun h ↦ (empty_model Unit h).1.false ()

end Tags

/-! ### The pointed form on the pure set -/

section Pointed

/-- Atomic diagrams over parameters `c` in the pure set `ℕ`. -/
abbrev pureΦc {k : ℕ} (c : Fin k → ℕ) :
    ∀ n, (Fin n → ℕ) → Language.empty.Formulaω (Fin (k + n)) :=
  fun _ a ↦ atomicDiagram (L := Language.empty) (Fin.append c a)

theorem pure_isOrbitPointed {k : ℕ} (c : Fin k → ℕ) :
    IsOrbitFormulaFamilyPointed (L := Language.empty) c (pureΦc c) :=
  atomicDiagram_isOrbitFormulaFamilyPointed (fun _ a b h ↦ pure_homogeneous a b h) c

/-- The pointed characterization on `ℕ`. -/
theorem pure_pointed_iff {k : ℕ} (c d : Fin k → ℕ) :
    (montalbanSentencePointed c (pureΦc c)).Realize d ↔
      ∃ e : ℕ ≃[Language.empty] ℕ, ⇑e ∘ c = d :=
  montalbanSentencePointed_characterizes (pure_isOrbitPointed c) ℕ d

/-- The pointed sentence holds at every tuple with the equality pattern of `c`. -/
theorem pure_pointed_of_pattern {k : ℕ} (c d : Fin k → ℕ) (h : ∀ i j, c i = c j ↔ d i = d j) :
    (montalbanSentencePointed c (pureΦc c)).Realize d :=
  (pure_pointed_iff c d).2 (pure_homogeneous c d fun idx ↦ by
    cases idx with
    | eq i j => exact h i j
    | rel R _ => exact isEmptyElim R)

/-- **B1, pointed**, with one parameter. -/
theorem pointed_self_one : (montalbanSentencePointed ![3] (pureΦc ![3])).Realize ![3] :=
  montalbanSentencePointed_self (pure_isOrbitPointed _)

/-- **One parameter**: the isomorphism produced by B2 carries `3` to `5`. -/
theorem pointed_one : ∃ e : ℕ ≃[Language.empty] ℕ, e 3 = 5 := by
  obtain ⟨e, he⟩ := exists_equiv_of_realize_montalbanSentencePointed ![3] (pureΦc ![3]) ℕ ![5]
    (pure_pointed_of_pattern _ _ (by decide))
  exact ⟨e, congrFun he 0⟩

/-- **Two parameters**: `(1, 2) ↦ (7, 4)`. -/
theorem pointed_two : ∃ e : ℕ ≃[Language.empty] ℕ, e 1 = 7 ∧ e 2 = 4 := by
  obtain ⟨e, he⟩ := exists_equiv_of_realize_montalbanSentencePointed ![1, 2] (pureΦc ![1, 2]) ℕ
    ![7, 4] (pure_pointed_of_pattern _ _ (by decide))
  exact ⟨e, congrFun he 0, congrFun he 1⟩

/-- **A repeated parameter**: `(1, 1) ↦ (4, 4)`. -/
theorem pointed_repeated : ∃ e : ℕ ≃[Language.empty] ℕ, e 1 = 4 := by
  obtain ⟨e, he⟩ := exists_equiv_of_realize_montalbanSentencePointed ![1, 1] (pureΦc ![1, 1]) ℕ
    ![4, 4] (pure_pointed_of_pattern _ _ (by decide))
  exact ⟨e, congrFun he 0⟩

/-- **Negative, repeated parameter**: `(1, 1)` is not carried to `(4, 5)`, so the pointed
sentence fails there; B2 alone, through the equality atoms. -/
theorem pointed_repeated_not :
    ¬ (montalbanSentencePointed ![1, 1] (pureΦc ![1, 1])).Realize (![4, 5] : Fin 2 → ℕ) :=
  fun h ↦ by
    obtain ⟨e, he⟩ := exists_equiv_of_realize_montalbanSentencePointed _ _ ℕ _ h
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    omega

/-- **`k = 0` compatibility** on the pure set. -/
theorem compat_pure (N : Type) :
    (montalbanSentence (pureΦ ℕ)).realize_as_sentence N ↔
      (montalbanSentencePointed (Fin.elim0 : Fin 0 → ℕ) fun n a ↦
        BoundedFormulaω.mapFreeVars (Fin.cast (Nat.zero_add n).symm) (pureΦ ℕ n a)).Realize
          (Fin.elim0 : Fin 0 → N) :=
  realize_montalbanSentence_iff_pointed _

/-- **`k = 0` as a syntactic equation** on the pure set: the pointed sentence over the empty
tuple, read as a sentence, holds in `ℤ`, by rewriting it into the unpointed one. -/
theorem eq_pointed_pure :
    (montalbanSentencePointed (Fin.elim0 : Fin 0 → ℕ) fun n a ↦
      BoundedFormulaω.mapFreeVars (Fin.cast (Nat.zero_add n).symm)
        (pureΦ ℕ n a)).realize_as_sentence ℤ := by
  rw [← montalbanSentence_eq_pointed_elim0]
  exact int_realizes

/-- The pointed B2 at the empty parameter tuple, through the compatibility lemma. -/
theorem pointed_zero : ∃ e : ℕ ≃[Language.empty] ℤ, ⇑e ∘ (Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 :=
  exists_equiv_of_realize_montalbanSentencePointed _ _ ℤ _ ((compat_pure ℤ).1 int_realizes)

end Pointed

/-! ### The empty tuple and the tuple quantifiers -/

section Tuples

/-- **The seed is a conjunct**: with `⊥` as the orbit formula of the empty tuple, the sentence
holds nowhere. -/
theorem bot_seed (N : Type) :
    ¬ (montalbanSentence fun n (_ : Fin n → ℕ) ↦
      (⊥ : Language.empty.Formulaω (Fin n))).realize_as_sentence N := by
  rw [realize_montalbanSentence]
  simp

/-- `x₀ ≠ x₁`. -/
def neq01 : Language.empty.Formulaω (Fin 2) :=
  (BoundedFormulaω.equal (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))).not

theorem realize_neq01 {N : Type} (b : Fin 2 → N) : neq01.Realize b ↔ b 0 ≠ b 1 := by
  simp [neq01, Formulaω.realize_def]

/-- `existsTuple`: two distinct points exist in `ℕ` and not in `Unit`. -/
theorem existsTuple_examples :
    (existsTuple 2 neq01).realize_as_sentence ℕ ∧
      ¬ (existsTuple 2 neq01).realize_as_sentence Unit := by
  unfold Formulaω.realize_as_sentence
  rw [realize_existsTuple, realize_existsTuple]
  exact ⟨⟨![0, 1], (realize_neq01 _).2 (by decide)⟩,
    fun ⟨b, hb⟩ ↦ (realize_neq01 b).1 hb (Subsingleton.elim _ _)⟩

/-- `forallTuple`: not all pairs of `ℕ` are distinct; `forallTupleFrom`: some point equals the
parameter `0`. -/
theorem forallTuple_examples :
    ¬ (forallTuple 2 neq01).realize_as_sentence ℕ ∧
      ¬ (forallTupleFrom 1 1 neq01).Realize (![0] : Fin 1 → ℕ) := by
  unfold Formulaω.realize_as_sentence
  rw [realize_forallTuple, realize_forallTupleFrom]
  exact ⟨fun h ↦ (realize_neq01 _).1 (h ![0, 0]) rfl, fun h ↦ (realize_neq01 _).1 (h ![0]) rfl⟩

/-- The tuple quantifiers at length `0` are the identity. -/
theorem tuple_zero (φ : Language.empty.Formulaω (Fin 0)) (N : Type) :
    ((forallTuple 0 φ).realize_as_sentence N ↔ φ.realize_as_sentence N) ∧
      ((existsTuple 0 φ).realize_as_sentence N ↔ φ.realize_as_sentence N) := by
  unfold Formulaω.realize_as_sentence
  rw [realize_forallTuple, realize_existsTuple]
  exact ⟨⟨fun h ↦ h _, fun h b ↦ Subsingleton.elim b Fin.elim0 ▸ h⟩,
    ⟨fun ⟨b, hb⟩ ↦ Subsingleton.elim b Fin.elim0 ▸ hb, fun h ↦ ⟨_, h⟩⟩⟩

/-- **`simp` normal form**: the tuple quantifiers are `@[simp]`, so `simp` turns `existsTuple`
and `forallTuple` into Lean quantifiers over tuples. -/
theorem simp_tupleQuantifiers {N : Type} (n : ℕ) (φ ψ : Language.empty.Formulaω (Fin n))
    (v : Fin 0 → N) :
    (existsTuple n φ).Realize v ∧ (forallTuple n ψ).Realize v ↔
      (∃ b : Fin n → N, φ.Realize b) ∧ ∀ b : Fin n → N, ψ.Realize b := by
  simp

/-- **`simp` normal form** for `forallTupleFrom`, here around a clause body, which `simp` also
unfolds (`realize_montalbanClauseBody` is `@[simp]`). -/
theorem simp_forallTupleFrom {N : Type} (k n : ℕ) (θ D : Language.empty.Formulaω (Fin (k + n)))
    (ψ : ℕ → Language.empty.Formulaω (Fin (k + n + 1))) (d : Fin k → N) :
    (forallTupleFrom k n (montalbanClauseBody θ D ψ)).Realize d ↔
      ∀ b : Fin n → N, θ.Realize (Fin.append d b) → D.Realize (Fin.append d b) ∧
        (∀ m, ∃ y, (ψ m).Realize (Fin.snoc (Fin.append d b) y)) ∧
          ∀ y, ∃ m, (ψ m).Realize (Fin.snoc (Fin.append d b) y) := by
  simp

end Tuples

end MontalbanGuard

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
  let target := `InfinitaryLogic.Scott.MontalbanSentence
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Scott.Sentence,
            `InfinitaryLogic.Lomega1omega.Theory] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let hits := cl.toList.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-- The public declarations of the module. -/
def moduleDecls : List Name :=
  [`forallTuple, `existsTuple, `forallTupleFrom, `realize_forallTuple, `realize_existsTuple,
   `realize_forallTupleFrom, `montalbanClauseBody, `realize_montalbanClauseBody,
   `montalbanClausePointed, `montalbanSentencePointed, `IsOrbitFormulaFamilyPointed,
   `realize_montalbanSentencePointed, `montalbanSentencePointed_self,
   `exists_equiv_of_realize_montalbanSentencePointed, `montalbanSentencePointed_characterizes,
   `montalbanClause, `montalbanSentence, `IsOrbitFormulaFamily, `realize_montalbanSentence,
   `realize_montalbanSentence_iff_pointed, `montalbanSentence_self,
   `nonempty_equiv_of_realize_montalbanSentence,
   `montalbanSentence_characterizes, `montalbanSentence_eq_pointed_elim0].map
    (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`atomicDiagram_isOrbitFormulaFamily, `atomicDiagram_isOrbitFormulaFamilyPointed,
   `pure_homogeneous, `nat_self, `nat_characterizes, `int_realizes, `nat_int_equiv,
   `fin3_not_realizes, `ulift_characterizes, `rat_extend, `rat_realize_pointed,
   `rat_homogeneous, `rat_isOrbit, `rat_characterizes, `nat_not_realizes_rat,
   `labelled_homogeneous, `labelled_isOrbit, `labelledOnly_not_realizes, `bool_isOrbit,
   `bool_self, `bool_two, `top_isOrbit, `noDiagram_holds, `atomicDiagram_needed,
   `empty_isOrbit, `pempty_isOrbit, `empty_model, `fin0_realizes, `pempty_not_realizes,
   `empty_not_realizes_pempty, `unit_not_realizes_empty, `pure_isOrbitPointed,
   `pure_pointed_iff, `pure_pointed_of_pattern, `pointed_self_one, `pointed_one, `pointed_two,
   `pointed_repeated, `pointed_repeated_not, `compat_pure, `eq_pointed_pure, `pointed_zero,
   `bot_seed, `existsTuple_examples, `forallTuple_examples, `tuple_zero,
   `simp_tupleQuantifiers, `simp_forallTupleFrom].map (`MontalbanGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in moduleDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Montalban-sentence regression guard: OK (applied: atomic diagrams as orbit \
    families, unpointed and pointed; the infinite pure set N against Z and Fin 3, and on the \
    Type 1 carrier ULift N; (Q, <) ultrahomogeneous by the pointed B2 from the one-point \
    extension property, its sentence failing in (N, <); labelled and unlabelled points with \
    the infinitary orbit formula not-or-P_i, failing where every point is labelled; the rigid \
    finite Bool, every countable model having two points; the atomic-diagram conjunct needed on \
    one point; the empty carrier, with models empty and satisfying the same nullary fact, \
    Fin 0 positive, PEmpty with the nullary fact false negative in both directions, Unit \
    negative; pointed with one, two and a repeated parameter, the produced isomorphism carrying \
    them, and a repeated parameter not carried to distinct values; k = 0 compatibility, \
    semantic and as a syntactic equation; the clause-by-clause characterizations used by \
    rewriting; the empty-tuple seed and tuple \
    quantifiers, closed by simp; import closure without Scott-process, descriptive, \
    method, model-theory, admissible or conditional modules; standard axioms)"
