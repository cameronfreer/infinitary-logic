/-
Regression guard for the quantifier rank of Montalbán's explicit Scott sentence
(`InfinitaryLogic/Scott/MontalbanQuantifierRank.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **The clause body.**  Over the empty carrier, `montalbanClauseBody ⊤ ⊤ (fun _ ↦ ⊤)` has rank
  exactly `1`: the back conjunct `∀y ⋁_m` adds `1` although the disjunction is empty.  The
  bound `α + 1` on a concrete body over `ℕ` at `α = ω + 1`.
* **Attainment of `α + ω` at an infinite level.**  The family
  `Φ n a := eqPattern a ⊓ pad n` on the pure set `ℕ`, where `pad n` has rank exactly
  `α = ω + 1` (one existential over the rank-`ω` conjunction `⋀_m ∃ m-tuple ⊤`), has every
  formula of rank exactly `α`; its sentence has rank exactly `(ω + 1) + ω = ω + ω`.  This is
  strictly above `α`, and it is **not** `ω + (ω + 1)`: the `ω` is added on the right.  The same
  attainment at the `Type 1` carrier `ULift.{1} ℕ`, unpointed and pointed.
* **The general exact value `max (Φ 0 ⟨⟩).qrank (α + ω)`** (`..._eq_max`).  On `ℕ`, a seed of
  rank `ω + 1` over equality patterns at positive lengths (`α = 0`) gives rank exactly `ω + 1`,
  not `0 + ω`: the seed dominates, unpointed and pointed over `(1, 1)`.  At the padded family
  the general value agrees with the attainment above.
* **Finite levels give `ω`.**  For any family of rank at most a natural number `k`, the
  sentence has rank at most `ω`; the family `∃ 3-tuple ⊤` on `ℕ` gives exactly `ω`.
* **The infinite pure set.**  The equality patterns (rank `0`) define the orbits of `ℕ`, so
  their sentence is a Scott sentence of `ℕ` (`montalbanSentence_characterizes`; it holds in `ℤ`
  and fails in `Fin 3`), and its rank is exactly `ω`.
* **The empty carrier.**  On `PEmpty` in any universe the rank is exactly
  `max (Φ 0 ⟨⟩).qrank 1`: `1` for the equality patterns, and `ω + 1` with the seed `pad 0`
  (the seed dominates; the bound `(ω + 1) + ω` is not attained).
* **Repeated parameters.**  Over `c = (1, 1)` in `ℕ`, the pointed equality patterns give a
  pointed sentence of rank exactly `ω`; over `c = (1, 1, 1)` in `ULift.{1} ℕ` with the padding,
  rank exactly `ω + ω`.  The seed is below the rank, through the exact clause-by-clause forms.
* **Import closure** of the module: exactly the 19 expected `InfinitaryLogic` modules
  (`[CLOSURE DRIFT]` otherwise).  The closure check and the axiom audit share one command, so
  the final OK line is printed only if both pass.
* **Standard axioms** for every public declaration added by the tranche and for the guard's own
  theorems.

Run with: lake env lean scripts/check_montalban_qrank_regressions.lean
-/
import InfinitaryLogic.Scott.MontalbanQuantifierRank
import InfinitaryLogic.Scott.FiniteMatching

set_option warningAsError true

open Lean FirstOrder FirstOrder.Language Structure BoundedFormulaω

universe u v w

noncomputable section

namespace MontalbanQRankGuard

attribute [local instance] Language.emptyStructure

/-! ### Equality patterns and padding -/

section Patterns

variable {L : Language.{u, v}}

/-- A finite conjunction, as a fold of `⊓`. -/
def finConj {β : Type*} (l : List (L.Formulaω β)) : L.Formulaω β := l.foldr (· ⊓ ·) ⊤

theorem realize_finConj {β : Type*} {M : Type*} [L.Structure M] (l : List (L.Formulaω β))
    (v : β → M) : (finConj l).Realize v ↔ ∀ φ ∈ l, φ.Realize v := by
  induction l with
  | nil => simp [finConj, Formulaω.realize_def]
  | cons φ l ih => simp [finConj, Formulaω.realize_inf, ← ih]

theorem qrank_finConj {β : Type*} (l : List (L.Formulaω β)) (h : ∀ φ ∈ l, φ.qrank = 0) :
    (finConj l).qrank = 0 := by
  induction l with
  | nil => exact qrank_top
  | cons φ l ih =>
    simp only [List.mem_cons, forall_eq_or_imp, Formulaω.qrank] at h
    simp only [finConj, List.foldr_cons, Formulaω.qrank, qrank_inf] at ih ⊢
    rw [h.1, ih h.2, max_self]

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

/-- An equality pattern has quantifier rank `0`. -/
theorem qrank_eqPattern {X : Type*} {n : ℕ} (a : Fin n → X) :
    (eqPattern (L := L) a).qrank = 0 := by
  classical
  refine qrank_finConj _ fun φ hφ ↦ ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
  refine qrank_finConj _ fun ψ hψ ↦ ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hψ
  split_ifs <;> simp [eqAtom]

/-- `m` existential quantifiers over `⊤`, above `n` free variables: rank exactly `m`. -/
def deep (n m : ℕ) : L.Formulaω (Fin n) := existsTupleFrom n m ⊤

theorem qrank_deep (n m : ℕ) : (deep (L := L) n m).qrank = m := by
  simp [deep, qrank_existsTupleFrom]

/-- `⋀_m ∃ m-tuple ⊤`: rank exactly `ω`. -/
def deepω (n : ℕ) : L.Formulaω (Fin n) := BoundedFormulaω.iInf fun m ↦ deep n m

theorem qrank_deepω (n : ℕ) : (deepω (L := L) n).qrank = Ordinal.omega0 := by
  rw [deepω, Formulaω.qrank, qrank_iInf]
  exact (congrArg _root_.iSup (funext fun m ↦ qrank_deep (L := L) n m)).trans
    Ordinal.iSup_natCast

/-- The padding `∃y ⋀_m ∃ m-tuple ⊤`: rank exactly `ω + 1`. -/
def pad (n : ℕ) : L.Formulaω (Fin n) := existsTupleFrom n 1 (deepω (n + 1))

theorem qrank_pad (n : ℕ) : (pad (L := L) n).qrank = Ordinal.omega0 + 1 := by
  rw [pad, qrank_existsTupleFrom, qrank_deepω, Nat.cast_one]

/-- The equality pattern padded to rank exactly `ω + 1`. -/
def padΦ {X : Type*} {n : ℕ} (a : Fin n → X) : L.Formulaω (Fin n) := eqPattern a ⊓ pad n

theorem qrank_padΦ {X : Type*} {n : ℕ} (a : Fin n → X) :
    (padΦ (L := L) a).qrank = Ordinal.omega0 + 1 := by
  have h₁ : BoundedFormulaω.qrank (eqPattern (L := L) a) = 0 := qrank_eqPattern a
  have h₂ : BoundedFormulaω.qrank (pad (L := L) n) = Ordinal.omega0 + 1 := qrank_pad n
  rw [padΦ, Formulaω.qrank, qrank_inf, h₁, h₂, max_eq_right zero_le]

/-- `(ω + 1) + ω = ω + ω`, which is not `ω + (ω + 1)`. -/
theorem omega_add_one_add_omega :
    Ordinal.omega0.{0} + 1 + Ordinal.omega0 = Ordinal.omega0 + Ordinal.omega0 ∧
      Ordinal.omega0.{0} + Ordinal.omega0 ≠ Ordinal.omega0 + (Ordinal.omega0 + 1) ∧
      Ordinal.omega0.{0} + 1 < Ordinal.omega0 + Ordinal.omega0 := by
  refine ⟨by rw [add_assoc, Ordinal.one_add_omega0], ?_, ?_⟩
  · rw [← add_assoc]; exact (lt_add_of_pos_right _ zero_lt_one).ne
  · exact add_lt_add_right Ordinal.one_lt_omega0 _

end Patterns

/-! ### The clause body -/

/-- Over the empty carrier, the back conjunct `∀y ⋁_m` still contributes `1`. -/
theorem clauseBody_empty :
    (montalbanClauseBody (M := PEmpty.{w + 1}) (⊤ : Language.empty.Formulaω (Fin 0)) ⊤
      fun _ ↦ ⊤).qrank = 1 := by
  rw [qrank_montalbanClauseBody]
  simp

/-- The bound `α + 1` on a concrete body over `ℕ`, at `α = ω + 1`. -/
theorem clauseBody_le (n : ℕ) (a : Fin n → ℕ) :
    (montalbanClauseBody (padΦ (L := Language.empty) a) (atomicDiagram (L := Language.empty) a)
      fun m ↦ padΦ (Fin.snoc a m)).qrank ≤ Ordinal.omega0 + 1 + 1 :=
  qrank_montalbanClauseBody_le ((qrank_padΦ a).trans_le (Order.le_succ _))
    ((atomicDiagram_qrank_eq_zero (L := Language.empty) a).trans_le zero_le)
    fun _ ↦ (qrank_padΦ _).le

/-! ### Attainment of `α + ω` -/

/-- **Attainment at `α = ω + 1`** on the pure set `ℕ`: rank exactly `ω + ω`, above `α` and not
`ω + α`. -/
theorem attain_nat :
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ padΦ a).qrank =
      Ordinal.omega0 + Ordinal.omega0 ∧
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ padΦ a).qrank ≠
      Ordinal.omega0 + (Ordinal.omega0 + 1) ∧
    Ordinal.omega0 + 1 < (montalbanSentence (L := Language.empty) (M := ℕ)
      fun _ a ↦ padΦ a).qrank := by
  have h := qrank_montalbanSentence_eq_add_omega0 (L := Language.empty) (M := ℕ)
    (α := Ordinal.omega0 + 1) (Φ := fun _ a ↦ padΦ a) (qrank_padΦ _).le
    fun _ a ↦ qrank_padΦ a
  rw [h, omega_add_one_add_omega.1]
  exact ⟨rfl, omega_add_one_add_omega.2⟩

/-- **The bound** at the same family, through `qrank_montalbanSentence_le`. -/
theorem bound_nat :
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ padΦ a).qrank ≤
      Ordinal.omega0 + 1 + Ordinal.omega0 :=
  qrank_montalbanSentence_le fun _ a ↦ (qrank_padΦ a).le

/-- **`Type 1` carrier**: the bound and its attainment at `ULift.{1} ℕ`. -/
theorem attain_ulift :
    (montalbanSentence (L := Language.empty) (M := ULift.{1} ℕ) fun _ a ↦ padΦ a).qrank =
      Ordinal.omega0 + Ordinal.omega0 ∧
    (montalbanSentence (L := Language.empty) (M := ULift.{1} ℕ) fun _ a ↦ padΦ a).qrank ≤
      Ordinal.omega0 + 1 + Ordinal.omega0 := by
  refine ⟨?_, qrank_montalbanSentence_le fun _ a ↦ (qrank_padΦ a).le⟩
  rw [qrank_montalbanSentence_eq_add_omega0 (α := Ordinal.omega0 + 1)
    (qrank_padΦ _).le fun _ a ↦ qrank_padΦ a, omega_add_one_add_omega.1]

/-! ### Finite levels -/

/-- **Finite levels give `ω`**: a family of rank at most a natural number `k`, on any carrier,
has a sentence of rank at most `ω`, unpointed and pointed. -/
theorem finite_level {L : Language.{u, v}} [Countable (Σ l, L.Relations l)] {M : Type w}
    [L.Structure M] [Countable M] (k : ℕ) {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)}
    (hΦ : ∀ n a, (Φ n a).qrank ≤ k) {j : ℕ} (c : Fin j → M)
    {Ψ : ∀ n, (Fin n → M) → L.Formulaω (Fin (j + n))} (hΨ : ∀ n a, (Ψ n a).qrank ≤ k) :
    (montalbanSentence Φ).qrank ≤ Ordinal.omega0 ∧
      (montalbanSentencePointed c Ψ).qrank ≤ Ordinal.omega0 :=
  ⟨(qrank_montalbanSentence_le hΦ).trans_eq (Ordinal.natCast_add_omega0 k),
    (qrank_montalbanSentencePointed_le c hΨ).trans_eq (Ordinal.natCast_add_omega0 k)⟩

/-- The family `∃ 3-tuple ⊤` on `ℕ`: rank exactly `3 + ω = ω`. -/
theorem finite_level_exact :
    (montalbanSentence (L := Language.empty) (M := ℕ) fun n _ ↦ deep n 3).qrank =
      Ordinal.omega0 := by
  rw [qrank_montalbanSentence_eq_add_omega0 (α := 3) (qrank_deep 0 3).le
    fun n _ ↦ qrank_deep (n + 1) 3]
  exact Ordinal.natCast_add_omega0 3

/-! ### The infinite pure set -/

/-- In the empty language, a common equality pattern is witnessed by a permutation. -/
theorem pure_homogeneous {X : Type w} {n : ℕ} (a b : Fin n → X)
    (h : ∀ i j, a i = a j ↔ b i = b j) : ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  obtain ⟨e, he, -, -⟩ := FiberAssembly.exists_equiv_of_matching
    (E := fun (_ _ : X) ↦ True) ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩ n a b h
    (fun _ ↦ trivial)
  exact ⟨{ toEquiv := e }, funext he⟩

/-- The equality patterns define the orbits of a pure set. -/
theorem pure_isOrbit (X : Type w) :
    IsOrbitFormulaFamily (L := Language.empty) (M := X) fun _ a ↦ eqPattern a := by
  intro n a b
  rw [realize_eqPattern]
  refine ⟨pure_homogeneous a b, fun ⟨e, he⟩ i j ↦ ?_⟩
  subst he
  exact e.injective.eq_iff.symm

/-- **The infinite pure set**: the sentence of the equality patterns is a Scott sentence of
`ℕ` (it holds in `ℤ` and fails in `Fin 3`), of rank exactly `ω`, within the bound `0 + ω`. -/
theorem pure_nat :
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ eqPattern a).qrank =
      Ordinal.omega0 ∧
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ eqPattern a).qrank ≤
      0 + Ordinal.omega0 ∧
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ eqPattern a).realize_as_sentence
      ℤ ∧
    ¬ (montalbanSentence (L := Language.empty) (M := ℕ)
      fun _ a ↦ eqPattern a).realize_as_sentence (Fin 3) := by
  have hZ : Nonempty (ℕ ≃[Language.empty] ℤ) := ⟨{ toEquiv := Equiv.intEquivNat.symm }⟩
  have hF : ¬ Nonempty (ℕ ≃[Language.empty] Fin 3) := fun ⟨e⟩ ↦
    not_finite_iff_infinite.2 inferInstance (Finite.of_equiv _ e.toEquiv.symm : Finite ℕ)
  have hS := montalbanSentence_characterizes (pure_isOrbit ℕ)
  refine ⟨?_, qrank_montalbanSentence_le fun _ a ↦ (qrank_eqPattern a).le,
    (hS ℤ).2 hZ, fun h ↦ hF ((hS (Fin 3)).1 h)⟩
  rw [qrank_montalbanSentence_eq_add_omega0 (α := 0) (qrank_eqPattern _).le
    fun _ a ↦ qrank_eqPattern a, zero_add]

/-! ### The empty carrier -/

/-- **Empty carrier** (any universe): rank exactly `max (Φ 0 ⟨⟩).qrank 1`, which is `1` for the
equality patterns and `ω + 1` with the seed `pad 0`; the bound `(ω + 1) + ω` is not attained. -/
theorem empty_carrier :
    (montalbanSentence (L := Language.empty) (M := PEmpty.{w + 1})
      fun _ a ↦ eqPattern a).qrank = 1 ∧
    (montalbanSentence (L := Language.empty) (M := PEmpty.{w + 1})
      fun _ a ↦ padΦ a).qrank = Ordinal.omega0 + 1 ∧
    (montalbanSentence (L := Language.empty) (M := PEmpty.{w + 1})
      fun _ a ↦ padΦ a).qrank < Ordinal.omega0 + 1 + Ordinal.omega0 := by
  rw [qrank_montalbanSentence_of_isEmpty, qrank_montalbanSentence_of_isEmpty, qrank_eqPattern,
    qrank_padΦ, max_eq_right zero_le, max_eq_left (le_add_self : (1 : Ordinal) ≤ _),
    omega_add_one_add_omega.1]
  exact ⟨rfl, rfl, omega_add_one_add_omega.2.2⟩

/-! ### Repeated parameters -/

/-- Equality patterns of `c⌢a`, over the parameters `c`. -/
abbrev pureΦc {X : Type w} {k : ℕ} (c : Fin k → X) :
    ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin (k + n)) :=
  fun _ a ↦ eqPattern (Fin.append c a)

/-- **Repeated parameters** `(1, 1)` in `ℕ`: the pointed sentence of the equality patterns has
rank exactly `ω`, within the bound `0 + ω`; the seed is below the rank. -/
theorem repeated_nat :
    (montalbanSentencePointed (![1, 1] : Fin 2 → ℕ) (pureΦc ![1, 1])).qrank =
      Ordinal.omega0 ∧
    (montalbanSentencePointed (![1, 1] : Fin 2 → ℕ) (pureΦc ![1, 1])).qrank ≤
      0 + Ordinal.omega0 ∧
    (pureΦc (![1, 1] : Fin 2 → ℕ) 0 Fin.elim0).qrank ≤
      (montalbanSentencePointed (![1, 1] : Fin 2 → ℕ) (pureΦc ![1, 1])).qrank := by
  refine ⟨?_, qrank_montalbanSentencePointed_le _ fun _ _ ↦ (qrank_eqPattern _).le, ?_⟩
  · rw [qrank_montalbanSentencePointed_eq_add_omega0 (α := 0) _
      (qrank_eqPattern _).le fun _ _ ↦ qrank_eqPattern _, zero_add]
  · rw [qrank_montalbanSentencePointed]
    exact le_max_left _ _

/-- **Repeated parameters at a `Type 1` carrier**: over `(1, 1, 1)` in `ULift.{1} ℕ`, the padded
pointed family gives rank exactly `ω + ω`. -/
theorem repeated_ulift :
    (montalbanSentencePointed (L := Language.empty)
      (![ULift.up 1, ULift.up 1, ULift.up 1] : Fin 3 → ULift.{1} ℕ)
      fun _ a ↦ padΦ (Fin.append ![ULift.up 1, ULift.up 1, ULift.up 1] a)).qrank =
      Ordinal.omega0 + Ordinal.omega0 := by
  rw [qrank_montalbanSentencePointed_eq_add_omega0 (α := Ordinal.omega0 + 1) _
    (qrank_padΦ _).le fun _ _ ↦ qrank_padΦ _, omega_add_one_add_omega.1]

/-! ### The general exact value: a seed that dominates -/

/-- The padded seed `pad (k + 0)` at the empty tuple, the equality patterns of `c⌢a` at
positive lengths. -/
def seedΦc {X : Type w} {k : ℕ} (c : Fin k → X) :
    ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin (k + n))
  | 0, _ => pad (k + 0)
  | _ + 1, a => eqPattern (Fin.append c a)

/-- The same family without parameters. -/
def seedΦ {X : Type w} : ∀ n, (Fin n → X) → Language.empty.Formulaω (Fin n)
  | 0, _ => pad 0
  | _ + 1, a => eqPattern a

/-- **The seed dominates** on the nonempty carrier `ℕ`: the seed has rank `ω + 1`, the positive
lengths rank exactly `0`, and the general exact value `max (ω + 1) (0 + ω)` is `ω + 1`, not
`0 + ω`; unpointed, and pointed over the repeated parameters `(1, 1)`.  On the empty carrier the
same seed gives `ω + 1` through `qrank_montalbanSentence_of_isEmpty` (`empty_carrier`). -/
theorem seed_dominates :
    (montalbanSentence (L := Language.empty) (M := ℕ) seedΦ).qrank = Ordinal.omega0 + 1 ∧
    (montalbanSentence (L := Language.empty) (M := ℕ) seedΦ).qrank ≠ 0 + Ordinal.omega0 ∧
    (montalbanSentencePointed (![1, 1] : Fin 2 → ℕ) (seedΦc ![1, 1])).qrank =
      Ordinal.omega0 + 1 := by
  have hω : max (Ordinal.omega0.{0} + 1) (0 + Ordinal.omega0) = Ordinal.omega0 + 1 := by
    rw [zero_add, max_eq_left le_self_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [qrank_montalbanSentence_eq_max (Φ := seedΦ) (α := 0) fun _ a ↦ qrank_eqPattern a]
    exact (congrArg (max · _) (qrank_pad 0)).trans hω
  · rw [qrank_montalbanSentence_eq_max (Φ := seedΦ) (α := 0) fun _ a ↦ qrank_eqPattern a,
      zero_add]
    exact ne_of_gt (lt_max_of_lt_left ((qrank_pad 0).symm ▸ Order.lt_succ _ :
      Ordinal.omega0 < (pad (L := Language.empty) 0).qrank))
  · rw [qrank_montalbanSentencePointed_eq_max (Φ := seedΦc ![1, 1]) (α := 0) _
      fun _ _ ↦ qrank_eqPattern _]
    exact (congrArg (max · _) (qrank_pad 2)).trans hω

/-- The general exact value at the padded family on `ℕ` (seed rank `ω + 1 = α`): it agrees with
`attain_nat`. -/
theorem eq_max_nat :
    (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ padΦ a).qrank =
      max (Ordinal.omega0 + 1) (Ordinal.omega0 + 1 + Ordinal.omega0) := by
  rw [qrank_montalbanSentence_eq_max (α := Ordinal.omega0 + 1) fun _ a ↦ qrank_padΦ a]
  exact congrArg (max · _) (qrank_padΦ _)

/-- The seed is below the rank, through the exact unpointed form. -/
theorem seed_le_nat :
    (eqPattern (L := Language.empty) (Fin.elim0 : Fin 0 → ℕ)).qrank ≤
      (montalbanSentence (L := Language.empty) (M := ℕ) fun _ a ↦ eqPattern a).qrank := by
  rw [qrank_montalbanSentence]
  exact le_max_left _ _

end MontalbanQRankGuard

end

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

/-- The exact `InfinitaryLogic` part of the import closure of `Scott.MontalbanQuantifierRank`:
19 modules. -/
def expectedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.Lomega1omega.QuantifierRank,
   `InfinitaryLogic.Lomega1omega.Theory, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Scott.Stabilization, `InfinitaryLogic.Scott.OrbitRank,
   `InfinitaryLogic.Scott.MontalbanSentence, `InfinitaryLogic.Scott.QuantifierRank,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Scott.MontalbanQuantifierRank]

/-- The public declarations added by the tranche. -/
def trancheDecls : List Name :=
  [`qrank_montalbanClauseBody, `qrank_montalbanClauseBody_le, `qrank_montalbanSentencePointed,
   `qrank_montalbanSentencePointed_le, `qrank_montalbanSentencePointed_eq_max,
   `qrank_montalbanSentencePointed_eq_add_omega0, `qrank_montalbanSentence_eq_max,
   `qrank_montalbanSentence, `qrank_montalbanSentence_le,
   `qrank_montalbanSentence_eq_add_omega0, `qrank_montalbanSentence_of_isEmpty].map
    (`FirstOrder.Language ++ ·)

/-- The guard's own theorems whose axioms are audited. -/
def guardDecls : List Name :=
  [`realize_finConj, `qrank_finConj, `realize_eqAtom, `realize_eqPattern, `qrank_eqPattern,
   `qrank_deep, `qrank_deepω, `qrank_pad, `qrank_padΦ, `omega_add_one_add_omega,
   `clauseBody_empty, `clauseBody_le, `attain_nat, `bound_nat, `attain_ulift, `finite_level,
   `finite_level_exact, `pure_homogeneous, `pure_isOrbit, `pure_nat, `empty_carrier,
   `repeated_nat, `repeated_ulift, `seed_dominates, `eq_max_nat, `seed_le_nat].map
    (`MontalbanQRankGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

-- The closure check and the axiom audit run in one command, so that the final OK line is
-- printed only when both pass.
run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.MontalbanQuantifierRank
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let il := cl.toList.filter (`InfinitaryLogic).isPrefixOf
  let extra := il.filter fun m ↦ !expectedClosure.contains m
  let missing := expectedClosure.filter fun m ↦ !cl.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the closure of {target}: unexpected {extra}, missing {missing}"
  unless il.length == 19 do
    throwError "[CLOSURE DRIFT] the closure of {target} has {il.length} modules, not 19"
  for n in trancheDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Montalban quantifier-rank regression guard: OK (applied: the clause body of rank 1 \
    over the empty carrier and the bound alpha + 1 at alpha = omega + 1; attainment of \
    alpha + omega at alpha = omega + 1 on N, rank exactly omega + omega, above alpha and not \
    omega + alpha, with the bound; the same at the Type 1 carrier ULift N; finite levels give \
    omega, unpointed and pointed, exactly omega for a rank-3 family; the equality-pattern \
    Scott sentence of N, holding in Z and failing in Fin 3, of rank exactly omega; the empty \
    carrier, rank 1 and omega + 1 with a padded seed, below omega + 1 + omega; repeated \
    parameters (1, 1) in N with rank omega and (1, 1, 1) in ULift N with rank omega + omega; \
    the general exact value max seed (alpha + omega), with a seed of rank omega + 1 dominating \
    on N, unpointed and pointed over (1, 1), and agreeing with the attainment at the padded \
    family; the seed below the rank through both exact forms; exact import closure of 19 \
    modules; standard axioms)"
