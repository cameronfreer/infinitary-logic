/-
Regression guard for the rank adapters: infinitary orbit formulas
(`InfinitaryLogic/Scott/OrbitFormulaThreshold.lean`) and whole-model recognition from an absolute
Scott sentence (`InfinitaryLogic/Scott/SentenceRecognition.lean`).  The proof-dependency audit is
the separate guard `check_rank_adapters_deps.lean`.

Every exported theorem is *applied*, not only listed for its axioms.

* **Actual infinitary orbit formulas.**  Over the empty language, the equality pattern of a
  tuple is the countable conjunction `patternω` (`einf` over `Fin n × Fin n`, an `iInf` over `ℕ`
  through the encoding; rank `0`), and `towers = ⋁ₖ ∃x₁ … ∃xₖ ⊤` is a countable disjunction
  (`iSup` over `ℕ`) whose rank `⨆ k, k = ω` is computed through the infinitary constructor.
  `orbitω a = patternω a ⊓ towers` is an orbit formula of rank `ω` in every empty-language
  structure: its realizations are exactly the automorphic images of `a` (a finite partial
  bijection extends to a permutation).
* **Orbit adapters** (`orbit_determined_of_infinitaryOrbitFormula`,
  `orbitRank_le_lift_qrank_of_infinitaryOrbitFormula`,
  `internalScottRank_le_of_infinitaryOrbitFormulas`): on the uncountable `Type 1` carrier
  `Ordinal.{0}` with a repeated tuple and the explicit lift `Ordinal.lift.{1, 0}` (rank `ω`
  threshold; orbit rank `0` through `patternω`, as `orbitRank_pureSet` says); internal rank at
  most `Ordinal.lift.{1, 0} (ω + 1)` through the rank-`ω` formulas (the library value is `1`).
* **No uniform finite rank**: the pointwise family `graded a = patternω a ⊓ ∃x₁ … ∃xₙ ⊤` has rank
  exactly `n` on tuples of length `n`; no finite `k` bounds it, and the strict premise at `α = ω`
  still gives internal rank at most `Ordinal.lift.{1, 0} ω`; also for an arbitrary `X : Type 3`
  with no `Countable` or `Nonempty` instance.
* **Arbitrary language universes and a `Type 3` carrier**: over any relational
  `L : Language.{u, v}` and any `M : Type 3` without instances, the empty tuple has the orbit
  formulas `towers` (rank `ω`, explicit `Ordinal.lift.{3, 0}`) and `⊤` (orbit rank `0`).
* **The empty carrier** `PEmpty : Type 3`, any relational language and structure: the nullary
  `⊤` defines the empty-tuple orbit, of orbit rank `0`; the internal rank is at most `1`, and at
  least `1` by the plus-one convention, so `0` would be false.
* **A singleton carrier** `PUnit : Type 1` with the repeated tuple `![x, x]`.
* **Recognition** (`recognition_of_sentence_rank`, `stabilizationOrdinal_le_of_sentence_rank`,
  `stabilizationOrdinal_le_qrank_of_sentence`): the rank-one sentence `∀x ⊥` holds exactly in
  the empty structures and is an absolute Scott specification of every empty structure in a
  language without relation symbols (the actual satisfaction/isomorphism equivalence, for every
  target on the carrier universe).  Applied in the empty language on `Empty`; on the empty
  carrier `PEmpty : Type 3`; in the explicit `Language.{1, 2}` on `Type 3`; and with the
  uncountable comparison ordinal `ω₁`, so no countability premise on `β` can be present.
* **Import closure** of `Scott.SentenceRecognition`: exactly the listed `InfinitaryLogic` modules
  (`[CLOSURE DRIFT]` otherwise), none of `Scott/OrbitRank`, `Scott/OrbitRankStabilization`,
  `Scott/OrbitFormulaThreshold`, `Scott/Height*`, `Scott/Rank` (all present in this
  environment, so the check is not vacuous); `Scott.OrbitFormulaThreshold` reaches
  `Scott/OrbitRank` and not `Scott/Sentence`.

The exported and guard declarations use only the standard axioms.

Run with: lake env lean scripts/check_rank_adapters_regressions.lean
-/
import InfinitaryLogic.Scott.OrbitFormulaThreshold
import InfinitaryLogic.Scott.SentenceRecognition
import InfinitaryLogic.Scott.OrbitRankStabilization
import InfinitaryLogic.Scott.Height
import InfinitaryLogic.Scott.Rank
import Mathlib.SetTheory.Cardinal.Arithmetic

open Lean FirstOrder FirstOrder.Language BoundedFormulaω

universe u v w

noncomputable section

namespace RankAdaptersGuard

attribute [local instance] Language.emptyStructure

/-! ### Infinitary building blocks -/

section Blocks

variable {L : Language.{u, v}} {α : Type*}

/-- `k` nested existential quantifiers over `⊤`. -/
def tower : ℕ → (m : ℕ) → L.BoundedFormulaω α m
  | 0, _ => ⊤
  | k + 1, m => (tower k (m + 1)).ex

/-- `tower k` has quantifier rank exactly `k`. -/
theorem qrank_tower : ∀ k m : ℕ, (tower (L := L) (α := α) k m).qrank = k
  | 0, _ => qrank_top
  | k + 1, m => by rw [tower, qrank_ex, qrank_tower k (m + 1), Nat.cast_succ]

/-- `tower k` holds iff `k = 0` or the carrier is nonempty. -/
theorem realize_tower {M : Type*} [L.Structure M] (v : α → M) :
    ∀ (k m : ℕ) (xs : Fin m → M), (tower (L := L) k m).Realize v xs ↔ (k = 0 ∨ Nonempty M)
  | 0, _, _ => by simp [tower]
  | k + 1, m, xs => by
    simp only [tower, realize_ex, realize_tower v k, Nat.add_one_ne_zero, false_or]
    exact ⟨fun ⟨x, _⟩ ↦ ⟨x⟩, fun ⟨x⟩ ↦ ⟨x, Or.inr ⟨x⟩⟩⟩

/-- **A genuinely infinitary disjunction**: `⋁ₖ tower k`, of rank `ω`, valid in every structure
(the disjunct `k = 0` is `⊤`). -/
def towers : L.Formulaω α := iSup fun k ↦ tower k 0

/-- The rank of `towers` is computed through `iSup`: `⨆ k, k = ω`. -/
theorem qrank_towers : (towers (L := L) (α := α)).qrank = Ordinal.omega0 := by
  simp only [towers, Formulaω.qrank, qrank_iSup, qrank_tower]
  exact Ordinal.iSup_natCast

/-- `towers` holds everywhere. -/
theorem realize_towers {M : Type*} [L.Structure M] (v : α → M) :
    Formulaω.Realize (towers (L := L)) v :=
  (realize_iSup _).2 ⟨0, (realize_tower v 0 0 _).2 (Or.inl rfl)⟩

end Blocks

/-! ### Infinitary orbit formulas on pure sets -/

section Pattern

variable {X : Type w}

open Classical in
/-- One clause of the equality pattern of `a`: `xᵢ = xⱼ` or `xᵢ ≠ xⱼ`. -/
def clause {n : ℕ} (a : Fin n → X) (p : Fin n × Fin n) : Language.empty.Formulaω (Fin n) :=
  if a p.1 = a p.2 then equal (Term.var (Sum.inl p.1)) (Term.var (Sum.inl p.2))
  else (equal (Term.var (Sum.inl p.1)) (Term.var (Sum.inl p.2))).not

/-- **The equality pattern as a countable conjunction**: `einf` over `Fin n × Fin n`, an `iInf`
over `ℕ` through the encoding. -/
def patternω {n : ℕ} (a : Fin n → X) : Language.empty.Formulaω (Fin n) := einf (clause a)

theorem qrank_patternω {n : ℕ} (a : Fin n → X) : (patternω a).qrank = 0 := by
  classical
  refine le_antisymm (?_ : (einf (clause a)).qrank ≤ 0) zero_le
  rw [qrank_einf]
  refine Ordinal.iSup_le fun p ↦ ?_
  unfold clause
  split_ifs <;> simp

theorem realize_patternω {n : ℕ} (a b : Fin n → X) :
    (patternω a).Realize b ↔ ∀ i j, (a i = a j ↔ b i = b j) := by
  classical
  simp only [patternω, Formulaω.realize_einf, Prod.forall]
  refine forall₂_congr fun i j ↦ ?_
  unfold clause
  split_ifs with h <;> simp [Formulaω.realize_def, h]

/-- Tuples with the same equality pattern are carried to each other by a permutation, in any
type: extend the finite partial bijection `a i ↦ b i`. -/
theorem exists_equiv_of_pattern {n : ℕ} {a b : Fin n → X}
    (h : ∀ i j, (a i = a j ↔ b i = b j)) :
    ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  let f : Set.range a → X := fun x ↦ b x.2.choose
  have hf : ∀ i, f ⟨a i, i, rfl⟩ = b i := fun i ↦
    (h _ i).1 (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, a j = a i))
  have hinj : Function.Injective f := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hij
    simp only [hf] at hij
    exact Subtype.ext ((h i j).2 hij)
  obtain ⟨g, hg⟩ : ∃ g : X ≃ X, ∀ x : Set.range a, g x = f x := by
    rcases finite_or_infinite X with hX | hX
    · exact Cardinal.extend_function_finite ⟨f, hinj⟩ ⟨Equiv.refl X⟩
    · exact Cardinal.extend_function_of_lt ⟨f, hinj⟩
        (Cardinal.mk_lt_aleph0.trans_le (Cardinal.aleph0_le_mk X)) ⟨Equiv.refl X⟩
  exact ⟨{ toEquiv := g }, funext fun i ↦ (hg ⟨a i, i, rfl⟩).trans (hf i)⟩

/-- The pattern condition is exactly membership in the automorphism orbit. -/
theorem pattern_iff_orbit {n : ℕ} (a b : Fin n → X) :
    (∀ i j, (a i = a j ↔ b i = b j)) ↔ ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  refine ⟨exists_equiv_of_pattern, ?_⟩
  rintro ⟨e, rfl⟩ i j
  simp [e.injective.eq_iff]

/-- **The countable conjunction `patternω a` is an infinitary orbit formula.** -/
theorem patternω_orbit {n : ℕ} (a b : Fin n → X) :
    (patternω a).Realize b ↔ ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b :=
  (realize_patternω a b).trans (pattern_iff_orbit a b)

/-- **An infinitary orbit formula of rank `ω`**: the countable conjunction of the pattern
together with the countable disjunction `towers`. -/
def orbitω {n : ℕ} (a : Fin n → X) : Language.empty.Formulaω (Fin n) := patternω a ⊓ towers

theorem qrank_orbitω {n : ℕ} (a : Fin n → X) : (orbitω a).qrank = Ordinal.omega0 := by
  show (BoundedFormulaω.and (patternω a) towers).qrank = _
  rw [qrank_and]
  exact (congrArg₂ max (qrank_patternω a) qrank_towers).trans (max_eq_right zero_le)

theorem orbitω_orbit {n : ℕ} (a b : Fin n → X) :
    (orbitω a).Realize b ↔ ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  rw [orbitω, Formulaω.realize_inf, patternω_orbit]
  exact and_iff_left (realize_towers b)

/-- **A pointwise family of finite but unbounded ranks**: the formula of a tuple of length `n`
has rank exactly `n`. -/
def graded {n : ℕ} (a : Fin n → X) : Language.empty.Formulaω (Fin n) := patternω a ⊓ tower n 0

theorem qrank_graded {n : ℕ} (a : Fin n → X) : (graded a).qrank = n := by
  show (BoundedFormulaω.and (patternω a) (tower n 0)).qrank = _
  rw [qrank_and]
  exact (congrArg₂ max (qrank_patternω a) (qrank_tower n 0)).trans (max_eq_right zero_le)

theorem graded_orbit {n : ℕ} (a b : Fin n → X) :
    (graded a).Realize b ↔ ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  rw [graded, Formulaω.realize_inf, patternω_orbit]
  refine and_iff_left ((realize_tower b n 0 Fin.elim0).2 ?_)
  rcases n with _ | n
  · exact Or.inl rfl
  · exact Or.inr ⟨a 0⟩

end Pattern

/-! ### Part A on concrete carriers -/

section OrbitApplications

/-- A tuple of the infinite, uncountable `Type 1` carrier `Ordinal.{0}` with a repeated
coordinate. -/
def ordTuple : Fin 3 → Ordinal.{0} := ![0, 1, 0]

/-- **Explicit lifted threshold** (`orbit_determined_of_infinitaryOrbitFormula`) through the
rank-`ω` infinitary orbit formula `orbitω`: equivalence at `Ordinal.lift.{1, 0} ω` gives an
automorphism. -/
theorem ord_orbit_determined (b : Fin 3 → Ordinal.{0})
    (hb : BFEquiv (L := Language.empty) (Ordinal.lift.{1, 0} Ordinal.omega0) 3 ordTuple b) :
    ∃ e : Ordinal.{0} ≃[Language.empty] Ordinal.{0}, ⇑e ∘ ordTuple = b :=
  orbit_determined_of_infinitaryOrbitFormula (orbitω_orbit ordTuple) b
    (by rwa [qrank_orbitω])

/-- **The orbit-rank bound** (`orbitRank_le_lift_qrank_of_infinitaryOrbitFormula`), with the
explicit lift, through `orbitω` (rank `ω`) and through the countable conjunction `patternω`
(rank `0`); the latter agrees with the library value `orbitRank_pureSet = 0`. -/
theorem ord_orbitRank :
    orbitRank (L := Language.empty) ordTuple ≤ Ordinal.lift.{1, 0} (orbitω ordTuple).qrank ∧
      orbitRank (L := Language.empty) ordTuple ≤ Ordinal.lift.{1, 0} Ordinal.omega0 ∧
      orbitRank (L := Language.empty) ordTuple ≤ Ordinal.lift.{1, 0} (patternω ordTuple).qrank ∧
      orbitRank (L := Language.empty) ordTuple = 0 :=
  ⟨orbitRank_le_lift_qrank_of_infinitaryOrbitFormula (orbitω_orbit ordTuple),
    qrank_orbitω ordTuple ▸
      orbitRank_le_lift_qrank_of_infinitaryOrbitFormula (orbitω_orbit ordTuple),
    orbitRank_le_lift_qrank_of_infinitaryOrbitFormula (patternω_orbit ordTuple),
    orbitRank_pureSet ordTuple⟩

/-- **Internal rank through a rank-`ω` orbit formula**: every tuple has the orbit formula
`orbitω`, of rank `ω < ω + 1`, so the internal Scott rank is at most `Ordinal.lift.{1, 0} (ω + 1)`
(consistent with the library value `internalScottRank_pureSet = 1`). -/
theorem ord_internalScottRank_omega_succ :
    internalScottRank (L := Language.empty) Ordinal.{0} ≤
      Ordinal.lift.{1, 0} (Ordinal.omega0 + 1) ∧
      internalScottRank (L := Language.empty) Ordinal.{0} = 1 :=
  ⟨internalScottRank_le_of_infinitaryOrbitFormulas fun _ a ↦
    ⟨orbitω a, by rw [qrank_orbitω]; exact Order.lt_add_one_iff.2 le_rfl, orbitω_orbit a⟩,
    internalScottRank_pureSet⟩

/-- **No uniform finite rank**: the pointwise family `graded` has a formula of rank `n` for each
tuple of length `n`, so no finite `k` bounds all of them. -/
theorem graded_not_uniform :
    ¬ ∃ k : ℕ, ∀ (n : ℕ) (a : Fin n → Ordinal.{0}), (graded a).qrank < k := by
  rintro ⟨k, hk⟩
  have := hk k fun _ ↦ 0
  rw [qrank_graded] at this
  exact lt_irrefl _ this

/-- **A pointwise family without a uniform finite rank**
(`internalScottRank_le_of_infinitaryOrbitFormulas` with `α = ω`): each rank is finite, hence
`< ω`, and the bound is `Ordinal.lift.{1, 0} ω`. -/
theorem ord_internalScottRank_graded :
    internalScottRank (L := Language.empty) Ordinal.{0} ≤ Ordinal.lift.{1, 0} Ordinal.omega0 :=
  internalScottRank_le_of_infinitaryOrbitFormulas fun n a ↦
    ⟨graded a, by rw [qrank_graded]; exact Ordinal.natCast_lt_omega0 n, graded_orbit a⟩

/-- **A `Type 3` carrier without `Countable` or `Nonempty` instances**: the empty-language
structure on an arbitrary `X : Type 3`, possibly empty or uncountable, has internal Scott rank at
most `Ordinal.lift.{3, 0} ω`, through the pointwise family `graded`. -/
theorem type3_internalScottRank (X : Type 3) :
    internalScottRank (L := Language.empty) X ≤ Ordinal.lift.{3, 0} Ordinal.omega0 :=
  internalScottRank_le_of_infinitaryOrbitFormulas fun n a ↦
    ⟨graded a, by rw [qrank_graded]; exact Ordinal.natCast_lt_omega0 n, graded_orbit a⟩

/-- `towers` is an infinitary orbit formula of the empty tuple in **every** structure. -/
theorem towers_orbit {L : Language.{u, v}} {M : Type w} [L.Structure M] (b : Fin 0 → M) :
    (towers : L.Formulaω (Fin 0)).Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ (Fin.elim0 : Fin 0 → M) = b :=
  iff_of_true (realize_towers (L := L) b) ⟨Language.Equiv.refl L M, funext fun i ↦ i.elim0⟩

/-- `⊤` is an infinitary orbit formula of the empty tuple in every structure. -/
theorem top_orbit {L : Language.{u, v}} {M : Type w} [L.Structure M] (b : Fin 0 → M) :
    (⊤ : L.Formulaω (Fin 0)).Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ (Fin.elim0 : Fin 0 → M) = b :=
  iff_of_true (Formulaω.realize_top.2 trivial) ⟨Language.Equiv.refl L M, funext fun i ↦ i.elim0⟩

/-- **Arbitrary language universes and a `Type 3` carrier with no `Countable` or `Nonempty`
instance**: the empty tuple through the rank-`ω` disjunction `towers` (explicit
`Ordinal.lift.{3, 0}`) and through `⊤` (orbit rank `0`). -/
theorem general_empty_tuple {L : Language.{u, v}} [L.IsRelational] {M : Type 3}
    [L.Structure M] :
    (∀ b : Fin 0 → M,
      BFEquiv (L := L) (Ordinal.lift.{3, 0} Ordinal.omega0) 0 (Fin.elim0 : Fin 0 → M) b →
      ∃ e : M ≃[L] M, ⇑e ∘ (Fin.elim0 : Fin 0 → M) = b) ∧
      orbitRank (L := L) (Fin.elim0 : Fin 0 → M) ≤ Ordinal.lift.{3, 0} Ordinal.omega0 ∧
      orbitRank (L := L) (Fin.elim0 : Fin 0 → M) = 0 := by
  refine ⟨fun b hb ↦ orbit_determined_of_infinitaryOrbitFormula (towers_orbit (L := L))
      b (by rwa [qrank_towers]), ?_, ?_⟩
  · simpa only [qrank_towers] using
      orbitRank_le_lift_qrank_of_infinitaryOrbitFormula (towers_orbit (L := L) (M := M))
  · refine le_antisymm ?_ zero_le
    simpa using orbitRank_le_lift_qrank_of_infinitaryOrbitFormula (top_orbit (L := L) (M := M))

/-- `⊤` is an orbit formula of every tuple of the empty carrier (no tuple of positive length
exists). -/
theorem top_orbit_pempty {L : Language.{u, v}} [L.Structure PEmpty.{4}] {n : ℕ}
    (a b : Fin n → PEmpty.{4}) :
    (⊤ : L.Formulaω (Fin n)).Realize b ↔ ∃ e : PEmpty.{4} ≃[L] PEmpty.{4}, ⇑e ∘ a = b :=
  iff_of_true (Formulaω.realize_top.2 trivial)
    ⟨Language.Equiv.refl L _, funext fun i ↦ (a i).elim⟩

/-- **The empty carrier** `PEmpty : Type 3`, over an arbitrary relational language with arbitrary
universes and an arbitrary structure: the nullary `⊤` defines the empty-tuple orbit, whose orbit
rank is `0`; the internal Scott rank is at most `1` (`α = 1`, strict premise `0 < 1`), and it is
**not** `0`: the plus-one convention gives `orbitRank Fin.elim0 + 1 = 1` as a lower bound. -/
theorem pempty_ranks {L : Language.{u, v}} [L.IsRelational] [L.Structure PEmpty.{4}] :
    orbitRank (L := L) (Fin.elim0 : Fin 0 → PEmpty.{4}) = 0 ∧
      internalScottRank (L := L) PEmpty.{4} ≤ 1 ∧
      1 ≤ internalScottRank (L := L) PEmpty.{4} := by
  have h0 : orbitRank (L := L) (Fin.elim0 : Fin 0 → PEmpty.{4}) = 0 := by
    refine le_antisymm ?_ zero_le
    simpa using orbitRank_le_lift_qrank_of_infinitaryOrbitFormula
      (top_orbit_pempty (L := L) (Fin.elim0 : Fin 0 → PEmpty.{4}))
  refine ⟨h0, ?_, ?_⟩
  · simpa using internalScottRank_le_of_infinitaryOrbitFormulas (L := L) (M := PEmpty.{4})
      (α := 1) fun n a ↦ ⟨⊤, by simp, top_orbit_pempty a⟩
  · simpa [h0] using orbitRank_add_one_le_internalScottRank (L := L)
      (Fin.elim0 : Fin 0 → PEmpty.{4})

/-- The repeated tuple `![x, x]` of the singleton `PUnit : Type 1`. -/
def pairUnit : Fin 2 → PUnit.{2} := ![PUnit.unit, PUnit.unit]

/-- **A singleton carrier with a repeated tuple** `![x, x]`: the lifted threshold through
`orbitω` and orbit rank `0` through `patternω`. -/
theorem punit_repeated (b : Fin 2 → PUnit.{2})
    (hb : BFEquiv (L := Language.empty) (Ordinal.lift.{1, 0} Ordinal.omega0) 2 pairUnit b) :
    (∃ e : PUnit.{2} ≃[Language.empty] PUnit.{2}, ⇑e ∘ pairUnit = b) ∧
      orbitRank (L := Language.empty) pairUnit = 0 := by
  refine ⟨orbit_determined_of_infinitaryOrbitFormula (orbitω_orbit pairUnit) b
    (by rwa [qrank_orbitω]), le_antisymm ?_ zero_le⟩
  simpa [qrank_patternω] using orbitRank_le_lift_qrank_of_infinitaryOrbitFormula
    (patternω_orbit pairUnit)

end OrbitApplications

/-! ### Part B: recognition from an absolute Scott sentence -/

section Recognition

/-- A relational language with no symbols, in the explicit universes `Language.{1, 2}`. -/
def lang12 : Language.{1, 2} := ⟨fun _ ↦ PEmpty, fun _ ↦ PEmpty⟩

instance : lang12.IsRelational := fun _ ↦ (inferInstance : IsEmpty PEmpty)

instance (l : ℕ) : IsEmpty (lang12.Relations l) := (inferInstance : IsEmpty PEmpty)

instance (l : ℕ) : IsEmpty (Language.empty.Relations l) := (inferInstance : IsEmpty Empty)

/-- The unique `lang12`-structure on any carrier. -/
instance lang12Structure (M : Type*) : lang12.Structure M :=
  ⟨fun f ↦ isEmptyElim f, fun r ↦ isEmptyElim r⟩

variable {L : Language.{u, v}}

/-- **The rank-one empty-model sentence** `∀x ⊥`. -/
def emptyModelSentence (L : Language.{u, v}) : L.Sentenceω := (⊥ : L.BoundedFormulaω Empty 1).all

theorem qrank_emptyModelSentence : (emptyModelSentence L).qrank = 1 := by
  simp [emptyModelSentence, Sentenceω.qrank]

/-- `∀x ⊥` holds exactly in the empty structures. -/
theorem realize_emptyModelSentence (N : Type*) [L.Structure N] :
    (emptyModelSentence L).Realize N ↔ IsEmpty N := by
  simp [Sentenceω.realize_def, emptyModelSentence, isEmpty_iff]

/-- Two empty structures in a language without relation symbols are isomorphic. -/
def emptyEquiv [L.IsRelational] [∀ l, IsEmpty (L.Relations l)] (M N : Type*) [IsEmpty M]
    [IsEmpty N] [L.Structure M] [L.Structure N] : M ≃[L] N where
  toEquiv := Equiv.equivOfIsEmpty M N
  map_fun' {_} f := isEmptyElim f
  map_rel' {_} r := isEmptyElim r

/-- **The actual satisfaction/isomorphism equivalence**: in a relational language with no
relation symbols, `∀x ⊥` is an absolute Scott specification of every empty structure, over all
targets on the same carrier universe. -/
theorem emptyModelSentence_spec [L.IsRelational] [∀ l, IsEmpty (L.Relations l)]
    (M : Type w) [IsEmpty M] [L.Structure M] (N : Type w) [L.Structure N] :
    (emptyModelSentence L).Realize N ↔ Nonempty (M ≃[L] N) := by
  rw [realize_emptyModelSentence]
  exact ⟨fun _ ↦ ⟨emptyEquiv M N⟩, fun ⟨e⟩ ↦ ⟨fun y ↦ isEmptyElim (e.symm y)⟩⟩

/-- **Recognition in the empty language** on the carrier `Empty`: `recognition_of_sentence_rank`
at the actual rank `1`, the bound `stabilizationOrdinal_le_of_sentence_rank`, and the
specialization `stabilizationOrdinal_le_qrank_of_sentence`. -/
theorem empty_recognition :
    StabilizesAt (L := Language.empty) Empty (1 : Ordinal.{0}) ∧
      stabilizationOrdinal (L := Language.empty) Empty ≤ 1 ∧
      stabilizationOrdinal (L := Language.empty) Empty ≤
        (emptyModelSentence Language.empty).qrank :=
  ⟨recognition_of_sentence_rank _ (fun N _ _ ↦ emptyModelSentence_spec Empty N)
      qrank_emptyModelSentence.le,
    stabilizationOrdinal_le_of_sentence_rank _ (fun N _ _ ↦ emptyModelSentence_spec Empty N)
      qrank_emptyModelSentence.le,
    stabilizationOrdinal_le_qrank_of_sentence _ (fun N _ _ ↦ emptyModelSentence_spec Empty N)⟩

/-- **The empty carrier at `Type 3`**: the same application on `PEmpty.{4}`, with targets on
`Type 3`; `β : Ordinal.{0}` carries no lift. -/
theorem pempty_recognition :
    StabilizesAt (L := Language.empty) PEmpty.{4} (1 : Ordinal.{0}) ∧
      stabilizationOrdinal (L := Language.empty) PEmpty.{4} ≤ 1 :=
  ⟨recognition_of_sentence_rank _ (fun N _ _ ↦ emptyModelSentence_spec PEmpty.{4} N)
      qrank_emptyModelSentence.le,
    stabilizationOrdinal_le_of_sentence_rank _
      (fun N _ _ ↦ emptyModelSentence_spec PEmpty.{4} N) qrank_emptyModelSentence.le⟩

/-- **Explicit `Language.{1, 2}` and carrier `Type 3`.** -/
theorem lang12_recognition :
    StabilizesAt (L := lang12) PEmpty.{4} (1 : Ordinal.{0}) ∧
      stabilizationOrdinal (L := lang12) PEmpty.{4} ≤ 1 :=
  ⟨recognition_of_sentence_rank (emptyModelSentence lang12)
      (fun N _ _ ↦ emptyModelSentence_spec PEmpty.{4} N) qrank_emptyModelSentence.le,
    stabilizationOrdinal_le_of_sentence_rank (emptyModelSentence lang12)
      (fun N _ _ ↦ emptyModelSentence_spec PEmpty.{4} N) qrank_emptyModelSentence.le⟩

/-- `1 ≤ ω₁`. -/
theorem one_le_omega_one : (1 : Ordinal.{0}) ≤ Ordinal.omega 1 :=
  Order.one_le_iff_pos.2 (Ordinal.omega_pos 1)

/-- **An uncountable comparison ordinal**: `β = ω₁`, which is not below `ω₁`, so no
countability premise on `β` can be present. -/
theorem omega1_recognition :
    StabilizesAt (L := lang12) PEmpty.{4} (Ordinal.omega.{0} 1) ∧
      stabilizationOrdinal (L := lang12) PEmpty.{4} ≤ Ordinal.omega 1 ∧
      ¬ Ordinal.omega.{0} 1 < Ordinal.omega 1 :=
  ⟨recognition_of_sentence_rank (emptyModelSentence lang12)
      (fun N _ _ ↦ emptyModelSentence_spec PEmpty.{4} N)
      (qrank_emptyModelSentence.trans_le one_le_omega_one),
    stabilizationOrdinal_le_of_sentence_rank (emptyModelSentence lang12)
      (fun N _ _ ↦ emptyModelSentence_spec PEmpty.{4} N)
      (qrank_emptyModelSentence.trans_le one_le_omega_one),
    lt_irrefl _⟩

end Recognition

end RankAdaptersGuard

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

/-- The exact `InfinitaryLogic` part of the import closure of `Scott.SentenceRecognition`. -/
def expectedRecognitionClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.Lomega1omega.QuantifierRank,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Scott.SentenceRecognition]

/-- Module-name prefixes the recognition closure may not reach: orbit ranks, orbit-rank
stabilization, the orbit-formula thresholds, complete heights and Scott ranks. -/
def forbiddenRecognitionPrefixes : List Name :=
  [`InfinitaryLogic.Scott.OrbitRank, `InfinitaryLogic.Scott.OrbitRankStabilization,
   `InfinitaryLogic.Scott.OrbitFormulaThreshold, `InfinitaryLogic.Scott.Height,
   `InfinitaryLogic.Scott.Rank]

run_cmd do
  let env ← getEnv
  -- the forbidden modules are in this environment, so the check below is not vacuous
  for m in forbiddenRecognitionPrefixes do
    unless (env.getModuleIdx? m).isSome do
      throwError "[VACUOUS] forbidden module {m} is not in the environment"
  let target := `InfinitaryLogic.Scott.SentenceRecognition
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let hits := cl.toList.filter fun m ↦ forbiddenRecognitionPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let il := cl.toList.filter (`InfinitaryLogic).isPrefixOf
  let extra := il.filter fun m ↦ !expectedRecognitionClosure.contains m
  let missing := expectedRecognitionClosure.filter fun m ↦ !cl.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the closure of {target}: unexpected {extra}, missing {missing}"
  -- part A stays in the orbit-formula threshold module, whose closure reaches the orbit ranks
  let clA := importClosure env `InfinitaryLogic.Scott.OrbitFormulaThreshold
  unless clA.contains `InfinitaryLogic.Scott.OrbitRank do
    throwError "[MISSING ROUTE] Scott.OrbitRank is not in the closure of \
      Scott.OrbitFormulaThreshold"
  if clA.contains `InfinitaryLogic.Scott.Sentence then
    throwError "[BROAD CONE] Scott.OrbitFormulaThreshold reaches Scott.Sentence"

/-- The exported declarations. -/
def exported : List Name :=
  [`orbit_determined_of_infinitaryOrbitFormula,
   `orbitRank_le_lift_qrank_of_infinitaryOrbitFormula,
   `internalScottRank_le_of_infinitaryOrbitFormulas,
   `recognition_of_sentence_rank,
   `stabilizationOrdinal_le_of_sentence_rank,
   `stabilizationOrdinal_le_qrank_of_sentence].map (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`qrank_tower, `realize_tower, `qrank_towers, `realize_towers, `qrank_patternω,
   `realize_patternω, `exists_equiv_of_pattern, `pattern_iff_orbit, `patternω_orbit,
   `qrank_orbitω, `orbitω_orbit, `qrank_graded, `graded_orbit, `ord_orbit_determined,
   `ord_orbitRank, `ord_internalScottRank_omega_succ, `graded_not_uniform,
   `ord_internalScottRank_graded, `type3_internalScottRank, `towers_orbit, `top_orbit,
   `general_empty_tuple, `top_orbit_pempty, `pempty_ranks, `punit_repeated,
   `qrank_emptyModelSentence, `realize_emptyModelSentence, `emptyModelSentence_spec,
   `empty_recognition, `pempty_recognition, `lang12_recognition, `one_le_omega_one,
   `omega1_recognition].map (`RankAdaptersGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in exported ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "rank adapters regression guard: OK (applied: the infinitary orbit formulas patternω \
    (a countable conjunction) and orbitω (with the rank-omega countable disjunction towers) on \
    a repeated tuple of the Type 1 carrier Ordinal.{0} with the explicit lift; internal rank at \
    most lift (omega + 1); the graded family without a uniform finite rank, internal rank at \
    most lift omega, also on an arbitrary Type 3 carrier; the empty tuple over an arbitrary \
    relational language on a Type 3 carrier; the empty carrier, orbit rank 0 and internal rank \
    exactly 1; the singleton with a repeated tuple; recognition from the rank-one empty-model \
    sentence in the empty language, on PEmpty at Type 3, in Language.{1, 2}, and at omega 1; \
    exact import closure of Scott.SentenceRecognition; standard axioms)"
