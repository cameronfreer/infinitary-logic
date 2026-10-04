/-
Regression guard for counting isomorphism classes through an isolating rank
(`InfinitaryLogic/Descriptive/ScatteredCounting.lean`) and for its one addition to the Scott
layer, `stabilizesAt_of_equiv` (`InfinitaryLogic/Scott/Sentence.lean`).

Every public declaration of the module is *applied*, not only listed for its axioms.

* **Generic applications, no countability.**  The contract `IsIsolatingRank` (its three fields),
  `isolates_of_le`, `lift`, `lift_mk`, `lift_lt_omega1`, `of_le`, `codeStabilizationOrdinal`,
  `codeStabilizationOrdinal_congr`, the code form `exists_isolating_codeLevel` with its
  contrapositive `not_countable_isoClasses_of_forall_unisolated`, and the four counting
  statements `countable_fibers`, `mk_isoClasses_le_aleph_one`, `mk_isoClasses_eq_aleph_one`,
  `countable_isoClasses_iff_bounded` are applied for an arbitrary relational `Language.{u, v}`
  with no countability instance in scope, and the code form and counting statements again in a
  language with uncountably many unary symbols.  `stabilizesAt_of_equiv` is applied for an
  arbitrary `Language.{u, v}` with neither a relational nor a countability instance.
* **The contract is abstract (decision 6).**  For countably many symbols the successor of the
  stabilization ordinal, `Order.succ ∘ codeStabilizationOrdinal`, is an isolating rank (by
  `of_le` from the instance) that differs from `codeStabilizationOrdinal` at every code.  In the
  pure-set language (one code, universes `{1, 2}`) the constant rank `5` is an isolating rank
  built directly from the three fields, with no stabilization ordinal.
* **Countably many classes, uncountably many codes (decision 8).**  In the language with
  countably many unary symbols, the isomorphism class `isoClassE` of the code `codeE` (the
  `0`-th symbol holds exactly at the even numbers) is **not countable as a set of codes**: the
  relabellings of `codeE` along the involutions swapping `2 n` and `2 n + 1` exactly when
  `x n` are pairwise distinct for distinct `x : ℕ → Bool`, and Cantor space is uncountable.  It
  meets one isomorphism class.  The code form `exists_isolating_codeLevel` (from the instance,
  from the shifted rank, and through the family form `exists_isolating_codeLevel_of_family`)
  gives a countable level isolating it, and the contrapositive shows that some countable level
  has no unisolated pair in it.
* **Countable iff bounded, both directions.**  `isoClassE` is back-and-forth scattered (it is
  concentrated, `concentratedAtBFLevels_of_countable`); `countable_isoClasses_iff_bounded` with
  the instance turns its countably many classes into a bound below `ω₁`, and conversely turns
  the explicit bound `Order.succ (codeStabilizationOrdinal codeE)` into countably many classes;
  `mk_isoClasses_le_aleph_one` bounds its classes by `ℵ₁`.  No class with `BFScattered` and
  uncountably many isomorphism classes is exhibited (non-vacuity of the `= ℵ₁` form is not
  shown).
* **Countability placement.**  The types of all public declarations of the module are
  inspected: an instance `Countable (Σ l, _)` occurs in exactly
  `isIsolatingRank_codeStabilizationOrdinal` (the instance) and the family bridge
  `exists_isolating_codeLevel_of_family` (`[COUNTABILITY DRIFT]`), and every public declaration
  of the module is classified; `stabilizesAt_of_equiv` mentions neither `Countable` nor
  `IsRelational`.
* **Exact import closures.**  The `InfinitaryLogic` closure of `Descriptive.ScatteredCounting`
  is exactly `allowedClosure` (35 modules: the 27 of `Descriptive.BFConcentration`, the 13 of
  `Scott.IsolatingLevel`, the 2 of `OrdinalCountability`, overlapping in 8, plus the module),
  and it is checked to be that union; it contains no `ModelTheory`, `Methods`, `Admissible`,
  `Conditional`, `ScottProcess` or `WIP` module and neither `Descriptive.BFScatteredSentence`
  nor `ModelTheory.MorleyCounting` (`[BROAD CONE]`, `[CLOSURE DRIFT]`).  (There is no module
  `Descriptive.MorleyCounting`; the counting theory is `ModelTheory.MorleyCounting`.)  The
  closure of `Scott.Sentence` is pinned exactly (10 modules), so `stabilizesAt_of_equiv` added
  no import.
* **Standard axioms** for every declaration of the module (enumerated from the environment),
  `stabilizesAt_of_equiv`, and every declaration of this guard.  The OK line is printed only
  after the closure and axiom checks.

Run with: lake env lean scripts/check_scattered_counting_regressions.lean
-/
import InfinitaryLogic.Descriptive.ScatteredCounting

open Lean FirstOrder FirstOrder.Language Set

universe u v w

noncomputable section

namespace ScatteredCountingRegressions

/-! ### Generic applications, no countability -/

/-- **The contract API for an arbitrary relational language**, no countability in scope. -/
theorem generic_contract_regression {L : Language.{u, v}} [L.IsRelational]
    {ρ : StructureSpace L → Ordinal.{0}} (hρ : IsIsolatingRank ρ) {c d : StructureSpace L}
    {γ : Ordinal.{0}} (hγ : ρ c ≤ γ) (h : CodeBFEquiv γ c d)
    (hcd : (structureIsoSetoid L).r c d) :
    (structureIsoSetoid L).r c d ∧ ρ c = ρ d ∧ ρ c < Ordinal.omega 1 ∧
      hρ.lift (Quotient.mk _ c) = ρ c ∧ hρ.lift (Quotient.mk _ d) < Ordinal.omega 1 ∧
      (CodeBFEquiv (ρ c) c d → (structureIsoSetoid L).r c d) :=
  ⟨hρ.isolates_of_le hγ h, hρ.iso_invariant hcd, hρ.lt_omega1 c, hρ.lift_mk c,
    hρ.lift_lt_omega1 _, fun h' ↦ hρ.isolates h'⟩

/-- **`of_le` for an arbitrary relational language**, no countability in scope. -/
theorem generic_ofLe_regression {L : Language.{u, v}} [L.IsRelational]
    {ρ ρ' : StructureSpace L → Ordinal.{0}} (hρ : IsIsolatingRank ρ) (hle : ∀ c, ρ c ≤ ρ' c)
    (hinv : ∀ ⦃c d : StructureSpace L⦄, (structureIsoSetoid L).r c d → ρ' c = ρ' d)
    (hlt : ∀ c, ρ' c < Ordinal.omega 1) : IsIsolatingRank ρ' :=
  hρ.of_le hle hinv hlt

/-- **`codeStabilizationOrdinal` and its congruence lemma for an arbitrary relational
language**, no countability in scope. -/
theorem generic_codeStabilization_regression {L : Language.{u, v}} [L.IsRelational]
    {c d : StructureSpace L} (h : (structureIsoSetoid L).r c d) :
    codeStabilizationOrdinal c = codeStabilizationOrdinal d :=
  codeStabilizationOrdinal_congr h

/-- **The code form and its contrapositive for any isolating rank**, no countability in scope;
the set `S` is arbitrary, only its classes are assumed countable. -/
theorem generic_codeLevel_regression {L : Language.{u, v}} [L.IsRelational]
    {ρ : StructureSpace L → Ordinal.{0}} (hρ : IsIsolatingRank ρ) {S : Set (StructureSpace L)} :
    ((Quotient.mk (structureIsoSetoid L) '' S).Countable →
      ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
        ∀ x ∈ S, ∀ y ∈ S, CodeBFEquiv γ x y → (structureIsoSetoid L).r x y) ∧
      ((∀ γ : Ordinal.{0}, γ < Ordinal.omega 1 →
        ∃ x ∈ S, ∃ y ∈ S, CodeBFEquiv γ x y ∧ ¬ (structureIsoSetoid L).r x y) →
        ¬ (Quotient.mk (structureIsoSetoid L) '' S).Countable) :=
  ⟨hρ.exists_isolating_codeLevel, hρ.not_countable_isoClasses_of_forall_unisolated⟩

/-- **The counting statements for any isolating rank and any back-and-forth scattered class**,
no countability, analyticity or invariance in scope. -/
theorem generic_counting_regression {L : Language.{u, v}} [L.IsRelational]
    {ρ : StructureSpace L → Ordinal.{0}} (hρ : IsIsolatingRank ρ) {K : Set (StructureSpace L)}
    (hK : BFScattered K) :
    (∀ α < Ordinal.omega 1,
      Countable {q : ↥(Quotient.mk (structureIsoSetoid L) '' K) // hρ.lift q.1 = α}) ∧
      Cardinal.mk ↥(Quotient.mk (structureIsoSetoid L) '' K) ≤ Cardinal.aleph 1 ∧
      (¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable →
        Cardinal.mk ↥(Quotient.mk (structureIsoSetoid L) '' K) = Cardinal.aleph 1) ∧
      ((Quotient.mk (structureIsoSetoid L) '' K).Countable ↔
        ∃ β < Ordinal.omega 1, ∀ x ∈ K, ρ x < β) :=
  ⟨hρ.countable_fibers hK, hρ.mk_isoClasses_le_aleph_one hK,
    hρ.mk_isoClasses_eq_aleph_one hK, hρ.countable_isoClasses_iff_bounded hK⟩

/-- **`stabilizesAt_of_equiv` for an arbitrary language**, with neither a relational nor a
countability instance, and an arbitrary carrier universe. -/
theorem generic_stabilizesAt_regression {L : Language.{u, v}} {M M' : Type w} [L.Structure M]
    [L.Structure M'] (e : M ≃[L] M') (α : Ordinal) (h : StabilizesAt (L := L) M α) :
    StabilizesAt (L := L) M' α :=
  stabilizesAt_of_equiv e α h

/-- Uncountably many unary relation symbols, one for each point of Cantor space. -/
def bigLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _x : ℕ → Bool // l = 1 }

instance : bigLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- **The code form and the counting statements in a language with uncountably many symbols**:
no `Countable` instance for its symbols exists or is assumed. -/
theorem bigLang_regression {ρ : StructureSpace bigLang → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {K : Set (StructureSpace bigLang)} (hK : BFScattered K)
    (hKc : (Quotient.mk (structureIsoSetoid bigLang) '' K).Countable) :
    (∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ x ∈ K, ∀ y ∈ K, CodeBFEquiv γ x y → (structureIsoSetoid bigLang).r x y) ∧
      Cardinal.mk ↥(Quotient.mk (structureIsoSetoid bigLang) '' K) ≤ Cardinal.aleph 1 ∧
      ∃ β < Ordinal.omega 1, ∀ x ∈ K, ρ x < β :=
  ⟨hρ.exists_isolating_codeLevel hKc, hρ.mk_isoClasses_le_aleph_one hK,
    (hρ.countable_isoClasses_iff_bounded hK).mp hKc⟩

/-! ### The contract is abstract -/

/-- **A second isolating rank, different everywhere from the instance**: for countably many
symbols, `Order.succ ∘ codeStabilizationOrdinal` is an isolating rank (by `of_le`), and it
differs from `codeStabilizationOrdinal` at every code. -/
theorem shifted_rank_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] :
    IsIsolatingRank (fun c : StructureSpace L ↦ Order.succ (codeStabilizationOrdinal c)) ∧
      ∀ c : StructureSpace L,
        Order.succ (codeStabilizationOrdinal c) ≠ codeStabilizationOrdinal c :=
  ⟨isIsolatingRank_codeStabilizationOrdinal.of_le (fun _ ↦ Order.le_succ _)
    (fun _ _ h ↦ by rw [codeStabilizationOrdinal_congr h])
    (fun c ↦ (Cardinal.isSuccLimit_omega 1).succ_lt
      (isIsolatingRank_codeStabilizationOrdinal.lt_omega1 c)),
    fun _ ↦ (Order.lt_succ _).ne'⟩

/-- The pure-set language: no function or relation symbols, in universes `{1, 2}`. -/
def pureLang : Language.{1, 2} where
  Functions _ := PEmpty
  Relations _ := PEmpty

instance : pureLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty PEmpty)

/-- There is only one code in the pure-set language. -/
instance : Subsingleton (StructureSpace pureLang) :=
  ⟨fun _ _ ↦ funext fun q ↦ PEmpty.elim q.1.2⟩

/-- The code of the pure-set language. -/
def pureCode : StructureSpace pureLang := fun _ ↦ false

/-- **A constant isolating rank, built from the three fields**: in the pure-set language the
constant `5` is an isolating rank, with no stabilization ordinal involved. -/
theorem constant_rank_regression :
    IsIsolatingRank (fun _ : StructureSpace pureLang ↦ (5 : Ordinal.{0})) :=
  { iso_invariant := fun _ _ _ ↦ rfl
    lt_omega1 := fun _ ↦ (Ordinal.natCast_lt_omega0 5).trans Ordinal.omega0_lt_omega_one
    isolates := fun c d _ ↦ Subsingleton.elim c d ▸ (structureIsoSetoid pureLang).iseqv.refl c }

/-- The constant rank isolates every set of codes of the pure-set language at one level. -/
theorem constant_rank_codeLevel_regression :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ x ∈ (univ : Set (StructureSpace pureLang)), ∀ y ∈ (univ : Set (StructureSpace pureLang)),
        CodeBFEquiv γ x y → (structureIsoSetoid pureLang).r x y := by
  refine constant_rank_regression.exists_isolating_codeLevel
    ((countable_singleton (Quotient.mk (structureIsoSetoid pureLang) pureCode)).mono ?_)
  rintro _ ⟨x, -, rfl⟩
  exact congrArg _ (Subsingleton.elim x pureCode)

/-! ### Countably many classes, uncountably many codes -/

/-- Countably many unary relation symbols, nothing else. -/
def unaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _k : ℕ // l = 1 }

instance : unaryLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, unaryLang.Relations l) :=
  inferInstanceAs (Countable (Σ l : ℕ, { _k : ℕ // l = 1 }))

/-- The `k`-th unary symbol. -/
def uR (k : ℕ) : unaryLang.Relations 1 := ⟨k, rfl⟩

/-- The index of a symbol. -/
def symIdx (R : Σ l, unaryLang.Relations l) : ℕ := (R.2 : { _k : ℕ // R.1 = 1 }).1

/-- The query "the `0`-th symbol holds at `n`". -/
def p0Query (n : ℕ) : RelQuery unaryLang := ⟨⟨1, uR 0⟩, fun _ ↦ n⟩

/-- Relabel a code along a permutation `σ` of `ℕ`. -/
def relabel (σ : ℕ ≃ ℕ) (c : StructureSpace unaryLang) : StructureSpace unaryLang :=
  fun q ↦ c ⟨q.1, σ ∘ q.2⟩

/-- `σ` is an isomorphism from the relabelled code to the original. -/
theorem relabel_iso (σ : ℕ ≃ ℕ) (c : StructureSpace unaryLang) :
    (structureIsoSetoid unaryLang).r (relabel σ c) c :=
  ⟨@Language.Equiv.mk unaryLang ℕ ℕ (relabel σ c).toStructure c.toStructure σ
    (fun f _ ↦ isEmptyElim f) (fun _ _ ↦ Iff.rfl)⟩

/-- `codeE`: the `0`-th symbol holds exactly at the even numbers; every other symbol holds
nowhere. -/
def codeE : StructureSpace unaryLang := fun q ↦ decide (symIdx q.1 = 0 ∧ ∀ i, q.2 i % 2 = 0)

/-- The isomorphism class of `codeE`. -/
def isoClassE : Set (StructureSpace unaryLang) := {c | (structureIsoSetoid unaryLang).r codeE c}

/-- Swap `2 n` and `2 n + 1` exactly when `x n`. -/
def swapAt (x : ℕ → Bool) (m : ℕ) : ℕ :=
  if x (m / 2) then (if m % 2 = 0 then m + 1 else m - 1) else m

theorem swapAt_div (x : ℕ → Bool) (m : ℕ) : swapAt x m / 2 = m / 2 := by
  unfold swapAt; split_ifs <;> omega

theorem swapAt_involutive (x : ℕ → Bool) : Function.Involutive (swapAt x) := by
  intro m
  change (if x (swapAt x m / 2) then _ else _) = m
  rw [swapAt_div]
  unfold swapAt
  by_cases h : x (m / 2) <;> simp only [h, ite_true, ite_false, Bool.false_eq_true]
  split_ifs <;> omega

theorem swapAt_even (x : ℕ → Bool) (n : ℕ) : swapAt x (2 * n) % 2 = 0 ↔ x n = false := by
  unfold swapAt
  rw [show 2 * n / 2 = n by omega]
  cases x n <;> simp

/-- The relabelling of `codeE` along the involution `swapAt x`. -/
def codeX (x : ℕ → Bool) : StructureSpace unaryLang :=
  relabel (swapAt_involutive x).toPerm codeE

theorem codeX_p0Query (x : ℕ → Bool) (n : ℕ) : codeX x (p0Query (2 * n)) = !x n := by
  have h := swapAt_even x n
  simp only [codeX, relabel, codeE, p0Query, symIdx, uR, Function.comp_apply,
    Function.Involutive.coe_toPerm, true_and, forall_const]
  cases hx : x n <;> simp_all

theorem codeX_injective : Function.Injective codeX := fun x y h ↦ funext fun n ↦ by
  simpa [codeX_p0Query] using congrFun h (p0Query (2 * n))

theorem codeX_mem_isoClassE (x : ℕ → Bool) : codeX x ∈ isoClassE :=
  (structureIsoSetoid unaryLang).iseqv.symm (relabel_iso _ codeE)

/-- **The class is uncountable as a set of codes**: Cantor space injects into it. -/
theorem isoClassE_not_countable : ¬ isoClassE.Countable := fun h ↦
  InfinitaryLogic.not_countable_univ_cantor
    (by simpa [preimage, codeX_mem_isoClassE] using h.preimage codeX_injective)

/-- **The class meets one isomorphism class.** -/
theorem isoClassE_classes_countable :
    (Quotient.mk (structureIsoSetoid unaryLang) '' isoClassE).Countable := by
  refine (countable_singleton (Quotient.mk (structureIsoSetoid unaryLang) codeE)).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact Quotient.sound ((structureIsoSetoid unaryLang).iseqv.symm hx)

/-- **The code form on uncountably many codes meeting countably many classes**: from the
instance, from the shifted rank and through the family form, and its contrapositive. -/
theorem codeLevel_regression :
    ¬ isoClassE.Countable ∧
      (∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧ ∀ x ∈ isoClassE, ∀ y ∈ isoClassE,
        CodeBFEquiv γ x y → (structureIsoSetoid unaryLang).r x y) ∧
      (∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧ ∀ x ∈ isoClassE, ∀ y ∈ isoClassE,
        CodeBFEquiv γ x y → (structureIsoSetoid unaryLang).r x y) ∧
      (∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧ ∀ x ∈ isoClassE, ∀ y ∈ isoClassE,
        CodeBFEquiv γ x y → (structureIsoSetoid unaryLang).r x y) ∧
      ¬ ∀ γ : Ordinal.{0}, γ < Ordinal.omega 1 → ∃ x ∈ isoClassE, ∃ y ∈ isoClassE,
        CodeBFEquiv γ x y ∧ ¬ (structureIsoSetoid unaryLang).r x y :=
  ⟨isoClassE_not_countable,
    isIsolatingRank_codeStabilizationOrdinal.exists_isolating_codeLevel isoClassE_classes_countable,
    (shifted_rank_regression (L := unaryLang)).1.exists_isolating_codeLevel
      isoClassE_classes_countable,
    exists_isolating_codeLevel_of_family isoClassE_classes_countable,
    fun h ↦ isIsolatingRank_codeStabilizationOrdinal.not_countable_isoClasses_of_forall_unisolated h
      isoClassE_classes_countable⟩

/-- **Countable iff bounded, both directions, on `isoClassE`**: it is back-and-forth scattered;
its countably many classes give a bound, and the explicit bound
`Order.succ (codeStabilizationOrdinal codeE)` gives countably many classes back; its classes are
at most `ℵ₁` and every fibre of the rank is countable. -/
theorem iff_bounded_regression :
    BFScattered isoClassE ∧
      (∃ β < Ordinal.omega 1, ∀ x ∈ isoClassE, codeStabilizationOrdinal x < β) ∧
      (Quotient.mk (structureIsoSetoid unaryLang) '' isoClassE).Countable ∧
      Cardinal.mk ↥(Quotient.mk (structureIsoSetoid unaryLang) '' isoClassE) ≤
        Cardinal.aleph 1 ∧
      ∀ α < Ordinal.omega 1, Countable {q : ↥(Quotient.mk (structureIsoSetoid unaryLang) ''
        isoClassE) // isIsolatingRank_codeStabilizationOrdinal.lift q.1 = α} := by
  have hK : BFScattered isoClassE :=
    (concentratedAtBFLevels_of_countable isoClassE_classes_countable).bfScattered
  have hρ := isIsolatingRank_codeStabilizationOrdinal (L := unaryLang)
  have hbound : ∃ β < Ordinal.omega 1, ∀ x ∈ isoClassE, codeStabilizationOrdinal x < β :=
    ⟨Order.succ (codeStabilizationOrdinal codeE),
      (Cardinal.isSuccLimit_omega 1).succ_lt (hρ.lt_omega1 codeE),
      fun x hx ↦ (codeStabilizationOrdinal_congr hx) ▸ Order.lt_succ _⟩
  exact ⟨hK, (hρ.countable_isoClasses_iff_bounded hK).mp isoClassE_classes_countable,
    (hρ.countable_isoClasses_iff_bounded hK).mpr hbound, hρ.mk_isoClasses_le_aleph_one hK,
    hρ.countable_fibers hK⟩

end ScatteredCountingRegressions

end

/-! ### Countability placement -/

open ScatteredCountingRegressions

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- The public declarations of the module whose types must not assume countably many relation
symbols: the contract with its generated declarations, the code form, the counting statements,
`codeStabilizationOrdinal` and its congruence lemma. -/
def countabilityFree : List Name :=
  fol [`IsIsolatingRank, `IsIsolatingRank.mk, `IsIsolatingRank.rec, `IsIsolatingRank.casesOn,
    `IsIsolatingRank.recOn, `IsIsolatingRank.iso_invariant, `IsIsolatingRank.lt_omega1,
    `IsIsolatingRank.isolates, `IsIsolatingRank.isolates_of_le, `IsIsolatingRank.lift,
    `IsIsolatingRank.lift_mk, `IsIsolatingRank.lift_lt_omega1, `IsIsolatingRank.of_le,
    `IsIsolatingRank.exists_isolating_codeLevel,
    `IsIsolatingRank.not_countable_isoClasses_of_forall_unisolated,
    `IsIsolatingRank.countable_fibers, `IsIsolatingRank.mk_isoClasses_le_aleph_one,
    `IsIsolatingRank.mk_isoClasses_eq_aleph_one,
    `IsIsolatingRank.countable_isoClasses_iff_bounded, `codeStabilizationOrdinal,
    `codeStabilizationOrdinal_congr]

/-- The public declarations of the module whose types assume countably many relation symbols:
exactly the instance and the family bridge. -/
def countabilityUsing : List Name :=
  fol [`isIsolatingRank_codeStabilizationOrdinal, `exists_isolating_codeLevel_of_family]

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Descriptive.ScatteredCounting

/-- The Scott-layer addition. -/
def stabEquiv : Name := `FirstOrder.Language.stabilizesAt_of_equiv

run_cmd do
  let env ← getEnv
  -- an instance `Countable (Σ l, _)`; a countable set or quotient in a hypothesis does not count
  let mentionsCountableSigma (n : Name) : Elab.Command.CommandElabM Bool := do
    let some ci := env.find? n | throwError "declaration {n} not found"
    return (ci.type.find? fun e ↦
      e.isAppOfArity ``Countable 1 && e.appArg!.isAppOf ``Sigma).isSome
  for n in countabilityFree do
    if ← mentionsCountableSigma n then
      throwError "[COUNTABILITY DRIFT] the type of {n} assumes countably many symbols"
  for n in countabilityUsing do
    unless ← mentionsCountableSigma n do
      throwError "[COUNTABILITY DRIFT] the type of {n} no longer assumes countably many \
        symbols; update the guard and the module docstring"
  -- every public declaration of the module is classified, so "exactly two" is exhaustive
  let some idx := env.getModuleIdx? targetModule | throwError "module {targetModule} not found"
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail && !(n.getString!.endsWith "congr_simp")
  let classified := countabilityFree ++ countabilityUsing
  let unclassified := pub.filter fun n ↦ !classified.contains n
  let absent := classified.filter fun n ↦ !pub.contains n
  unless unclassified.isEmpty && absent.isEmpty do
    throwError "[COUNTABILITY DRIFT] the public declarations of {targetModule} changed \
      (unclassified {unclassified}, not declared there {absent}); classify them"
  -- the Scott-layer addition assumes neither countability nor a relational language
  let some se := env.find? stabEquiv | throwError "declaration {stabEquiv} not found"
  if (se.type.find? fun e ↦ e.isAppOf ``Countable ||
      e.isAppOf ``FirstOrder.Language.IsRelational).isSome then
    throwError "[COUNTABILITY DRIFT] the type of {stabEquiv} assumes Countable or IsRelational"
  let some sidx := env.getModuleIdxFor? stabEquiv | throwError "no module for {stabEquiv}"
  unless env.header.moduleNames[sidx.toNat]! == `InfinitaryLogic.Scott.Sentence do
    throwError "[PLACEMENT] {stabEquiv} is not declared in Scott.Sentence"

/-! ### Exact import closures and axiom hygiene -/

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

/-- The `InfinitaryLogic` modules of a closure. -/
def ilClosure (env : Environment) (m : Name) : List Name :=
  (importClosure env m).toList.filter fun n ↦ (`InfinitaryLogic).isPrefixOf n

/-- Module prefixes the closure of `Descriptive.ScatteredCounting` may not reach, and two exact
modules: the sentence form of `BFScattered` and the counting theory it brings in. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.ModelTheory, `InfinitaryLogic.Methods, `InfinitaryLogic.Admissible,
   `InfinitaryLogic.Conditional, `InfinitaryLogic.ScottProcess, `InfinitaryLogic.WIP,
   `InfinitaryLogic.Descriptive.BFScatteredSentence, `InfinitaryLogic.ModelTheory.MorleyCounting,
   `InfinitaryLogic.Descriptive.MorleyCounting]

/-- The exact `InfinitaryLogic` import closure of `Descriptive.ScatteredCounting`: the closures
of `Descriptive.BFConcentration` (27), `Scott.IsolatingLevel` (13) and `OrdinalCountability`
(2), overlapping in 8 modules, plus the module itself.  `Karp.PotentialIso` enters through
`Scott.Sentence`, inherently to `Scott.RefinementCount`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.OrdinalCountability,
   `InfinitaryLogic.Topology.Perfect,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Operations, `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics,
   `InfinitaryLogic.Karp.PotentialIso,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Scott.RefinementCount, `InfinitaryLogic.Scott.IsolatingLevel,
   `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Descriptive.StructureSpace, `InfinitaryLogic.Descriptive.Topology,
   `InfinitaryLogic.Descriptive.Measurable, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.SatisfactionBorel, `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.BFTree,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.AnalyticClosure, `InfinitaryLogic.Descriptive.BFSeparation,
   `InfinitaryLogic.Descriptive.BFScattered, `InfinitaryLogic.Descriptive.BFConcentration,
   `InfinitaryLogic.Descriptive.ScatteredCounting]

/-- The exact `InfinitaryLogic` import closure of `Scott.Sentence`, unchanged by
`stabilizesAt_of_equiv`. -/
def sentenceClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.Karp.PotentialIso,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence]

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`generic_contract_regression, `generic_ofLe_regression, `generic_codeStabilization_regression,
   `generic_codeLevel_regression, `generic_counting_regression, `generic_stabilizesAt_regression,
   `bigLang, `bigLang_regression, `shifted_rank_regression, `pureLang, `pureCode,
   `constant_rank_regression,
   `constant_rank_codeLevel_regression, `unaryLang, `relabel, `relabel_iso, `codeE, `isoClassE,
   `swapAt, `swapAt_div, `swapAt_involutive, `swapAt_even, `codeX, `codeX_p0Query,
   `codeX_injective, `codeX_mem_isoClassE, `isoClassE_not_countable,
   `isoClassE_classes_countable, `codeLevel_regression,
   `iff_bounded_regression].map (`ScatteredCountingRegressions ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Exact comparison of a computed closure with a pinned list. -/
def checkExact (what : Name) (actual expected : List Name) : Elab.Command.CommandElabM Unit := do
  let extra := actual.filter fun m ↦ !expected.contains m
  let missing := expected.filter fun m ↦ !actual.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {what} is {actual}; update the \
      pinned list deliberately (extra {extra}, missing {missing})"

-- the closure checks and the axiom audit run in one command, then the OK line
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? targetModule
    | throwError "module {targetModule} is not in the environment"
  -- the module's closure: exact, forbidden-free, and the predicted union
  let ilModules := ilClosure env targetModule
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {targetModule} reaches {hits}"
  checkExact targetModule ilModules allowedClosure
  unless ilModules.length == 35 do
    throwError "[CLOSURE DRIFT] expected 35 InfinitaryLogic modules, found {ilModules.length}"
  let parts := [`InfinitaryLogic.Descriptive.BFConcentration,
    `InfinitaryLogic.Scott.IsolatingLevel, `InfinitaryLogic.OrdinalCountability]
  let sizes := parts.map fun p ↦ (ilClosure env p).length
  unless sizes == [27, 13, 2] do
    throwError "[CLOSURE DRIFT] the closures of {parts} have sizes {sizes}, not [27, 13, 2]"
  let union := (parts.foldl (fun s p ↦ s ++ .ofList (ilClosure env p)) ({} : NameSet)).insert
    targetModule
  checkExact targetModule ilModules union.toList
  -- the Scott-layer closure is unchanged
  checkExact `InfinitaryLogic.Scott.Sentence (ilClosure env `InfinitaryLogic.Scott.Sentence)
    sentenceClosure
  -- axioms: every declaration of the module, the Scott addition and the guard's declarations
  let enumerated := (env.header.moduleData[idx.toNat]!).constNames.toList
  let audited := enumerated ++ [stabEquiv] ++ guardDecls
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"scattered counting regression guard: OK (applied: the contract and its API, the \
    code form and its contrapositive, and the four counting statements for an arbitrary \
    relational Language.\{u, v} with no countability, and in a language with uncountably many \
    symbols; stabilizesAt_of_equiv with no relational or countability instance; the contract \
    is abstract: the shifted rank succ ∘ codeStabilizationOrdinal is isolating and differs \
    everywhere, and a constant rank is isolating in the pure-set language; on the isomorphism \
    class of one code, uncountable as a set of codes but meeting one class, the code form from \
    the instance, the shifted rank and the family bridge, and the contrapositive; countable iff \
    bounded in both directions there, with the le-aleph-one bound and countable fibres; \
    Countable (Σ l, _) in the types of exactly the instance and the family bridge, every public \
    declaration classified; exact import closure ({ilModules.length} modules, the union of \
    BFConcentration, IsolatingLevel and OrdinalCountability plus the module) with no \
    ModelTheory, Methods, Admissible, Conditional, ScottProcess, WIP, BFScatteredSentence or \
    MorleyCounting module; Scott.Sentence closure unchanged \
    ({sentenceClosure.length} modules); standard axioms for {audited.length} declarations)"
