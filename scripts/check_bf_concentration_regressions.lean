/-
Regression guard for concentration at back-and-forth levels
(`InfinitaryLogic/Descriptive/BFConcentration.lean`).

Every new public declaration is *applied*, not only listed for its axioms.

* **Signature generality (RA-1).**  `CodeBFEquiv.of_iso`, the definition of
  `ConcentratedAtBFLevels`, `ConcentratedAtBFLevels.mono`, `concentratedAtBFLevels_of_countable`,
  the bridge `ConcentratedAtBFLevels.bfScattered`, the Cantor endpoint
  `ConcentratedAtBFLevels.not_hasCantorAntichainOn`, the analytic-sides forms
  `exists_bfLevel_saturated_of_analyticSets` and
  `ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets`, the necessity lemma
  `invariant_of_bfLevel_saturated` and the core
  `ConcentratedAtBFLevels.countable_isoClasses_of_saturatedAt` are applied for an arbitrary
  relational `Language.{u, v}` with no countability instance in scope; the bridge, the Cantor
  endpoint and both analytic-sides forms also in a language with uncountably many unary symbols.
  The three countable-symbol declarations (`ConcentratedAtBFLevels.isThinOn`,
  `exists_bfLevel_saturated`, `ConcentratedAtBFLevels.countable_isoClasses_or`) are applied with
  countably many symbols.  The types of all public declarations of the module are inspected:
  an instance `Countable (Σ l, _)` occurs in exactly those three (`[COUNTABILITY DRIFT]`), and
  every public declaration of the module is classified.
* **No analyticity of the class (RA-2).**  The bridge, the Cantor endpoint and thinness are
  applied with only the concentration hypothesis in scope, and the core with no invariance and
  no analyticity binder.
* **Invariant splits (RA-3).**  In the pure-set language (one code, universes `{1, 2}`) the split
  of all codes is a plumbing check of the relatively Borel forms.  In the language with
  countably many unary symbols, the split `emptyP0` of all codes ("the `0`-th symbol holds
  nowhere") is closed and isomorphism invariant (checked directly); level `0` does not saturate
  it (all codes are `CodeBFEquiv 0`-equivalent, and `codeT ∉ emptyP0 ∋ codeF`), every level
  `β ≥ 1` does (checked directly, through the back step), and the level returned by
  `exists_bfLevel_saturated` is nonzero.  The class of all codes there is not concentrated (it
  carries a Cantor antichain); on the concentrated pair `{codeT, codeF}` the relatively Borel
  counting form is applied to the same split.
* **Non-invariant splits (RA-4).**  `invariant_of_bfLevel_saturated` is applied generically.
  Concretely, the isomorphism class `isoClassC0` of the code `c0` (the `0`-th symbol holds exactly
  at `0`) contains `c1 = relabel (swap 0 1) c0` (the `0`-th symbol holds exactly at `1`); the
  split `splitB = isoClassC0 ∩ {c | the 0-th symbol holds at 0}` is cut out by a clopen set,
  contains `c0` and not `c1`, all members of `isoClassC0` are `CodeBFEquiv α`-equivalent at every
  level, and no level saturates it.  The class `isoClassC0` meets one isomorphism class, so it is
  concentrated (`concentratedAtBFLevels_of_countable`), and so is `splitB` (`.mono`).
* **Standard axioms** for every new public declaration and the concrete regressions.
* **Exact import closure** of `Descriptive.BFConcentration`: the closure of
  `Descriptive.BFScattered` (25 `InfinitaryLogic` modules) plus `Scott.BFEquivRelabel`, the one
  newly required dependency (for `BFEquiv.map_equiv` in `CodeBFEquiv.of_iso`), plus the module
  itself: 27 modules, with no `Karp`, `ModelTheory`, `Methods`, `Admissible`, `Conditional` or
  `ScottProcess` module.  The OK line is printed only after the closure and axiom checks.

Run with: lake env lean scripts/check_bf_concentration_regressions.lean
-/
import InfinitaryLogic.Descriptive.BFConcentration

open Lean FirstOrder FirstOrder.Language MeasureTheory Set

universe u v

noncomputable section

namespace BFConcentrationRegressions

/-! ### RA-1, RA-2: generic applications, no countability, no analyticity of the class -/

/-- `CodeBFEquiv.of_iso` and the definition of concentration, for an arbitrary relational
language with no countability. -/
theorem generic_ofIso_def_regression {L : Language.{u, v}} [L.IsRelational]
    {c d : StructureSpace L} (h : (structureIsoSetoid L).r c d) (α : Ordinal.{0})
    (C : Set (StructureSpace L)) :
    CodeBFEquiv α c d ∧ (ConcentratedAtBFLevels C ↔ ∀ α : Ordinal.{0}, α < Ordinal.omega 1 →
      ∃ k : StructureSpace L,
        (Quotient.mk (structureIsoSetoid L) '' {x | x ∈ C ∧ ¬ CodeBFEquiv α x k}).Countable) :=
  ⟨CodeBFEquiv.of_iso h α, Iff.rfl⟩

/-- **The bridge, the Cantor endpoint and `.mono` with only concentration in scope**: no
countability instance, no analyticity, Borelness or invariance hypothesis on `C`. -/
theorem generic_bridge_regression {L : Language.{u, v}} [L.IsRelational]
    {C C' : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) (h : C' ⊆ C) :
    BFScattered C ∧ ¬ HasCantorAntichainOn (structureIsoSetoid L) C ∧
      ConcentratedAtBFLevels C' :=
  ⟨hC.bfScattered, hC.not_hasCantorAntichainOn, hC.mono h⟩

/-- **Thinness with only concentration in scope**, besides countably many relation symbols. -/
theorem generic_thin_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {C : Set (StructureSpace L)}
    (hC : ConcentratedAtBFLevels C) : IsThinOn (structureIsoSetoid L) C :=
  hC.isThinOn

/-- A set meeting countably many isomorphism classes is concentrated, with no countability of
the relation symbols. -/
theorem generic_ofCountable_regression {L : Language.{u, v}} [L.IsRelational]
    {C : Set (StructureSpace L)} (hC : (Quotient.mk (structureIsoSetoid L) '' C).Countable) :
    ConcentratedAtBFLevels C :=
  concentratedAtBFLevels_of_countable hC

/-- **Saturation with analytic sides, no countability**; the level convention is pinned by type
ascription (`Ordinal.{0}` below `Ordinal.omega 1`, no lift, no offset). -/
theorem generic_saturation_regression {L : Language.{u, v}} [L.IsRelational]
    {B C : Set (StructureSpace L)} (hB : AnalyticSet B) (hCB : AnalyticSet (C \ B))
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
      ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv β x y → (x ∈ B ↔ y ∈ B) :=
  (exists_bfLevel_saturated_of_analyticSets hB hCB hinv :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
      ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv β x y → (x ∈ B ↔ y ∈ B))

/-- **Saturation, relatively Borel form**, with countably many relation symbols. -/
theorem generic_saturation_borel_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {B C : Set (StructureSpace L)} (hC : AnalyticSet C)
    (hB : ∃ D : Set (StructureSpace L), MeasurableSet D ∧ B = C ∩ D)
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
      ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv β x y → (x ∈ B ↔ y ∈ B) :=
  exists_bfLevel_saturated hC hB hinv

/-- **Necessity of invariance**, generically: saturation at one level gives invariance. -/
theorem generic_necessity_regression {L : Language.{u, v}} [L.IsRelational]
    {B C : Set (StructureSpace L)} {α : Ordinal.{0}}
    (hsat : ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv α x y → (x ∈ B ↔ y ∈ B)) (hBC : B ⊆ C) :
    ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B :=
  invariant_of_bfLevel_saturated hsat hBC

/-- **The core with no invariance, no analyticity and no countability binder.** -/
theorem generic_core_regression {L : Language.{u, v}} [L.IsRelational]
    {B C : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) (hBC : B ⊆ C)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hsat : ∀ x ∈ B, ∀ y ∈ C, CodeBFEquiv α x y → y ∈ B) :
    (Quotient.mk (structureIsoSetoid L) '' B).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (C \ B)).Countable :=
  hC.countable_isoClasses_of_saturatedAt hBC hα hsat

/-- **One side countable, analytic sides, no countability.** -/
theorem generic_split_regression {L : Language.{u, v}} [L.IsRelational]
    {B C : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) (hBC : B ⊆ C)
    (hB : AnalyticSet B) (hCB : AnalyticSet (C \ B))
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    (Quotient.mk (structureIsoSetoid L) '' B).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (C \ B)).Countable :=
  hC.countable_isoClasses_or_of_analyticSets hBC hB hCB hinv

/-- **One side countable, relatively Borel form**, with countably many relation symbols. -/
theorem generic_split_borel_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {B C : Set (StructureSpace L)}
    (hC : ConcentratedAtBFLevels C) (hCa : AnalyticSet C)
    (hB : ∃ D : Set (StructureSpace L), MeasurableSet D ∧ B = C ∩ D)
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    (Quotient.mk (structureIsoSetoid L) '' B).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (C \ B)).Countable :=
  hC.countable_isoClasses_or hCa hB hinv

/-- Uncountably many unary relation symbols, one for each point of Cantor space. -/
def bigLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _x : ℕ → Bool // l = 1 }

instance : bigLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- **The bridge, the Cantor endpoint and both analytic-sides forms in a language with
uncountably many symbols**: no `Countable` instance for its symbols exists or is assumed. -/
theorem bigLang_regression {B C : Set (StructureSpace bigLang)} (hC : ConcentratedAtBFLevels C)
    (hBC : B ⊆ C) (hB : AnalyticSet B) (hCB : AnalyticSet (C \ B))
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid bigLang).r x y → y ∈ B) :
    BFScattered C ∧ ¬ HasCantorAntichainOn (structureIsoSetoid bigLang) C ∧
      (∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
        ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv β x y → (x ∈ B ↔ y ∈ B)) ∧
      ((Quotient.mk (structureIsoSetoid bigLang) '' B).Countable ∨
        (Quotient.mk (structureIsoSetoid bigLang) '' (C \ B)).Countable) :=
  ⟨hC.bfScattered, hC.not_hasCantorAntichainOn,
    exists_bfLevel_saturated_of_analyticSets hB hCB hinv,
    hC.countable_isoClasses_or_of_analyticSets hBC hB hCB hinv⟩

/-! ### RA-3: the degenerate pure-set split (plumbing) -/

/-- The pure-set language: no function or relation symbols, in universes `{1, 2}`. -/
def pureLang : Language.{1, 2} where
  Functions _ := PEmpty
  Relations _ := PEmpty

instance : pureLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty PEmpty)

instance : Countable (Σ l, pureLang.Relations l) :=
  inferInstanceAs (Countable (Σ _ : ℕ, PEmpty.{3}))

/-- There is only one code in the pure-set language. -/
instance : Subsingleton (StructureSpace pureLang) :=
  ⟨fun _ _ ↦ funext fun q ↦ PEmpty.elim q.1.2⟩

/-- **Plumbing check of the relatively Borel forms** in the pure-set language: there is one
code, so the only splits are `∅` and `univ`; the split `univ` of `univ` is saturated from some
countable level on, and one of its sides meets countably many classes. -/
theorem pureSet_split_regression :
    (∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
        ∀ x ∈ (univ : Set (StructureSpace pureLang)), ∀ y ∈ (univ : Set (StructureSpace pureLang)),
          CodeBFEquiv β x y → (x ∈ (univ : Set (StructureSpace pureLang)) ↔
            y ∈ (univ : Set (StructureSpace pureLang)))) ∧
      ((Quotient.mk (structureIsoSetoid pureLang) '' univ).Countable ∨
        (Quotient.mk (structureIsoSetoid pureLang) '' (univ \ univ)).Countable) := by
  have hC : AnalyticSet (univ : Set (StructureSpace pureLang)) := isClosed_univ.analyticSet
  have hB : ∃ D : Set (StructureSpace pureLang), MeasurableSet D ∧ univ = univ ∩ D :=
    ⟨univ, MeasurableSet.univ, (inter_univ _).symm⟩
  have hinv : ∀ x ∈ (univ : Set (StructureSpace pureLang)), ∀ y ∈ univ,
      (structureIsoSetoid pureLang).r x y → y ∈ univ := fun _ _ _ hy _ ↦ hy
  exact ⟨exists_bfLevel_saturated hC hB hinv,
    (concentratedAtBFLevels_of_countable (Set.to_countable _)).countable_isoClasses_or hC hB hinv⟩

/-! ### RA-3: a meaningful split, with countably many unary symbols -/

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

/-- The Cantor family: in `cantorCode x` the `k`-th symbol holds everywhere if `x k` and
nowhere otherwise. -/
def cantorCode (x : ℕ → Bool) : StructureSpace unaryLang := fun q ↦ x (symIdx q.1)

theorem continuous_cantorCode : Continuous cantorCode :=
  continuous_pi fun q ↦ continuous_apply (symIdx q.1)

/-- The all-true member of the Cantor family. -/
def codeT : StructureSpace unaryLang := cantorCode fun _ ↦ true

/-- The all-false member of the Cantor family. -/
def codeF : StructureSpace unaryLang := cantorCode fun _ ↦ false

/-- All codes agree at level `0`: an atomic formula over the empty tuple would need a nullary
symbol. -/
theorem codeBFEquiv_zero (c d : StructureSpace unaryLang) : CodeBFEquiv 0 c d :=
  (@BFEquiv.zero unaryLang ℕ c.toStructure ℕ d.toStructure _ _ _).mpr fun idx ↦ by
    cases idx with
    | eq i _ => exact i.elim0
    | rel R f =>
      obtain ⟨_, rfl⟩ := R
      exact (f 0).elim0

/-- Distinct members of the Cantor family are not isomorphic. -/
theorem cantorCode_noniso {x y : ℕ → Bool} (hxy : x ≠ y) :
    ¬ (structureIsoSetoid unaryLang).r (cantorCode x) (cantorCode y) := by
  rintro ⟨e⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
  have := @Language.Equiv.map_rel unaryLang ℕ ℕ (cantorCode x).toStructure
    (cantorCode y).toStructure e 1 (uR k) (fun _ ↦ 0)
  exact hk (Bool.eq_iff_iff.mpr this.symm)

/-- The query "the `0`-th symbol holds at `n`". -/
def p0Query (n : ℕ) : RelQuery unaryLang := ⟨⟨1, uR 0⟩, fun _ ↦ n⟩

/-- The split: codes in which the `0`-th symbol holds nowhere. -/
def emptyP0 : Set (StructureSpace unaryLang) := {c | ∀ n, c (p0Query n) = false}

theorem isClosed_emptyP0 : IsClosed emptyP0 := by
  have : emptyP0 = ⋂ n, {c : StructureSpace unaryLang | c (p0Query n) = true}ᶜ := by
    ext c
    simp [emptyP0]
  rw [this]
  exact isClosed_iInter fun n ↦ (isOpen_relHolds _).isClosed_compl

/-- `emptyP0` is closed under isomorphism, checked directly: an isomorphism `e` carries the
`0`-th symbol at `e⁻¹ n` to the `0`-th symbol at `n`. -/
theorem emptyP0_invariant :
    ∀ x ∈ emptyP0, ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
      (structureIsoSetoid unaryLang).r x y → y ∈ emptyP0 := by
  rintro x hx y - ⟨e⟩ n
  have h := @Language.Equiv.map_rel' _ _ _ x.toStructure y.toStructure e _ (uR 0)
    (fun _ ↦ e.invFun n)
  have h' : (e.toFun ∘ fun _ : Fin 1 ↦ e.invFun n) = fun _ ↦ n :=
    funext fun _ ↦ e.right_inv n
  rw [h'] at h
  change y (p0Query n) = true ↔ x (p0Query (e.invFun n)) = true at h
  rw [hx (e.invFun n)] at h
  simpa using h

/-- `codeF` lies in the split, `codeT` does not. -/
theorem codeF_mem_emptyP0 : codeF ∈ emptyP0 := fun _ ↦ rfl

theorem codeT_not_mem_emptyP0 : codeT ∉ emptyP0 := fun h ↦ absurd (h 0) (by decide)

/-- The one-sided saturation at level `1`, directly through the back step: if `y` has the
`0`-th symbol at `n`, the back step finds `m` with the same atomic type, so `x` has it at
`m`. -/
theorem mem_emptyP0_of_codeBFEquiv_one {x y : StructureSpace unaryLang}
    (h : CodeBFEquiv 1 x y) (hx : x ∈ emptyP0) : y ∈ emptyP0 := by
  intro n
  have h1 : (1 : Ordinal.{0}) = Order.succ 0 := by simp
  rw [CodeBFEquiv, h1] at h
  obtain ⟨m, h0⟩ := @BFEquiv.back unaryLang ℕ x.toStructure ℕ y.toStructure _ _ _ _ h n
  have hat := (@BFEquiv.zero unaryLang ℕ x.toStructure ℕ y.toStructure _ _ _).mp h0
    (AtomicIdx.rel (uR 0) fun _ ↦ Fin.last 0)
  have hm : (Fin.snoc (Fin.elim0 : Fin 0 → ℕ) m ∘ fun _ : Fin 1 ↦ Fin.last 0) = fun _ ↦ m :=
    funext fun _ ↦ Fin.snoc_last (α := fun _ ↦ ℕ) _ _
  have hn : (Fin.snoc (Fin.elim0 : Fin 0 → ℕ) n ∘ fun _ : Fin 1 ↦ Fin.last 0) = fun _ ↦ n :=
    funext fun _ ↦ Fin.snoc_last (α := fun _ ↦ ℕ) _ _
  simp only [AtomicIdx.holds, hm, hn] at hat
  change x (p0Query m) = true ↔ y (p0Query n) = true at hat
  rw [hx m] at hat
  simpa using hat


/-- Saturation of `emptyP0` at every level `β ≥ 1`, directly: monotonicity down to level `1`,
then the back step in both directions. -/
theorem emptyP0_saturated {β : Ordinal.{0}} (hβ : 1 ≤ β) :
    ∀ x ∈ (univ : Set (StructureSpace unaryLang)), ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
      CodeBFEquiv β x y → (x ∈ emptyP0 ↔ y ∈ emptyP0) := fun _ _ _ _ h ↦
  have h1 := CodeBFEquiv.monotone hβ h
  ⟨mem_emptyP0_of_codeBFEquiv_one h1,
    mem_emptyP0_of_codeBFEquiv_one ((codeBFEquivSetoid unaryLang 1).iseqv.symm h1)⟩

/-- **The meaningful invariant split (RA-3)**: `emptyP0` is closed and invariant; all codes are
`CodeBFEquiv 0`-equivalent, so level `0` does not saturate it (`codeT ∉ emptyP0 ∋ codeF`); every
level `β ≥ 1` does; and the level returned by `exists_bfLevel_saturated` (with `C = univ`,
`D = emptyP0`) is nonzero. -/
theorem emptyP0_split_regression :
    IsClosed emptyP0 ∧
      (∀ x ∈ emptyP0, ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
        (structureIsoSetoid unaryLang).r x y → y ∈ emptyP0) ∧
      (∀ c d : StructureSpace unaryLang, CodeBFEquiv 0 c d) ∧
      ¬ (∀ x ∈ (univ : Set (StructureSpace unaryLang)),
        ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
          CodeBFEquiv 0 x y → (x ∈ emptyP0 ↔ y ∈ emptyP0)) ∧
      (∀ β : Ordinal.{0}, 1 ≤ β → ∀ x ∈ (univ : Set (StructureSpace unaryLang)),
        ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
          CodeBFEquiv β x y → (x ∈ emptyP0 ↔ y ∈ emptyP0)) ∧
      ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ 1 ≤ α ∧ ∀ β : Ordinal.{0}, α ≤ β →
        ∀ x ∈ (univ : Set (StructureSpace unaryLang)),
          ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
            CodeBFEquiv β x y → (x ∈ emptyP0 ↔ y ∈ emptyP0) := by
  have hnot0 : ¬ (∀ x ∈ (univ : Set (StructureSpace unaryLang)),
      ∀ y ∈ (univ : Set (StructureSpace unaryLang)),
        CodeBFEquiv 0 x y → (x ∈ emptyP0 ↔ y ∈ emptyP0)) := fun h ↦
    codeT_not_mem_emptyP0 ((h codeT trivial codeF trivial (codeBFEquiv_zero _ _)).mpr
      codeF_mem_emptyP0)
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated (C := univ) isClosed_univ.analyticSet
    ⟨emptyP0, isClosed_emptyP0.measurableSet, (univ_inter _).symm⟩ emptyP0_invariant
  refine ⟨isClosed_emptyP0, emptyP0_invariant, codeBFEquiv_zero, hnot0,
    fun β hβ ↦ emptyP0_saturated hβ, α, hα, Order.one_le_iff_ne_zero.mpr fun h0 ↦ ?_, hsat⟩
  subst h0
  exact hnot0 (hsat 0 le_rfl)

/-- The set of all codes carries a Cantor antichain. -/
theorem hasCantorAntichainOn_univ :
    HasCantorAntichainOn (structureIsoSetoid unaryLang) univ :=
  ⟨cantorCode, continuous_cantorCode, fun _ ↦ trivial, fun _ _ h ↦ cantorCode_noniso h⟩

/-- **The class of all codes in the split above is not concentrated**: it carries a Cantor
antichain, which `ConcentratedAtBFLevels.not_hasCantorAntichainOn` excludes. -/
theorem univ_not_concentrated_regression :
    ¬ ConcentratedAtBFLevels (univ : Set (StructureSpace unaryLang)) := fun hC ↦
  hC.not_hasCantorAntichainOn hasCantorAntichainOn_univ

/-- The pair `{codeT, codeF}`. -/
def pairTF : Set (StructureSpace unaryLang) := {codeT, codeF}

/-- **The relatively Borel counting form on a concentrated class**: the pair `pairTF` is finite,
hence analytic and concentrated (`concentratedAtBFLevels_of_countable`), and the split
`pairTF ∩ emptyP0` is invariant within it.  The conclusion is trivially true here (every
concentrated class exhibited in this guard meets countably many isomorphism classes); this is a
plumbing check. -/
theorem pair_split_regression :
    ConcentratedAtBFLevels pairTF ∧
      ((Quotient.mk (structureIsoSetoid unaryLang) '' (pairTF ∩ emptyP0)).Countable ∨
        (Quotient.mk (structureIsoSetoid unaryLang) ''
          (pairTF \ (pairTF ∩ emptyP0))).Countable) := by
  have hfin : pairTF.Finite := (finite_singleton _).insert _
  have hC := concentratedAtBFLevels_of_countable (hfin.image (Quotient.mk _)).countable
  exact ⟨hC, hC.countable_isoClasses_or hfin.isClosed.analyticSet
    ⟨emptyP0, isClosed_emptyP0.measurableSet, rfl⟩
    fun x hx y hy h ↦ ⟨hy, emptyP0_invariant x hx.2 y trivial h⟩⟩

/-! ### RA-4: a non-invariant split inside one isomorphism class -/

/-- Relabel a code along a permutation `σ` of `ℕ`. -/
def relabel (σ : ℕ ≃ ℕ) (c : StructureSpace unaryLang) : StructureSpace unaryLang :=
  fun q ↦ c ⟨q.1, σ ∘ q.2⟩

/-- `σ` is an isomorphism from the relabelled code to the original. -/
theorem relabel_iso (σ : ℕ ≃ ℕ) (c : StructureSpace unaryLang) :
    (structureIsoSetoid unaryLang).r (relabel σ c) c :=
  ⟨@Language.Equiv.mk unaryLang ℕ ℕ (relabel σ c).toStructure c.toStructure σ
    (fun f _ ↦ isEmptyElim f) (fun _ _ ↦ Iff.rfl)⟩

/-- `c0`: the `0`-th symbol holds exactly at `0`; every other symbol holds nowhere. -/
def c0 : StructureSpace unaryLang := fun q ↦ decide (symIdx q.1 = 0 ∧ ∀ i, q.2 i = 0)

/-- `c1`: `c0` relabelled by the transposition of `0` and `1`, so the `0`-th symbol holds exactly
at `1`. -/
def c1 : StructureSpace unaryLang := relabel (Equiv.swap 0 1) c0

/-- Codes in which the `0`-th symbol holds at `0` (a clopen set). -/
def p0At0 : Set (StructureSpace unaryLang) := {c | c (p0Query 0) = true}

/-- The isomorphism class of `c0`. -/
def isoClassC0 : Set (StructureSpace unaryLang) := {c | (structureIsoSetoid unaryLang).r c0 c}

/-- The non-invariant split of `isoClassC0`. -/
def splitB : Set (StructureSpace unaryLang) := isoClassC0 ∩ p0At0

theorem c0_mem_p0At0 : c0 ∈ p0At0 := by
  simp [p0At0, c0, p0Query, symIdx, uR]

theorem c1_not_mem_p0At0 : c1 ∉ p0At0 := by
  simp [p0At0, c1, relabel, c0, p0Query, symIdx, uR]

theorem c1_mem_isoClassC0 : c1 ∈ isoClassC0 :=
  (structureIsoSetoid unaryLang).iseqv.symm (relabel_iso _ c0)

/-- **No saturating level for a non-invariant split (RA-4(b))**: inside the isomorphism class
`isoClassC0`, the split `splitB` is cut out by the clopen set `p0At0`, contains `c0` but not the
isomorphic `c1`, so it is not invariant within `isoClassC0`; all members of `isoClassC0` are
`CodeBFEquiv α`-equivalent at every level `α`; and by `invariant_of_bfLevel_saturated` no level
saturates `splitB` within `isoClassC0`. -/
theorem nonInvariant_split_regression :
    IsClopen p0At0 ∧ splitB ⊆ isoClassC0 ∧ c0 ∈ splitB ∧ c1 ∈ isoClassC0 \ splitB ∧
      (∀ α : Ordinal.{0}, ∀ x ∈ isoClassC0, ∀ y ∈ isoClassC0, CodeBFEquiv α x y) ∧
      ¬ (∀ x ∈ splitB, ∀ y ∈ isoClassC0, (structureIsoSetoid unaryLang).r x y → y ∈ splitB) ∧
      ∀ α : Ordinal.{0},
        ¬ ∀ x ∈ isoClassC0, ∀ y ∈ isoClassC0, CodeBFEquiv α x y → (x ∈ splitB ↔ y ∈ splitB) := by
  have hc0 : c0 ∈ isoClassC0 := (structureIsoSetoid unaryLang).iseqv.refl c0
  have hnoninv : ¬ (∀ x ∈ splitB, ∀ y ∈ isoClassC0,
      (structureIsoSetoid unaryLang).r x y → y ∈ splitB) := fun h ↦
    c1_not_mem_p0At0 (h c0 ⟨hc0, c0_mem_p0At0⟩ c1 c1_mem_isoClassC0 c1_mem_isoClassC0).2
  refine ⟨isClopen_relHolds _, inter_subset_left, ⟨hc0, c0_mem_p0At0⟩,
    ⟨c1_mem_isoClassC0, fun h ↦ c1_not_mem_p0At0 h.2⟩, fun α x hx y hy ↦ ?_, hnoninv,
    fun α hsat ↦ hnoninv (invariant_of_bfLevel_saturated hsat inter_subset_left)⟩
  exact CodeBFEquiv.of_iso
    ((structureIsoSetoid unaryLang).iseqv.trans ((structureIsoSetoid unaryLang).iseqv.symm hx) hy) α

/-- **`concentratedAtBFLevels_of_countable` and `.mono` on one isomorphism class**: `isoClassC0`
meets a single isomorphism class, so it is concentrated, and so is its subset `splitB`. -/
theorem isoClass_concentrated_regression :
    (Quotient.mk (structureIsoSetoid unaryLang) '' isoClassC0).Countable ∧
      ConcentratedAtBFLevels isoClassC0 ∧ ConcentratedAtBFLevels splitB := by
  have hcount : (Quotient.mk (structureIsoSetoid unaryLang) '' isoClassC0).Countable := by
    refine (countable_singleton (Quotient.mk (structureIsoSetoid unaryLang) c0)).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Quotient.sound ((structureIsoSetoid unaryLang).iseqv.symm hx)
  have hC := concentratedAtBFLevels_of_countable hcount
  exact ⟨hcount, hC, hC.mono inter_subset_left⟩

end BFConcentrationRegressions

end

/-! ### Countability placement -/

open BFConcentrationRegressions

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- The public declarations of the module whose types must not assume countably many relation
symbols. -/
def countabilityFree : List Name :=
  fol [`CodeBFEquiv.of_iso, `ConcentratedAtBFLevels, `ConcentratedAtBFLevels.mono,
    `concentratedAtBFLevels_of_countable, `ConcentratedAtBFLevels.bfScattered,
    `ConcentratedAtBFLevels.not_hasCantorAntichainOn, `exists_bfLevel_saturated_of_analyticSets,
    `invariant_of_bfLevel_saturated, `ConcentratedAtBFLevels.countable_isoClasses_of_saturatedAt,
    `ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets]

/-- The public declarations of the module whose types assume countably many relation symbols:
exactly these three. -/
def countabilityUsing : List Name :=
  fol [`ConcentratedAtBFLevels.isThinOn, `exists_bfLevel_saturated,
    `ConcentratedAtBFLevels.countable_isoClasses_or]

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Descriptive.BFConcentration

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
  -- every public declaration of the module is classified, so "exactly three" is exhaustive
  let some idx := env.getModuleIdx? targetModule | throwError "module {targetModule} not found"
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail && !(n.getString!.endsWith "congr_simp")
  let classified := countabilityFree ++ countabilityUsing
  let unclassified := pub.filter fun n ↦ !classified.contains n
  let absent := classified.filter fun n ↦ !pub.contains n
  unless unclassified.isEmpty && absent.isEmpty do
    throwError "[COUNTABILITY DRIFT] the public declarations of {targetModule} changed \
      (unclassified {unclassified}, not declared there {absent}); classify them"

/-! ### Axiom hygiene -/

/-- The declarations whose axioms are audited: every new public declaration and the concrete
regressions. -/
def headline : List Name :=
  countabilityFree ++ countabilityUsing ++
    [`BFConcentrationRegressions.generic_ofIso_def_regression,
     `BFConcentrationRegressions.generic_ofCountable_regression,
     `BFConcentrationRegressions.generic_saturation_regression,
     `BFConcentrationRegressions.generic_saturation_borel_regression,
     `BFConcentrationRegressions.generic_necessity_regression,
     `BFConcentrationRegressions.generic_core_regression,
     `BFConcentrationRegressions.generic_bridge_regression,
     `BFConcentrationRegressions.generic_thin_regression,
     `BFConcentrationRegressions.generic_split_regression,
     `BFConcentrationRegressions.generic_split_borel_regression,
     `BFConcentrationRegressions.bigLang_regression,
     `BFConcentrationRegressions.pureSet_split_regression,
     `BFConcentrationRegressions.emptyP0_split_regression,
     `BFConcentrationRegressions.univ_not_concentrated_regression,
     `BFConcentrationRegressions.pair_split_regression,
     `BFConcentrationRegressions.nonInvariant_split_regression,
     `BFConcentrationRegressions.isoClass_concentrated_regression]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-! ### Exact import closure -/

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

/-- Module prefixes the closure of `Descriptive.BFConcentration` may not reach. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Karp, `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Methods,
   `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional, `InfinitaryLogic.ScottProcess]

/-- The exact `InfinitaryLogic` import closure of the module: the 25 modules of the closure of
`Descriptive.BFScattered`, plus `Scott.BFEquivRelabel` (the one newly required dependency, for
`BFEquiv.map_equiv` in `CodeBFEquiv.of_iso`), plus the module itself.  Extending it is a
deliberate decision: update this list together with the module docstring. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.Topology.Perfect,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Descriptive.StructureSpace, `InfinitaryLogic.Descriptive.Topology,
   `InfinitaryLogic.Descriptive.Measurable, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.SatisfactionBorel, `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.BFTree,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.AnalyticClosure, `InfinitaryLogic.Descriptive.BFSeparation,
   `InfinitaryLogic.Descriptive.BFScattered,
   `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Descriptive.BFConcentration]

-- the closure and axiom checks, then the OK line
run_cmd do
  let env ← getEnv
  -- closure
  unless (env.getModuleIdx? targetModule).isSome do
    throwError "module {targetModule} is not in the environment"
  let cl := importClosure env targetModule
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {targetModule} reaches {hits}"
  unless ilModules.contains `InfinitaryLogic.Scott.BFEquivRelabel do
    throwError "[CLOSURE DRIFT] the closure of {targetModule} no longer contains \
      Scott.BFEquivRelabel; update allowedClosure and the module docstring"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {targetModule} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  unless ilModules.length == 27 do
    throwError "[CLOSURE DRIFT] expected 27 InfinitaryLogic modules, found {ilModules.length}"
  -- the closure of `Descriptive.BFScattered` is the allowed closure minus the two new modules
  let base := (importClosure env `InfinitaryLogic.Descriptive.BFScattered).toList.filter
    fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let expectedBase := allowedClosure.filter fun m ↦
    m != `InfinitaryLogic.Scott.BFEquivRelabel && m != targetModule
  unless base.length == 25 && expectedBase.all base.contains && base.all expectedBase.contains do
    throwError "[CLOSURE DRIFT] the closure of Descriptive.BFScattered is {base}, not the 25 \
      modules this guard extends"
  -- axioms
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"bf concentration regression guard: OK (applied: CodeBFEquiv.of_iso, the \
    definition, mono, concentratedAtBFLevels_of_countable, the bridge to BFScattered, the Cantor \
    endpoint, both saturation forms, the necessity lemma, the core and both counting forms; the \
    bridge, the Cantor endpoint and the analytic-sides forms for an arbitrary relational \
    Language.\{u, v} with no countability and in a language with uncountably many symbols; \
    the bridge, both endpoints and the core with no analyticity binder; Countable (Σ l, _) in \
    the types of exactly isThinOn, exists_bfLevel_saturated and countable_isoClasses_or, every \
    public declaration classified; the degenerate pure-set split as plumbing; the closed \
    invariant split emptyP0 in countably many unary symbols: level 0 does not saturate, every \
    level ≥ 1 does, the returned level is nonzero, all codes not concentrated; the counting \
    form on a concentrated pair; a clopen non-invariant split inside one isomorphism class with \
    no saturating level, its class concentrated and the split by mono; import closure of \
    {ilModules.length} InfinitaryLogic modules, exactly BFScattered's 25 plus \
    Scott.BFEquivRelabel plus the module, with no Karp, ModelTheory, Methods, Admissible, \
    Conditional or ScottProcess module; standard axioms for {headline.length} declarations)"
