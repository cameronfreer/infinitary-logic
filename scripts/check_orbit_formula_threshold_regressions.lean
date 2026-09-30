/-
Regression guard for first-order orbit formulas and finite back-and-forth thresholds
(`InfinitaryLogic/Scott/OrbitFormulaThreshold.lean`) and the finite-rank lemma
`BoundedFormula.qrank_toLω_lt_omega0` (`InfinitaryLogic/Lomega1omega/QuantifierRank.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **Finite rank** (`BoundedFormula.qrank_toLω_lt_omega0`): for an arbitrary language with
  independent universes and an arbitrary free-variable type, and for a concrete language with
  function symbols of every arity (`∀ x, f x = x`).
* **Orbit formulas in pure sets.**  Over the empty language, the equality-pattern formula of a
  tuple `a` of any type `X` is an orbit formula: its realizations are the tuples with the same
  equality pattern, which are exactly the automorphic images of `a` (a finite partial bijection
  extends to a permutation, `Cardinal.extend_function_finite` / `extend_function_of_lt`).  This
  holds for every `X`: finite, empty, countable or not.
* **Thresholds** (`orbit_determined_of_orbitFormula`, `exists_finite_orbit_threshold`,
  `orbitRank_le_lift_qrank_of_orbitFormula`, `orbitRank_lt_omega0_of_orbitFormula`): on the
  `Type 1` carrier `Ordinal.{0}` (uncountable, so
  no countability enters), with the explicit lift `Ordinal.lift.{1, 0}`, on a repeated tuple and
  on the empty tuple; the empty tuple also with the orbit formula `⊤`, over an arbitrary
  relational language and an arbitrary (possibly empty) carrier.
* **Internal rank** (`internalScottRank_le_omega0_of_orbitFormulas`): every empty-language
  structure has internal Scott rank at most `ω`; instances on `Ordinal.{0}` (consistent with the
  library value `internalScottRank_pureSet = 1`), on the finite `Fin 3`, and on the empty
  carrier `Empty` (no `Nonempty` instance).
* **Why `≤ ω` and not `< ω`.**  The exact-`ω` carrier of `ModelTheory/FiberExactOmega.lean`
  (`omega_orbitRank_lt` and `omega_bound_transport` in
  `scripts/check_rank_comparison_regressions.lean`) has every orbit rank finite and internal
  Scott rank exactly `ω`: pointwise finite thresholds need not give a uniform finite bound.  It
  is not claimed to have first-order orbit formulas, so it is not by itself a counterexample to
  a strict bound under the orbit-formula hypothesis.
* **Composition with the Scott process** (no library corollaries): on the infinite pure set
  `Ordinal.{0}`, the orbit-rank bounds from `orbitRank_lt_omega0_of_orbitFormula` are fed to
  `stabilizesAt_of_orbitRank_le` (`[Infinite M]`, length `ω + 2`, `ω + 1 < ω + 2`, explicit
  `Ordinal.lift.{1}`) and to `rank_le_of_orbitRank_le` (with termination).
* **Import closure** of the core module: it reaches the forward Karp lemma
  (`Karp/CarrierTheorem`) and the orbit-rank API (`Scott/OrbitRank`), and neither the Scott
  process, nor Scott sentences, nor descriptive, admissible, method or model-theory modules.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_orbit_formula_threshold_regressions.lean
-/
import InfinitaryLogic.Scott.OrbitFormulaThreshold
import InfinitaryLogic.ScottProcess.RankComparison
import InfinitaryLogic.ModelTheory.FiberExactOmega
import Mathlib.SetTheory.Cardinal.Arithmetic

open Lean FirstOrder FirstOrder.Language InfinitaryLogic InfinitaryLogic.ScottProcess.Semantic

universe u v w w'

noncomputable section

/-! ### Finite rank of the first-order image -/

section FiniteRank

/-- Arbitrary language universes and an arbitrary free-variable type. -/
example {L : Language.{u, v}} {ι : Type w} {k : ℕ} (φ : L.BoundedFormula ι k) :
    φ.toLω.qrank < Ordinal.omega0 :=
  BoundedFormula.qrank_toLω_lt_omega0 φ

/-- A language with one function symbol of every arity and no relation symbols, in independent
universes. -/
def funLang : Language.{u, v} := ⟨fun _ ↦ PUnit.{u + 1}, fun _ ↦ PEmpty.{v + 1}⟩

/-- `∀ x, f x = x` in `funLang`, with a free-variable type in a third universe. -/
def fixedPointAxiom (ι : Type w) : (funLang.{u, v}).BoundedFormula ι 0 :=
  BoundedFormula.all (Term.bdEqual (Term.func (L := funLang) PUnit.unit ![&0]) &0)

/-- **Function symbols are allowed**: `∀ x, f x = x` has finite rank. -/
theorem fixedPointAxiom_qrank_lt (ι : Type w) :
    (fixedPointAxiom.{u, v, w} ι).toLω.qrank < Ordinal.omega0 :=
  BoundedFormula.qrank_toLω_lt_omega0 _

end FiniteRank

/-! ### Orbit formulas in pure sets -/

section Pattern

variable {X : Type w}

/-- The unique empty-language structure on `X`, local to this file. -/
local instance instEmptyStructure : Language.empty.Structure X := Language.emptyStructure

open Classical in
/-- The equality pattern of `a`: `xᵢ = xⱼ` if `a i = a j`, and `xᵢ ≠ xⱼ` otherwise. -/
def patternFormula {n : ℕ} (a : Fin n → X) : Language.empty.Formula (Fin n) :=
  Formula.iInf fun p : Fin n × Fin n ↦
    if a p.1 = a p.2 then (Term.var p.1).equal (Term.var p.2)
    else ((Term.var p.1).equal (Term.var p.2)).not

/-- The pattern formula of `a` holds of `b` iff `b` has the equality pattern of `a`. -/
theorem realize_patternFormula {n : ℕ} (a b : Fin n → X) :
    (patternFormula a).Realize b ↔ ∀ i j, (a i = a j ↔ b i = b j) := by
  classical
  simp only [patternFormula, Formula.realize_iInf, Prod.forall]
  refine forall₂_congr fun i j ↦ ?_
  split_ifs with h <;> simp [h]

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

/-- **The pattern formula is an orbit formula**, in every empty-language structure. -/
theorem patternFormula_orbit {n : ℕ} (a b : Fin n → X) :
    (patternFormula a).Realize b ↔ ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  rw [realize_patternFormula]
  refine ⟨exists_equiv_of_pattern, ?_⟩
  rintro ⟨e, rfl⟩ i j
  simp [e.injective.eq_iff]

/-- Every tuple of every empty-language structure has an orbit formula. -/
theorem pattern_orbitFormulas : ∀ (n : ℕ) (a : Fin n → X), ∃ φ : Language.empty.Formula (Fin n),
    ∀ b : Fin n → X, φ.Realize b ↔ ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b :=
  fun _ a ↦ ⟨patternFormula a, patternFormula_orbit a⟩

/-- **Internal rank at most `ω`** for every empty-language structure, in any universe
(`internalScottRank_le_omega0_of_orbitFormulas`). -/
theorem pattern_internalScottRank_le :
    internalScottRank (L := Language.empty) X ≤ Ordinal.omega0 :=
  internalScottRank_le_omega0_of_orbitFormulas pattern_orbitFormulas

end Pattern

/-! ### Thresholds and internal rank on concrete carriers -/

section Concrete

/-- The empty-language structure on the `Type 1` carrier `Ordinal.{0}`. -/
local instance instOrdStructure : Language.empty.Structure Ordinal.{0} := Language.emptyStructure

/-- A repeated tuple of the uncountable `Type 1` carrier `Ordinal.{0}`. -/
def repeatedTuple : Fin 2 → Ordinal.{0} := ![0, 0]

/-- **Explicit threshold with an explicit lift** (`orbit_determined_of_orbitFormula`): on a
repeated tuple of `Ordinal.{0} : Type 1`, equivalence at `Ordinal.lift.{1, 0}` of the rank of
the pattern formula gives an automorphism. -/
theorem repeated_orbit_determined (b : Fin 2 → Ordinal.{0})
    (hb : BFEquiv (L := Language.empty)
      (Ordinal.lift.{1, 0} (patternFormula repeatedTuple).toLω.qrank) 2 repeatedTuple b) :
    ∃ e : Ordinal.{0} ≃[Language.empty] Ordinal.{0}, ⇑e ∘ repeatedTuple = b :=
  orbit_determined_of_orbitFormula (patternFormula_orbit repeatedTuple) b hb

/-- **Finite threshold** (`exists_finite_orbit_threshold`), **the rank inequality**
(`orbitRank_le_lift_qrank_of_orbitFormula`, explicit `Ordinal.lift.{1, 0}`) and **finite orbit
rank** (`orbitRank_lt_omega0_of_orbitFormula`) on the repeated tuple; the orbit rank agrees with
the library value `orbitRank_pureSet = 0`. -/
theorem repeated_threshold :
    (∃ β : Ordinal.{1}, β < Ordinal.omega0 ∧ ∀ b : Fin 2 → Ordinal.{0},
      BFEquiv (L := Language.empty) β 2 repeatedTuple b →
        ∃ e : Ordinal.{0} ≃[Language.empty] Ordinal.{0}, ⇑e ∘ repeatedTuple = b) ∧
      orbitRank (L := Language.empty) repeatedTuple ≤
        Ordinal.lift.{1, 0} (patternFormula repeatedTuple).toLω.qrank ∧
      orbitRank (L := Language.empty) repeatedTuple < Ordinal.omega0 ∧
      orbitRank (L := Language.empty) repeatedTuple = 0 :=
  ⟨exists_finite_orbit_threshold (patternFormula_orbit repeatedTuple),
    orbitRank_le_lift_qrank_of_orbitFormula (patternFormula_orbit repeatedTuple),
    orbitRank_lt_omega0_of_orbitFormula (patternFormula_orbit repeatedTuple),
    orbitRank_pureSet repeatedTuple⟩

/-- **The empty tuple** of `Ordinal.{0}`, through its pattern formula. -/
theorem empty_tuple_threshold :
    ∃ β : Ordinal.{1}, β < Ordinal.omega0 ∧ ∀ b : Fin 0 → Ordinal.{0},
      BFEquiv (L := Language.empty) β 0 (Fin.elim0 : Fin 0 → Ordinal.{0}) b →
        ∃ e : Ordinal.{0} ≃[Language.empty] Ordinal.{0}, ⇑e ∘ Fin.elim0 = b :=
  exists_finite_orbit_threshold (patternFormula_orbit (Fin.elim0 : Fin 0 → Ordinal.{0}))

/-- `⊤` is an orbit formula for the empty tuple of any structure. -/
theorem top_orbitFormula {L : Language.{u, v}} {M : Type w} [L.Structure M] (b : Fin 0 → M) :
    (⊤ : L.Formula (Fin 0)).Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ (Fin.elim0 : Fin 0 → M) = b :=
  iff_of_true (by simp) ⟨Language.Equiv.refl L M, funext fun i ↦ i.elim0⟩

/-- **The empty tuple, with the orbit formula `⊤`**, over an arbitrary relational language and
an arbitrary carrier (possibly empty; no `Nonempty` and no countability), at the explicit lifted
rank. -/
theorem top_orbit_determined {L : Language.{u, v}} [L.IsRelational] {M : Type w}
    [L.Structure M] (b : Fin 0 → M)
    (hb : BFEquiv (L := L) (Ordinal.lift.{w, 0} (⊤ : L.Formula (Fin 0)).toLω.qrank) 0
      (Fin.elim0 : Fin 0 → M) b) :
    ∃ e : M ≃[L] M, ⇑e ∘ (Fin.elim0 : Fin 0 → M) = b :=
  orbit_determined_of_orbitFormula top_orbitFormula b hb

/-- **The infinite pure set on a `Type 1` carrier**: the bound `≤ ω` from orbit formulas is
consistent with the library value `internalScottRank_pureSet = 1`. -/
theorem ord_internalScottRank :
    internalScottRank (L := Language.empty) Ordinal.{0} ≤ Ordinal.omega0 ∧
      internalScottRank (L := Language.empty) Ordinal.{0} = 1 :=
  ⟨pattern_internalScottRank_le, internalScottRank_pureSet⟩

/-- The empty-language structure on `Fin 3`. -/
local instance instFin3Structure : Language.empty.Structure (Fin 3) := Language.emptyStructure

/-- **A finite structure**: `Fin 3` over the empty language. -/
theorem fin3_internalScottRank :
    internalScottRank (L := Language.empty) (Fin 3) ≤ Ordinal.omega0 :=
  pattern_internalScottRank_le

/-- The empty-language structure on `Empty`. -/
local instance instEmptyCarrierStructure : Language.empty.Structure Empty :=
  Language.emptyStructure

/-- **The empty carrier**: no `Nonempty` instance is needed. -/
theorem empty_internalScottRank :
    internalScottRank (L := Language.empty) Empty ≤ Ordinal.omega0 :=
  pattern_internalScottRank_le

end Concrete

/-! ### Why the bound is `≤ ω`: the exact-`ω` carrier

On the exact-`ω` carrier (`ModelTheory/FiberExactOmega.lean`, and `omega_orbitRank_lt` /
`omega_bound_transport` in `scripts/check_rank_comparison_regressions.lean`), every orbit rank is
finite and the internal Scott rank is exactly `ω`: pointwise finite thresholds need not give a
uniform finite bound.  The carrier is not claimed to have first-order orbit formulas, so this is
not by itself a counterexample to a strict bound under the orbit-formula hypothesis; it records
why the conclusion of `internalScottRank_le_omega0_of_orbitFormulas` is stated as `≤ ω`. -/

section ExactOmega

open FirstOrder.Language.FiberAssembly FirstOrder.Language.FiberAssembly.ExactOmega

/-- Every orbit rank finite, internal Scott rank not below `ω`. -/
theorem exactOmega_not_lt :
    (∀ (n : ℕ) (a : Fin n → Carrier'), orbitRank (L := lang ℕ Language.empty) a < Ordinal.omega0) ∧
      ¬ internalScottRank (L := lang ℕ Language.empty) Carrier' < Ordinal.omega0 := by
  refine ⟨fun n a ↦ Order.add_one_le_iff.1
    (internalScottRank_exactOmega ▸ orbitRank_add_one_le_internalScottRank a), ?_⟩
  rw [internalScottRank_exactOmega]
  exact lt_irrefl _

end ExactOmega

/-! ### Composition with the Scott process

No corollaries are added to the library: the per-tuple bounds are fed to
`stabilizesAt_of_orbitRank_le` and `rank_le_of_orbitRank_le` of `ScottProcess/RankComparison.lean`
as they stand, keeping `[Infinite M]`, the length `δ`, `ω + 1 < δ`, termination and the explicit
lift. -/

section Process

/-- The empty-language structure on `Ordinal.{0}`. -/
local instance instOrdStructure' : Language.empty.Structure Ordinal.{0} := Language.emptyStructure

/-- `ω + 1 < ω + 2` in `Ordinal.{0}`. -/
theorem omega_add_one_lt' : Ordinal.omega0.{0} + 1 < Ordinal.omega0 + 2 :=
  (add_lt_add_iff_left _).2 one_lt_two

/-- `0 < ω + 2`. -/
theorem omega_add_two_pos' : 0 < Ordinal.omega0.{0} + 2 :=
  Ordinal.omega0_pos.trans_le le_self_add

/-- Orbit formulas bound every orbit rank of the `Type 1` pure set by `Ordinal.lift.{1} ω`. -/
theorem ord_orbitRank_le_lift (n : ℕ) (a : Fin n → Ordinal.{0}) :
    orbitRank (L := Language.empty) a ≤ Ordinal.lift.{1, 0} Ordinal.omega0.{0} := by
  rw [Ordinal.lift_omega0]
  exact (orbitRank_lt_omega0_of_orbitFormula (patternFormula_orbit a)).le

/-- **Process composition** on the `Type 1` pure set, with process length `ω + 2`:
`stabilizesAt_of_orbitRank_le` gives stabilization at `ω`, hence termination, and
`rank_le_of_orbitRank_le` gives rank at most `ω`. -/
theorem ord_process :
    ∃ h : (scottProcessOf Language.empty Ordinal.{0} _ omega_add_two_pos').StabilizesAt
        Ordinal.omega0,
      (scottProcessOf Language.empty Ordinal.{0} _ omega_add_two_pos').rank ⟨_, h⟩ ≤
        Ordinal.omega0 :=
  let h := stabilizesAt_of_orbitRank_le omega_add_one_lt' ord_orbitRank_le_lift
  ⟨h, rank_le_of_orbitRank_le _ ord_orbitRank_le_lift⟩

end Process

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

/-- Module-name prefixes no module of the core closure may have. -/
def forbiddenCorePrefixes : List Name :=
  [`InfinitaryLogic.ScottProcess, `InfinitaryLogic.Scott.Sentence, `InfinitaryLogic.Scott.Rank,
   `InfinitaryLogic.Scott.Code, `InfinitaryLogic.Descriptive, `InfinitaryLogic.Admissible,
   `InfinitaryLogic.Methods, `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Conditional,
   `InfinitaryLogic.WIP]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.OrbitFormulaThreshold
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Karp.CarrierTheorem, `InfinitaryLogic.Scott.OrbitRank,
            `InfinitaryLogic.Lomega1omega.QuantifierRank] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let hits := cl.toList.filter fun m => forbiddenCorePrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-- The core declarations. -/
def coreHeadline : List Name :=
  [`FirstOrder.Language.BoundedFormula.qrank_toLω_lt_omega0] ++
  ([`orbit_determined_of_orbitFormula,
    `exists_finite_orbit_threshold,
    `orbitRank_le_lift_qrank_of_orbitFormula,
    `orbitRank_lt_omega0_of_orbitFormula,
    `internalScottRank_le_omega0_of_orbitFormulas]).map (`FirstOrder.Language ++ ·)

/-- The declarations whose axioms are audited. -/
def headline : List Name :=
  coreHeadline ++
  [`fixedPointAxiom_qrank_lt, `realize_patternFormula, `exists_equiv_of_pattern,
   `patternFormula_orbit, `pattern_orbitFormulas, `pattern_internalScottRank_le,
   `repeated_orbit_determined, `repeated_threshold, `empty_tuple_threshold, `top_orbitFormula,
   `top_orbit_determined, `ord_internalScottRank, `fin3_internalScottRank,
   `empty_internalScottRank, `exactOmega_not_lt, `ord_orbitRank_le_lift, `ord_process]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "orbit-formula threshold regression guard: OK (applied: finite rank of the first-order \
    image for arbitrary universes and with function symbols; pattern formulas are orbit formulas \
    in every empty-language structure; explicit lifted threshold, rank inequality, finite \
    threshold and orbit rank 0 on a repeated tuple of the Type 1 carrier Ordinal.{0}; the empty \
    tuple through its pattern formula and through the orbit formula top over any relational \
    language and carrier; internal rank at most omega on Ordinal.{0} (library value 1), Fin 3 \
    and Empty; the exact-omega carrier: finite orbit ranks without a uniform finite bound; \
    composition with stabilizesAt_of_orbitRank_le and rank_le_of_orbitRank_le on Ordinal.{0}; \
    core import closure without the Scott process, Scott sentences or application modules; \
    standard axioms)"
