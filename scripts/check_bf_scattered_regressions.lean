/-
Regression guard for thinness from countably many back-and-forth classes at every level
(`InfinitaryLogic/Descriptive/BFScattered.lean`, its sentence form
`InfinitaryLogic/Descriptive/BFScatteredSentence.lean`, and the off-diagonal lemma
`MeasureTheory.AnalyticSet.offDiag` in `InfinitaryLogic/Descriptive/AnalyticClosure.lean`).

Every new public declaration is *applied*, not only listed for its axioms.

* **Generic applications.**  `codeBFEquivSetoid`, `codeBFEquivSetoid_r_iff`,
  `not_structureIso_of_mem_offDiag`, the definition of `BFScattered`,
  `exists_forall_not_codeBFEquiv_of_analyticSet` and `not_hasCantorAntichainOn_of_bfScattered`
  for an arbitrary relational `Language.{u, v}` with no countability instance in scope;
  `isThinOn_of_bfScattered` and `Sentenceω.isThinOnNatModels_of_bfScattered` with countably many
  relation symbols; `AnalyticSet.offDiag` in an arbitrary Hausdorff space;
  `bfEquivSetoid_eq_comap` by `rfl`.
* **Signature generality.**  The separation lemma and the Cantor endpoint are also applied to a
  language with uncountably many unary symbols (one for each point of Cantor space), and the
  types of the new declarations are inspected: an instance `Countable (Σ l, L.Relations l)`
  occurs exactly in `isThinOn_of_bfScattered` and `Sentenceω.isThinOnNatModels_of_bfScattered`.
* **Arbitrary class.**  The Cantor endpoint and the thinness theorem take no analyticity, Borel
  or invariance hypothesis on `K`: the generic applications have none in scope.
* **Positive.**  A countable set of codes (for instance a single code) is back-and-forth
  scattered, hence thin and free of Cantor antichains; in the pure-set language (no symbols,
  universes `{1, 2}`) every sentence is thin through the sentence form.
* **Necessity of the hypothesis at a positive level.**  In the language with countably many
  unary relation symbols, all codes agree at level `0` (there is no nullary symbol), so the set
  of all codes has exactly one `CodeBFEquiv 0`-class; but level `1` separates the codes of a
  continuous Cantor family (a unary symbol holds everywhere in one and nowhere in the other), so
  the level-`1` quotient is uncountable.  Directly from that, and not through the theorems under
  test, the set of all codes is not `BFScattered`; and it carries a Cantor antichain, so it is
  not thin.  Countably many classes at level `0` alone does not give thinness.
* **Level convention.**  The statement shape of `exists_forall_not_codeBFEquiv_of_analyticSet`
  is pinned by type ascription: an `Ordinal.{0}` below `Ordinal.omega 1`, used as
  `CodeBFEquiv η` with no lift and no offset.  On the Cantor family above, the returned level is
  nonzero (level `0` separates nothing) and level `1` separates; this is consistent with the
  convention but does not by itself pin it, since any level at least `1` also separates.
* **Standard axioms** for the new declarations and the concrete regressions.
* **Exact import closure** of `Descriptive.BFScattered`: the closure of `Descriptive.BFSeparation`
  plus the module itself.  It needs no `Scott.BFEquivRelabel`, and it contains no `Karp`,
  `ModelTheory`, `Methods`, `Admissible`, `Conditional` or `ScottProcess` module; the sentence
  form, which needs `ModelTheory.MorleyCounting` for `bfEquivSetoid`, lives in
  `Descriptive.BFScatteredSentence` outside that closure.

Run with: lake env lean scripts/check_bf_scattered_regressions.lean
-/
import InfinitaryLogic.Descriptive.BFScatteredSentence

open Lean FirstOrder FirstOrder.Language MeasureTheory Set Cardinal

universe u v

noncomputable section

namespace BFScatteredRegressions

/-! ### Generic applications -/

/-- The setoid, its membership lemma, and the definition of `BFScattered`, for an arbitrary
relational language with no countability. -/
theorem generic_setoid_regression {L : Language.{u, v}} [L.IsRelational] (η : Ordinal.{0})
    (c d : StructureSpace L) :
    ((codeBFEquivSetoid L η).r c d ↔ CodeBFEquiv η c d) ∧
      (BFScattered (L := L) ∅ ↔ ∀ α : Ordinal.{0}, α < Ordinal.omega 1 →
        Countable (Quotient ((codeBFEquivSetoid L α).comap
          (Subtype.val : (∅ : Set (StructureSpace L)) → StructureSpace L)))) :=
  ⟨codeBFEquivSetoid_r_iff, Iff.rfl⟩

/-- The off-diagonal of a pairwise non-isomorphic set, with no countability. -/
theorem generic_offDiag_regression {L : Language.{u, v}} [L.IsRelational]
    {P : Set (StructureSpace L)}
    (hP : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∀ p ∈ P.offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 :=
  not_structureIso_of_mem_offDiag hP

/-- The off-diagonal of an analytic set in an arbitrary Hausdorff space is analytic, and so is
that of a closed set in a Polish space. -/
theorem generic_analyticSet_offDiag_regression {X : Type*} [TopologicalSpace X] [T2Space X]
    {P : Set X} (hP : AnalyticSet P) {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    {Q : Set Y} (hQ : IsClosed Q) : AnalyticSet P.offDiag ∧ AnalyticSet Q.offDiag :=
  ⟨hP.offDiag, hQ.analyticSet.offDiag⟩

/-- **Level convention pinned by type ascription**, with no countability: `Ordinal.{0}`, below
`Ordinal.omega 1`, used as `CodeBFEquiv η` with no lift and no offset. -/
theorem generic_level_regression {L : Language.{u, v}} [L.IsRelational]
    {P : Set (StructureSpace L)} (hP : AnalyticSet P)
    (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y :=
  (exists_forall_not_codeBFEquiv_of_analyticSet hP hanti :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧ ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y)

/-- **Arbitrary class, no countability**: no Cantor antichain on any back-and-forth scattered
`K`, with no countability instance and no definability hypothesis on `K` in scope. -/
theorem generic_cantor_regression {L : Language.{u, v}} [L.IsRelational]
    {K : Set (StructureSpace L)} (hK : BFScattered K) :
    ¬ HasCantorAntichainOn (structureIsoSetoid L) K :=
  not_hasCantorAntichainOn_of_bfScattered hK

/-- **Arbitrary class**: thinness for any back-and-forth scattered `K`, with countably many
relation symbols and no definability hypothesis on `K` in scope. -/
theorem generic_thin_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)} (hK : BFScattered K) :
    IsThinOn (structureIsoSetoid L) K :=
  isThinOn_of_bfScattered hK

/-- Uncountably many unary relation symbols, one for each point of Cantor space. -/
def bigLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _x : ℕ → Bool // l = 1 }

instance : bigLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- **The separation lemma and the Cantor endpoint in a language with uncountably many
symbols**: no `Countable` instance for its symbols exists or is assumed. -/
theorem bigLang_regression {P K : Set (StructureSpace bigLang)} (hP : AnalyticSet P)
    (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid bigLang).r x y → x = y)
    (hK : BFScattered K) :
    (∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y) ∧
      ¬ HasCantorAntichainOn (structureIsoSetoid bigLang) K :=
  ⟨exists_forall_not_codeBFEquiv_of_analyticSet hP hanti,
    not_hasCantorAntichainOn_of_bfScattered hK⟩

/-- The sentence form, and the sentence setoid as a restriction. -/
theorem generic_sentence_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {φ : L.Sentenceω}
    (h : ∀ η : Ordinal.{0}, η < Ordinal.omega 1 → Countable (Quotient (bfEquivSetoid φ η))) :
    φ.IsThinOnNatModels ∧ ∀ η : Ordinal.{0},
      bfEquivSetoid φ η = (codeBFEquivSetoid L η).comap (Subtype.val : ModelsOf φ → _) :=
  ⟨Sentenceω.isThinOnNatModels_of_bfScattered h, bfEquivSetoid_eq_comap φ⟩

/-! ### Positive: countable sets, and the pure-set language -/

/-- A countable set of codes is back-and-forth scattered: the quotient of a countable type is
countable. -/
theorem bfScattered_of_countable {L : Language.{u, v}} [L.IsRelational]
    {K : Set (StructureSpace L)} (hK : K.Countable) : BFScattered K := fun _ _ ↦
  have := hK.to_subtype
  inferInstance

/-- **Positive regression**: a single code is back-and-forth scattered, hence thin and free of
Cantor antichains. -/
theorem singleton_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (c : StructureSpace L) :
    IsThinOn (structureIsoSetoid L) {c} ∧ ¬ HasCantorAntichainOn (structureIsoSetoid L) {c} :=
  ⟨isThinOn_of_bfScattered (bfScattered_of_countable (countable_singleton c)),
    not_hasCantorAntichainOn_of_bfScattered (bfScattered_of_countable (countable_singleton c))⟩

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

/-- **Positive regression, sentence form**: every sentence of the pure-set language is thin. -/
theorem pureSet_sentence_regression (φ : pureLang.Sentenceω) : φ.IsThinOnNatModels :=
  Sentenceω.isThinOnNatModels_of_bfScattered fun _ _ ↦ inferInstance

/-! ### Necessity: countably many unary symbols -/

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

/-- All codes agree at level `0`: an atomic formula over the empty tuple would need a nullary
symbol. -/
theorem codeBFEquiv_zero (c d : StructureSpace unaryLang) : CodeBFEquiv 0 c d :=
  (@BFEquiv.zero unaryLang ℕ c.toStructure ℕ d.toStructure _ _ _).mpr fun idx ↦ by
    cases idx with
    | eq i _ => exact i.elim0
    | rel R f =>
      obtain ⟨_, rfl⟩ := R
      exact (f 0).elim0

/-- Level `1` separates distinct members of the Cantor family. -/
theorem not_codeBFEquiv_one {x y : ℕ → Bool} (hxy : x ≠ y) :
    ¬ CodeBFEquiv 1 (cantorCode x) (cantorCode y) := by
  intro h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
  have h1 : (1 : Ordinal.{0}) = Order.succ 0 := by simp
  rw [CodeBFEquiv, h1] at h
  obtain ⟨n', h0⟩ := @BFEquiv.forth unaryLang ℕ (cantorCode x).toStructure ℕ
    (cantorCode y).toStructure _ _ _ _ h 0
  have hat := (@BFEquiv.zero unaryLang ℕ (cantorCode x).toStructure ℕ (cantorCode y).toStructure
    _ _ _).mp h0 (AtomicIdx.rel (uR k) fun _ ↦ 0)
  exact hk (Bool.eq_iff_iff.mpr hat)

/-- Distinct members of the Cantor family are not isomorphic: an isomorphism carries the
`k`-th symbol at `0` to the `k`-th symbol at the image of `0`. -/
theorem cantorCode_noniso {x y : ℕ → Bool} (hxy : x ≠ y) :
    ¬ (structureIsoSetoid unaryLang).r (cantorCode x) (cantorCode y) := by
  rintro ⟨e⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
  have := @Language.Equiv.map_rel unaryLang ℕ ℕ (cantorCode x).toStructure
    (cantorCode y).toStructure e 1 (uR k) (fun _ ↦ 0)
  exact hk (Bool.eq_iff_iff.mpr this.symm)

/-- The set of all codes carries a Cantor antichain. -/
theorem hasCantorAntichainOn_univ :
    HasCantorAntichainOn (structureIsoSetoid unaryLang) univ :=
  ⟨cantorCode, continuous_cantorCode, fun _ ↦ trivial, fun _ _ h ↦ cantorCode_noniso h⟩

/-- Cantor space is uncountable. -/
theorem not_countable_cantor : ¬ Countable (ℕ → Bool) := by
  rw [← Cardinal.mk_le_aleph0_iff, not_le]
  simp [Cardinal.aleph0_lt_continuum]

/-- **Necessity regression**: one level-`0` class, uncountably many level-`1` classes, not
`BFScattered`, not thin. -/
theorem necessity_regression :
    (∀ c d : StructureSpace unaryLang, CodeBFEquiv 0 c d) ∧
      Countable (Quotient ((codeBFEquivSetoid unaryLang 0).comap
        (Subtype.val : ↥(univ : Set (StructureSpace unaryLang)) → _))) ∧
      ¬ Countable (Quotient ((codeBFEquivSetoid unaryLang 1).comap
        (Subtype.val : ↥(univ : Set (StructureSpace unaryLang)) → _))) ∧
      ¬ BFScattered (univ : Set (StructureSpace unaryLang)) ∧
      ¬ IsThinOn (structureIsoSetoid unaryLang) univ := by
  have h1 : ¬ Countable (Quotient ((codeBFEquivSetoid unaryLang 1).comap
      (Subtype.val : ↥(univ : Set (StructureSpace unaryLang)) → _))) := by
    intro _
    refine not_countable_cantor (Function.Injective.countable
      (f := fun x ↦ (⟦⟨cantorCode x, trivial⟩⟧ : Quotient ((codeBFEquivSetoid unaryLang 1).comap
        (Subtype.val : ↥(univ : Set (StructureSpace unaryLang)) → _)))) fun x y hxy ↦ ?_)
    by_contra hne
    exact not_codeBFEquiv_one hne (Quotient.exact hxy)
  -- `¬ BFScattered` directly from level `1`, not through the theorems under test
  have h1ω : (1 : Ordinal.{0}) < Ordinal.omega 1 :=
    Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one
  refine ⟨codeBFEquiv_zero, ?_, h1, fun h ↦ h1 (h 1 h1ω),
    fun h ↦ h.no_cantorAntichain hasCantorAntichainOn_univ⟩
  · have : Subsingleton (Quotient ((codeBFEquivSetoid unaryLang 0).comap
        (Subtype.val : ↥(univ : Set (StructureSpace unaryLang)) → _))) :=
      ⟨fun a b ↦ Quotient.inductionOn₂ a b fun c d ↦ Quotient.sound (codeBFEquiv_zero c d)⟩
    infer_instance

/-- **The returned level on a concrete antichain**: the range of the Cantor family is analytic
and pairwise non-isomorphic; the level returned by `exists_forall_not_codeBFEquiv_of_analyticSet`
is nonzero, since level `0` separates nothing, and level `1` itself separates the range.  This
is consistent with the no-offset convention but does not by itself pin it: the type ascription
in `generic_level_regression` does. -/
theorem level_regression :
    (∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧ 1 ≤ η ∧
      ∀ x ∈ range cantorCode, ∀ y ∈ range cantorCode, x ≠ y → ¬ CodeBFEquiv η x y) ∧
      ∀ x ∈ range cantorCode, ∀ y ∈ range cantorCode, x ≠ y → ¬ CodeBFEquiv 1 x y := by
  have hanti : ∀ x ∈ range cantorCode, ∀ y ∈ range cantorCode,
      (structureIsoSetoid unaryLang).r x y → x = y := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    by_contra hne
    exact cantorCode_noniso (fun hab ↦ hne (congrArg _ hab)) h
  obtain ⟨η, hη, hsep⟩ :=
    exists_forall_not_codeBFEquiv_of_analyticSet
      (isCompact_range continuous_cantorCode).isClosed.analyticSet hanti
  refine ⟨⟨η, hη, Order.one_le_iff_ne_zero.mpr fun h0 ↦ ?_, hsep⟩, ?_⟩
  · subst h0
    have hne : cantorCode (fun _ ↦ true) ≠ cantorCode (fun _ ↦ false) := fun h ↦
      Bool.false_ne_true (congrFun h ⟨⟨1, uR 0⟩, fun _ ↦ 0⟩).symm
    exact hsep _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ hne (codeBFEquiv_zero _ _)
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    exact not_codeBFEquiv_one fun hab ↦ hne (congrArg _ hab)

end BFScatteredRegressions

end

/-! ### Axiom hygiene -/

open BFScatteredRegressions

/-- The declarations whose axioms are audited. -/
def headline : List Name :=
  [`FirstOrder.Language.codeBFEquivSetoid, `FirstOrder.Language.codeBFEquivSetoid_r_iff,
   `FirstOrder.Language.BFScattered, `FirstOrder.Language.not_structureIso_of_mem_offDiag,
   `FirstOrder.Language.exists_forall_not_codeBFEquiv_of_analyticSet,
   `FirstOrder.Language.not_hasCantorAntichainOn_of_bfScattered,
   `FirstOrder.Language.isThinOn_of_bfScattered,
   `FirstOrder.Language.bfEquivSetoid_eq_comap,
   `FirstOrder.Language.Sentenceω.isThinOnNatModels_of_bfScattered,
   `MeasureTheory.AnalyticSet.offDiag,
   `BFScatteredRegressions.singleton_regression,
   `BFScatteredRegressions.generic_cantor_regression,
   `BFScatteredRegressions.bigLang_regression,
   `BFScatteredRegressions.pureSet_sentence_regression,
   `BFScatteredRegressions.necessity_regression, `BFScatteredRegressions.level_regression]

/-- The new declarations whose types must not assume countably many relation symbols. -/
def countabilityFree : List Name :=
  [`FirstOrder.Language.codeBFEquivSetoid, `FirstOrder.Language.codeBFEquivSetoid_r_iff,
   `FirstOrder.Language.BFScattered, `FirstOrder.Language.not_structureIso_of_mem_offDiag,
   `FirstOrder.Language.exists_forall_not_codeBFEquiv_of_analyticSet,
   `FirstOrder.Language.not_hasCantorAntichainOn_of_bfScattered,
   `FirstOrder.Language.bfEquivSetoid_eq_comap, `MeasureTheory.AnalyticSet.offDiag]

/-- The new declarations whose types assume countably many relation symbols. -/
def countabilityUsing : List Name :=
  [`FirstOrder.Language.isThinOn_of_bfScattered,
   `FirstOrder.Language.Sentenceω.isThinOnNatModels_of_bfScattered]

run_cmd do
  let env ← getEnv
  -- an instance `Countable (Σ l, _)`; a countable quotient in a hypothesis does not count
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

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"

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

/-- Module prefixes the closure of `Descriptive.BFScattered` may not reach. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Karp, `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Methods,
   `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional, `InfinitaryLogic.ScottProcess]

/-- The exact `InfinitaryLogic` import closure of the module: the closure of
`Descriptive.BFSeparation` plus the module itself.  Extending it is a deliberate decision:
update this list together with the module docstring.  `Scott.BFEquivRelabel` is not needed.
`Topology.Perfect` is newly required through `PerfectAntichain` (it holds
`Perfect.mk_eq_continuum`). -/
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
   `InfinitaryLogic.Descriptive.BFScattered]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Descriptive.BFScattered
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  if ilModules.contains `InfinitaryLogic.Scott.BFEquivRelabel then
    throwError "[BROAD CONE] the closure of {target} reaches Scott.BFEquivRelabel, which it \
      does not need; adding it requires documenting the new dependency"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  logInfo m!"bf scattered regression guard: OK (applied: the setoid, BFScattered, the \
    off-diagonal lemma, the analytic separation lemma and the Cantor endpoint for an arbitrary \
    relational Language.\{u, v} with no countability; the separation lemma and the Cantor \
    endpoint in a language with uncountably many symbols; Countable (Σ l, _) in the types of \
    exactly isThinOn_of_bfScattered and the sentence form; AnalyticSet.offDiag in an arbitrary \
    Hausdorff space; the separating level pinned as an Ordinal.\{0} below omega 1 with no lift \
    or offset; thinness for an arbitrary BFScattered class; the sentence form; a single code \
    and every pure-set sentence thin; necessity: countably many unary symbols, one level-0 \
    class, uncountably many level-1 classes, hence not BFScattered, and not thin; the returned \
    level on the Cantor family is nonzero and level 1 separates it; standard axioms; import \
    closure of {ilModules.length} InfinitaryLogic modules, exactly as listed, with no Karp, \
    ModelTheory, Methods, Admissible, Conditional or ScottProcess module and no \
    Scott.BFEquivRelabel)"
