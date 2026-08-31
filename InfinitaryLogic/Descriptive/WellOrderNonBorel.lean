/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.LopezEscobar
import InfinitaryLogic.Descriptive.WellOrderClass
import InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import InfinitaryLogic.Lomega1omega.InfiniteAxiom

/-!
# Non-Borelness of the countable well-order class (issue #33)

The descriptive-set-theoretic payoff of Marker's boundedness theorem: the class **WO** of
countable well-orders is **not Borel** as a subset of the logic space.

```
theorem wellOrderClass_not_measurableSet (lt : L.Relations 2) : ¬ MeasurableSet (wellOrderClass lt)
```

Were it Borel, López–Escobar (#10) would give a sentence `φ` with `ModelsOf φ = WO` — but only
over **coded** structures, whose carrier is `ℕ`.  The bridge from there to arbitrary models is
the fragment-elementary substructure machinery (#13), applied to `φ ⊓ infiniteAxiom` so that
finite models cannot escape:

* `exists_countable_defect_seed` — a structure whose distinguished relation is not a well-order
  carries a **countable nonempty seed** of witnesses (a trichotomy or transitivity failure, or
  the range of an infinite descending sequence) whose presence forces the same failure in every
  subset containing it;
* `isWellOrder_of_realize` — hence every model of `φ ⊓ infiniteAxiom` is well-ordered: seed a
  countable fragment-elementary substructure with the defect, transport it to the carrier `ℕ`,
  and the resulting code would be a member of `ModelsOf φ = WO` that is not a well-order.

Marker's Corollary 4.27 then bounds the order types of all models of `φ ⊓ infiniteAxiom` by a
single countable ordinal, which `exists_code_type_eq` contradicts.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

/-! ## The defect seed -/

section Defect

variable {M : Type} {r : M → M → Prop}

/-- A structure whose relation fails to be a well-order carries a **countable nonempty seed**
of witnesses: every subset containing the seed inherits the failure.  In this Mathlib a
well-order is trichotomy plus well-foundedness (transitivity is derived), so there are exactly
two cases: a two-element trichotomy failure, and the range of an infinite descending sequence. -/
theorem exists_countable_defect_seed (h : ¬ IsWellOrder M r) :
    ∃ X : Set M, X.Countable ∧ X.Nonempty ∧
      ∀ N : Set M, X ⊆ N → ¬ IsWellOrder ↥N fun x y : ↥N => r ↑x ↑y := by
  by_cases htri : Std.Trichotomous r
  · -- the relation must be ill-founded
    have hwf : ¬ IsWellFounded M r := fun hwf => h (@IsWellOrder.mk M r hwf htri)
    have hnwf : ¬ WellFounded r := fun hw => hwf ⟨hw⟩
    rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff] at hnwf
    obtain ⟨f, hf⟩ := hnwf.some
    refine ⟨Set.range f, Set.countable_range f, ⟨f 0, 0, rfl⟩, fun N hXN hwo => ?_⟩
    exact (wellFounded_iff_isEmpty_descending_chain.mp hwo.toIsWellFounded.wf).false
      ⟨fun n => (⟨f n, hXN ⟨n, rfl⟩⟩ : ↥N), fun n => hf n⟩
  · -- trichotomy fails: a two-element seed
    have hex : ∃ a b : M, ¬ r a b ∧ ¬ r b a ∧ a ≠ b := by
      by_contra hc
      push Not at hc
      exact htri ⟨fun a b hab hba => hc a b hab hba⟩
    obtain ⟨a, b, hab, hba, hne⟩ := hex
    refine ⟨{a, b}, ((Set.finite_singleton b).insert a).countable,
      ⟨a, Set.mem_insert _ _⟩, fun N hXN hwo => ?_⟩
    have ha : a ∈ N := hXN (Set.mem_insert _ _)
    have hb : b ∈ N := hXN (Set.mem_insert_of_mem _ rfl)
    have := hwo
    exact hne (congrArg Subtype.val (Std.Trichotomous.trichotomous
      (r := fun x y : ↥N => r ↑x ↑y) ⟨a, ha⟩ ⟨b, hb⟩ hab hba))

end Defect

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ## The bridge: coded definability forces every model to be well-ordered -/

omit [Countable (Σ l, L.Relations l)] in
/-- **The bridge** (#13's role in this argument), in containment form: if every *code* satisfying
`φ` is a well-order, then every model of `φ` **conjoined with the infiniteness axiom** interprets
the distinguished relation as a well-order.  A defect would survive into a countable
fragment-elementary substructure seeded with its witnesses, and that substructure — infinite by
the added conjunct — transports to a code of `ModelsOf φ` that is not a well-order.

Containment, not equality: the argument only ever pushes a *particular* code into
`wellOrderClass lt`, so nothing is lost, and this is the form the analytic-PC sandwich of #64
supplies — a `pcSentence` whose reduct class sits inside an invariant envelope, never exactly
equals a prescribed set.  `isWellOrder_of_realize` is the equality-form corollary. -/
theorem isWellOrder_of_realize_of_modelsOf_subset (lt : L.Relations 2) {φ : L.Sentenceω}
    (hφ : ModelsOf φ ⊆ wellOrderClass lt) (M : Type) [instM : L.Structure M]
    (hM : Sentenceω.Realize (φ.and (infiniteAxiom L)) M) :
    IsWellOrder M fun x y : M => RelMap lt ![x, y] := by
  by_contra hwo
  obtain ⟨X, hXc, hXne, hXdefect⟩ := exists_countable_defect_seed hwo
  -- a countable fragment-elementary substructure containing the defect witnesses
  obtain ⟨N, hXN, hAe, hNc⟩ := exists_countable_aElementary_substructure (M := M)
    (Fragment.generatedSentence (φ.and (infiniteAxiom L))) hXc
    (Fragment.generatedSentence_countable _)
  obtain ⟨x₀, hx₀⟩ := hXne
  have : Nonempty ↥N := ⟨⟨x₀, hXN hx₀⟩⟩
  have hN : Sentenceω.Realize (φ.and (infiniteAxiom L)) ↥N :=
    (hAe.realize_sentence_iff (Fragment.mem_generatedSentence _)).mp hM
  obtain ⟨hNφ, hNinf⟩ := (BoundedFormulaω.realize_and _ _).mp hN
  -- re-ascribed at the sentence level: `SentenceInf.Realize` is a plain definition upstream, so
  -- `realize_infiniteAxiom`'s implicit arguments cannot be solved against the unfolded form
  have hNinfS : Sentenceω.Realize (infiniteAxiom L) ↥N := hNinf
  have : Infinite ↥N := realize_infiniteAxiom.mp hNinfS
  -- transport it to the carrier `ℕ`
  let e : ↥N ≃ ℕ := (nonempty_equiv_of_countable (α := ↥N) (β := ℕ)).some
  have hd : StructureSpaceOn.encodeViaEquiv e ∈ ModelsOf φ :=
    StructureSpaceOn.encodeViaEquiv_models e hNφ
  -- the ONLY use of the hypothesis: push this one code into the well-order class
  replace hd := hφ hd
  -- the code is a well-order, hence so is `N`
  have hrel : ∀ x y : ℕ, @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y] ↔
        @Structure.RelMap L ↥N _ 2 lt ![e.symm x, e.symm y] := by
    intro x y
    rw [StructureSpaceOn.toStructure_encodeViaEquiv_eq, Equiv.inducedStructure_RelMap]
    rw [show (⇑e.symm ∘ ![x, y]) = ![e.symm x, e.symm y] from
      funext fun i => by fin_cases i <;> rfl]
  have hiso : (fun x y : ℕ => @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y]) ≃r
        fun x y : ↥N => @Structure.RelMap L ↥N _ 2 lt ![x, y] :=
    ⟨e.symm, fun {a b} => (hrel a b).symm⟩
  have : IsWellOrder ℕ fun x y : ℕ => @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y] := hd
  have hwoN : IsWellOrder ↥N fun x y : ↥N => @Structure.RelMap L ↥N _ 2 lt ![x, y] :=
    hiso.symm.toRelEmbedding.isWellOrder
  -- but the defect survived into `N`
  have hsub : ∀ x y : ↥N, (@Structure.RelMap L ↥N _ 2 lt ![x, y] ↔
      @Structure.RelMap L M instM 2 lt ![(x : M), (y : M)]) := by
    intro x y
    have h := N.subtype.map_rel lt ![x, y]
    rw [show (⇑N.subtype ∘ ![x, y]) = ![(x : M), (y : M)] from
      funext fun i => by fin_cases i <;> rfl] at h
    exact h.symm
  refine hXdefect (N : Set M) hXN (@IsWellOrder.mk _ _ ⟨?_⟩ ⟨?_⟩)
  · exact Subrelation.wf (fun {a b} hab => (hsub a b).mpr hab) hwoN.toIsWellFounded.wf
  · exact fun a b hab hba => Std.Trichotomous.trichotomous
      (r := fun x y : ↥N => @Structure.RelMap L ↥N _ 2 lt ![x, y]) a b
      (fun h => hab ((hsub a b).mp h)) (fun h => hba ((hsub b a).mp h))

omit [Countable (Σ l, L.Relations l)] in
/-- **The bridge**, equality form: if a sentence *defines* the well-order class on codes, then
every model of it conjoined with the infiniteness axiom is well-ordered.

The `ModelsOf φ = wellOrderClass lt` specialization of
`isWellOrder_of_realize_of_modelsOf_subset`; the defect-seed argument lives there and is not
repeated. -/
theorem isWellOrder_of_realize (lt : L.Relations 2) {φ : L.Sentenceω}
    (hφ : ModelsOf φ = wellOrderClass lt) (M : Type) [instM : L.Structure M]
    (hM : Sentenceω.Realize (φ.and (infiniteAxiom L)) M) :
    IsWellOrder M fun x y : M => RelMap lt ![x, y] :=
  isWellOrder_of_realize_of_modelsOf_subset lt hφ.subset M hM

/-! ## The endpoint -/

/-- **The countable well-order class is not Borel** (issue #33): no Borel set of codes consists
exactly of the well-ordered ones. -/
@[blueprint "thm:wellordering-nonborel"
  (title := /-- Non-Borelness of the countable well-order class -/)
  (statement := /-- Over a countable relational vocabulary with a distinguished binary
    relation, the class of codes whose relation well-orders the carrier is **not** Borel in the
    logic space. -/)
  (proof := /-- If it were Borel, López--Escobar would present it as $\mathrm{ModelsOf}\
    \varphi$ — but only over coded structures, whose carrier is $\mathbb{N}$.  Conjoin the
    $\Lomegaone$ infiniteness axiom, so that no finite model escapes, and let $M$ be any model
    of the conjunction whose relation is not a well-order.  A well-order here is trichotomy
    plus well-foundedness, so the failure is witnessed either by two incomparable unequal
    elements or by an infinite descending chain; seed a countable fragment-elementary
    substructure with those witnesses and the failure survives, while the added conjunct keeps
    the substructure infinite, so it transports to a code lying in the class without being a
    well-order — a contradiction.  Hence every model of the conjunction is well-ordered, and
    Marker's Corollary 4.27 bounds all their order types by one countable $\alpha$; the
    comparison structure of type $\alpha + \omega$ transported to $\mathbb{N}$ is a code of the
    class exceeding that bound. -/)
  (uses := ["thm:lopez-escobar", "thm:wellordering-boundedness"])]
theorem wellOrderClass_not_measurableSet (lt : L.Relations 2) :
    ¬ MeasurableSet (wellOrderClass lt) := by
  intro hB
  -- López–Escobar: the class is defined by a sentence, on codes
  obtain ⟨φ, hφ⟩ := lopez_escobar hB (wellOrderClass_isomorphismInvariant lt)
  -- every model of `φ ⊓ infiniteAxiom` is well-ordered, so its order types are bounded
  obtain ⟨α, hα, hbound⟩ := wellOrder_type_boundedness (φ.and (infiniteAxiom L)) lt
    (fun M inst hreal => isWellOrder_of_realize lt hφ.symm M hreal)
  -- `α + ω` is countable, infinite, and at least `α`
  have hαc : α.card ≤ Cardinal.aleph0 := by
    have h1 : α.card < Cardinal.aleph 1 := Cardinal.lt_ord.mp hα
    rw [show Cardinal.aleph 1 = Order.succ (Cardinal.aleph 0) from by
      rw [Cardinal.succ_aleph, zero_add], Cardinal.aleph_zero] at h1
    exact Order.lt_succ_iff.mp h1
  have hcnt : α + Ordinal.omega0 < (Cardinal.aleph 1).ord := by
    rw [Cardinal.lt_ord, Ordinal.card_add, Ordinal.card_omega0]
    calc α.card + Cardinal.aleph0 ≤ Cardinal.aleph0 + Cardinal.aleph0 :=
          add_le_add hαc le_rfl
      _ = Cardinal.aleph0 := Cardinal.aleph0_add_aleph0
      _ < Cardinal.aleph 1 := by
          rw [show Cardinal.aleph 1 = Order.succ (Cardinal.aleph 0) from by
            rw [Cardinal.succ_aleph, zero_add], Cardinal.aleph_zero]
          exact Order.lt_succ _
  -- but the class realizes every countably infinite order type
  obtain ⟨c, hc, htype⟩ := exists_code_type_eq (L := L) lt
    (β := α + Ordinal.omega0) le_add_self hcnt
  have hcφ : @Sentenceω.Realize L (φ.and (infiniteAxiom L)) ℕ c.toStructure := by
    let : L.Structure ℕ := c.toStructure
    have hinf : Sentenceω.Realize (infiniteAxiom L) ℕ := realize_infiniteAxiom.mpr inferInstance
    refine (BoundedFormulaω.realize_and _ _).mpr ⟨?_, hinf⟩
    have hmem : c ∈ ModelsOf φ := by rw [← hφ]; exact hc
    exact hmem
  have hb : @Ordinal.type ℕ
      (fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]) hc < α :=
    hbound ℕ c.toStructure hcφ
  rw [htype] at hb
  exact absurd hb (not_lt.mpr le_self_add)

end FirstOrder.Language
