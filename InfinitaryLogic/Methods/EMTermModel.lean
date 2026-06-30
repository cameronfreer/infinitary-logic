/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SkolemClosure
import InfinitaryLogic.Methods.EM.TailAdapter
import InfinitaryLogic.Lomega1omega.QuantifierRank
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ehrenfeucht–Mostowski term model (M-deep-interpretation), step 1: skeleton support

The bespoke EM term model realizes the tail-template theory over `(skolemColim L)[[J]]` without
full compactness. Its carrier is the closed terms quotiented by **deep equality in the source model
`M`**: two closed terms are identified when, interpreting their finitely-many `J`-constants as a
strictly-increasing *deep* tuple of the tail-indiscernible sequence, they evaluate equally in `M`
(eventually, as the depth grows). Congruence is then inherited from `M` being a genuine structure.

This file builds the first ingredient: the finite set of `J`-constants ("skeleton constants")
mentioned in a closed term, which the deep interpretation enumerates in increasing `J`-order.
-/

namespace FirstOrder.Language

/-- The variables of a relabeled term are the image of the original variables (a Mathlib gap). -/
theorem Term.varFinset_relabel {L' : Language} {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : α → β) (t : L'.Term α) : (t.relabel g).varFinset = t.varFinset.image g := by
  induction t with
  | var i => simp [Term.relabel, Term.varFinset]
  | func f ts ih =>
    ext x
    simp only [Term.relabel, Term.varFinset, ih, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    tauto

/-- A term's realization depends only on the assignment of the variables that actually appear (a
Mathlib gap). -/
theorem Term.realize_eq_of_eq_on_varFinset {L' : Language} {M' : Type} [L'.Structure M']
    {α : Type} [DecidableEq α] {v w : α → M'} :
    ∀ t : L'.Term α, (∀ x ∈ t.varFinset, v x = w x) → t.realize v = t.realize w := by
  intro t
  induction t with
  | var i => intro h; exact h i (by simp [Term.varFinset])
  | func f ts ih =>
    intro h
    simp only [Term.realize]
    congr 1
    funext i
    exact ih i (fun x hx => h x (by
      simp only [Term.varFinset, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, hx⟩))

/-! ### Quantifier-rank invariance under the operations of `skolemWitnessFormula`

The `all`/Skolem case of the truth lemma recurses into `skolemWitnessFormula (¬φ)`, which is **not a
structural subformula** of `all φ`. The correct termination measure is lexicographic `(qrank, depth)`:
`qrank` strictly drops at the Skolem step (`qrank (skolemWitnessFormula (¬φ)) = qrank φ < qrank (all φ)`)
while `depth` handles `imp`/`iSup`/`iInf` at equal `qrank`. These lemmas establish the `qrank` half.
(`qrank_relabel`/`qrank_not`/`qrank_castLE` already exist in `QuantifierRank.lean`; these three are the
remaining `mapLanguage`/`openBounds`/`subst` cases. They belong in `QuantifierRank.lean` eventually.) -/

/-- `qrank` is invariant under language maps (they preserve the connective/quantifier skeleton). -/
theorem BoundedFormulaω.qrank_mapLanguage {L L' : Language} (g : L →ᴸ L') {α : Type*} {n : ℕ}
    (φ : L.BoundedFormulaω α n) : (φ.mapLanguage g).qrank = φ.qrank := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.qrank, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.qrank, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.qrank]; exact iSup_congr ih
  | iInf φs ih =>
    simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.qrank]; exact iSup_congr ih

/-- `qrank` is invariant under free-variable substitution. -/
theorem BoundedFormulaω.qrank_subst {L : Language} {α β : Type} {n : ℕ} (tf : α → L.Term β)
    (φ : L.BoundedFormulaω α n) : (φ.subst tf).qrank = φ.qrank := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.subst, BoundedFormulaω.qrank, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.subst, BoundedFormulaω.qrank, ih]
  | iSup φs ih => simp only [BoundedFormulaω.subst, BoundedFormulaω.qrank]; exact iSup_congr ih
  | iInf φs ih => simp only [BoundedFormulaω.subst, BoundedFormulaω.qrank]; exact iSup_congr ih

/-- `qrank` is invariant under `openBounds` (it preserves quantifier nesting; the `all` case adds a
`relabel`, which `qrank_relabel` discharges). -/
theorem BoundedFormulaω.qrank_openBounds {L : Language} {n : ℕ} (φ : L.BoundedFormulaω Empty n) :
    φ.openBounds.qrank = φ.qrank := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.qrank, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.qrank, BoundedFormulaω.qrank_relabel, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.qrank]; exact iSup_congr ih
  | iInf φs ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.qrank]; exact iSup_congr ih

variable (L : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- **The Skolem-step measure decrease** (foundation of the `all`-case induction): the Skolem witness
formula of `¬φ` has strictly smaller quantifier rank than `all φ`. Since `skolemWitnessFormula` only
applies `openBounds`/`mapLanguage`/`subst`/`relabel`/`not` to `φ` — all `qrank`-invariant — its rank is
`qrank φ`, while `qrank (all φ) = qrank φ + 1`. This is the `qrank` component of the lexicographic
`(qrank, depth)` termination measure for the full truth lemma. -/
theorem qrank_skolemWitnessFormula_lt {k n : ℕ}
    (φ : (skolemStage L k).BoundedFormulaω Empty (n + 1)) :
    (skolemWitnessFormula L φ.not).qrank < (BoundedFormulaω.all φ).qrank := by
  simp only [skolemWitnessFormula, BoundedFormulaω.qrank_relabel, BoundedFormulaω.qrank_subst,
    BoundedFormulaω.qrank_mapLanguage, BoundedFormulaω.qrank_openBounds, BoundedFormulaω.qrank_not,
    BoundedFormulaω.qrank_all]
  exact lt_add_one _

/-- The `J`-constant carried by a function symbol of `(skolemColim L)[[J]]`: only an arity-`0`
symbol from the `constantsOn J` summand is a skeleton constant. -/
def jConstOf : {n : ℕ} → (skolemColim L)[[J]].Functions n → Finset J
  | 0, Sum.inr j => {j}
  | _, _ => ∅

/-- The finite set of `J`-constants (skeleton constants) mentioned in a term of
`(skolemColim L)[[J]]`. The deep interpretation enumerates this support in increasing `J`-order. -/
def jSupport {α : Type} : (skolemColim L)[[J]].Term α → Finset J
  | .var _ => ∅
  | .func f ts => (Finset.univ.biUnion fun i => jSupport (ts i)) ∪ jConstOf L J f

/-- Support monotonicity: an argument's skeleton support is contained in the whole term's. -/
theorem jSupport_subterm {α : Type} {n : ℕ} (f : (skolemColim L)[[J]].Functions n)
    (ts : Fin n → (skolemColim L)[[J]].Term α) (i : Fin n) :
    jSupport L J (ts i) ⊆ jSupport L J (.func f ts) := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

/-- The de-substituted term `constantsToVars t` uses only the variables `Sum.inl j` for `j` a
skeleton constant of `t`: its variable set is contained in `Sum.inl` of the skeleton support. -/
theorem constantsToVars_varFinset_subset (t : (skolemColim L)[[J]].Term Empty) :
    t.constantsToVars.varFinset ⊆ (jSupport L J t).image Sum.inl := by
  induction t with
  | var e => exact e.elim
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | c
      · simp [Term.constantsToVars, Term.varFinset]
      · simp only [Term.constantsToVars, jSupport, jConstOf, Term.varFinset]; rfl
    · rcases f with f' | c
      · simp only [Term.constantsToVars, Term.varFinset, jSupport, jConstOf, Finset.union_empty]
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hxi⟩ := hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (ih i hxi)
        exact Finset.mem_image.mpr ⟨y, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩, rfl⟩
      · exact c.elim

/-! ### Step 2: ordered support (ranks) -/

/-- The **rank** of `j` in a finite support `S`: the number of support elements below it, i.e. its
0-indexed position in the increasing `J`-order. So a support `{j₀ < j₁ < …}` has ranks `0, 1, …`
and the deep interpretation sends it to `a_d, a_{d+1}, …` (a strictly-increasing deep tuple). -/
def deepRank (S : Finset J) (j : J) : ℕ := (S.filter (· < j)).card

/-- On the support, ranks strictly increase with `J`-order: the deep tuple is strictly increasing,
hence injective on the support. -/
theorem deepRank_lt_of_lt {S : Finset J} {j j' : J} (hj : j ∈ S) (hjj' : j < j') :
    deepRank J S j < deepRank J S j' := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hjj'⟩
  · exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hj, hjj'⟩))).2 (lt_irrefl j)

/-- The rank of the `i`-th support element (in increasing order) is `i`: the enumeration
`orderEmbOfFin` and the rank are mutually inverse. The elements of `S` strictly below the `i`-th
are exactly the first `i`. -/
theorem deepRank_orderEmbOfFin (S : Finset J) {k : ℕ} (h : S.card = k) (i : Fin k) :
    deepRank J S (S.orderEmbOfFin h i) = (i : ℕ) := by
  have step : S.filter (· < S.orderEmbOfFin h i)
      = (Finset.univ.filter (fun j : Fin k => j < i)).image (S.orderEmbOfFin h) := by
    conv_lhs => arg 2; rw [← Finset.image_orderEmbOfFin_univ S h]
    rw [Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, OrderEmbedding.lt_iff_lt]
  unfold deepRank
  rw [step, Finset.card_image_of_injective _ (S.orderEmbOfFin h).injective,
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

/-- The rank of a support element is below the cardinality: a valid `Fin S.card` position. -/
theorem deepRank_lt_card {S : Finset J} {j : J} (hj : j ∈ S) : deepRank J S j < S.card := by
  have hmem : (j : J) ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin S rfl]; exact hj
  obtain ⟨i, rfl⟩ := hmem
  rw [deepRank_orderEmbOfFin]; exact i.2

/-- The enumeration recovers a support element from its rank: `orderEmbOfFin` at position
`deepRank S j` is `j`, for `j ∈ S`. -/
theorem orderEmbOfFin_deepRank (S : Finset J) {k : ℕ} (h : S.card = k) {j : J} (hj : j ∈ S)
    (hlt : deepRank J S j < k) : S.orderEmbOfFin h ⟨deepRank J S j, hlt⟩ = j := by
  have hmem : (j : J) ∈ Set.range (S.orderEmbOfFin h) := by
    rw [Finset.range_orderEmbOfFin S h]; exact hj
  obtain ⟨i, rfl⟩ := hmem
  congr 1
  exact Fin.ext (deepRank_orderEmbOfFin J S h i)

/-! ### Step 3: deep interpretation -/

section DeepInterp

variable {M : Type} [L.Structure M] [Nonempty M] (a : ℕ → M)

/-- The **deep interpretation** of a closed term at depth `d` relative to a support `S`: interpret
each `J`-constant `c_j` by the source sequence at position `d + deepRank S j` (so support constants
map to a strictly-increasing deep tuple of `a`), and evaluate in `M`'s `L^Sk`-structure. -/
noncomputable def deepInterp (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) : M :=
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  t.realize Empty.elim

/-- Deep interpretation commutes with function application (same depth and support): it is the
structure's `funMap` of the argument interpretations. Immediate from `Term.realize`. -/
theorem deepInterp_func (d : ℕ) (S : Finset J) {n : ℕ}
    (f : (skolemColim L)[[J]].Functions n) (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    deepInterp L J a d S (.func f ts) =
      letI : (skolemColim L).Structure M := skolemColimStructure L
      letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
      Structure.funMap f (fun i => deepInterp L J a d S (ts i)) :=
  rfl

/-- Shifting the depth past a cutoff sends every support constant past it: each constant lands at
position `≥ d`, so `N ≤ d` forces all positions `≥ N`. -/
theorem le_depth_position (d : ℕ) (S : Finset J) (j : J) : d ≤ d + deepRank J S j :=
  Nat.le_add_right _ _

/-- Deep interpretation commutes with `Fin.snoc`: interpreting the one-point extension `Fin.snoc ts u`
gives the snoc of the interpretations. The term-side bridge for the truth lemma's `all` case (relating
the carrier's `∀x` over term-classes to the body's argument tuple). -/
theorem deepInterp_snoc (d : ℕ) (S : Finset J) {n : ℕ}
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (u : (skolemColim L)[[J]].Term Empty) :
    (fun i => deepInterp L J a d S
        ((Fin.snoc ts u : Fin (n + 1) → (skolemColim L)[[J]].Term Empty) i))
      = Fin.snoc (fun i => deepInterp L J a d S (ts i)) (deepInterp L J a d S u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-- The **colimit Skolem-witness term**: the stage-`(k+1)` Skolem function symbol for the stage-`k`
formula `χ` (of arity `n+1`), included into `L^Sk` and then `[[J]]`, applied to the closed argument
terms `ts`. Its deep interpretation is the Hilbert-Skolem value for `∃x χ`. -/
def skWitnessTerm {k n : ℕ} (χ : (skolemStage L k).BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) : (skolemColim L)[[J]].Term Empty :=
  Term.func ((lhomWithConstants (skolemColim L) J).onFunction
    ((skolemStageInclusion L (k + 1)).onFunction
      (Sum.inr χ : (skolemStage L (k + 1)).Functions n))) ts

/-- The witness term mentions only the `J`-constants of its arguments (its head is an `L^Sk`-function
symbol, not a skeleton constant), so its support is covered whenever the arguments' is. -/
theorem jSupport_skWitnessTerm {k n : ℕ} (χ : (skolemStage L k).BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    jSupport L J (skWitnessTerm L J χ ts) = Finset.univ.biUnion fun i => jSupport L J (ts i) := by
  have hjc : jConstOf L J ((lhomWithConstants (skolemColim L) J).onFunction
      ((skolemStageInclusion L (k + 1)).onFunction (Sum.inr χ))) = ∅ := by cases n <;> rfl
  rw [skWitnessTerm,
    show jSupport L J (Term.func ((lhomWithConstants (skolemColim L) J).onFunction
        ((skolemStageInclusion L (k + 1)).onFunction (Sum.inr χ))) ts)
      = (Finset.univ.biUnion fun i => jSupport L J (ts i))
        ∪ jConstOf L J ((lhomWithConstants (skolemColim L) J).onFunction
            ((skolemStageInclusion L (k + 1)).onFunction (Sum.inr χ))) from rfl,
    hjc, Finset.union_empty]

/-- **Deep value of the Skolem-witness term**: it is exactly the Hilbert-choice Skolem value for `χ`
on the deep interpretations of the arguments (read in the source model's stage-`k` structure). The
funMap coherence through `skolemColimStructure`/`skolemStageStructure`/`skolem₁ωStructure` is fully
definitional, so this is `rfl` after the term/funMap unfolding. -/
theorem deepInterp_skWitness (d : ℕ) (S : Finset J) {k n : ℕ}
    (χ : (skolemStage L k).BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    letI : (skolemStage L k).Structure M := skolemStageStructure L k
    deepInterp L J a d S (skWitnessTerm L J χ ts)
      = Classical.epsilon (fun b => χ.Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => deepInterp L J a d S (ts i)) b)) := by
  rw [skWitnessTerm, deepInterp_func]; rfl

/-- **Skolem-witness universality** (the contrapositive Skolem axiom, transported to the deep tuple):
if the body `ψ₀` holds at the deep interpretation of its Skolem-witness term (for `¬ψ₀`), then it holds
at *every* `M`-element. This is `hw` for the truth lemma's `all` case, supplied to
`eventualDeepTruth_all_support_self_of_skolem`. Proof: transport the colimit realizations to stage `k`
(`realize_map_stageInclusion`), then `skolem₁ω_funMap_spec` on `¬ψ₀` — its Skolem value (the witness
term's deep value, by `deepInterp_skWitness`) is a counterexample whenever one exists. -/
theorem skWitness_universal (d : ℕ) (S : Finset J) {k n : ℕ}
    (ψ₀ : (skolemStage L k).BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (ψ₀.mapLanguage (skolemStageInclusion L k)).Realize (Empty.elim : Empty → M)
        (Fin.snoc (fun i => deepInterp L J a d S (ts i))
          (deepInterp L J a d S (skWitnessTerm L J ψ₀.not ts))) →
      ∀ x : M, (ψ₀.mapLanguage (skolemStageInclusion L k)).Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => deepInterp L J a d S (ts i)) x) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (skolemStage L k).Structure M := skolemStageStructure L k
  simp only [realize_map_stageInclusion]
  intro hψw x
  by_contra hcon
  have hex : ∃ b, (ψ₀.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => deepInterp L J a d S (ts i)) b) :=
    ⟨x, by rw [BoundedFormulaω.realize_not]; exact hcon⟩
  have hspec := skolem₁ω_funMap_spec (ψ₀.not) (fun i => deepInterp L J a d S (ts i)) hex
  rw [show Structure.funMap (L := skolem₁ω (skolemStage L k)) ψ₀.not
        (fun i => deepInterp L J a d S (ts i))
      = deepInterp L J a d S (skWitnessTerm L J ψ₀.not ts) from
      (deepInterp_skWitness L J a d S ψ₀.not ts).symm,
    BoundedFormulaω.realize_not] at hspec
  exact hspec hψw

/-- **De-substitution bridge** (step 2): the deep interpretation of a closed term equals the
*de-substituted* `L^Sk`-term `constantsToVars t` (each skeleton constant `c_j` turned into the
variable `Sum.inl j`) realized with `j ↦ a (d + deepRank S j)`. Turns the support machinery from
combinatorial into semantic — the right-hand side is a genuine formula realization, so tail
indiscernibility applies. -/
theorem deepInterp_eq_realize (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S t =
      t.constantsToVars.realize (Sum.elim (fun j => a (d + deepRank J S j)) Empty.elim) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  show t.realize Empty.elim = _
  exact (Term.realize_constantsToVars (t := t) (v := Empty.elim)).symm

/-- **M-side term substitution**: the deep interpretation of a substituted term is the realization
(in `M`'s `[[J]]`-structure at depth `d`) of the body on the deep interpretations of the substituted
terms. Mostly `Term.realize_subst` (deep interpretation *is* realization in the `σ_d`-structure). -/
theorem deepInterp_subst (d : ℕ) (S : Finset J) {n : ℕ}
    (t : (skolemColim L)[[J]].Term (Empty ⊕ Fin n))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
    deepInterp L J a d S (t.subst (Sum.elim (fun e => e.elim) ts)) =
      t.realize (Sum.elim Empty.elim fun i => deepInterp L J a d S (ts i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
  show (t.subst (Sum.elim (fun e => e.elim) ts)).realize Empty.elim = _
  rw [Term.realize_subst]
  congr 1
  funext x
  cases x with
  | inl e => exact e.elim
  | inr i => rfl

/-- **Deep interpretation of a base-language substituted term**: combining `deepInterp_subst` with
`realize_onTerm`, the deep interpretation of `(onTerm t).subst ts` equals `t` realized in `M`'s
`L^Sk`-structure on the deep interpretations of the substituted terms. -/
theorem deepInterp_onTerm_subst (d : ℕ) (S : Finset J) {n : ℕ}
    (t : (skolemColim L).Term (Empty ⊕ Fin n))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S
        (((lhomWithConstants (skolemColim L) J).onTerm t).subst (Sum.elim (fun e => e.elim) ts)) =
      t.realize (Sum.elim Empty.elim fun i => deepInterp L J a d S (ts i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
  rw [deepInterp_subst]
  exact LHom.realize_onTerm (lhomWithConstants (skolemColim L) J) t _

/-- The **de-substituted term at ordered support positions**: each skeleton constant `c_j` becomes
the `ℕ`-variable `deepRank S j` (its 0-indexed position in the increasing support order). An
`L^Sk`-term over `ℕ`. (Over `ℕ` rather than `Fin S.card` so the relabel needs no junk value; only
the values `< S.card` are hit when `jSupport t ⊆ S`.) -/
def deTermPos (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) : (skolemColim L).Term ℕ :=
  t.constantsToVars.relabel (Sum.elim (fun j => deepRank J S j) Empty.elim)

/-- The ordered-position term uses only variables `< S.card` (valid `Fin S.card` positions), once the
support `S` covers the term's skeleton constants. -/
theorem deTermPos_varFinset_subset {S : Finset J} {t : (skolemColim L)[[J]].Term Empty}
    (hsub : jSupport L J t ⊆ S) : (deTermPos L J S t).varFinset ⊆ Finset.range S.card := by
  rw [deTermPos, Term.varFinset_relabel]
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (constantsToVars_varFinset_subset L J t hx)
  simp only [Sum.elim_inl]
  exact Finset.mem_range.mpr (deepRank_lt_card (J := J) (hsub hj))

/-- **Ordered-position realize bridge** (step 3): the deep interpretation is the realize of the
ordered-position de-substituted term on the *consecutive* deep tuple `n ↦ a (d + n)`. The cleaned-up
form of `deepInterp_eq_realize`, with variables at ordered support positions — exactly the shape tail
indiscernibility consumes (a strictly-increasing deep tuple). -/
theorem deepInterp_eq_realize_pos (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S t = (deTermPos L J S t).realize (fun n => a (d + n)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deepInterp_eq_realize, deTermPos, Term.realize_relabel]
  congr 1
  funext x
  cases x with
  | inl j => rfl
  | inr e => exact e.elim

/-- The **de-substituted term at `Fin S.card` positions**: `deTermPos` with its (already `< S.card`)
variables packaged as genuine `Fin S.card` indices, via `restrictVar` (no junk value needed, since
every variable that appears is `< S.card` when `S` covers the skeleton constants). The arity-`S.card`
term whose equality atom tail indiscernibility consumes. -/
def deTermFin (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) (hsub : jSupport L J t ⊆ S) :
    (skolemColim L).Term (Fin S.card) :=
  (deTermPos L J S t).restrictVar
    (fun x => ⟨x.1, Finset.mem_range.mp (deTermPos_varFinset_subset (L := L) (J := J) hsub x.2)⟩)

/-- **`Fin`-arity realize bridge**: the deep interpretation is the realize of the `Fin S.card`-indexed
de-substituted term on the consecutive deep tuple `i ↦ a (d + i)`. The `Fin`-arity form of
`deepInterp_eq_realize_pos`, directly feeding the atom. -/
theorem deepInterp_eq_realize_fin (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty)
    (hsub : jSupport L J t ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S t = (deTermFin L J S t hsub).realize (fun i : Fin S.card => a (d + i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deepInterp_eq_realize_pos, deTermFin]
  symm
  exact Term.realize_restrictVar (fun n => a (d + n)) (fun _ => rfl)

/-- **Per-term superset realize**: the `Fin`-arity de-substituted term over `S`, realized on the
`T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))`, equals the deep interpretation
over the larger support `T`. The core shared by the equality- and relation-atom superset bridges
(restrictVar realize with a `dite`-extended assignment, then `realize_eq_of_eq_on_varFinset` to
discard the junk, then `orderEmbOfFin_deepRank`). -/
theorem deTermFin_realize_superset (d : ℕ) (S T : Finset J) (w : (skolemColim L)[[J]].Term Empty)
    (hw : jSupport L J w ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deTermFin L J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = deepInterp L J a d T w := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  have hrv : (deTermFin L J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = (deTermPos L J S w).realize
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0)) := by
    rw [deTermFin]
    refine Term.realize_restrictVar
      (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
      (fun x => ?_)
    simp only [dif_pos (Finset.mem_range.mp (deTermPos_varFinset_subset (L := L) (J := J) hw x.2))]
  rw [hrv, deepInterp_eq_realize, deTermPos, Term.realize_relabel]
  apply Term.realize_eq_of_eq_on_varFinset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (constantsToVars_varFinset_subset L J w hx)
  have hjS : j ∈ S := hw hj
  have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
  simp only [Function.comp_apply, Sum.elim_inl, dif_pos hlt]
  rw [orderEmbOfFin_deepRank J S rfl hjS hlt]

/-- The **de-substituted equality atom** of two closed terms over a covering support `S`: an
`L^Sk`-formula of arity `S.card` whose truth on the consecutive deep tuple is the deep equality of
`t, u`. Since `L^Sk` is countable, all such atoms form a countable family that seeds the
tail-indiscernible `Γ`. -/
def deEqAtom (S : Finset J) (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S) :
    (skolemColim L).BoundedFormulaω Empty S.card :=
  BoundedFormulaω.equal ((deTermFin L J S t ht).relabel Sum.inr)
    ((deTermFin L J S u hu).relabel Sum.inr)

/-- **Atom realize bridge** (step 4): the de-substituted equality atom holds on the consecutive deep
tuple `i ↦ a (d + i)` iff `t` and `u` have equal deep interpretations at depth `d` over `S`. -/
theorem realize_deEqAtom (d : ℕ) (S : Finset J) (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deEqAtom L J S t u ht hu).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      deepInterp L J a d S t = deepInterp L J a d S u := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel,
    Sum.elim_comp_inr, ← deepInterp_eq_realize_fin (t := t) (hsub := ht),
    ← deepInterp_eq_realize_fin (t := u) (hsub := hu)]

/-- **Superset atom bridge** (step 5, renaming): the *same* equality atom over `S`, realized on the
`T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))` (where `S ⊆ T`), holds iff `t` and
`u` have equal deep interpretations over the larger support `T`. So one arity-`S.card` formula carries
both the `S`-truth (on the consecutive tuple) and the `T`-truth (on this strictly-increasing tuple) —
the input to tail indiscernibility. -/
theorem realize_deEqAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T)
    (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deEqAtom L J S t u ht hu).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      deepInterp L J a d T t = deepInterp L J a d T u := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  have key : ∀ (w : (skolemColim L)[[J]].Term Empty) (hw : jSupport L J w ⊆ S),
      (deTermFin L J S w hw).realize
          (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
        = deepInterp L J a d T w := by
    intro w hw
    have hrv : (deTermFin L J S w hw).realize
          (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
        = (deTermPos L J S w).realize
          (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0)) := by
      rw [deTermFin]
      refine Term.realize_restrictVar
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
        (fun x => ?_)
      simp only [dif_pos (Finset.mem_range.mp (deTermPos_varFinset_subset (L := L) (J := J) hw x.2))]
    rw [hrv, deepInterp_eq_realize, deTermPos, Term.realize_relabel]
    apply Term.realize_eq_of_eq_on_varFinset
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (constantsToVars_varFinset_subset L J w hx)
    have hjS : j ∈ S := hw hj
    have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
    simp only [Function.comp_apply, Sum.elim_inl, dif_pos hlt]
    rw [orderEmbOfFin_deepRank J S rfl hjS hlt]
  rw [deEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel,
    Sum.elim_comp_inr, key t ht, key u hu]

/-- The **de-substituted relation atom**: the relation `R` applied to the `Fin`-arity de-substituted
terms of a tuple over a covering support `S`. The relation analogue of `deEqAtom`. -/
def deRelAtom (S : Finset J) {l : ℕ} (R : (skolemColim L).Relations l)
    (ts : Fin l → (skolemColim L)[[J]].Term Empty) (ht : ∀ i, jSupport L J (ts i) ⊆ S) :
    (skolemColim L).BoundedFormulaω Empty S.card :=
  BoundedFormulaω.rel R fun i => (deTermFin L J S (ts i) (ht i)).relabel Sum.inr

/-- **Relation atom realize bridge**: the de-substituted relation atom holds on the consecutive deep
tuple iff `R` holds in `M` on the deep interpretations over `S`. -/
theorem realize_deRelAtom (d : ℕ) (S : Finset J) {l : ℕ} (R : (skolemColim L).Relations l)
    (ts : Fin l → (skolemColim L)[[J]].Term Empty) (ht : ∀ i, jSupport L J (ts i) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deRelAtom L J S R ts ht).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      Structure.RelMap R fun i => deepInterp L J a d S (ts i) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, ← deepInterp_eq_realize_fin]

/-- **Superset relation atom bridge**: the same relation atom over `S`, realized on the `T`-induced
deep tuple (`S ⊆ T`), holds iff `R` holds in `M` on the deep interpretations over `T`. The relation
analogue of `realize_deEqAtom_superset`, via `deTermFin_realize_superset`. -/
theorem realize_deRelAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T) {l : ℕ}
    (R : (skolemColim L).Relations l) (ts : Fin l → (skolemColim L)[[J]].Term Empty)
    (ht : ∀ i, jSupport L J (ts i) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deRelAtom L J S R ts ht).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      Structure.RelMap R fun i => deepInterp L J a d T (ts i) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, deTermFin_realize_superset]

/-- **Support of a base-language term after bound-variable substitution**: substituting the closed
terms `ts` for the free variables of a base-language term `(onTerm t)` (which itself carries no
`J`-constants, being a `skolemColim L`-image) produces only the `J`-constants of the `ts`. The bridge
from the truth lemma's uniform support hypothesis `S ⊇ ⋃ jSupport (ts i)` to the per-atom support
hypotheses of `eventualDeepTruth_equal_iff`/`_rel_iff`. -/
theorem jSupport_onTerm_subst_subset {n : ℕ} (t : (skolemColim L).Term (Empty ⊕ Fin n))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    jSupport L J (((lhomWithConstants (skolemColim L) J).onTerm t).subst
        (Sum.elim (fun e => e.elim) ts))
      ⊆ Finset.univ.biUnion fun i => jSupport L J (ts i) := by
  induction t with
  | var x =>
    cases x with
    | inl e => exact e.elim
    | inr i => exact Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)
  | @func l f args ih =>
    have hjc : jConstOf L J ((lhomWithConstants (skolemColim L) J).onFunction f) = ∅ := by
      cases l <;> rfl
    show jSupport L J (Term.func ((lhomWithConstants (skolemColim L) J).onFunction f) _) ⊆ _
    rw [jSupport, hjc, Finset.union_empty]
    exact Finset.biUnion_subset.mpr fun i _ => ih i

/-! ### Step 3': the general de-substituted formula

`deEqAtom`/`deRelAtom` reduce *atoms* on deep interpretations to `L^Sk`-formulas of arity `S.card`
on the consecutive deep tuple. The general truth lemma needs the same reduction for an *arbitrary*
base-language formula `φ` (to obtain the 0-1 law for `φ`'s eventual deep truth from tail
indiscernibility). `deForm` performs it uniformly: open `φ`'s bound variables to free, substitute each
by the `Fin`-arity de-substituted term `deTermFin S (ts i)`, and rebind the support positions. -/

/-- The **general de-substituted formula** of `φ` on closed argument terms `ts` over a covering
support `S`: an `L^Sk`-formula of arity `S.card` whose realization on the consecutive deep tuple is
`φ` realized on the deep interpretations of `ts`. Generalizes `deEqAtom`/`deRelAtom` to all formulas
(`openBounds → subst → relabel Sum.inr`). -/
def deForm (S : Finset J) {n : ℕ} (φ : (skolemColim L).BoundedFormulaω Empty n)
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (hsub : ∀ i, jSupport L J (ts i) ⊆ S) :
    (skolemColim L).BoundedFormulaω Empty S.card :=
  (φ.openBounds.subst (fun i => deTermFin L J S (ts i) (hsub i))).relabel Sum.inr

/-- **General formula realize bridge** (generalizes `realize_deEqAtom`/`realize_deRelAtom`): the
de-substituted formula holds on the consecutive deep tuple `i ↦ a (d + i)` iff `φ` holds in `M` (its
`L^Sk`-structure) on the deep interpretations of `ts` at depth `d` over `S`. -/
theorem realize_deForm (d : ℕ) (S : Finset J) {n : ℕ}
    (φ : (skolemColim L).BoundedFormulaω Empty n)
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (hsub : ∀ i, jSupport L J (ts i) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deForm L J S φ ts hsub).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      φ.Realize Empty.elim (fun i => deepInterp L J a d S (ts i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  have hassign : (fun i => (deTermFin L J S (ts i) (hsub i)).realize
        (fun i : Fin S.card => a (d + i)))
      = (fun i => deepInterp L J a d S (ts i)) :=
    funext fun i => (deepInterp_eq_realize_fin L J a d S (ts i) (hsub i)).symm
  rw [deForm, BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.Realize, BoundedFormulaω.realize_subst]
  rw [hassign]
  exact realize_openBounds φ _

/-! ### Step 4: eventual deep equality `EMEq` and the carrier -/

/-- **Eventual deep equality**: closed terms `t, u` are identified when, for all sufficiently deep
interpretations of their **combined** skeleton support, they evaluate equally in `M`. (The combined
support means both terms are read against the same ordered finite skeleton.) -/
def EMEq (t u : (skolemColim L)[[J]].Term Empty) : Prop :=
  ∀ᶠ d in Filter.atTop,
    deepInterp L J a d (jSupport L J t ∪ jSupport L J u) t =
      deepInterp L J a d (jSupport L J t ∪ jSupport L J u) u

theorem EMEq.refl (t : (skolemColim L)[[J]].Term Empty) : EMEq L J a t t :=
  Filter.Eventually.of_forall fun _ => rfl

theorem EMEq.symm {t u : (skolemColim L)[[J]].Term Empty} (h : EMEq L J a t u) :
    EMEq L J a u t := by
  unfold EMEq
  rw [Finset.union_comm (jSupport L J u) (jSupport L J t)]
  exact h.mono fun _ hd => hd.symm

/-- **Support-enlargement invariance** (steps 6-7, the atom-slice payoff): if `t, u` are eventually
deep-equal on their combined support `S₀` (i.e. `EMEq t u`) and the de-substituted equality atom of
`S₀` lies in a tail-indiscernible family `Γ`, then they are eventually deep-equal on *any* larger
support `S ⊇ S₀`. Tail indiscernibility identifies the truth of the one arity-`S₀.card` atom on the
consecutive `S₀`-tuple and on the strictly-increasing `S`-tuple; the two atom bridges convert those to
the `S₀`- and `S`-deep equalities. This is the unlock for `EMEq.trans` and the quotient structure's
function/relation congruence. -/
theorem EMEq_eventually_on_superset
    {Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)}
    (hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ)
    {t u : (skolemColim L)[[J]].Term Empty}
    (hmem : (⟨(jSupport L J t ∪ jSupport L J u).card,
        deEqAtom L J (jSupport L J t ∪ jSupport L J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ)
    (h : EMEq L J a t u) {S : Finset J} (hS : jSupport L J t ∪ jSupport L J u ⊆ S) :
    ∀ᶠ d in Filter.atTop, deepInterp L J a d S t = deepInterp L J a d S u := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  set S₀ := jSupport L J t ∪ jSupport L J u with hS₀def
  obtain ⟨N, hN⟩ := hind hmem
  rw [EMEq, Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  rw [Filter.eventually_atTop]
  refine ⟨max N N₀, fun d hd => ?_⟩
  have hdN : N ≤ d := le_trans (le_max_left _ _) hd
  have hdN₀ : N₀ ≤ d := le_trans (le_max_right _ _) hd
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hdN (Nat.le_add_right d k))
    (fun k => le_trans hdN (Nat.le_add_right d _))
  have hb0 := realize_deEqAtom L J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_deEqAtom_superset L J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact hbS.mp (hiff.mp (hb0.mpr (hN₀ d hdN₀)))

/-- **Support-enlargement *iff*** (the symmetric core): on the deep tail the deep equality over the
combined support `S₀` is *equivalent* to the deep equality over any larger support `S ⊇ S₀`. This
gives both directions — descending from a larger support back to `S₀` is what `EMEq.trans` needs (it
works over the union of three supports and must return to the `(t,v)`-support). -/
theorem eventually_deepInterp_superset_iff
    {Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)}
    (hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ)
    {t u : (skolemColim L)[[J]].Term Empty}
    (hmem : (⟨(jSupport L J t ∪ jSupport L J u).card,
        deEqAtom L J (jSupport L J t ∪ jSupport L J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : jSupport L J t ∪ jSupport L J u ⊆ S) :
    ∀ᶠ d in Filter.atTop,
      (deepInterp L J a d (jSupport L J t ∪ jSupport L J u) t
            = deepInterp L J a d (jSupport L J t ∪ jSupport L J u) u ↔
          deepInterp L J a d S t = deepInterp L J a d S u) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := jSupport L J t ∪ jSupport L J u with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_deEqAtom L J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_deEqAtom_superset L J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

/-- **Relation support-independence** (the relation analogue of `eventually_deepInterp_superset_iff`):
on the deep tail, the truth of `R` on the deep interpretations over the combined support `S₀` of the
arguments is equivalent to its truth over any larger support `S ⊇ S₀`. This is what makes the
quotient `RelMap` independent of the chosen common support. -/
theorem eventually_relMap_superset_iff
    {Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)}
    (hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ)
    {l : ℕ} (R : (skolemColim L).Relations l) {ts : Fin l → (skolemColim L)[[J]].Term Empty}
    (hmem : (⟨(Finset.univ.biUnion fun i => jSupport L J (ts i)).card,
        deRelAtom L J (Finset.univ.biUnion fun i => jSupport L J (ts i)) R ts
          fun i => Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)⟩ :
        Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    ∀ᶠ d in Filter.atTop,
      (Structure.RelMap R
            (fun i => deepInterp L J a d (Finset.univ.biUnion fun i => jSupport L J (ts i)) (ts i)) ↔
        Structure.RelMap R (fun i => deepInterp L J a d S (ts i))) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := Finset.univ.biUnion fun i => jSupport L J (ts i) with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_deRelAtom L J a d S₀ R ts
    fun i => Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)
  have hbS := realize_deRelAtom_superset L J a d hS R ts
    fun i => Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

/-- The **EM term model carrier**: closed terms of `(skolemColim L)[[J]]` quotiented by eventual
deep equality. (`Quot`, so no equivalence proof is needed to form the carrier; transitivity enters
only when reasoning about the quotient, via support-enlargement invariance.) -/
def EMTermModel : Type := Quot (EMEq L J a)

/-- A closed term as an element of the EM term model. -/
def EMTermModel.mk (t : (skolemColim L)[[J]].Term Empty) : EMTermModel L J a := Quot.mk _ t

end DeepInterp

/-! ### Step 4D-4/5/6: the EM quotient and its structure

To avoid threading the indiscernible sequence, its tail-indiscernible family, and the atomic-diagram
membership through every congruence proof, we bundle them in an `EMContext`. Every quotient operation
then uses `EMEq_eventually_on_superset` (via the support-enlargement *iff*) as its standing congruence
engine. -/

section Quotient

variable {M : Type} [L.Structure M] [Nonempty M]

/-- The **standing data** for the EM quotient over a fixed source model `M`: a sequence `a` of deep
indiscernibles, a tail-indiscernible family `Γ`, and the fact that every de-substituted equality atom
lies in `Γ` (dischargeable since `L^Sk` is countable, so the whole atomic diagram seeds `Γ`). -/
structure EMContext where
  /-- The deep indiscernible sequence. -/
  a : ℕ → M
  /-- The tail-indiscernible formula family. -/
  Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)
  /-- Tail indiscernibility of `a` on `Γ`. -/
  hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ
  /-- Every de-substituted equality atom is in `Γ`. -/
  atom_mem : ∀ (S : Finset J) (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S),
    (⟨S.card, deEqAtom L J S t u ht hu⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ
  /-- Every de-substituted relation atom is in `Γ`. -/
  rel_mem : ∀ (S : Finset J) {l : ℕ} (R : (skolemColim L).Relations l)
    (ts : Fin l → (skolemColim L)[[J]].Term Empty) (ht : ∀ i, jSupport L J (ts i) ⊆ S),
    (⟨S.card, deRelAtom L J S R ts ht⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ

/-- **Transitivity of `EMEq`** (the congruence engine's first payoff): enlarge to the union of all
three supports, transport both hypotheses up to it via the enlargement *iff*, chain the equalities
in `M`, and descend back to the `(t,v)`-support. -/
theorem EMContext.trans (ctx : EMContext L J (M := M)) {t u v : (skolemColim L)[[J]].Term Empty}
    (h1 : EMEq L J ctx.a t u) (h2 : EMEq L J ctx.a u v) : EMEq L J ctx.a t v := by
  set S := jSupport L J t ∪ jSupport L J u ∪ jSupport L J v with hSdef
  have hsub_tu : jSupport L J t ∪ jSupport L J u ⊆ S := Finset.subset_union_left
  have hsub_uv : jSupport L J u ∪ jSupport L J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_right).trans Finset.subset_union_left) Finset.subset_union_right
  have hsub_tv : jSupport L J t ∪ jSupport L J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_left).trans Finset.subset_union_left) Finset.subset_union_right
  have iff_tu := eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ t u Finset.subset_union_left Finset.subset_union_right) hsub_tu
  have iff_uv := eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ u v Finset.subset_union_left Finset.subset_union_right) hsub_uv
  have iff_tv := eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ t v Finset.subset_union_left Finset.subset_union_right) hsub_tv
  have hS_tu := (h1.and iff_tu).mono (fun _ p => p.2.mp p.1)
  have hS_uv := (h2.and iff_uv).mono (fun _ p => p.2.mp p.1)
  have hS_tv := (hS_tu.and hS_uv).mono (fun _ p => p.1.trans p.2)
  exact (iff_tv.and hS_tv).mono (fun _ p => p.1.mpr p.2)

/-- **Function congruence**: if the arguments are pairwise `EMEq`, so are the function terms. Enlarge
every argument's deep equality up to the whole term's support, combine the finitely many eventual
equalities, and apply `deepInterp_func` (deep interpretation commutes with function application). -/
theorem EMContext.func_congr (ctx : EMContext L J (M := M)) {n : ℕ}
    (f : (skolemColim L)[[J]].Functions n) {ts ts' : Fin n → (skolemColim L)[[J]].Term Empty}
    (h : ∀ i, EMEq L J ctx.a (ts i) (ts' i)) :
    EMEq L J ctx.a (.func f ts) (.func f ts') := by
  unfold EMEq
  set S₀ := jSupport L J (.func f ts) ∪ jSupport L J (.func f ts') with hS₀
  have hi : ∀ i, ∀ᶠ d in Filter.atTop,
      deepInterp L J ctx.a d S₀ (ts i) = deepInterp L J ctx.a d S₀ (ts' i) := by
    intro i
    refine EMEq_eventually_on_superset L J ctx.a ctx.hind
      (ctx.atom_mem _ (ts i) (ts' i) Finset.subset_union_left Finset.subset_union_right) (h i) ?_
    exact Finset.union_subset
      ((jSupport_subterm L J f ts i).trans Finset.subset_union_left)
      ((jSupport_subterm L J f ts' i).trans Finset.subset_union_right)
  refine (Filter.eventually_all.mpr hi).mono (fun d hd => ?_)
  rw [deepInterp_func, deepInterp_func]
  congr 1
  funext i
  exact hd i

/-- `EMEq` is an equivalence relation on closed terms (refl/symm need no context; trans is
`EMContext.trans`). -/
def EMContext.setoid (ctx : EMContext L J (M := M)) : Setoid ((skolemColim L)[[J]].Term Empty) where
  r := EMEq L J ctx.a
  iseqv := ⟨fun t => EMEq.refl L J ctx.a t, fun h => EMEq.symm L J ctx.a h,
    fun h1 h2 => EMContext.trans (L := L) (J := J) ctx h1 h2⟩

/-- The **EM term model carrier** for a context: closed `(skolemColim L)[[J]]`-terms modulo `EMEq`. -/
def EMContext.Carrier (ctx : EMContext L J (M := M)) : Type :=
  Quotient ctx.setoid

/-- A closed term as an element of the carrier. -/
def EMContext.mkClass (ctx : EMContext L J (M := M)) (t : (skolemColim L)[[J]].Term Empty) :
    ctx.Carrier :=
  Quotient.mk ctx.setoid t

/-- A common support covering all argument representatives — the support over which a relation's deep
truth is read. -/
noncomputable def EMContext.commonSupport (ctx : EMContext L J (M := M)) {n : ℕ}
    (xs : Fin n → ctx.Carrier) : Finset J :=
  Finset.univ.biUnion fun i => jSupport L J (Quotient.out (xs i))

/-- The **EM term-model structure** on the carrier: function symbols act by term formation
`f([t̄]) := [func f t̄]` (skeleton constants `c_j` are the arity-0 case, giving the classes `[c_j]`),
and a relation holds iff it holds in `M` on the deep interpretations for all sufficiently deep `d`
(read over a common support of the arguments). Well-definedness is proved separately, via the
enlargement-invariance congruence engine. -/
noncomputable def EMContext.structure (ctx : EMContext L J (M := M)) :
    (skolemColim L)[[J]].Structure ctx.Carrier where
  funMap {_} f xs := Quotient.mk ctx.setoid (Term.func f fun i => Quotient.out (xs i))
  RelMap {n} R xs :=
    ∀ᶠ d in Filter.atTop,
      letI : (skolemColim L).Structure M := skolemColimStructure L
      letI : (constantsOn J).Structure M :=
        constantsOn.structure fun j => ctx.a (d + deepRank J (ctx.commonSupport (xs := xs)) j)
      @Structure.RelMap ((skolemColim L)[[J]]) M _ n R
        fun i => deepInterp L J ctx.a d (ctx.commonSupport (xs := xs)) (Quotient.out (xs i))

/-- **Function interpretation computes on classes** (well-definedness, API form): applying the
interpreted function symbol to a tuple of term-classes gives the class of the function term. Immediate
from `func_congr` and `Quotient.out_eq`. (The arity-0 case is `constMap_mkClass`: skeleton constants
`c_j` interpret as `[c_j]`.) -/
theorem EMContext.funMap_mkClass (ctx : EMContext L J (M := M)) {n : ℕ}
    (f : (skolemColim L)[[J]].Functions n) (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    @Structure.funMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure n f
        (fun i => ctx.mkClass (t := ts i)) = ctx.mkClass (t := .func f ts) := by
  apply Quotient.sound
  apply ctx.func_congr
  exact fun i => Quotient.exact (Quotient.out_eq (ctx.mkClass (t := ts i)))

/-- The arity-0 case: a skeleton constant `c_j` (or any `L^Sk`-constant) interprets as the class of
its constant term. -/
theorem EMContext.constMap_mkClass (ctx : EMContext L J (M := M))
    (c : (skolemColim L)[[J]].Functions 0) :
    @Structure.funMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure 0 c Fin.elim0
      = ctx.mkClass (t := .func c Fin.elim0) := by
  apply Quotient.sound
  apply ctx.func_congr
  exact fun i => i.elim0

/-- **Relation congruence on terms** (helper): changing a finite tuple of argument terms by `EMEq`,
all over a fixed covering support `T`, preserves the eventual deep truth of a relation. Combines the
per-term equality invariance over `T` (`EMEq_eventually_on_superset`) with `Filter.eventually_all`. -/
theorem EMContext.eventually_relMap_congr_terms (ctx : EMContext L J (M := M)) {l : ℕ}
    (R : (skolemColim L).Relations l) {ts ts' : Fin l → (skolemColim L)[[J]].Term Empty}
    (h : ∀ i, EMEq L J ctx.a (ts i) (ts' i)) {T : Finset J}
    (hts : ∀ i, jSupport L J (ts i) ⊆ T) (hts' : ∀ i, jSupport L J (ts' i) ⊆ T) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (∀ᶠ d in Filter.atTop, Structure.RelMap R fun i => deepInterp L J ctx.a d T (ts i)) ↔
      (∀ᶠ d in Filter.atTop, Structure.RelMap R fun i => deepInterp L J ctx.a d T (ts' i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  have hcong : ∀ᶠ d in Filter.atTop, ∀ i,
      deepInterp L J ctx.a d T (ts i) = deepInterp L J ctx.a d T (ts' i) :=
    Filter.eventually_all.mpr fun i =>
      EMEq_eventually_on_superset L J ctx.a ctx.hind
        (ctx.atom_mem _ (ts i) (ts' i) Finset.subset_union_left Finset.subset_union_right) (h i)
        (Finset.union_subset (hts i) (hts' i))
  exact Filter.eventually_congr (hcong.mono fun _ hd => Iff.of_eq (congrArg _ (funext hd)))

/-- **Relation interpretation computes on classes** (well-definedness, API form): the interpreted
relation holds on a tuple of term-classes iff it holds in `M` on the deep interpretations for all
sufficiently deep `d`, over *any* support `S` covering the arguments — independent of the quotient
representatives and of the chosen support. The relation analogue of `funMap_mkClass`, by
support-normalization through a bridge support `T = S ∪ Sout`. -/
theorem EMContext.relMap_mkClass_iff (ctx : EMContext L J (M := M)) {l : ℕ}
    (R : (skolemColim L).Relations l) (ts : Fin l → (skolemColim L)[[J]].Term Empty)
    {S : Finset J} (hS : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S) :
    @Structure.RelMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure l (Sum.inl R)
        (fun i => ctx.mkClass (t := ts i)) ↔
      letI : (skolemColim L).Structure M := skolemColimStructure L
      ∀ᶠ d in Filter.atTop, Structure.RelMap R fun i => deepInterp L J ctx.a d S (ts i) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  show (∀ᶠ d in Filter.atTop, Structure.RelMap R fun i =>
        deepInterp L J ctx.a d
          (Finset.univ.biUnion fun i => jSupport L J (Quotient.out (ctx.mkClass (t := ts i))))
          (Quotient.out (ctx.mkClass (t := ts i)))) ↔ _
  set rep : Fin l → (skolemColim L)[[J]].Term Empty :=
    fun i => Quotient.out (ctx.mkClass (t := ts i)) with hrep
  set Sout : Finset J := Finset.univ.biUnion fun i => jSupport L J (rep i) with hSout
  set T : Finset J := S ∪ Sout with hT
  have hrep_eq : ∀ i, EMEq L J ctx.a (rep i) (ts i) :=
    fun i => Quotient.exact (Quotient.out_eq (ctx.mkClass (t := ts i)))
  have hSout_T : Sout ⊆ T := Finset.subset_union_right
  have hS_T : S ⊆ T := Finset.subset_union_left
  have hrep_T : ∀ i, jSupport L J (rep i) ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => jSupport L J (rep i)) (Finset.mem_univ i)).trans hSout_T
  have hts_S : ∀ i, jSupport L J (ts i) ⊆ S := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)).trans hS
  have hts_T : ∀ i, jSupport L J (ts i) ⊆ T := fun i => (hts_S i).trans hS_T
  -- (a) move the rep-side from Sout up to T
  have ha := Filter.eventually_congr (eventually_relMap_superset_iff L J ctx.a ctx.hind R (ts := rep)
    (ctx.rel_mem _ R rep fun i =>
      Finset.subset_biUnion_of_mem (fun i => jSupport L J (rep i)) (Finset.mem_univ i)) hSout_T)
  -- (b) swap reps for ts over T
  have hb := EMContext.eventually_relMap_congr_terms (L := L) (J := J) ctx R hrep_eq hrep_T hts_T
  -- (c) relate the ts-side over T and over S (both to the canonical S₀(ts))
  have hcT := Filter.eventually_congr (eventually_relMap_superset_iff L J ctx.a ctx.hind R (ts := ts)
    (ctx.rel_mem _ R ts fun i =>
      Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)) (hS.trans hS_T))
  have hcS := Filter.eventually_congr (eventually_relMap_superset_iff L J ctx.a ctx.hind R (ts := ts)
    (ctx.rel_mem _ R ts fun i =>
      Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)) hS)
  exact ha.trans (hb.trans (hcT.symm.trans hcS))

/-! ### Step 4D-7: the Γ*-restricted truth-lemma RHS

The Γ*-restricted truth lemma will state that realizing a (base-language) formula `φ` in the EM term
model on a tuple of term-classes is equivalent to `φ`'s **eventual deep truth**: `φ` holds in the
source model `M` on the deep interpretations of the argument terms, for all sufficiently deep `d`.
That predicate is named here (not inlined through the induction); `φ` ranges over `skolemColim L`
(the family `Γ*` carries no `J`-constants — those enter only through the argument terms `ts`). -/

/-- **Eventual deep truth** of a base-language formula `φ` on a tuple of closed argument terms over a
support `S`: `φ` holds in `M` (in its `L^Sk`-structure) on the deep interpretations of the terms, for
all sufficiently deep `d`. The right-hand side of the Γ*-truth lemma. -/
def EMContext.eventualDeepTruth (ctx : EMContext L J (M := M)) {n : ℕ}
    (φ : (skolemColim L).BoundedFormulaω Empty n) (ts : Fin n → (skolemColim L)[[J]].Term Empty)
    (S : Finset J) : Prop :=
  letI : (skolemColim L).Structure M := skolemColimStructure L
  ∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i)

/-- The **base `L^Sk`-structure** on the carrier: the reduct of the term-model `[[J]]`-structure along
the skeleton-constant inclusion (a base function/relation symbol acts as its `Sum.inl` image). -/
noncomputable def EMContext.structureBase (ctx : EMContext L J (M := M)) :
    (skolemColim L).Structure ctx.Carrier where
  funMap {n} f xs := @Structure.funMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure n (Sum.inl f) xs
  RelMap {n} R xs := @Structure.RelMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure n (Sum.inl R) xs

/-- **Map-language plumbing**: the skeleton-constant inclusion `skolemColim L → (skolemColim L)[[J]]`
is an expansion of the carrier's base structure to its term-model `[[J]]`-structure (definitional, as
the `[[J]]`-structure interprets `Sum.inl` symbols by the base reduct). Lets `realize_mapLanguage`
transfer realizations of base-language formulas. Mirrors `skolemStageInclusion_isExpansionOn`. -/
theorem EMContext.lhomWithConstants_isExpansionOn (ctx : EMContext L J (M := M)) :
    @LHom.IsExpansionOn (skolemColim L) ((skolemColim L)[[J]])
      (lhomWithConstants (skolemColim L) J) ctx.Carrier ctx.structureBase ctx.structure := by
  letI : (skolemColim L).Structure ctx.Carrier := ctx.structureBase
  letI : (skolemColim L)[[J]].Structure ctx.Carrier := ctx.structure
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Carrier-side term substitution**: realizing a term in the EM term model under the assignment
`Sum.elim Empty.elim (mkClass ∘ ts)` gives the class of the substituted closed term. By induction on
the term, using `funMap_mkClass`. -/
theorem EMContext.realize_term_mkClass (ctx : EMContext L J (M := M)) {n : ℕ}
    (ts : Fin n → (skolemColim L)[[J]].Term Empty)
    (t : (skolemColim L)[[J]].Term (Empty ⊕ Fin n)) :
    @Term.realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure (Empty ⊕ Fin n)
        (Sum.elim Empty.elim fun i => ctx.mkClass (t := ts i)) t
      = ctx.mkClass (t := t.subst (Sum.elim (fun e => e.elim) ts)) := by
  induction t with
  | var x => cases x with
    | inl e => exact e.elim
    | inr i => rfl
  | func f args ih =>
    have hargs : (fun j => @Term.realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure _
          (Sum.elim Empty.elim fun i => ctx.mkClass (t := ts i)) (args j))
        = (fun j => ctx.mkClass (t := (args j).subst (Sum.elim (fun e => e.elim) ts))) := funext ih
    show @Structure.funMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure _ f _ = _
    rw [hargs, ctx.funMap_mkClass]
    rfl

/-- **Truth lemma, equality-atom case**: realizing a base-language equality atom in the EM term model
on a tuple of term-classes is equivalent to its eventual deep truth. Carrier side via
`realize_term_mkClass`; quotient side via `Quotient.eq`; deep side via
`eventually_deepInterp_superset_iff` and `deepInterp_onTerm_subst`. -/
theorem EMContext.eventualDeepTruth_equal_iff (ctx : EMContext L J (M := M)) {n : ℕ}
    (t₁ t₂ : (skolemColim L).Term (Empty ⊕ Fin n))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) {S : Finset J}
    (hS : jSupport L J (((lhomWithConstants (skolemColim L) J).onTerm t₁).subst
            (Sum.elim (fun e => e.elim) ts))
          ∪ jSupport L J (((lhomWithConstants (skolemColim L) J).onTerm t₂).subst
            (Sum.elim (fun e => e.elim) ts)) ⊆ S) :
    @BoundedFormulaω.Realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.equal t₁ t₂).mapLanguage (lhomWithConstants (skolemColim L) J))
        Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
      EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.equal t₁ t₂) ts S := by
  have hcarrier : @BoundedFormulaω.Realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.equal t₁ t₂).mapLanguage (lhomWithConstants (skolemColim L) J))
        Empty.elim (fun i => ctx.mkClass (t := ts i))
      ↔ ctx.mkClass (t := ((lhomWithConstants (skolemColim L) J).onTerm t₁).subst
            (Sum.elim (fun e => e.elim) ts))
        = ctx.mkClass (t := ((lhomWithConstants (skolemColim L) J).onTerm t₂).subst
            (Sum.elim (fun e => e.elim) ts)) := by
    letI : (skolemColim L)[[J]].Structure ctx.Carrier := ctx.structure
    rw [show (BoundedFormulaω.equal t₁ t₂).mapLanguage (lhomWithConstants (skolemColim L) J)
        = BoundedFormulaω.equal ((lhomWithConstants (skolemColim L) J).onTerm t₁)
            ((lhomWithConstants (skolemColim L) J).onTerm t₂) from rfl,
      BoundedFormulaω.realize_equal, EMContext.realize_term_mkClass (L := L) (J := J) ctx ts,
      EMContext.realize_term_mkClass (L := L) (J := J) ctx ts]
  have hcommon : EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.equal t₁ t₂) ts S ↔
      (∀ᶠ d in Filter.atTop,
        letI : (skolemColim L).Structure M := skolemColimStructure L
        deepInterp L J ctx.a d S (((lhomWithConstants (skolemColim L) J).onTerm t₁).subst
            (Sum.elim (fun e => e.elim) ts))
          = deepInterp L J ctx.a d S (((lhomWithConstants (skolemColim L) J).onTerm t₂).subst
            (Sum.elim (fun e => e.elim) ts))) := by
    letI : (skolemColim L).Structure M := skolemColimStructure L
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun d => ?_)
    rw [BoundedFormulaω.realize_equal, ← deepInterp_onTerm_subst, ← deepInterp_onTerm_subst]
  rw [hcarrier, hcommon]
  show Quotient.mk ctx.setoid _ = Quotient.mk ctx.setoid _ ↔ _
  rw [Quotient.eq]
  show EMEq L J ctx.a _ _ ↔ _
  unfold EMEq
  exact Filter.eventually_congr (eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ _ _ Finset.subset_union_left Finset.subset_union_right) hS)

/-- **Truth lemma, relation-atom case**: realizing a base-language relation atom in the EM term model
on a tuple of term-classes is equivalent to its eventual deep truth. Carrier side via
`realize_term_mkClass`; then `relMap_mkClass_iff`; deep side via `deepInterp_onTerm_subst`. -/
theorem EMContext.eventualDeepTruth_rel_iff (ctx : EMContext L J (M := M)) {n l : ℕ}
    (R : (skolemColim L).Relations l) (args : Fin l → (skolemColim L).Term (Empty ⊕ Fin n))
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) {S : Finset J}
    (hS : (Finset.univ.biUnion fun i => jSupport L J
            (((lhomWithConstants (skolemColim L) J).onTerm (args i)).subst
              (Sum.elim (fun e => e.elim) ts))) ⊆ S) :
    @BoundedFormulaω.Realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.rel R args).mapLanguage (lhomWithConstants (skolemColim L) J))
        Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
      EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.rel R args) ts S := by
  have hcarrier : @BoundedFormulaω.Realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.rel R args).mapLanguage (lhomWithConstants (skolemColim L) J))
        Empty.elim (fun i => ctx.mkClass (t := ts i))
      ↔ @Structure.RelMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure l (Sum.inl R)
          (fun i => ctx.mkClass (t := ((lhomWithConstants (skolemColim L) J).onTerm (args i)).subst
            (Sum.elim (fun e => e.elim) ts))) := by
    letI : (skolemColim L)[[J]].Structure ctx.Carrier := ctx.structure
    rw [show (BoundedFormulaω.rel R args).mapLanguage (lhomWithConstants (skolemColim L) J)
        = BoundedFormulaω.rel (Sum.inl R)
            (fun i => (lhomWithConstants (skolemColim L) J).onTerm (args i)) from rfl,
      BoundedFormulaω.realize_rel]
    apply Iff.of_eq
    congr 1
    funext i
    exact EMContext.realize_term_mkClass (L := L) (J := J) ctx ts _
  have hcommon : EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.rel R args) ts S ↔
      (∀ᶠ d in Filter.atTop,
        letI : (skolemColim L).Structure M := skolemColimStructure L
        Structure.RelMap R fun i => deepInterp L J ctx.a d S
          (((lhomWithConstants (skolemColim L) J).onTerm (args i)).subst
            (Sum.elim (fun e => e.elim) ts))) := by
    letI : (skolemColim L).Structure M := skolemColimStructure L
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun d => ?_)
    rw [BoundedFormulaω.realize_rel]
    apply Iff.of_eq
    congr 1
    funext i
    exact (deepInterp_onTerm_subst L J ctx.a d S (args i) ts).symm
  rw [hcarrier, hcommon]
  exact EMContext.relMap_mkClass_iff (L := L) (J := J) ctx R
    (fun i => ((lhomWithConstants (skolemColim L) J).onTerm (args i)).subst
      (Sum.elim (fun e => e.elim) ts)) hS

/-- **0-1 law for eventual deep truth** (the unlock for the truth lemma's `imp`/connective cases): if
the de-substituted formula `deForm S φ ts` lies in the tail-indiscernible family `Γ`, then `φ`'s
eventual deep truth is *decided* — either `φ` holds on the deep interpretations for all sufficiently
deep `d`, or it fails for all sufficiently deep `d`. The value is eventually constant because tail
indiscernibility makes all sufficiently-deep consecutive tuples agree on the single arity-`S.card`
formula `deForm S φ ts`. -/
theorem EMContext.eventualDeepTruth_decided (ctx : EMContext L J (M := M)) {n : ℕ}
    (φ : (skolemColim L).BoundedFormulaω Empty n)
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (S : Finset J)
    (hsub : ∀ i, jSupport L J (ts i) ⊆ S)
    (hmem : (⟨S.card, deForm L J S φ ts hsub⟩ :
        Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ ctx.Γ) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i)) ∨
      (∀ᶠ d in Filter.atTop, ¬ φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  obtain ⟨N, hN⟩ := ctx.hind hmem
  have hmono : ∀ d : ℕ, StrictMono (fun i : Fin S.card => d + (i : ℕ)) :=
    fun d _ _ hii' => Nat.add_lt_add_left hii' d
  by_cases hbase :
      (deForm L J S φ ts hsub).Realize Empty.elim (fun i : Fin S.card => ctx.a (N + (i : ℕ)))
  · refine Or.inl (Filter.eventually_atTop.mpr ⟨N, fun d hd => ?_⟩)
    rw [← realize_deForm L J ctx.a d S φ ts hsub]
    exact (hN (fun i => d + (i : ℕ)) (fun i => N + (i : ℕ)) (hmono d) (hmono N)
      (fun k => le_trans hd (Nat.le_add_right d k)) (fun k => Nat.le_add_right N k)).mpr hbase
  · refine Or.inr (Filter.eventually_atTop.mpr ⟨N, fun d hd hPd => hbase ?_⟩)
    rw [← realize_deForm L J ctx.a d S φ ts hsub] at hPd
    exact (hN (fun i => N + (i : ℕ)) (fun i => d + (i : ℕ)) (hmono N) (hmono d)
      (fun k => Nat.le_add_right N k) (fun k => le_trans hd (Nat.le_add_right d k))).mpr hPd

/-- An eventual implication splits as an implication of eventuals exactly when the antecedent's
eventual truth is *decided*. The Filter fact behind the truth lemma's `imp` case — note only the
antecedent's decidedness is needed (the consequent's plays no role). -/
theorem eventually_imp_iff_imp_eventually {α : Type*} {f : Filter α} {P Q : α → Prop}
    (hP : (∀ᶠ x in f, P x) ∨ (∀ᶠ x in f, ¬ P x)) :
    (∀ᶠ x in f, P x → Q x) ↔ ((∀ᶠ x in f, P x) → (∀ᶠ x in f, Q x)) := by
  constructor
  · intro h hP'
    exact (h.and hP').mono fun _ p => p.1 p.2
  · intro h
    rcases hP with hP | hP
    · exact (h hP).mono fun _ hQ _ => hQ
    · exact hP.mono fun _ hnp hp => absurd hp hnp

/-- **Truth lemma, falsum case** (eventual-deep-truth side): `falsum` has no eventual deep truth.
Immediate from `Filter.eventually_const` (`atTop` on `ℕ` is `NeBot`). -/
theorem EMContext.eventualDeepTruth_falsum_iff (ctx : EMContext L J (M := M)) {n : ℕ}
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (S : Finset J) :
    EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.falsum) ts S ↔ False := by
  simp only [EMContext.eventualDeepTruth, BoundedFormulaω.realize_falsum]
  exact Filter.eventually_const

/-- **Truth lemma, imp case** (eventual-deep-truth side): the eventual deep truth of `φ ⟹ ψ` is the
implication of their eventual deep truths, *provided* `φ`'s eventual deep truth is decided (supplied
by `eventualDeepTruth_decided`). Combined with the carrier-side `realize_imp` and the inductive
hypotheses, this is the `imp` step of the truth lemma. -/
theorem EMContext.eventualDeepTruth_imp_iff (ctx : EMContext L J (M := M)) {n : ℕ}
    (φ ψ : (skolemColim L).BoundedFormulaω Empty n)
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (S : Finset J)
    (hdec :
      letI : (skolemColim L).Structure M := skolemColimStructure L
      (∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i)) ∨
        (∀ᶠ d in Filter.atTop, ¬ φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i))) :
    EMContext.eventualDeepTruth (L := L) (J := J) ctx (φ.imp ψ) ts S ↔
      (EMContext.eventualDeepTruth (L := L) (J := J) ctx φ ts S →
        EMContext.eventualDeepTruth (L := L) (J := J) ctx ψ ts S) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  simp only [EMContext.eventualDeepTruth, BoundedFormulaω.realize_imp]
  exact eventually_imp_iff_imp_eventually hdec

/-! ### Step 4D-7: the `⋁`/`⋀`-completeness mixin and the Γ*-restricted truth lemma

The countable connectives need more than tail indiscernibility: the truth lemma's `iSup` case asks for
a *uniform witness* (`∀ᶠ d, ∃i Pᵢ d → ∃i ∀ᶠ d, Pᵢ d`) and the `iInf` case for a *uniform cutoff*
(`∀i ∀ᶠ d, Pᵢ d → ∀ᶠ d, ∀i Pᵢ d`). Since `atTop` on `ℕ` is not countably complete, neither follows
from `IsLomega1omegaIndiscernibleOnTail` + decidedness. They are the infinitary analogue of the
consistency-property `C3`/`C4` rules for `⋁`/`⋀`, packaged here as a **separate `Prop` mixin** over
`EMContext` (not core fields, so the quotient/congruence/atom API is untouched). The truth lemma takes
`hc : ctx.OmegaComplete`; producing such a context (from a witness-homogeneous extraction) is later
work. -/

/-- **`⋁`/`⋀`-completeness of an `EMContext`'s eventual deep truth**: the genuinely non-formal residual
for the countable connectives — a uniform `iSup`-witness and a uniform `iInf`-cutoff. -/
structure EMContext.OmegaComplete (ctx : EMContext L J (M := M)) : Prop where
  /-- Eventual deep truth of `⋁φs` provides a single component witness. -/
  iSup_complete : ∀ {m : ℕ} (φs : ℕ → (skolemColim L).BoundedFormulaω Empty m)
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J),
    EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.iSup φs) ts S →
      ∃ i, EMContext.eventualDeepTruth (L := L) (J := J) ctx (φs i) ts S
  /-- Eventual deep truth of all components provides eventual deep truth of `⋀φs`. -/
  iInf_complete : ∀ {m : ℕ} (φs : ℕ → (skolemColim L).BoundedFormulaω Empty m)
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J),
    (∀ i, EMContext.eventualDeepTruth (L := L) (J := J) ctx (φs i) ts S) →
      EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.iInf φs) ts S

/-- The easy `iSup` direction: a single component's eventual deep truth gives the disjunction's. -/
theorem EMContext.eventualDeepTruth_iSup_of_exists (ctx : EMContext L J (M := M)) {m : ℕ}
    (φs : ℕ → (skolemColim L).BoundedFormulaω Empty m)
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J)
    (h : ∃ i, EMContext.eventualDeepTruth (L := L) (J := J) ctx (φs i) ts S) :
    EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.iSup φs) ts S := by
  obtain ⟨i, hi⟩ := h
  simp only [EMContext.eventualDeepTruth, BoundedFormulaω.realize_iSup] at hi ⊢
  exact hi.mono fun _ hd => ⟨i, hd⟩

/-- The easy `iInf` direction: the conjunction's eventual deep truth gives every component's. -/
theorem EMContext.eventualDeepTruth_iInf_forall (ctx : EMContext L J (M := M)) {m : ℕ}
    (φs : ℕ → (skolemColim L).BoundedFormulaω Empty m)
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J)
    (h : EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.iInf φs) ts S) (i : ℕ) :
    EMContext.eventualDeepTruth (L := L) (J := J) ctx (φs i) ts S := by
  simp only [EMContext.eventualDeepTruth, BoundedFormulaω.realize_iInf] at h ⊢
  exact h.mono fun _ hd => hd i

/-- **Decidedness of a formula's eventual deep truth** (the named output of
`eventualDeepTruth_decided`): either it holds eventually, or it fails eventually. -/
def EMContext.Decided (ctx : EMContext L J (M := M)) {m : ℕ}
    (φ : (skolemColim L).BoundedFormulaω Empty m)
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J) : Prop :=
  letI : (skolemColim L).Structure M := skolemColimStructure L
  (∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i)) ∨
    (∀ᶠ d in Filter.atTop, ¬ φ.Realize Empty.elim fun i => deepInterp L J ctx.a d S (ts i))

/-- **Truth-lemma readiness** of a formula on `ts`/`S`: the closure data the Γ*-truth-lemma induction
consumes — decidedness at every `imp`-antecedent (for `eventualDeepTruth_imp_iff`), recursively down
the connectives. The `all φ` case requires the **body** `φ` to be ready at every one-point extension
`Fin.snoc ts u` (the carrier's `∀x` ranges over all term-classes `mkClass u` via `Quotient.ind`), so
the `all` case recurses on the structural subformula `φ` — no skolem-witness recursion is needed here.
Discharged later from the Γ* deForm-closure via `eventualDeepTruth_decided`. -/
def EMContext.TLReady (ctx : EMContext L J (M := M)) :
    ∀ {m : ℕ}, (skolemColim L).BoundedFormulaω Empty m →
      (Fin m → (skolemColim L)[[J]].Term Empty) → Finset J → Prop
  | _, .falsum, _, _ => True
  | _, .equal _ _, _, _ => True
  | _, .rel _ _, _, _ => True
  | _, .imp φ ψ, ts, S =>
      EMContext.Decided (L := L) (J := J) ctx φ ts S ∧
        EMContext.TLReady ctx φ ts S ∧ EMContext.TLReady ctx ψ ts S
  | _, .iSup φs, ts, S => ∀ i, EMContext.TLReady ctx (φs i) ts S
  | _, .iInf φs, ts, S => ∀ i, EMContext.TLReady ctx (φs i) ts S
  | _, .all φ, ts, S =>
      ∀ u : (skolemColim L)[[J]].Term Empty,
        EMContext.TLReady ctx φ (Fin.snoc ts u) (S ∪ jSupport L J u)

/-- Forming classes commutes with `Fin.snoc`: the carrier tuple obtained by snocing `mkClass u` onto
`mkClass ∘ ts` is `mkClass ∘ (Fin.snoc ts u)`. The bridge between the carrier-side `∀x` (over
term-classes) and the term-side `Fin.snoc ts u` in the `all` case. -/
theorem EMContext.mkClass_snoc (ctx : EMContext L J (M := M)) {m : ℕ}
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (u : (skolemColim L)[[J]].Term Empty) :
    Fin.snoc (fun i => ctx.mkClass (t := ts i)) (ctx.mkClass (t := u))
      = fun i => ctx.mkClass
          (t := (Fin.snoc ts u : Fin (m + 1) → (skolemColim L)[[J]].Term Empty) i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-- **The exact `all`-case Skolem obligation** (stated, proved in a later chunk against the colimit
machinery): the eventual deep truth of `∀ φ` over `S` is the conjunction over *all* closed argument
terms `u` of the eventual deep truth of the body at `Fin.snoc ts u`. The `→` direction is universal
instantiation (`x := deep u`); the hard `←` picks `u` to be the Skolem witness term of `¬φ` (whence
`qrank_skolemWitnessFormula_lt`) and uses `M`'s Skolem axiom — that proof needs the stage/colimit
transport and is deferred. With it, the truth lemma's `all` case is `Quotient.ind` + the body's IH. -/
def EMContext.SkolemSemantic (ctx : EMContext L J (M := M)) : Prop :=
  ∀ {m : ℕ} (φ : (skolemColim L).BoundedFormulaω Empty (m + 1))
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J),
    (∀ i, jSupport L J (ts i) ⊆ S) →
    (EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.all φ) ts S ↔
      ∀ u : (skolemColim L)[[J]].Term Empty,
        EMContext.eventualDeepTruth (L := L) (J := J) ctx φ (Fin.snoc ts u) (S ∪ jSupport L J u))

/-- **Pure-Skolem `all`-self-support lemma** (the genuinely-new `all`-case content, isolated from the
support-enlargement bookkeeping): given a witness term `w` whose deep interpretation is a Skolem
counterexample for `¬φ` at every depth (`hw`: if `φ` holds at `w`'s deep value then it holds at *every*
`M`-element — the contrapositive Skolem axiom), the eventual deep truth of `∀ φ` over `S` equals the
universal-over-terms statement at the **same** support `S`. The `→` is universal instantiation; the
`←` plugs in `u := w` and applies `hw` pointwise. No support invariance is used (the witness `w` will
have support `⊆ S`); constructing `w`/`hw` via the Skolem-axiom colimit transport is the WF refactor's
job. -/
theorem EMContext.eventualDeepTruth_all_support_self_of_skolem (ctx : EMContext L J (M := M)) {m : ℕ}
    (φ : (skolemColim L).BoundedFormulaω Empty (m + 1))
    (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J)
    (w : (skolemColim L)[[J]].Term Empty)
    (hw : letI : (skolemColim L).Structure M := skolemColimStructure L
      ∀ d : ℕ, φ.Realize Empty.elim (Fin.snoc (fun i => deepInterp L J ctx.a d S (ts i))
              (deepInterp L J ctx.a d S w)) →
            ∀ x : M, φ.Realize Empty.elim (Fin.snoc (fun i => deepInterp L J ctx.a d S (ts i)) x)) :
    EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.all φ) ts S ↔
      ∀ u : (skolemColim L)[[J]].Term Empty,
        EMContext.eventualDeepTruth (L := L) (J := J) ctx φ (Fin.snoc ts u) S := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  simp only [EMContext.eventualDeepTruth, BoundedFormulaω.realize_all, deepInterp_snoc]
  constructor
  · intro h u
    exact h.mono fun d hd => hd (deepInterp L J ctx.a d S u)
  · intro h
    exact (h w).mono fun d hd => hw d hd

/-- **The Γ*-restricted truth lemma**, conditional on `⋁`/`⋀`-completeness `hc` and the `all`-case
Skolem obligation `hsk : ctx.SkolemSemantic`. For a base-language formula `φ` realized in the EM term
model on a tuple of term-classes `mkClass ∘ ts` (over a covering support `S`), realization is equivalent
to `φ`'s **eventual deep truth** in the source model. Atoms use `eventualDeepTruth_equal_iff`/`_rel_iff`
(support bridged by `jSupport_onTerm_subst_subset`); `imp` uses antecedent decidedness from `TLReady`;
`iSup`/`iInf` use `hc`'s uniform witness/cutoff; `all` uses `Quotient.ind` + the body's IH + `hsk`. The
induction is structural — the `all` case needs only the body `φ` (a subformula), not the (non-subformula)
skolem-witness formula; the Skolem content is isolated in `hsk` (proved separately). -/
theorem EMContext.truthLemma (ctx : EMContext L J (M := M)) (hc : ctx.OmegaComplete)
    (hsk : ctx.SkolemSemantic) :
    ∀ {m : ℕ} (φ : (skolemColim L).BoundedFormulaω Empty m)
      (ts : Fin m → (skolemColim L)[[J]].Term Empty) (S : Finset J),
      (∀ i, jSupport L J (ts i) ⊆ S) → EMContext.TLReady (L := L) (J := J) ctx φ ts S →
      (@BoundedFormulaω.Realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure Empty m
          (φ.mapLanguage (lhomWithConstants (skolemColim L) J))
          Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
        EMContext.eventualDeepTruth (L := L) (J := J) ctx φ ts S) := by
  letI : (skolemColim L)[[J]].Structure ctx.Carrier := ctx.structure
  intro m φ
  induction φ with
  | falsum =>
    intro ts S _ _
    simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.realize_falsum,
      EMContext.eventualDeepTruth_falsum_iff]
  | equal t₁ t₂ =>
    intro ts S hsub _
    have hbi : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S :=
      Finset.biUnion_subset.mpr fun i _ => hsub i
    exact EMContext.eventualDeepTruth_equal_iff (L := L) (J := J) ctx t₁ t₂ ts
      (Finset.union_subset ((jSupport_onTerm_subst_subset L J t₁ ts).trans hbi)
        ((jSupport_onTerm_subst_subset L J t₂ ts).trans hbi))
  | rel R args =>
    intro ts S hsub _
    have hbi : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S :=
      Finset.biUnion_subset.mpr fun i _ => hsub i
    exact EMContext.eventualDeepTruth_rel_iff (L := L) (J := J) ctx R args ts
      (Finset.biUnion_subset.mpr fun i _ => (jSupport_onTerm_subst_subset L J (args i) ts).trans hbi)
  | imp φ ψ ihφ ihψ =>
    intro ts S hsub hready
    obtain ⟨hdec, hrφ, hrψ⟩ := hready
    rw [EMContext.eventualDeepTruth_imp_iff (L := L) (J := J) ctx φ ψ ts S hdec]
    simp only [BoundedFormulaω.mapLanguage_imp, BoundedFormulaω.realize_imp]
    exact imp_congr (ihφ ts S hsub hrφ) (ihψ ts S hsub hrψ)
  | all φ ih =>
    intro ts S hsub hready
    have hsub_u : ∀ (u : (skolemColim L)[[J]].Term Empty) (i : Fin _),
        jSupport L J ((Fin.snoc ts u : Fin _ → (skolemColim L)[[J]].Term Empty) i)
          ⊆ S ∪ jSupport L J u := by
      intro u i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact Finset.subset_union_right
      · rw [Fin.snoc_castSucc]; exact (hsub j).trans Finset.subset_union_left
    rw [hsk φ ts S hsub,
      show (BoundedFormulaω.all φ).mapLanguage (lhomWithConstants (skolemColim L) J)
          = BoundedFormulaω.all (φ.mapLanguage (lhomWithConstants (skolemColim L) J)) from rfl,
      BoundedFormulaω.realize_all]
    constructor
    · intro h u
      rw [← ih (Fin.snoc ts u) (S ∪ jSupport L J u) (hsub_u u) (hready u)]
      have hx := h (ctx.mkClass (t := u))
      rwa [EMContext.mkClass_snoc (L := L) (J := J) ctx ts u] at hx
    · intro h
      refine Quotient.ind (fun u => ?_)
      show (φ.mapLanguage (lhomWithConstants (skolemColim L) J)).Realize Empty.elim
          (Fin.snoc (fun i => ctx.mkClass (t := ts i)) (ctx.mkClass (t := u)))
      rw [EMContext.mkClass_snoc (L := L) (J := J) ctx ts u, ih (Fin.snoc ts u) (S ∪ jSupport L J u) (hsub_u u) (hready u)]
      exact h u
  | iSup φs ih =>
    intro ts S hsub hready
    rw [show (BoundedFormulaω.iSup φs).mapLanguage (lhomWithConstants (skolemColim L) J)
          = BoundedFormulaω.iSup
              (fun i => (φs i).mapLanguage (lhomWithConstants (skolemColim L) J)) from rfl,
      BoundedFormulaω.realize_iSup]
    constructor
    · rintro ⟨i, hi⟩
      exact EMContext.eventualDeepTruth_iSup_of_exists (L := L) (J := J) ctx φs ts S
        ⟨i, (ih i ts S hsub (hready i)).mp hi⟩
    · intro h
      obtain ⟨i, hi⟩ := hc.iSup_complete φs ts S h
      exact ⟨i, (ih i ts S hsub (hready i)).mpr hi⟩
  | iInf φs ih =>
    intro ts S hsub hready
    rw [show (BoundedFormulaω.iInf φs).mapLanguage (lhomWithConstants (skolemColim L) J)
          = BoundedFormulaω.iInf
              (fun i => (φs i).mapLanguage (lhomWithConstants (skolemColim L) J)) from rfl,
      BoundedFormulaω.realize_iInf]
    constructor
    · intro h
      exact hc.iInf_complete φs ts S fun i => (ih i ts S hsub (hready i)).mp (h i)
    · intro h i
      exact (ih i ts S hsub (hready i)).mpr
        (EMContext.eventualDeepTruth_iInf_forall (L := L) (J := J) ctx φs ts S h i)

/-- **Staged truth-lemma readiness** (support-*uniform*): the colimit `TLReady` of the staged formula's
image under `skolemStageInclusion k` holds at *every* enlarged support `T ⊇ S`. The uniformity is what
the `all` case needs — it reads the body's readiness at `S ∪ jSupport u` (for the Skolem witness, whose
own support is `⊆ S`). Monotone in `S` by construction; `Γ*` later discharges it uniformly. Since
`mapLanguage` distributes definitionally, `TLReady` at each `T` unfolds to `imp`-antecedent decidedness,
`iSup`/`iInf` component readiness, and `all`-body readiness at `Fin.snoc ts u` over `T ∪ jSupport u`. -/
def EMContext.TLReadyStage (ctx : EMContext L J (M := M)) (k : ℕ) {n : ℕ}
    (ψ : (skolemStage L k).BoundedFormulaω Empty n)
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (S : Finset J) : Prop :=
  ∀ T : Finset J, S ⊆ T →
    EMContext.TLReady (L := L) (J := J) ctx (ψ.mapLanguage (skolemStageInclusion L k)) ts T

/-- **The staged Γ*-truth lemma** (the load-bearing endpoint): for a **staged** base-language formula
`ψ : (skolemStage L k).BoundedFormulaω`, realizing its colimit image in the EM term model on term-classes
is equivalent to its eventual deep truth. Structural induction on `ψ`: atoms/connectives via the colimit
lemmas (`mapLanguage` distributes definitionally), `iSup`/`iInf` via `hc.OmegaComplete`, and the `all`
case via the Skolem-witness transport — the witness has support `⊆ S`, and support-uniform readiness
supplies the body's readiness at every enlarged support. No `SkolemSemantic`/`hsk` parameter; the
Skolem step is discharged inline. -/
theorem EMContext.truthLemmaStage (ctx : EMContext L J (M := M)) (hc : ctx.OmegaComplete) (k : ℕ) :
    ∀ {n : ℕ} (ψ : (skolemStage L k).BoundedFormulaω Empty n)
      (ts : Fin n → (skolemColim L)[[J]].Term Empty) (S : Finset J),
      (∀ i, jSupport L J (ts i) ⊆ S) → EMContext.TLReadyStage (L := L) (J := J) ctx k ψ ts S →
      (@BoundedFormulaω.Realize ((skolemColim L)[[J]]) ctx.Carrier ctx.structure Empty n
          ((ψ.mapLanguage (skolemStageInclusion L k)).mapLanguage (lhomWithConstants (skolemColim L) J))
          Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
        EMContext.eventualDeepTruth (L := L) (J := J) ctx
          (ψ.mapLanguage (skolemStageInclusion L k)) ts S) := by
  letI : (skolemColim L)[[J]].Structure ctx.Carrier := ctx.structure
  intro n ψ
  induction ψ with
  | falsum =>
    intro ts S _ _
    simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.realize_falsum,
      EMContext.eventualDeepTruth_falsum_iff]
  | equal t₁ t₂ =>
    intro ts S hsub _
    have hbi : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S :=
      Finset.biUnion_subset.mpr fun i _ => hsub i
    exact EMContext.eventualDeepTruth_equal_iff (L := L) (J := J) ctx
      ((skolemStageInclusion L k).onTerm t₁) ((skolemStageInclusion L k).onTerm t₂) ts
      (Finset.union_subset
        ((jSupport_onTerm_subst_subset L J ((skolemStageInclusion L k).onTerm t₁) ts).trans hbi)
        ((jSupport_onTerm_subst_subset L J ((skolemStageInclusion L k).onTerm t₂) ts).trans hbi))
  | rel R args =>
    intro ts S hsub _
    have hbi : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S :=
      Finset.biUnion_subset.mpr fun i _ => hsub i
    exact EMContext.eventualDeepTruth_rel_iff (L := L) (J := J) ctx
      ((skolemStageInclusion L k).onRelation R)
      (fun i => (skolemStageInclusion L k).onTerm (args i)) ts
      (Finset.biUnion_subset.mpr fun i _ =>
        (jSupport_onTerm_subst_subset L J ((skolemStageInclusion L k).onTerm (args i)) ts).trans hbi)
  | imp φ ψ ihφ ihψ =>
    intro ts S hsub hready
    have hdec := (hready S (le_refl S)).1
    simp only [BoundedFormulaω.mapLanguage_imp]
    rw [EMContext.eventualDeepTruth_imp_iff (L := L) (J := J) ctx
      (φ.mapLanguage (skolemStageInclusion L k)) (ψ.mapLanguage (skolemStageInclusion L k)) ts S hdec,
      BoundedFormulaω.realize_imp]
    exact imp_congr (ihφ ts S hsub fun T hT => (hready T hT).2.1)
      (ihψ ts S hsub fun T hT => (hready T hT).2.2)
  | iSup φs ih =>
    intro ts S hsub hready
    rw [show ((BoundedFormulaω.iSup φs).mapLanguage (skolemStageInclusion L k)).mapLanguage
          (lhomWithConstants (skolemColim L) J)
        = BoundedFormulaω.iSup (fun i => ((φs i).mapLanguage (skolemStageInclusion L k)).mapLanguage
            (lhomWithConstants (skolemColim L) J)) from rfl,
      BoundedFormulaω.realize_iSup]
    constructor
    · rintro ⟨i, hi⟩
      exact EMContext.eventualDeepTruth_iSup_of_exists (L := L) (J := J) ctx
        (fun i => (φs i).mapLanguage (skolemStageInclusion L k)) ts S
        ⟨i, (ih i ts S hsub fun T hT => (hready T hT) i).mp hi⟩
    · intro h
      obtain ⟨i, hi⟩ := hc.iSup_complete
        (fun i => (φs i).mapLanguage (skolemStageInclusion L k)) ts S h
      exact ⟨i, (ih i ts S hsub fun T hT => (hready T hT) i).mpr hi⟩
  | iInf φs ih =>
    intro ts S hsub hready
    rw [show ((BoundedFormulaω.iInf φs).mapLanguage (skolemStageInclusion L k)).mapLanguage
          (lhomWithConstants (skolemColim L) J)
        = BoundedFormulaω.iInf (fun i => ((φs i).mapLanguage (skolemStageInclusion L k)).mapLanguage
            (lhomWithConstants (skolemColim L) J)) from rfl,
      BoundedFormulaω.realize_iInf]
    constructor
    · intro h
      exact hc.iInf_complete (fun i => (φs i).mapLanguage (skolemStageInclusion L k)) ts S
        fun i => (ih i ts S hsub fun T hT => (hready T hT) i).mp (h i)
    · intro h i
      exact (ih i ts S hsub fun T hT => (hready T hT) i).mpr
        (EMContext.eventualDeepTruth_iInf_forall (L := L) (J := J) ctx
          (fun i => (φs i).mapLanguage (skolemStageInclusion L k)) ts S h i)
  | all ψ₀ ih =>
    intro ts S hsub hready
    set φ₀ := ψ₀.mapLanguage (skolemStageInclusion L k) with hφ₀
    have hwS : jSupport L J (skWitnessTerm L J ψ₀.not ts) ⊆ S := by
      rw [jSupport_skWitnessTerm]; exact Finset.biUnion_subset.mpr fun i _ => hsub i
    have hsnoc : ∀ (u : (skolemColim L)[[J]].Term Empty) (i : Fin (_ + 1)),
        jSupport L J ((Fin.snoc ts u : Fin _ → (skolemColim L)[[J]].Term Empty) i)
          ⊆ S ∪ jSupport L J u := by
      intro u i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact Finset.subset_union_right
      · rw [Fin.snoc_castSucc]; exact (hsub j).trans Finset.subset_union_left
    have hsnocw : ∀ i, jSupport L J
        ((Fin.snoc ts (skWitnessTerm L J ψ₀.not ts) :
            Fin _ → (skolemColim L)[[J]].Term Empty) i) ⊆ S := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hwS
      · rw [Fin.snoc_castSucc]; exact hsub j
    -- support-uniform body readiness at every `snoc ts u` over `S ∪ jSupport u`
    have hbody : ∀ (u : (skolemColim L)[[J]].Term Empty),
        EMContext.TLReadyStage (L := L) (J := J) ctx k ψ₀ (Fin.snoc ts u) (S ∪ jSupport L J u) := by
      intro u T' hT'
      have h := (hready T' (Finset.subset_union_left.trans hT')) u
      rwa [Finset.union_eq_left.mpr (Finset.subset_union_right.trans hT')] at h
    have hready_wS : EMContext.TLReadyStage (L := L) (J := J) ctx k ψ₀
        (Fin.snoc ts (skWitnessTerm L J ψ₀.not ts)) S := by
      have h := hbody (skWitnessTerm L J ψ₀.not ts)
      rwa [Finset.union_eq_left.mpr hwS] at h
    -- witness bridge: `eDT (∀φ₀)` over any `T` ↔ body `eDT` at the witness
    have hwit : ∀ (T : Finset J),
        EMContext.eventualDeepTruth (L := L) (J := J) ctx φ₀
            (Fin.snoc ts (skWitnessTerm L J ψ₀.not ts)) T ↔
          EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.all φ₀) ts T := by
      intro T
      letI : (skolemColim L).Structure M := skolemColimStructure L
      rw [EMContext.eventualDeepTruth, EMContext.eventualDeepTruth]
      refine Filter.eventually_congr (Filter.Eventually.of_forall fun d => ?_)
      rw [BoundedFormulaω.realize_all, deepInterp_snoc]
      exact ⟨fun hd => skWitness_universal L J ctx.a d T ψ₀ ts hd,
        fun hd => hd (deepInterp L J ctx.a d T (skWitnessTerm L J ψ₀.not ts))⟩
    have hinst : ∀ (T : Finset J) (u : (skolemColim L)[[J]].Term Empty),
        EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.all φ₀) ts T →
          EMContext.eventualDeepTruth (L := L) (J := J) ctx φ₀ (Fin.snoc ts u) T := by
      intro T u h
      letI : (skolemColim L).Structure M := skolemColimStructure L
      rw [EMContext.eventualDeepTruth] at h ⊢
      refine h.mono fun d hd => ?_
      rw [deepInterp_snoc]
      rw [BoundedFormulaω.realize_all] at hd
      exact hd (deepInterp L J ctx.a d T u)
    rw [show ((BoundedFormulaω.all ψ₀).mapLanguage (skolemStageInclusion L k)).mapLanguage
          (lhomWithConstants (skolemColim L) J)
        = BoundedFormulaω.all (φ₀.mapLanguage (lhomWithConstants (skolemColim L) J)) from rfl,
      BoundedFormulaω.realize_all]
    constructor
    · intro hcar
      have hcarw := hcar (ctx.mkClass (t := skWitnessTerm L J ψ₀.not ts))
      rw [EMContext.mkClass_snoc (L := L) (J := J) ctx ts (skWitnessTerm L J ψ₀.not ts)] at hcarw
      exact (hwit S).mp
        ((ih (Fin.snoc ts (skWitnessTerm L J ψ₀.not ts)) S hsnocw hready_wS).mp hcarw)
    · intro heDT
      refine Quotient.ind (fun u => ?_)
      show (φ₀.mapLanguage (lhomWithConstants (skolemColim L) J)).Realize Empty.elim
          (Fin.snoc (fun i => ctx.mkClass (t := ts i)) (ctx.mkClass (t := u)))
      rw [EMContext.mkClass_snoc (L := L) (J := J) ctx ts u]
      have hready_wSj : EMContext.TLReadyStage (L := L) (J := J) ctx k ψ₀
          (Fin.snoc ts (skWitnessTerm L J ψ₀.not ts)) (S ∪ jSupport L J u) :=
        fun T' hT' => hready_wS T' (Finset.subset_union_left.trans hT')
      have hsnocwj : ∀ i, jSupport L J
          ((Fin.snoc ts (skWitnessTerm L J ψ₀.not ts) :
              Fin _ → (skolemColim L)[[J]].Term Empty) i) ⊆ S ∪ jSupport L J u :=
        fun i => (hsnocw i).trans Finset.subset_union_left
      have hcarw := (ih (Fin.snoc ts (skWitnessTerm L J ψ₀.not ts)) S hsnocw hready_wS).mpr
        ((hwit S).mpr heDT)
      have hwT : EMContext.eventualDeepTruth (L := L) (J := J) ctx (BoundedFormulaω.all φ₀) ts
          (S ∪ jSupport L J u) :=
        (hwit (S ∪ jSupport L J u)).mp
          ((ih (Fin.snoc ts (skWitnessTerm L J ψ₀.not ts)) (S ∪ jSupport L J u) hsnocwj
            hready_wSj).mp hcarw)
      exact (ih (Fin.snoc ts u) (S ∪ jSupport L J u) (hsnoc u) (hbody u)).mpr
        (hinst (S ∪ jSupport L J u) u hwT)

/-! ### Step 4D-9: Γ* supplies support-uniform readiness

Given a deForm-membership closure `hmem` (every `Γ*` member's de-substituted formula, over every
covering support and argument tuple, lies in `Γ`), the readiness `TLReadyStage` holds for every `Γ*`
formula. The `imp`-antecedent decidedness obligations are discharged by `eventualDeepTruth_decided`
(fed by `hmem`); the recursion descends through `Γ*`'s subformula/component closure (`skSubStep`); the
`all` case reads the body's readiness at the one-point extension over the enlarged support — supplied
uniformly because the witness's own support is `⊆ S`. `hmem` itself (the "template-renaming" closure)
is produced from `Γ*` in the following chunk. `OmegaComplete` is a *separate* obligation, not here. -/

/-- **Readiness (un-quantified support form)**: from the deForm-membership closure `hmem`, every `Γ*`
formula `ψ` has `TLReady` at every covering support `T`. The core induction; `TLReadyStage_of_GammaStar`
wraps it over `T ⊇ S`. -/
theorem EMContext.TLReady_mapLang_of_GammaStar (ctx : EMContext L J (M := M)) {k : ℕ}
    {Γ₀ : Set (SkFormula L)}
    (hmem : ∀ {m' : ℕ} (φ' : (skolemStage L k).BoundedFormulaω Empty m'),
      (⟨k, m', φ'⟩ : SkFormula L) ∈ Γstar L Γ₀ →
      ∀ (ts' : Fin m' → (skolemColim L)[[J]].Term Empty) (T' : Finset J)
        (hcov' : ∀ i, jSupport L J (ts' i) ⊆ T'),
        (⟨T'.card, deForm L J T' (φ'.mapLanguage (skolemStageInclusion L k)) ts' hcov'⟩ :
          Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ ctx.Γ) :
    ∀ {n : ℕ} (ψ : (skolemStage L k).BoundedFormulaω Empty n),
      (⟨k, n, ψ⟩ : SkFormula L) ∈ Γstar L Γ₀ →
      ∀ (ts : Fin n → (skolemColim L)[[J]].Term Empty) (T : Finset J),
        (∀ i, jSupport L J (ts i) ⊆ T) →
        EMContext.TLReady (L := L) (J := J) ctx
          (ψ.mapLanguage (skolemStageInclusion L k)) ts T := by
  intro n ψ
  induction ψ with
  | falsum => intro _ _ _ _; exact trivial
  | equal t₁ t₂ => intro _ _ _ _; exact trivial
  | rel R args => intro _ _ _ _; exact trivial
  | imp φ' ψ' ihφ ihψ =>
    intro hψ ts T hcov
    have hφ'mem : (⟨k, _, φ'⟩ : SkFormula L) ∈ Γstar L Γ₀ :=
      skSubStep_subset_Γstar L hψ (Set.mem_image_of_mem _ (Set.mem_insert _ _))
    have hψ'mem : (⟨k, _, ψ'⟩ : SkFormula L) ∈ Γstar L Γ₀ :=
      skSubStep_subset_Γstar L hψ (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ rfl))
    exact ⟨EMContext.eventualDeepTruth_decided (L := L) (J := J) ctx
        (φ'.mapLanguage (skolemStageInclusion L k)) ts T hcov (hmem φ' hφ'mem ts T hcov),
      ihφ hφ'mem ts T hcov, ihψ hψ'mem ts T hcov⟩
  | iSup φs ih =>
    intro hψ ts T hcov i
    exact ih i (skSubStep_subset_Γstar L hψ (Set.mem_image_of_mem _ (Set.mem_range_self i)))
      ts T hcov
  | iInf φs ih =>
    intro hψ ts T hcov i
    exact ih i (skSubStep_subset_Γstar L hψ (Set.mem_image_of_mem _ (Set.mem_range_self i)))
      ts T hcov
  | all χ' ih =>
    intro hψ ts T hcov u
    have hχ'mem : (⟨k, _, χ'⟩ : SkFormula L) ∈ Γstar L Γ₀ :=
      skSubStep_subset_Γstar L hψ (Set.mem_image_of_mem _ rfl)
    have hcov' : ∀ i, jSupport L J ((Fin.snoc ts u : Fin _ → (skolemColim L)[[J]].Term Empty) i)
        ⊆ T ∪ jSupport L J u := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact Finset.subset_union_right
      · rw [Fin.snoc_castSucc]; exact (hcov j).trans Finset.subset_union_left
    exact ih hχ'mem (Fin.snoc ts u) (T ∪ jSupport L J u) hcov'

/-- **`Γ*` supplies support-uniform `TLReadyStage`** (this chunk's endpoint, modulo the deForm-closure
`hmem`): every `Γ*` formula is `truthLemmaStage`-ready. Wraps `TLReady_mapLang_of_GammaStar` over the
enlarged supports `T ⊇ S` (each still covers `ts`). -/
theorem EMContext.TLReadyStage_of_GammaStar (ctx : EMContext L J (M := M)) {k : ℕ}
    {Γ₀ : Set (SkFormula L)}
    (hmem : ∀ {m' : ℕ} (φ' : (skolemStage L k).BoundedFormulaω Empty m'),
      (⟨k, m', φ'⟩ : SkFormula L) ∈ Γstar L Γ₀ →
      ∀ (ts' : Fin m' → (skolemColim L)[[J]].Term Empty) (T' : Finset J)
        (hcov' : ∀ i, jSupport L J (ts' i) ⊆ T'),
        (⟨T'.card, deForm L J T' (φ'.mapLanguage (skolemStageInclusion L k)) ts' hcov'⟩ :
          Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ ctx.Γ)
    {n : ℕ} (ψ : (skolemStage L k).BoundedFormulaω Empty n)
    (hψ : (⟨k, n, ψ⟩ : SkFormula L) ∈ Γstar L Γ₀)
    (ts : Fin n → (skolemColim L)[[J]].Term Empty) (S : Finset J)
    (hcov : ∀ i, jSupport L J (ts i) ⊆ S) :
    EMContext.TLReadyStage (L := L) (J := J) ctx k ψ ts S :=
  fun T hST => EMContext.TLReady_mapLang_of_GammaStar (L := L) (J := J) ctx hmem ψ hψ ts T
    (fun i => (hcov i).trans hST)

end Quotient

end FirstOrder.Language
