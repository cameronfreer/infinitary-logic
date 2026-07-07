/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Sort
import Mathlib.SetTheory.Cardinal.Regular
import InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction
import InfinitaryLogic.Methods.GeneratedSublanguage

/-!
# The Marker stage: finite-fragment support extraction and Erdős–Rado certification

First layer of the template/consistency-property reshape of the Morley–Hanf chain (the
replacement for the ZFC-refutable in-`M` extraction ladder — see the audit fences on
`PureColoringHypothesis`/`MorleyHanfExtraction` in `Conditional/MorleyHanfTransfer.lean`).
Following Marker, *Lectures on Infinitary Model Theory* §5.2, the consistency-property route
certifies each **finite** fragment of an `L'[[J]]` template/constant theory by a large
homogeneous set in the source model, with the indiscernible sequence materializing only in
the model built by Model Existence.

This file provides the syntactic/combinatorial bridge between "finite fragment of a
constant theory" and "finite-arity Erdős–Rado approximation":

* a finite fragment is presented by its **index data** — a finite family of pairs
  `(fml p : L'.BoundedFormulaω Empty (ar p), tup p : Fin (ar p) ↪o J)` (per the template
  machinery in `Methods/EM/Realization.lean`, membership in a template theory carries
  exactly this witness data, so no syntactic support extraction is ever needed);
* `exists_markerSupport_factor` — collect the finite `J`-constant support of the family,
  enumerate it as `enum : Fin k ↪o J`, and factor every `tup p` through `enum`
  (via `exists_orderEmbedding_factor`);
* `markerStage_homogeneous` — pull the family back to a single arity-`k` truth-vector
  coloring over the source model and apply `finiteArityHomogeneousUpTo_beth_stage`:
  for every `α < ω₁`, a source of size `≥ ℶ_{ω₁}` yields a `(ℶ_α)⁺`-suborder on which the
  truth vector of the whole fragment is tuple-independent.

The per-`α` conclusion (available for **every** `α < ω₁` at once) is the Marker schedule.

## Layer 2: the certification predicates and their closure calculus

Toward the Marker consistency property, this file also provides the candidate member
predicate and its easy closure lemmas:

* `sentenceJConsts` — the syntactic `J`-constant support of an `L'[[J]]`-sentence (a `Set J`
  carved out of `functionsIn`; only countable in general, finite exactly for the sentences
  the construction certifies — support finiteness is *demanded* by the predicate, never
  computed);
* `MarkerFiniteCert M α F` — a finite set of sentences is certified at level `α`: a common
  finite support `S`, a `(ℶ_α)⁺`-suborder `e` of `M`, and satisfaction of every member under
  every constant interpretation that is increasing on `S` into `e`'s range;
* `MarkerCofinalConsistent M Sset` — every finite subset is certified at cofinally many
  `α < ω₁` (finite character makes weakening and chain closure pleasant);
* the closure lemmas that need **no** uniform countable choice: weakening, chain closure,
  the `C0` pair (no falsum, no contradiction), `C2` (double negation), `C3` (conjunction
  components), `C4'` (negated-disjunction components) — each by replacing the derived
  sentence with its trigger inside the certified fragment
  (`MarkerCofinalConsistent.extend_of_semantic`) and pushing pointwise `realize` lemmas
  through the same interpretations;
* `exists_uniform_of_cofinal_countable` — the `ω₁`-pigeonhole engine (ω₁ is regular, so a
  countably-colored cofinal α-schedule has a monochromatic cofinal subschedule);
* `MarkerISupUniform` — **the stated hard test**: does `⋁ᵢ φᵢ ∈ Sset` yield ONE disjunct
  `k` with `Sset ∪ {φs k}` still cofinally consistent? Per finite fragment `F` and level
  `α`, re-homogenization + the pigeonhole produce `k(F)`; the open question is uniformizing
  over ALL finite `F ⊆ Sset` — a directed intersection of antitone nonempty subsets of `ℕ`,
  which is NOT automatic. If provable, `markerConsistencyPropertyEq` is mostly assembly; if
  not, the fallback is a finite-member consistency notion with its own Henkin/model-existence
  adapter (the existing `ConsistencyPropertyEq` API also demands `extension` for ARBITRARY
  sentences, which certification cannot supply for sentences of infinite support — another
  reason the finite-member adapter may be the honest endpoint).

**C7/Henkin witness design note (decision pending, do not leave implicit):** over a
relational `L'`, the closed `L'[[J]]`-terms are exactly the `J`-constants, so quantifier
witnesses must be *fresh constants*; freshness alone is not enough — the witness constant
must occupy a specific order-position of `J` relative to the fragment's support, and an
arbitrary linear `J` need not have an element in the required gap. Candidate resolutions:
run the construction over a Henkin constant expansion of `L'[[J]]`; or restrict/embed `J`
into a dense-enough order first; or route witnesses through the existing local Skolem
machinery. To be settled before `markerConsistencyPropertyEq`.
-/

universe u

namespace FirstOrder.Language

open Cardinal

/-- Every finite ordinal step stays below `ω₁`: if `α < ω₁` then `α + n < ω₁` for every
natural `n` — the room the Marker `α`-schedule uses to absorb per-fragment ladder costs. -/
theorem add_natCast_lt_omega_one {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) :
    ∀ n : ℕ, α + (n : Ordinal) < Ordinal.omega 1
  | 0 => by simpa using hα
  | (n + 1) => by
    have hn : α + (n : Ordinal) < Ordinal.omega 1 := add_natCast_lt_omega_one hα n
    have : α + ((n + 1 : ℕ) : Ordinal) = Order.succ (α + (n : Ordinal)) := by
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Order.succ_eq_add_one]
    rw [this]
    exact (Cardinal.isSuccLimit_omega 1).succ_lt hn

/-- **Support factorization for a finite constant-fragment.** Given a finite family of
`J`-constant tuples `tup p : Fin (ar p) ↪o J` (the index data of a finite fragment of an
`L'[[J]]` constant theory), collect the finite support, enumerate it in increasing order as
`enum : Fin k ↪o J`, and factor every tuple through the enumeration. The range equation
identifies `enum` with the exact constant support of the fragment. -/
theorem exists_markerSupport_factor {J : Type u} [LinearOrder J]
    {m : ℕ} {ar : Fin m → ℕ} (tup : ∀ p, Fin (ar p) ↪o J) :
    ∃ (k : ℕ) (enum : Fin k ↪o J) (r : ∀ p, Fin (ar p) ↪o Fin k),
      (∀ p, (r p).trans enum = tup p) ∧
      Set.range ⇑enum = ⋃ p, Set.range ⇑(tup p) := by
  classical
  set S : Finset J := Finset.univ.biUnion fun p => Finset.univ.image ⇑(tup p) with hS
  have hrange : Set.range ⇑(S.orderEmbOfFin rfl) = ↑S := Finset.range_orderEmbOfFin S rfl
  have hmem : ∀ p (i : Fin (ar p)), tup p i ∈ Set.range ⇑(S.orderEmbOfFin rfl) := by
    intro p i
    rw [hrange]
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
  choose r hr using fun p =>
    exists_orderEmbedding_factor (S.orderEmbOfFin rfl) (tup p) (hmem p)
  refine ⟨S.card, S.orderEmbOfFin rfl, r, hr, ?_⟩
  rw [hrange]
  simp [hS]

/-- **The Marker-stage Erdős–Rado certification.** A finite fragment of an `L'[[J]]`
constant theory, presented by its index data `(fml p, tup p)`, pulls back along the support
factorization to a single arity-`k` truth-vector coloring over the source model `M`; for
every `α < ω₁`, `finiteArityHomogeneousUpTo_beth_stage` then yields a `(ℶ_α)⁺`-suborder of
`M` on which the truth of every formula of the fragment (at its own positions `r p` inside
the support) is independent of the choice of increasing `k`-tuple.

This is the per-fragment certification of the Marker consistency property: available at
every `α < ω₁` simultaneously (the cofinal schedule), from the single hypothesis
`|M| ≥ ℶ_{ω₁}` — per-`α`, per-finite-fragment approximations, never one `ω₁`-suborder
homogeneous for all arities at once (that jump is ZFC-refutable; see the audit fences). -/
theorem markerStage_homogeneous {L' : Language.{0, 0}} (M : Type) [L'.Structure M]
    [LinearOrder M] [WellFoundedLT M]
    (hM : Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1))
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1)
    {J : Type} [LinearOrder J]
    {m : ℕ} {ar : Fin m → ℕ} (fml : ∀ p : Fin m, L'.BoundedFormulaω Empty (ar p))
    (tup : ∀ p, Fin (ar p) ↪o J) :
    ∃ (k : ℕ) (enum : Fin k ↪o J) (r : ∀ p, Fin (ar p) ↪o Fin k),
      (∀ p, (r p).trans enum = tup p) ∧
      Set.range ⇑enum = ⋃ p, Set.range ⇑(tup p) ∧
      ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
        ∀ u u' : Fin k ↪o M,
          (∀ i, u i ∈ Set.range e) → (∀ i, u' i ∈ Set.range e) →
          ∀ p, ((fml p).Realize (Empty.elim : Empty → M) (⇑u ∘ ⇑(r p)) ↔
            (fml p).Realize (Empty.elim : Empty → M) (⇑u' ∘ ⇑(r p))) := by
  classical
  obtain ⟨k, enum, r, hr, hrange⟩ := exists_markerSupport_factor tup
  refine ⟨k, enum, r, hr, hrange, ?_⟩
  -- The truth-vector coloring at the support arity, defaulted elsewhere.
  let realColor : (Fin k ↪o M) → (Fin m → Prop) := fun u p =>
    (fml p).Realize (Empty.elim : Empty → M) (⇑u ∘ ⇑(r p))
  let c : ∀ n, (Fin n ↪o M) → (Fin m → Prop) :=
    Function.update (fun _ _ _ => True) k realColor
  have hc : c k = realColor := Function.update_self _ _ _
  have hsize : Cardinal.beth (α + ((2 * k + 2 : ℕ) : Ordinal)) ≤ Cardinal.mk M :=
    (Cardinal.beth_le_beth.mpr (add_natCast_lt_omega_one hα (2 * k + 2)).le).trans hM
  have hC : ∀ n : ℕ, Cardinal.mk (Fin m → Prop) ≤ Cardinal.beth α := fun _ =>
    (Cardinal.mk_lt_aleph0 (α := Fin m → Prop)).le.trans (Cardinal.aleph0_le_beth α)
  obtain ⟨e, he⟩ :=
    finiteArityHomogeneousUpTo_beth_stage α k hsize (fun _ => Fin m → Prop) hC c
  refine ⟨e, fun u u' hu hu' p => ?_⟩
  have h : c k u = c k u' := he k le_rfl u u' hu hu'
  have h' : realColor u = realColor u' := by rw [← hc]; exact h
  exact iff_of_eq (congrFun h' p)

/-! ## Layer 2: the certification predicates -/

section Certification

variable {L' : Language.{0, 0}} {J : Type}

/-- The syntactic `J`-constant support of an `L'[[J]]`-sentence: the constants (arity-0
`Sum.inr` function symbols) among its mentioned symbols. Only countable in general
(`functionsIn_countable` — countably-branching connectives); the certification predicate
below *demands* containment in a finite set rather than computing one. -/
def sentenceJConsts (τ : L'[[J]].Sentenceω) : Set J :=
  {j | (⟨0, (Sum.inr j : L'[[J]].Functions 0)⟩ : Σ n, L'[[J]].Functions n) ∈
    BoundedFormulaω.functionsIn τ}

/-- Negation does not change the constant support (`not` is `imp · falsum`). -/
theorem sentenceJConsts_not (τ : L'[[J]].Sentenceω) :
    sentenceJConsts (L' := L') τ.not = sentenceJConsts (L' := L') τ := by
  ext j
  simp [sentenceJConsts, BoundedFormulaω.functionsIn]

/-- A conjunction component's constant support is contained in the conjunction's. -/
theorem sentenceJConsts_component_iInf (φs : ℕ → L'[[J]].Sentenceω) (k : ℕ) :
    sentenceJConsts (L' := L') (φs k) ⊆
      sentenceJConsts (L' := L') (BoundedFormulaω.iInf φs) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_setOf_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_iUnion.mpr ⟨k, hj⟩

/-- A disjunction component's constant support is contained in the disjunction's. -/
theorem sentenceJConsts_component_iSup (φs : ℕ → L'[[J]].Sentenceω) (k : ℕ) :
    sentenceJConsts (L' := L') (φs k) ⊆
      sentenceJConsts (L' := L') (BoundedFormulaω.iSup φs) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_setOf_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_iUnion.mpr ⟨k, hj⟩

variable [LinearOrder J] (M : Type) [L'.Structure M] [LinearOrder M]

/-- **The per-level Marker certification of a finite fragment**: a common finite constant
support `S`, a `(ℶ_α)⁺`-suborder `e` of the (well-ordered) source `M`, and satisfaction of
every member sentence under every constant interpretation that is strictly increasing on
`S` with values in the range of `e`. This is Marker's "`ℶ_α`-large set realizing `σ`",
stated semantically over interpretations so that the closure calculus needs no constructor
inversion through the template pipeline. -/
def MarkerFiniteCert (α : Ordinal.{0}) (F : Set L'[[J]].Sentenceω) : Prop :=
  ∃ S : Finset J, (∀ τ ∈ F, sentenceJConsts (L' := L') τ ⊆ ↑S) ∧
    ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
      ∀ σ : J → M, StrictMonoOn σ ↑S → (∀ j ∈ S, σ j ∈ Set.range e) →
        letI : (constantsOn J).Structure M := constantsOn.structure σ
        ∀ τ ∈ F, Sentenceω.Realize τ M

/-- **The candidate Marker member predicate**: every finite subfragment is certified at
cofinally many levels `α < ω₁`. Finite character makes weakening and chain closure direct;
the uniformization questions (`MarkerISupUniform` below) are exactly where it is honest. -/
def MarkerCofinalConsistent (Sset : Set L'[[J]].Sentenceω) : Prop :=
  ∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ Sset →
    ∀ β, β < Ordinal.omega 1 →
      ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧ MarkerFiniteCert M α F

variable {M}

/-- Certification is monotone (downward-closed) in the fragment. -/
theorem MarkerFiniteCert.mono {α : Ordinal.{0}} {F F' : Set L'[[J]].Sentenceω}
    (hFF : F' ⊆ F) (h : MarkerFiniteCert M α F) : MarkerFiniteCert M α F' := by
  obtain ⟨S, hsupp, e, hsat⟩ := h
  exact ⟨S, fun τ hτ => hsupp τ (hFF hτ), e,
    fun σ h1 h2 τ hτ => hsat σ h1 h2 τ (hFF hτ)⟩

/-- Cofinal consistency is monotone (downward-closed) in the sentence set. -/
theorem MarkerCofinalConsistent.mono {Sset Sset' : Set L'[[J]].Sentenceω}
    (hSS : Sset' ⊆ Sset) (h : MarkerCofinalConsistent M Sset) :
    MarkerCofinalConsistent M Sset' :=
  fun F hFin hsub => h F hFin (hsub.trans hSS)

/-- **Chain closure**: the union of a nonempty `⊆`-chain of cofinally consistent sets is
cofinally consistent — a finite subfragment of the union lies in one chain member. -/
theorem MarkerCofinalConsistent.sUnion_chain {chain : Set (Set L'[[J]].Sentenceω)}
    (hchain : ∀ T ∈ chain, MarkerCofinalConsistent M T)
    (hC : IsChain (· ⊆ ·) chain) (hne : chain.Nonempty) :
    MarkerCofinalConsistent M (⋃₀ chain) := by
  have key : ∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ ⋃₀ chain →
      ∃ T ∈ chain, F ⊆ T := by
    intro F hFin
    induction F, hFin using Set.Finite.induction_on with
    | empty =>
      intro _
      obtain ⟨T, hT⟩ := hne
      exact ⟨T, hT, Set.empty_subset T⟩
    | insert ha hs ih =>
      rename_i a s
      intro hsub
      obtain ⟨T₁, hT₁, hsT₁⟩ := ih fun x hx => hsub (Set.mem_insert_of_mem _ hx)
      obtain ⟨T₂, hT₂, haT₂⟩ := Set.mem_sUnion.mp (hsub (Set.mem_insert a s))
      rcases eq_or_ne T₁ T₂ with rfl | hne12
      · exact ⟨T₁, hT₁, Set.insert_subset_iff.mpr ⟨haT₂, hsT₁⟩⟩
      rcases hC.total hT₁ hT₂ with h12 | h21
      · exact ⟨T₂, hT₂, Set.insert_subset_iff.mpr ⟨haT₂, hsT₁.trans h12⟩⟩
      · exact ⟨T₁, hT₁, Set.insert_subset_iff.mpr ⟨h21 haT₂, hsT₁⟩⟩
  intro F hFin hsub β hβ
  obtain ⟨T, hT, hFT⟩ := key F hFin hsub
  exact hchain T hT F hFin hFT β hβ

/-- There is always an interpretation that is increasing on a given finite support into the
range of a `(ℶ_α)⁺`-suborder — the suborder's domain is infinite, so it contains increasing
tuples of every finite length. Supplies the "evaluation point" for the `C0` lemmas. -/
theorem exists_strictMonoOn_interp {α : Ordinal.{0}}
    (e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M) (S : Finset J) :
    ∃ σ : J → M, StrictMonoOn σ ↑S ∧ ∀ j ∈ S, σ j ∈ Set.range e := by
  classical
  have hinf : Infinite (Order.succ (Cardinal.beth α)).ord.ToType := by
    rw [Cardinal.infinite_iff, Cardinal.mk_ord_toType]
    exact (Cardinal.aleph0_le_beth α).trans (Order.le_succ _)
  obtain ⟨s, -, hcard⟩ :=
    (Set.infinite_univ (α := (Order.succ (Cardinal.beth α)).ord.ToType)).exists_subset_card_eq
      S.card
  refine ⟨fun j => if h : j ∈ S then e (s.orderEmbOfFin hcard ((S.orderIsoOfFin rfl).symm ⟨j, h⟩))
    else e (Classical.arbitrary _), ?_, ?_⟩
  · intro j hj j' hj' hlt
    dsimp only
    rw [dif_pos (Finset.mem_coe.mp hj), dif_pos (Finset.mem_coe.mp hj')]
    exact e.strictMono ((s.orderEmbOfFin hcard).strictMono
      ((S.orderIsoOfFin rfl).symm.strictMono (Subtype.mk_lt_mk.mpr hlt)))
  · intro j hj
    dsimp only
    rw [dif_pos hj]
    exact ⟨_, rfl⟩

/-- **`C0` (no falsum)**: a certified fragment cannot contain `⊥` — an increasing
interpretation exists and would have to realize it. -/
theorem MarkerFiniteCert.falsum_notMem {α : Ordinal.{0}} {F : Set L'[[J]].Sentenceω}
    (h : MarkerFiniteCert M α F) :
    (BoundedFormulaω.falsum : L'[[J]].Sentenceω) ∉ F := by
  intro hmem
  obtain ⟨S, hsupp, e, hsat⟩ := h
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  exact hsat σ hmono hrange _ hmem

/-- **`C0` (no contradiction)**: a certified fragment cannot contain both a sentence and
its negation. -/
theorem MarkerFiniteCert.not_mem_and_not_mem {α : Ordinal.{0}} {F : Set L'[[J]].Sentenceω}
    (h : MarkerFiniteCert M α F) (τ : L'[[J]].Sentenceω) : ¬(τ ∈ F ∧ τ.not ∈ F) := by
  rintro ⟨h1, h2⟩
  obtain ⟨S, hsupp, e, hsat⟩ := h
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  exact (BoundedFormulaω.realize_not τ).mp (hsat σ hmono hrange _ h2)
    (hsat σ hmono hrange _ h1)

/-- **The semantic extension scheme** behind the choice-free closure conditions: if a
`trigger` sentence of `Sset` semantically entails a `new` sentence pointwise (under every
constant interpretation) and the constant support does not grow, then adjoining `new`
preserves cofinal consistency — inside any finite subfragment, replace `new` by its
trigger and reuse the certificate. -/
theorem MarkerCofinalConsistent.extend_of_semantic {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {trigger new : L'[[J]].Sentenceω}
    (hmem : trigger ∈ Sset)
    (hsupp : sentenceJConsts (L' := L') new ⊆ sentenceJConsts (L' := L') trigger)
    (hder : ∀ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      Sentenceω.Realize trigger M → Sentenceω.Realize new M) :
    MarkerCofinalConsistent M (Sset ∪ {new}) := by
  classical
  intro F hFin hsub β hβ
  by_cases hnew : new ∈ F
  · -- Replace `new` by `trigger` and re-certify.
    have hGfin : ((F \ {new}) ∪ {trigger}).Finite :=
      (hFin.subset Set.sdiff_subset).union (Set.finite_singleton _)
    have hGsub : (F \ {new}) ∪ {trigger} ⊆ Sset := by
      rintro τ (⟨hτF, hτne⟩ | hτ)
      · rcases hsub hτF with hS | h1
        · exact hS
        · exact absurd (Set.mem_singleton_iff.mp h1) hτne
      · rw [Set.mem_singleton_iff.mp hτ]
        exact hmem
    obtain ⟨α, hβα, hα, S, hsuppG, e, hsat⟩ := h _ hGfin hGsub β hβ
    have htrig : trigger ∈ (F \ {new}) ∪ {trigger} := Set.mem_union_right _ rfl
    refine ⟨α, hβα, hα, S, ?_, e, ?_⟩
    · intro τ hτ
      by_cases hτnew : τ = new
      · subst hτnew
        exact hsupp.trans (hsuppG trigger htrig)
      · exact hsuppG τ (Set.mem_union_left _ ⟨hτ, hτnew⟩)
    · intro σ h1 h2 τ hτ
      by_cases hτnew : τ = new
      · subst hτnew
        exact hder σ (hsat σ h1 h2 trigger htrig)
      · exact hsat σ h1 h2 τ (Set.mem_union_left _ ⟨hτ, hτnew⟩)
  · -- `new` unused: `F` already sits inside `Sset`.
    refine h F hFin (fun τ hτ => ?_) β hβ
    rcases hsub hτ with hS | h1
    · exact hS
    · rw [Set.mem_singleton_iff.mp h1] at hτ
      exact absurd hτ hnew

/-- **`C2` (double negation)**: `¬¬φ ∈ Sset` allows adjoining `φ`. -/
theorem MarkerCofinalConsistent.not_not {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {φ : L'[[J]].Sentenceω}
    (hmem : φ.not.not ∈ Sset) : MarkerCofinalConsistent M (Sset ∪ {φ}) :=
  h.extend_of_semantic hmem (by simp [sentenceJConsts_not]) fun σ => by
    letI : (constantsOn J).Structure M := constantsOn.structure σ
    exact fun hreal => of_not_not fun hn =>
      (BoundedFormulaω.realize_not φ.not).mp hreal ((BoundedFormulaω.realize_not φ).mpr hn)

/-- **`C3` (conjunction components)**: `⋀ᵢ φᵢ ∈ Sset` allows adjoining every component. -/
theorem MarkerCofinalConsistent.iInf_component {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {φs : ℕ → L'[[J]].Sentenceω}
    (hmem : BoundedFormulaω.iInf φs ∈ Sset) (k : ℕ) :
    MarkerCofinalConsistent M (Sset ∪ {φs k}) :=
  h.extend_of_semantic hmem (sentenceJConsts_component_iInf φs k) fun σ => by
    letI : (constantsOn J).Structure M := constantsOn.structure σ
    exact fun hreal => (BoundedFormulaω.realize_iInf φs).mp hreal k

/-- **`C4'` (negated-disjunction components)**: `¬⋁ᵢ φᵢ ∈ Sset` allows adjoining every
negated component. -/
theorem MarkerCofinalConsistent.neg_iSup_component {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {φs : ℕ → L'[[J]].Sentenceω}
    (hmem : (BoundedFormulaω.iSup φs).not ∈ Sset) (k : ℕ) :
    MarkerCofinalConsistent M (Sset ∪ {(φs k).not}) :=
  h.extend_of_semantic hmem
    (by rw [sentenceJConsts_not, sentenceJConsts_not]
        exact sentenceJConsts_component_iSup φs k)
    fun σ => by
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      exact fun hreal => (BoundedFormulaω.realize_not (φs k)).mpr fun hk =>
        (BoundedFormulaω.realize_not _).mp hreal
          ((BoundedFormulaω.realize_iSup φs).mpr ⟨k, hk⟩)

end Certification

/-! ## The ω₁-pigeonhole engine and the stated uniformization test -/

/-- **The cofinal-schedule pigeonhole**: `ω₁` is regular, so if cofinally many levels below
`ω₁` each carry a witness from a countable index type, ONE index works cofinally. This is
the engine behind every uniformization step of the Marker consistency property (binary
choices such as `C1`, and — if it suffices — the disjunction choice `C4`). -/
theorem exists_uniform_of_cofinal_countable {K : Type} [Countable K]
    (P : Ordinal.{0} → K → Prop)
    (h : ∀ β, β < Ordinal.omega 1 → ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧ ∃ k, P α k) :
    ∃ k, ∀ β, β < Ordinal.omega 1 → ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧ P α k := by
  by_contra hcon
  push Not at hcon
  choose β hβlt hβ using hcon
  obtain ⟨α, hle, hα, k, hP⟩ := h (⨆ k, β k) (Ordinal.iSup_lt_omega_one hβlt)
  exact hβ k α ((Ordinal.le_iSup β k).trans hle) hα hP

variable {L' : Language.{0, 0}} {J : Type} [LinearOrder J]

/-- **The hard uniformization test** (deliberately a named statement, not a theorem): does
a disjunction in a cofinally consistent set admit ONE disjunct whose adjunction stays
cofinally consistent? Per finite subfragment `F` and level `α`, re-homogenizing the
disjunct index (countably many colors, `≤ ℶ_α`) and pigeonholing the cofinal schedule
(`exists_uniform_of_cofinal_countable`) produce a per-`F` disjunct `k(F)`; the open
content is uniformizing over ALL finite `F ⊆ Sset` — a directed intersection of antitone
nonempty subsets of `ℕ`, which is not automatic. If this holds, the Marker consistency
property (`ConsistencyPropertyEq`'s `C4_iSup`) is mostly assembly; if it fails, the honest
route is a finite-member consistency notion with its own Henkin/model-existence adapter
(see the module docstring, including the `extension`-field obstruction). -/
def MarkerISupUniform (M : Type) [L'.Structure M] [LinearOrder M] : Prop :=
  ∀ (Sset : Set L'[[J]].Sentenceω) (φs : ℕ → L'[[J]].Sentenceω),
    MarkerCofinalConsistent M Sset → BoundedFormulaω.iSup φs ∈ Sset →
    ∃ k, MarkerCofinalConsistent M (Sset ∪ {φs k})

end FirstOrder.Language
