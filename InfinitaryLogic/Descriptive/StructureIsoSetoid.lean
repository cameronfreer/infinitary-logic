/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.PerfectAntichain
import InfinitaryLogic.Descriptive.SatisfactionBorel
import Architect

/-!
# The ambient isomorphism relation on coded structures

`isoSetoid φ` lives on the subtype `↥(ModelsOf φ)`, which means every statement about it is
implicitly a statement about a chosen Polish structure *on that subtype*.  For a perfect set
that is the wrong place to work: whether a set is perfect should be a fact about the ambient
`StructureSpace L`, not about a refinement chosen to make one particular model class Polish.

So the isomorphism relation is defined **once**, ambiently, as `structureIsoSetoid L`, and
`isoSetoid φ` *is* its pullback along the subtype inclusion — that is its definition, not a
theorem about it.  The sentence-level predicates below then quantify over perfect subsets of
`StructureSpace L` contained in `ModelsOf φ`, and the chosen refinement never enters their
statements.
-/

open Cardinal Set

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational]

/-- **The ambient isomorphism relation**: two codes are related iff the structures they decode
on `ℕ` are `L`-isomorphic.  Stated on all of `StructureSpace L`, with no reference to any
sentence. -/
@[blueprint "def:structure-iso-setoid"
  (title := /-- Ambient isomorphism relation -/)
  (statement := /-- The equivalence relation on all of the structure space where two codes are
    related iff the structures they decode on $\mathbb{N}$ are $L$-isomorphic.  Defined without
    reference to any sentence, so that perfectness of a set of codes is a property of the ambient
    space rather than of a refinement chosen to make one model class Polish. -/)
  (uses := ["def:structure-space"])]
def structureIsoSetoid (L : Language.{u, v}) [L.IsRelational] : Setoid (StructureSpace L) where
  r c₁ c₂ := Nonempty (@Language.Equiv L ℕ ℕ c₁.toStructure c₂.toStructure)
  iseqv :=
    { refl := fun c => ⟨@Language.Equiv.refl L ℕ c.toStructure⟩
      symm := fun {c₁ c₂} ⟨e⟩ => ⟨@Language.Equiv.symm L ℕ ℕ c₁.toStructure c₂.toStructure e⟩
      trans := fun {c₁ c₂ c₃} ⟨e₁⟩ ⟨e₂⟩ =>
        ⟨@Language.Equiv.comp L ℕ ℕ c₁.toStructure c₂.toStructure ℕ c₃.toStructure e₂ e₁⟩ }

variable [Countable (Σ l, L.Relations l)]

/-- The isomorphism equivalence relation on coded ℕ-models of φ: the ambient relation
restricted to the models of `φ`.  Two codes are related iff the decoded structures on ℕ are
L-isomorphic. -/
@[blueprint "def:iso-setoid"
  (title := /-- Isomorphism setoid on coded models -/)
  (statement := /-- The equivalence relation on coded $\mathbb{N}$-models of $\varphi$
    where two codes are related iff their decoded structures are $L$-isomorphic.  It is the
    ambient relation restricted along the subtype inclusion. -/)
  (uses := ["def:structure-iso-setoid"])]
def isoSetoid (φ : L.Sentenceω) : Setoid ↥(ModelsOf φ) :=
  (structureIsoSetoid L).comap Subtype.val

/-- `isoSetoid φ` is the ambient relation pulled back along the subtype inclusion.  True by
definition; stated so consumers can rewrite with it without unfolding. -/
theorem isoSetoid_eq_comap (φ : L.Sentenceω) :
    isoSetoid φ = (structureIsoSetoid L).comap (Subtype.val : ↥(ModelsOf φ) → StructureSpace L) :=
  rfl

/-- Membership in the pulled-back relation is membership in the ambient one. -/
theorem isoSetoid_r_iff {φ : L.Sentenceω} {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ ↔ (structureIsoSetoid L).r c₁.1 c₂.1 := Iff.rfl

/-! ### Sentence-level predicates

Stated ambiently, so that no Polish refinement of the model subtype appears in the
definitions. -/

/-- `φ` has a perfect set of pairwise non-isomorphic countable models. -/
def Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels (φ : L.Sentenceω) : Prop :=
  HasPerfectAntichainOn (structureIsoSetoid L) (ModelsOf φ)

/-- `φ` is thin on its countable models: no such perfect set. -/
@[blueprint "def:thin-nat-models"
  (title := /-- Thinness on coded $\mathbb{N}$-models -/)
  (statement := /-- A sentence $\varphi$ is \emph{thin on its $\mathbb{N}$-models} if the set of
    codes of $\mathbb{N}$-models of $\varphi$ carries no perfect antichain for the ambient
    isomorphism relation on the structure space.  Stated ambiently, so no Polish refinement of
    the model subtype enters the definition. -/)
  (uses := ["def:thin-on", "def:structure-iso-setoid"])]
def Sentenceω.IsThinOnNatModels (φ : L.Sentenceω) : Prop :=
  IsThinOn (structureIsoSetoid L) (ModelsOf φ)

theorem Sentenceω.isThinOnNatModels_iff {φ : L.Sentenceω} :
    φ.IsThinOnNatModels ↔ ¬φ.HasPerfectSetOfPairwiseNonisomorphicNatModels := Iff.rfl

/-- **The bridge to the existing quotient**: a perfect set of pairwise non-isomorphic models
gives continuum-many isomorphism classes.

The antichain lives in the ambient space, while the quotient is over the subtype, so the
transversal is transported through the inclusion — which is exactly what `isoSetoid_eq_comap`
licenses. -/
theorem Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels.continuum_le
    {φ : L.Sentenceω} (h : φ.HasPerfectSetOfPairwiseNonisomorphicNatModels) :
    Cardinal.continuum ≤ #(Quotient (isoSetoid φ)) := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  -- the ambient perfect set sits inside `ModelsOf φ`, so it maps into the subtype quotient
  have hinj : Function.Injective
      (fun x : P => (Quotient.mk (isoSetoid φ) ⟨x.1, hsub x.2⟩)) := by
    intro x y hxy
    have hq : Quotient.mk (isoSetoid φ) ⟨x.1, hsub x.2⟩
        = Quotient.mk (isoSetoid φ) ⟨y.1, hsub y.2⟩ := hxy
    have hr : (isoSetoid φ).r ⟨x.1, hsub x.2⟩ ⟨y.1, hsub y.2⟩ := Quotient.exact hq
    exact Subtype.ext (hanti x.1 x.2 y.1 y.2 (isoSetoid_r_iff.mp hr))
  -- `StructureSpace L` is metrizable but carries no chosen metric, so upgrade the Polish
  -- structure here; the topology is unchanged, hence `hperf` still applies.
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  calc Cardinal.continuum = #P := (hperf.mk_eq_continuum hne).symm
    _ ≤ #(Quotient (isoSetoid φ)) := Cardinal.mk_le_of_injective hinj

end FirstOrder.Language
