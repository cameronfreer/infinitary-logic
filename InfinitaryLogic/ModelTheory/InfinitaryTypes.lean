/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Operations

/-!
# Complete infinitary types and small models

The general types API of the countably-many-types project (issue #11): the complete
`L_{ω₁ω}`-type of a finite tuple over the empty set (`infinitaryType`), the family of realized
types at each arity (`RealizedInfinitaryTypes`), and the smallness predicate
(`Lomega1omegaSmall`: countably many realized types at every arity).

Smallness DESCENDS along reducts (`Lomega1omegaSmall.of_expansion` — each reduct type is the
preimage of an expansion type under `mapLanguage`, so the realized reduct types are a countable
image); it does NOT ascend through arbitrary expansions, which is why the arbitrary-language
endpoint of issue #11 must go through a canonical uniform expansion rather than this lemma.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- The complete infinitary type of a tuple over the empty set: all `L_{ω₁ω}`-formulas (in `n`
free variables) it realizes. -/
def infinitaryType (M : Type w) [L.Structure M] {n : ℕ} (a : Fin n → M) :
    Set (L.BoundedFormulaω Empty n) :=
  { ψ | ψ.Realize Empty.elim a }

/-- The realized complete types of `M` at arity `n`. -/
def RealizedInfinitaryTypes (M : Type w) [L.Structure M] (n : ℕ) :
    Set (Set (L.BoundedFormulaω Empty n)) :=
  Set.range fun a : Fin n → M => infinitaryType M a

/-- **Smallness**: `M` realizes only countably many complete `L_{ω₁ω}`-types, across all finite
arities. -/
def Lomega1omegaSmall (M : Type w) [L.Structure M] : Prop :=
  ∀ n, (RealizedInfinitaryTypes (L := L) M n).Countable

theorem infinitaryType_mem_realizedInfinitaryTypes (M : Type w) [L.Structure M] {n : ℕ}
    (a : Fin n → M) : infinitaryType M a ∈ RealizedInfinitaryTypes (L := L) M n :=
  ⟨a, rfl⟩

/-- **Smallness descends along reducts**: if `M` is small as an `L'`-structure and `g : L →ᴸ L'`
is an expansion on `M`, then `M` is small as an `L`-structure. (The converse FAILS for
arbitrary expansions — new symbols can realize new types.) -/
theorem Lomega1omegaSmall.of_expansion {L' : Language.{u, v}} (g : L →ᴸ L')
    {M : Type w} [L.Structure M] [L'.Structure M] [g.IsExpansionOn M]
    (h : Lomega1omegaSmall (L := L') M) : Lomega1omegaSmall (L := L) M := by
  intro n
  have hmap : RealizedInfinitaryTypes (L := L) M n
      = (fun p : Set (L'.BoundedFormulaω Empty n) =>
          {ψ : L.BoundedFormulaω Empty n | ψ.mapLanguage g ∈ p}) ''
        RealizedInfinitaryTypes (L := L') M n := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨infinitaryType M a, ⟨a, rfl⟩, ?_⟩
      ext ψ
      exact BoundedFormulaω.realize_mapLanguage g ψ Empty.elim a
    · rintro ⟨p', ⟨a, rfl⟩, rfl⟩
      refine ⟨a, ?_⟩
      ext ψ
      exact (BoundedFormulaω.realize_mapLanguage g ψ Empty.elim a).symm
  rw [hmap]
  exact ((h n).image _)

end Language

end FirstOrder
