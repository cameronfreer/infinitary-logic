/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.ModelTheory.Basic

/-!
# Coding Space for Countable Structures

This file defines the space of countable relational L-structures on ℕ, coded as
functions from relation queries to Bool. This is the first step toward proving that
satisfaction of Lω₁ω sentences is Borel.

## Main Definitions

- `RelQuery L`: Index type for relation queries (which relation, which tuple).
- `StructureSpace L`: The coding space `RelQuery L → Bool`.
- `StructureSpace.toStructure`: Decode a code into an L-structure on ℕ.
- `StructureSpace.ofStructure`: Encode a structure into a code.

## Main Results

- `StructureSpace.relMap_toStructure`: Relation holding in the decoded structure
  corresponds to the code returning `true`.
- `StructureSpace.toStructure_ofStructure`: Round-trip from structure to code to structure
  preserves relation satisfaction.
-/

universe u v

namespace FirstOrder

namespace Language

open Structure

variable (L : Language.{u, v})

/-- A relation query: a choice of relation symbol and a tuple of natural numbers.
This indexes the "coordinates" of the structure space. -/
def RelQuery := Σ (R : Σ l, L.Relations l), (Fin R.1 → ℕ)

variable {L}

instance [Countable (Σ l, L.Relations l)] : Countable (RelQuery L) := by
  unfold RelQuery
  infer_instance

/-- The coding space for countable L-structures on ℕ: for each relation query,
does the relation hold on that tuple? -/
def StructureSpace (L : Language.{u, v}) := RelQuery L → Bool

namespace StructureSpace

/-- Decode a code into an L-structure on ℕ.
Relations are determined by the code; functions are eliminated by `IsRelational`. -/
noncomputable def toStructure [L.IsRelational]
    (c : StructureSpace L) : L.Structure ℕ where
  funMap := fun f => isEmptyElim f
  RelMap := fun {_} R v => c ⟨⟨_, R⟩, v⟩ = true

/-- The relation holding in the decoded structure corresponds to the code value. -/
@[simp]
theorem relMap_toStructure [L.IsRelational] (c : StructureSpace L)
    {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap _ _ c.toStructure _ R v ↔ c ⟨⟨l, R⟩, v⟩ = true :=
  Iff.rfl

/-- Encode an L-structure on ℕ into a code.
Takes an explicit structure instance rather than using the typeclass. -/
noncomputable def ofStructure [L.IsRelational]
    (inst : L.Structure ℕ) : StructureSpace L :=
  fun ⟨⟨_, R⟩, v⟩ => @decide _ (Classical.dec (@Structure.RelMap _ _ inst _ R v))

/-- Round-trip: decoding the code of a structure preserves relation satisfaction. -/
theorem toStructure_ofStructure [L.IsRelational]
    (inst : L.Structure ℕ) {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap _ _ (ofStructure inst).toStructure _ R v ↔
    @Structure.RelMap _ _ inst _ R v := by
  simp only [relMap_toStructure, ofStructure, decide_eq_true_eq]

/-- Round-trip: encoding a decoded structure recovers the original code. -/
theorem ofStructure_toStructure [L.IsRelational]
    (c : StructureSpace L) : ofStructure (c.toStructure) = c := by
  funext ⟨⟨l, R⟩, v⟩
  simp only [ofStructure, relMap_toStructure]
  cases c ⟨⟨l, R⟩, v⟩ <;> simp

end StructureSpace

end Language

end FirstOrder
