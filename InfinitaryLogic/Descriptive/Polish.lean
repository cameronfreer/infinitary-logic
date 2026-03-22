/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.Topology
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Architect

/-!
# Polish Space and Borel Space Structure on the Structure Space

This file proves that `StructureSpace L` is a Polish space, a Borel space, and
a standard Borel space when the language has countably many relation symbols.

## Strategy

`StructureSpace L = RelQuery L → Bool` with the product topology. When
`RelQuery L` is countable, `Encodable.ofCountable` provides an encoding, and
Mathlib's instances for products of discrete spaces give:
- `CompactSpace`, `MetrizableSpace`, `SecondCountableTopology` (from `Pi.*`)
- `IsCompletelyMetrizableSpace` (compact + metrizable → complete)
- `PolishSpace` = `SecondCountableTopology` + `IsCompletelyMetrizableSpace`
- `BorelSpace` (product σ-algebra = Borel σ-algebra for second-countable spaces)
- `StandardBorelSpace` (from `PolishSpace` + `BorelSpace`)

Since `StructureSpace L` is a `def` (not `abbrev`), type class resolution cannot
see through it. We provide the intermediate instances explicitly.

## Main Results

- `PolishSpace (StructureSpace L)`: The structure space is Polish.
- `BorelSpace (StructureSpace L)`: The product σ-algebra equals the Borel σ-algebra.
- `StandardBorelSpace (StructureSpace L)`: The structure space is standard Borel.
- Analogous instances for the pair space `StructureSpace L × StructureSpace L`.
-/

universe u v

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) [Countable (Σ l, L.Relations l)]

/-- `RelQuery L` is encodable when the language has countably many relation symbols.
This is the key ingredient for all topological instances. -/
noncomputable instance : Encodable (RelQuery L) :=
  Encodable.ofCountable _

-- Bridge instances: StructureSpace L is a def, so TC can't unfold it.
-- We explicitly provide what Mathlib proves for `RelQuery L → Bool`.

instance : CompactSpace (StructureSpace L) := by
  unfold StructureSpace; infer_instance

instance : TopologicalSpace.MetrizableSpace (StructureSpace L) := by
  unfold StructureSpace; infer_instance

instance : SecondCountableTopology (StructureSpace L) := by
  unfold StructureSpace; infer_instance

instance : TopologicalSpace.IsCompletelyMetrizableSpace (StructureSpace L) := by
  unfold StructureSpace; infer_instance

/-- The structure space is Polish: second-countable and completely metrizable.
This follows from `StructureSpace L = RelQuery L → Bool` being a countable product
of finite discrete spaces, hence compact and metrizable. -/
@[blueprint "thm:structure-space-polish"
  (title := /-- Structure space is Polish -/)
  (statement := /-- For a countable relational language, the structure space is a Polish space. -/)
  (proof := /-- The structure space is a countable product of copies of $\{0,1\}$, which is compact and metrizable, hence Polish. -/)
  (uses := ["def:structure-space"])]
instance : PolishSpace (StructureSpace L) := PolishSpace.mk

/-- The product σ-algebra on the structure space equals the Borel σ-algebra. -/
instance : BorelSpace (StructureSpace L) := by
  unfold StructureSpace at *; infer_instance

/-- The structure space is standard Borel (Polish + Borel). -/
instance : StandardBorelSpace (StructureSpace L) := inferInstance

/-- The pair space `StructureSpace L × StructureSpace L` is Polish. -/
instance : PolishSpace (StructureSpace L × StructureSpace L) := inferInstance

/-- The pair space is Borel. -/
instance : BorelSpace (StructureSpace L × StructureSpace L) := inferInstance

/-- The pair space is standard Borel. -/
instance : StandardBorelSpace (StructureSpace L × StructureSpace L) := inferInstance

end Language

end FirstOrder
