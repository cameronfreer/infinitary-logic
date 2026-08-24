/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.PermPolishGroup
import InfinitaryLogic.Descriptive.LogicAction
import InfinitaryLogic.Descriptive.Polish

/-!
# The Polish logic action of `S∞` on the structure space (issue #27, commit 3)

The capstone: the algebraic action of `S∞ = Equiv.Perm ℕ` on `StructureSpace L` (from
`LogicAction.lean`) is **jointly continuous** for the pointwise topology on `Equiv.Perm ℕ`
(`PermPolishGroup.lean`) and the *existing* product topology on `StructureSpace L`
(`Topology.lean`) — packaged as a `ContinuousSMul` instance. Together with the Polish structures
already in place this exhibits `StructureSpace L` as a **Polish `S∞`-space**.

## Main results

- `FirstOrder.Language.continuous_smul_action` and the `ContinuousSMul` instance: the action
  `(σ, c) ↦ σ • c` is jointly continuous. No countability or relationality hypothesis is needed.
- `FirstOrder.Language.isPolishSInftySpace`: under `[Countable (Σ l, L.Relations l)]`,
  `StructureSpace L` is a Polish `S∞`-space — `Equiv.Perm ℕ` is a Polish topological group,
  `StructureSpace L` is Polish, and the action is continuous.

## Design

Joint continuity factors coordinatewise, exactly as anticipated: for a fixed relation query
`⟨R, v⟩`, the value `(σ • c) ⟨R, v⟩ = c ⟨R, σ⁻¹ ∘ v⟩` reads `c` at a query whose tuple depends on
`σ` through the finitely many *continuous* evaluations `σ⁻¹ (v i)`. On the clopen neighborhood where
those are frozen, the map reduces to a single continuous evaluation of `c`. The countability
hypothesis for Polishness of `StructureSpace L` lives only in the final packaging — never on the
action, the algebra, or the orbit equivalence.
-/

open Topology Filter

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-- **Per-query continuity.** For a fixed relation query `⟨R, v⟩`, the map
`(σ, c) ↦ (σ • c) ⟨R, v⟩` is continuous: near `(σ₀, c₀)` the tuple `σ⁻¹ ∘ v` is frozen at
`i ↦ σ₀⁻¹ (v i)` on a clopen neighborhood, where the map is the single evaluation `c ↦ c ⟨R, m⟩`. -/
theorem continuous_smul_query (R : Σ l, L.Relations l) (v : Fin R.1 → ℕ) :
    Continuous (fun p : Equiv.Perm ℕ × StructureSpace L => (p.1 • p.2) ⟨R, v⟩) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨σ₀, c₀⟩
  set m : Fin R.1 → ℕ := fun i => σ₀⁻¹ (v i) with hm
  have hcont : ContinuousAt (fun p : Equiv.Perm ℕ × StructureSpace L => p.2 ⟨R, m⟩) (σ₀, c₀) :=
    ((continuous_apply (⟨R, m⟩ : RelQuery L)).comp continuous_snd).continuousAt
  refine hcont.congr ?_
  have hmem : ∀ i : Fin R.1,
      {p : Equiv.Perm ℕ × StructureSpace L | p.1⁻¹ (v i) = m i} ∈ 𝓝 (σ₀, c₀) := by
    intro i
    have hopen : IsOpen {p : Equiv.Perm ℕ × StructureSpace L | p.1⁻¹ (v i) = m i} :=
      (isOpen_discrete ({m i} : Set ℕ)).preimage
        ((NatPerm.continuous_inv_apply (v i)).comp continuous_fst)
    exact hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, hm])
  filter_upwards [Filter.iInter_mem.mpr hmem] with p hp
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hp
  have hmw : (⇑p.1⁻¹ ∘ v) = m := by funext i; exact hp i
  show p.2 ⟨R, m⟩ = (p.1 • p.2) ⟨R, v⟩
  rw [logicAction_apply, hmw]

/-- **Joint continuity** of the logic action `(σ, c) ↦ σ • c`. -/
theorem continuous_smul_action :
    Continuous fun p : Equiv.Perm ℕ × StructureSpace L => p.1 • p.2 := by
  apply continuous_pi
  intro q
  obtain ⟨R, v⟩ := q
  exact continuous_smul_query R v

/-- The logic action of `S∞` on `StructureSpace L` is jointly continuous. -/
instance instContinuousSMulPermStructureSpace :
    ContinuousSMul (Equiv.Perm ℕ) (StructureSpace L) :=
  ⟨continuous_smul_action⟩

/-- **Packaged Polish `S∞`-space.** For a countable relational vocabulary, `StructureSpace L` is a
Polish `S∞`-space: `Equiv.Perm ℕ` is a Polish topological group, `StructureSpace L` is Polish, and
the logic action is jointly continuous. The countability hypothesis appears here and nowhere
upstream — the action, its `MulAction` laws, and the orbit/isomorphism identification are all
hypothesis-free. -/
theorem isPolishSInftySpace [Countable (Σ l, L.Relations l)] :
    PolishSpace (Equiv.Perm ℕ) ∧ IsTopologicalGroup (Equiv.Perm ℕ) ∧
      PolishSpace (StructureSpace L) ∧ ContinuousSMul (Equiv.Perm ℕ) (StructureSpace L) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end FirstOrder.Language
