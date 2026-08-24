/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.GandyHarrington
import InfinitaryLogic.Descriptive.PerfectAntichain
import Architect

/-!
# Silver's dichotomy delivered as an ambient Cantor antichain

`silver_core_polish` speaks about a Polish space and an equivalence relation on all of it.  The
consumers here have neither: the relation of interest lives on a *Borel subset* `A` of a Polish
space, and the antichain has to end up in the *ambient* space, since that is where perfectness is
a meaningful notion (see `Descriptive/StructureIsoSetoid.lean`).  Bridging that gap is the same
four-step argument every time, so it is factored once:

1. `A` is Borel, hence clopenable: there is a finer Polish topology `t'` making `A` clopen.
2. Closed in a Polish topology makes the subtype `↥A` Polish, and `t' ≤ t` means the two
   topologies have the same Borel sets — so the *given* measurable structure is still the Borel
   one, and the relation's measurability hypothesis is unaffected by the refinement.
3. `silver_core_polish` applies on `↥A`, giving either a countable quotient or a Cantor antichain
   there.
4. The antichain returns to the ambient space in two moves: along the inclusion
   (`HasCantorAntichainOn.of_subtype`) and then down to the coarser ambient topology
   (`HasCantorAntichainOn.mono_topology`).

Step 4 is why nothing here needs perfectness to survive coarsening — which it does not.  Only the
*Cantor* form is coarsened, where continuity is the single topological clause; perfectness is
recovered afterwards, ambiently, by `HasCantorAntichainOn.hasPerfectAntichainOn`.

The relation Silver is applied to need not be the one the antichain is claimed for.  It may be any
*coarser* relation `s` on the subtype, with `hrs` recording that the ambient relation refines it;
the antichain then transfers by `HasCantorAntichainOn.mono_relation`.  That slack is not
decoration — it is exactly the Scott-height stratification's shape, where the Borel relation Silver
sees is back-and-forth equivalence at some level and the antichain is wanted for isomorphism.
Taking `s` to be the pullback itself and `hrs := fun _ _ => id` recovers the plain case.
-/

open MeasureTheory

universe u

variable {X : Type u}

/-- **Silver for a closed subset**, with the antichain delivered in the ambient space.

The refinement-free half of the pipeline: `A` is already closed, so the subtype is Polish outright
and no topology has to be moved afterwards. -/
theorem silver_countable_or_cantorAntichain_of_isClosed
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : IsClosed A) (R : Setoid X) (s : Setoid ↥A)
    (hrs : ∀ x y : ↥A, R.r x.1 y.1 → s.r x y)
    (hs : MeasurableSet {p : ↥A × ↥A | s.r p.1 p.2}) :
    Countable (Quotient s) ∨ HasCantorAntichainOn R A := by
  have : PolishSpace ↥A := hA.polishSpace
  -- a metric, not just metrizability, is what `silver_core_polish` asks for; the topology is
  -- unchanged, so the witness it returns is continuous for the subspace topology as required
  let := TopologicalSpace.upgradeIsCompletelyMetrizable ↥A
  rcases silver_core_polish s hs with hcount | ⟨f, hcont, -, hineq⟩
  · exact Or.inl hcount
  · exact Or.inr (HasCantorAntichainOn.of_subtype
      (HasCantorAntichainOn.mono_relation hrs ⟨f, hcont, fun _ => Set.mem_univ _, hineq⟩))

/-- **Silver for a Borel subset**, with the antichain delivered in the ambient space.

`A` is only assumed Borel, so a clopenable refinement `t'` is taken first.  The three instance
arguments handed to the closed case are the ones that actually change with the topology:
`PolishSpace` at `t'` comes from the refinement, and `BorelSpace` at `t'` holds because a finer
Polish topology has the same Borel sets.  The measurable structure itself never moves, which is
why `hs` — a statement about the subtype's measurable space, not its topology — needs no
adjustment. -/
theorem silver_countable_or_cantorAntichain
    [t : TopologicalSpace X] [hX : PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : MeasurableSet A) (R : Setoid X) (s : Setoid ↥A)
    (hrs : ∀ x y : ↥A, R.r x.1 y.1 → s.r x y)
    (hs : MeasurableSet {p : ↥A × ↥A | s.r p.1 p.2}) :
    Countable (Quotient s) ∨ HasCantorAntichainOn R A := by
  obtain ⟨t', hle, ht', hclosed, -⟩ := hA.isClopenable
  have hborel : ‹MeasurableSpace X› = @borel X t' := by
    rw [borel_eq_borel_of_le ht' hX hle]
    exact BorelSpace.measurable_eq
  -- supplied by `@`-application rather than by `letI`: a local topology instance would be picked
  -- up by every later elaboration, including the goal's own `HasCantorAntichainOn`
  rcases @silver_countable_or_cantorAntichain_of_isClosed X t' ht' _ ⟨hborel⟩ A hclosed R s hrs hs
    with hcount | hcantor
  · exact Or.inl hcount
  · exact Or.inr (hcantor.mono_topology hle)
