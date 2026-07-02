/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMFamily
import InfinitaryLogic.Conditional.MorleyHanfTransfer

/-!
# The local EM context (first layer): the extraction bridge

Start of the `EMContext` re-base over the countable `localColim s₀`. This file's first layer is
the **extraction bridge**: instantiating the proved tail extraction
(`morleyHanfExtractionTail_holds`) at the countable local family `ΓEMlocal` — via its enumeration
`exists_ΓEMlocalEnum` — yields, inside any source model of size `≥ ℶ_{ω₁}` (the honest
Morley–Hanf premise), a pairwise-distinct sequence that is tail-indiscernible on the *whole*
family. This is exactly the `hind` + distinctness data of the future local `EMContext`; its
`atom_mem`/`rel_mem`/deForm-closure obligations are already discharged by the `ΓEMlocal`
membership interface (`locDeEqAtom_mem_ΓEMlocal` etc. in `LocalEMFamily.lean`). What could not
even be *stated* usefully over the uncountable `skolemColim` atom diagram is here a two-line
composition — the payoff of the whole L_Γ pivot.

Import-layering note: this Methods file imports `Conditional/MorleyHanfTransfer.lean` — a
deliberate, temporary inversion of the Core→Methods→Conditional axis. The consumed theorem
`morleyHanfExtractionTail_holds` is *proved* (sorry-free, axiom-clean), not a conditional
hypothesis; once the frontier stabilizes it should migrate out of `Conditional/` and this
inversion disappears.

Next layers (subsequent chunks): local deep interpretation and realize bridges, the local
quotient with atom congruence, the `skolemNeedSymbol` witness term, and the family-membership-
carrying restricted truth lemma.
-/

namespace FirstOrder.Language

variable (s₀ : LocalStage)

/-- **The extraction bridge**: inside any `s₀.Lang`-structure of size `≥ ℶ_{ω₁}`, there is a
pairwise-distinct sequence that is tail-indiscernible (over `localColimStructure`) on the whole
countable local family `ΓEMlocal s₀`. Discharges the future local `EMContext`'s `hind` and
distinctness obligations in one stroke. -/
theorem exists_ΓEMlocal_tail_indiscernible (M : Type) [s₀.Lang.Structure M] [Nonempty M]
    (hSize : Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    ∃ a : ℕ → M,
      (∀ i j : ℕ, i ≠ j → a i ≠ a j) ∧
      @IsLomega1omegaIndiscernibleOnTail (localColim s₀) M (localColimStructure s₀) a
        (ΓEMlocal s₀) := by
  haveI : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  letI : (localColim s₀).Structure M := localColimStructure s₀
  obtain ⟨e, he⟩ := exists_ΓEMlocalEnum s₀
  obtain ⟨a, hinj, hind⟩ := morleyHanfExtractionTail_holds (L' := localColim s₀) e M hSize
  refine ⟨a, hinj, ?_⟩
  rw [he]
  exact hind

end FirstOrder.Language
