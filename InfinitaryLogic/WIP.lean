-- The old skolemColim EM term model (kept CI-checked; no longer imported by the local stack)
import InfinitaryLogic.Methods.EMTermModel
-- The local EM extraction bridge (its Conditional/MorleyHanfTransfer import stays isolated here)
import InfinitaryLogic.Methods.LocalEMExtraction
-- The pure local stack: semantic layer onward (LocalEMFamily -> LocalColimit -> LocalTower ->
-- LocalSkolem -> LocalEMSupport, plus the explicit Henkin.Construction realize lemmas)
import InfinitaryLogic.Methods.LocalEMContext

/-!
# WIP: the work-in-progress frontier bundle

Root of the **non-default** `InfinitaryLogicWIP` build target: the in-progress
Ehrenfeucht–Mostowski / Skolem-hull realizability construction aimed at discharging
the Morley–Hanf residual `TailTemplateRealizable`. Three imports are needed — since the
local stack no longer imports `EMTermModel`, no single module covers the cluster:
the old `skolemColim` track (`EMTermModel`), the extraction bridge (`LocalEMExtraction`,
isolating the Conditional import), and the pure local stack (`LocalEMContext`). Together
they transitively cover:

* `Methods/Skolem.lean` → `SkolemColimit.lean` → `SkolemClosure.lean` — the full
  (uncountable) Skolem tower `skolemStage`/`skolemColim` and the countable staged
  family `Γ*`;
* `Methods/EMTermModel.lean` — the EM term model over `(skolemColim L)[[J]]` with the
  staged truth lemma `truthLemmaStage`;
* `Methods/LocalEMSupport.lean` → `LocalSkolem.lean` → `LocalTower.lean` → `LocalColimit.lean`
  → `LocalEMFamily.lean` → {`LocalEMExtraction.lean`, `LocalEMContext.lean`} — the countable
  family-restricted re-base (shared generic support, `localSkolem`, the mutually recursive
  `Llocal`/`Γlocal` tower with `skolemNeed`, the countable colimit `localColim` with cocone and
  semantic transport, the countable atom/deForm family `ΓEMlocal` with the canonical J-free
  seeds and the `EMContext`-instantiation membership interface, the extraction bridge
  `exists_ΓEMlocal_tail_indiscernible`, and the generic deep-interpretation/realize-bridge
  semantic layer).

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
