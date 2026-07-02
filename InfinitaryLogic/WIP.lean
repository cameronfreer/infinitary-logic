-- The old skolemColim EM term model (kept CI-checked; no longer imported by the local stack)
import InfinitaryLogic.Methods.EMTermModel
-- The local EM extraction bridge (pulls the local stack LocalEMFamily -> LocalColimit ->
-- LocalTower -> LocalSkolem -> LocalEMSupport, plus the proved tail extraction from
-- Conditional/MorleyHanfTransfer)
import InfinitaryLogic.Methods.LocalEMExtraction

/-!
# WIP: the work-in-progress frontier bundle

Root of the **non-default** `InfinitaryLogicWIP` build target: the in-progress
Ehrenfeucht–Mostowski / Skolem-hull realizability construction aimed at discharging
the Morley–Hanf residual `TailTemplateRealizable`. The two imports transitively cover
the whole frontier cluster:

* `Methods/Skolem.lean` → `SkolemColimit.lean` → `SkolemClosure.lean` — the full
  (uncountable) Skolem tower `skolemStage`/`skolemColim` and the countable staged
  family `Γ*`;
* `Methods/EMTermModel.lean` — the EM term model over `(skolemColim L)[[J]]` with the
  staged truth lemma `truthLemmaStage`;
* `Methods/LocalSkolem.lean` → `LocalTower.lean` → `LocalColimit.lean` → `LocalEMFamily.lean` →
  `LocalEMExtraction.lean` — the countable family-restricted re-base (`localSkolem`, the
  mutually recursive `Llocal`/`Γlocal` tower with `skolemNeed`, the countable colimit
  `localColim` with cocone and semantic transport, the countable atom/deForm family `ΓEMlocal`
  with the canonical J-free seeds and the `EMContext`-instantiation membership interface, and
  the extraction bridge `exists_ΓEMlocal_tail_indiscernible`).

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
