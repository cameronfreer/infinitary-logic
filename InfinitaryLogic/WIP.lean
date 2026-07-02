-- The countable local atom/deForm family GammaEMlocal (imports the whole frontier:
-- LocalColimit -> LocalTower -> LocalSkolem and EMTermModel -> SkolemClosure chain)
import InfinitaryLogic.Methods.LocalEMFamily

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
* `Methods/LocalSkolem.lean` → `LocalTower.lean` → `LocalColimit.lean` → `LocalEMFamily.lean` —
  the countable family-restricted re-base (`localSkolem`, the mutually recursive
  `Llocal`/`Γlocal` tower with `skolemNeed`, the countable colimit `localColim` with cocone and
  semantic transport, and the countable atom/deForm family `ΓEMlocal` with the canonical J-free
  seeds and the `EMContext`-instantiation membership interface).

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
