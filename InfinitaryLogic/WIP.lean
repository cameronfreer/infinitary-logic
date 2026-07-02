-- The countable local Skolem tower (L_Γ pivot): localSkolem + Llocal/Γlocal
import InfinitaryLogic.Methods.LocalTower
-- The EM term model on the colimit Skolem language (truth lemmas, congruence engine)
import InfinitaryLogic.Methods.EMTermModel

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
* `Methods/LocalSkolem.lean` → `LocalTower.lean` — the countable family-restricted
  re-base (`localSkolem`, the mutually recursive `Llocal`/`Γlocal` tower).

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
