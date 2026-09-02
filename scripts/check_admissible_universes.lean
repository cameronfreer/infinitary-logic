/-
Guard: the admissible model-universe boundary, as compiling probes.

The low-level semantic boundary has moved deliberately: `Theoryω.IsSatisfiableIn` selects a carrier
universe, and `finitaryFragment_compactIn` works for any language.  The ambient Barwise interface
has not moved yet: `hfAmbient_compact` still concludes the published universe-zero
`Theoryω.IsSatisfiable` and remains confined to `Language.{0, 0}`.

The result being pinned is therefore three-part: representation is universe-general, finitary
compactness is universe-general with an explicit output level, and the ambient compactness endpoint
is still universe-zero.  This prevents the remaining interface restriction from being read back
onto either syntax coding or Mathlib's first-order compactness.

Probes are stated at EXPLICIT levels, `Language.{1, 2}`, not at generic `u v`. A generic probe
proves nothing here: it would elaborate just as happily if the declarations had been silently
pinned to `Language.{0, 0}`, since the section variables would unify at whatever the definitions
demanded. Explicit levels — and two distinct ones, so a `u = v` collapse cannot hide either —
force the claim to be about universe generality.

Codings are taken as HYPOTHESES rather than constructed. The question is what elaborates at which
levels, and constructing a `FinitaryCoding` for a `Language.{1, 2}` would test countability of that
language instead.

The negative control is the informative half, and it is deliberately COMBINED: one declaration
whose conclusion exhibits the higher-universe representation route while `fail_if_success` rejects
`hfAmbient_compact` at that same language. Split into two declarations the pairing could rot — a
positive that stopped being about universes, next to a negative failing for an unrelated reason,
each still passing. Together they state the boundary in a single breath.

Run with: lake env lean scripts/check_admissible_universes.lean
-/
import InfinitaryLogic.Admissible

namespace FirstOrder.Language

/-! ## Positive: the representation layer is universe-general -/

/-- The ambient presentation itself elaborates at explicitly higher levels.  `noncomputable`
because `hfAmbient` inverts its coding by choice; irrelevant to the universe claim. -/
noncomputable example (L : Language.{1, 2}) (C : FinitaryCoding L) :
    AmbientPresentation.{1, 2, 0, 0} L :=
  hfAmbient C

/-- Adequacy elaborates there. -/
example (L : Language.{1, 2}) (C : FinitaryCoding L) :
    (hfAmbient C).AdequateFor (finitaryFragment L) :=
  hfAmbient_adequate C

/-- The corrected `A`-finiteness characterization elaborates there. -/
example (L : Language.{1, 2}) (C : FinitaryCoding L) {T : L.Theoryω} :
    (hfAmbient C).AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L :=
  hfAmbient_aFinite_iff C

/-! ## Positive: finitary compactness is language-universe general -/

/-- Finite-subtheory models in `Type 3` yield Mathlib's canonical output model in `Type 2` for a
`Language.{1, 2}`.  Distinct explicit levels ensure neither the language nor witness universe can
silently collapse to zero. -/
example (L : Language.{1, 2}) {T : L.Theoryω} (hT : T ⊆ finitaryFragment L)
    (hfin : Theoryω.IsFinitelySatisfiableIn.{1, 2, 3} T) :
    Theoryω.IsSatisfiableIn.{1, 2, 2} T :=
  finitaryFragment_compactIn hT hfin

/-! ## Positive: the satisfiability endpoint at `Language.{0, 0}` -/

/-- The ambient compactness API retains its published universe-zero endpoint. -/
example (L : Language.{0, 0}) (C : FinitaryCoding L) (T : L.Theoryω)
    (hT : (hfAmbient C).ACEnumerable T)
    (hfin : (hfAmbient C).toTheoryPresentation.AFinitelySatisfiable T) : T.IsSatisfiable :=
  hfAmbient_compact C T hT hfin

/-! ## The combined negative control -/

/-- **The remaining boundary, in one declaration.**  At `Language.{1, 2}` the representation route
is available — that is this example's conclusion — while `hfAmbient_compact` is not.

If `hfAmbient_compact` is ever generalized, `fail_if_success` will report that its body succeeded.
That is the correct failure: it means the boundary moved, and this guard is the record of where it
used to be. Update it deliberately rather than deleting the control. -/
example (L : Language.{1, 2}) (C : FinitaryCoding L) :
    (hfAmbient C).AdequateFor (finitaryFragment L) := by
  fail_if_success have := hfAmbient_compact (L := L)
  exact hfAmbient_adequate C

end FirstOrder.Language

open Lean in
run_cmd logInfo "universe boundary guard: OK (representation and finitary compactness elaborate at \
  higher universes; the ambient compactness endpoint remains Language.{0, 0} and is rejected at \
  {1, 2})"
