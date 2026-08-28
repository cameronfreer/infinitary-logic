/-
Guard: the honest coded-fragment interface must stay reachable from the DEFAULT import surface.

Promotion out of `WIP` puts modules in production *directories*; it does not put them on a
production *import surface*. Commit 7d82fda did the former without the latter, and the interface
compiled and passed every other gate while no bundle imported it — its only importers were the WIP
stubs and a guard script. This file is the regression test for exactly that.

Deliberately tiny: one promised declaration per module boundary
(`Admissible/Family.lean`, `Admissible/CodedFamily.lean`, `Admissible/Theory.lean`,
`Admissible/Fragment/Honest.lean`, `Admissible/Predicates.lean`, `Admissible/HF.lean`).
Do not grow it into a general API smoke test.

Run *after* `lake build`, so the oleans it resolves against are current.
-/
import InfinitaryLogic

#check FirstOrder.Language.FamilyPresentation
#check FirstOrder.Language.AdmissiblePresentation
#check FirstOrder.Language.CodedFamily
#check FirstOrder.Language.AdmissibleFragment
#check FirstOrder.Language.TheoryPresentation.AFinite
#check FirstOrder.Language.AdmissiblePresentation.AFinite
#check FirstOrder.Language.hfAdmissibleFragment
