/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment

/-!
# Admissible fragment from a bare compactness hypothesis

`admissibleFragmentOfUniv` constructs an `AdmissibleFragment L` with
`formulas := Set.univ` from a bare compactness hypothesis. All closure fields
are trivial because `Set.univ` is trivially closed under everything.

This is a **packaging** constructor, not a substantive theorem: the hard
content (the compactness property) is assumed, not derived. The intended
downstream use is to provide an `AdmissibleFragment L[[J]]` for
Ehrenfeucht–Mostowski realization, where `L[[J]]`-compactness is packaged
as a hypothesis that a future project may eventually prove.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- An admissible fragment on the full universe of sentences, built from a bare
compactness hypothesis. All closure fields are trivial because `formulas` is
`Set.univ`. The `height` is taken as a parameter (any ordinal `> ω` suffices).

This is a **packaging** constructor: the hard content (compactness) is assumed
as `hCompact`, not derived from any prior fragment or admissibility argument.
Callers that have a `FullBarwiseFragment L` can supply `B.height` and
`B.height_gt_omega` for the ordinal parameters. -/
noncomputable def admissibleFragmentOfUniv
    (height : Ordinal) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L.Sentenceω,
      (∀ F : Set L.Sentenceω, F.Finite → F ⊆ S →
        ∃ (M : Type) (_ : L.Structure M), Theoryω.Model F M) →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model S M) :
    AdmissibleFragment L where
  formulas := Set.univ
  height := height
  height_gt_omega := h_height
  closed_neg := fun _ _ => trivial
  closed_imp := fun _ _ _ _ => trivial
  closed_iInf := fun _ _ => trivial
  closed_iSup := fun _ _ => trivial
  closed_quantifier_instance := fun _ _ _ => trivial
  falsum_mem := trivial
  closed_imp_left := fun _ _ _ => trivial
  closed_imp_right := fun _ _ _ => trivial
  closed_iInf_component := fun _ _ _ => trivial
  closed_iSup_component := fun _ _ _ => trivial
  compact := fun S _ hfin =>
    hCompact S fun F hFfin hFS => hfin F (Set.subset_univ F) hFfin hFS

@[simp]
theorem admissibleFragmentOfUniv_formulas
    {height : Ordinal} {h_height : Ordinal.omega0 < height}
    {hCompact : ∀ S : Set L.Sentenceω,
      (∀ F : Set L.Sentenceω, F.Finite → F ⊆ S →
        ∃ (M : Type) (_ : L.Structure M), Theoryω.Model F M) →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model S M} :
    (admissibleFragmentOfUniv height h_height hCompact).formulas = Set.univ := rfl

end Language

end FirstOrder
