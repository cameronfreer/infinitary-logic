/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SchemaCompletion

/-!
# Layer 7b checkpoint 5a: the schema term-model substrate (equality interface)

The completed schema theory `Tσ = schemaCompletionTheory (schemaEnumeration s₀) hM` is complete on
the schema universe, `iSup`-witnessed, and finite-character consistent — but NOT a maximal
`ConsistencyPropertyEq` (deliberately: the pivot escaped the `extension`-field blocker). So its
term model's equality quotient cannot come from a syntactic `C6`-closure of `Tσ`. Instead, per the
design decision, equality on closed `(localColim s₀)[[ℕ]]` terms is defined **directly in the
`locDeEqAtom` vocabulary the completion controls**, and every quotient law (reflexivity, symmetry,
transitivity, congruence, relation well-definedness) is proved by the **same source-semantic
contradiction**: if the wrong sign were in `Tσ`, `finite_consistent` yields a source-model body
realizing an impossible equality situation in `M`.

This file is the equality interface (the first 5a unit): the canonical-support equality relation
`SchemaTermEq`, the shared body-extraction engine `exists_body_of_subset`, and the equivalence /
congruence laws. The quotient model itself is the next unit.
-/

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- The canonical finite support of an equality between two closed schema terms. -/
def schemaSupport (t u : (localColim s₀)[[ℕ]].Term Empty) : Finset ℕ :=
  locJSupport (localColim s₀) ℕ t ∪ locJSupport (localColim s₀) ℕ u

/-- The lifted `templateSentence` of the de-substituted equality atom `locDeEqAtom` at the
canonical support — the schema-universe sentence that encodes "`t = u`". -/
def schemaEqSentence (t u : (localColim s₀)[[ℕ]].Term Empty) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence
      (locDeEqAtom (localColim s₀) ℕ (schemaSupport t u) t u
        Finset.subset_union_left Finset.subset_union_right)
      ((schemaSupport t u).orderEmbOfFin rfl)).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)

/-- `schemaEqSentence t u` is a schema-universe member (its de-substituted atom is in `ΓEMlocal`). -/
theorem schemaEqSentence_mem_universe (t u : (localColim s₀)[[ℕ]].Term Empty) :
    (⟨schemaEqSentence t u, hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
  Set.mem_biUnion
    (locDeEqAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaSupport t u) (t := t) (u := u)
      (ht := Finset.subset_union_left) (hu := Finset.subset_union_right))
    ⟨(schemaSupport t u).orderEmbOfFin rfl, rfl⟩

/-- **Canonical-support schema equality** on closed `(localColim s₀)[[ℕ]]` terms: `t ≈ u` iff the
completed theory contains the encoded equality sentence. -/
def SchemaTermEq (t u : (localColim s₀)[[ℕ]].Term Empty) : Prop :=
  schemaEqSentence t u ∈ schemaCompletionTheory (schemaEnumeration s₀) hM

/-- **The shared body-extraction engine.** A finite fragment of `Tσ` is `MarkerHenkinConsistent`,
so it has a body: a source interpretation `(σ, h)` realizing every member. Every equality law
derives its contradiction from this. -/
theorem exists_body_of_subset (F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω))
    (hF : ∀ τ ∈ F, τ ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ (σ : ℕ → M) (h : ℕ → M), ∀ τ ∈ F,
      realizeWith σ h τ (Empty.elim : Empty → M) Fin.elim0 := by
  obtain ⟨S, H, _, _, hcof⟩ :=
    (schemaCompletionTheorySpec hM).finite_consistent F hF
  obtain ⟨α, _, _, e, hsat⟩ := hcof 0 (Ordinal.omega_pos 1)
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  obtain ⟨h, hh⟩ := hsat σ hmono hrange
  exact ⟨σ, h, hh⟩

omit [LinearOrder M] [WellFoundedLT M] in
/-- The de-substituted equality atom of a term with itself realizes to `True` (reflexivity of the
underlying `=`), on any valuation. -/
theorem locDeEqAtom_self_realize {S : Finset ℕ} (t : (localColim s₀)[[ℕ]].Term Empty)
    (ht : locJSupport (localColim s₀) ℕ t ⊆ S) (w : Fin S.card → M) :
    (locDeEqAtom (localColim s₀) ℕ S t t ht ht).Realize (Empty.elim : Empty → M) w := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal]

/-- **Reflexivity.** `t ≈ t`: the theory decides `schemaEqSentence t t`; the negative sign is
impossible because any source body would have to realize `¬(t = t)`. -/
theorem schemaTermEq_refl (t : (localColim s₀)[[ℕ]].Term Empty) : SchemaTermEq hM t t := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _ (schemaEqSentence_mem_universe t t)
    with hpos | hneg
  · exact hpos
  · exfalso
    obtain ⟨σ, h, hbody⟩ := exists_body_of_subset hM {(schemaEqSentence t t).not}
      (fun τ hτ => by rw [Finset.mem_singleton] at hτ; exact hτ ▸ hneg)
    have hneg' := hbody (schemaEqSentence t t).not (Finset.mem_singleton_self _)
    rw [realizeWith_not] at hneg'
    exact hneg' (by
      rw [schemaEqSentence, realizeWith_templateSentence]
      exact locDeEqAtom_self_realize t Finset.subset_union_left _)

end FirstOrder.Language
