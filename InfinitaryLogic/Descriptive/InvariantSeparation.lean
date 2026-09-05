/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.PolishAction
import InfinitaryLogic.Descriptive.LopezEscobar

/-!
# Invariant analytic separation

An analytic set disjoint from an *invariant* analytic set can be separated from it by an
**invariant** Borel set (`invariant_analytic_separation`).  The proof iterates ordinary Lusin
separation (`AnalyticSet.measurablySeparable`) with the saturation of the separator under the
permutation action: each saturation is analytic (the action is continuous) and still disjoint
from the invariant excluded set, so it can be separated again; the union of the ω stages is
Borel and invariant.  No Borelness of the isomorphism relation is used.

Composed with López–Escobar (`lopez_escobar`), the invariant separator is the model class of one
`L_{ω₁ω}`-sentence: `sentence_separates_analytic_classes`.

## Classical background

The separation argument is the same iterative separation-and-saturation construction as Gao,
*Invariant Descriptive Set Theory* (CRC Press, 2009), Lemma 5.4.6, specialized to the
isomorphism action.  Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016),
Corollary 4.3.6 and Theorem 4.3.7, gives the invariant-separation and López–Escobar background
through interpolation (Corollary 4.24 and Theorem 4.25 in the Fall 2013 lecture notes).
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}}

/-- The saturation of a set of structures under the permutation action. -/
def saturation (A : Set (StructureSpace L)) : Set (StructureSpace L) :=
  (fun p : Equiv.Perm ℕ × StructureSpace L => p.1 • p.2) '' (Set.univ ×ˢ A)

theorem mem_saturation {A : Set (StructureSpace L)} {y : StructureSpace L} :
    y ∈ saturation A ↔ ∃ (σ : Equiv.Perm ℕ) (x : StructureSpace L), x ∈ A ∧ σ • x = y := by
  simp only [saturation, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Prod.exists]

theorem subset_saturation (A : Set (StructureSpace L)) : A ⊆ saturation A := fun x hx =>
  mem_saturation.mpr ⟨1, x, hx, one_smul _ _⟩

/-- The saturation of an analytic set is analytic: the action is continuous. -/
theorem analyticSet_saturation [Countable (Σ n, L.Relations n)] {A : Set (StructureSpace L)}
    (hA : AnalyticSet A) : AnalyticSet (saturation A) := by
  simpa only [saturation, Set.univ_prod] using
    (hA.preimage continuous_snd).image_of_continuous continuous_smul_action

theorem saturation_invariant (A : Set (StructureSpace L)) : ActionInvariant (saturation A) := by
  intro σ x
  constructor
  · intro hx
    obtain ⟨τ, y, hy, rfl⟩ := mem_saturation.mp hx
    exact mem_saturation.mpr ⟨σ * τ, y, hy, mul_smul σ τ y⟩
  · intro hx
    obtain ⟨τ, y, hy, hxy⟩ := mem_saturation.mp hx
    refine mem_saturation.mpr ⟨σ⁻¹ * τ, y, hy, ?_⟩
    rw [mul_smul, hxy, inv_smul_smul]

theorem disjoint_saturation {A B : Set (StructureSpace L)} (hB : ActionInvariant B)
    (hd : Disjoint B A) : Disjoint B (saturation A) := by
  apply Set.disjoint_left.mpr
  intro z hz hza
  obtain ⟨σ, x, hx, rfl⟩ := mem_saturation.mp hza
  exact Set.disjoint_left.mp hd ((hB σ x).mpr hz) hx

/-- **Invariant analytic separation.**  An analytic set disjoint from an invariant analytic set
is contained in an invariant Borel set disjoint from it.  Iterated saturation; no Borel
isomorphism relation is used. -/
theorem invariant_analytic_separation [Countable (Σ n, L.Relations n)]
    {A B : Set (StructureSpace L)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hinv : ActionInvariant B) (hd : Disjoint A B) :
    ∃ C, A ⊆ C ∧ Disjoint B C ∧ MeasurableSet C ∧ ActionInvariant C := by
  classical
  obtain ⟨D₀, hA₀, hB₀, hm₀⟩ := hA.measurablySeparable hB hd
  let Good := {D : Set (StructureSpace L) // MeasurableSet D ∧ Disjoint B D}
  have next_exists (D : Good) : ∃ E : Good, saturation D.val ⊆ E.val := by
    have hdis := disjoint_saturation hinv D.property.2
    obtain ⟨E, hDE, hBE, hmE⟩ :=
      (analyticSet_saturation D.property.1.analyticSet).measurablySeparable hB hdis.symm
    exact ⟨⟨E, hmE, hBE⟩, hDE⟩
  choose next hnext using next_exists
  let D : ℕ → Good := Nat.rec ⟨D₀, hm₀, hB₀⟩ (fun _ prev => next prev)
  have hstep (n : ℕ) : saturation (D n).val ⊆ (D (n + 1)).val := hnext (D n)
  refine ⟨⋃ n, (D n).val, ?_, ?_, ?_, ?_⟩
  · exact hA₀.trans (Set.subset_iUnion (fun n => (D n).val) 0)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact Set.disjoint_left.mp (D n).property.2 hx hn
  · exact MeasurableSet.iUnion fun n => (D n).property.1
  · have forward (σ : Equiv.Perm ℕ) (x : StructureSpace L)
        (hx : x ∈ ⋃ n, (D n).val) : σ • x ∈ ⋃ n, (D n).val := by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n + 1, hstep n (mem_saturation.mpr ⟨σ, x, hn, rfl⟩)⟩
    intro σ x
    refine ⟨forward σ x, ?_⟩
    intro hx
    simpa only [inv_smul_smul] using forward σ⁻¹ (σ • x) hx

/-- **A sentence separates an analytic class from a disjoint invariant analytic class**, by
López–Escobar applied to the invariant separator. -/
theorem sentence_separates_analytic_classes [L.IsRelational] [Countable (Σ n, L.Relations n)]
    {A B : Set (StructureSpace L)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hinv : ActionInvariant B) (hd : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ ModelsOf θ ∧ Disjoint B (ModelsOf θ) := by
  obtain ⟨C, hAC, hBC, hmC, hiC⟩ := invariant_analytic_separation hA hB hinv hd
  obtain ⟨θ, hθ⟩ := lopez_escobar hmC ((actionInvariant_iff_isomorphismInvariant C).mp hiC)
  exact ⟨θ, hθ ▸ hAC, hθ ▸ hBC⟩

end FirstOrder.Language
