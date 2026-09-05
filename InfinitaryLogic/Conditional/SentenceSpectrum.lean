/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.SilverAntichain
import InfinitaryLogic.Descriptive.SentenceRecovery
import InfinitaryLogic.Descriptive.SentenceObservables
import Architect

/-!
# The sentence-spectrum characterization of thinness

For a Borel class `C` of coded structures over a countable relational language,

  `IsThinOn (structureIsoSetoid L) C ↔ ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable`

(`thin_iff_countable_sentence_spectra`): `C` carries no perfect set of pairwise non-isomorphic
structures exactly when every countable list of `L_{ω₁ω}`-sentences has only countably many
truth sequences realized on `C`.  The class need **not** be isomorphism-invariant, and no
Borelness of isomorphism is assumed.

* Thin ⟹ countable spectra: Silver (`silver_countable_or_cantorAntichain`) is applied to the
  kernel of the Borel truth-sequence map, a Borel equivalence relation coarser than isomorphism;
  its Cantor alternative is an isomorphism antichain, which thinness refutes.
* Countable spectra ⟹ thin: on a Borel Cantor antichain the sentences recover the parameter
  (`sentences_recover_cantor`), so the spectrum of that list is uncountable.

Sentence form: `Sentenceω.isThinOnNatModels_iff_countable_sentence_spectra`, with Borelness of
the model class discharged.

## Not claimed

Countable spectra say `∀ θ, countable image`.  They do not supply one list `θ` that classifies
isomorphism on `C`: a Borel complete invariant together with thinness forces countably many
classes (`countable_iso_classes_of_thin_borel_classifiable`).  Nothing here establishes the
spectrum bound for any particular sentence; applications must supply their own smallness
argument.  This module lives in `Conditional/` beside
`MorleyPerfect.lean` because it consumes the Silver adapter.
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- **Silver on truth sequences.**  For a Borel class and a sentence list, either the realized
truth sequences are countable or the class contains a continuous Cantor isomorphism antichain.
Silver is applied to equality of truth sequences, coarser than isomorphism. -/
theorem sentence_spectrum_countable_or_cantor (C : Set (StructureSpace L))
    (hC : MeasurableSet C) (θ : ℕ → L.Sentenceω) :
    (sentenceTheory θ '' C).Countable ∨ HasCantorAntichainOn (structureIsoSetoid L) C := by
  let f : C → (ℕ → Bool) := fun c => sentenceTheory θ c.val
  have hf : Measurable f := (measurable_sentenceTheory θ).comp measurable_subtype_coe
  rcases silver_countable_or_cantorAntichain hC (structureIsoSetoid L) (Setoid.ker f)
      (fun _ _ h => sentenceTheory_eq_of_iso θ h)
      (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd))
      with hc | ha
  · left
    have := hc
    have : Countable (Set.range f) :=
      (Setoid.quotientKerEquivRange f).symm.injective.countable
    have he : Set.range f = sentenceTheory θ '' C := by
      ext t
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨c.val, c.property, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨c, hc⟩, rfl⟩
    rw [← he]
    exact Set.to_countable _
  · exact Or.inr ha

/-- **Thinness is countability of every countable sentence spectrum**, on any Borel class. -/
@[blueprint "thm:thin-iff-countable-sentence-spectra"
  (title := /-- The sentence-spectrum characterization of thinness -/)
  (statement := /-- Let $C$ be a Borel class of coded structures over a countable relational
    language.  Then $C$ is thin for isomorphism --- carries no perfect set of pairwise
    non-isomorphic structures --- if and only if for every sequence $(\theta_n)_{n<\omega}$ of
    $L_{\omega_1\omega}$-sentences, only countably many truth sequences
    $(\mathbb{1}[c \models \theta_n])_{n}$ are realized by $c \in C$.  The class need not be
    isomorphism-invariant. -/)
  (proof := /-- Thin to countable: the truth-sequence map of a fixed list is Borel, and equality
    of truth sequences is a Borel equivalence relation coarser than isomorphism, so Silver's
    dichotomy on $C$ gives either countably many truth sequences or a continuous Cantor
    antichain for isomorphism, which thinness excludes.  Countable to thin: a perfect antichain
    yields a Borel Cantor isomorphism antichain $f$; for each bit $n$, the saturations of
    $f[\{x : x_n = 1\}]$ and $f[\{x : x_n = 0\}]$ are disjoint invariant analytic classes,
    separated by an invariant Borel set by iterated Lusin separation and saturation, hence by a
    sentence $\theta_n$ via L\'opez--Escobar.  The list $(\theta_n)$ then recovers every
    parameter, so its spectrum on $C$ is uncountable. -/)
  (uses := ["def:thin-on", "thm:cantor-to-perfect"])]
theorem thin_iff_countable_sentence_spectra (C : Set (StructureSpace L)) (hC : MeasurableSet C) :
    IsThinOn (structureIsoSetoid L) C ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable := by
  constructor
  · intro hthin θ
    rcases sentence_spectrum_countable_or_cantor C hC θ with hc | ha
    · exact hc
    · exact False.elim (hthin ha.hasPerfectAntichainOn)
  · intro hsmall hperfect
    let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
    obtain ⟨f, hf, hm, ha⟩ := hperfect.hasCantorAntichainOn
    exact no_antichain_of_countable_sentence_spectra C hsmall f hf.measurable hm ha

/-- Sentence form: a sentence is thin on its `ℕ`-models exactly when every countable sentence
list has countably many truth sequences realized in its models. -/
theorem Sentenceω.isThinOnNatModels_iff_countable_sentence_spectra (φ : L.Sentenceω) :
    φ.IsThinOnNatModels ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' ModelsOf φ).Countable :=
  thin_iff_countable_sentence_spectra (ModelsOf φ) (modelsOf_measurableSet φ)

/-- **Guardrail**: a Borel complete invariant cannot classify an uncountable thin class.  This does
not conflict with countable sentence spectra, which quantify over each list separately rather than
assert one complete list exists. -/
theorem countable_iso_classes_of_thin_borel_classifiable (C : Set (StructureSpace L))
    (hC : MeasurableSet C) (hthin : IsThinOn (structureIsoSetoid L) C)
    (hp : ∃ p : C → (ℕ → Bool), Measurable p ∧ ∀ c d : C,
      (structureIsoSetoid L).r c.val d.val ↔ p c = p d) :
    Countable (Quotient (Setoid.comap (fun c : C => c.val) (structureIsoSetoid L))) := by
  obtain ⟨θ, hθ⟩ := (sentence_classification_iff_borel_classification C hC).mpr hp
  let f : C → (ℕ → Bool) := fun c => sentenceTheory θ c.val
  have hsmall := (thin_iff_countable_sentence_spectra C hC).mp hthin θ
  have hrange : (Set.range f).Countable := hsmall.mono (by
    rintro _ ⟨c, rfl⟩
    exact ⟨c.val, c.property, rfl⟩)
  have := hrange.to_subtype
  have hs : Setoid.comap (fun c : C => c.val) (structureIsoSetoid L) = Setoid.ker f :=
    Setoid.ext hθ
  rw [hs]
  exact (Setoid.quotientKerEquivRange f).injective.countable

end FirstOrder.Language
