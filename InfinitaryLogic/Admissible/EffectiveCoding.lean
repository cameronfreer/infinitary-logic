/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.AmbientHF
import Mathlib.Computability.PartrecCode

/-!
# The effective coding layer (issue #19A, step 3)

`FinitaryCoding` stays the **weak** layer: an injective numbering, enough for adequacy and for the
`A`-finiteness characterization, and available for any language.  This file adds a **second**
layer, used only by Σ-definability, and proves that `Sigma1` does not depend on which effective
coding was chosen.

**The two layers do not mix.**  `hfAmbient` still takes a plain `FinitaryCoding`, so computability
data cannot infect the fragment or theory layers; `gate6_adequacy_needs_no_effective_data` and
`gate6_aFinite_needs_no_effective_data` are the structural guards for that, and they typecheck only
because the weak layer really is sufficient there.

## Why injectivity was not enough

Injectivity makes the decoded *range* numbering-independent — that is `hfAmbient_range_indep`, and
it is why adequacy and containment need nothing more.  It says nothing about `Sigma1`: two
injective numberings can disagree about which theories are c.e., because a numbering may scramble
codes non-computably.  The fix is not a stronger single numbering but a **relation** between
numberings, `ComputablyEquivalent`, along which `Sigma1` transports.

## The bijectivity simplification

`EffectiveCoding` requires the numbering to be **onto**, so every natural is a valid sentence code.
This is the simplification of "if invalid-code bookkeeping dominates, use stored bijective
numberings; then acceptable numberings differ by computable permutations of `ℕ`".  It is a change
of bookkeeping, not of mathematics:

- gate 2 (invalid inputs introduce no extra decoded sentences) becomes *provably vacuous* rather
  than assumed — `gate2_no_invalid_codes` states it explicitly instead of dropping it;
- `forward` and `backward` become mutually inverse total computable permutations
  (`backward_forward`, `forward_backward`), so the image of a code set along one is the preimage
  along the other (`forward_image_eq_backward_preimage`), and gate 4 needs only closure of c.e.
  sets under computable preimage — no dovetailing.

The cost is stated honestly by `equiv`: an `EffectiveCoding` exists exactly when `L.Sentence` is
denumerable.  That is the intended setting — effective Barwise theory is for recursive languages —
and languages outside it correctly get no effective layer at all, while keeping the weak one.

## Main definitions

- `CE`: genuine computable enumerability, `∃ f, Nat.Partrec f ∧ ∀ n, n ∈ S ↔ (f n).Dom`.
- `EffectiveCoding`: `FinitaryCoding` plus surjectivity; `decode` is its inverse.
- `ComputablyEquivalent`: the partial-recursive translation data relating two effective codings.

## Main results

The six gates, named `gate1_`…`gate6_`:

1. `gate1_forward_decodes_same`: a translation maps every valid code to a code for the *same*
   sentence.
2. `gate2_no_invalid_codes`: there are no invalid inputs to bookkeep.
3. `gate3_backward_decodes_same`: the reverse translation, likewise.
4. `gate4_ce_transport`: c.e. code sets transport along each translation.
5. `gate5_sigma1_iff`: consequently `Sigma1` is coding-independent.
6. `gate6_*`: adequacy and the corrected `A`-finiteness characterization remain available from a
   plain `FinitaryCoding`.
-/

namespace FirstOrder.Language

universe u v

variable {L : Language.{u, v}}

/-! ## Computable enumerability

Spelled out rather than taken as an existential over an arbitrary `W : ℕ → Set ℕ`, which would
carry no computability content at all. -/

/-- **A genuinely c.e. set of naturals**: the domain of a partial recursive function.  By
`Nat.Partrec.Code.exists_code` these are exactly the domains of `Nat.Partrec.Code`s, so the
Σ-definition codes of `hfAmbient` are *complete* for this notion rather than a modelling
convenience. -/
def CE (S : Set ℕ) : Prop :=
  ∃ f : ℕ →. ℕ, Nat.Partrec f ∧ ∀ n, n ∈ S ↔ (f n).Dom

/-- C.e. sets are closed under computable preimage.  With bijective numberings this is all of
gate 4: no dovetailing, because image along one translation is preimage along the other. -/
theorem CE.preimage {S : Set ℕ} (hS : CE S) {g : ℕ → ℕ} (hg : Computable g) : CE (g ⁻¹' S) := by
  obtain ⟨f, hf, hmem⟩ := hS
  exact ⟨fun n => f (g n), Partrec.nat_iff.mp ((Partrec.nat_iff.mpr hf).comp hg),
    fun n => hmem (g n)⟩

/-! ## The effective layer -/

variable (L) in
/-- **The effective coding layer.**  A `FinitaryCoding` whose numbering is additionally onto, so
every natural is a valid sentence code.

Used *only* by Σ-definability.  Adequacy and `A`-finiteness continue to take the weak layer; see
the gate-6 guards. -/
structure EffectiveCoding (L : Language.{u, v}) extends FinitaryCoding L where
  /-- Every natural is a code.  This is the invalid-code bookkeeping simplification, and its
  content is exactly that `L.Sentence` is denumerable — see `EffectiveCoding.equiv`. -/
  enc_surjective : Function.Surjective enc

namespace EffectiveCoding

/-- **The layer is inhabited**, exactly when the finitary sentences are denumerable.  Without a
witness the gates below would be conditionally vacuous; with one they are not. -/
def ofDenumerable (L : Language.{u, v}) [Denumerable L.Sentence] : EffectiveCoding L where
  enc := Denumerable.eqv L.Sentence
  enc_injective := (Denumerable.eqv L.Sentence).injective
  enc_surjective := (Denumerable.eqv L.Sentence).surjective

variable (C : EffectiveCoding L)

/-- What surjectivity costs, made explicit: an effective coding *is* a denumeration of the
finitary sentences. -/
noncomputable def equiv : L.Sentence ≃ ℕ :=
  Equiv.ofBijective C.enc ⟨C.enc_injective, C.enc_surjective⟩

/-- The inverse numbering. -/
noncomputable def decode (n : ℕ) : L.Sentence := (C.enc_surjective n).choose

@[simp] theorem enc_decode (n : ℕ) : C.enc (C.decode n) = n := (C.enc_surjective n).choose_spec

@[simp] theorem decode_enc (φ₀ : L.Sentence) : C.decode (C.enc φ₀) = φ₀ :=
  C.enc_injective (C.enc_decode _)

/-- **Every natural is a sentence code.**  This is what makes gate 2 vacuous. -/
theorem isSentenceCode (n : ℕ) : (hfAmbient C.toFinitaryCoding).IsSentenceCode n :=
  C.enc_surjective n

/-- Ambient sentence decoding *is* the inverse numbering, transported into `Lω₁ω`. -/
theorem decodeSentence_eq (s : (hfAmbient C.toFinitaryCoding).SentenceCode) :
    (hfAmbient C.toFinitaryCoding).decodeSentence s = (C.decode s.1).toLω :=
  congrArg Sentence.toLω (C.enc_injective (s.2.choose_spec.trans (C.enc_decode s.1).symm))

end EffectiveCoding

/-- **Gate 2, discharged by being vacuous.**  Under the bijectivity simplification there are no
invalid inputs, so no invalid input can contribute a decoded sentence.

Stated rather than dropped: the obligation is real for a general numbering, and this records
exactly which hypothesis retires it.  It is a fact about a *single* coding, so it lives here and
not among the translation gates. -/
theorem gate2_no_invalid_codes (C : EffectiveCoding L) :
    {n : ℕ | ¬(hfAmbient C.toFinitaryCoding).IsSentenceCode n} = ∅ :=
  Set.eq_empty_of_forall_notMem fun n hn => hn (C.isSentenceCode n)

/-! ## Computable equivalence of codings

**A deviation from the sketch, forced by Lean.**  This cannot be `Prop`-valued: `forward` and
`backward` are data (`ℕ → ℕ`), and a structure with a data field does not live in `Prop`.  Use
`Nonempty (ComputablyEquivalent C C')` where the propositional relation is wanted. -/

/-- **The translation data relating two effective codings.**

Both translations are *total* computable functions, because both numberings are onto; the
specifications say each sends a code to the code of the same sentence under the other numbering.
Mutual inversion is then derived, not assumed. -/
structure ComputablyEquivalent (C C' : EffectiveCoding L) where
  /-- `C`-codes to `C'`-codes. -/
  forward : ℕ → ℕ
  /-- `C'`-codes back to `C`-codes. -/
  backward : ℕ → ℕ
  /-- The translation is effective. -/
  forward_computable : Computable forward
  /-- …and so is its inverse. -/
  backward_computable : Computable backward
  /-- `forward` renumbers the sentence, it does not change it. -/
  forward_spec : ∀ n, forward n = C'.enc (C.decode n)
  /-- Likewise `backward`. -/
  backward_spec : ∀ n, backward n = C.enc (C'.decode n)

namespace ComputablyEquivalent

variable {C C' : EffectiveCoding L} (E : ComputablyEquivalent C C')

@[simp] theorem decode_forward (n : ℕ) : C'.decode (E.forward n) = C.decode n := by
  rw [E.forward_spec, C'.decode_enc]

@[simp] theorem decode_backward (n : ℕ) : C.decode (E.backward n) = C'.decode n := by
  rw [E.backward_spec, C.decode_enc]

@[simp] theorem backward_forward (n : ℕ) : E.backward (E.forward n) = n := by
  rw [E.backward_spec, E.decode_forward, C.enc_decode]

@[simp] theorem forward_backward (n : ℕ) : E.forward (E.backward n) = n := by
  rw [E.forward_spec, E.decode_backward, C'.enc_decode]

/-- Computable equivalence is symmetric — the two translations simply swap roles. -/
def symm : ComputablyEquivalent C' C where
  forward := E.backward
  backward := E.forward
  forward_computable := E.backward_computable
  backward_computable := E.forward_computable
  forward_spec := E.backward_spec
  backward_spec := E.forward_spec

/-- …and reflexive. -/
def refl (C : EffectiveCoding L) : ComputablyEquivalent C C where
  forward := id
  backward := id
  forward_computable := Computable.id
  backward_computable := Computable.id
  forward_spec n := (C.enc_decode n).symm
  backward_spec n := (C.enc_decode n).symm

/-! ### The gates -/

/-- **Gate 1.**  A partial-recursive translation maps every valid `C`-code to a `C'`-code for the
**same** sentence.  Validity of the target is `C'.isSentenceCode`; the content is the equation. -/
theorem gate1_forward_decodes_same (n : ℕ) :
    (hfAmbient C'.toFinitaryCoding).decodeSentence ⟨E.forward n, C'.isSentenceCode _⟩ =
      (hfAmbient C.toFinitaryCoding).decodeSentence ⟨n, C.isSentenceCode n⟩ := by
  rw [C'.decodeSentence_eq, C.decodeSentence_eq, E.decode_forward]

/-- **Gate 3.**  The reverse translation has the analogous property. -/
theorem gate3_backward_decodes_same (n : ℕ) :
    (hfAmbient C.toFinitaryCoding).decodeSentence ⟨E.backward n, C.isSentenceCode _⟩ =
      (hfAmbient C'.toFinitaryCoding).decodeSentence ⟨n, C'.isSentenceCode n⟩ :=
  E.symm.gate1_forward_decodes_same n

/-- The translations are inverse bijections, so pushing a code set forward is the same as pulling
it back.  This is what lets gate 4 avoid dovetailing. -/
theorem forward_image_eq_backward_preimage (S : Set ℕ) : E.forward '' S = E.backward ⁻¹' S := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa only [Set.mem_preimage, E.backward_forward] using hm
  · intro hn
    exact ⟨E.backward n, hn, E.forward_backward n⟩

/-- **Gate 4.**  C.e. code sets transport along each translation. -/
theorem gate4_ce_transport {S : Set ℕ} (hS : CE S) : CE (E.forward '' S) := by
  rw [E.forward_image_eq_backward_preimage]
  exact hS.preimage E.backward_computable

include E in
/-- One direction of gate 5.  A Σ-definition code for `C` is turned into one for `C'` by
precomposing its partial-recursive enumeration with `backward` — the c.e. transport of gate 4,
carried through `Nat.Partrec.Code.exists_code`. -/
theorem sigma1_of_sigma1 {T : L.Theoryω} (h : (hfAmbient C.toFinitaryCoding).Sigma1 T) :
    (hfAmbient C'.toFinitaryCoding).Sigma1 T := by
  obtain ⟨d, rfl⟩ := h
  have hp : Nat.Partrec fun n =>
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code d.1) (E.backward n) :=
    Partrec.nat_iff.mp
      (Nat.Partrec.Code.eval_part.comp
        (Computable.const (Denumerable.ofNat Nat.Partrec.Code d.1)) E.backward_computable)
  obtain ⟨e', he'⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨⟨Encodable.encode e', trivial⟩, ?_⟩
  have hcode : Denumerable.ofNat Nat.Partrec.Code (Encodable.encode e') = e' :=
    Denumerable.ofNat_encode e'
  ext φ
  simp only [AmbientPresentation.mem_theoryOf, hfAmbient, hcode, he', Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨E.backward s.1, C.isSentenceCode _⟩, hs, ?_⟩
    exact E.gate3_backward_decodes_same s.1
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨E.forward s.1, C'.isSentenceCode _⟩, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, E.backward_forward] using hs
    · exact E.gate1_forward_decodes_same s.1

include E in
/-- **Gate 5.**  `Sigma1` does not depend on which effective coding was chosen.

This is the property injectivity alone could not give, and it is why the effective layer exists
separately from `FinitaryCoding`. -/
theorem gate5_sigma1_iff {T : L.Theoryω} :
    (hfAmbient C.toFinitaryCoding).Sigma1 T ↔ (hfAmbient C'.toFinitaryCoding).Sigma1 T :=
  ⟨E.sigma1_of_sigma1, E.symm.sigma1_of_sigma1⟩

end ComputablyEquivalent

/-! ### Gate 6 — the layers really are separate

These typecheck only because the fragment and theory layers take the **weak** coding.  If effective
data ever leaked into `hfAmbient`, `hfAmbient_adequate` or `hfAmbient_aFinite_iff`, these would stop
elaborating — which is the point of writing them. -/

/-- **Gate 6, adequacy.**  No effective data. -/
theorem gate6_adequacy_needs_no_effective_data (C : FinitaryCoding L) :
    (hfAmbient C).AdequateFor (finitaryFragment L) :=
  hfAmbient_adequate C

/-- **Gate 6, `A`-finiteness.**  Likewise — the corrected characterization is a fact about the weak
layer, so computability has not infected the theory layer. -/
theorem gate6_aFinite_needs_no_effective_data (C : FinitaryCoding L) {T : L.Theoryω} :
    (hfAmbient C).AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L :=
  hfAmbient_aFinite_iff C

/-- …and an effective coding is usable there too, by forgetting its effective data. -/
example (C : EffectiveCoding L) : (hfAmbient C.toFinitaryCoding).AdequateFor (finitaryFragment L) :=
  hfAmbient_adequate _

end FirstOrder.Language
