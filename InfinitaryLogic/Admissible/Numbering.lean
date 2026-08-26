/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.AmbientHF
import Mathlib.Computability.PartrecCode

/-!
# Numberings of the finitary sentences, and `Sigma1` invariance (issue #19A, step 3)

`Sigma1` is **already defined** from the weak layer: `hfAmbient` takes a plain `FinitaryCoding` and
supplies `enumerates`, so every coding has its own coding-relative `Sigma1`.  What a single coding
cannot give is **independence** — two injective numberings can disagree about which theories are
c.e.  This file supplies what does:

```
FinitaryCoding              adequacy, AFinite, and Sigma1 itself      -- any language
FinitaryNumbering           a *bijective* numbering; no effectiveness on its own
ComputablyEquivalent C C'   Sigma1 invariance across numberings       -- the actual content
```

**Read the middle line carefully.**  `FinitaryNumbering` is structurally a bijective numbering and
nothing more: `FinitaryNumbering.ofDenumerable` builds one from a bare `Denumerable` instance, with
no computability evidence whatsoever.  It is *not* intrinsically effective, and it was renamed from
`EffectiveCoding` precisely so the name stops claiming that.  Invariance holds **only when a
`ComputablyEquivalent` witness is supplied**; the numbering alone proves nothing about `Sigma1`.

**The layers do not mix.**  `hfAmbient` still takes a plain `FinitaryCoding`, so numbering data
cannot infect the fragment or theory layers.  That refusal is enforced by
`hfAmbient_rejects_numbering`, a `fail_if_success` regression — not merely by the positive examples
below, which show only that the weak layer suffices.

## The bijectivity simplification

Surjectivity is required, so every natural is a valid sentence code.  This is the "if invalid-code
bookkeeping dominates, use stored bijective numberings; then acceptable numberings differ by
computable permutations of `ℕ`" route, and it is a change of bookkeeping, not of mathematics:

- invalid-input bookkeeping becomes *provably vacuous* — `invalid_codes_eq_empty` states it
  explicitly instead of dropping the obligation;
- `forward` and `backward` become mutually inverse total computable permutations, so the image of a
  code set along one is the preimage along the other (`forward_image_eq_backward_preimage`), and
  c.e. transport needs only closure under computable preimage — no dovetailing.

The cost is stated by `equiv`: a `FinitaryNumbering` exists exactly when `L.Sentence` is denumerable.
That is the intended setting — effective Barwise theory is for recursive languages — and languages
outside it keep the weak layer and correctly get no numbering at all.

## Main definitions

- `CE`: genuine computable enumerability, `∃ f, Nat.Partrec f ∧ ∀ n, n ∈ S ↔ (f n).Dom`.
- `FinitaryNumbering`: `FinitaryCoding` plus surjectivity; `decode` is its inverse.
- `FinitaryNumbering.Sigma1`: the production-facing Σ-predicate, relative to a numbering.
- `ComputablyEquivalent`: the computable translation data (in `Type`, since it is data).
- `AreComputablyEquivalent`: its `Prop`-valued wrapper, an equivalence relation.

## Main results

- `ComputablyEquivalent.sigma1_iff` / `AreComputablyEquivalent.sigma1_iff`: `Sigma1` is
  numbering-independent.  This is the property injectivity alone could not give.
- `ComputablyEquivalent.ce_forward_image`: c.e. code sets transport along a translation.
- `hfAmbient_rejects_numbering`: the layer-separation guard.
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

/-- C.e. sets are closed under computable preimage.  With bijective numberings this is all the
transport that is needed: image along one translation is preimage along the other. -/
theorem CE.preimage {S : Set ℕ} (hS : CE S) {g : ℕ → ℕ} (hg : Computable g) : CE (g ⁻¹' S) := by
  obtain ⟨f, hf, hmem⟩ := hS
  exact ⟨fun n => f (g n), Partrec.nat_iff.mp ((Partrec.nat_iff.mpr hf).comp hg),
    fun n => hmem (g n)⟩

/-! ## Bijective numberings -/

/-- **A bijective numbering of the finitary sentences.**

`FinitaryCoding` plus surjectivity, so every natural is a valid sentence code.

**This carries no effectiveness.**  It is a numbering, not an effective one: `ofDenumerable` builds
it from a bare `Denumerable` instance, and nothing here constrains how `enc` is computed.  `Sigma1`
is already available from the weak `FinitaryCoding` layer; what a numbering buys is only the ability
to *state* `ComputablyEquivalent`, and independence holds only once such a witness is supplied. -/
structure FinitaryNumbering (L : Language.{u, v}) extends FinitaryCoding L where
  /-- Every natural is a code.  This is the invalid-code bookkeeping simplification, and its
  content is exactly that `L.Sentence` is denumerable — see `FinitaryNumbering.equiv`. -/
  enc_surjective : Function.Surjective enc

namespace FinitaryNumbering

/-- **The layer is inhabited**, exactly when the finitary sentences are denumerable.  Without a
witness the results below would be conditionally vacuous; with one they are not.

Note what this does *not* need: no computability hypothesis at all.  That is the honest reason the
structure is called a numbering rather than an effective coding. -/
def ofDenumerable (L : Language.{u, v}) [Denumerable L.Sentence] : FinitaryNumbering L where
  enc := Denumerable.eqv L.Sentence
  enc_injective := (Denumerable.eqv L.Sentence).injective
  enc_surjective := (Denumerable.eqv L.Sentence).surjective

variable (C : FinitaryNumbering L)

/-- What surjectivity costs, made explicit: a numbering *is* a denumeration of the finitary
sentences. -/
noncomputable def equiv : L.Sentence ≃ ℕ :=
  Equiv.ofBijective C.enc ⟨C.enc_injective, C.enc_surjective⟩

/-- The inverse numbering. -/
noncomputable def decode (n : ℕ) : L.Sentence := (C.enc_surjective n).choose

@[simp] theorem enc_decode (n : ℕ) : C.enc (C.decode n) = n := (C.enc_surjective n).choose_spec

@[simp] theorem decode_enc (φ₀ : L.Sentence) : C.decode (C.enc φ₀) = φ₀ :=
  C.enc_injective (C.enc_decode _)

/-- **Every natural is a sentence code.** -/
theorem isSentenceCode (n : ℕ) : (hfAmbient C.toFinitaryCoding).IsSentenceCode n :=
  C.enc_surjective n

/-- **There are no invalid inputs to bookkeep**, so no invalid input can contribute a decoded
sentence.

Stated rather than dropped: the obligation is real for a general numbering, and this records
exactly which hypothesis retires it. -/
theorem invalid_codes_eq_empty :
    {n : ℕ | ¬(hfAmbient C.toFinitaryCoding).IsSentenceCode n} = ∅ :=
  Set.eq_empty_of_forall_notMem fun n hn => hn (C.isSentenceCode n)

/-- Ambient sentence decoding *is* the inverse numbering, transported into `Lω₁ω`. -/
theorem decodeSentence_eq (s : (hfAmbient C.toFinitaryCoding).SentenceCode) :
    (hfAmbient C.toFinitaryCoding).decodeSentence s = (C.decode s.1).toLω :=
  congrArg Sentence.toLω (C.enc_injective (s.2.choose_spec.trans (C.enc_decode s.1).symm))

/-- **The production-facing Σ-predicate**, relative to a numbering.

Definitionally the ambient `Sigma1` of the underlying weak coding — the numbering adds nothing to
the *definition*.  It exists as a separate name so that consumers state their hypotheses against a
numbering, which is what makes `AreComputablyEquivalent.sigma1_iff` applicable to them. -/
def Sigma1 (T : L.Theoryω) : Prop := (hfAmbient C.toFinitaryCoding).Sigma1 T

theorem sigma1_def {T : L.Theoryω} : C.Sigma1 T ↔ (hfAmbient C.toFinitaryCoding).Sigma1 T :=
  Iff.rfl

end FinitaryNumbering

/-! ## Computable equivalence of numberings

The witness structure lives in `Type` — `forward` and `backward` are data, and a structure with a
data field cannot be `Prop`.  `AreComputablyEquivalent` is the `Prop`-valued public relation. -/

/-- **The translation data relating two numberings.**

Both translations are *total* computable functions, because both numberings are onto; the
specifications say each sends a code to the code of the same sentence under the other numbering.
Mutual inversion is then derived, not assumed. -/
structure ComputablyEquivalent (C C' : FinitaryNumbering L) where
  /-- `C`-codes to `C'`-codes. -/
  forward : ℕ → ℕ
  /-- `C'`-codes back to `C`-codes. -/
  backward : ℕ → ℕ
  /-- The translation is effective.  **This** is where effectiveness enters — not the numbering. -/
  forward_computable : Computable forward
  /-- …and so is its inverse. -/
  backward_computable : Computable backward
  /-- `forward` renumbers the sentence, it does not change it. -/
  forward_spec : ∀ n, forward n = C'.enc (C.decode n)
  /-- Likewise `backward`. -/
  backward_spec : ∀ n, backward n = C.enc (C'.decode n)

namespace ComputablyEquivalent

variable {C C' C'' : FinitaryNumbering L} (E : ComputablyEquivalent C C')

@[simp] theorem decode_forward (n : ℕ) : C'.decode (E.forward n) = C.decode n := by
  rw [E.forward_spec, C'.decode_enc]

@[simp] theorem decode_backward (n : ℕ) : C.decode (E.backward n) = C'.decode n := by
  rw [E.backward_spec, C.decode_enc]

@[simp] theorem backward_forward (n : ℕ) : E.backward (E.forward n) = n := by
  rw [E.backward_spec, E.decode_forward, C.enc_decode]

@[simp] theorem forward_backward (n : ℕ) : E.forward (E.backward n) = n := by
  rw [E.forward_spec, E.decode_backward, C'.enc_decode]

/-- Computable equivalence is reflexive. -/
def refl (C : FinitaryNumbering L) : ComputablyEquivalent C C where
  forward := id
  backward := id
  forward_computable := Computable.id
  backward_computable := Computable.id
  forward_spec n := (C.enc_decode n).symm
  backward_spec n := (C.enc_decode n).symm

/-- …symmetric — the two translations simply swap roles. -/
def symm : ComputablyEquivalent C' C where
  forward := E.backward
  backward := E.forward
  forward_computable := E.backward_computable
  backward_computable := E.forward_computable
  forward_spec := E.backward_spec
  backward_spec := E.forward_spec

/-- …and transitive, by composing translations.  Computability composes, and the specifications
compose through `decode_forward` / `decode_backward`. -/
def trans (F : ComputablyEquivalent C' C'') : ComputablyEquivalent C C'' where
  forward n := F.forward (E.forward n)
  backward n := E.backward (F.backward n)
  forward_computable := F.forward_computable.comp E.forward_computable
  backward_computable := E.backward_computable.comp F.backward_computable
  forward_spec n := by rw [F.forward_spec, E.decode_forward]
  backward_spec n := by rw [E.backward_spec, F.decode_backward]

/-! ### Translation preserves sentences -/

/-- **`forward` maps every code to a code for the same sentence.** -/
theorem decodeSentence_forward (n : ℕ) :
    (hfAmbient C'.toFinitaryCoding).decodeSentence ⟨E.forward n, C'.isSentenceCode _⟩ =
      (hfAmbient C.toFinitaryCoding).decodeSentence ⟨n, C.isSentenceCode n⟩ := by
  rw [C'.decodeSentence_eq, C.decodeSentence_eq, E.decode_forward]

/-- **…and so does `backward`.** -/
theorem decodeSentence_backward (n : ℕ) :
    (hfAmbient C.toFinitaryCoding).decodeSentence ⟨E.backward n, C.isSentenceCode _⟩ =
      (hfAmbient C'.toFinitaryCoding).decodeSentence ⟨n, C'.isSentenceCode n⟩ :=
  E.symm.decodeSentence_forward n

/-! ### C.e. transport and invariance -/

/-- The translations are inverse bijections, so pushing a code set forward is the same as pulling
it back.  This is what lets c.e. transport avoid dovetailing. -/
theorem forward_image_eq_backward_preimage (S : Set ℕ) : E.forward '' S = E.backward ⁻¹' S := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa only [Set.mem_preimage, E.backward_forward] using hm
  · intro hn
    exact ⟨E.backward n, hn, E.forward_backward n⟩

/-- **C.e. code sets transport along a translation.** -/
theorem ce_forward_image {S : Set ℕ} (hS : CE S) : CE (E.forward '' S) := by
  rw [E.forward_image_eq_backward_preimage]
  exact hS.preimage E.backward_computable

include E in
/-- A Σ-definition code for `C` is turned into one for `C'` by precomposing its partial-recursive
enumeration with `backward`, then re-coding through `Nat.Partrec.Code.exists_code`. -/
theorem sigma1_of_sigma1 {T : L.Theoryω} (h : C.Sigma1 T) : C'.Sigma1 T := by
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
    exact ⟨⟨E.backward s.1, C.isSentenceCode _⟩, hs, E.decodeSentence_backward s.1⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨E.forward s.1, C'.isSentenceCode _⟩, ?_, E.decodeSentence_forward s.1⟩
    simpa only [Set.mem_ofPred_eq, E.backward_forward] using hs

include E in
/-- **`Sigma1` does not depend on which numbering was chosen.**

This is the property injectivity alone could not give, and the reason the numbering layer exists
separately from `FinitaryCoding`.  Note the hypothesis: the *witness* `E` is what carries the
content — a numbering by itself proves nothing here. -/
theorem sigma1_iff {T : L.Theoryω} : C.Sigma1 T ↔ C'.Sigma1 T :=
  ⟨E.sigma1_of_sigma1, E.symm.sigma1_of_sigma1⟩

end ComputablyEquivalent

/-! ## The public relation

`ComputablyEquivalent` must live in `Type` because it stores functions.  The relation consumers
should quantify over is this `Prop`-valued wrapper. -/

/-- **Two numberings are computably equivalent** when some translation witnesses it. -/
def AreComputablyEquivalent (C C' : FinitaryNumbering L) : Prop :=
  Nonempty (ComputablyEquivalent C C')

namespace AreComputablyEquivalent

variable {C C' C'' : FinitaryNumbering L}

@[refl] theorem refl (C : FinitaryNumbering L) : AreComputablyEquivalent C C :=
  ⟨ComputablyEquivalent.refl C⟩

@[symm] theorem symm (h : AreComputablyEquivalent C C') : AreComputablyEquivalent C' C :=
  h.elim fun E => ⟨E.symm⟩

theorem trans (h : AreComputablyEquivalent C C') (h' : AreComputablyEquivalent C' C'') :
    AreComputablyEquivalent C C'' :=
  h.elim fun E => h'.elim fun F => ⟨E.trans F⟩

/-- **`Sigma1` invariance, in propositional form.**  The public statement of the whole file. -/
theorem sigma1_iff (h : AreComputablyEquivalent C C') {T : L.Theoryω} :
    C.Sigma1 T ↔ C'.Sigma1 T :=
  h.elim fun E => E.sigma1_iff

end AreComputablyEquivalent

/-! ## Layer separation, enforced

The positive examples show the weak layer *suffices* for adequacy and `A`-finiteness.  They do not
by themselves prevent numbering data from leaking into those layers, so the actual guard is the
`fail_if_success` regression: `hfAmbient` must **refuse** a `FinitaryNumbering`. -/

/-- Adequacy needs no numbering. -/
example (C : FinitaryCoding L) : (hfAmbient C).AdequateFor (finitaryFragment L) :=
  hfAmbient_adequate C

/-- Nor does the corrected `A`-finiteness characterization. -/
example (C : FinitaryCoding L) {T : L.Theoryω} :
    (hfAmbient C).AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L :=
  hfAmbient_aFinite_iff C

/-- **The guard**, stating both halves at once: `hfAmbient` **refuses** a numbering directly, and
the forgetful route through `.toFinitaryCoding` is what works.

The `fail_if_success` line is the durable form of the separation claim.  If `hfAmbient` were ever
widened to accept numbering data it would start succeeding and this breaks — which the positive
examples above would not detect. -/
theorem hfAmbient_rejects_numbering (C : FinitaryNumbering L) :
    (hfAmbient C.toFinitaryCoding).AdequateFor (finitaryFragment L) := by
  fail_if_success have := hfAmbient C
  exact hfAmbient_adequate _

end FirstOrder.Language
