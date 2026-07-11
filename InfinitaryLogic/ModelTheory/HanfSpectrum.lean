/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.HanfSpectrum.Countable
import InfinitaryLogic.ModelTheory.HanfSpectrum.LadderSyntax
import InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds

/-!
# Bounded-spectrum witnesses: lower bounds for the `L_{ω₁ω}` Hanf number

Facade for the sharpness pilot (toward `Hanf(L_{ω₁ω}) = ℶ_{ω₁}`): concrete sentences whose model
spectra are BOUNDED, each consumed through the generic endpoint
`lt_Lomega1omegaHanfNumber_of_maximal_model` (`ModelTheory/MorleyHanf.lean`).

* `HanfSpectrum/Countable.lean` — spectrum exactly `{ℵ₀}`:
  `aleph0_lt_Lomega1omegaHanfNumber`.
* `HanfSpectrum/LadderSyntax.lean` — the common ladder language and sentence (Marker,
  Exercise 5.3) with the semantic packaging `realize_ladderSentence_iff`/`IsLadderModel`.
* `HanfSpectrum/CardinalBounds.lean` — the consumer-shaped cardinal arithmetic: countable
  sigma/union bounds, powerset-injection bound, and `⨆_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁}`.
* (next) `HanfSpectrum/Powerset.lean` — the α = 0 instance: maximal model `Set ℕ`, `ℶ_1 < H`.
* (later) `HanfSpectrum/BethLadder.lean` — the Marker Exercise 5.3 ladder: for each `α < ω₁` a
  sentence of maximal model size `ℶ_{α+1}`, then `sup_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁} ≤ H` — gated on a
  statement audit of the successor/limit clauses and the final supremum argument.
-/
