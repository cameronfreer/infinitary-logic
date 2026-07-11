/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.HanfSpectrum.Countable
import InfinitaryLogic.ModelTheory.HanfSpectrum.LadderSyntax
import InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds
import InfinitaryLogic.ModelTheory.HanfSpectrum.IndexOrder
import InfinitaryLogic.ModelTheory.HanfSpectrum.Powerset
import InfinitaryLogic.ModelTheory.HanfSpectrum.VonNeumannModel

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
* `HanfSpectrum/Powerset.lean` — the α = 0 instance: maximal model `Set ℕ`,
  `beth_one_lt_Lomega1omegaHanfNumber`.
* `HanfSpectrum/IndexOrder.lean` — the deferred `typein` layer: `idxVal`/`idxOf`, endpoint
  values, `⋖`/limit transfers, and `Countable (Index α)` for `α < ω₁`.
* (next) `HanfSpectrum/BethLadder.lean` — the general stage: for each `α < ω₁` a maximal model
  of size `ℶ_{α+1}` (the von Neumann levels `V_{ω+β}` + Shrink transport), then the supremum
  `⨆_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁}` (`CardinalBounds.lean`) gives `Lomega1omegaHanfNumber = ℶ_{ω₁}`.
-/
