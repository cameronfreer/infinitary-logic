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
import InfinitaryLogic.ModelTheory.HanfSpectrum.LadderBound
import InfinitaryLogic.ModelTheory.HanfSpectrum.BethLadder

/-!
# Bounded-spectrum witnesses: lower bounds for the `L_{ω₁ω}` Hanf number

Facade for the sharpness half of `Hanf(L_{ω₁ω}) = ℶ_{ω₁}`
(`Lomega1omegaHanfNumber_eq_beth_omega1`, `BethLadder.lean`): concrete sentences whose model
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
* `HanfSpectrum/VonNeumannModel.lean` / `LadderBound.lean` — the general stage: the maximal
  model of size exactly `ℶ_{α+1}` (von Neumann levels `V_{ω+β}` + Shrink transport) and the
  matching upper bound for every model.
* `HanfSpectrum/BethLadder.lean` — the assembly: `beth_add_one_lt_Lomega1omegaHanfNumber` for
  each `α < ω₁`, the supremum, and **`Lomega1omegaHanfNumber_eq_beth_omega1`**.
-/
