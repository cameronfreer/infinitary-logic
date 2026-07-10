/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.HanfSpectrum.Countable

/-!
# Bounded-spectrum witnesses: lower bounds for the `L_{ω₁ω}` Hanf number

Facade for the sharpness pilot (toward `Hanf(L_{ω₁ω}) = ℶ_{ω₁}`): concrete sentences whose model
spectra are BOUNDED, each consumed through the generic endpoint
`lt_Lomega1omegaHanfNumber_of_maximal_model` (`ModelTheory/MorleyHanf.lean`).

* `HanfSpectrum/Countable.lean` — spectrum exactly `{ℵ₀}`:
  `aleph0_lt_Lomega1omegaHanfNumber`.
* (next) `HanfSpectrum/Powerset.lean` — the Marker powerset witness as ladder stage `α = 0`
  (ranked levels `U₀ ⊆ U₁`, extensional `E`, constants enumerating `U₀`): `ℶ_1 < H`.
* (later) `HanfSpectrum/BethLadder.lean` — the Marker Exercise 5.3 ladder: for each `α < ω₁` a
  sentence of maximal model size `ℶ_{α+1}`, then `sup_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁} ≤ H` — gated on a
  statement audit of the successor/limit clauses and the final supremum argument.
-/
