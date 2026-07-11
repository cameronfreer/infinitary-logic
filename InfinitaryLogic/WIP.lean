-- The old skolemColim EM term model (kept CI-checked; no longer imported by the local stack)
import InfinitaryLogic.Methods.EMTermModel
-- The local EM extraction bridge (its Conditional/MorleyHanfTransfer import stays isolated here)
import InfinitaryLogic.Methods.LocalEMExtraction
-- The pure local stack: semantic layer onward (LocalEMFamily -> LocalColimit -> LocalTower ->
-- LocalSkolem -> LocalEMSupport, plus the explicit Henkin.Construction realize lemmas)
import InfinitaryLogic.Methods.LocalEMContext
-- The local EM truth lemma layer 1: Skolem-witness transport (imports LocalEMContext)
import InfinitaryLogic.Methods.LocalEMTruth
-- The issue #11 equivariance spike + packaging: the local EM setoid is preserved/reflected by
-- skeleton renaming; descended base-reduct automorphism (imports LocalEMContext)
import InfinitaryLogic.Methods.LocalEMEquivariance
-- The issue #11 order-theoretic interface: highly order-transitive linear orders
import InfinitaryLogic.Methods.HighlyOrderTransitive
-- The issue #11 compression layer: finite-support term codes (imports LocalEMEquivariance)
import InfinitaryLogic.Methods.LocalEMCompression
-- The issue #11 orbit classification: tuple codes; equal code => same automorphism orbit
import InfinitaryLogic.Methods.LocalEMTupleOrbit
-- The issue #11 conditional smallness theorem: countably many types via subsingleton code fibers
import InfinitaryLogic.Methods.LocalEMSmall
-- The issue #11 exact carrier cardinality: located term codes (imports LocalEMCompression)
import InfinitaryLogic.Methods.LocalEMCardinality
-- The local EM truth lemma layer 2: readiness + the staged truth lemma (imports LocalEMTruth)
import InfinitaryLogic.Methods.LocalEMTruthLemma
-- The template-realization bridge (imports the EM-side template machinery; Conditional-free)
import InfinitaryLogic.Methods.LocalEMTemplateRealization
-- The Conditional-facing Ω-residual bridge (LocalEMOmegaExtraction → TailTemplateRealizable)
import InfinitaryLogic.Methods.LocalEMOmegaResidual
-- The parameterized pair Erdős–Rado (color bound κ): chunk 1 toward bounded finite-arity ER
import InfinitaryLogic.Combinatorics.PairErdosRadoGeneral
-- The finite-arity induction: ladder + bounded theorem + Marker-stage supply (chunk 2b)
import InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction
-- The arity-general end-homogenization engine (EHMR with tuple-typed nodes): ER hard chunk 2a
import InfinitaryLogic.Combinatorics.EndHomogeneousErdosRado
-- The Marker stage: finite-fragment support extraction + ER certification (reshape layer 1)
import InfinitaryLogic.Methods.MarkerStage
-- Layer 7a: the schema-template Ω-witness bridge (TailTemplateOmegaWitnessed → OmegaCompleteForColim)
import InfinitaryLogic.Methods.SchemaOmegaWitness
-- Layer 7b checkpoint 1: the countable schema sentence universe (completion decision list)
import InfinitaryLogic.Methods.SchemaCompletion
-- Layer 7b checkpoint 5a: the schema term-model equality interface (locDeEqAtom setoid)
import InfinitaryLogic.Methods.SchemaTermModel
import InfinitaryLogic.Methods.SchemaTermTruth
import InfinitaryLogic.Methods.LocalSkolemUniversal
import InfinitaryLogic.Methods.SchemaLocalEMSource

/-!
# WIP: the work-in-progress frontier bundle

Root of the **non-default** `InfinitaryLogicWIP` build target: the Ehrenfeucht–Mostowski /
Skolem-hull realizability construction that (as of 2026-07-10) **has discharged** the
Morley–Hanf seed residual — the endpoint `morley_hanf` is on the default surface — plus the
historical frontier it grew out of. The frontier has two disjoint roots —
the old `skolemColim` track (`EMTermModel`) and the pure local stack, whose top is the
extraction bridge (`LocalEMExtraction`, isolating the Conditional import); since
`LocalEMExtraction` now imports `LocalEMContext`, that one root already pulls in the whole
local stack. `LocalEMContext` is imported explicitly too, as a manifest anchor. Together
these imports transitively cover:

* `Methods/Skolem.lean` → `SkolemColimit.lean` → `SkolemClosure.lean` — the full
  (uncountable) Skolem tower `skolemStage`/`skolemColim` and the countable staged
  family `Γ*`;
* `Methods/EMTermModel.lean` — the EM term model over `(skolemColim L)[[J]]` with the
  staged truth lemma `truthLemmaStage`;
* `Methods/LocalEMSupport.lean` → `LocalSkolem.lean` → `LocalTower.lean` → `LocalColimit.lean`
  → `LocalEMFamily.lean` → {`LocalEMExtraction.lean`, `LocalEMContext.lean` → `LocalEMTruth.lean`
  → `LocalEMTruthLemma.lean`}
  — the countable family-restricted re-base (shared generic support, `localSkolem`, the mutually
  recursive `Llocal`/`Γlocal` tower with `skolemNeed`, the countable colimit `localColim` with
  cocone and semantic transport, the countable atom/deForm family `ΓEMlocal` with the canonical
  J-free seeds and the `EMContext`-instantiation membership interface, the extraction bridge
  `exists_ΓEMlocal_tail_indiscernible`, the generic deep-interpretation/realize-bridge semantic
  layer, the `LocalEMEq` quotient carrier + `Λ[[J]]`-`Structure`, the local Skolem-witness
  transport `locSkWitnessTerm`/`locDeepInterp_skWitness`/`locSkWitness_universal`, and the
  truth-lemma endpoints: the `OmegaComplete` mixin, `TLReady`/`TLReadyStage` readiness with the
  `DeFormClosedForColim` mixin + `ΓEMlocal` discharger, and the staged truth lemma
  `LocalEMContext.truthLemmaStage` with its stage-`k` lift corollary `truthLemmaStage_of_mem`);
* `Methods/LocalEMTemplateRealization.lean` — the template-realization bridge (imports the
  EM-side template machinery, stays Conditional-free): `LocalStage.ofSeq`, the
  subsequence-preserving Ramsey extraction `exists_orderEmb_tailIndiscernible_ΓEMlocal` +
  `exists_localEMContext_subseq`, template preservation under subsequence, the parameterized EM
  model theorem `LocalEMContext.templateTheoryOn_seed_model`, and the per-`s` acceptance lemma
  `tailTemplateRealizable_of_localEM` (hypothesis-relative; its ∀-`s` closure is false-shaped —
  a `{Pᵢ} ∪ {⋀ᵢ Pᵢ}` seed against a height model defeats any extraction — so the named
  residuals are seed-specific and source-aware: `MorleySeedOmegaExtraction` and its cleanest
  form `MorleySeedOmegaHomogeneousExtraction`, both over `morleySeed φ = {φ, x₀ ≠ x₁}` with the
  `ℶ_{ω₁}`/`φ`-realization/pairwise source facts);
* `Methods/LocalEMOmegaResidual.lean` — the Conditional-facing one-theorem bridge
  `morleySeedTailTemplateRealizable_of_localEMOmega : MorleySeedOmegaExtraction L' →
  MorleySeedTailTemplateRealizable` (modulo the bridge's extra function-symbol countability),
  isolating the `Conditional/MorleyHanfTransfer` import like `LocalEMExtraction`. **Audit
  outcome:** both seed Ω-residuals are REFUTED there (`height_no_seed_omega_homogeneous`,
  `not_morleySeedOmegaHomogeneousExtraction_height`, `not_morleySeedOmegaExtraction_height`) —
  the height pattern hides inside the true seed sentence `∃x, ¬⋀ᵢ Pᵢ(x)`, whose subformula
  closure re-imports the divergent conjunction into `ΓlocalColim`, defeating the uniform
  `iInf`-cutoff on every subsequence; those artifacts are kept as permanent fences.
  **The honest route (the reshape, end of that file):**
  `morleySeedTailTemplateRealizable_of_morleyHanfExtraction` wires the classical
  full-indiscernibility extraction residual `MorleyHanfExtraction` — a fresh fully indiscernible
  sequence from `M`, the `ℶ_{ω₁}` premise doing real Erdős–Rado work — through
  `omegaCompleteForColim_of_indiscernibleOn` (full indiscernibility kills witness drift, via the
  constructor-inversion component plumbing `iSup/iInf_component_mem_ΓlocalColim`) and the
  absolute Morley-seed template agreement (`morleySeed_template_agreement`), into the existing
  truth-lemma pipeline; `morley_hanf_of_morleyHanfExtraction` derives the Hanf bound from the
  extraction alone — over any countable-relational `L'`, with the tower's function-symbol
  countability discharged by the generated sublanguage (`Methods/GeneratedSublanguage.lean`:
  `functionsIn`/`funSublang`/`restrictFuns`, plus the `expandFunStructure` re-expansion and the
  `IsEmpty J` fallback in `LocalEMOmegaResidual`). The bridge is normalized down to partition
  calculus: `morley_hanf_of_pureColoring` (no compactness oracle — superseding the legacy
  `*_pureColoring_and_compact` wrappers) and `morley_hanf_of_finiteArityErdosRado` with
  hypothesis `FiniteArityErdosRadoOmega1 ℶ_1` (`Combinatorics/FiniteArityErdosRado.lean`).
  **Second audit outcome (statement audit 2026-07-07):** the whole in-`M` extraction ladder —
  `FiniteArityErdosRadoOmega1`, `PureColoringHypothesis`, `IndiscernibleSequenceHypothesis`,
  `MorleyHanfExtraction` — is FALSE-SHAPED, refutable in ZFC via the Erdős-cardinal argument
  (`ℶ_ω₁ ↛ (ω)^{<ω}_2`: the least `κ → (ω)^{<ω}_2` is the inaccessible `κ(ω) > ℶ_ω₁`; full
  fences with citations on `PureColoringHypothesis` and `FiniteArityErdosRadoOmega1`). The
  bridges remain true implications and the local-EM truth-lemma pipeline they exercise is fully
  proved; the honest continuation is the template/consistency-property reshape (Marker §5.2 —
  per-arity bounded ER approximations certify an EM template, the sequence materializes in the
  constructed model), the next design chunk;
* `Combinatorics/PairErdosRadoGeneral.lean` — the **parameterized pair Erdős–Rado**, ER hard
  chunk 1: a controlled, sorry-free extraction of the active EHMR path from the legacy
  `ErdosRado.lean` (fresh namespace `PairERGen`, ~61 declarations), generalized from
  `Bool`/`ℵ₀` to an arbitrary color bound — `pairErdosRado_general` (`#C ≤ κ`, source
  `Source κ = ((2^κ)⁺).ord.ToType` ⇒ a `κ⁺`-suborder pair-monochromatic), the abstract-source
  wrapper `pairErdosRado_general_of_large` (any well-ordered `I` with `#I ≥ (2^κ)⁺`), and the
  regression check `erdos_rado_pair_omega1_from_general` recovering the legacy Bool/ℵ₀ shape at
  `κ = ℵ₀`. Cardinal arithmetic isolated in a helpers section (`mk_source`,
  `succ_le_two_power`, `mk_node_le`, `succ_mul_two_power`, `ordIso_ordToType_of_card_ge`);
* `Combinatorics/EndHomogeneousErdosRado.lean` — the **arity-general end-homogenization
  engine**, ER hard chunk 2a (EHMR with tuple-typed nodes, namespace `EndHomogER`):
  `exists_endHomogeneous_of_large` (source `#I ≥ (2^λ)⁺` ⇒ a `λ⁺`-suborder on which the color
  of any `(n+2)`-tuple is independent of its final point), with the regression check
  `pairER_from_endHomogeneous` recovering the pair theorem at `n = 0`;
* `Combinatorics/FiniteArityErdosRadoInduction.lean` — the **finite-arity induction and the
  bounded theorem**, ER chunk 2b: the cardinal ladder `finiteERBound` with its beth bounds,
  the easy arities `0`/`1`/`2`, the hard step `finiteArityHomogeneousUpTo_step`
  (end-homogenize the top arity, feed the induced color to the IH), and the assembled
  `finiteArityErdosRadoBounded` (+ `_beth_one`) — one `κ⁺`-suborder homogeneous for all
  arities `≤ N` simultaneously, every finite `N`, plus the Marker-stage supply
  `finiteArityHomogeneousUpTo_beth_stage` (per-`α`, per-`N` approximations). This is the
  TRUE bounded supply for the template/consistency-property reshape; the all-arity jump to
  `FiniteArityErdosRadoOmega1` is refutable (see the audit fences);
* `Methods/MarkerStage.lean` — reshape layer 1, the finite-fragment certification bridge:
  `exists_markerSupport_factor` (collect + enumerate the finite `J`-constant support of a
  fragment's index data, factor every tuple through it) and `markerStage_homogeneous`
  (pull the fragment back to one arity-`k` truth-vector coloring over the source and apply
  the Marker-stage supply: for every `α < ω₁`, a `(ℶ_α)⁺`-suborder on which the whole
  fragment's truth vector is tuple-independent). **This program is COMPLETE** (2026-07-10):
  the schema route (`Methods/SchemaCompletion`, `Methods/SchemaTermModel`,
  `Methods/SchemaTermTruth`, `Methods/LocalSkolemUniversal`, `Methods/SchemaLocalEMSource`)
  proved `MorleySeedTailTemplateRealizable`, and the unconditional `morley_hanf` endpoint
  lives in `Conditional/MorleyHanfSchemaDischarge.lean`. The schema files are therefore now
  ALSO part of the `Everything` closure (through the discharge); they remain listed here
  while their docstring narrative is being stabilized.

These modules are deliberately NOT part of `InfinitaryLogic.All` or
`InfinitaryLogic.Everything` — they are under active construction. This target exists
so CI typechecks them (`lake build InfinitaryLogicWIP`), preventing silent regressions
at toolchain bumps.
-/
