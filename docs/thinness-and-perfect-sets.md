# Thinness and perfect sets

The counting results in `InfinitaryLogic/Descriptive/` are stated cardinally: bounds such as
`≤ ℵ₀` or `≤ ℵ₁`, and alternatives of exactly `2^ℵ₀`. The underlying dichotomies are sharper than
that.
On the "many classes" side, the classical proofs produce a **witness** — a perfect set of pairwise
inequivalent points — and cardinality is a consequence of that witness rather than the primary
output.

This note describes the vocabulary the repository supplies for talking about such witnesses, and
the one criterion it supplies for ruling them out. It is a description of what exists, not a plan.

## The generic vocabulary

All of it lives in `InfinitaryLogic/Descriptive/PerfectAntichain.lean`, stated for an arbitrary
`Setoid X` on an arbitrary topological space, with no model theory involved.

### `IsThinOn r A`

`A` is **thin** for `r` when it carries no perfect antichain:

```lean
def IsThinOn (r : Setoid X) (A : Set X) : Prop := ¬HasPerfectAntichainOn r A
```

Thinness is thus the *absence of an ambient perfect antichain* — a statement about the topology `X`
already carries, not about any refinement chosen to make some subset nicer.

### `HasPerfectAntichainOn r A`

A nonempty perfect `P ⊆ A` whose points are pairwise `r`-inequivalent.

### `HasCantorAntichainOn r A`

A continuous `f : (ℕ → Bool) → X` landing in `A` and sending distinct points to `r`-inequivalent
ones. This is the **load-bearing intermediary**, and it is worth being explicit about why it exists
as a separate notion rather than being folded into the perfect-set form:

- it is what the Cantor-scheme builders produce directly (`CantorScheme.hasCantorAntichainOn`);
- it is the form a thinness proof must actually refute;
- it needs no metric or completeness assumptions to state, so results that consume it keep
  minimal hypotheses.

Injectivity of a Cantor antichain is *derived*, not assumed: distinct arguments have inequivalent
images, and every point is equivalent to itself, so `HasCantorAntichainOn.injective` follows from
reflexivity alone.

## The two chains

```
perfect antichain  ←──→  Cantor antichain  ──→  continuum-many classes
ThinRankAnalysis   ──→  no Cantor antichain  ──→  thinness
structureIsoSetoid + ModelsOf φ  ──→  IsThinOnNatModels
```

The first chain is now an equivalence, but the two directions cost very different hypotheses:

- `HasPerfectAntichainOn.hasCantorAntichainOn` goes via `Perfect.exists_nat_bool_injection` and
  needs a **complete metric space**;
- `HasCantorAntichainOn.hasPerfectAntichainOn` needs only **`T2Space`**. A continuous injection
  out of Cantor space into a Hausdorff space is a closed embedding, so its range is closed; and
  the range inherits Cantor space's lack of isolated points by transporting accumulation points
  along that injection (`AccPt.map`). No metric, completeness, or second-countability enters.

`HasCantorAntichainOn.continuum_le_quotient` closes the chain and needs only a topology.

The Hausdorff-only direction is why `HasCantorAntichainOn` is worth keeping as a separate notion:
a construction that produces one gets the ambient perfect set for free, without first having to
exhibit a metric on the ambient space.

## The model-theoretic specialization

`InfinitaryLogic/Descriptive/StructureIsoSetoid.lean` defines isomorphism once, ambiently, on
`StructureSpace L`, and obtains `isoSetoid φ` on `↥(ModelsOf φ)` as its restriction. That ordering
is what makes the sentence-level predicate honest:

```lean
def Sentenceω.IsThinOnNatModels (φ : L.Sentenceω) : Prop :=
  IsThinOn (structureIsoSetoid L) (ModelsOf φ)
```

Perfectness here is a property of a subset of the ambient `StructureSpace L`. If the predicate were
instead stated on the subtype `↥(ModelsOf φ)`, it would silently be a statement about whichever
Polish refinement was chosen to make that subtype standard Borel — a different assertion.

### Getting back from the refinement

That raises the obvious problem: a Cantor antichain is *built* where the model class is well
behaved, namely in a finer Polish topology of the kind `modelsOf_isClopenable` supplies, while the
perfect set has to be perfect in the ambient space. Proving directly that perfectness survives
coarsening would be delicate — and false in general.

The two steps are therefore ordered so the delicate one never arises:

```
IsClopenable refinement  (t' ≤ t)
  → Cantor antichain in t'
  → Cantor antichain in t          HasCantorAntichainOn.mono_topology
  → ambient perfect antichain      HasCantorAntichainOn.hasPerfectAntichainOn
```

Coarsening is applied to the *Cantor* antichain, where only the continuity clause is topological;
perfectness is then obtained in the ambient space.
`Sentenceω.hasPerfectSet_of_refined_cantorAntichain` packages the chain, and
`Sentenceω.exists_clopenable_refinement_forcing_perfectSet` records that the refinement
`modelsOf_isClopenable` produces is one the chain accepts — retaining the closedness and openness
of `ModelsOf φ` in `t'` in its conclusion, so a consumer that needs the clopen structure keeps it.

## The thinness criterion

`InfinitaryLogic/Descriptive/RankedThinness.lean` supplies the standard rank argument.
`ThinRankAnalysis r A` is a structure carrying four pieces of **evidence**: a rank function, the
fact that ranks on `A` are `< ω₁`, countability of each fixed-rank antichain, and boundedness of
the rank on any Cantor antichain.

`no_cantorAntichain` and `isThinOn` are **derived theorems, not fields**. A structure whose fields
already asserted thinness would prove nothing; the content is that this particular evidence
suffices.

**ThinRankAnalysis packages sufficient evidence for thinness, and `ThinRankAnalysis.isThinOn`
proves the implication. No concrete instance of that package is supplied here.** The repository
provides the criterion, not an application of it.

Its `[MetricSpace] [CompleteSpace]` hypotheses are *not* relaxed by the cheap Hausdorff direction
above: `isThinOn` consumes `IsThinOn.of_no_cantorAntichain`, which is the perfect → Cantor
direction. The cheap direction gives the companion `IsThinOn.no_cantorAntichain` instead.

## Two things that do not follow

**Cardinal equality does not establish thinness.** Knowing that the quotient has exactly `ℵ₁`
classes does not establish thinness in ZFC. Under CH, `ℵ₁ = 2^ℵ₀`, so that cardinality is
compatible with a perfect antichain. Under `¬CH`, exact `ℵ₁` does rule out a perfect antichain.

Separately, the counting theorems as stated forget the witness: the `SilverBurgessDichotomy`
hypothesis concludes with a cardinal disjunction and retains nothing from which a perfect set
could be extracted. Consequently, the current cardinal interface cannot itself produce a
perfect-set witness.

**"Scattered" is not formalized.** Terminology involving "scattered" varies in the literature and
is not formalized here; no `IsScattered` alias is introduced. The repository uses *thin*
throughout, for one notion under one name.
