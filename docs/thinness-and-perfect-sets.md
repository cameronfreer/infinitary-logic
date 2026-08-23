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
perfect antichain  ──→  Cantor antichain  ──→  continuum-many classes
ThinRankAnalysis   ──→  no Cantor antichain  ──→  thinness
structureIsoSetoid + ModelsOf φ  ──→  IsThinOnNatModels
```

Left-to-right along the first chain: `HasPerfectAntichainOn.hasCantorAntichainOn` (via
`Perfect.exists_nat_bool_injection`, needing a complete metric space), then
`HasCantorAntichainOn.continuum_le_quotient`, which needs only a topology.

Only perfect antichain → Cantor antichain is currently formalized. The converse requires showing
that a continuous injective Cantor image has perfect range.

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
