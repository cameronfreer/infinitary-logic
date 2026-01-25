# Implementation Notes

## Current Sorry Status

### AtomicDiagram.lean
- `sameAtomicType_iff_realize_atomicDiagram` - **FILLED** (classical simp + case split)

### Formula.lean
- `scottFormula` definition uses placeholder `if α = 0 then ... else sorry`
  - **Fix**: Replace with `Ordinal.limitRecOn` recursion:
    ```lean
    noncomputable def scottFormula (a : Fin n → M) : Ordinal → L.Formulaω (Fin n) :=
      Ordinal.limitRecOn
        (atomicDiagram (L := L) (M := M) a)
        (fun α φα =>
          haveI : Encodable M := Encodable.ofCountable M
          φα ⊓
          einf (fun m : M => existsLastVar (scottFormula (snoc a m) α)) ⊓
          forallLastVar (esup (fun m : M => scottFormula (snoc a m) α)))
        (fun α ih => einf (fun ⟨β, hβ⟩ => ih β hβ))
    ```

- `realize_scottFormula_iff_BFEquiv` - needs `BoundedFormulaω.realize_relabel` lemma
  - **Dependency**: Port `BoundedFormula.realize_relabel` from `Mathlib/ModelTheory/Semantics.lean`
  - Without this lemma, the successor-step proof (for existsLastVar/forallLastVar) is painful

### Sentence.lean
- `BFEquiv_succ_implies_extend_fg` - uses BF forth property to extend FGEquiv
- `BFEquiv_implies_isExtensionPair` - repeated application of forth
- `exists_stabilization` - key cardinality argument
  - **Hint**: Use `Ordinal.iSup_sequence_lt_omega_one` from `Mathlib/SetTheory/Cardinal/Regular.lean`
  - Uses countability of space of FGEquivs
- `scottSentence_characterizes` - main theorem, uses `equiv_between_cg` from `Mathlib/ModelTheory/PartialEquiv.lean`

### Rank.lean
- `stabilizationOrdinal_le_scottRank` - elementRank bounds stabilization
- `scottRank_lt_omega1` - supremum of countably many countable ordinals
  - **Hint**: Use `Ordinal.iSup_sequence_lt_omega_one`
- `scottSentence_eq_scottFormula_rank` - equality at rank level
- `elementRank_lt_omega1` - each element rank is countable

## Key API References

### Ordinal recursion
- `Ordinal.limitRecOn` - recursion with zero/succ/limit cases
- Case names in tactics: `zero`, `succ`, `limit`
- Limit case uses `Order.IsSuccLimit` (not `Ordinal.IsLimit`)
- Successor uses `Order.succ` (not `α + 1` in pattern matching)

### BFEquiv signature
```lean
def BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop
```
Note: `n` is **explicit**, not implicit!

### Mathlib PartialEquiv API
- `L.FGEquiv M N` - finitely generated partial isomorphisms
- `L.IsExtensionPair M N` - extension property
- `equiv_between_cg` - main isomorphism construction from extension pairs

### Countable ordinal bounds
- `Ordinal.omega 1` (not `Ordinal.omega1`)
- `Ordinal.iSup_sequence_lt_omega_one` for supremum bounds
