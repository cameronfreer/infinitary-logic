# Checkpoint 5b-1: reviewed plan and compiling Lean probe

Date: 2026-07-10  
Audited against: `3db339e`  
Lean source files modified: none

## Verdict

The proposed `Finset.sup` equalizer is sound and materially simpler than the anchor-block construction. The complete chain below was checked with Lean LSP as one standalone snippet and compiled with no diagnostics:

1. the global strictly monotone equalizer;
2. the finite admissible pair through the Marker certificate suborder;
3. `schemaCompletionTheory_tuple_uniform` for every member of `ΓEMlocal s₀`.

The no-support-enlargement observation is correct. `MarkerHenkinBody` asks for strict monotonicity and membership in `range e` only on its certificate support `S`. Values away from `S` are free. The construction nevertheless controls the tuple entries by including them only in the auxiliary finite bounding set

```lean
A := (S ∪ univ.image t) ∪ univ.image t'
```

used to choose `K`. This does **not** enlarge the support passed to the Marker body.

Two minor review notes:

- `exists_strictMono_equalizer` is Mathlib-only, but `exists_admissible_pair` uses the project theorem `exists_orderEmb_fin` from `MarkerStage.lean`. That is already in scope through `SchemaCompletion` and is the intended API.
- A public theorem whose statement mentions a `private abbrev schemaLift` is legal and the probe compiles, but it is not the nicest downstream API. In production, either make the lift constructor public (it will be reused in 5b-3) or state `schemaCompletionTheory_tuple_uniform` with the two expanded `mapLanguage` expressions.

The formula works for `m = 0`: both filters are empty, `Finset.sup` is `0`, and both equalizers reduce to strictly monotone translations of the identity.

## Standalone compiling probe

The following block can be placed in a scratch file and checked with

```bash
lake env lean Scratch.lean
```

It contains no `sorry` and no custom axiom.

```lean
import InfinitaryLogic.Methods.SchemaCompletion

namespace FirstOrder.Language

open Cardinal

private def equalizerShift {m : ℕ} (p' : Fin m → ℕ) (p : Fin m → ℕ) (x : ℕ) : ℕ :=
  (Finset.univ.filter fun i => p i ≤ x).sup p'

private theorem equalizerShift_mono {m : ℕ} (p' : Fin m → ℕ) (p : Fin m → ℕ) :
    Monotone (equalizerShift p' p) := by
  intro x y hxy
  apply Finset.sup_mono
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans hxy⟩

private theorem equalizerShift_anchor {m : ℕ} {p p' : Fin m → ℕ}
    (hp : StrictMono p) (hp' : StrictMono p') (i : Fin m) :
    equalizerShift p' p (p i) = p' i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    rw [Finset.mem_filter] at hj
    exact hp'.monotone ((hp.le_iff_le).mp hj.2)
  · apply Finset.le_sup
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, le_rfl⟩

theorem exists_strictMono_equalizer {m : ℕ} (p p' : Fin m → ℕ)
    (hp : StrictMono p) (hp' : StrictMono p') :
    ∃ q q' : ℕ → ℕ, StrictMono q ∧ StrictMono q' ∧
      ∀ i, q (p i) = q' (p' i) := by
  let q : ℕ → ℕ := fun x => x + equalizerShift p' p x
  let q' : ℕ → ℕ := fun x => equalizerShift p p' x + x
  have hq : StrictMono q := by
    intro x y hxy
    exact Nat.add_lt_add_of_lt_of_le hxy (equalizerShift_mono p' p hxy.le)
  have hq' : StrictMono q' := by
    intro x y hxy
    exact Nat.add_lt_add_of_le_of_lt (equalizerShift_mono p p' hxy.le) hxy
  refine ⟨q, q', hq, hq', fun i => ?_⟩
  rw [show q (p i) = p i + equalizerShift p' p (p i) from rfl,
    show q' (p' i) = equalizerShift p p' (p' i) + p' i from rfl,
    equalizerShift_anchor hp hp' i, equalizerShift_anchor hp' hp i,
    Nat.add_comm]

theorem exists_admissible_pair
    {M D : Type} [LinearOrder M] [LinearOrder D] [Infinite D]
    {m : ℕ} (S : Finset ℕ) (e : D ↪o M)
    (t t' : Fin m ↪o ℕ) (dflt : M) :
    ∃ σ₁ σ₂ : ℕ → M,
      StrictMonoOn σ₁ ↑S ∧ (∀ j ∈ S, σ₁ j ∈ Set.range e) ∧
      StrictMonoOn σ₂ ↑S ∧ (∀ j ∈ S, σ₂ j ∈ Set.range e) ∧
      ∀ i, σ₁ (t i) = σ₂ (t' i) := by
  classical
  obtain ⟨q, q', hq, hq', heq⟩ :=
    exists_strictMono_equalizer t t' t.strictMono t'.strictMono
  let A : Finset ℕ := (S ∪ Finset.univ.image t) ∪ Finset.univ.image t'
  let B : ℕ := A.sup id
  let K : ℕ := max (q B) (q' B) + 1
  let dEmb : Fin K ↪o D := Classical.choice (exists_orderEmb_fin K)
  have hbound_q {j : ℕ} (hj : j ∈ A) : q j < K := by
    have hjB : j ≤ B := by
      dsimp only [B]
      exact Finset.le_sup (f := id) hj
    calc
      q j ≤ q B := hq.monotone hjB
      _ ≤ max (q B) (q' B) := le_max_left _ _
      _ < max (q B) (q' B) + 1 := Nat.lt_succ_self _
  have hbound_q' {j : ℕ} (hj : j ∈ A) : q' j < K := by
    have hjB : j ≤ B := by
      dsimp only [B]
      exact Finset.le_sup (f := id) hj
    calc
      q' j ≤ q' B := hq'.monotone hjB
      _ ≤ max (q B) (q' B) := le_max_right _ _
      _ < max (q B) (q' B) + 1 := Nat.lt_succ_self _
  let σ₁ : ℕ → M := fun j =>
    if hj : q j < K then e (dEmb ⟨q j, hj⟩) else dflt
  let σ₂ : ℕ → M := fun j =>
    if hj : q' j < K then e (dEmb ⟨q' j, hj⟩) else dflt
  have hSA {j : ℕ} (hj : j ∈ S) : j ∈ A := by
    simp only [A, Finset.mem_union]
    exact Or.inl (Or.inl hj)
  have htA (i : Fin m) : t i ∈ A := by
    simp only [A, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image_of_mem t (Finset.mem_univ i)))
  have htA' (i : Fin m) : t' i ∈ A := by
    simp only [A, Finset.mem_union]
    exact Or.inr (Finset.mem_image_of_mem t' (Finset.mem_univ i))
  refine ⟨σ₁, σ₂, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · intro a ha b hb hab
    rw [show σ₁ a = if h : q a < K then e (dEmb ⟨q a, h⟩) else dflt from rfl,
      show σ₁ b = if h : q b < K then e (dEmb ⟨q b, h⟩) else dflt from rfl,
      dif_pos (hbound_q (hSA (Finset.mem_coe.mp ha))),
      dif_pos (hbound_q (hSA (Finset.mem_coe.mp hb)))]
    exact e.strictMono (dEmb.strictMono (hq hab))
  · intro j hj
    rw [show σ₁ j = if h : q j < K then e (dEmb ⟨q j, h⟩) else dflt from rfl,
      dif_pos (hbound_q (hSA hj))]
    exact ⟨dEmb ⟨q j, hbound_q (hSA hj)⟩, rfl⟩
  · intro a ha b hb hab
    rw [show σ₂ a = if h : q' a < K then e (dEmb ⟨q' a, h⟩) else dflt from rfl,
      show σ₂ b = if h : q' b < K then e (dEmb ⟨q' b, h⟩) else dflt from rfl,
      dif_pos (hbound_q' (hSA (Finset.mem_coe.mp ha))),
      dif_pos (hbound_q' (hSA (Finset.mem_coe.mp hb)))]
    exact e.strictMono (dEmb.strictMono (hq' hab))
  · intro j hj
    rw [show σ₂ j = if h : q' j < K then e (dEmb ⟨q' j, h⟩) else dflt from rfl,
      dif_pos (hbound_q' (hSA hj))]
    exact ⟨dEmb ⟨q' j, hbound_q' (hSA hj)⟩, rfl⟩
  · rw [show σ₁ (t i) =
        if h : q (t i) < K then e (dEmb ⟨q (t i), h⟩) else dflt from rfl,
      show σ₂ (t' i) =
        if h : q' (t' i) < K then e (dEmb ⟨q' (t' i), h⟩) else dflt from rfl,
      dif_pos (hbound_q (htA i)), dif_pos (hbound_q' (htA' i))]
    apply congrArg e
    apply congrArg dEmb
    apply Fin.ext
    exact heq i

private abbrev schemaLift {s₀ : LocalStage} {m : ℕ}
    (ψ : (localColim s₀).BoundedFormulaω Empty m) (t : Fin m ↪o ℕ) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)

private theorem schemaLift_mem_universe {s₀ : LocalStage} {m : ℕ}
    {ψ : (localColim s₀).BoundedFormulaω Empty m}
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t : Fin m ↪o ℕ) :
    (⟨schemaLift ψ t, hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
  Set.mem_biUnion hψ ⟨t, rfl⟩

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

theorem schemaCompletionTheory_tuple_uniform
    {m : ℕ} {ψ : (localColim s₀).BoundedFormulaω Empty m}
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t t' : Fin m ↪o ℕ) :
    schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift ψ t' ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  classical
  have transfer : ∀ (u v : Fin m ↪o ℕ),
      schemaLift ψ u ∈ schemaCompletionTheory (schemaEnumeration s₀) hM →
        schemaLift ψ v ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    intro u v hu
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaLift_mem_universe hψ v) with hv | hnv
    · exact hv
    · exfalso
      let F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) :=
        {schemaLift ψ u, (schemaLift ψ v).not}
      have hF : ∀ τ ∈ F,
          τ ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
        intro τ hτ
        change τ ∈ {schemaLift ψ u, (schemaLift ψ v).not} at hτ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
        rcases hτ with rfl | rfl
        · exact hu
        · exact hnv
      obtain ⟨S, H, hS, hH, hcof⟩ :=
        (schemaCompletionTheorySpec hM).finite_consistent F hF
      obtain ⟨α, hα0, hα1, hbody⟩ := hcof 0 (Ordinal.omega_pos 1)
      obtain ⟨e, hsat⟩ := hbody
      let D := (Order.succ (Cardinal.beth α)).ord.ToType
      haveI : Infinite D := by
        rw [show D = (Order.succ (Cardinal.beth α)).ord.ToType from rfl,
          Cardinal.infinite_iff, Cardinal.mk_ord_toType]
        exact (Cardinal.aleph0_le_beth α).trans (Order.le_succ _)
      let dflt : M := e (Classical.arbitrary D)
      obtain ⟨σ₁, σ₂, hσ₁mono, hσ₁range, hσ₂mono, hσ₂range, heq⟩ :=
        exists_admissible_pair S e u v dflt
      obtain ⟨w₁, hw₁⟩ := hsat σ₁ hσ₁mono hσ₁range
      obtain ⟨w₂, hw₂⟩ := hsat σ₂ hσ₂mono hσ₂range
      have hpos := hw₁ (schemaLift ψ u) (by
        rw [Finset.mem_coe]
        exact Finset.mem_insert_self _ _)
      have hneg := hw₂ (schemaLift ψ v).not (by
        rw [Finset.mem_coe]
        change (schemaLift ψ v).not ∈ {schemaLift ψ u, (schemaLift ψ v).not}
        simp)
      rw [schemaLift, realizeWith_templateSentence] at hpos
      rw [realizeWith_not, schemaLift, realizeWith_templateSentence] at hneg
      apply hneg
      rw [show (fun i => σ₂ (v i)) = fun i => σ₁ (u i) from
        funext fun i => (heq i).symm]
      exact hpos
  exact ⟨transfer t t', transfer t' t⟩

end FirstOrder.Language
```

## Suggested production split

The proposed two-commit split is good:

1. `exists_strictMono_equalizer` plus `exists_admissible_pair`;
2. the lift/universe helper plus `schemaCompletionTheory_tuple_uniform`.

Keep `equalizerShift`, `equalizerShift_mono`, and `equalizerShift_anchor` private. `exists_admissible_pair` is useful only for this Marker proof at present, so it can also be private unless another checkpoint consumes it.

There is no need to change `SchemaCompletionTheorySpec`, and this work is independent of the later negative-`iInf` completion repair. The negative-`iInf` repair remains necessary before the restricted truth lemma, but it does not block landing 5b-1 first.

## Validation performed

- `exists_strictMono_equalizer`: compiled separately with no diagnostics.
- `exists_admissible_pair`: compiled together with the equalizer, including empty supports and zero-arity tuples at the type level.
- full standalone block through `schemaCompletionTheory_tuple_uniform`: compiled with no diagnostics.
- no `.lean` file was created or edited.

