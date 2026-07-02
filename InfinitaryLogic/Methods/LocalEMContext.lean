/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMFamily
import InfinitaryLogic.Methods.Henkin.Construction

/-!
# The local EM context, layer 1: deep interpretation and realize bridges

The semantic layer of the `EMContext` re-base, **generic over `Λ`**: the deep interpretation of
closed `Λ[[J]]`-terms in a source model and the realize bridges connecting it to the syntactic
de-substitution pipeline of `LocalEMFamily.lean`. Mirrors the `skolemColim`-specific chain of
`EMTermModel.lean`, with one systematic simplification: every original proof touched the language
structure only through `letI := skolemColimStructure L`, so here the structure is simply the
ambient instance `[Λ.Structure M]` — `localColimStructure` enters only at instantiation sites
(as in `LocalEMExtraction.lean`). No `[Nonempty M]` is needed (no Hilbert choice in this layer).

Contents (source lemma in `EMTermModel.lean` in parentheses):
* `locDeepInterp` (`deepInterp`) + `locDeepInterp_func`, and the realization bridges
  `locDeepInterp_eq_realize`, `locDeepInterp_subst`, `locDeepInterp_onTerm_subst`;
* the support bridge `locJSupport_onTerm_subst_subset` (`jSupport_onTerm_subst_subset`);
* the ordered-position/`Fin`-arity bridges `locDeepInterp_eq_realize_pos`,
  `locDeTermFin_realize` (`deepInterp_eq_realize_fin`), and the **superset realization
  invariance** `locDeTermFin_realize_superset`;
* the atom bridges `realize_locDeEqAtom(_superset)`, `realize_locDeRelAtom(_superset)` — the
  superset variants route through `locDeTermFin_realize_superset` instead of re-deriving the
  per-term key inline as the originals do;
* the general formula bridge `realize_locDeForm` (`realize_deForm`), consuming
  `realize_openBounds` (imported explicitly from `Methods/Henkin/Construction.lean`) and
  `realize_relabel_sumInr_zero` (from the `Lomega1omega` core).

Next layers (subsequent chunks): `locDeepInterp_snoc`, the `skolemNeedSymbol` witness-term
transport, local `EMEq`/quotient/congruence, and the family-membership-carrying restricted
truth lemma.
-/

namespace FirstOrder.Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-! ### Support of substituted base-language terms (syntactic) -/

/-- **Support of a base-language term after substitution**: substituting the closed terms `ts`
for the free variables of a base-language term `(onTerm t)` (which itself carries no
`J`-constants, being a `Λ`-image) produces only the `J`-constants of the `ts`. The bridge from a
uniform support hypothesis `S ⊇ ⋃ locJSupport (ts i)` to the per-atom support hypotheses of the
congruence layer. -/
theorem locJSupport_onTerm_subst_subset {n : ℕ} (t : Λ.Term (Empty ⊕ Fin n))
    (ts : Fin n → Λ[[J]].Term Empty) :
    locJSupport Λ J (((lhomWithConstants Λ J).onTerm t).subst (Sum.elim (fun e => e.elim) ts))
      ⊆ Finset.univ.biUnion fun i => locJSupport Λ J (ts i) := by
  induction t with
  | var x =>
    cases x with
    | inl e => exact e.elim
    | inr i =>
      exact Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (ts i)) (Finset.mem_univ i)
  | @func l f args ih =>
    have hjc : locJConstOf Λ J ((lhomWithConstants Λ J).onFunction f) = ∅ := by
      cases l <;> rfl
    show locJSupport Λ J (Term.func ((lhomWithConstants Λ J).onFunction f) _) ⊆ _
    rw [locJSupport, hjc, Finset.union_empty]
    exact Finset.biUnion_subset.mpr fun i _ => ih i

/-! ### Deep interpretation -/

section DeepInterp

variable {M : Type} [Λ.Structure M] (a : ℕ → M)

/-- The **deep interpretation** of a closed `Λ[[J]]`-term at depth `d` relative to a support `S`:
interpret each `J`-constant `c_j` by the source sequence at position `d + deepRank S j` (so
support constants map to a strictly-increasing deep tuple of `a`), and evaluate in `M`'s ambient
`Λ`-structure. -/
noncomputable def locDeepInterp (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) : M :=
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  t.realize Empty.elim

/-- Deep interpretation commutes with function application (same depth and support): it is the
structure's `funMap` of the argument interpretations. Immediate from `Term.realize`. -/
theorem locDeepInterp_func (d : ℕ) (S : Finset J) {n : ℕ}
    (f : Λ[[J]].Functions n) (ts : Fin n → Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S (.func f ts) =
      letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
      Structure.funMap f (fun i => locDeepInterp Λ J a d S (ts i)) :=
  rfl

/-- **De-substitution bridge**: the deep interpretation of a closed term equals the
*de-substituted* `Λ`-term `constantsToVars t` (each skeleton constant `c_j` turned into the
variable `Sum.inl j`) realized with `j ↦ a (d + deepRank S j)`. Turns the support machinery from
combinatorial into semantic — the right-hand side is a genuine formula realization, so tail
indiscernibility applies. -/
theorem locDeepInterp_eq_realize (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S t =
      t.constantsToVars.realize (Sum.elim (fun j => a (d + deepRank J S j)) Empty.elim) := by
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  show t.realize Empty.elim = _
  exact (Term.realize_constantsToVars (t := t) (v := Empty.elim)).symm

/-- **M-side term substitution**: the deep interpretation of a substituted term is the
realization (in `M`'s `[[J]]`-structure at depth `d`) of the body on the deep interpretations of
the substituted terms. Mostly `Term.realize_subst` (deep interpretation *is* realization in the
depth-`d` structure). -/
theorem locDeepInterp_subst (d : ℕ) (S : Finset J) {n : ℕ}
    (t : Λ[[J]].Term (Empty ⊕ Fin n)) (ts : Fin n → Λ[[J]].Term Empty) :
    letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
    locDeepInterp Λ J a d S (t.subst (Sum.elim (fun e => e.elim) ts)) =
      t.realize (Sum.elim Empty.elim fun i => locDeepInterp Λ J a d S (ts i)) := by
  letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
  show (t.subst (Sum.elim (fun e => e.elim) ts)).realize Empty.elim = _
  rw [Term.realize_subst]
  congr 1
  funext x
  cases x with
  | inl e => exact e.elim
  | inr i => rfl

/-- **Deep interpretation of a base-language substituted term**: combining `locDeepInterp_subst`
with `realize_onTerm`, the deep interpretation of `(onTerm t).subst ts` equals `t` realized in
`M`'s ambient `Λ`-structure on the deep interpretations of the substituted terms. -/
theorem locDeepInterp_onTerm_subst (d : ℕ) (S : Finset J) {n : ℕ}
    (t : Λ.Term (Empty ⊕ Fin n)) (ts : Fin n → Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S
        (((lhomWithConstants Λ J).onTerm t).subst (Sum.elim (fun e => e.elim) ts)) =
      t.realize (Sum.elim Empty.elim fun i => locDeepInterp Λ J a d S (ts i)) := by
  letI : (constantsOn J).Structure M := constantsOn.structure fun j => a (d + deepRank J S j)
  rw [locDeepInterp_subst]
  exact LHom.realize_onTerm (lhomWithConstants Λ J) t _

/-! ### Ordered-position and `Fin`-arity realize bridges -/

/-- **Ordered-position realize bridge**: the deep interpretation is the realize of the
ordered-position de-substituted term on the *consecutive* deep tuple `n ↦ a (d + n)` — exactly
the shape tail indiscernibility consumes (a strictly-increasing deep tuple). -/
theorem locDeepInterp_eq_realize_pos (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S t = (locDeTermPos Λ J S t).realize (fun n => a (d + n)) := by
  rw [locDeepInterp_eq_realize, locDeTermPos, Term.realize_relabel]
  congr 1
  funext x
  cases x with
  | inl j => rfl
  | inr e => exact e.elim

/-- **`Fin`-arity realize bridge**: the deep interpretation is the realize of the
`Fin S.card`-indexed de-substituted term on the consecutive deep tuple `i ↦ a (d + i)`, directly
feeding the atoms. -/
theorem locDeTermFin_realize (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty)
    (hsub : locJSupport Λ J t ⊆ S) :
    locDeepInterp Λ J a d S t
      = (locDeTermFin Λ J S t hsub).realize (fun i : Fin S.card => a (d + i)) := by
  rw [locDeepInterp_eq_realize_pos, locDeTermFin]
  symm
  exact Term.realize_restrictVar (fun n => a (d + n)) (fun _ => rfl)

/-- **Superset realization invariance**: the `Fin`-arity de-substituted term over `S`, realized
on the `T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))`, equals the deep
interpretation over the larger support `T`. The core shared by the equality- and relation-atom
superset bridges (restrictVar realize with a `dite`-extended assignment, then
`realize_eq_of_eq_on_varFinset` to discard the junk, then `orderEmbOfFin_deepRank`). -/
theorem locDeTermFin_realize_superset (d : ℕ) (S T : Finset J) (w : Λ[[J]].Term Empty)
    (hw : locJSupport Λ J w ⊆ S) :
    (locDeTermFin Λ J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = locDeepInterp Λ J a d T w := by
  have hrv : (locDeTermFin Λ J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = (locDeTermPos Λ J S w).realize
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0)) := by
    rw [locDeTermFin]
    refine Term.realize_restrictVar
      (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
      (fun x => ?_)
    simp only [dif_pos (Finset.mem_range.mp (locDeTermPos_varFinset_subset (Λ := Λ) (J := J) hw x.2))]
  rw [hrv, locDeepInterp_eq_realize, locDeTermPos, Term.realize_relabel]
  apply Term.realize_eq_of_eq_on_varFinset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (locConstantsToVars_varFinset_subset Λ J w hx)
  have hjS : j ∈ S := hw hj
  have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
  simp only [Function.comp_apply, Sum.elim_inl, dif_pos hlt]
  rw [orderEmbOfFin_deepRank J S rfl hjS hlt]

/-! ### Atom and formula realize bridges -/

/-- **Equality-atom realize bridge**: the local de-substituted equality atom holds on the
consecutive deep tuple `i ↦ a (d + i)` iff `t` and `u` have equal deep interpretations at depth
`d` over `S`. -/
theorem realize_locDeEqAtom (d : ℕ) (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (locDeEqAtom Λ J S t u ht hu).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      locDeepInterp Λ J a d S t = locDeepInterp Λ J a d S u := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel,
    Term.realize_relabel, Sum.elim_comp_inr, ← locDeTermFin_realize (t := t) (hsub := ht),
    ← locDeTermFin_realize (t := u) (hsub := hu)]

/-- **Superset equality-atom bridge**: the *same* atom over `S`, realized on the `T`-induced deep
tuple (`S ⊆ T`), holds iff `t` and `u` have equal deep interpretations over `T`. One
arity-`S.card` formula carries both the `S`-truth (consecutive tuple) and the `T`-truth (this
strictly-increasing tuple) — the input to tail indiscernibility. -/
theorem realize_locDeEqAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T)
    (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (locDeEqAtom Λ J S t u ht hu).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      locDeepInterp Λ J a d T t = locDeepInterp Λ J a d T u := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel,
    Term.realize_relabel, Sum.elim_comp_inr,
    locDeTermFin_realize_superset (w := t) (hw := ht),
    locDeTermFin_realize_superset (w := u) (hw := hu)]

/-- **Relation-atom realize bridge**: the local de-substituted relation atom holds on the
consecutive deep tuple iff `R` holds in `M` on the deep interpretations over `S`. -/
theorem realize_locDeRelAtom (d : ℕ) (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (locDeRelAtom Λ J S R ts ht).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      Structure.RelMap R fun i => locDeepInterp Λ J a d S (ts i) := by
  rw [locDeRelAtom, canonRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, ← locDeTermFin_realize]

/-- **Superset relation-atom bridge**: the same relation atom over `S`, realized on the
`T`-induced deep tuple (`S ⊆ T`), holds iff `R` holds in `M` on the deep interpretations over
`T`. Via `locDeTermFin_realize_superset`. -/
theorem realize_locDeRelAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T) {l : ℕ}
    (R : Λ.Relations l) (ts : Fin l → Λ[[J]].Term Empty)
    (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (locDeRelAtom Λ J S R ts ht).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      Structure.RelMap R fun i => locDeepInterp Λ J a d T (ts i) := by
  rw [locDeRelAtom, canonRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, locDeTermFin_realize_superset]

/-- **General formula realize bridge** (generalizes the atom bridges): the local de-substituted
formula holds on the consecutive deep tuple `i ↦ a (d + i)` iff `φ` holds in `M`'s ambient
`Λ`-structure on the deep interpretations of `ts` at depth `d` over `S`. -/
theorem realize_locDeForm (d : ℕ) (S : Finset J) {n : ℕ}
    (φ : Λ.BoundedFormulaω Empty n)
    (ts : Fin n → Λ[[J]].Term Empty) (hsub : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (locDeForm Λ J S φ ts hsub).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      φ.Realize Empty.elim (fun i => locDeepInterp Λ J a d S (ts i)) := by
  have hassign : (fun i => (locDeTermFin Λ J S (ts i) (hsub i)).realize
        (fun i : Fin S.card => a (d + i)))
      = (fun i => locDeepInterp Λ J a d S (ts i)) :=
    funext fun i => (locDeTermFin_realize Λ J a d S (ts i) (hsub i)).symm
  rw [locDeForm, canonDeForm, BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.Realize, BoundedFormulaω.realize_subst]
  rw [hassign]
  exact realize_openBounds φ _

end DeepInterp

end FirstOrder.Language
