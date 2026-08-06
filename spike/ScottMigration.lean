/-
SPIKE — Scott formulas on the carrier-parameterized syntax (roadmap items 5 and 6).

Item 5 (adoption test): the existing countable Scott construction ports. `einf`/`esup` call
sites become `iInfAlong`/`iSupAlong`, encoding choices are explicit at construction boundaries
(`ofEncodableWith`), and — because the tuple sits in BOUND positions — the entire
`relabel insertLastBound` layer (~130 lines of `Fin` plumbing in the production
`Scott/Formula.lean`) is not needed: `existsLast` and `.all` do the quantification directly.

Item 6 (new mathematics): the construction is stated FIRST at an abstract carrier `ι` with
explicit codings, with NO countability hypothesis on `M`, NO countability of the language, and
NO `α < ω₁` restriction:

  realize_scottApproxAt_iff_BFEquiv : … ↔ BFEquiv β k a b     (unconditional in β)
  scottApproxAt_qrank_le            : qrank ≤ β

The countable specialization recovers the production `scottFormula` up to semantic
equivalence — free from the two characterizations, since both sides are `↔ BFEquiv`. The
canonical carrier `M ⊕ (α.ToType ⊕ Σ k, L.AtomicIdx k)` is packaged last.

Build with:  lake build ScottMigration    (the Spike lib is not a CI target)
-/
import CarrierSyntax
import InfinitaryLogic.Scott.Formula

universe u v uι w w'

namespace FirstOrder.Language

open BoundedFormulaIdx Fin

variable {L : Language.{u, v}}

/-! ## Connective and rank prerequisites not yet in the spike core -/

namespace BoundedFormulaIdx

variable {ι : Type uι} {δ : Type*} {n : ℕ}

/-- Conjunction. -/
protected def and (φ ψ : L.BoundedFormulaIdx ι δ n) : L.BoundedFormulaIdx ι δ n :=
  (φ.imp ψ.not).not

instance : Min (L.BoundedFormulaIdx ι δ n) := ⟨BoundedFormulaIdx.and⟩

section RealizeInf

variable {M : Type w} [L.Structure M] {v : δ → M} {xs : Fin n → M}

@[simp] theorem realize_inf {φ ψ : L.BoundedFormulaIdx ι δ n} :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  show ((φ.imp ψ.not).not).Realize v xs ↔ _
  simp only [realize_not, realize_imp]
  tauto

end RealizeInf

@[simp] theorem qrank_not (φ : L.BoundedFormulaIdx ι δ n) : φ.not.qrank = φ.qrank := by
  show max φ.qrank (0 : Ordinal) = φ.qrank
  exact max_eq_left (Ordinal.bot_eq_zero ▸ bot_le)

@[simp] theorem qrank_inf (φ ψ : L.BoundedFormulaIdx ι δ n) :
    (φ ⊓ ψ).qrank = max φ.qrank ψ.qrank := by
  show (BoundedFormulaIdx.and φ ψ).qrank = _
  simp only [BoundedFormulaIdx.and, qrank_not, qrank_imp]

@[simp] theorem qrank_existsLast (φ : L.BoundedFormulaIdx ι δ (n + 1)) :
    (existsLast φ).qrank = Order.succ φ.qrank := by
  simp only [existsLast, qrank_not, qrank_all]

/-- Rank bound for coded conjunctions: the padding contributes only rank `0`. -/
theorem qrank_iInfAlong_le {ι' : Type*} (c : IndexCoding ι' ι)
    {φs : ι' → L.BoundedFormulaIdx ι δ n} {x : Ordinal.{uι}}
    (h : ∀ i, (φs i).qrank ≤ x) : (iInfAlong c φs).qrank ≤ x := by
  simp only [iInfAlong, qrank_iInf]
  refine Ordinal.iSup_le fun k => ?_
  rcases hd : c.decode k with _ | i
  · rw [c.pad_of_decode_none hd, qrank_top]
    exact Ordinal.bot_eq_zero ▸ bot_le
  · rw [c.pad_of_decode_some hd]
    exact h i

/-- Rank bound for coded disjunctions. -/
theorem qrank_iSupAlong_le {ι' : Type*} (c : IndexCoding ι' ι)
    {φs : ι' → L.BoundedFormulaIdx ι δ n} {x : Ordinal.{uι}}
    (h : ∀ i, (φs i).qrank ≤ x) : (iSupAlong c φs).qrank ≤ x := by
  simp only [iSupAlong, qrank_iSup]
  refine Ordinal.iSup_le fun k => ?_
  rcases hd : c.decode k with _ | i
  · rw [c.pad_of_decode_none hd, qrank_bot]
    exact Ordinal.bot_eq_zero ▸ bot_le
  · rw [c.pad_of_decode_some hd]
    exact h i

end BoundedFormulaIdx

/-! ## The atomic diagram at an abstract carrier

Tuple in BOUND positions, so this is a `BoundedFormulaIdx ι Empty k` — no free variables and
no relabeling anywhere in the Scott construction. -/

section Scott

variable {M : Type w} [L.Structure M] {ι : Type uι}

open Classical in
/-- The atomic diagram of a tuple, as a conjunction along an explicit coding of the atomic
indices. No countability of the language is required — only the given coding. -/
noncomputable def atomicDiagramAt {k : ℕ} (cA : IndexCoding (L.AtomicIdx k) ι)
    (a : Fin k → M) : L.BoundedFormulaIdx ι Empty k :=
  iInfAlong cA fun idx =>
    if idx.holds a then atomicFormulaIdx idx else (atomicFormulaIdx idx).not

theorem realize_atomicDiagramAt {N : Type w'} [L.Structure N] {k : ℕ}
    (cA : IndexCoding (L.AtomicIdx k) ι) (a : Fin k → M) (b : Fin k → N) :
    (atomicDiagramAt cA a).Realize Empty.elim b ↔ SameAtomicType (L := L) a b := by
  simp only [atomicDiagramAt, realize_iInfAlong]
  constructor
  · intro h idx
    have hidx := h idx
    by_cases hA : idx.holds a
    · rw [if_pos hA, realize_atomicFormulaIdx] at hidx
      exact iff_of_true hA hidx
    · rw [if_neg hA, realize_not, realize_atomicFormulaIdx] at hidx
      exact iff_of_false hA hidx
  · intro h idx
    by_cases hA : idx.holds a
    · rw [if_pos hA, realize_atomicFormulaIdx]
      exact (h idx).mp hA
    · rw [if_neg hA, realize_not, realize_atomicFormulaIdx]
      exact fun hb => hA ((h idx).mpr hb)

@[simp] theorem qrank_atomicFormulaIdx {k : ℕ} (idx : L.AtomicIdx k) :
    (atomicFormulaIdx (ι := ι) idx : L.BoundedFormulaIdx ι Empty k).qrank = 0 := by
  cases idx <;> rfl

theorem qrank_atomicDiagramAt_le {k : ℕ} (cA : IndexCoding (L.AtomicIdx k) ι)
    (a : Fin k → M) : (atomicDiagramAt cA a).qrank ≤ 0 := by
  refine qrank_iInfAlong_le _ fun idx => le_of_eq ?_
  split_ifs <;> simp

/-! ## The carrier-general Scott approximant

Parameterized by an abstract carrier and explicit codings — of `M`, of the atomic indices,
and (for limit stages up to `α`) of the initial segments of ordinals. NO countability of `M`,
NO countability of the language, NO `α < ω₁` restriction. -/

variable {α : Ordinal.{uι}}

/-- The Scott approximant of a tuple at ordinal level `β ≤ α`, at an abstract carrier.

At level 0: the atomic diagram. At `β + 1`: the level-`β` formula, the forth condition
(an `M`-conjunction of existentials), and the back condition (a universal over an
`M`-disjunction). At limit `β`: the conjunction over all lower levels, along the given
initial-segment coding. All quantification is on BOUND variables: `existsLast` and `.all`
replace the production's `relabel insertLastBound` machinery outright. -/
noncomputable def scottApproxAt (cM : IndexCoding M ι)
    (cA : ∀ k : ℕ, IndexCoding (L.AtomicIdx k) ι)
    (cOrd : ∀ β : Ordinal.{uι}, β ≤ α → IndexCoding {γ : Ordinal.{uι} // γ < β} ι)
    (β : Ordinal.{uι}) :
    β ≤ α → ∀ k : ℕ, (Fin k → M) → L.BoundedFormulaIdx ι Empty k :=
  Ordinal.limitRecOn
    (motive := fun β => β ≤ α → ∀ k : ℕ, (Fin k → M) → L.BoundedFormulaIdx ι Empty k) β
    (fun _ k a => atomicDiagramAt (cA k) a)
    (fun β ih hβ k a =>
      have hβ' : β ≤ α := le_trans (le_of_lt (Order.lt_succ β)) hβ
      ih hβ' k a ⊓
        iInfAlong cM (fun m : M => existsLast (ih hβ' (k + 1) (Fin.snoc a m))) ⊓
        (iSupAlong cM fun m : M => ih hβ' (k + 1) (Fin.snoc a m)).all)
    (fun β _hlim ih hβ k a =>
      iInfAlong (cOrd β hβ) fun γ : {γ : Ordinal.{uι} // γ < β} =>
        ih γ.1 γ.2 (le_trans (le_of_lt γ.2) hβ) k a)

section Equations

variable (cM : IndexCoding M ι) (cA : ∀ k : ℕ, IndexCoding (L.AtomicIdx k) ι)
  (cOrd : ∀ β : Ordinal.{uι}, β ≤ α → IndexCoding {γ : Ordinal.{uι} // γ < β} ι)

theorem scottApproxAt_zero (h0 : (0 : Ordinal.{uι}) ≤ α) (k : ℕ) (a : Fin k → M) :
    scottApproxAt cM cA cOrd 0 h0 k a = atomicDiagramAt (cA k) a := by
  simp only [scottApproxAt, Ordinal.limitRecOn_zero]

theorem scottApproxAt_succ {β : Ordinal.{uι}} (hβ : β + 1 ≤ α) (k : ℕ)
    (a : Fin k → M) :
    scottApproxAt cM cA cOrd (β + 1) hβ k a =
      scottApproxAt cM cA cOrd β (le_trans (le_of_lt (Order.lt_succ β)) hβ) k a ⊓
        iInfAlong cM (fun m : M => existsLast
          (scottApproxAt cM cA cOrd β (le_trans (le_of_lt (Order.lt_succ β)) hβ) (k + 1)
            (Fin.snoc a m))) ⊓
        (iSupAlong cM fun m : M =>
          scottApproxAt cM cA cOrd β (le_trans (le_of_lt (Order.lt_succ β)) hβ) (k + 1)
            (Fin.snoc a m)).all := by
  simp only [scottApproxAt, Ordinal.limitRecOn_add_one]

theorem scottApproxAt_limit {β : Ordinal.{uι}} (hlim : Order.IsSuccLimit β) (hβ : β ≤ α)
    (k : ℕ) (a : Fin k → M) :
    scottApproxAt cM cA cOrd β hβ k a =
      iInfAlong (cOrd β hβ) (fun γ : {γ : Ordinal.{uι} // γ < β} =>
        scottApproxAt cM cA cOrd γ.1 (le_trans (le_of_lt γ.2) hβ) k a) := by
  simp only [scottApproxAt]
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlim]

end Equations

/-- **The carrier-general Scott characterization**, unconditional in the ordinal: a tuple `b`
realizes the level-`β` Scott approximant of `a` iff `a` and `b` are back-and-forth equivalent
at level `β`. Compare the production `realize_scottFormula_iff_BFEquiv`, which requires
`[Countable M]` and `α < ω₁`. -/
theorem realize_scottApproxAt_iff_BFEquiv {N : Type w'} [L.Structure N]
    (cM : IndexCoding M ι) (cA : ∀ k : ℕ, IndexCoding (L.AtomicIdx k) ι)
    (cOrd : ∀ β : Ordinal.{uι}, β ≤ α → IndexCoding {γ : Ordinal.{uι} // γ < β} ι)
    (β : Ordinal.{uι}) :
    ∀ (hβ : β ≤ α) {k : ℕ} (a : Fin k → M) (b : Fin k → N),
      (scottApproxAt cM cA cOrd β hβ k a).Realize Empty.elim b ↔
        BFEquiv (L := L) β k a b := by
  induction β using Ordinal.limitRecOn with
  | zero =>
    intro hβ k a b
    rw [scottApproxAt_zero, BFEquiv.zero]
    exact realize_atomicDiagramAt (cA k) a b
  | add_one β ih =>
    intro hβ k a b
    have hsucc := BFEquiv.succ (L := L) (M := M) (N := N) (n := k) β a b
    rw [Order.succ_eq_add_one] at hsucc
    rw [scottApproxAt_succ, hsucc]
    simp only [realize_inf]
    constructor
    · rintro ⟨⟨hbase, hforth⟩, hback⟩
      rw [realize_iInfAlong] at hforth
      rw [realize_all] at hback
      refine ⟨(ih _ a b).mp hbase, fun m => ?_, fun n' => ?_⟩
      · have hm := hforth m
        rw [realize_existsLast] at hm
        obtain ⟨n', hn'⟩ := hm
        exact ⟨n', (ih _ (Fin.snoc a m) (Fin.snoc b n')).mp hn'⟩
      · have hn := hback n'
        rw [realize_iSupAlong] at hn
        obtain ⟨m, hm⟩ := hn
        exact ⟨m, (ih _ (Fin.snoc a m) (Fin.snoc b n')).mp hm⟩
    · rintro ⟨hbase, hforth, hback⟩
      refine ⟨⟨(ih _ a b).mpr hbase, ?_⟩, ?_⟩
      · rw [realize_iInfAlong]
        intro m
        rw [realize_existsLast]
        obtain ⟨n', hn'⟩ := hforth m
        exact ⟨n', (ih _ (Fin.snoc a m) (Fin.snoc b n')).mpr hn'⟩
      · rw [realize_all]
        intro n'
        rw [realize_iSupAlong]
        obtain ⟨m, hm⟩ := hback n'
        exact ⟨m, (ih _ (Fin.snoc a m) (Fin.snoc b n')).mpr hm⟩
  | limit β hlim ih =>
    intro hβ k a b
    rw [scottApproxAt_limit cM cA cOrd hlim, BFEquiv.limit β hlim, realize_iInfAlong]
    exact ⟨fun h γ hγ => (ih γ hγ _ a b).mp (h ⟨γ, hγ⟩),
           fun h γ => (ih γ.1 γ.2 _ a b).mpr (h γ.1 γ.2)⟩

/-- **Rank bound, carrier-general**: the level-`β` Scott approximant has quantifier rank at
most `β` — at every carrier, with no countability anywhere. -/
theorem scottApproxAt_qrank_le (cM : IndexCoding M ι)
    (cA : ∀ k : ℕ, IndexCoding (L.AtomicIdx k) ι)
    (cOrd : ∀ β : Ordinal.{uι}, β ≤ α → IndexCoding {γ : Ordinal.{uι} // γ < β} ι)
    (β : Ordinal.{uι}) :
    ∀ (hβ : β ≤ α) (k : ℕ) (a : Fin k → M),
      (scottApproxAt cM cA cOrd β hβ k a).qrank ≤ β := by
  induction β using Ordinal.limitRecOn with
  | zero =>
    intro hβ k a
    rw [scottApproxAt_zero]
    exact qrank_atomicDiagramAt_le (cA k) a
  | add_one β ih =>
    intro hβ k a
    have hsucc_le : Order.succ β ≤ β + 1 := le_of_eq (Order.succ_eq_add_one β)
    have hlt : β < β + 1 := lt_of_lt_of_le (Order.lt_succ β) hsucc_le
    rw [scottApproxAt_succ]
    simp only [qrank_inf, qrank_all]
    refine max_le (max_le ?_ ?_) ?_
    · exact le_trans (ih _ k a) (le_of_lt hlt)
    · refine qrank_iInfAlong_le _ fun m => ?_
      rw [qrank_existsLast]
      exact le_trans (Order.succ_le_succ (ih _ (k + 1) (Fin.snoc a m))) hsucc_le
    · exact le_trans
        (Order.succ_le_succ (qrank_iSupAlong_le _ fun m => ih _ (k + 1) (Fin.snoc a m)))
        hsucc_le
  | limit β hlim ih =>
    intro hβ k a
    rw [scottApproxAt_limit cM cA cOrd hlim]
    exact qrank_iInfAlong_le _ fun γ => le_trans (ih γ.1 γ.2 _ k a) (le_of_lt γ.2)

/-! ## The countable specialization: recovering the production `scottFormula`

Carrier `ℕ`, every coding explicit via `ofEncodableWith`. The characterization and the rank
bound are instantiations of the general theorems; semantic equivalence to the production
`scottFormula` is free from the two characterizations. -/

/-- Initial segments of ordinals below `ω₁` are countable (ported from the production
`scottFormula` limit-stage derivation). -/
theorem countable_Iio_of_lt_omega1 {β : Ordinal.{uι}} (hβ : β < Ordinal.omega 1) :
    Countable {γ : Ordinal.{uι} // γ < β} := by
  haveI : Countable β.ToType := by
    rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType]
    have h_card : β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp hβ
    have h1 : Cardinal.aleph 1 = Order.succ (Cardinal.aleph 0) := by
      rw [Cardinal.succ_aleph, zero_add]
    rw [h1, Cardinal.aleph_zero] at h_card
    exact Order.lt_succ_iff.mp h_card
  exact Countable.of_equiv β.ToType (Ordinal.ToType.mk).symm.toEquiv

variable [Countable (Σ l, L.Relations l)]

/-- The countable Scott formula on the new syntax: the `ι := ℕ` instance of `scottApproxAt`,
with every encoding explicit at the construction boundary. This is the port of the production
`scottFormula` (item 5); `einf`/`esup` have become `iInfAlong`/`iSupAlong`. -/
noncomputable def scottFormulaB [Countable M] {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    {k : ℕ} (a : Fin k → M) : L.BoundedFormulaOmega Empty k :=
  scottApproxAt (ι := ℕ)
    (IndexCoding.ofEncodableWith (Encodable.ofCountable M))
    (fun k => IndexCoding.ofEncodableWith (Encodable.ofCountable (L.AtomicIdx k)))
    (fun β hβ =>
      haveI : Countable {γ : Ordinal.{0} // γ < β} :=
        countable_Iio_of_lt_omega1 (lt_of_le_of_lt hβ hα)
      IndexCoding.ofEncodableWith
        (Encodable.ofCountable {γ : Ordinal.{0} // γ < β}))
    α le_rfl k a

/-- Port of `realize_scottFormula_iff_BFEquiv` — an instantiation of the general theorem. -/
theorem realize_scottFormulaB_iff_BFEquiv [Countable M] {N : Type w'} [L.Structure N]
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) {k : ℕ} (a : Fin k → M) (b : Fin k → N) :
    (scottFormulaB (L := L) hα a).Realize Empty.elim b ↔ BFEquiv (L := L) α k a b :=
  realize_scottApproxAt_iff_BFEquiv _ _ _ α le_rfl a b

/-- Port of `scottFormula_qrank_le` — an instantiation of the general theorem. -/
theorem scottFormulaB_qrank_le [Countable M] {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    {k : ℕ} (a : Fin k → M) : (scottFormulaB (L := L) hα a).qrank ≤ α :=
  scottApproxAt_qrank_le _ _ _ α le_rfl k a

/-- **Semantic equivalence with the production `scottFormula`** — free from the two
characterizations, with no syntactic comparison (the encodings differ, so semantic
equivalence is the correct endpoint). -/
theorem realize_scottFormulaB_iff_scottFormula [L.IsRelational] [Countable M] {N : Type w'}
    [L.Structure N] {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) {k : ℕ} (a : Fin k → M)
    (b : Fin k → N) :
    (scottFormulaB (L := L) hα a).Realize Empty.elim b ↔ (scottFormula (L := L) a α).Realize b :=
  (realize_scottFormulaB_iff_BFEquiv hα a b).trans
    (realize_scottFormula_iff_BFEquiv a b α hα).symm

end Scott

/-! ## The canonical carrier packaging: `M ⊕ (α.ToType ⊕ Σ k, L.AtomicIdx k)`

Only after the abstract version: one concrete carrier receiving all three coding families.
The ordinal stages code through `Ordinal.ToType.mk`, staying at the small `α.ToType` rather
than the universe-bumped subtype of ordinals. -/

section CanonicalCarrier

namespace IndexCoding

/-- The inclusion coding of a smaller initial segment of ordinals into a larger one. -/
noncomputable def subtypeIioLe {α β : Ordinal.{uι}} (h : β ≤ α) :
    IndexCoding {γ : Ordinal.{uι} // γ < β} {γ : Ordinal.{uι} // γ < α} where
  encode γ := ⟨γ.1, lt_of_lt_of_le γ.2 h⟩
  decode δ := if hd : δ.1 < β then some ⟨δ.1, hd⟩ else none
  decode_encode γ := by simp [γ.2]

end IndexCoding

variable {M : Type w} [L.Structure M]

/-- The canonical Scott carrier for a structure `M` and an ordinal bound `α`. The ordinal
universe matches the carrier universe `max u v w`; the ordinal stages enter through the
small `α.ToType`, not the universe-bumped subtype of ordinals. -/
abbrev ScottCarrier (L : Language.{u, v}) (M : Type w) (α : Ordinal.{max u v w}) :
    Type (max u v w) :=
  M ⊕ (α.ToType ⊕ Σ k : ℕ, L.AtomicIdx k)

/-- The Scott approximant at the canonical carrier: `scottApproxAt` with the three canonical
codings. Defined for arbitrary `M` — no countability anywhere. -/
noncomputable def scottApprox (α β : Ordinal.{max u v w}) (hβ : β ≤ α) {k : ℕ}
    (a : Fin k → M) : L.BoundedFormulaIdx (ScottCarrier L M α) Empty k :=
  scottApproxAt
    (IndexCoding.sumInl M _)
    (fun k => ((IndexCoding.sigmaIn (fun k : ℕ => L.AtomicIdx k) k).trans
      (IndexCoding.sumInr α.ToType _)).trans (IndexCoding.sumInr M _))
    (fun _β hβ => (((IndexCoding.subtypeIioLe hβ).trans
      (IndexCoding.ofEquiv (Ordinal.ToType.mk).toEquiv)).trans
        (IndexCoding.sumInl α.ToType _)).trans (IndexCoding.sumInr M _))
    β hβ k a

/-- The canonical-carrier characterization, unconditional in the ordinal. -/
theorem realize_scottApprox_iff_BFEquiv {N : Type w'} [L.Structure N]
    (α β : Ordinal.{max u v w}) (hβ : β ≤ α) {k : ℕ} (a : Fin k → M) (b : Fin k → N) :
    (scottApprox (L := L) α β hβ a).Realize Empty.elim b ↔ BFEquiv (L := L) β k a b :=
  realize_scottApproxAt_iff_BFEquiv _ _ _ β hβ a b

/-- The canonical-carrier rank bound. -/
theorem scottApprox_qrank_le (α β : Ordinal.{max u v w}) (hβ : β ≤ α) {k : ℕ}
    (a : Fin k → M) : (scottApprox (L := L) α β hβ a).qrank ≤ β :=
  scottApproxAt_qrank_le _ _ _ β hβ k a

end CanonicalCarrier

end FirstOrder.Language
