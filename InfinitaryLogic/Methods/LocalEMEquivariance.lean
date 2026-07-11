/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMContext

/-!
# Equivariance of the local EM quotient (the issue #11 spike)

An order automorphism `e : J ≃o J` acts on `Λ[[J]]`-terms by renaming skeleton constants
(`locJRename`, via Mathlib's `lhomWithConstantsMap`). The spike question for the
countably-many-types project: does the DEFINING semantic equivalence `LocalEMEq` of the local
EM quotient commute with this action? The three test lemmas, in the order of risk:

* `locJSupport_locJRename` — the finite skeleton support maps by `Finset.image e`;
* `deepRank_image_orderIso` — the support's internal rank enumeration is invariant: an order
  automorphism preserves each element's rank in a finite support;
* `locDeepInterp_locJRename` — the deep interpretation of the renamed term over the renamed
  support EQUALS (not merely relates to) that of the original — pointwise in the depth `d`.

Consequently `LocalEMEq_locJRename_iff`: the setoid is preserved AND reflected by renaming —
the two `∀ᶠ` propositions are pointwise equal, so the critical gate of the spike holds with no
reconstruction of semantic truth outside the quotient's defining fragment. The verdict is that
the existing quotient (`LocalEMContext.Carrier`) is the correct vehicle for the induced
automorphisms; the descended carrier equivalence, the equivariant structure isomorphism
(`F(c_j) = c_{e j}`), and the base-reduct automorphism are the follow-on packaging.
-/

namespace FirstOrder

namespace Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- The skeleton-constant renaming action of an order automorphism on closed `Λ[[J]]`-terms. -/
def locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) : Λ[[J]].Term α :=
  (Λ.lhomWithConstantsMap (e : J → J)).onTerm t

/-- Renaming carries each function symbol's skeleton constant by `Finset.image e`. -/
theorem locJConstOf_lhomWithConstantsMap (e : J ≃o J) {n : ℕ} (f : Λ[[J]].Functions n) :
    locJConstOf Λ J ((Λ.lhomWithConstantsMap (e : J → J)).onFunction f)
      = (locJConstOf Λ J f).image e := by
  rcases n with _ | n
  · rcases f with f' | j
    · rfl
    · simp only [locJConstOf]
      rfl
  · rcases f with f' | c
    · rfl
    · exact c.elim

/-- **Test lemma 1**: the skeleton support of the renamed term is the image of the support. -/
theorem locJSupport_locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    locJSupport Λ J (locJRename Λ J e t) = (locJSupport Λ J t).image e := by
  induction t with
  | var x => simp [locJRename, LHom.onTerm, locJSupport]
  | @func l f ts ih =>
    show locJSupport Λ J (Term.func ((Λ.lhomWithConstantsMap (e : J → J)).onFunction f)
      fun i => locJRename Λ J e (ts i)) = _
    rw [locJSupport, locJSupport, Finset.image_union, locJConstOf_lhomWithConstantsMap]
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      rw [ih i] at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨y, ⟨i, hy⟩, rfl⟩
    · rintro ⟨y, ⟨i, hy⟩, rfl⟩
      exact ⟨i, by rw [ih i]; exact Finset.mem_image_of_mem _ hy⟩

/-- **Test lemma 2**: an order automorphism preserves the internal rank enumeration of a finite
support: the rank of `e j` in `S.image e` is the rank of `j` in `S`. -/
theorem deepRank_image_orderIso (e : J ≃o J) (S : Finset J) (j : J) :
    deepRank J (S.image e) (e j) = deepRank J S j := by
  unfold deepRank
  rw [Finset.filter_image]
  have hpred : (S.filter fun x => (e x : J) < e j) = S.filter (· < j) :=
    Finset.filter_congr fun x _ => e.lt_iff_lt
  rw [hpred]
  exact Finset.card_image_of_injective _ e.injective

/-- De-substitution intertwines skeleton renaming with variable relabeling: the
`constantsToVars` of the renamed term is the relabel of the original's along `Sum.map e id`. -/
theorem constantsToVars_locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    (locJRename Λ J e t).constantsToVars
      = t.constantsToVars.relabel (Sum.map e id) := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | j
      · show Term.func f' (fun i => (locJRename Λ J e (ts i)).constantsToVars)
          = Term.relabel _ (Term.func f' fun i => (ts i).constantsToVars)
        rw [Term.relabel]
        congr 1
        exact funext fun i => ih i
      · rfl
    · rcases f with f' | c
      · show Term.func f' (fun i => (locJRename Λ J e (ts i)).constantsToVars)
          = Term.relabel _ (Term.func f' fun i => (ts i).constantsToVars)
        rw [Term.relabel]
        congr 1
        exact funext fun i => ih i
      · exact c.elim

/-- **Test lemma 3**: the deep interpretation of the renamed term over the image support equals
that of the original term over the original support — pointwise in the depth `d`, not merely
eventually. -/
theorem locDeepInterp_locJRename {M : Type} [Λ.Structure M] (a : ℕ → M) (e : J ≃o J)
    (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d (S.image e) (locJRename Λ J e t) = locDeepInterp Λ J a d S t := by
  rw [locDeepInterp_eq_realize, locDeepInterp_eq_realize, constantsToVars_locJRename,
    Term.realize_relabel]
  congr 1
  funext x
  rcases x with j | ee
  · show a (d + deepRank J (S.image e) (e j)) = a (d + deepRank J S j)
    rw [deepRank_image_orderIso]
  · exact ee.elim

/-- **The critical gate**: the defining semantic equivalence of the local EM quotient is
preserved AND reflected by skeleton renaming — the two eventual equalities are pointwise
equivalent propositions. The existing quotient is equivariant. -/
theorem LocalEMEq_locJRename_iff {M : Type} [Λ.Structure M] (a : ℕ → M) (e : J ≃o J)
    (t u : Λ[[J]].Term Empty) :
    LocalEMEq Λ J a (locJRename Λ J e t) (locJRename Λ J e u) ↔ LocalEMEq Λ J a t u := by
  unfold LocalEMEq
  rw [locJSupport_locJRename, locJSupport_locJRename, ← Finset.image_union]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun d => by
    rw [locDeepInterp_locJRename, locDeepInterp_locJRename])

/-- The setoid form of the gate, for a full local EM context: renamed representatives are
related exactly when the originals are. -/
theorem LocalEMContext.setoid_locJRename_iff {M : Type} [Λ.Structure M]
    (ctx : LocalEMContext Λ J (M := M)) (e : J ≃o J) (t u : Λ[[J]].Term Empty) :
    ctx.setoid.r (locJRename Λ J e t) (locJRename Λ J e u) ↔ ctx.setoid.r t u :=
  LocalEMEq_locJRename_iff Λ J ctx.a e t u

end Language

end FirstOrder
