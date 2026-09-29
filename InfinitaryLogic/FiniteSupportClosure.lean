/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Closure
import Mathlib.Data.Finset.Union

/-!
# From finite hulls to a finitary closure operator

A closure operator `c` on the finite subsets of a type extends to a closure operator on all
subsets by finite character: a point is in the closure of `A` iff it lies in `c S` for some finite
`S ⊆ A` (`setClosure c`).  The extension agrees with `c` on finite inputs (`setClosure_finset`),
is the unique finite-character operator doing so (`setClosure_unique`), and a set is closed iff
it contains the hull of each of its finite subsets (`setClosure_closed_iff`).  Anti-exchange
transfers from `c` to the extension (`setClosure_antiExchange`).

No model theory is involved.  This module and `TwoGeneratorCardinality` are generic supporting
material whose natural eventual home is Mathlib.
-/

set_option autoImplicit false

namespace InfinitaryLogic.FiniteSupportClosure

variable {M : Type*}

/-- Finite-character extension: a point is forced by a finite subset of the input. -/
def extension (c : ClosureOperator (Finset M)) (A : Set M) : Set M :=
  {x | ∃ S : Finset M, (↑S : Set M) ⊆ A ∧ x ∈ c S}

/-- Monotonicity passes from finite hulls to arbitrary inputs. -/
theorem extension_mono (c : ClosureOperator (Finset M)) : Monotone (extension c) := by
  intro A B h x hx
  obtain ⟨S, hS, hx⟩ := hx
  exact ⟨S, hS.trans h, hx⟩

/-- Singleton witnesses make the extension extensive. -/
theorem subset_extension (c : ClosureOperator (Finset M)) (A : Set M) : A ⊆ extension c A := by
  intro x hx
  refine ⟨{x}, ?_, c.le_closure _ (Finset.mem_singleton_self x)⟩
  simpa using hx

/-- The extension agrees literally with the given operator on every finite input. -/
theorem extension_finset (c : ClosureOperator (Finset M)) (S : Finset M) :
    extension c (↑S : Set M) = (↑(c S) : Set M) := by
  ext x
  constructor
  · rintro ⟨T, hT, hx⟩
    exact c.monotone hT hx
  · intro hx
    exact ⟨S, Set.Subset.rfl, hx⟩

/-- Finitely many forced points have one common finite set of witnesses. -/
theorem finite_support (c : ClosureOperator (Finset M)) {A : Set M} (S : Finset M)
    (hS : (↑S : Set M) ⊆ extension c A) :
    ∃ T : Finset M, (↑T : Set M) ⊆ A ∧ S ⊆ c T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, Finset.empty_subset _⟩
  | @insert x S hx ih =>
    obtain ⟨U, hU, hxU⟩ := hS (Finset.mem_insert_self x S)
    obtain ⟨T, hT, hST⟩ := ih (fun y hy => hS (Finset.mem_insert_of_mem hy))
    refine ⟨U ∪ T, ?_, Finset.insert_subset ?_ ?_⟩
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hU hy
      · exact hT hy
    · exact c.monotone Finset.subset_union_left hxU
    · exact hST.trans (c.monotone Finset.subset_union_right)

/-- Finite witnesses can be flattened, so closing twice adds nothing. -/
theorem extension_idem_le (c : ClosureOperator (Finset M)) (A : Set M) :
    extension c (extension c A) ⊆ extension c A := by
  rintro x ⟨S, hS, hx⟩
  obtain ⟨T, hT, hST⟩ := finite_support c S hS
  refine ⟨T, hT, ?_⟩
  have := c.monotone hST hx
  simpa only [c.idempotent] using this

/-- The canonical finite-character closure operator on arbitrary subsets. -/
def setClosure (c : ClosureOperator (Finset M)) : ClosureOperator (Set M) :=
  ClosureOperator.mk' (extension c) (extension_mono c) (subset_extension c)
    (extension_idem_le c)

/-- The set closure retains the original finite hull. -/
theorem setClosure_finset (c : ClosureOperator (Finset M)) (S : Finset M) :
    setClosure c (↑S : Set M) = (↑(c S) : Set M) := extension_finset c S

/-- Membership has a finite witness from the input. -/
theorem mem_setClosure_iff (c : ClosureOperator (Finset M)) {A : Set M} {x : M} :
    x ∈ setClosure c A ↔ ∃ S : Finset M, (↑S : Set M) ⊆ A ∧ x ∈ c S := Iff.rfl

/-- An empty-preserving finite hull has an empty-preserving set extension. -/
theorem setClosure_empty (c : ClosureOperator (Finset M)) (h0 : c ∅ = ∅) :
    setClosure c ∅ = ∅ := by
  simpa only [Finset.coe_empty, h0] using setClosure_finset c ∅

/-- A set is closed precisely when it contains the hull of each finite subset. -/
theorem setClosure_closed_iff (c : ClosureOperator (Finset M)) (A : Set M) :
    (setClosure c).IsClosed A ↔
      ∀ S : Finset M, (↑S : Set M) ⊆ A → (↑(c S) : Set M) ⊆ A := by
  rw [ClosureOperator.isClosed_iff_closure_le]
  constructor
  · intro h S hS x hx
    exact h ⟨S, hS, hx⟩
  · rintro h x ⟨S, hS, hx⟩
    exact h S hS hx

/-- Finite character and agreement on finite inputs uniquely determine the extension. -/
theorem setClosure_unique (c : ClosureOperator (Finset M))
    (d : ClosureOperator (Set M))
    (hd : ∀ (A : Set M) (x : M), x ∈ d A ↔
      ∃ S : Finset M, (↑S : Set M) ⊆ A ∧ x ∈ d (↑S : Set M))
    (hfinite : ∀ S : Finset M, d (↑S : Set M) = (↑(c S) : Set M)) :
    d = setClosure c := by
  apply DFunLike.ext
  intro A
  ext x
  rw [hd]
  simp only [hfinite, mem_setClosure_iff, Finset.mem_coe]

/-- Anti-exchange globalizes by combining the two finite witnesses inside a closed set. -/
theorem setClosure_antiExchange [DecidableEq M] (c : ClosureOperator (Finset M))
    (ha : ∀ (S : Finset M) (x y : M), x ≠ y → x ∉ c S →
      x ∈ c (insert y S) → y ∉ c (insert x S))
    {A : Set M} (hA : setClosure c A = A) {x y : M}
    (hxy : x ≠ y) (hxA : x ∉ A) (hx : x ∈ setClosure c (insert y A)) :
    y ∉ setClosure c (insert x A) := by
  classical
  rintro ⟨T, hT, hyT⟩
  obtain ⟨S, hS, hxS⟩ := hx
  let B := S.erase y ∪ T.erase x
  have hBA : (↑B : Set M) ⊆ A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨hzy, hzS⟩ := Finset.mem_erase.mp hz
      exact (hS hzS).resolve_left hzy
    · obtain ⟨hzx, hzT⟩ := Finset.mem_erase.mp hz
      exact (hT hzT).resolve_left hzx
  have hcBA : (↑(c B) : Set M) ⊆ A := by
    rw [← hA, ← setClosure_finset]
    exact (setClosure c).monotone hBA
  have hSB : S ⊆ insert y B := by
    intro z hz
    by_cases hzy : z = y
    · simp [hzy]
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzy, hz⟩))
  have hTB : T ⊆ insert x B := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzx, hz⟩))
  exact ha B x y hxy (fun hxB => hxA (hcBA hxB))
    (c.monotone hSB hxS) (c.monotone hTB hyT)

end InfinitaryLogic.FiniteSupportClosure
