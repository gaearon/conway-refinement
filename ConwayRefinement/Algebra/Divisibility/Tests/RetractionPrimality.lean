/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Algebra.Divisibility.RetractionPrimality
public import ConwayRefinement.Algebra.Divisibility.PrimalPreimage

import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Tests for primality from retractions and in a `D + M` construction

With the identity retraction and the zero ideal, primality from germs and restrictions reduces to
refinement in the ring itself; the integers give a nondegenerate client. A second client forwards
the hypotheses of primality in a `D + M` construction.
-/

public section

namespace Tests

/-- Every nonzero integer is primal, via the retraction criterion with the identity retraction,
the zero ideal and the cofactor `1`. -/
theorem int_isPrimal_of_retractions {f : ℤ} (hf : f ≠ 0) : IsPrimal f := by
  refine isPrimal_of_frequently_retraction_mul_isPrimal (ι := Unit) ⊥ ⊤
    (fun _ ↦ RingHom.id ℤ) (fun _ _ ↦ rfl) (fun j hj ↦ ?_) (fun _ _ _ _ _ h ↦ h) ?_ ?_
  · rw [Ideal.mem_bot] at hj
    simp [hj]
  · intro g x y hg
    obtain ⟨a, b, ⟨q₁, rfl⟩, ⟨q₂, rfl⟩, rfl⟩ := DecompositionMonoid.primal g hg
    exact ⟨a, b, q₁, q₂, by simp, by simp, by simp⟩
  · rw [Filter.frequently_top]
    exact ⟨(), hf, 1, by simp, isUnit_one.isPrimal⟩

/-- A client of primality in a `D + M` construction with nonzero residue. -/
theorem isPrimal_residueSubring_of_residue_ne_zero
    {L A : Type*} [Field L] [CommRing A] [Algebra L A] [IsDomain A]
    {π : A →ₐ[L] L} {S : Subring L} {b : A} (hb : π b ∈ S) (hb0 : π b ≠ 0)
    (hA : IsPrimal b) (hS : IsPrimal (⟨π b, hb⟩ : S)) :
    IsPrimal (⟨b, hb⟩ : Subring.residueSubring π S) :=
  Subring.isPrimal_residueSubring_of_isPrimal_of_residue hb hA (fun _ ↦ hS)
    (fun h ↦ absurd h hb0)

end Tests
