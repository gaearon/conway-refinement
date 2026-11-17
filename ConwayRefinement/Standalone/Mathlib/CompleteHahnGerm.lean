/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Germs of Hahn series over a Cauchy-complete exponent group

Let `G` be a nontrivial ordered abelian group, `K` a field, and `K((G^{≤ 0}))` the ring of Hahn
series supported in the nonpositive cone of `G`. Let `J` be the ideal of series whose support is
bounded away from zero, so that two series have the same image in `K((G^{≤ 0}))/J` exactly when
they agree on some interval immediately below zero. If `K` has characteristic zero and `G`, with
its order topology and the associated group uniformity, is Cauchy complete, then this ring of
germs is a polynomial algebra over `K`. Consequently `J` is a prime ideal, and the ring of germs
has four-factor refinement. For `G = ℝ` the primality of `J` is Berarducci's theorem
(Berarducci 2000, Cor. 9.8).
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.CompleteHahnGerm

universe u v

variable (G : Type u) (K : Type v)
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Nontrivial G] [Field K]

/-- The Hahn-series `K`-algebra `K((G^{≤ 0}))`. -/
def NonpositiveSeries : Subalgebra K (HahnSeries G K) where
  carrier := {x | x.support ⊆ Set.Iic 0}
  algebraMap_mem' k := by
    intro g hg
    rw [HahnSeries.algebraMap_apply] at hg
    have hg0 : g = 0 := HahnSeries.support_single_subset hg
    simp [hg0]
  add_mem' := fun hx hy ↦
    (HahnSeries.support_add_subset _ _).trans (Set.union_subset hx hy)
  mul_mem' := fun hx hy ↦ HahnSeries.support_mul_subset.trans fun _ ⟨i, hi, j, hj, h⟩ ↦
    h ▸ show i + j ≤ 0 from add_nonpos (hx hi) (hy hj)

/-- The ideal of series whose support is bounded away from zero. -/
def BoundedAwayIdeal : Ideal (NonpositiveSeries G K) where
  carrier := {x | ∃ r < (0 : G), (x : HahnSeries G K).support ⊆ Set.Iic r}
  zero_mem' := by
    obtain ⟨r, hr⟩ := exists_lt (0 : G)
    exact ⟨r, hr, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr, hxr⟩ ⟨s, hs, hys⟩
    refine ⟨max r s, max_lt hr hs, ?_⟩
    intro q hq
    rcases HahnSeries.support_add_subset (x : HahnSeries G K) y hq with hqx | hqy
    · exact (hxr hqx).trans (le_max_left r s)
    · exact (hys hqy).trans (le_max_right r s)
  smul_mem' := by
    rintro x y ⟨r, hr, hyr⟩
    refine ⟨r, hr, HahnSeries.support_mul_subset.trans ?_⟩
    rintro _ ⟨i, hi, j, hj, rfl⟩
    simpa only [Set.mem_Iic, zero_add] using add_le_add (x.2 hi) (hyr hj)

/-- The germ ring `K((G^{≤ 0}))` modulo series supported away from zero. -/
abbrev Germ := NonpositiveSeries G K ⧸ BoundedAwayIdeal G K

/-- The germ ring is isomorphic to a polynomial algebra over `K`. -/
abbrev IsPolynomialRing : Prop :=
  ∀ [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [CompleteSpace G] [CharZero K],
    ∃ ι : Type (max (u + 1) v), Nonempty (MvPolynomial ι K ≃ₐ[K] Germ G K)

/-- The ideal of series whose support is bounded away from zero is prime. -/
abbrev BoundedAwayIdealIsPrime : Prop :=
  ∀ [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [CompleteSpace G] [CharZero K],
    (BoundedAwayIdeal G K).IsPrime

/-- Every equation of four germs admits a four-factor refinement. -/
abbrev HasRefinement : Prop :=
  ∀ [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [CompleteSpace G] [CharZero K],
      ∀ a b c d : Germ G K, a * b = c * d →
        ∃ e f g h : Germ G K,
          a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

end ConwayRefinement.Standalone.CompleteHahnGerm

/-!
## Formal proof

Proof module: `CompleteHahnGermProof`.

* `IsPolynomialRing` → `IsPolynomialRing.proof`
* `BoundedAwayIdealIsPrime` → `BoundedAwayIdealIsPrime.proof`
* `HasRefinement` → `HasRefinement.proof`
-/
