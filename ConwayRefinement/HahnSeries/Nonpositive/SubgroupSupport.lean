/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Truncation
public import ConwayRefinement.HahnSeries.Nonpositive.Basic

import ConwayRefinement.Blueprint
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Rat.Floor

/-!
# Nonpositive series supported in a subgroup of the exponents

Splitting a series into its part supported in a subgroup `H` of the exponents and the rest is
compatible with multiplication by series supported in `H`. If `H` is convex, both factors of a
nonzero product of nonpositive series supported in `H` are supported in `H`.
-/

/-!
## Series supported in a subgroup of the exponents

Splitting a series into the part supported in a subgroup `H` and the rest is compatible with
multiplication by a series supported in `H`, because `H` and its complement are separated by
translation: adding an element of `H` cannot move an exponent into `H` from outside it.

The consequence recorded here is that divisibility descends: if a series supported in `H` divides
another one in the whole ring, the quotient is again supported in `H`. This is the reason a
finitely generated subgroup of the exponents may be fixed once and for all when computing
divisors, and it replaces the free-module argument of Gilmer and Parker, Proposition 5.1 for the
purpose of comparing divisibility.
-/

section

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
open Classical in
/-- Restricting to the exponents satisfying a predicate and to those failing it splits a
series. -/
theorem filter_add_filter_not (p : G → Prop) (x : K⟦G⟧) :
    filter p x + filter (fun g ↦ ¬ p g) x = x := by
  ext g
  rw [HahnSeries.coeff_add, HahnSeries.coeff_filter, HahnSeries.coeff_filter]
  by_cases hg : p g <;> simp [hg]

/-- A product of a series supported in `H` with one supported outside `H` is supported outside
`H`. -/
private theorem support_mul_subset_compl {H : AddSubgroup G} {e y : K⟦G⟧}
    (he : e.support ⊆ (H : Set G)) (hy : ∀ g ∈ y.support, g ∉ H) :
    ∀ g ∈ (e * y).support, g ∉ H := by
  intro g hg
  obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hg
  intro hmem
  exact hy j hj (by simpa using H.sub_mem hmem (he hi))

/-- Divisibility descends to a subgroup of the exponents: a quotient of two series supported in
`H` is again supported in `H`. -/
theorem support_subset_of_mul_eq {H : AddSubgroup G} {e u f : K⟦G⟧}
    (he : e.support ⊆ (H : Set G)) (he0 : e ≠ 0)
    (hf : f.support ⊆ (H : Set G)) (hmul : f = e * u) :
    u.support ⊆ (H : Set G) := by
  classical
  set u₀ := filter (fun g ↦ g ∈ H) u with hu₀
  set u₁ := filter (fun g ↦ g ∉ H) u with hu₁
  have hsplit : u₀ + u₁ = u := filter_add_filter_not _ u
  have h₀ : u₀.support ⊆ (H : Set G) := by
    rw [hu₀, HahnSeries.support_filter]
    exact fun g hg ↦ hg.2
  have h₁ : ∀ g ∈ u₁.support, g ∉ H := by
    rw [hu₁]
    intro g hg
    rw [HahnSeries.support_filter] at hg
    exact hg.2
  have hprod₀ : (e * u₀).support ⊆ (H : Set G) := by
    intro g hg
    obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hg
    exact H.add_mem (he hi) (h₀ hj)
  have hprod₁ := support_mul_subset_compl he h₁
  have hzero : e * u₁ = 0 := by
    ext g
    by_cases hg : g ∈ H
    · by_contra hne
      exact hprod₁ g ((HahnSeries.mem_support _ _).mpr hne) hg
    · have hfg : f.coeff g = 0 := by
        by_contra hne
        exact hg (hf ((HahnSeries.mem_support _ _).mpr hne))
      have h₀g : (e * u₀).coeff g = 0 := by
        by_contra hne
        exact hg (hprod₀ ((HahnSeries.mem_support _ _).mpr hne))
      have hexp : f = e * u₀ + e * u₁ := by rw [hmul, ← mul_add, hsplit]
      have := congrArg (fun s : K⟦G⟧ ↦ s.coeff g) hexp
      simp only [HahnSeries.coeff_add, hfg, h₀g, zero_add] at this
      simpa using this.symm
  have hu₁zero : u₁ = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h he0
    · exact h
  intro g hg
  rw [← hsplit, hu₁zero, add_zero] at hg
  exact h₀ hg

open Classical in
/-- Multiplying by a series supported in `H` commutes with restricting to the exponents satisfying
a predicate that is invariant under translation by `H`. -/
theorem filter_mul_of_invariant {H : AddSubgroup G} {f u : K⟦G⟧}
    (hf : f.support ⊆ (H : Set G))
    (p : G → Prop)
    (hp : ∀ i ∈ H, ∀ j : G, p (i + j) ↔ p j) :
    filter p (f * u) = f * filter p u := by
  ext c
  rw [HahnSeries.coeff_filter, HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  have hsub : Finset.addAntidiagonal f.isPWO_support (filter p u).isPWO_support c
      ⊆ Finset.addAntidiagonal f.isPWO_support u.isPWO_support c := by
    intro b hb
    rw [Finset.mem_addAntidiagonal] at hb ⊢
    exact ⟨hb.1, HahnSeries.support_filter_subset _ u hb.2.1, hb.2.2⟩
  have hrestrict : ∀ b ∈ Finset.addAntidiagonal f.isPWO_support (filter p u).isPWO_support c,
      f.coeff b.1 * (filter p u).coeff b.2 = f.coeff b.1 * u.coeff b.2 := by
    intro b hb
    rw [Finset.mem_addAntidiagonal] at hb
    rw [HahnSeries.support_filter] at hb
    rw [HahnSeries.coeff_filter, if_pos hb.2.1.2]
  by_cases hc : p c
  · rw [if_pos hc]
    refine Finset.sum_congr ?_ (fun b hb ↦ (hrestrict b hb).symm)
    refine Finset.Subset.antisymm (fun b hb ↦ ?_) hsub
    rw [Finset.mem_addAntidiagonal] at hb ⊢
    obtain ⟨hb1, hb2, hb0⟩ := hb
    refine ⟨hb1, ?_, hb0⟩
    rw [HahnSeries.support_filter]
    refine ⟨hb2, ?_⟩
    exact (hp b.1 (hf hb1) b.2).mp (by rw [hb0]; exact hc)
  · rw [if_neg hc]
    refine (Finset.sum_eq_zero fun b hb ↦ ?_).symm
    rw [Finset.mem_addAntidiagonal] at hb
    rw [HahnSeries.support_filter] at hb
    refine absurd ?_ hc
    have hb0 := hb.2.2
    rw [← hb0]
    exact (hp b.1 (hf hb.1) b.2).mpr hb.2.1.2

end HahnSeries

end
end

/-!
## Factors supported in a convex exponent subgroup

If a product of two nonzero nonpositive Hahn series is supported in a convex subgroup of the
exponents, then both factors are supported there. Their lowest exponents add to the lowest
exponent of the product. Convexity first puts each lowest exponent in the subgroup, then puts
every later nonpositive support exponent there as well.
-/

section

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Field K]

/-- Nonzero nonpositive factors of a series supported in a convex exponent subgroup are
themselves supported in that subgroup. -/
@[blueprint "lem:convex-support-of-factors"
  (phase := "Finitely many Archimedean classes")
  (title := "Convexity of the supports of factors")
  (statement := /--
    Let $H$ be a convex subgroup of a linearly ordered abelian group $G$.  If
    $a,b\in K((G^{\le0}))$ are nonzero and
    $\operatorname{supp}(ab)\subseteq H$, then
    \[
      \operatorname{supp}(a)\subseteq H,
      \qquad
      \operatorname{supp}(b)\subseteq H.
    \]
  -/)
  (proof := /--
    The least support exponents satisfy
    $\min\operatorname{supp}(ab)=\min\operatorname{supp}(a)+
    \min\operatorname{supp}(b)$.  This sum and zero lie in $H$, while both
    summands are nonpositive, so convexity puts each least exponent in $H$.
    Every later support exponent lies between its least exponent and zero and
    therefore also belongs to $H$.
  -/)]
theorem support_subset_convex_of_mul_support_subset
    {H : AddSubgroup G} (hH : (H : Set G).OrdConnected)
    {a b : Nonpositive G K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (habH : ((a * b : Nonpositive G K) : K⟦G⟧).support ⊆ (H : Set G)) :
    (a : K⟦G⟧).support ⊆ (H : Set G) ∧ (b : K⟦G⟧).support ⊆ (H : Set G) := by
  have ha0' : (a : K⟦G⟧) ≠ 0 := fun h ↦ ha0 (Subtype.ext h)
  have hb0' : (b : K⟦G⟧) ≠ 0 := fun h ↦ hb0 (Subtype.ext h)
  have hab0' : ((a * b : Nonpositive G K) : K⟦G⟧) ≠ 0 := mul_ne_zero ha0' hb0'
  have habOrder : (a : K⟦G⟧).order + (b : K⟦G⟧).order ∈ H := by
    rw [← HahnSeries.order_mul_of_ne_zero (mul_ne_zero
      (HahnSeries.leadingCoeff_ne_zero.mpr ha0')
      (HahnSeries.leadingCoeff_ne_zero.mpr hb0'))]
    apply habH
    exact (HahnSeries.mem_support _ _).mpr
      (HahnSeries.coeff_order_eq_zero.not.mpr hab0')
  have haOrderMem : (a : K⟦G⟧).order ∈ (a : K⟦G⟧).support :=
    (HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr ha0')
  have hbOrderMem : (b : K⟦G⟧).order ∈ (b : K⟦G⟧).support :=
    (HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr hb0')
  have haOrderH : (a : K⟦G⟧).order ∈ H := by
    apply hH.out habOrder H.zero_mem
    constructor
    · simpa using add_le_add_left (support_subset b hbOrderMem) (a : K⟦G⟧).order
    · exact support_subset a haOrderMem
  have hbOrderH : (b : K⟦G⟧).order ∈ H := by
    apply hH.out habOrder H.zero_mem
    constructor
    · simpa [add_comm] using
        add_le_add_left (support_subset a haOrderMem) (b : K⟦G⟧).order
    · exact support_subset b hbOrderMem
  constructor
  · intro g hg
    apply hH.out haOrderH H.zero_mem
    exact ⟨HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support _ _).mp hg),
      support_subset a hg⟩
  · intro g hg
    apply hH.out hbOrderH H.zero_mem
    exact ⟨HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support _ _).mp hg),
      support_subset b hg⟩

end HahnSeries.Nonpositive

end
end
