/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.ExponentPrimitive
public import Mathlib.Algebra.MonoidAlgebra.Basic

import ConwayRefinement.HahnSeries.Nonpositive.SubgroupSupport
import Mathlib.Data.Rat.Floor

/-!
# Finite-support series supported in a subgroup as a group ring

The finite-support series supported in a subgroup `H` of the exponents form the group ring of `H`. A
least common multiple computed in this subring remains one in the whole finite-support ring (Gilmer
and Parker, Theorem 5.2).
-/

/-!
## Series supported in a subgroup as a group ring

The finite-support series supported in a subgroup `H` of the exponents are the group ring of `H`.
The identification is the algebra map sending a group element to its monomial, so multiplication
is matched by the monomial rule and no convolution computation is needed.

This is what carries unique factorisation, and with it least common multiples, from the group ring
of a free abelian group of finite rank into the series ring.
-/

section

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- Monomials with exponent in a subgroup, as a monoid homomorphism. -/
def subgroupMonomialHom (H : AddSubgroup G) : Multiplicative H →* K⟦G⟧ where
  toFun h := single ((Multiplicative.toAdd h : H) : G) (1 : K)
  map_one' := by simp
  map_mul' a b := by
    rw [HahnSeries.single_mul_single, one_mul]
    rfl

/-- The group ring of a subgroup of the exponents, mapped into the series ring. -/
def subgroupAlgebraHom (H : AddSubgroup G) : AddMonoidAlgebra K H →ₐ[K] K⟦G⟧ :=
  AddMonoidAlgebra.lift K (K⟦G⟧) H (subgroupMonomialHom H)

@[simp]
theorem subgroupAlgebraHom_single (H : AddSubgroup G) (a : H) (b : K) :
    subgroupAlgebraHom H (Finsupp.single a b) = single (a : G) b := by
  rw [subgroupAlgebraHom, AddMonoidAlgebra.lift_single]
  ext g
  simp [subgroupMonomialHom, HahnSeries.coeff_single]

open Classical in
/-- The coefficients of a monomial image. -/
private theorem coeff_subgroupAlgebraHom_single (H : AddSubgroup G) (a : H) (b : K) (g : G) :
    (subgroupAlgebraHom H (Finsupp.single a b)).coeff g
      = if hg : g ∈ H then (Finsupp.single a b : H →₀ K) ⟨g, hg⟩ else 0 := by
  rw [subgroupAlgebraHom_single, HahnSeries.coeff_single]
  by_cases hg : g ∈ H
  · rw [dif_pos hg, Finsupp.single_apply]
    by_cases hga : g = (a : G)
    · rw [if_pos hga, if_pos (Subtype.ext hga.symm : a = ⟨g, hg⟩)]
    · rw [if_neg hga, if_neg (fun h : a = ⟨g, hg⟩ ↦ hga (congrArg Subtype.val h).symm)]
  · rw [dif_neg hg, if_neg]
    rintro rfl
    exact hg a.2

open Classical in
/-- The coefficients of the image are the coefficients of the group-ring element. -/
theorem coeff_subgroupAlgebraHom (H : AddSubgroup G) (f : AddMonoidAlgebra K H) (g : G) :
    (subgroupAlgebraHom H f).coeff g = if hg : g ∈ H then f ⟨g, hg⟩ else 0 := by
  induction f using AddMonoidAlgebra.induction_on with
  | hM m =>
    have hof : (AddMonoidAlgebra.of K H (Multiplicative.ofAdd m) : AddMonoidAlgebra K H)
        = Finsupp.single m 1 := rfl
    rw [hof]
    exact coeff_subgroupAlgebraHom_single H m 1 g
  | hadd x y hx hy =>
    rw [map_add, HahnSeries.coeff_add, hx, hy]
    by_cases hg : g ∈ H <;> simp [hg]
  | hsmul r x hx =>
    rw [map_smul, HahnSeries.coeff_smul, hx]
    by_cases hg : g ∈ H <;> simp [hg]

open Classical in
theorem subgroupAlgebraHom_injective (H : AddSubgroup G) :
    Function.Injective (subgroupAlgebraHom H (K := K)) := by
  intro f₁ f₂ h
  ext a
  have hc := congrArg (fun x : K⟦G⟧ ↦ x.coeff (a : G)) h
  simp only [coeff_subgroupAlgebraHom, dif_pos a.2] at hc
  simpa using hc

open Classical in
theorem support_subgroupAlgebraHom_subset (H : AddSubgroup G) (f : AddMonoidAlgebra K H) :
    (subgroupAlgebraHom H f).support ⊆ (H : Set G) := by
  intro g hg
  rw [HahnSeries.mem_support, coeff_subgroupAlgebraHom] at hg
  by_cases hgH : g ∈ H
  · exact hgH
  · rw [dif_neg hgH] at hg
    exact absurd rfl hg

open Classical in
theorem support_subgroupAlgebraHom_finite (H : AddSubgroup G) (f : AddMonoidAlgebra K H) :
    (subgroupAlgebraHom H f).support.Finite := by
  refine Set.Finite.subset ((f.support : Finset H).finite_toSet.image ((↑) : H → G)) ?_
  intro g hg
  rw [HahnSeries.mem_support, coeff_subgroupAlgebraHom] at hg
  by_cases hgH : g ∈ H
  · rw [dif_pos hgH] at hg
    exact ⟨⟨g, hgH⟩, Finsupp.mem_support_iff.mpr hg, rfl⟩
  · rw [dif_neg hgH] at hg
    exact absurd rfl hg

open Classical in
/-- Every finite-support series supported in `H` comes from the group ring of `H`. -/
theorem exists_subgroupAlgebraHom_eq
    (H : AddSubgroup G) {x : K⟦G⟧} (hfin : x.support.Finite)
    (hsub : x.support ⊆ (H : Set G)) :
    ∃ f : AddMonoidAlgebra K H, subgroupAlgebraHom H f = x := by
  set xf : G →₀ K := Finsupp.onFinset hfin.toFinset x.coeff
    (fun a ha ↦ hfin.mem_toFinset.mpr ha) with hxf
  have hinj : Set.InjOn ((↑) : H → G) (((↑) : H → G) ⁻¹' xf.support) :=
    fun a _ b _ hab ↦ Subtype.ext hab
  refine ⟨Finsupp.comapDomain ((↑) : H → G) xf hinj, ?_⟩
  ext g
  rw [coeff_subgroupAlgebraHom]
  by_cases hgH : g ∈ H
  · rw [dif_pos hgH, Finsupp.comapDomain_apply, hxf, Finsupp.onFinset_apply]
  · rw [dif_neg hgH]
    by_contra hne
    exact hgH (hsub ((HahnSeries.mem_support _ _).mpr (Ne.symm hne)))

/-- Divisibility in the group ring of `H` matches divisibility of the images. -/
theorem dvd_iff_groupRingDvd_subgroupAlgebraHom (H : AddSubgroup G) (a b : AddMonoidAlgebra K H) :
    a ∣ b ↔ GroupRingDvd (subgroupAlgebraHom H a) (subgroupAlgebraHom H b) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact groupRingDvd_iff.mpr ⟨subgroupAlgebraHom H c, support_subgroupAlgebraHom_finite H c,
      by rw [map_mul]⟩
  · intro h
    obtain ⟨w, hwf, hw⟩ := groupRingDvd_iff.mp h
    rcases eq_or_ne (subgroupAlgebraHom H a) 0 with h0 | h0
    · have ha : a = 0 := subgroupAlgebraHom_injective H (by rw [h0, map_zero])
      refine ⟨0, ?_⟩
      refine subgroupAlgebraHom_injective H ?_
      rw [map_mul, map_zero, mul_zero, hw, h0, zero_mul]
    · have hwsub : w.support ⊆ (H : Set G) :=
        support_subset_of_mul_eq (support_subgroupAlgebraHom_subset H a) h0
          (support_subgroupAlgebraHom_subset H b) hw
      obtain ⟨c, hc⟩ := exists_subgroupAlgebraHom_eq H hwf hwsub
      refine ⟨c, subgroupAlgebraHom_injective H ?_⟩
      rw [map_mul, hc, hw]

end HahnSeries

end
end

/-!
## Transferring least common multiples out of a subgroup of the exponents

Gilmer and Parker, Theorem 5.2 computes a least common multiple inside a finitely generated
subgroup of the exponents and observes that it stays one in the whole ring, because the ring is a
free module over the subring on coset representatives.

The same conclusion is reached here without modules. A common multiple is peeled one coset at a
time: multiplying by a factor supported in the subgroup commutes with restricting to a coset, so
each restriction is again a common multiple, and translating it back into the subgroup puts it in
the range of the hypothesis. The remaining part has strictly smaller support, which drives the
induction.
-/

section

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

theorem groupRingDvd_zero (e : K⟦G⟧) : GroupRingDvd e 0 :=
  groupRingDvd_iff.mpr ⟨0, by simp, by simp⟩

theorem GroupRingDvd.add {e a b : K⟦G⟧} (ha : GroupRingDvd e a) (hb : GroupRingDvd e b) :
    GroupRingDvd e (a + b) := by
  obtain ⟨u, huf, hu⟩ := groupRingDvd_iff.mp ha
  obtain ⟨v, hvf, hv⟩ := groupRingDvd_iff.mp hb
  exact groupRingDvd_iff.mpr ⟨u + v, (huf.union hvf).subset (HahnSeries.support_add_subset u v),
    by rw [hu, hv, mul_add]⟩

theorem GroupRingDvd.trans {e a b : K⟦G⟧} (h1 : GroupRingDvd e a) (h2 : GroupRingDvd a b) :
    GroupRingDvd e b := by
  obtain ⟨u, huf, hu⟩ := groupRingDvd_iff.mp h1
  obtain ⟨v, hvf, hv⟩ := groupRingDvd_iff.mp h2
  refine groupRingDvd_iff.mpr ⟨u * v, ?_, by rw [hv, hu, mul_assoc]⟩
  exact (huf.add hvf).subset HahnSeries.support_mul_subset

theorem GroupRingDvd.sub {e a b : K⟦G⟧} (ha : GroupRingDvd e a) (hb : GroupRingDvd e b) :
    GroupRingDvd e (a - b) := by
  obtain ⟨u, huf, hu⟩ := groupRingDvd_iff.mp ha
  obtain ⟨v, hvf, hv⟩ := groupRingDvd_iff.mp hb
  refine groupRingDvd_iff.mpr ⟨u - v, ?_, by rw [hu, hv, mul_sub]⟩
  refine (huf.union hvf).subset ?_
  rw [sub_eq_add_neg]
  refine (HahnSeries.support_add_subset u (-v)).trans ?_
  rw [HahnSeries.support_neg]

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- Membership in a fixed coset is invariant under translation by the subgroup. -/
private theorem coset_invariant (H : AddSubgroup G) (s : G) :
    ∀ i ∈ H, ∀ j : G, (i + j - s ∈ H ↔ j - s ∈ H) := by
  intro i hi j
  constructor
  · intro hij
    have hrw : j - s = i + j - s - i := by abel
    rw [hrw]
    exact H.sub_mem hij hi
  · intro hj
    have hrw : i + j - s = i + (j - s) := by abel
    rw [hrw]
    exact H.add_mem hi hj

open Classical in
/-- Gilmer and Parker, Theorem 5.2: a common multiple property verified inside a subgroup of the
exponents holds against every finite-support common multiple. -/
theorem groupRingDvd_of_forall_subgroup {H : AddSubgroup G} {f g h : K⟦G⟧}
    (hf : f.support ⊆ (H : Set G)) (hg : g.support ⊆ (H : Set G))
    (hlcm : ∀ m : K⟦G⟧, m.support.Finite → m.support ⊆ (H : Set G) →
      GroupRingDvd f m → GroupRingDvd g m → GroupRingDvd h m)
    {m : K⟦G⟧} (hmfin : m.support.Finite) (h1 : GroupRingDvd f m) (h2 : GroupRingDvd g m) :
    GroupRingDvd h m := by
  suffices key : ∀ (n : ℕ) (S : Finset G) (w : K⟦G⟧),
      S.card ≤ n → w.support ⊆ (S : Set G) → GroupRingDvd f w → GroupRingDvd g w →
        GroupRingDvd h w by
    exact key hmfin.toFinset.card hmfin.toFinset m le_rfl (by simp) h1 h2
  intro n
  induction n with
  | zero =>
    intro S w hcard hsub _ _
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    rw [hS] at hsub
    have hw : w = 0 := by
      rw [← HahnSeries.support_eq_empty_iff]
      exact Set.subset_empty_iff.mp (by simpa using hsub)
    rw [hw]
    exact groupRingDvd_zero h
  | succ n ih =>
    intro S w hcard hsub hfw hgw
    rcases eq_or_ne w 0 with rfl | hw0
    · exact groupRingDvd_zero h
    obtain ⟨s, hs⟩ := HahnSeries.support_nonempty_iff.mpr hw0
    have hsS : s ∈ S := by simpa using hsub hs
    have hwfin : w.support.Finite := (S.finite_toSet).subset hsub
    have hinv := coset_invariant H s
    -- restrict to the coset of `s`; the rest is the difference
    have hdvd : ∀ e : K⟦G⟧, e.support ⊆ (H : Set G) → GroupRingDvd e w →
        GroupRingDvd e (filter (fun g ↦ g - s ∈ H) w) := by
      intro e he hew
      obtain ⟨u, huf, rfl⟩ := groupRingDvd_iff.mp hew
      exact groupRingDvd_iff.mpr ⟨filter (fun g ↦ g - s ∈ H) u,
        huf.subset (HahnSeries.support_filter_subset _ u),
        filter_mul_of_invariant he (fun g ↦ g - s ∈ H) hinv⟩
    have hf₀ := hdvd f hf hfw
    have hg₀ := hdvd g hg hgw
    have hcoeff : ∀ x : G,
        (w - filter (fun g ↦ g - s ∈ H) w).coeff x = if x - s ∈ H then 0 else w.coeff x := by
      intro x
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_filter]
      by_cases hx : x - s ∈ H <;> simp [hx]
    -- the remaining part misses `s`, so its support fits in a smaller finset
    have hrest : GroupRingDvd h (w - filter (fun g ↦ g - s ∈ H) w) := by
      refine ih (S.erase s) _ ?_ ?_ (hfw.sub hf₀) (hgw.sub hg₀)
      · have := Finset.card_erase_of_mem hsS
        omega
      · intro x hx
        rw [HahnSeries.mem_support, hcoeff x] at hx
        by_cases hxp : x - s ∈ H
        · exact absurd (if_pos hxp) hx
        · rw [if_neg hxp] at hx
          refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, ?_⟩)
          · rintro rfl
            exact hxp (by simp)
          · simpa using hsub ((HahnSeries.mem_support _ _).mpr hx)
    -- the coset part translates into the subgroup, where the hypothesis applies
    have hcoset : GroupRingDvd h (filter (fun g ↦ g - s ∈ H) w) := by
      set w₀ := filter (fun g ↦ g - s ∈ H) w with hw₀
      have hback : translate s (translate (-s) w₀) = w₀ := by
        rw [HahnSeries.translate_add_apply]
        simp
      have hsupp : (translate (-s) w₀).support ⊆ (H : Set G) := by
        rw [HahnSeries.support_translate]
        rintro _ ⟨x, hx, rfl⟩
        rw [hw₀, HahnSeries.support_filter] at hx
        change -s + x ∈ (H : Set G)
        rw [show -s + x = x - s from by abel]
        exact hx.2
      have hfin : (translate (-s) w₀).support.Finite := by
        rw [HahnSeries.support_translate]
        exact (hwfin.subset (hw₀ ▸ HahnSeries.support_filter_subset _ w)).image _
      have hkey := hlcm _ hfin hsupp
        (by rw [← hback] at hf₀; exact groupRingDvd_translate_iff.mp hf₀)
        (by rw [← hback] at hg₀; exact groupRingDvd_translate_iff.mp hg₀)
      rw [← hback]
      exact groupRingDvd_translate_iff.mpr hkey
    have hsum : filter (fun g ↦ g - s ∈ H) w + (w - filter (fun g ↦ g - s ∈ H) w) = w := by
      abel
    rw [← hsum]
    exact hcoset.add hrest

end HahnSeries

end
end
