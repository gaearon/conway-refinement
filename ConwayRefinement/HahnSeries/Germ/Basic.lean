/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import ConwayRefinement.HahnSeries.Nonpositive.Basic

import ConwayRefinement.Blueprint
public import ConwayRefinement.HahnSeries.CantorBendixson.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import ConwayRefinement.HahnSeries.CantorBendixson.Truncation
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The ideal of series bounded away from zero

Let `G` be a nontrivial ordered abelian group and `R` a commutative ring. The ideal `J` of
`R((G^{≤0}))` consists of the nonpositive series whose support is bounded away from zero, that is,
contained in `(-∞, c]` for some `c < 0`. The quotient `R((G^{≤0}))/J` is the ring of germs at zero:
two series have the same germ exactly when they agree above some negative exponent.

For the order topology on `G`, a series lies in `J` exactly when its Cantor–Bendixson value is
zero, and series congruent modulo `J` have the same Cantor–Bendixson value. That `J` is prime when
`G` is Cauchy complete and `R` is a field of characteristic zero is proved in
`ConwayRefinement.HahnSeries.Germ.PolynomialRing`.
-/

public noncomputable section
open Set
universe u v
namespace HahnSeries.Nonpositive
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Nontrivial G] [CommRing R]

variable (G R) in
/-- The ideal `J` of nonpositive series whose support is bounded away from zero. -/
@[blueprint "def:bounded-away-ideal"
  (phase := "Germs of translated truncations")
  (title := "The ideal $J$")
  (statement := /--
    Let $G$ be a nontrivial ordered abelian group and $R$ a commutative ring.
    Let $J\subseteq R((G^{\le0}))$ be the set of series $b$ for which there is
    $c<0$ with $\operatorname{supp}(b)\subseteq(-\infty,c]$, that is, the series
    whose support is bounded away from $0$.  Then $J$ is an ideal of
    $R((G^{\le0}))$.  For $G=\mathbb R$ this is the ideal $J$ of
    [Ber00, Def. 5.1].
  -/)
  (proof := /--
    The zero series has empty support, and $G$ has a negative element because
    it is nontrivial.  If $\operatorname{supp}(b)\subseteq(-\infty,c]$ and
    $\operatorname{supp}(d)\subseteq(-\infty,c']$, then
    $\operatorname{supp}(b+d)\subseteq(-\infty,\max(c,c')]$.  For
    $a\in R((G^{\le0}))$, $\operatorname{supp}(ab)\subseteq
    \operatorname{supp}(a)+\operatorname{supp}(b)\subseteq(-\infty,c]$
    because $\operatorname{supp}(a)\subseteq(-\infty,0]$.
  -/)]
def boundedAwayIdeal : Ideal (Nonpositive G R) where
  carrier := {b | ∃ c < (0 : G), (b : HahnSeries G R).support ⊆ Iic c}
  zero_mem' := by
    obtain ⟨c, hc⟩ := exists_lt (0 : G)
    exact ⟨c, hc, by simp⟩
  add_mem' := by
    rintro b d ⟨c, hc, hb⟩ ⟨c', hc', hd⟩
    refine ⟨max c c', max_lt hc hc', fun x hx => ?_⟩
    rcases HahnSeries.support_add_subset (b : HahnSeries G R) d hx with hx | hx
    · exact (hb hx).trans (le_max_left c c')
    · exact (hd hx).trans (le_max_right c c')
  smul_mem' := by
    rintro a b ⟨c, hc, hb⟩
    refine ⟨c, hc, fun x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := HahnSeries.support_mul_subset hx
    exact (add_le_add (support_subset a hy) (hb hz)).trans_eq (zero_add c)

/-- A series lies in `J` exactly when its support is bounded strictly below zero. -/
theorem mem_boundedAwayIdeal (b : Nonpositive G R) :
    b ∈ boundedAwayIdeal G R ↔ ∃ c < (0 : G), (b : HahnSeries G R).support ⊆ Iic c := Iff.rfl

/-- The constant `1` is not bounded away from zero. -/
theorem one_notMem_boundedAwayIdeal [Nontrivial R] :
    (1 : Nonpositive G R) ∉ boundedAwayIdeal G R := by
  rintro ⟨c, hc, h⟩
  have h0 : (0 : G) ∈ ((1 : Nonpositive G R) : HahnSeries G R).support := by
    rw [HahnSeries.mem_support]
    simp
  exact absurd (h h0) (not_le.mpr hc)

instance [Nontrivial R] : Nontrivial (Nonpositive G R ⧸ boundedAwayIdeal G R) :=
  Ideal.Quotient.nontrivial_iff.mpr ((Ideal.ne_top_iff_one _).mpr one_notMem_boundedAwayIdeal)

/-- Two germs agree exactly when their representatives agree above some negative bound. -/
theorem mk_eq_mk_iff_eventually_coeff_eq (b c : Nonpositive G R) :
    Ideal.Quotient.mk (boundedAwayIdeal G R) b = Ideal.Quotient.mk (boundedAwayIdeal G R) c ↔
        ∃ e < (0 : G), ∀ g > e, (b : HahnSeries G R).coeff g = (c : HahnSeries G R).coeff g := by
  rw [Ideal.Quotient.eq, mem_boundedAwayIdeal]
  constructor
  · rintro ⟨e, he, hbc⟩
    refine ⟨e, he, fun g hg ↦ ?_⟩
    have hz : ((b - c : Nonpositive G R) : HahnSeries G R).coeff g = 0 := by
      by_contra hn
      exact (not_le_of_gt hg) (hbc hn)
    change ((b : HahnSeries G R) - (c : HahnSeries G R)).coeff g = 0 at hz
    simpa only [coeff_sub, sub_eq_zero] using hz
  · rintro ⟨e, he, hbc⟩
    refine ⟨e, he, fun g hg ↦ ?_⟩
    apply le_of_not_gt
    intro hge
    have hz := hbc g hge
    apply hg
    change ((b : HahnSeries G R) - (c : HahnSeries G R)).coeff g = 0
    simpa only [coeff_sub, sub_eq_zero] using hz

/-- A series representing a unit germ has nonzero coefficient at exponent zero. -/
theorem constantCoeff_ne_zero_of_isUnit_mk [Nontrivial R] {b : Nonpositive G R}
    (hb : IsUnit (Ideal.Quotient.mk (boundedAwayIdeal G R) b)) :
    constantCoeff b ≠ 0 := by
  let J := boundedAwayIdeal G R
  obtain ⟨q, hbq, _⟩ := isUnit_iff_exists.mp hb
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  have heq : Ideal.Quotient.mk J (b * c) = Ideal.Quotient.mk J 1 := by
    simpa only [map_mul, map_one] using hbq
  obtain ⟨e, he, hcoeff⟩ := (mk_eq_mk_iff_eventually_coeff_eq (b * c) 1).mp heq
  have hbc : constantCoeff b * constantCoeff c = 1 := by
    have hbc' := hcoeff 0 he
    rw [show ((b * c : Nonpositive G R) : HahnSeries G R).coeff 0 =
      (b : HahnSeries G R).coeff 0 * (c : HahnSeries G R).coeff 0 from
        coeff_zero_mul b c] at hbc'
    simpa only [constantCoeff_apply, Subring.coe_one, HahnSeries.coeff_one, if_pos] using hbc'
  intro hb0
  rw [hb0, zero_mul] at hbc
  exact zero_ne_one hbc

variable [TopologicalSpace G] [OrderTopology G]

/-- A series lies in `J` exactly when its Cantor–Bendixson value vanishes. -/
theorem mem_boundedAwayIdeal_iff_cantorBendixsonValue_eq_zero (b : Nonpositive G R) :
    b ∈ boundedAwayIdeal G R ↔ (b : HahnSeries G R).cantorBendixsonValue = 0 :=
  (cantorBendixsonValue_eq_zero_iff_support_bounded_lt _ (support_subset b)).symm

/-- Series congruent modulo `J` have the same Cantor–Bendixson value. -/
theorem cantorBendixsonValue_eq_of_sub_mem {b d : Nonpositive G R}
    (h : b - d ∈ boundedAwayIdeal G R) :
    (b : HahnSeries G R).cantorBendixsonValue = (d : HahnSeries G R).cantorBendixsonValue := by
  obtain ⟨c, hc, hs⟩ := h
  have hcoeff : ∀ x, c < x → (b : HahnSeries G R).coeff x = (d : HahnSeries G R).coeff x := by
    intro x hx
    by_contra hne
    have hmem : x ∈ ((b - d : Nonpositive G R) : HahnSeries G R).support := by
      change ((b : HahnSeries G R) - (d : HahnSeries G R)).coeff x ≠ 0
      rwa [coeff_sub, sub_ne_zero]
    exact absurd (hs hmem) (not_le.mpr hx)
  refine cantorBendixsonValue_congr_of_support_inter_eq isOpen_Ioi hc (Set.ext fun x => ?_)
  simp only [mem_inter_iff, HahnSeries.mem_support, mem_Ioi]
  exact ⟨fun ⟨h1, h2⟩ => ⟨hcoeff x h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hcoeff x h2).symm ▸ h1, h2⟩⟩

end HahnSeries.Nonpositive
