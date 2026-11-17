/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive
public import ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Order.WellFounded
public import Mathlib.RingTheory.HahnSeries.Basic

import Mathlib.Order.WellFoundedSet
import ConwayRefinement.Blueprint

/-!
# Archimedean classes met by a nonpositive Hahn support

The Archimedean-class order puts elements of smaller magnitude in higher classes. Consequently,
on nonpositive exponents the class map is monotone: moving an exponent toward zero moves its class
up. The Archimedean classes met by a well-founded nonpositive support are therefore well ordered
in the ascending class order.

This orientation is the one needed by the Conway induction. Restriction to the closed class ball at
`c` keeps classes at least `c`; its complement consists of classes strictly below `c`, a proper
initial segment when the support meets `c`.
-/

universe u

open Set

namespace ArchimedeanClass

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

public section

/-- On nonpositive elements, the Archimedean-class map is monotone. -/
theorem mk_le_mk_of_le_of_nonpos {a b : G} (hab : a ≤ b) (hb : b ≤ 0) :
    ArchimedeanClass.mk a ≤ ArchimedeanClass.mk b := by
  refine ArchimedeanClass.mk_le_mk_of_abs ?_
  rw [abs_of_nonpos hb, abs_of_nonpos (hab.trans hb)]
  exact neg_le_neg hab

/-- An element outside the closed class ball at `c` has class strictly below `c`. -/
theorem mk_lt_of_not_mem_closedBallAddSubgroup {c : ArchimedeanClass G} {g : G}
    (hg : g ∉ closedBallAddSubgroup c) : ArchimedeanClass.mk g < c := by
  rw [mem_closedBallAddSubgroup_iff] at hg
  exact lt_of_not_ge hg

end

end ArchimedeanClass

namespace HahnSeries

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

public section

/-- The Archimedean classes of the nonzero exponents in a nonpositive Hahn series. Exponent zero
is excluded because the complementary factor has constant coefficient one; including its class
would prevent the induction rank from decreasing. -/
def Nonpositive.nonzeroSupportArchimedeanClasses
    {R : Type*} [Ring R] (x : Nonpositive G R) : Set (ArchimedeanClass G) :=
  ArchimedeanClass.mk '' ((x : R⟦G⟧).support \ {0})

/-- Membership among the Archimedean classes of the nonzero support. -/
theorem Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff
    {R : Type*} [Ring R] {x : Nonpositive G R} {c : ArchimedeanClass G} :
    c ∈ x.nonzeroSupportArchimedeanClasses ↔
      ∃ g ∈ (x : R⟦G⟧).support, g ≠ 0 ∧ ArchimedeanClass.mk g = c := by
  rw [nonzeroSupportArchimedeanClasses]
  constructor
  · rintro ⟨g, ⟨hg, hg0⟩, hgc⟩
    exact ⟨g, hg, by simpa only [Set.mem_singleton_iff] using hg0, hgc⟩
  · rintro ⟨g, hg, hg0, hgc⟩
    exact ⟨g, ⟨hg, by simpa only [Set.mem_singleton_iff] using hg0⟩, hgc⟩

/-- The Archimedean classes met by a nonpositive Hahn series are partially well ordered. -/
theorem Nonpositive.isPWO_supportArchimedeanClasses
    {R : Type*} [Ring R] (x : Nonpositive G R) :
    (ArchimedeanClass.mk '' (x : R⟦G⟧).support).IsPWO := by
  apply (x : R⟦G⟧).isPWO_support.image_of_monotoneOn
  intro a ha b hb hab
  exact ArchimedeanClass.mk_le_mk_of_abs (by
    rw [abs_of_nonpos (Nonpositive.support_subset x hb),
      abs_of_nonpos (Nonpositive.support_subset x ha)]
    exact neg_le_neg hab)

/-- The Archimedean classes of the nonzero support are partially well ordered. -/
theorem Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
    {R : Type*} [Ring R] (x : Nonpositive G R) :
    x.nonzeroSupportArchimedeanClasses.IsPWO := by
  apply x.isPWO_supportArchimedeanClasses.mono
  exact Set.image_mono Set.sdiff_subset

/-- If the nonzero support classes of one series lie strictly below a support class of another,
their order type is strictly smaller. -/
@[blueprint "lem:support-class-order-type-strict-decrease"
  (phase := "Transfinite induction on Archimedean classes")
  (title := "Strict decrease of support-class order type")
  (statement := /--
    Let $x,y\in K((G^{\le0}))$.  If $c$ is a nonzero Archimedean class met by
    $\operatorname{supp}(x)$ and every nonzero class met by
    $\operatorname{supp}(y)$ is a class met by $\operatorname{supp}(x)$ and is
    strictly below $c$, then the order type of the nonzero support classes of
    $y$ is strictly
    smaller than that of $x$.
  -/)
  (proof := /--
    The classes met by either nonpositive support are partially well ordered.
    Monotonicity of order type embeds the classes of $y$ into the initial
    segment of the classes of $x$ below $c$, and a proper initial segment of a
    well-order has strictly smaller order type.
  -/)]
theorem Nonpositive.orderType_nonzeroSupportArchimedeanClasses_lt
    {R : Type*} [Ring R] (x y : Nonpositive G R)
    {c : ArchimedeanClass G} (hc : c ∈ x.nonzeroSupportArchimedeanClasses)
    (hsub : y.nonzeroSupportArchimedeanClasses ⊆
      x.nonzeroSupportArchimedeanClasses ∩ Set.Iio c) :
    y.isPWO_nonzeroSupportArchimedeanClasses.orderType <
      x.isPWO_nonzeroSupportArchimedeanClasses.orderType := by
  let hxbelow := x.isPWO_nonzeroSupportArchimedeanClasses.mono
    (s := x.nonzeroSupportArchimedeanClasses ∩ Set.Iio c) Set.inter_subset_left
  exact (y.isPWO_nonzeroSupportArchimedeanClasses.orderType_mono hxbelow hsub).trans_lt
    (x.isPWO_nonzeroSupportArchimedeanClasses.orderType_inter_Iio_lt hc)

end

end HahnSeries
