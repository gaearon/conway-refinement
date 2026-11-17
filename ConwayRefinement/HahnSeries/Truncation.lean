/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

import ConwayRefinement.HahnSeries.EmbDomain
import Mathlib.Data.Rat.Floor

/-!
# Truncation and translation of Hahn series

A Hahn series can be restricted to a decidable set of exponents; restricting to the half-lines below
or above a cutoff gives the truncations used by Berarducci and by L'Innocente and Mantova.
Translation of exponents by `a` is multiplication by the monomial `t^a`.
-/

/-!
## Coefficient restrictions and truncations of Hahn series

This module restricts a Hahn series to an arbitrary decidable predicate on its exponents. The four
interval restrictions specialize this operation to LM24, Definition 3.2.2. Mathlib already
provides the strict lower truncation `HahnSeries.truncLT`; the definitions here add the weak lower,
weak upper, and strict upper truncations with the same argument order and `ZeroHom` interface.
Every resulting support is a subset of the original support, so these operations preserve any
fixed upper bound on support cardinality used in LM24.

The inequalities use the ambient order on the exponents. Thus `truncLE c x` retains the coefficient
of `x` at `i` exactly when `i ≤ c`; no reversal of the support order occurs.

Mathlib supplies `HahnSeries.truncLT`, which is reused directly. `Finsupp.filter` cannot apply to an
arbitrary well-ordered, possibly infinite support, and CombinatorialGames' surreal truncation uses
its reverse-support representation. The operations here therefore work directly with Hahn-series
coefficients and support proofs.
-/

section

universe u v

public noncomputable section

namespace HahnSeries

variable {R : Type v} {G : Type u}

section Zero

variable [PartialOrder G] [Zero R]

/-- Keep exactly the coefficients whose indices satisfy `p`. -/
def filter (p : G → Prop) [DecidablePred p] : ZeroHom R⟦G⟧ R⟦G⟧ where
  toFun x :=
    { coeff i := if p i then x.coeff i else 0
      isPWO_support' := x.isPWO_support.mono (by simp) }
  map_zero' := by ext; simp

@[simp]
protected theorem coeff_filter (p : G → Prop) [DecidablePred p] (x : R⟦G⟧) (i : G) :
    (filter p x).coeff i = if p i then x.coeff i else 0 :=
  (rfl)

/-- The support of a coefficient restriction is the corresponding subset of the original support. -/
theorem support_filter (p : G → Prop) [DecidablePred p] (x : R⟦G⟧) :
    (filter p x).support = {i ∈ x.support | p i} := by
  ext i
  simp [and_comm]

theorem support_filter_subset (p : G → Prop) [DecidablePred p] (x : R⟦G⟧) :
    (filter p x).support ⊆ x.support := by
  rw [support_filter]
  exact Set.sep_subset _ _

/-- Keeps exactly the coefficients at indices `i` satisfying `i ≤ c`. -/
def truncLE [DecidableLE G] (c : G) : ZeroHom R⟦G⟧ R⟦G⟧ :=
  filter (· ≤ c)

/-- Keeps exactly the coefficients at indices `i` satisfying `c < i`. -/
def truncGT [DecidableLT G] (c : G) : ZeroHom R⟦G⟧ R⟦G⟧ :=
  filter (c < ·)

@[simp]
protected theorem coeff_truncLE [DecidableLE G] (c : G) (x : R⟦G⟧) (i : G) :
    (truncLE c x).coeff i = if i ≤ c then x.coeff i else 0 :=
  (rfl)

@[simp]
protected theorem coeff_truncGT [DecidableLT G] (c : G) (x : R⟦G⟧) (i : G) :
    (truncGT c x).coeff i = if c < i then x.coeff i else 0 :=
  (rfl)

theorem coeff_truncLE_of_le [DecidableLE G] {c i : G} (h : i ≤ c) (x : R⟦G⟧) :
    (truncLE c x).coeff i = x.coeff i := by
  simp [h]

theorem support_truncLE [DecidableLE G] (c : G) (x : R⟦G⟧) :
    (truncLE c x).support = {i ∈ x.support | i ≤ c} :=
  support_filter _ _

theorem support_truncLE_subset [DecidableLE G] (c : G) (x : R⟦G⟧) :
    (truncLE c x).support ⊆ x.support :=
  support_filter_subset _ _

theorem support_truncGT_subset [DecidableLT G] (c : G) (x : R⟦G⟧) :
    (truncGT c x).support ⊆ x.support :=
  support_filter_subset _ _

/-- A weak lower truncation is the original series when the support lies below its cutoff. -/
theorem truncLE_eq_self_of_support_subset_Iic [DecidableLE G]
    {c : G} {x : R⟦G⟧} (h : x.support ⊆ Set.Iic c) :
    truncLE c x = x := by
  ext i
  by_cases hi : i ∈ x.support
  · exact coeff_truncLE_of_le (h hi) x
  · have hcoeff : x.coeff i = 0 := not_ne_iff.mp hi
    simp [hcoeff]

end Zero

section AddMonoid

variable [PartialOrder G] [AddMonoid R]

theorem filter_add (p : G → Prop) [DecidablePred p] (x y : R⟦G⟧) :
    filter p (x + y) = filter p x + filter p y := by
  ext i
  by_cases hi : p i <;> simp [hi]

theorem truncLE_add [DecidableLE G] (c : G) (x y : R⟦G⟧) :
    truncLE c (x + y) = truncLE c x + truncLE c y :=
  filter_add _ _ _

end AddMonoid

section LinearOrder

variable [LinearOrder G] [AddMonoid R]

end LinearOrder

end HahnSeries

end
end

/-!
## Translation of Hahn-series exponents

An order isomorphism between exponent types induces an additive equivalence between the
corresponding Hahn-series types. Translation by `a` is the specialization to the order
isomorphism `g ↦ a + g`. Its support is the translate of the original support, and it preserves
support order type.

For a semiring of coefficients, translation agrees with multiplication on either side by the
coefficient-one monomial at `a`. Thus `HahnSeries.translate a x` is the operation denoted by
`t^a x` or `x t^a` in LM24.

The construction uses `HahnSeries.embDomain`; the exact support formula comes from the
domain-embedding interface.
-/

section

universe u v w

public noncomputable section

namespace HahnSeries

section Reindex

variable {R : Type w} {G : Type u} {H : Type v}
variable [PartialOrder G] [PartialOrder H] [AddMonoid R]

/-- Reindex Hahn-series exponents along an order isomorphism. -/
def embDomainAddEquiv (e : G ≃o H) : R⟦G⟧ ≃+ R⟦H⟧ where
  toFun := embDomain e.toOrderEmbedding
  invFun := embDomain e.symm.toOrderEmbedding
  left_inv x := by
    ext g
    have outer := embDomain_coeff (f := e.symm.toOrderEmbedding)
      (x := embDomain e.toOrderEmbedding x) (a := e g)
    have inner := embDomain_coeff (f := e.toOrderEmbedding) (x := x) (a := g)
    simpa using outer.trans inner
  right_inv x := by
    ext h
    have outer := embDomain_coeff (f := e.toOrderEmbedding)
      (x := embDomain e.symm.toOrderEmbedding x) (a := e.symm h)
    have inner := embDomain_coeff (f := e.symm.toOrderEmbedding) (x := x) (a := h)
    simpa using outer.trans inner
  map_add' := embDomain_add e.toOrderEmbedding

@[simp]
theorem coeff_embDomainAddEquiv (e : G ≃o H) (x : R⟦G⟧) (g : G) :
    (embDomainAddEquiv e x).coeff (e g) = x.coeff g :=
  embDomain_coeff

end Reindex

section OrderType

variable {R : Type v} {G H : Type u}
variable [LinearOrder G] [LinearOrder H] [AddMonoid R]

end OrderType

section Translation

variable {R : Type v} {G : Type u}
variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [AddMonoid R]

/-- Translate every exponent in a Hahn series by `a`. -/
def translate (a : G) : R⟦G⟧ ≃+ R⟦G⟧ :=
  embDomainAddEquiv (OrderIso.addLeft a)

theorem coeff_translate_add (a g : G) (x : R⟦G⟧) :
    (translate a x).coeff (a + g) = x.coeff g :=
  coeff_embDomainAddEquiv _ _ _

/-- Translation evaluates at `g` by reading the original coefficient at `g - a`. -/
@[simp]
theorem coeff_translate (a g : G) (x : R⟦G⟧) :
    (translate a x).coeff g = x.coeff (g - a) := by
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    coeff_translate_add a (g - a) x

/-- The support of a translated Hahn series is the corresponding translate of its support. -/
theorem support_translate (a : G) (x : R⟦G⟧) :
    (translate a x).support = (a + ·) '' x.support :=
  support_embDomain _ _

@[simp]
theorem translate_zero_apply (x : R⟦G⟧) : translate 0 x = x := by
  ext g
  simp

@[simp]
theorem translate_add_apply (a b : G) (x : R⟦G⟧) :
    translate a (translate b x) = translate (a + b) x := by
  ext g
  simp [sub_sub]

end Translation

section TranslationOrderType

variable {R : Type v} {G : Type u}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [AddMonoid R]

end TranslationOrderType

section Monomial

variable {R : Type v} {G : Type u}
variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Semiring R]

/-- Left multiplication by the coefficient-one monomial at `a` translates exponents by `a`. -/
theorem single_one_mul_eq_translate (a : G) (x : R⟦G⟧) :
    single a 1 * x = translate a x := by
  ext g
  rw [coeff_single_mul, coeff_translate, one_mul]

/-- Right multiplication by the coefficient-one monomial at `a` translates exponents by `a`. -/
theorem mul_single_one_eq_translate (x : R⟦G⟧) (a : G) :
    x * single a 1 = translate a x := by
  ext g
  rw [coeff_mul_single, coeff_translate, mul_one]

/-- The product of two translated Hahn series is the translate of their product by the sum of
the two shifts. -/
theorem translate_mul_translate (a b : G) (x y : R⟦G⟧) :
    translate a x * translate b y = translate (a + b) (x * y) := by
  calc
    translate a x * translate b y =
        (single a 1 * x) * (single b 1 * y) := by
      rw [single_one_mul_eq_translate, single_one_mul_eq_translate]
    _ = single a 1 * (x * single b 1) * y := by simp only [mul_assoc]
    _ = single a 1 * translate b x * y := by
      rw [mul_single_one_eq_translate x b]
    _ = single a 1 * (single b 1 * x) * y := by
      rw [single_one_mul_eq_translate b x]
    _ = (single a 1 * single b 1) * (x * y) := by simp only [mul_assoc]
    _ = single (a + b) 1 * (x * y) := by rw [single_mul_single, one_mul]
    _ = translate (a + b) (x * y) := single_one_mul_eq_translate _ _

end Monomial

end HahnSeries

end
end
