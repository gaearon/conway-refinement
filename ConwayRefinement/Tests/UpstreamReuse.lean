/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.MonoidAlgebra.ToDirectSum
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.HahnSeries.Cardinal
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Cardinal.Cofinality.Basic
import Mathlib.SetTheory.ZFC.Class
import Mathlib.SetTheory.Ordinal.Family
import CombinatorialGames.NatOrdinal.Pow
import CombinatorialGames.Surreal.HahnSeries.Basic
import CombinatorialGames.Surreal.Ordinal

/-!
# Upstream reuse checks

This module pins the availability and compiler-visible signatures of selected upstream interfaces.
It intentionally declares no mathematical API. The hash-command linter is disabled here because
the module consists precisely of checked signature fixtures.
-/

set_option linter.hashCommand false

universe u v w

#check @FractionRing

#check @algebraicClosure

#check @minpoly.natDegree_eq_one_iff

#check (@IsPrimal : {α : Type u} → [Semigroup α] → α → Prop)

#check (@DecompositionMonoid : (α : Type u) → [Semigroup α] → Prop)

#check
  (@Ordinal.isPrincipal_add_iff_zero_or_omega0_opow :
    {o : Ordinal.{u}} →
      Ordinal.IsPrincipal (· + ·) o ↔
        o = 0 ∨ o ∈ Set.range fun e : Ordinal.{u} ↦ Ordinal.omega0 ^ e)

#check
  (@Ordinal.sub_omega0_opow_log_lt :
    {o : Ordinal.{u}} →
      o ≠ 0 → o - Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o < o)

#check NatOrdinal.wpow_add

#check Ordinal.isPrincipal_mul_iff_le_two_or_omega0_opow_opow

#check Ordinal.log_opow

#check Ordinal.opow_add

#check StrictMonoOn.orderIso

#check Ordinal.isSuccPrelimit_type_lt_iff

#check Ordinal.lt_mul_iff_of_isSuccLimit

#check OrderIso.isLUB_image'

#check List.dropLast_append_getLast

#check Ideal.span

#check Ideal.IsPrime.mem_or_mem

#check Ideal.mul_mem_right

#check Ideal.Quotient.mk

#check Ideal.Quotient.eq

#check AddSubgroup.mem_sup

#check Valuation

#check Valuation.supp

#check Valuation.extendToLocalization

#check QuotientAddGroup.map
#check QuotientAddGroup.lift

#check DirectSum.map
#check DirectSum.toModule

#check Submonoid.IsLocalizationMap

#check Localization.algEquiv

#check IsLocalization.ringEquivOfRingEquiv

#check IsLocalization.tensorProductEquivOfMapIncludeRight

#check FractionRing

#check IsLocalization.lift

#check IsLocalization.lift_mk'_spec

#check IsLocalization.ringHom_ext

#check Algebra.TensorProduct.rightAlgebra

#check IsLocalization.isDomain_localization

#check Valuation.integer

#check Valuation.ltIdeal

#check DirectSum.GCommRing

#check DirectSum.GSemiring

#check DirectSum.GNonUnitalNonAssocSemiring.add_mul

#check DirectSum.GNonUnitalNonAssocSemiring.mul_add

#check LinearMap.mk₂

#check LinearEquiv.cast

#check AddEquiv.cast

#check DirectSum.toAlgebra

#check DirectSum.of_eq_of_gradedMonoid_eq

#check Derivation.mk'

#check Finset.set_biUnion_insert

#check NatOrdinal.add_lt_wpow

#check DirectSum.mul_eq_sum_support_ghas_mul

#check AddMonoidAlgebra.toDirectSum

#check AddMonoidAlgebra.toDirectSum_mul

#check DirectSum.toAddMonoidAlgebra_toDirectSum

#check AddMonoidAlgebra.scalarTensorEquiv

#check AddMonoidAlgebra.scalarTensorEquiv_tmul

#check AddMonoidAlgebra.scalarTensorEquiv_symm_single

#check AddMonoidAlgebra.mapRingHom

#check AddMonoidAlgebra.range_map

#check Finset.max

#check Con

#check Con.mk'

#check DirectSum.ofZeroRingHom

#check TensorProduct.directSumLeft

#check Filter.Germ

#check Filter.Germ.map

#check Filter.Germ.LiftPred

#check Filter.Germ.inductionOn

#check TensorProduct.map

#check TensorProduct.lift

#check LinearMap.rTensor

#check LinearMap.leftInverse_comp_of_inj

#check DirectSum.congrLinearEquiv

#check Algebra.TensorProduct.productMap

#check AlgEquiv.ofBijective

#check Submodule.exists_isCompl

#check Submodule.quotientEquivOfIsCompl

#check Module.Free.chooseBasis

#check Module.Projective.exists_dual_eq_one

#check MvPolynomial.aeval

#check RingHom.quotientKerEquivOfSurjective

#check RingHom.mem_range

#check Finsupp.ne_iff

#check IsField.mul_inv_cancel

#check csInf_mem

#check NatOrdinal.of

#check
  (@HahnSeries.cardSuppLTSubring :
    (Γ : Type u) →
      (R : Type v) →
        (κ : Cardinal.{u}) →
          [PartialOrder Γ] →
            [AddCommMonoid Γ] →
              [IsOrderedCancelAddMonoid Γ] →
                [Ring R] → [Fact (Cardinal.aleph0 ≤ κ)] → Subring (HahnSeries Γ R))

#check
  (@HahnSeries.cardSuppLTSubfield :
    (Γ : Type u) →
      (R : Type v) →
        (κ : Cardinal.{u}) →
          [LinearOrder Γ] →
            [AddCommGroup Γ] →
              [IsOrderedAddMonoid Γ] →
                [Field R] → [Fact (Cardinal.aleph0 < κ)] → Subfield (HahnSeries Γ R))

#check
  (@Order.le_cof_iff :
    ∀ {α : Type u} [Preorder α] {c : Cardinal.{u}},
      c ≤ Order.cof α ↔ ∀ s : Set α, IsCofinal s → c ≤ Cardinal.mk ↥s)

#check
  (@not_isCofinal_iff :
    ∀ {α : Type u} [LinearOrder α] {s : Set α},
      ¬ IsCofinal s ↔ ∃ x, ∀ y ∈ s, y < x)

#check
  (@HahnSeries.cardSupp_single_mul_le :
    ∀ {Γ : Type u} {R : Type v} [PartialOrder Γ] [AddCommMonoid Γ]
      [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
      (x : HahnSeries Γ R) (a : Γ) (r : R),
        (HahnSeries.single a r * x).cardSupp ≤ x.cardSupp)

#check
  (@HahnSeries.iterateEquiv :
    {Γ : Type u} →
      {Γ' : Type v} →
        {R : Type w} →
          [PartialOrder Γ] →
            [Zero R] →
              [PartialOrder Γ'] →
                HahnSeries Γ (HahnSeries Γ' R) ≃ HahnSeries (Lex (Γ × Γ')) R)

#check
  (@HahnSeries.truncLT :
    {Γ : Type u} →
      {R : Type v} →
        [Zero R] →
          [PartialOrder Γ] →
            [DecidableLT Γ] → Γ → ZeroHom (HahnSeries Γ R) (HahnSeries Γ R))

#check
  (@HahnSeries.embDomain :
    {Γ : Type u} →
      {Γ' : Type v} →
        {R : Type w} →
          [PartialOrder Γ] →
            [Zero R] →
              [PartialOrder Γ'] →
                (Γ ↪o Γ') → HahnSeries Γ R → HahnSeries Γ' R)

#check
  (@HahnSeries.support_embDomain_subset :
    {Γ : Type u} →
      {Γ' : Type v} →
        {R : Type w} →
          [PartialOrder Γ] →
            [Zero R] →
              [PartialOrder Γ'] →
                {f : Γ ↪o Γ'} →
                  {x : HahnSeries Γ R} →
                    (HahnSeries.embDomain f x).support ⊆ f '' x.support)

#check
  (@WithBot.coe_sSup' :
    {α : Type u} →
      [Preorder α] →
        [SupSet α] →
          {s : Set α} →
            s.Nonempty →
              BddAbove s →
                ((sSup s : α) : WithBot α) =
                  sSup ((fun a : α ↦ (a : WithBot α)) '' s))

#check (@SurrealHahnSeries.length : SurrealHahnSeries.{u} → Ordinal.{u})

#check
  (@SurrealHahnSeries.type_support :
    ∀ x : SurrealHahnSeries.{u},
      Ordinal.type (α := x.support) (· > ·) = Ordinal.lift.{u + 1} x.length)

#check (@ZFSet.small_coe : ∀ x : ZFSet.{u}, Small.{u} x)

#check (@ZFSet.coeEquiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u} s})

#check (@ZFSet.range : {α : Type v} → [Small.{u} α] → (α → ZFSet.{u}) → ZFSet.{u})

#check
  (@not_injective_of_ordinal :
    ∀ {α : Type v} [Small.{u} α] (f : Ordinal.{u} → α), ¬Function.Injective f)

#check (@NatOrdinal.toSurreal : NatOrdinal.{u} ↪o Surreal.{u})
