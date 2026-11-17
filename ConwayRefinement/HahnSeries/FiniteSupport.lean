/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp

import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.HahnSeries.Cardinal

/-!
# Finite-support Hahn series

This file packages finite-support Hahn series as the specialization at `Cardinal.aleph0` of
Mathlib's cardinal-bounded Hahn-series subring. It also pulls that subring back to nonpositive
Hahn series. The latter is the ring denoted by `K(G^{≤ 0})` in LM24.
-/

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}

section HahnSeries

variable [PartialOrder G] [AddCommMonoid G] [IsOrderedCancelAddMonoid G] [Ring K]

/-- The subring of Hahn series with finite support. -/
def finiteSupportSubring : Subring K⟦G⟧ :=
  let _ : Fact (Cardinal.aleph0 ≤ Cardinal.aleph0) := ⟨le_rfl⟩
  HahnSeries.cardSuppLTSubring G K Cardinal.aleph0

/-- Membership in the finite-support subring is finiteness of the Hahn-series support. -/
@[simp]
theorem mem_finiteSupportSubring_iff (b : K⟦G⟧) :
    b ∈ (finiteSupportSubring : Subring K⟦G⟧) ↔ b.support.Finite := by
  letI : Fact (Cardinal.aleph0 ≤ Cardinal.aleph0) := ⟨le_rfl⟩
  rw [finiteSupportSubring, HahnSeries.mem_cardSuppLTSubring, HahnSeries.cardSupp]
  exact Cardinal.lt_aleph0_iff_set_finite

end HahnSeries

namespace Nonpositive

variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Ring K]

/-- The subring of nonpositive Hahn series with finite support. -/
def finiteSupportSubring : Subring (Nonpositive G K) :=
  HahnSeries.finiteSupportSubring.comap (HahnSeries.nonpositiveSubring G K).subtype

/-- The type of finite-support nonpositive Hahn series. -/
abbrev FiniteSupportRing :=
  (finiteSupportSubring : Subring (Nonpositive G K))

/-! The structures on the finite-support ring, named here rather than rebuilt at each use.
`Zero` is the one that matters: it is asked for by every comparison against `0`, and resolving it
through the `Subring` membership classes is not cheap. -/

instance : Zero (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : One (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : Semiring (FiniteSupportRing (G := G) (K := K)) := inferInstance

/-- Membership in the nonpositive finite-support subring is finiteness of the underlying support.
-/
@[simp]
theorem mem_finiteSupportSubring_iff (b : Nonpositive G K) :
    b ∈ (finiteSupportSubring : Subring (Nonpositive G K)) ↔
      (b : K⟦G⟧).support.Finite := by
  rw [finiteSupportSubring, Subring.mem_comap]
  rw [HahnSeries.mem_finiteSupportSubring_iff]
  simp only [Subring.subtype_apply]

end Nonpositive

namespace Nonpositive

variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [CommRing K]

instance : CommRing (FiniteSupportRing (G := G) (K := K)) := inferInstance

/-- The coefficient field embeds in the finite-support ring as constant Hahn series. -/
def finiteSupportScalarHom :
    K →+* (finiteSupportSubring : Subring (Nonpositive G K)) :=
  (C : K →+* Nonpositive G K).codRestrict finiteSupportSubring fun k ↦ by
    rw [mem_finiteSupportSubring_iff, coe_C]
    exact Set.Finite.subset (Set.finite_singleton (0 : G))
      HahnSeries.support_single_subset

/-- The scalar map is the constant-series embedding on underlying Hahn series. -/
@[simp]
theorem coe_finiteSupportScalarHom (k : K) :
    ((((finiteSupportScalarHom (G := G) k :
        (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧)) = HahnSeries.C k :=
  coe_C k

end Nonpositive

end HahnSeries
