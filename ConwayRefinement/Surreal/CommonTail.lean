/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Algebra.Order.Module.ConvexQuotientSplitting
public import ConwayRefinement.Surreal.CutFilling
public import ConwayRefinement.Surreal.RealModule
public import ConwayRefinement.HahnSeries.Nonpositive.ArchimedeanClasses
public import ConwayRefinement.Topology.Order.OrderedAddGroup
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

import ConwayRefinement.Blueprint

/-!
# Common-tail quotients of the surreal numbers

For a family of finite Archimedean classes, its common tail is a rational subspace of the
surreals. Quotienting by that subspace gives the usual ordered tail quotient together with its
native rational-vector-space structure. At a nonempty limit family, the quotient is Cauchy
complete for its additive uniformity: the canonical representatives of the family are a small
positive coinitial family, and surreal simplicity fills every cut indexed by that family.

This presentation is used when a small closed rational subspace of the tail quotient must be
formed. Its additive subgroup is exactly the tail kernel used by the older additive presentation.
-/

open Set

universe u

public noncomputable section

namespace Surreal

/-- The quotient by the rational subspace underlying a family of Archimedean tails. -/
abbrev RationalTailQuotient (T : Set (FiniteArchimedeanClass Surreal.{u})) :=
  Surreal.{u} ⧸ FiniteArchimedeanClass.tailSubmodule ℚ T

noncomputable instance rationalTailQuotientLinearOrder
    (T : Set (FiniteArchimedeanClass Surreal.{u})) : LinearOrder (RationalTailQuotient T) :=
  ConvexQuotient.instLinearOrder (H :=
    (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup)

instance rationalTailQuotientIsOrderedAddMonoid
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    IsOrderedAddMonoid (RationalTailQuotient T) :=
  ConvexQuotient.instIsOrderedAddMonoid (H :=
    (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup)

instance rationalTailQuotientPosSMulMono
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    PosSMulMono ℚ (RationalTailQuotient T) where
  smul_le_smul_of_nonneg_left q hq x y hxy := by
    change ∃ a b : Surreal.{u}, Submodule.Quotient.mk a = x ∧
      Submodule.Quotient.mk b = y ∧ a ≤ b at hxy
    obtain ⟨a, b, ha, hb, hab⟩ := hxy
    change ∃ a b : Surreal.{u}, Submodule.Quotient.mk a = q • x ∧
      Submodule.Quotient.mk b = q • y ∧ a ≤ b
    refine ⟨q • a, q • b, ?_, ?_, smul_le_smul_of_nonneg_left hab hq⟩
    · simpa only [Submodule.Quotient.mk_smul] using congrArg (q • ·) ha
    · simpa only [Submodule.Quotient.mk_smul] using congrArg (q • ·) hb

instance rationalTailQuotientPosSMulStrictMono
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    PosSMulStrictMono ℚ (RationalTailQuotient T) :=
  PosSMulMono.toPosSMulStrictMono

noncomputable instance rationalTailQuotientTopologicalSpace
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    TopologicalSpace (RationalTailQuotient T) :=
  Preorder.topology (RationalTailQuotient T)

instance rationalTailQuotientOrderTopology
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    OrderTopology (RationalTailQuotient T) :=
  ⟨rfl⟩

instance rationalTailQuotientDenselyOrdered
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    DenselyOrdered (RationalTailQuotient T) := by
  constructor
  intro a b hab
  refine ⟨(2 : ℚ)⁻¹ • (a + b), ?_, ?_⟩
  · calc
      a = (2 : ℚ)⁻¹ • (a + a) := by rw [smul_add, ← add_smul]; norm_num
      _ < (2 : ℚ)⁻¹ • (a + b) :=
        smul_lt_smul_of_pos_left
          (add_lt_add_left hab a |>.trans_eq (add_comm _ _)) (by norm_num)
  · calc
      (2 : ℚ)⁻¹ • (a + b) < (2 : ℚ)⁻¹ • (b + b) :=
        smul_lt_smul_of_pos_left
          (by simpa [add_comm] using (add_lt_add_left hab b)) (by norm_num)
      _ = b := by rw [smul_add, ← add_smul]; norm_num

instance rationalTailQuotientIsTopologicalAddGroup
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    IsTopologicalAddGroup (RationalTailQuotient T) where
  toContinuousAdd := continuousAdd_of_orderTopology (RationalTailQuotient T)
  toContinuousNeg := continuousNeg_of_orderTopology (RationalTailQuotient T)

noncomputable instance rationalTailQuotientUniformSpace
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    UniformSpace (RationalTailQuotient T) :=
  IsTopologicalAddGroup.rightUniformSpace (RationalTailQuotient T)

instance rationalTailQuotientIsUniformAddGroup
    (T : Set (FiniteArchimedeanClass Surreal.{u})) :
    IsUniformAddGroup (RationalTailQuotient T) :=
  isUniformAddGroup_of_addCommGroup

/-- Canonical positive scales in a rational tail quotient, indexed by a small copy of the
class family. -/
def rationalTailQuotientScale
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (i : Shrink.{u} T) :
    RationalTailQuotient T :=
  Submodule.Quotient.mk
    (FiniteArchimedeanClass.positiveRepresentative ((equivShrink T).symm i).1)

/-- At a limit family, every canonical tail-quotient scale is positive. -/
theorem rationalTailQuotientScale_pos
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) (i : Shrink.{u} T) :
    0 < rationalTailQuotientScale T i := by
  rw [← Submodule.Quotient.mk_zero]
  apply ConvexQuotient.mk_lt_mk_iff.mpr
  constructor
  · exact FiniteArchimedeanClass.positiveRepresentative_pos _
  · intro hmem
    have htail : FiniteArchimedeanClass.positiveRepresentative ((equivShrink T).symm i).1 ∈
        FiniteArchimedeanClass.tailKernel T := by
      rw [← FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T]
      simpa using hmem
    exact FiniteArchimedeanClass.positiveRepresentative_not_mem_tailKernel hT _ htail

/-- The canonical scales are coinitial among the positive elements of the tail quotient. -/
theorem exists_rationalTailQuotientScale_le
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    {x : RationalTailQuotient T} (hx : 0 < x) :
    ∃ i : Shrink.{u} T, rationalTailQuotientScale T i ≤ x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hxq : (Submodule.Quotient.mk (0 : Surreal.{u}) : RationalTailQuotient T) <
        (Submodule.Quotient.mk x : RationalTailQuotient T) := by
      simpa using hx
    have hx0 : 0 < x := ConvexQuotient.lt_of_mk_lt_mk hxq
    have hxH : x ∉ FiniteArchimedeanClass.tailKernel T := by
      intro hmem
      apply (ConvexQuotient.mk_lt_mk_iff.mp hxq).2
      have : x ∈ (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup := by
        simpa only [FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T] using hmem
      simpa using this
    rw [FiniteArchimedeanClass.mem_tailKernel_iff] at hxH
    push Not at hxH
    obtain ⟨c, hxc⟩ := hxH
    refine ⟨equivShrink T c, ConvexQuotient.mk_le_mk ?_⟩
    apply (ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ hx0.le).le
    rw [FiniteArchimedeanClass.mk_positiveRepresentative]
    simpa using hxc

/-- The positive representatives of a limit family give a small coinitial family in its rational
tail quotient. -/
theorem rationalTailQuotientScale_pos_and_coinitial
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) :
    (∀ i : Shrink.{u} T, 0 < rationalTailQuotientScale T i) ∧
      ∀ x : RationalTailQuotient T, 0 < x →
        ∃ i : Shrink.{u} T, rationalTailQuotientScale T i ≤ x :=
  ⟨rationalTailQuotientScale_pos T hT, fun _ hx ↦ exists_rationalTailQuotientScale_le T hx⟩

/-- A rational tail quotient at a nonempty limit family is Cauchy complete for its additive
uniformity. -/
@[blueprint "lem:surreal-common-tail-quotient-complete"
  (phase := "Surreal numbers and omnific integers")
  (title := "Cauchy completeness of $\\mathbf{No}/\\mathbf{No}_T$")
  (statement := /--
    Let $T$ be a nonempty set of fewer than $\kappa$ nonzero Archimedean classes of $\mathbf{No}$,
    without $\prec$-least element. Then $\mathbf{No}/\mathbf{No}_T$ is Cauchy complete for its order
    topology and group uniformity.
  -/)
  (proof := /--
    For $\sigma\in T$ let $\varepsilon_\sigma$ be the image in $\mathbf{No}/\mathbf{No}_T$ of a
    positive element of class $\sigma$. It is positive, because some $\tau\in T$ has
    $\tau\prec\sigma$, so that element is not in $\mathbf{No}_T$. These images are coinitial among
    positive elements: a positive element outside $\mathbf{No}_T$ has class $\succ\sigma$ for some
    $\sigma\in T$. Halving supplies the scales $\varepsilon_\sigma/2$ required by
    \ref{lem:complete-of-coinitial-scales-and-cut-filling}. To fill a cut between two families in
    $\mathbf{No}/\mathbf{No}_T$ indexed by $T$, lift them to $\mathbf{No}$. Strict inequalities in
    the quotient by a convex subgroup lift to strict inequalities between representatives, and the
    lifted families are small since $T$ is. So \ref{thm:surreal-simplicity-small-cuts} gives a
    surreal number between the lifts, and its image lies between the original families.
  -/)]
theorem completeSpace_rationalTailQuotient
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T] [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) : CompleteSpace (RationalTailQuotient T) := by
  letI : Nonempty (Shrink.{u} T) := ⟨equivShrink T (Classical.arbitrary T)⟩
  obtain ⟨hpos, hcoinitial⟩ := rationalTailQuotientScale_pos_and_coinitial T hT
  apply completeSpace_of_coinitial_of_exists_half (rationalTailQuotientScale T)
  · exact hpos
  · exact hcoinitial
  · intro x hx
    exact ⟨(2 : ℚ)⁻¹ • x, smul_pos (by norm_num) hx, by
      rw [← add_smul]
      norm_num⟩
  · exact FillsCuts.of_surjective (Submodule.Quotient.mk_surjective _)
      (fun _ _ h ↦ ConvexQuotient.mk_le_mk h)
      (fun _ _ h ↦ ConvexQuotient.lt_of_mk_lt_mk h) Surreal.fillsCuts

end Surreal
