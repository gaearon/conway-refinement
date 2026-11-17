/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Topology.CantorBendixson.Basic

public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.Order.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Cantor–Bendixson point ranks of well-ordered supports

For a closed well-ordered subset of a linearly ordered space, each point disappears at a
successor derivative stage. The ordinal index of the point in the well-ordered support gives
a bound, because a sufficiently small neighborhood contains no larger support point.

The point rank is the least ordinal whose successor derivative omits the point. On the support,
membership in stage `o` is equivalent to `o` being at most the point rank. Points outside the
support have rank zero. All derivatives use the given ambient topology.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u

variable {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]

/-- A well-ordered support has no points immediately to the right of any given ambient point. -/
theorem Set.IsPWO.eventually_le {s : Set X} (hs : s.IsPWO) (x : X) :
    ∀ᶠ y in 𝓝 x, y ∈ s → y ≤ x := by
  let v := s ∩ Ioi x
  by_cases hn : v.Nonempty
  · have hv : v.IsWF := hs.isWF.mono inter_subset_left
    let m := hv.min hn
    have hm : m ∈ v := hv.min_mem hn
    filter_upwards [Iio_mem_nhds hm.2] with y hy hys
    exact le_of_not_gt fun hxy ↦ (not_lt_of_ge (hv.min_le hn ⟨hys, hxy⟩)) hy
  · apply Filter.Eventually.of_forall
    intro y hy
    exact le_of_not_gt fun hxy ↦ hn ⟨y, hy, hxy⟩

namespace TopologicalSpace.Closeds

/-- Every ambient point is absent from some successor derivative of a closed well-ordered set. -/
theorem exists_notMem_cantorBendixson_succ (s : Closeds X) (hs : (s : Set X).IsPWO) (x : X) :
    ∃ o : Ordinal.{u}, x ∉ (s.cantorBendixson (o + 1) : Set X) := by
  classical
  letI : WellFoundedLT (s : Set X) := ⟨hs.isWF⟩
  let r (y : X) : Ordinal.{u} :=
    if h : y ∈ s then Ordinal.typein (α := (s : Set X)) (· < ·) ⟨y, h⟩ else 0
  have hr : ∀ y ∈ s, ∀ᶠ z in 𝓝 y, z ∈ s → z ≠ y → r z < r y := by
    intro y hy
    filter_upwards [hs.eventually_le y] with z hz hzs hzy
    simp only [r, dif_pos hzs, dif_pos hy, Ordinal.typein_lt_typein]
    exact (lt_of_le_of_ne (hz hzs) hzy : z < y)
  refine ⟨r x, fun hx ↦ ?_⟩
  exact (not_le_of_gt (Order.lt_succ (r x)))
    (s.cantorBendixson_subset_of_locally_lt r hr (r x + 1) hx)

/-- The least ordinal whose successor derivative omits the point; zero outside the set. -/
def cantorBendixsonRank (s : Closeds X) (hs : (s : Set X).IsPWO) (x : X) : Ordinal.{u} :=
  wellFounded_lt.min {o : Ordinal.{u} | x ∉ (s.cantorBendixson (o + 1) : Set X)}
    (s.exists_notMem_cantorBendixson_succ hs x)

/-- The successor of the point rank removes that point. -/
theorem notMem_cantorBendixson_rank_add_one (s : Closeds X)
    (hs : (s : Set X).IsPWO) (x : X) :
    x ∉ (s.cantorBendixson (s.cantorBendixsonRank hs x + 1) : Set X) := by
  exact wellFounded_lt.min_mem
    {o : Ordinal.{u} | x ∉ (s.cantorBendixson (o + 1) : Set X)}
    (s.exists_notMem_cantorBendixson_succ hs x)

/-- Any successor stage omitting a point gives an upper bound on its rank. -/
theorem cantorBendixsonRank_le_of_notMem (s : Closeds X) (hs : (s : Set X).IsPWO)
    (x : X) {o : Ordinal.{u}} (ho : x ∉ (s.cantorBendixson (o + 1) : Set X)) :
    s.cantorBendixsonRank hs x ≤ o := by
  exact wellFounded_lt.min_le ho

/-- A point belongs to a derivative exactly when it lies in the set and its rank is high enough. -/
theorem mem_cantorBendixson_iff (s : Closeds X) (hs : (s : Set X).IsPWO)
    (x : X) (o : Ordinal.{u}) :
    x ∈ (s.cantorBendixson o : Set X) ↔ x ∈ s ∧ o ≤ s.cantorBendixsonRank hs x := by
  constructor
  · intro hx
    refine ⟨s.cantorBendixson_le o hx, ?_⟩
    by_contra! ho
    exact s.notMem_cantorBendixson_rank_add_one hs x
      (s.cantorBendixson_antitone (Order.succ_le_of_lt ho) hx)
  · rintro ⟨hx, ho⟩
    induction o using Ordinal.limitRecOn with
    | zero => simpa using hx
    | add_one o ih =>
      by_contra hn
      exact (not_le_of_gt ((Order.lt_succ o).trans_le ho))
        (s.cantorBendixsonRank_le_of_notMem hs x hn)
    | limit o hlo ih =>
      rw [cantorBendixson_limit _ _ hlo]
      exact mem_iInf.mpr fun i ↦ ih i.1 i.2 (i.2.le.trans ho)

/-- All other sufficiently nearby support points have strictly smaller rank. -/
theorem cantorBendixsonRank_locally_lt (s : Closeds X) (hs : (s : Set X).IsPWO)
    (x : X) : ∀ᶠ y in 𝓝 x, y ∈ s → y ≠ x →
      s.cantorBendixsonRank hs y < s.cantorBendixsonRank hs x := by
  have hn := s.notMem_cantorBendixson_rank_add_one hs x
  rw [cantorBendixson_add_one, coe_derived, mem_derivedSet, accPt_iff_frequently,
    Filter.not_frequently] at hn
  filter_upwards [hn] with y hy hys hyx
  by_contra! hle
  exact hy ⟨hyx, (s.mem_cantorBendixson_iff hs y _).mpr ⟨hys, hle⟩⟩

end TopologicalSpace.Closeds
