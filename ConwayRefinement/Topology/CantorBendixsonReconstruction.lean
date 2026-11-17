/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Topology.CantorBendixsonRank
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.DiscreteSubset

import Mathlib.Topology.Maps.Basic

/-!
# Locality of Cantor–Bendixson stages

Homeomorphisms preserve derivative stages and point ranks. Transfinite derivatives agree locally
whenever the original closed sets agree on an open set, and so do Cantor–Bendixson point ranks. For
a closed well-ordered support, the points of exact rank `a` are dense in its `a`-th derivative.

The statements use the given ambient topology and hold at arbitrary ordinal cofinalities.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u v w

/-- Homeomorphisms preserve every transfinite derivative stage of a closed set. -/
theorem Homeomorph.mem_cantorBendixson_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]
    (e : X ≃ₜ Y) (s : Closeds X) (t : Closeds Y) (he : e '' (s : Set X) = (t : Set Y))
    (x : X) (o : Ordinal.{v}) :
    e x ∈ (t.cantorBendixson o : Set Y) ↔ x ∈ (s.cantorBendixson o : Set X) := by
  have hf (y : Y) : (e ⁻¹' {y}).Finite := (finite_singleton y).preimage e.injective.injOn
  have hg (x : X) : (e.symm ⁻¹' {x}).Finite :=
    (finite_singleton x).preimage e.symm.injective.injOn
  have ht' : (⟨e '' (s : Set X), e.isClosedMap _ s.isClosed⟩ : Closeds Y) = t :=
    SetLike.coe_injective he
  have he' : e.symm '' (t : Set Y) = (s : Set X) := by
    rw [← he, ← Set.image_comp]
    simp
  have hs' : (⟨e.symm '' (t : Set Y), e.symm.isClosedMap _ t.isClosed⟩ : Closeds X) = s :=
    SetLike.coe_injective he'
  have hst := e.isClosedMap.cantorBendixson_image_subset hf s o
  have hts := e.symm.isClosedMap.cantorBendixson_image_subset hg t o
  rw [ht'] at hst
  rw [hs'] at hts
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hst hx
    exact e.injective hyx ▸ hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hts hx
    have hxy : y = e x := by simpa using congrArg e hyx
    exact hxy ▸ hy

/-- Restricting a set to an open set preserves its derived set inside that open set. -/
theorem IsOpen.derivedSet_inter_eq {X : Type*} [TopologicalSpace X] {U s : Set X}
    (hU : IsOpen U) : derivedSet (s ∩ U) ∩ U = derivedSet s ∩ U := by
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    exact ⟨derivedSet_mono _ _ inter_subset_left hx, hxU⟩
  · rintro ⟨hx, hxU⟩
    refine ⟨mem_derivedSet.mpr (accPt_iff_frequently.mpr ?_), hxU⟩
    exact ((accPt_iff_frequently.mp (mem_derivedSet.mp hx)).and_eventually
      (hU.mem_nhds hxU)).mono fun y hy ↦ ⟨hy.1.1, hy.1.2, hy.2⟩

/-- Sets agreeing on an open set have closures agreeing there. -/
theorem IsOpen.closure_congr {X : Type*} [TopologicalSpace X] {U s t : Set X}
    (hU : IsOpen U) (hst : s ∩ U = t ∩ U) : closure s ∩ U = closure t ∩ U := by
  ext x
  constructor
  · intro hx
    have hm := hU.closure_inter hx
    rw [hst] at hm
    exact ⟨closure_mono inter_subset_left hm, hx.2⟩
  · intro hx
    have hm := hU.closure_inter hx
    rw [← hst] at hm
    exact ⟨closure_mono inter_subset_left hm, hx.2⟩

/-- Sets agreeing on an open set have derived sets agreeing there. -/
theorem IsOpen.derivedSet_congr {X : Type*} [TopologicalSpace X] {U s t : Set X}
    (hU : IsOpen U) (hst : s ∩ U = t ∩ U) : derivedSet s ∩ U = derivedSet t ∩ U := by
  rw [← hU.derivedSet_inter_eq (s := s), hst, hU.derivedSet_inter_eq]

namespace TopologicalSpace.Closeds

variable {X : Type u} [TopologicalSpace X] [T1Space X]

/-- Closed sets agreeing on an open set have every derivative stage agreeing there. -/
theorem cantorBendixson_congr_on_open (s t : Closeds X) {U : Set X} (hU : IsOpen U)
    (hst : (s : Set X) ∩ U = (t : Set X) ∩ U) (o : Ordinal.{v}) :
    (s.cantorBendixson o : Set X) ∩ U = (t.cantorBendixson o : Set X) ∩ U := by
  induction o using Ordinal.limitRecOn with
  | zero => simpa using hst
  | add_one o ih =>
    simpa only [cantorBendixson_add_one, coe_derived] using hU.derivedSet_congr ih
  | limit o ho ih =>
    rw [cantorBendixson_limit _ _ ho, cantorBendixson_limit _ _ ho]
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨Closeds.mem_iInf.mpr (fun i ↦ ?_), hxU⟩
      exact ((Set.ext_iff.mp (ih i.1 i.2) x).mp
        ⟨Closeds.mem_iInf.mp hx i, hxU⟩).1
    · rintro ⟨hx, hxU⟩
      refine ⟨Closeds.mem_iInf.mpr (fun i ↦ ?_), hxU⟩
      exact ((Set.ext_iff.mp (ih i.1 i.2) x).mpr
        ⟨Closeds.mem_iInf.mp hx i, hxU⟩).1

variable [LinearOrder X] [OrderTopology X]

/-- Point rank depends only on the closed set in a neighborhood of the point. -/
theorem cantorBendixsonRank_congr_on_open (s t : Closeds X)
    (hs : (s : Set X).IsPWO) (ht : (t : Set X).IsPWO)
    {U : Set X} (hU : IsOpen U) (hst : (s : Set X) ∩ U = (t : Set X) ∩ U)
    {x : X} (hx : x ∈ U) : s.cantorBendixsonRank hs x = t.cantorBendixsonRank ht x := by
  apply le_antisymm
  · apply s.cantorBendixsonRank_le_of_notMem hs x
    intro hm
    have he := s.cantorBendixson_congr_on_open t hU hst (t.cantorBendixsonRank ht x + 1)
    exact t.notMem_cantorBendixson_rank_add_one ht x ((Set.ext_iff.mp he x).mp ⟨hm, hx⟩).1
  · apply t.cantorBendixsonRank_le_of_notMem ht x
    intro hm
    have he := s.cantorBendixson_congr_on_open t hU hst (s.cantorBendixsonRank hs x + 1)
    exact s.notMem_cantorBendixson_rank_add_one hs x ((Set.ext_iff.mp he x).mpr ⟨hm, hx⟩).1

end TopologicalSpace.Closeds

/-- Homeomorphisms carrying one closed well-ordered support onto another preserve point ranks. -/
theorem Homeomorph.cantorBendixsonRank_eq {X Y : Type u}
    [LinearOrder X] [LinearOrder Y] [TopologicalSpace X] [TopologicalSpace Y]
    [OrderTopology X] [OrderTopology Y] (e : X ≃ₜ Y)
    (s : Closeds X) (t : Closeds Y) (hs : (s : Set X).IsPWO) (ht : (t : Set Y).IsPWO)
    (he : e '' (s : Set X) = (t : Set Y)) (x : X) :
    t.cantorBendixsonRank ht (e x) = s.cantorBendixsonRank hs x := by
  apply le_antisymm
  · apply t.cantorBendixsonRank_le_of_notMem ht (e x)
    intro hx
    exact s.notMem_cantorBendixson_rank_add_one hs x
      ((e.mem_cantorBendixson_iff s t he x _).mp hx)
  · apply s.cantorBendixsonRank_le_of_notMem hs x
    intro hx
    exact t.notMem_cantorBendixson_rank_add_one ht (e x)
      ((e.mem_cantorBendixson_iff s t he x _).mpr hx)
