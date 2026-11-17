/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.CantorBendixson.Basic

public import ConwayRefinement.HahnSeries.Truncation

public import Mathlib.Topology.Algebra.Group.Defs
import ConwayRefinement.Topology.CantorBendixson.Locality
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Cantor–Bendixson ranks under translated truncation

A weak lower truncation preserves the closed support locally at its cutoff, since a well-ordered
support has a gap immediately to the right. Translation preserves point ranks. Consequently,
the value of the translated weak truncation at `c` reads the original point rank at `c`,
with value zero exactly when `c` is outside the original closed support.

The value depends only on the support in a neighbourhood of zero. Truncation uses `i ≤ c`,
retaining the cutoff coefficient, and translation by `-c` sends that exponent to zero. No
multiplication identity is assumed.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type v} [LinearOrder G] [TopologicalSpace G]
  [OrderTopology G]

section Zero

variable [Zero R]

/-- Weak lower truncation preserves the closed support in a neighborhood of its cutoff. -/
theorem closedSupport_truncLE_locally_eq (b : HahnSeries G R) (c : G) :
    ∃ U : Set G, IsOpen U ∧ c ∈ U ∧
      ((truncLE c b).closedSupport : Set G) ∩ U = (b.closedSupport : Set G) ∩ U := by
  obtain ⟨U, hU, hUo, hcU⟩ := mem_nhds_iff.mp (b.isPWO_support.eventually_le c)
  refine ⟨U, hUo, hcU, ?_⟩
  rw [coe_closedSupport, coe_closedSupport]
  apply hUo.closure_congr
  rw [support_truncLE]
  ext y
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hU h.2 h.1⟩, h.2⟩⟩

/-- Weak lower truncation preserves the Cantor–Bendixson rank at its cutoff. -/
theorem cantorBendixsonRank_truncLE (b : HahnSeries G R) (c : G) :
    (truncLE c b).cantorBendixsonRank c = b.cantorBendixsonRank c := by
  obtain ⟨U, hU, hc, he⟩ := b.closedSupport_truncLE_locally_eq c
  rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
  exact (truncLE c b).closedSupport.cantorBendixsonRank_congr_on_open b.closedSupport
    (truncLE c b).closedSupport_isPWO b.closedSupport_isPWO hU he hc

/-- The cutoff belongs to the truncated closed support exactly when it belongs to the original. -/
theorem mem_closedSupport_truncLE (b : HahnSeries G R) (c : G) :
    c ∈ (truncLE c b).closedSupport ↔ c ∈ b.closedSupport := by
  obtain ⟨U, _, hc, he⟩ := b.closedSupport_truncLE_locally_eq c
  exact ⟨fun h ↦ ((Set.ext_iff.mp he c).mp ⟨h, hc⟩).1,
    fun h ↦ ((Set.ext_iff.mp he c).mpr ⟨h, hc⟩).1⟩

/-- The Cantor–Bendixson value depends only on the support in a neighbourhood of zero. -/
theorem cantorBendixsonValue_congr_of_support_inter_eq [Zero G] {b d : HahnSeries G R}
    {U : Set G} (hU : IsOpen U) (h0 : (0 : G) ∈ U) (h : b.support ∩ U = d.support ∩ U) :
    b.cantorBendixsonValue = d.cantorBendixsonValue := by
  have he : (b.closedSupport : Set G) ∩ U = (d.closedSupport : Set G) ∩ U := by
    rw [coe_closedSupport, coe_closedSupport]; exact hU.closure_congr h
  have hr : b.cantorBendixsonRank 0 = d.cantorBendixsonRank 0 := by
    rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
    exact b.closedSupport.cantorBendixsonRank_congr_on_open d.closedSupport
      b.closedSupport_isPWO d.closedSupport_isPWO hU he h0
  have hm : 0 ∈ closure b.support ↔ 0 ∈ closure d.support := by
    have h' := Set.ext_iff.mp he 0
    simp only [coe_closedSupport, Set.mem_inter_iff, and_iff_left h0] at h'
    exact h'
  by_cases hb : 0 ∈ closure b.support
  · rw [b.cantorBendixsonValue_of_mem hb, d.cantorBendixsonValue_of_mem (hm.mp hb), hr]
  · rw [b.cantorBendixsonValue_of_notMem hb, d.cantorBendixsonValue_of_notMem (mt hm.mpr hb)]

end Zero

section Translation

variable [AddCommGroup G] [IsOrderedAddMonoid G] [IsTopologicalAddGroup G] [AddMonoid R]

omit [TopologicalSpace G] [OrderTopology G] [IsTopologicalAddGroup G] in
/-- A translated weak lower truncation always has nonpositive support. -/
theorem support_translated_truncLE (b : HahnSeries G R) (c : G) :
    (translate (-c) (truncLE c b)).support ⊆ Iic 0 := by
  rw [support_translate]
  rintro x ⟨y, hy, rfl⟩
  rw [support_truncLE] at hy
  simpa only [mem_Iic, neg_add_cancel] using add_le_add_right hy.2 (-c)

/-- Translating the exponents and the target point together preserves Cantor–Bendixson rank. -/
theorem cantorBendixsonRank_translate (b : HahnSeries G R) (a x : G) :
    (translate a b).cantorBendixsonRank (a + x) = b.cantorBendixsonRank x := by
  rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
  apply (Homeomorph.addLeft a).cantorBendixsonRank_eq b.closedSupport (translate a b).closedSupport
    b.closedSupport_isPWO (translate a b).closedSupport_isPWO
  rw [coe_closedSupport, coe_closedSupport, support_translate]
  exact (Homeomorph.addLeft a).image_closure _

omit [OrderTopology G] in
/-- Translation transports membership in the closed support. -/
theorem mem_closedSupport_translate (b : HahnSeries G R) (a x : G) :
    a + x ∈ (translate a b).closedSupport ↔ x ∈ b.closedSupport := by
  rw [mem_closedSupport, mem_closedSupport, support_translate]
  have he : (a + ·) '' closure b.support = closure ((a + ·) '' b.support) :=
    (Homeomorph.addLeft a).image_closure b.support
  rw [← he]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (add_left_cancel he : y = x) ▸ hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

/-- The rank at zero after translated weak truncation is the original rank at the cutoff. -/
theorem cantorBendixsonRank_translated_truncLE (b : HahnSeries G R) (c : G) :
    (translate (-c) (truncLE c b)).cantorBendixsonRank 0 = b.cantorBendixsonRank c := by
  simpa only [neg_add_cancel] using
    ((truncLE c b).cantorBendixsonRank_translate (-c) c).trans (b.cantorBendixsonRank_truncLE c)

open Classical in
/-- The translated weak truncation value reads the Cantor–Bendixson rank at the cutoff. -/
theorem cantorBendixsonValue_translated_truncLE (b : HahnSeries G R) (c : G) :
    (translate (-c) (truncLE c b)).cantorBendixsonValue =
      if c ∈ b.closedSupport then Ordinal.omega0 ^ b.cantorBendixsonRank c else 0 := by
  have hm : (0 : G) ∈ (translate (-c) (truncLE c b)).closedSupport ↔ c ∈ b.closedSupport := by
    simpa only [neg_add_cancel] using
      ((truncLE c b).mem_closedSupport_translate (-c) c).trans (b.mem_closedSupport_truncLE c)
  by_cases hc : c ∈ b.closedSupport
  · rw [if_pos hc, cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp (hm.mpr hc)),
      cantorBendixsonRank_translated_truncLE]
  · rw [if_neg hc]
    apply cantorBendixsonValue_of_notMem
    intro hh
    exact hc (hm.mp ((mem_closedSupport _ _).mpr hh))

/-- Nearby proper translated truncations have strictly smaller value when the value is nonzero. -/
theorem eventually_value_translated_truncLE_lt (b : HahnSeries G R)
    (hb : b.cantorBendixsonValue ≠ 0) :
    ∀ᶠ c in 𝓝 (0 : G), c ≠ 0 →
      (translate (-c) (truncLE c b)).cantorBendixsonValue < b.cantorBendixsonValue := by
  classical
  have hb0 : 0 ∈ closure b.support :=
    not_not.mp (mt (b.cantorBendixsonValue_eq_zero_iff).mpr hb)
  filter_upwards [b.closedSupport.cantorBendixsonRank_locally_lt b.closedSupport_isPWO 0]
    with c hc hne
  rw [b.cantorBendixsonValue_translated_truncLE, b.cantorBendixsonValue_of_mem hb0]
  by_cases hmem : c ∈ b.closedSupport
  · rw [if_pos hmem]
    apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    simpa only [cantorBendixsonRank_eq] using hc hmem hne
  · rw [if_neg hmem]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos

end Translation

end HahnSeries
