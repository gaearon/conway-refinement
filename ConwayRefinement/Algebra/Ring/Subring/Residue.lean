/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Algebra.Hom

/-!
# The subring cut out by a residue condition

Let `L` be a field, `A` a commutative `L`-algebra, and `π : A →ₐ[L] L` a retraction of the
structure map. For a subring `S ⊆ L`, the elements of `A` whose residue under `π` lies in `S` form
a subring `π ⁻¹ S`; together with `Frac S`, realised inside `L`, it is the setting of the `D + M`
construction. Primality in `π ⁻¹ S` is decided in
`ConwayRefinement.Algebra.Divisibility.PrimalPreimage`.
-/

public section

variable {L A : Type*} [Field L] [CommRing A] [Algebra L A]

namespace Subring

/-- `π ⁻¹ S`, as a subring of `A`. -/
abbrev residueSubring (π : A →ₐ[L] L) (S : Subring L) : Subring A := S.comap (π : A →+* L)

/-- `Frac S`, realised as a subring of the ambient field `L`. -/
abbrev fracSubring (S : Subring L) : Subring L := (Subfield.closure (S : Set L)).toSubring

variable {π : A →ₐ[L] L} {S : Subring L}

theorem mem_residueSubring {b : A} : b ∈ residueSubring π S ↔ π b ∈ S := (Iff.rfl)

theorem le_fracSubring : S ≤ fracSubring S := fun _ hx ↦ Subfield.subset_closure hx

/-- Every element of `Frac S` has a denominator in `S`. -/
theorem exists_den {x : L} (hx : x ∈ fracSubring S) :
    ∃ s ∈ S, s ≠ 0 ∧ s * x ∈ S := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨1, S.one_mem, one_ne_zero, by simp⟩
  · exact ⟨z, hz, hz0, by rw [mul_div_cancel₀ _ hz0]; exact hy⟩

theorem inv_mem_fracSubring {x : L} (hx : x ∈ fracSubring S) : x⁻¹ ∈ fracSubring S :=
  Subfield.inv_mem _ hx

end Subring
