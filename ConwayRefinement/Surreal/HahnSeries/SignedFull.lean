/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.DomainEquiv
public import ConwayRefinement.HahnSeries.Translation
public import ConwayRefinement.Surreal.HahnSeries.Full

/-!
# Conway normal forms with signed surreal exponents

The order dual in `Surreal.toFullHahnSeries` records the reversal from Conway's `ω` to
LM24's `t = ω⁻¹`. Sending a dual exponent `i` to the ordinary surreal exponent `-i` makes
that reversal explicit and places the normal form in a Hahn field whose exponent group is
`Surreal` itself. This is the orientation in which the surreal Archimedean-stratum assumptions
apply directly.
-/

universe u

public noncomputable section

namespace Surreal

/-- Negation identifies dual Conway exponents with signed ordinary surreal exponents. -/
def dualExponentOrderAddMonoidIso : Surrealᵒᵈ ≃+o Surreal :=
  { toFun := fun x ↦ -x.ofDual
    invFun := fun x ↦ OrderDual.toDual (-x)
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; simp [add_comm]
    map_le_map_iff' := by
      intro x y
      change -x.ofDual ≤ -y.ofDual ↔ y.ofDual ≤ x.ofDual
      exact neg_le_neg_iff }

end Surreal
