/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Data.Real.Basic

import ConwayRefinement.Algebra.MvPolynomial.GCDMonoid
import ConwayRefinement.Blueprint
import ConwayRefinement.HahnSeries.FiniteSupportNormalizedGCD
import ConwayRefinement.HahnSeries.Germ.RealSeries

/-!
# Greatest common divisors in the series ring

The series ring `K((ℝ^{≤0}))` is a polynomial ring over its finite-support subring `K_fin`
(`HahnSeries.Nonpositive.exists_mvPolynomial_algEquiv_finiteSupportRing`). LM24, Fact 2.5.2 makes
`K_fin` a GCD domain, and the multivariate Gauss theorem in
`ConwayRefinement.Algebra.MvPolynomial.GCDMonoid` transfers greatest common divisors to the
polynomial ring. The polynomial presentation then transports them to the series ring.
-/

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- The nonpositive real series ring over a characteristic-zero field is a GCD domain. The result
is stated through `Nonempty` because `GCDMonoid` contains a choice of gcd operation. -/
@[blueprint "thm:hahn-series-gcd-domain"
  (phase := "Primality and factorisation for real exponents")
  (title := "Greatest common divisors in $K((\\mathbb R^{\\le 0}))$")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  The ring
    $K((\mathbb R^{\le 0}))$ of generalised power series with nonpositive real
    exponents is a GCD domain.
  -/)
  (proof := /--
    By \ref{thm:hahn-series-polynomial-algebra},
    $K((\mathbb R^{\le 0}))$ is a polynomial ring over the finite-support
    subring $K(\mathbb R^{\le 0})$. By \ref{fact:finite-support-hahn-gcd},
    the coefficient ring is a GCD domain. Normalising each nonzero greatest
    common divisor by the coefficient of $t^{\sup(p)}$ supplies the hypothesis
    required by \ref{lem:multivariate-polynomial-gcd}. Transport the
    resulting gcd operation across the isomorphism.
  -/)
  (highlight)]
theorem nonemptyGCDMonoid : Nonempty (GCDMonoid (Nonpositive ℝ K)) := by
  obtain ⟨ι, ⟨e⟩⟩ := exists_mvPolynomial_algEquiv_finiteSupportRing.{v, 0} (K := K)
  letI : Nonempty (NormalizedGCDMonoid (FiniteSupportRing (G := ℝ) (K := K))) :=
    nonemptyNormalizedGCDMonoid_finiteSupport
  letI : Nonempty (GCDMonoid (MvPolynomial ι (FiniteSupportRing (G := ℝ) (K := K)))) :=
    MvPolynomial.nonemptyGCDMonoid
  exact MulEquiv.nonemptyGCDMonoid e.symm.toMulEquiv

end HahnSeries.Nonpositive
