/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.Basic
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Data.Real.Basic

import ConwayRefinement.Algebra.MvPolynomial.GCDMonoid
import ConwayRefinement.Blueprint
import ConwayRefinement.HahnSeries.Nonpositive.FiniteSupportGCD
import ConwayRefinement.HahnSeries.Nonpositive.PolynomialRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Greatest common divisors in the series ring

The series ring `K((ℝ^{≤0}))` over a field of characteristic zero is a polynomial ring over its
finite-support subring, which is a GCD domain. Hence `K((ℝ^{≤0}))` is a GCD domain; every series is
primal, every irreducible series is prime, and factorisations into irreducibles are unique up to
order and units.
-/

/-!
## Greatest common divisors in the series ring

The series ring `K((ℝ^{≤0}))` is a polynomial ring over its finite-support subring `K_fin`
(`HahnSeries.Nonpositive.exists_mvPolynomial_algEquiv_finiteSupportRing`). LM24, Fact 2.5.2 makes
`K_fin` a GCD domain, and the multivariate Gauss theorem in
`ConwayRefinement.Algebra.MvPolynomial.GCDMonoid` transfers greatest common divisors to the
polynomial ring. The polynomial presentation then transports them to the series ring.
-/

section

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- The nonpositive real series ring over a characteristic-zero field is a GCD domain. The result
is stated through `Nonempty` because `GCDMonoid` contains a choice of gcd operation. -/
@[blueprint "thm:hahn-series-gcd-domain"
  (phase := "Polynomial presentations")
  (title := "Greatest common divisors in $K((\\mathbb R^{\\le 0}))$")
  (statement := /--
    Let $K$ have characteristic $0$. Then $K((\mathbb R^{\le 0}))$ is a GCD domain. As GCD domains
    are pre-Schreier [LM24, Fact 2.5.1] and irreducible elements of a GCD domain are prime, this
    answers the questions of [LM24, §1.2] whether $K((\mathbb R^{\le0}))$ is a pre-Schreier domain,
    and of [LM24, §7] whether all its irreducible elements are prime.
  -/)
  (proof := /--
    By \ref{thm:hahn-series-polynomial-algebra}, $K((\mathbb R^{\le 0}))$ is isomorphic to a
    polynomial ring over $K(\mathbb R^{\le 0})$, which is a GCD domain by
    \ref{fact:finite-support-hahn-gcd}. A polynomial ring in finitely many variables over a GCD
    domain is a GCD domain, by Gauss's lemma and induction on the number of variables. This extends
    to any set of variables: two polynomials lie in the polynomial ring in finitely many of the
    variables, and a greatest common divisor there is one in the full polynomial ring, because a
    common divisor of two polynomials that are not both $0$ involves only variables occurring in
    them.
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

end
end

/-!
## Factorisation in the series ring

Let `K((ℝ^{≤0}))` be the series ring over a field `K` of characteristic zero and `K(ℝ^{≤0})` its
subring of series with finite support [LM24, Not. 2.1.5], written `K_fin` below. The polynomial
presentation identifies `K((ℝ^{≤0}))` with an arbitrary-variable polynomial ring over `K_fin`.
The GCD-domain structure established above therefore
gives Mathlib's `DecompositionMonoid` structure on the series ring. Thus every series is primal,
every irreducible series is prime, and factorisations into irreducibles are unique up to order
and units.
-/

section

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-! ### Pre-Schreier consequences of greatest common divisors -/

/-- `K((ℝ^{≤0}))` is pre-Schreier (Mathlib's `DecompositionMonoid`) because it is a GCD
domain. -/
instance decompositionMonoid : DecompositionMonoid (Nonpositive ℝ K) := by
  letI : Nonempty (GCDMonoid (Nonpositive ℝ K)) := nonemptyGCDMonoid
  infer_instance

/-- Every series is primal in `K((ℝ^{≤0}))`. -/
theorem isPrimal (a : Nonpositive ℝ K) : IsPrimal a :=
  DecompositionMonoid.primal a

/-- Every irreducible series is prime in `K((ℝ^{≤0}))`. -/
theorem prime_of_irreducible {a : Nonpositive ℝ K} (ha : Irreducible a) : Prime a :=
  ha.prime_of_isPrimal (isPrimal a)

/-- Unique factorisation in `K((ℝ^{≤0}))`: two factorisations of a series into irreducibles agree
up to order and units, that is, the two multisets of factors are related by association. -/
theorem factorization_unique {f g : Multiset (Nonpositive ℝ K)} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (hfg : Associated f.prod g.prod) :
    Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx ↦ prime_of_irreducible (hf x hx))
    (fun x hx ↦ prime_of_irreducible (hg x hx)) hfg

end HahnSeries.Nonpositive

end
end
