module

public import Mathlib.RingTheory.IntegralClosure.GoingDown

import StacksCore.Tactic.StacksAttribute

/-!
# Criteria for going down

Flat algebras have going down (Mathlib's `Algebra.HasGoingDown.of_flat`) and so do integral
extensions of an integrally closed domain (a Mathlib instance); both already carry their tags
upstream. The minimal polynomial over the fraction field of an integrally closed domain is the
base change of the minimal polynomial over the domain, so its coefficients lie in the domain.
-/

-- The former @[stacks 00HS] declaration is now Mathlib's `Algebra.HasGoingDown.of_flat`, and
-- the former @[stacks 00H8] declaration is now Mathlib's `HasGoingDown` instance for an
-- integral extension of an integrally closed domain. Both already carry their tags upstream.

-- The former @[stacks 00H7] declaration is now the Mathlib theorem.
add_to_stacks 00H7 "the minimal polynomial over the fraction field is the base change of the
minimal polynomial over the integrally closed base, so its coefficients lie in the base"
  minpoly.isIntegrallyClosed_eq_field_fractions
