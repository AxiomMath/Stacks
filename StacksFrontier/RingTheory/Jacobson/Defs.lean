module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Jacobson rings

Mathlib already states all four tags of this file.

Stacks 00G0 defines a Jacobson ring as one in which every radical ideal is the intersection of
the maximal ideals containing it. That intersection is `Ideal.jacobson`, so the condition is
`IsJacobsonRing`, with `isJacobsonRing_iff` its unfolded form.

Stacks 00G1 — an algebra of finite type over a field is Jacobson — is
`isJacobsonRing_of_finiteType`, in the greater generality of a Jacobson base ring, of which a
field is one.

Stacks 00G2 — a ring whose primes are each the intersection of the maximal ideals containing
them is Jacobson — is the `mpr` half of `isJacobsonRing_iff_prime_eq`.

Stacks 00G3 — a ring is Jacobson exactly when its spectrum is a Jacobson space — is
`PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`.
-/

@[expose] public section

add_to_stacks 00G0 "a Jacobson ring" IsJacobsonRing
add_to_ega "IV 10.4.1" IsJacobsonRing
add_to_stacks 00G0 "the defining condition: every radical ideal is its own Jacobson radical,
  i.e. the intersection of the maximal ideals containing it" isJacobsonRing_iff
add_to_stacks 00G1 "in the generality of a Jacobson base ring" isJacobsonRing_of_finiteType
add_to_sga "3 VIA 1.1.2" "partial" isJacobsonRing_of_finiteType
add_to_ega "IV 10.4.7" "special case" isJacobsonRing_of_finiteType
add_to_ega "IV 10.4.6" "in particular"
  isJacobsonRing_of_finiteType
add_to_stacks 00G2 "the `mpr` direction" isJacobsonRing_iff_prime_eq
add_to_stacks 00G3 PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace
add_to_ega "IV 10.4.2" "special case" PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace
add_to_ega "IV 10.4.1" "ring: Spec(A) Jacobson" PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace
