module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Jacobson.Criteria
public import StacksFrontier.RingTheory.Jacobson.Examples
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine

/-!
# Jacobson schemes of finite type over a base

A scheme locally of finite type over a Jacobson base is a Jacobson space. This file records
the four bases of [Stacks, Tag 02J6]: a field, the integers, a one-dimensional Noetherian domain
with infinitely many prime ideals, and the punctured spectrum of a Noetherian local ring.

## Main results

* `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` (Mathlib) covers a scheme locally of
  finite type over a field.
* `AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType_over_integers` covers a scheme with a
  locally finite type morphism to `Spec ℤ`.
* `AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType_over_oneDimensionalNoetherianDomain`
  covers a one-dimensional Noetherian domain with infinitely many prime ideals.
* `AlgebraicGeometry.jacobsonSpace_puncturedSpectrum` and
  `AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType_over_puncturedSpectrum` cover the
  punctured spectrum of a Noetherian local ring and the schemes locally of finite type over it.

## Implementation notes

Being locally of finite type over the integers is expressed by a locally finite type morphism
to the terminal scheme, which is the universe-polymorphic model of the spectrum of `ℤ`. Having
infinitely many primes means that the set of prime ideals of the base ring is infinite, and the
base scheme is the spectrum of that ring.

The punctured spectrum is the open subscheme `Stacks.Divisors.puncturedSpectrum R` of `Spec R`
cut out by the complement of the closed point.

## References

* [Stacks Project, Tag 02J6](https://stacks.math.columbia.edu/tag/02J6)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

add_to_stacks 02J6 "over_field" AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_sga "3 VIB 1.3.0" "Jacobson property of G"
  AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_sga "4 VIII 3.13" "more general" AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_ega "IV 10.4.7" AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_ega "IV 10.4.9" "more general" AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_ega "IV 10.6.1" "(i), condition 1° for X" AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_ega "IV 10.7.1" "1°, partial" AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace

/-- A scheme locally of finite type over the integers is Jacobson. -/
@[stacks 02J6 "over_integers",
  ega "IV 10.4.7" "base = Spec Z",
  ega "IV 10.4.6" "over Z",
  ega "IV 10.4.9" "over Z", ega "IV 10.7.1" "1° over Z"]
theorem jacobsonSpace_of_locallyOfFiniteType_over_integers {X : Scheme.{u}}
    (f : X ⟶ ⊤_ Scheme.{u}) [LocallyOfFiniteType f] : JacobsonSpace X := by
  have : IsJacobsonRing (ULift.{u} ℤ) :=
    (isJacobsonRing_iso (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)).mpr int_isJacobsonRing
  have : JacobsonSpace (⊤_ Scheme.{u}) :=
    JacobsonSpace.of_isClosedEmbedding (Scheme.homeoOfIso
      (Limits.terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal)).isClosedEmbedding
  exact LocallyOfFiniteType.jacobsonSpace f

/-- A scheme locally of finite type over a one-dimensional Noetherian domain with infinitely
many prime ideals is Jacobson. -/
@[stacks 02J6 "over_dimension_one_domain",
  ega "IV 10.4.7" "1-dim Noeth domain base",
  ega "IV 10.7.1" "special case"]
theorem jacobsonSpace_of_locallyOfFiniteType_over_oneDimensionalNoetherianDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hprimes : {p : Ideal A | p.IsPrime}.Infinite)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    JacobsonSpace X := by
  have : FiniteRingKrullDim A :=
    (finiteRingKrullDim_iff_ne_bot_and_top).2 ⟨by norm_num [hdim], by
      rw [hdim]
      exact (WithBot.coe_eq_top.not).2 (ENat.natCast_ne_top 1)⟩
  have : IsJacobsonRing A :=
    isJacobsonRing_of_forall_isMaximal_or_infinite_setOf_isPrime A (by
      intro p hp
      by_cases hp0 : p = ⊥
      · right
        simpa [hp0] using hprimes
      · left
        apply Ideal.isMaximal_of_height_eq_ringKrullDim
        apply le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top)
        rw [hdim]
        exact_mod_cast (show 1 ≤ p.height from by
          simpa using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hp0)))
  exact LocallyOfFiniteType.jacobsonSpace f

/-- The punctured spectrum `Spec R \ {𝔪}` of a Noetherian local ring `R` is a Jacobson
scheme. -/
@[stacks 02J6 "part (4): the punctured spectrum itself, R Noetherian local", instance,
  ega "IV 10.4.7" "punctured spectrum base", ega "IV 10.5.7" "special case"]
theorem jacobsonSpace_puncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    JacobsonSpace (Stacks.Divisors.puncturedSpectrum R).toScheme :=
  PrimeSpectrum.jacobsonSpace_compl_closedPoint R

/-- A scheme locally of finite type over the punctured spectrum of a Noetherian local ring is
Jacobson. -/
@[stacks 02J6 "part (4): schemes lft over the punctured spectrum, R Noetherian local",
  ega "IV 10.4.7" "punctured spectrum base", ega "IV 10.5.7" "special case"]
theorem jacobsonSpace_of_locallyOfFiniteType_over_puncturedSpectrum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ (Stacks.Divisors.puncturedSpectrum R).toScheme)
    [LocallyOfFiniteType f] : JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace f

end AlgebraicGeometry
