module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoCriteria
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# Standard classes of J-2 schemes

A scheme locally of finite type over a base whose ring is J-2 is itself J-2, so each of the
standard classes of J-2 rings produces a class of J-2 schemes: schemes locally of finite type
over a field, over a Noetherian complete local ring, over the integers, over a one-dimensional
Noetherian local ring, over a one-dimensional Nagata ring, or over a Dedekind domain of
characteristic zero.

## Main results

* `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_over_field`,
  `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_over_completeLocalRing`,
  `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_over_int`,
  `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_over_localRing_of_dim_one`,
  `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_over_nagataRing_of_dim_one` and
  `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_over_dedekindDomain`: the six classes.

## Implementation notes

Each case is the ring-theoretic statement that the base ring is J-2, which is
`isJ2_of_standard_classes_and_finiteType`, read on the spectrum through
`AlgebraicGeometry.Scheme.isJ2_Spec_iff` and transported to the source along the structure
morphism by `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType`. A scheme over a ring is
presented by an explicit structure morphism to the ring's spectrum; local Noetherianity of the
source is automatic from that morphism and is requested as an instance argument, as in
`AlgebraicGeometry.Scheme.IsJ2` itself.

Completeness of a local ring is `IsPrecomplete (IsLocalRing.maximalIdeal R) R`, separatedness
being automatic for a Noetherian local ring. The spectrum of `ℤ` lives in the bottom universe,
so the statement about the integers is about schemes there.

## References

* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme locally of finite type over the spectrum of a Noetherian J-2 ring is J-2. -/
private theorem isJ2_of_locallyOfFiniteType_of_isJ2 (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : _root_.IsJ2 R) {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] : IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian ((isJ2_Spec_iff R).mpr hR) f

/-- **Stacks Project, Tag 07R5.** A scheme locally of finite type over a field is J-2. -/
@[stacks 07R5 "field_case", ega "IV 6.12.6" "(ii), field base", sga "5 I 3.1.1" "field base"]
public theorem isJ2_of_locallyOfFiniteType_over_field (k : Type u) [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isJ2 k ((isJ2_of_standard_classes_and_finiteType.{u, u}).1 k) f

/-- **Stacks Project, Tag 07R5.** A scheme locally of finite type over a Noetherian complete
local ring is J-2. -/
@[stacks 07R5 "complete_local_case", ega "IV 6.12.8", sga "5 I 3.1.1" "complete local base"]
public theorem isJ2_of_locallyOfFiniteType_over_completeLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isJ2 R ((isJ2_of_standard_classes_and_finiteType.{u, u}).2.1 R) f

/-- **Stacks Project, Tag 07R5.** A scheme locally of finite type over the integers is J-2. -/
@[stacks 07R5 "integers_case"]
public theorem isJ2_of_locallyOfFiniteType_over_int {X : Scheme.{0}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] : IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isJ2 ℤ (isJ2_of_standard_classes_and_finiteType.{0, 0}).2.2.1 f

/-- **Stacks Project, Tag 07R5.** A scheme locally of finite type over a Noetherian local ring
of dimension one is J-2. -/
@[stacks 07R5 "local_dimension_one_case"]
public theorem isJ2_of_locallyOfFiniteType_over_localRing_of_dim_one (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hR : ringKrullDim R = 1) {X : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isJ2 R
    ((isJ2_of_standard_classes_and_finiteType.{u, u}).2.2.2.1 R hR) f

/-- **Stacks Project, Tag 07R5.** A scheme locally of finite type over a Nagata ring of
dimension one is J-2. -/
@[stacks 07R5 "nagata_dimension_one_case"]
public theorem isJ2_of_locallyOfFiniteType_over_nagataRing_of_dim_one (R : Type u) [CommRing R]
    [IsNagataRing R] (hR : ringKrullDim R = 1) {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isJ2 R
    ((isJ2_of_standard_classes_and_finiteType.{u, u}).2.2.2.2.1 R inferInstance hR) f

/-- **Stacks Project, Tag 07R5.** A scheme locally of finite type over a Dedekind domain of
characteristic zero is J-2. -/
@[stacks 07R5 "dedekind_characteristic_zero_case",
  ega "IV 6.12.6" "(i)",
  sga "5 I 3.1.1" "Dedekind char 0 base"]
public theorem isJ2_of_locallyOfFiniteType_over_dedekindDomain (R : Type u) [CommRing R]
    [IsDedekindDomain R] [CharZero R] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : IsJ2 X :=
  isJ2_of_locallyOfFiniteType_of_isJ2 R
    ((isJ2_of_standard_classes_and_finiteType.{u, u}).2.2.2.2.2.1 R) f

end AlgebraicGeometry.Scheme
