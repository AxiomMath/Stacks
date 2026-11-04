module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Nagata.Examples

/-!
# Classes of Nagata schemes

A scheme locally of finite type over a Nagata ring is Nagata
(`AlgebraicGeometry.isNagataScheme_of_isNagataRing`, Tag 035A), so each class of Nagata rings
listed in Tag 0335 produces a class of Nagata schemes. This file records the bases a Noetherian
complete local ring, `ℤ`, and a Dedekind domain of characteristic zero, which are items (2), (3)
and (4) of Tag 035B. Item (1), a field, is
`AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field`, and item (5), *and so on*,
is the statement over an arbitrary Nagata ring itself.

## Main results

* `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_isPrecomplete`: a scheme locally
  of finite type over a Noetherian complete local ring is Nagata.
* `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_int` and
  `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_uliftInt`: a scheme locally of
  finite type over `ℤ` is Nagata, over `Spec ℤ` itself and over the universe-polymorphic base
  `Spec (ULift ℤ)`.
* `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_isDedekindDomain_of_charZero`: a
  scheme locally of finite type over a Dedekind domain of characteristic zero is Nagata.

## Implementation notes

`Spec (CommRingCat.of ℤ)` is a scheme at universe `0` only, so a morphism to it constrains its
source to `Scheme.{0}`; the base over which an arbitrary `X : Scheme.{u}` is a `ℤ`-scheme is
`Spec (CommRingCat.of (ULift.{u} ℤ))`, which is the terminal scheme
(`AlgebraicGeometry.specULiftZIsTerminal`). Both forms are recorded, the second obtained by
transporting `Int.isNagataRing` along `ULift.ringEquiv.symm` across the universe boundary with
`MonogenicN1.isNagataRing_of_ringEquiv`.

Completeness of the local base is asked for as `IsPrecomplete (IsLocalRing.maximalIdeal R) R`,
exactly as in Tag 032W (`IsNagataRing.of_isPrecomplete_maximalIdeal`): the Hausdorff half of
`IsAdicComplete` is automatic for a Noetherian local ring, so nothing is added to the source's
hypothesis.

## References

* [Stacks Project, Tag 035B](https://stacks.math.columbia.edu/tag/035B)
* [Stacks Project, Tag 035A](https://stacks.math.columbia.edu/tag/035A)
* [Stacks Project, Tag 0335](https://stacks.math.columbia.edu/tag/0335)
* [Stacks Project, Tag 032W](https://stacks.math.columbia.edu/tag/032W)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 035B (2).** A scheme locally of finite type over a Noetherian complete
local ring is a Nagata scheme: such a ring is Nagata by Tag 032W. -/
@[stacks 035B "(2) A scheme locally of finite type over a Noetherian complete local ring; \
  completeness is `IsPrecomplete (IsLocalRing.maximalIdeal R) R`, the hypothesis of Tag 032W."]
theorem isNagataScheme_of_locallyOfFiniteType_over_isPrecomplete (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : IsNagataScheme X :=
  isNagataScheme_of_isNagataRing f IsNagataRing.of_isPrecomplete_maximalIdeal

/-- **Stacks Project, Tag 035B (3).** A scheme locally of finite type over `ℤ` is a Nagata
scheme: `ℤ` is a Nagata ring by Tag 0335 (3). -/
@[stacks 035B "(3) A scheme locally of finite type over `ℤ`, for the base `Spec ℤ`, which forces \
  the source to live at universe 0; `isNagataScheme_of_locallyOfFiniteType_over_uliftInt` is the \
  same statement for a source at an arbitrary universe."]
theorem isNagataScheme_of_locallyOfFiniteType_over_int {X : Scheme.{0}} (f : X ⟶ Spec (.of ℤ))
    [LocallyOfFiniteType f] : IsNagataScheme X :=
  isNagataScheme_of_isNagataRing f Int.isNagataRing

/-- **Stacks Project, Tag 035B (3), at an arbitrary universe.** A scheme locally of finite type
over `Spec (ULift ℤ)`, the terminal scheme, is a Nagata scheme. -/
@[stacks 035B "(3) A scheme locally of finite type over `ℤ` with the source at an arbitrary \
  universe, the base being `Spec (ULift ℤ)`, the terminal scheme."]
theorem isNagataScheme_of_locallyOfFiniteType_over_uliftInt {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType f] : IsNagataScheme X :=
  isNagataScheme_of_isNagataRing f
    (MonogenicN1.isNagataRing_of_ringEquiv ULift.ringEquiv.symm Int.isNagataRing)

/-- **Stacks Project, Tag 035B (4).** A scheme locally of finite type over a Dedekind domain
whose fraction field has characteristic zero is a Nagata scheme: such a ring is Nagata by
Tag 0335 (4). -/
@[stacks 035B "(4) A scheme locally of finite type over a Dedekind ring of characteristic zero, \
  the characteristic condition read as `CharZero R` as in Tag 0335 (4)."]
theorem isNagataScheme_of_locallyOfFiniteType_over_isDedekindDomain_of_charZero (R : Type u)
    [CommRing R] [IsDedekindDomain R] [CharZero R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] : IsNagataScheme X :=
  isNagataScheme_of_isNagataRing f IsNagataRing.of_isDedekindDomain_of_charZero

/- Item (5) of the source, *and so on*, is the statement over an arbitrary Nagata ring, which is
`isNagataScheme_of_isNagataRing`, itself Tag 035A specialized to an affine base. -/
add_to_stacks 035B "(5) \"And so on\": a scheme locally of finite type over an arbitrary Nagata \
  ring." isNagataScheme_of_isNagataRing

end AlgebraicGeometry

end
