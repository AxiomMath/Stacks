module

public import StacksFrontier.RingTheory.Dualizing.GorensteinCriteria

/-!
# Gorenstein rings and dualizing complexes that are locally a shifted unit

Let `A` be a Noetherian ring and `K` a dualizing complex over `A`. [Stacks, Tag 0DW9 (1)(a)]
says that `A` is Gorenstein exactly when `K` is an invertible object of `D(A)`, and
[Stacks, Tag 0FNT] says that an object of `D(A)` is invertible exactly when it is, over a
principal neighbourhood of every prime, a shift of the localized ring. This file composes the
two, so that Gorensteinness is read off the Zariski-local shape of `K` without naming a monoidal
structure.

## Main results

* `Dualizing.isGorensteinRing_iff_isLocallyShiftedUnit` — a Noetherian ring with a dualizing
  complex is Gorenstein exactly when that complex is locally a shifted unit.

## Implementation notes

No `@[stacks]` attribute is placed. The mathematics is that of
`Dualizing.isGorensteinRing_iff_isInvertible_canonical` ([Stacks, Tag 0DW9 (1)(a)]) and
`DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit` ([Stacks, Tag 0FNT]), both of
which already carry their tags; this is the composite, whose value is that its statement names no
monoidal structure and so can be read at an affine open of a scheme.

`attribute [local instance 10000] HasDerivedCategory.standard` rather than the plain attribute:
`DerivedCategory.Invertible.IsLocallyShiftedUnit` and
`Dualizing.isGorensteinRing_iff_isInvertible_canonical` are both stated at the standard model, and
a global locally small instance anywhere in the import closure would otherwise beat a
default-priority local attribute.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- A Noetherian ring carrying a dualizing complex `K` is Gorenstein exactly when `K` is locally
a shifted unit, that is, when every prime has a principal neighbourhood over which the derived
localization of `K` is a shift of the localized ring.

This is [Stacks, Tag 0DW9 (1)(a)] composed with the local description of the invertible objects
of `D(A)` from [Stacks, Tag 0FNT]. -/
public theorem isGorensteinRing_iff_isLocallyShiftedUnit
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    Dualizing.IsGorensteinRing A ↔ DerivedCategory.Invertible.IsLocallyShiftedUnit K :=
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  (isGorensteinRing_iff_isInvertible_canonical K hK).trans
    (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit K).1

end Dualizing

end
