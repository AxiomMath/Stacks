module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# A perfect complex together with an effective Cartier divisor

The standing data for blowing up a complex along a divisor: a scheme, an effective Cartier
divisor on it, and a perfect object of the unbounded derived category of
`𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation` packages the scheme, the divisor, and the
  perfect derived object.

## Implementation notes

The divisor is represented by `AlgebraicGeometry.Scheme.IdealSheafData`, which also
determines its ideal sheaf and its closed subscheme. The existence of the derived category
of `𝒪_X`-modules is carried as an instance-implicit field, since it is the Lean datum
needed to form the type of the perfect object; `attribute [instance]` makes it available to
typeclass inference at every use site.

## References

* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
-/

@[expose] public section

open CategoryTheory StrictlyPerfect

universe u d

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0F8S.** The standing situation of a perfect derived object on a
scheme together with an effective Cartier divisor on that scheme. -/
@[stacks 0F8S]
structure ComplexAndDivisorSituation where
  /-- The scheme. -/
  X : Scheme.{u}
  /-- The effective Cartier divisor, given by its ideal sheaf. -/
  D : X.IdealSheafData
  /-- The divisor is effective Cartier. -/
  isEffectiveCartierDivisor : Stacks.Divisors.IsEffectiveCartierDivisor D
  /-- The derived category of modules on `X` exists. -/
  [hasDerivedCategory : HasDerivedCategory.{d} (OXMod X.toRingedSpace)]
  /-- The derived object. -/
  M : DerivedCategory (OXMod X.toRingedSpace)
  /-- The derived object is perfect. -/
  isPerfect : RingedSpace.IsPerfect M

attribute [instance] ComplexAndDivisorSituation.hasDerivedCategory

end AlgebraicGeometry
