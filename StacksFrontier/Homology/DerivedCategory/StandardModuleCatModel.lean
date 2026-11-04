module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.Perfect.Defs

/-!
# The derived category of modules over a ring, at the standard model

For a commutative ring `R` in universe `u`, this module names the unbounded derived category
`D(R)` of `R`-modules (`ModuleCat.{u} R`) **at the standard model**
`CategoryTheory.HasDerivedCategory.standard` (morphisms in `Type (u + 1)`), together with
perfectness of its objects ([Stacks, Tag 0657]) at that model.

## Main definitions

* `StacksDraft.ringHasDerivedCategory R`: the standard model, as a term.
* `StacksDraft.ringDerivedCategory R`: `D(R)` at that model.
* `StacksDraft.ringIsPerfect K`: `K` is a perfect object of `D(R)` at that model.
* `StacksDraft.ringRestrictScalars f`: restriction of scalars `D(A) ⥤ D(R)` along `f : R →+* A`,
  at that model on both sides.

## Implementation notes

The model is named explicitly, through `ringHasDerivedCategory`, rather than installed as an
instance. The library also carries `ModuleCat.hasDerivedCategory`, the
locally small model (morphisms in `Type u`), and in a file which activates it bare instance search
on `DerivedCategory (ModuleCat.{u} R)` finds that one. Declarations made in files which install
`HasDerivedCategory.standard` as a local instance, such as the derived sections
`AlgebraicGeometry.Space.representedAffineDerivedSections` and the derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, have their `D(R)` at the
standard model. In a file without that local instance, writing `DerivedCategory (ModuleCat R)` or
`(ModuleCat.restrictScalars f).mapDerivedCategory` silently lands in the locally small model, and
no longer composes with them. An expected type does not repair the second: instance search runs
first, and the objects of the two models agree, so only the morphisms then fail to match (in
`Type u` against `Type (u + 1)`).

Writing every such type as `ringDerivedCategory R`, and derived restriction of scalars as
`ringRestrictScalars f`, keeps the standard model without a `local instance` line.
`ringDerivedCategory R` unfolds to `DerivedCategory (ModuleCat.{u} R)` as elaborated in a file with
`attribute [local instance] HasDerivedCategory.standard`, and `ringRestrictScalars f` is, by `rfl`,
the right adjoint of `RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction f`, so
statements written against either spelling compose.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace StacksDraft

/-- The standard model `HasDerivedCategory.standard` of the derived category of `R`-modules, as a
term (it is deliberately not an instance; see the module docstring). -/
abbrev ringHasDerivedCategory (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- `D(R)`: the unbounded derived category of `R`-modules, at the standard model. -/
abbrev ringDerivedCategory (R : Type u) [CommRing R] :=
  @DerivedCategory (ModuleCat.{u} R) _ _ (ringHasDerivedCategory R)

/-- **Perfect objects of `D(R)`** ([Stacks, Tag 0657]) at the standard model: `K` is isomorphic to
a bounded complex of finite projective `R`-modules. -/
abbrev ringIsPerfect {R : Type u} [CommRing R] (K : ringDerivedCategory R) : Prop :=
  @StacksDraft.Perfect.IsPerfect R _ (ringHasDerivedCategory R) K

/-- **Derived restriction of scalars** `D(A) ⥤ D(R)` along `f : R →+* A`, at the standard model on
both sides. -/
abbrev ringRestrictScalars {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    ringDerivedCategory A ⥤ ringDerivedCategory R :=
  letI := ringHasDerivedCategory A
  letI := ringHasDerivedCategory R
  (ModuleCat.restrictScalars f).mapDerivedCategory

end StacksDraft
