module

public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects

/-!
# A left dual in `D(O)` restricts to a left dual in `D(O|_U)`

Let `(C, O)` be a ringed site, `U` an object of `C`, and let `M` have a left dual `N` in the
symmetric monoidal category `D(O)` of Stacks 0FPT — an exact pairing, which is Definition 0FFP.
Then `M|_U` has the left dual `N|_U` in `D(O|_U)`, for the same monoidal structure read on the
localized ringed site `(C/U, O|_U)`.

It is the shrinking step in the proofs of Stacks 0FPV, and of Stacks 0FPD on a ringed space:
an argument that passes to a smaller object of the site keeps a left dual to work with.

## Main definitions

* `AlgebraicGeometry.RingedSite.exactPairingRestrict`: the pairing restricts to the localized
  ringed site.

## Main results

* `AlgebraicGeometry.RingedSite.restriction_eq_overFunctor`: derived restriction as this file
  spells it is, definitionally, the functor `SheafOfModules.overFunctor` over which the locality
  of perfectness, `AlgebraicGeometry.RingedSite.isPerfect_of_locally`, is stated.

## Implementation notes

The restriction is immediate from two inputs:

* `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`, a **strong** monoidal
  structure on derived restriction (lax would not serve: the tensorator has to be invertible);
  and
* `CategoryTheory.ExactPairing.map`, which carries an exact pairing forward along a monoidal
  functor.

Conclusion (a) of Stacks 0FPD on a ringed space is
`Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing`, whose shrinking step is the same
restriction for the open subspaces of the ringed space,
`Stacks.Cohomology.LeftDualPerfect.exactPairingRestrictOpen`.

At the concrete site `Stacks.SheafOfModules.ringedSite Rc` of a ringed space, instance search
does not find `(restriction (ringedSite Rc) U).Additive`, `preservesFiniteLimits_restriction` or
`preservesFiniteColimits_restriction`, although they apply there by name; a statement at that site
introduces them by `letI`, starting from
`Stacks.DerivedTensor.ExtensionByZero.additive_restriction (ringedSite Rc) U`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Derived restriction to a localized site is the slice restriction functor of the locality
of perfectness.** `Stacks.DerivedTensor.ExtensionByZero.restriction`, over which the monoidal
structure of
`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal` is built, is definitionally
`SheafOfModules.overFunctor`, over which
`AlgebraicGeometry.RingedSite.isPerfect_of_locally` is stated. -/
theorem restriction_eq_overFunctor :
    restriction X U =
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U :=
  rfl

/-- **A left dual in `D(O)` restricts to a left dual in `D(O|_U)`.** If `N` is a left dual of
`M` in the symmetric monoidal category `D(O)` of Stacks 0FPT, then `N|_U` is a left dual of
`M|_U` in `D(O|_U)` for the same structure on the localized ringed site `(C/U, O|_U)`.

This is the shrinking step of Stacks 0FPV and of Stacks 0FPD: the pairing travels with the
restriction, so an argument may pass to a smaller object of the site and still have a left dual
to work with. It is `CategoryTheory.ExactPairing.map` along
`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`; the four instance arguments
are sheafification side conditions.

The monoidal structure on the target is written at `X.O.over U`, the spelling in which
`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal` states it. That is the
structure sheaf of the localized ringed site `X.over U` on the nose, by
`AlgebraicGeometry.RingedSite.over_O`. -/
@[instance_reducible]
def exactPairingRestrict (M N : DerivedCategory (Modules X.O))
    (pair : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O;
      ExactPairing M N) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.O.over U)
    ExactPairing ((restriction X U).mapDerivedCategory.obj M)
      ((restriction X U).mapDerivedCategory.obj N) :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.O.over U)
  letI := pair
  letI := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X U
  ExactPairing.map _ M N

end AlgebraicGeometry.RingedSite

end
