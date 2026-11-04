module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedComplexDerivedStalk
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# The geometric stalk and the universe lift

The geometric stalk of an *abelian* sheaf on the small étale site of an algebraic space is a
colimit over a neighbourhood category whose objects live one universe above the sections, so it
exists in `AddCommGrpCat.{u + 1}` and not in `AddCommGrpCat.{u}`: that is why
`AlgebraicGeometry.Space.smallEtaleAbelianStalk` is pinned at `u + 1`.  The stalk of a sheaf of
*modules* is a different construction — the fibre at the point of the site of Stacks 04K0 — and
it is available at `u` itself.  The two therefore cannot be compared at a single universe, and
anything that reads a statement about abelian stalks as a statement about the modules of this
development has to lift the coefficients.

This file supplies the lift: the fibre at a point of a site commutes with the universe lift of
abelian groups, and consequently the geometric module stalk at `u`, forgotten to abelian groups
and lifted, is the geometric stalk at `u + 1` of the lifted underlying abelian sheaf.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSheafFiberUliftIso`: the fibre at the point of Stacks 04K0
  commutes with the universe lift of abelian groups.
* `AlgebraicGeometry.Space.smallEtaleAbelianStalkUliftIso`: the same read with the geometric
  stalk of Stacks 04JY on the upper side.
* `AlgebraicGeometry.Space.geometricModuleStalkCompUliftIso`: the geometric module stalk at `u`,
  forgotten to abelian groups and lifted, is the geometric stalk at `u + 1` of the lifted
  underlying abelian sheaf.

## Implementation notes

The commutation is `CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso`, whose
coefficient categories are independent, so `AddCommGrpCat.{u}` and `AddCommGrpCat.{u + 1}` is a
legal instantiation; the direction taken here is the opposite one, which is what transports a
statement from `u` up to `u + 1`.  Its two side conditions —
`CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}` for the lift and
`CategoryTheory.GrothendieckTopology.HasSheafCompose` for it — both hold by instance search on
the small étale site, so no longhand instance is needed here.

The module half is free: `Stacks.sheafModuleFiberCompForget₂` is `Iso.refl`, the stalk of a
sheaf of modules being by construction the fibre of its underlying abelian sheaf with the scalar
action carried along.  What is not free is the identification of that fibre with the geometric
stalk of Stacks 04JY, which is
`AlgebraicGeometry.Space.sheafFiberGeometricStalkIso`.

## References

* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04K1](https://stacks.math.columbia.edu/tag/04K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The fibre at a geometric point commutes with the universe lift of abelian groups.**  For a
geometric point `x` of an algebraic space `X`, lifting the coefficients of an abelian sheaf on
the small étale site of `X` from `u` to `u + 1` and then taking the fibre at the point of
Stacks 04K0 gives the lift of the fibre taken at `u`.

The fibre is a filtered colimit and the lift preserves filtered colimits, which is the content;
this is `CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso` at the two coefficient
categories, read in the direction that carries a statement at `u` up to `u + 1`. -/
def smallEtaleSheafFiberUliftIso (x : GeometricPoint B S hS X.1) :
    (etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := AddCommGrpCat.{u}) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
        (etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := AddCommGrpCat.{u + 1}) :=
  ((etaleSitePoint B S hS X.1 x X.2).sheafFiberCompIso
    AddCommGrpCat.uliftFunctor.{u + 1, u}).symm

/-- **The geometric stalk commutes with the universe lift of abelian groups.**
`AlgebraicGeometry.Space.smallEtaleSheafFiberUliftIso` with the geometric stalk of Stacks 04JY
in place of the fibre of Stacks 04K0 on the upper side, the two being identified by
`AlgebraicGeometry.Space.sheafFiberGeometricStalkIso`.

This is the form in which the lift is consumed: the geometric stalk of an abelian sheaf exists
only from `u + 1` upwards, so a statement about it can only be compared with a construction at
`u` after lifting, and this says the lift does no damage. -/
def smallEtaleAbelianStalkUliftIso (x : GeometricPoint B S hS X.1) :
    (etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := AddCommGrpCat.{u}) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
        smallEtaleAbelianStalk B S hS x :=
  smallEtaleSheafFiberUliftIso B S hS X x ≪≫
    Functor.isoWhiskerLeft
      (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u})
      (sheafFiberGeometricStalkIso.{u, u} B S hS X.1 X.2 x)

/-- **The geometric module stalk, forgotten and lifted, is the geometric stalk of the lifted
underlying abelian sheaf.**  For a sheaf of rings `R` on the small étale site of an algebraic
space `X` and a geometric point `x` of `X`, the stalk of a sheaf of `R`-modules at `x` — a module
over the stalk of `R`, at universe `u` — has as underlying abelian group, after the lift to
`u + 1`, the geometric stalk of Stacks 04JY of the lift of the underlying abelian sheaf.

This is the dictionary that lets a statement about geometric stalks of abelian sheaves be read as
a statement about the geometric module stalks of this development, which is where the functors of
Stacks 0AEW and Stacks 0AEX live.  Its two halves are `Stacks.sheafModuleFiberCompForget₂`, which
is the identity, and `AlgebraicGeometry.Space.smallEtaleAbelianStalkUliftIso`. -/
def geometricModuleStalkCompUliftIso
    (R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (x : GeometricPoint B S hS X.1) :
    geometricModuleStalkFunctor B S hS X.1 X.2 R x ⋙
        forget₂ (ModuleCat.{u} (((etaleSitePoint B S hS X.1 x X.2).presheafFiber
          (A := RingCat.{u})).obj R.obj)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      SheafOfModules.toSheaf.{u} R ⋙
        sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
          smallEtaleAbelianStalk B S hS x :=
  Functor.isoWhiskerRight
      (Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS X.1 x X.2) R)
      AddCommGrpCat.uliftFunctor.{u + 1, u} ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} R)
      (smallEtaleAbelianStalkUliftIso B S hS X x)

end AlgebraicGeometry.Space

end
