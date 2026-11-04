module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison

/-!
# The two abelian étale stalk frameworks agree

The library carries two notions of the stalk of an abelian sheaf at a geometric point, on the two
small étale sites it carries.

* `AlgebraicGeometry.etaleStalkFunctorAbelian` is the stalk on the *bounded* small étale site
  `AlgebraicGeometry.SmallEtale B S hS` cut out of a big étale site. It is the colimit of the
  sections over `AlgebraicGeometry.geometricPointFiber`, the category of pointed étale
  neighbourhoods of the geometric point.
* `Stacks.EtaleCohomology.smallEtaleStalkAb` is the stalk on Mathlib's small étale site
  `AlgebraicGeometry.Scheme.Etale`, namely the fibre of the site point
  `AlgebraicGeometry.Scheme.pointSmallEtale`.

The two sheaf categories are identified by `AlgebraicGeometry.SmallEtale.sheafEquiv`, the dense
subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite` being full, faithful and cover-dense.
The bridge is therefore not an equality of functors on one category but a natural isomorphism
*across that equivalence*, which is what this file supplies.

## Main results

* `AlgebraicGeometry.sheafEquivCompSmallEtaleStalkAbIso` — the stalk on Mathlib's small étale
  site, read through the identification of the two sheaf categories, is the bounded site's own
  abelian stalk functor.
* `AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso` — its per-sheaf form.

## Implementation notes

The only input is the general transport
`AlgebraicGeometry.sheafFiberIsoOfAdjOfFiberIso`: a continuous functor of sites, together with an
isomorphism identifying the pulled-back fibre functor of a point of the target with the fibre
functor of a point of the source, identifies any left adjoint of the direct image followed by the
fibre at the target point with the fibre at the source point. Here the functor is
`AlgebraicGeometry.SmallEtale.toEtaleSite`, the fibre comparison is
`AlgebraicGeometry.toEtaleSiteFiberIso`, and the left adjoint is the forward direction of
`AlgebraicGeometry.SmallEtale.sheafEquiv`.

The module-valued case of exactly this comparison is
`AlgebraicGeometry.sheafEquivCompSheafFiberIso`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison`; this file is its
`AddCommGrpCat` instance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (s : GeometricPoint X.obj)

/-- **The two abelian étale stalk frameworks agree.** The stalk functor of Mathlib's point of the
small étale site at a geometric point, read through the identification of the two sheaf
categories, is the bounded site's own abelian stalk functor at that point.

This is the `AddCommGrpCat` instance of `AlgebraicGeometry.sheafEquivCompSheafFiberIso`, whose
module-valued form does not apply to the abelian theory. -/
public def sheafEquivCompSmallEtaleStalkAbIso :
    (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor ⋙
        Stacks.EtaleCohomology.smallEtaleStalkAb s.hom ≅
      etaleStalkFunctorAbelian B X.obj X.property s :=
  sheafFiberIsoOfAdjOfFiberIso (geometricSitePoint B X s)
    (Scheme.pointSmallEtale s.hom) (SmallEtale.toEtaleSite B X.obj X.property)
    (toEtaleSiteFiberIso B X.obj X.property s)
    (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).toAdjunction

/-- The per-sheaf form of the bridge: for an abelian sheaf on the bounded small étale site, the
stalk of its transport to Mathlib's small étale site is the stalk computed on the bounded site. -/
public def smallEtaleStalkAb_sheafEquiv_obj_iso
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj
        ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor.obj F) ≅
      etaleStalk B X.obj X.property s ((sheafToPresheaf _ _).obj F) :=
  (sheafEquivCompSmallEtaleStalkAbIso B X s).app F

end AlgebraicGeometry

end
