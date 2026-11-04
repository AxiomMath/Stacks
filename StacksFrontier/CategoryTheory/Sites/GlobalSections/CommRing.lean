module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The ring of global regular functions on a ringed site is commutative

Sheaves of modules on a ringed site `X` are taken over `AlgebraicGeometry.RingedSite.ringSheaf`,
the structure sheaf with its commutativity forgotten, and the ring over which the cohomology of
such a module is a module is `Stacks.Cohomology.SiteModules.GlobalSectionRing` of that sheaf of
rings: the subring `RingCat.sectionsSubring` of compatible families of sections.  Commutativity
of that ring is not an instance, because the `RingCat`-valued sheaf has forgotten it.

This file supplies it, from the commutativity of the sections of the structure sheaf itself.
It is what extension of scalars asks for: `ModuleCat.extendScalars` is defined only for a ring
map between *commutative* rings.

## Main definitions

* `AlgebraicGeometry.RingedSite.sectionsCommRing`: the sections of `ringSheaf X` over an object
  of the site commute, that sheaf of rings being the structure sheaf with commutativity
  forgotten.
* `AlgebraicGeometry.RingedSite.globalSectionsCommRing`: **the ring of global regular functions
  of a ringed site is commutative.**

## Implementation notes

Both are stated as definitions and not as instances, and are meant to be activated with
`attribute [local instance]` where they are needed.  A global `CommRing` instance on
`RingCat.sectionsSubring (ringSheaf X).obj` would offer instance search a second route to the
`Ring` structure on that subring, through `CommRing.toRing`; the development states its module
categories over the route through `Subring`, and `CategoryTheory.Limits.ModuleCat` depends on
which `Ring` instance is found, so the two routes must not compete.

For the same reason `globalSectionsCommRing` extends the `Ring` instance already present rather
than being obtained from `Subring.toCommRing`: its `CommRing.toRing` is then the very instance
the module categories of this development are stated over, up to structure eta, and no
unification of two different ring structures on one type is ever required.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public section

open CategoryTheory
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- The sections of the structure sheaf of a ringed site over an object of the site commute.
Sheaves of modules are taken over `AlgebraicGeometry.RingedSite.ringSheaf`, which is the
structure sheaf with its commutativity forgotten; this recovers it. -/
@[instance_reducible]
noncomputable def sectionsCommRing (X : RingedSite.{u, v, w}) (U : X.Cᵒᵖ) :
    CommRing (ToType ((ringSheaf X.O).obj.obj U)) :=
  inferInstanceAs (CommRing (ToType (X.O.obj.obj U)))

/-- **The ring of global regular functions of a ringed site is commutative.**  Global sections
are compatible families of sections over the objects of the site, with pointwise operations, so
this is `AlgebraicGeometry.RingedSite.sectionsCommRing` read on each component.

The `Ring` structure is the one already present on the subring, not one rebuilt from the
commutative ambient ring; see the implementation notes. -/
@[instance_reducible]
noncomputable def globalSectionsCommRing (X : RingedSite.{u, v, w}) :
    CommRing ↥(RingCat.sectionsSubring (ringSheaf X.O).obj) :=
  letI inst : Ring ↥(RingCat.sectionsSubring (ringSheaf X.O).obj) := inferInstance
  { inst with
    mul_comm := fun a b => Subtype.ext (funext fun U =>
      mul_comm (G := ToType (X.O.obj.obj U)) (a.1 U) (b.1 U)) }

end AlgebraicGeometry.RingedSite

end
