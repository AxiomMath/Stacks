module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLargeSections
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of ringed sites whose sections live above the site

`AlgebraicGeometry.RingedSite.Hom` is declared for `RingedSite.{u, u, w}`: the objects and the
morphisms of the two sites share a universe, while the sections `w` of the structure sheaves are
free. The developments stated for `AlgebraicGeometry.RingedSite.HomGeneral`, whose site
universes are independent, are reached from it by
`AlgebraicGeometry.RingedSite.Hom.toHomGeneral`, and that passage is available only at
`RingedSite.{u, u, u}`. The reason is the site condition: `HomGeneral` carries the unrestricted
`IsMorphismOfSites.{w}`, left exactness of the inverse image on sheaves of `Type w`-valued sets,
whereas `AlgebraicGeometry.RingedSite.Hom` carries `CategoryTheory.Functor.IsMorphismOfSites`,
the small-site condition of [Stacks, Tag 00X1], which is left exactness at the site universe; and
`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites` converts the one into the other
at that universe alone.

This file removes the restriction.
`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback_largeSections` says that left
exactness of the inverse image at the site universe gives left exactness at every larger universe
of sections, so the small-site condition gives the unrestricted condition at every universe
containing the site, and a morphism of ringed sites with sections in any such universe is a
morphism of ringed sites in the sense of `HomGeneral`.

## Main results

* `CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSitesLargeSections`: the small-site
  condition of [Stacks, Tag 00X1] gives the unrestricted one at every universe of sections
  containing the site universe.
* `AlgebraicGeometry.RingedSite.Hom.toHomGeneralLargeSections`: a morphism of ringed sites
  between `RingedSite.{u, u, max u w}`s is a morphism of ringed sites at independent universes.
* `AlgebraicGeometry.RingedSite.Hom.toHomGeneralLargeSections_u` and
  `..._fsharp`: it carries the same functor and the same structure map, and
  `AlgebraicGeometry.RingedSite.Hom.toHomGeneral_eq_toHomGeneralLargeSections`: at
  `RingedSite.{u, u, u}` it is `AlgebraicGeometry.RingedSite.Hom.toHomGeneral`.

## Implementation notes

Neither statement carries a `@[stacks]` attribute. The first is
`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites` with its universe of sections
freed, and that declaration carries no tag either: [Stacks, Tag 00X1] is carried by
`CategoryTheory.Functor.IsMorphismOfSites` itself. The second is
`AlgebraicGeometry.RingedSite.Hom.toHomGeneral` with the same freeing, and the tag of that
passage, [Stacks, Tag 03AD] part (2), sits on the two structures.

The sections universe is written `max u w` rather than a free `w`. At a universe not containing
the site universe the sheaves of `Type w`-valued sets on the site are not the topos the
condition speaks about, and the inverse image at that universe is not what [Stacks, Tag 00XC]
produces; `max u w` ranges over exactly the universes for which the statement is the intended
one, and `w := u` recovers the existing declarations.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public section

open CategoryTheory

universe u w

/-- **The small-site condition gives the unrestricted one at every larger universe of
sections.** If the inverse image of a continuous functor between sites small in one universe is
left exact on sheaves of sets valued in that universe, then it is left exact on sheaves of sets
valued in any universe containing it, so the functor defines a morphism of sites in the
unrestricted sense there.

`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites` is the case `w = u`. The left
exactness at the larger universe is
`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback_largeSections`, and the left adjoint
exhibited is the chosen sheaf pullback there. -/
theorem CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSitesLargeSections
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (h : F.IsMorphismOfSites J K) : _root_.IsMorphismOfSites.{max u w} F J K :=
  have := h.isContinuous
  { __ := h.isContinuous
    hasExactLeftAdjoint :=
      ⟨F.sheafPullback (Type (max u w)) J K,
        ⟨F.sheafAdjunctionContinuous (Type (max u w)) J K⟩,
        CategoryTheory.Functor.preservesFiniteLimits_sheafPullback_largeSections.{u, w} h⟩ }

namespace AlgebraicGeometry.RingedSite

/-- **A morphism of ringed sites whose sections live above the site is a morphism of ringed
sites at independent universes.** It has the same underlying functor and the same structure
map; what has to be supplied is the site condition in the unrestricted form `HomGeneral` asks
for, which is `CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSitesLargeSections`.

`AlgebraicGeometry.RingedSite.Hom.toHomGeneral` is the case `w = u`. -/
def Hom.toHomGeneralLargeSections {X Y : RingedSite.{u, u, max u w}} (f : Hom X Y) :
    HomGeneral X Y where
  u := f.u
  isMorphismOfSites := f.isMorphismOfSites.toIsMorphismOfSitesLargeSections.{u, w}
  fsharp := f.fsharp

/-- The passage leaves the underlying functor unchanged. -/
@[simp]
theorem Hom.toHomGeneralLargeSections_u {X Y : RingedSite.{u, u, max u w}} (f : Hom X Y) :
    (f.toHomGeneralLargeSections.{u, w}).u = f.u := rfl

/-- The passage leaves the structure map unchanged. -/
@[simp]
theorem Hom.toHomGeneralLargeSections_fsharp {X Y : RingedSite.{u, u, max u w}} (f : Hom X Y) :
    (f.toHomGeneralLargeSections.{u, w}).fsharp = f.fsharp := rfl

/-- At a single universe the passage is `AlgebraicGeometry.RingedSite.Hom.toHomGeneral`: the
two have the same underlying functor and the same structure map, and the site conditions are
propositions. -/
theorem Hom.toHomGeneral_eq_toHomGeneralLargeSections {X Y : RingedSite.{u, u, u}}
    (f : Hom X Y) : f.toHomGeneral = f.toHomGeneralLargeSections.{u, u} := rfl

end AlgebraicGeometry.RingedSite

end
