module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism

/-!
# A morphism of ringed sites, read as a site-presented morphism of ringed topoi

A morphism of ringed sites `(f, f♯) : (C, O) ⟶ (D, O')` of Stacks 01D3 part (2) consists of a
functor `u : D ⥤ C` which is a morphism of sites together with a structure map
`f♯ : O' ⟶ f_* O` in direct-image form. A `AlgebraicGeometry.RingedToposSiteHom` — the
site-presented morphism of ringed topoi over which the pushforward and the pullback of sheaves
of modules of Stacks 03D6, and therefore the derived pullback of Stacks 06YY, are stated —
consists of exactly the same two data, except that it asks only for *continuity* of `u` rather
than for `u` to be a morphism of sites.

So a morphism of ringed sites is a site-presented morphism of ringed topoi, on the nose: that
is `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` below. The point of the declaration
is not its content but its target: `AlgebraicGeometry.RingedSite.Hom.ringedToposHom`, the other
passage from a morphism of ringed sites to a morphism of ringed topoi, lands in the abstract
`AlgebraicGeometry.RingedToposHom`, which records the geometric morphism as an adjoint pair and
over which no derived pullback is available. Everything stated for a
`RingedToposSiteHom` — the pullback and pushforward of sheaves of modules, their adjunction,
the derived pullback and its composition formula — therefore becomes available along a
morphism of ringed sites only through this declaration.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom`: a morphism of ringed sites read as a
  site-presented morphism of ringed topoi, for Stacks 01D3 part (2).

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isMorphismOfSites_toRingedToposSiteHom`: the underlying
  functor is a morphism of sites, which is the hypothesis the derived development asks for
  separately and which a morphism of ringed sites carries.
* `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom_comp`: the passage is functorial, for
  Stacks 01D3 part (3) and Stacks 03AD part (3).
* `AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive`: the pushforward of sheaves of
  modules along a morphism of ringed sites is additive.

## Implementation notes

The three universes of the ringed site are collapsed, as they already are in
`AlgebraicGeometry.RingedSite.Hom`: `CategoryTheory.Functor.IsMorphismOfSites` is stated for
sheaves of sets valued in the universe of the site, so a morphism of ringed sites whose
structure sheaf has larger sections cannot be read as a morphism of ringed topoi at all. See
the module docstring of
`StacksFrontier/CategoryTheory/Sites/Modules/LocalizationRingedSites/LocalizedMorphism.lean`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSite

variable {X Y Z : RingedSite.{u, u, u}}

/-- **Stacks 01D3 part (2) for a morphism of ringed sites.** A morphism of ringed sites, read
as a site-presented morphism of ringed topoi: the two structures have the same two fields, a
functor between the underlying sites in the opposite direction and a structure map in
direct-image form, and a morphism of sites is in particular continuous.

This is the form in which the pushforward and the pullback of sheaves of modules of
Stacks 03D6, and the derived pullback of Stacks 06YY, are available along a morphism of ringed
sites. -/
def Hom.toRingedToposSiteHom (f : RingedSite.Hom X Y) :
    AlgebraicGeometry.RingedToposSiteHom (ringedTopos X) (ringedTopos Y) where
  u := f.u
  isContinuous := f.isMorphismOfSites.isContinuous
  fSharp := f.fsharp

/-- The functor underlying `f.toRingedToposSiteHom` is the functor `f.u` of `f`. -/
@[simp]
theorem Hom.toRingedToposSiteHom_u (f : RingedSite.Hom X Y) :
    f.toRingedToposSiteHom.u = f.u :=
  rfl

/-- The structure map of `f.toRingedToposSiteHom` is the structure map `f.fsharp` of `f`. -/
@[simp]
theorem Hom.toRingedToposSiteHom_fSharp (f : RingedSite.Hom X Y) :
    f.toRingedToposSiteHom.fSharp = f.fsharp :=
  rfl

/-- The functor underlying the site-presented morphism of ringed topoi of a morphism of ringed
sites is a morphism of sites. The derived development asks for this as a hypothesis separate
from the morphism, so it is recorded here in the spelling that hypothesis uses. -/
theorem Hom.isMorphismOfSites_toRingedToposSiteHom (f : RingedSite.Hom X Y) :
    f.toRingedToposSiteHom.u.IsMorphismOfSites (ringedTopos Y).J (ringedTopos X).J :=
  f.isMorphismOfSites

/-- **Stacks 01D3 part (3) and Stacks 03AD part (3).** The passage from a morphism of ringed
sites to a site-presented morphism of ringed topoi is functorial: it carries the composition of
morphisms of ringed sites to the composition of morphisms of ringed topoi. Both composites are
built from the same two data in the same way, so the two sides are equal. -/
theorem Hom.toRingedToposSiteHom_comp (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z) :
    (f.comp g).toRingedToposSiteHom =
      AlgebraicGeometry.RingedToposSiteHom.comp g.toRingedToposSiteHom f.toRingedToposSiteHom :=
  rfl

attribute [local instance] hasSheafCompose_forget₂_ringCat

/-- Additivity of the pushforward of sheaves of modules along a morphism of ringed sites. This
is `AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos_additive` at the universes of a
morphism of ringed sites: that instance is stated for a morphism of ringed topoi, whose two
universes the shape of `CategoryTheory.Functor.Additive` does not determine, so instance search
does not find it at the site-presented spelling and it is instantiated here instead.

It is not registered as a global instance: it is the instance argument of
`CategoryTheory.Functor.mapHomotopyCategory`, so the derived development needs the term, and a
second proof of it would give a second degreewise direct image. Consumers enable it with
`attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive`. -/
theorem Hom.pushforwardTopos_additive (f : RingedSite.Hom X Y) :
    f.toRingedToposSiteHom.pushforwardTopos.Additive :=
  AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos_additive.{u} _

end AlgebraicGeometry.RingedSite

end
