module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism of ringed sites at independent universes, read as a morphism of ringed topoi

`AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` reads a morphism of ringed sites as a
site-presented morphism of ringed topoi, which is the form in which the pushforward and the
pullback of sheaves of modules of Stacks 03D6, and the derived pullback of Stacks 06YY, are
available.  It is stated for `AlgebraicGeometry.RingedSite.Hom`, whose endpoints lie in
`RingedSite.{u, u, u}`, so the objects of a site, its morphisms and the sections of its
structure sheaf are forced into one universe and no site of schemes qualifies.

This file gives the same passage for `AlgebraicGeometry.RingedSite.HomGeneral`, the morphism of
ringed sites whose source and target may have different object and morphism universes, and
records the resulting pullback and pushforward of sheaves of modules.  The two structures again
carry the same two data — a functor between the underlying sites in the opposite direction and a
structure map in direct-image form — and a morphism of sites is in particular continuous, so the
passage has no content beyond its target.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposSiteHom`: a morphism of ringed sites at
  independent universes, read as a site-presented morphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesGeneral`: the pushforward
  `f_* : Mod(O_X) ⥤ Mod(O_Y)` of sheaves of modules along it.
* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneral`: the pullback
  `f^* : Mod(O_Y) ⥤ Mod(O_X)`, and
  `AlgebraicGeometry.RingedSite.HomGeneral.pullbackAdjPushforwardModulesGeneral`, the adjunction
  between them.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.isMorphismOfSites_toRingedToposSiteHom`: the
  underlying functor is a morphism of sites.
* `AlgebraicGeometry.RingedSite.Hom.toHomGeneral_toRingedToposSiteHom`: the passage agrees with
  `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` on the morphisms of ringed sites where
  the latter is defined, by `rfl`.

## Implementation notes

The site condition of `HomGeneral` is the unrestricted `IsMorphismOfSites`, which asks that the
direct image on sheaves of sets admit a left exact left adjoint; a `RingedToposSiteHom` asks only
for continuity of the functor, which `IsMorphismOfSites.toIsContinuous` supplies.  In the other
direction `AlgebraicGeometry.RingedSite.Hom.ofRingedToposSiteHom` of
`StacksFrontier/CategoryTheory/Sites/Modules/RingedToposModulesPullbackTopos.lean` reads a
site-presented morphism of ringed topoi whose functor is a morphism of sites as a morphism of
ringed sites; no such converse is stated here, because the two site conditions are different
predicates and the comparison between them is
`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites`, available only on a small site.

The pullback is `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, so it carries that
declaration's hypotheses: the source site essentially small and the target site locally small in
the universe `w` of the sections of the structure sheaves, together with sheafification of
abelian presheaves on the target site.  For the small étale site of a scheme those are exactly
the conditions that hold and `SmallCategory` does not.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- **Stacks 01D3 part (2) for a morphism of ringed sites at independent universes.**  A
morphism of ringed sites whose source and target may have different object and morphism
universes, read as a site-presented morphism of ringed topoi: the two structures have the same
two fields, a functor between the underlying sites in the opposite direction and a structure map
in direct-image form, and a morphism of sites is in particular continuous. -/
def HomGeneral.toRingedToposSiteHom (f : HomGeneral X Y) :
    AlgebraicGeometry.RingedToposSiteHom (toRingedTopos X) (toRingedTopos Y) where
  u := f.u
  isContinuous := f.isMorphismOfSites.toIsContinuous
  fSharp := f.fsharp

/-- The functor underlying `f.toRingedToposSiteHom` is the functor `f.u`. -/
@[simp]
theorem HomGeneral.toRingedToposSiteHom_u (f : HomGeneral X Y) :
    f.toRingedToposSiteHom.u = f.u :=
  rfl

/-- The structure map of `f.toRingedToposSiteHom` is the structure map `f.fsharp`. -/
@[simp]
theorem HomGeneral.toRingedToposSiteHom_fSharp (f : HomGeneral X Y) :
    f.toRingedToposSiteHom.fSharp = f.fsharp :=
  rfl

/-- The functor underlying the site-presented morphism of ringed topoi of a morphism of ringed
sites at independent universes is a morphism of sites. -/
theorem HomGeneral.isMorphismOfSites_toRingedToposSiteHom (f : HomGeneral X Y) :
    _root_.IsMorphismOfSites.{w} f.toRingedToposSiteHom.u
      (toRingedTopos Y).J (toRingedTopos X).J :=
  f.isMorphismOfSites

section Modules

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **Stacks 03D6 part (1) for a morphism of ringed sites at independent universes.**  The
pushforward of sheaves of modules: the underlying sheaf of abelian groups is the direct image
`f_* F`, and the module structure is restriction of scalars along `f^♯ : O_Y ⟶ f_* O_X`. -/
@[sga "4 Vbis 1.3.6" "special case"]
def HomGeneral.pushforwardModulesGeneral (f : HomGeneral X Y) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O) :=
  f.toRingedToposSiteHom.pushforwardTopos

/-- The pushforward of sheaves of modules is additive: on underlying presheaves of modules it is
precomposition with `u.op`, which is additive on the nose. -/
instance HomGeneral.pushforwardModulesGeneral_additive (f : HomGeneral X Y) :
    f.pushforwardModulesGeneral.Additive :=
  AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos_additive f.toRingedToposSiteHom

variable [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D6 part (2) for a morphism of ringed sites at independent universes.**  The
pullback of sheaves of modules, characterised as the left adjoint of the pushforward. -/
def HomGeneral.pullbackModulesGeneral (f : HomGeneral X Y) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) :=
  f.toRingedToposSiteHom.pullbackToposGeneral

/-- **Stacks 03D7 for a morphism of ringed sites at independent universes.**  The pullback of
sheaves of modules is left adjoint to the pushforward. -/
def HomGeneral.pullbackAdjPushforwardModulesGeneral (f : HomGeneral X Y) :
    f.pullbackModulesGeneral ⊣ f.pushforwardModulesGeneral :=
  f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral

/-- The pullback of sheaves of modules is additive, being a left adjoint of the additive functor
`pushforwardModulesGeneral`. -/
instance HomGeneral.pullbackModulesGeneral_additive (f : HomGeneral X Y) :
    f.pullbackModulesGeneral.Additive :=
  AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral_additive f.toRingedToposSiteHom

end Modules

/-- The passage of a morphism of ringed sites at independent universes to a site-presented
morphism of ringed topoi extends `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom`: on a
morphism of ringed sites in a single universe the two produce the same morphism of ringed
topoi. -/
theorem Hom.toHomGeneral_toRingedToposSiteHom {X Y : RingedSite.{w, w, w}} (f : Hom X Y) :
    f.toHomGeneral.toRingedToposSiteHom = f.toRingedToposSiteHom :=
  rfl

end AlgebraicGeometry.RingedSite

end
