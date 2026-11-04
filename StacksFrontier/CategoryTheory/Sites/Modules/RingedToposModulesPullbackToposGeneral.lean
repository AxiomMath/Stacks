module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSiteGeneral

/-!
# The two pullbacks of sheaves of modules along a morphism of ringed sites, at independent
universes

A morphism of ringed sites gives rise to two constructions of `f^*` on sheaves of modules, and
they are built from different presentations of the same geometric morphism.

* `Stacks.Sheaves.RingedToposModules.pullbackModules`, Stacks 03D6 part (2) of the modules
  development, is taken along a *four-field* morphism of ringed topoi: an adjoint pair on sheaves
  of sets together with a structure map.  It is the inverse image of Stacks 03D2 followed by
  extension of scalars along the inverse-image form of the structure map.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral` is taken along the *site-presented*
  morphism, and is `AlgebraicGeometry.SheafOfModules.pullback` of the direct-image form of the
  structure map, i.e. a chosen left adjoint of the pushforward.

`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`
(`StacksFrontier/CategoryTheory/Sites/Modules/RingedToposModulesPullbackTopos.lean`) identifies the
two, but only for `RingedSite.{u, u, u}`: the objects of both underlying sites, their morphisms
and the sections of both structure sheaves are forced into one universe.  Every site of schemes
in this development has objects in `Type (u + 1)` and morphisms and sections in `Type u`, so that
identification is not available for any of them.

This file carries it out for `AlgebraicGeometry.RingedSite.HomGeneral`, at independent object and
morphism universes, with the two sections universes still agreeing — which is all a `HomGeneral`
asks for.  The mathematics is unchanged from the single-universe case and so is the proof; what
is new is only that none of the ingredients needed the universes to agree.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.sectionsComparisonGeneral`: the sections over `Z` of
  the direct image of a sheaf of sets are the sections over `u(Z)`, on the nose.
* `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposObjIsoGeneral` and
  `pushforwardToposIsoGeneral`: the two pushforwards of sheaves of modules agree.
* `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral`: the same with the
  modules development's pushforward on the left.
* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`: **the two pullbacks
  of sheaves of modules agree**, by uniqueness of left adjoints.

## Implementation notes

The comparison of the pushforwards is the identity on underlying sheaves of sets.  Both functors
have the direct image `f_* F` as underlying sheaf of abelian groups; what differs is how the
scalar action is produced — by transport along the adjoint pair for the modules development, by
restriction of scalars along `f^♯` for the site-presented one — and the two agree because the
direct image followed by sections over `Z` *is* sections over `u(Z)`, which is what
`sectionsComparisonGeneral` records.  So the components are built with
`Stacks.Sheaves.RingedToposModules.ofSheafHom` out of the identity of the underlying sheaf, and
every equation between morphisms of modules is checked on underlying sheaves of sets by
`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`.

The declarations are stated for a `HomGeneral` between `RingedSite` *variables* rather than at
any particular pair of sites.  That is not only for generality: the typeclass hypotheses of
`CategoryTheory.Sheaf.app_moduleAddObj` include
`CategoryTheory.Limits.PreservesFiniteProducts` of the direct image composed with a sections
functor, and at a concrete ringed site packaged as a `def` the ambient category instance is a
projection that does not reduce at instance transparency, so that hypothesis is not found.  With
the sites left as variables the projections are variables too and instance search matches
directly.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (f : HomGeneral X Y)

/-- The sections over `Z` of the direct image of a sheaf of sets along a morphism of ringed sites
at independent universes are the sections over `u(Z)`: the direct image is restriction along `u`,
so the composite of the direct image with the sections functor at `Z` is the sections functor at
`u(Z)`, on the nose.

This transformation is the identity on sections; its purpose is to let
`CategoryTheory.Sheaf.app_moduleAddObj` and `CategoryTheory.Sheaf.app_moduleSMulObj` read the
structure transported along the direct image as the structure of the sections over `u(Z)`. -/
public def HomGeneral.sectionsComparisonGeneral (Z : Y.Cᵒᵖ) :
    (f.toposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z) ⟶
      Sheaf.sectionsFunctor X.J (f.u.op.obj Z) where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **The two pushforwards of a sheaf of modules along a morphism of ringed sites at independent
universes agree.**  The underlying sheaf of sets is the direct image on both sides and the
comparison is the identity there; the transported addition and scalar action of the
topos-theoretic pushforward are the restricted ones of the site-presented pushforward because the
direct image followed by sections over `Z` is sections over `u(Z)`.

That the scalars are restricted along the same morphism of sheaves of rings is definitional: the
structure map of `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` is `f^♯` composed with
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, and that identification is the identity on
sections. -/
public def HomGeneral.pushforwardToposObjIsoGeneral
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) :
    f.toRingedToposHom.pushforwardModules.obj F ≅
      f.toRingedToposSiteHom.pushforwardTopos.obj F where
  hom := ofSheafHom (𝟙 _)
    (fun Z x y => Sheaf.app_moduleAddObj _ F (f.sectionsComparisonGeneral Z) x y)
    (fun Z _ x => Sheaf.app_moduleSMulObj _ F (f.sectionsComparisonGeneral Z) _ x)
  inv := ofSheafHom (𝟙 _)
    (fun Z x y => (Sheaf.app_moduleAddObj _ F (f.sectionsComparisonGeneral Z) x y).symm)
    (fun Z _ x => (Sheaf.app_moduleSMulObj _ F (f.sectionsComparisonGeneral Z) _ x).symm)
  hom_inv_id := hom_ext_moduleSheafFunctor rfl
  inv_hom_id := hom_ext_moduleSheafFunctor rfl

/-- **Stacks 03D6 part (1) is independent of the presentation of the morphism of ringed topoi, at
independent universes.**  The pushforward of sheaves of modules built from the adjoint-pair
presentation of the geometric morphism of a morphism of ringed sites is the pushforward built
from its presentation by the functor of the underlying sites.  The components are
`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposObjIsoGeneral` and naturality holds on
underlying sheaves of sets, where both functors are the direct image. -/
public def HomGeneral.pushforwardToposIsoGeneral :
    f.toRingedToposHom.pushforwardModules ≅ f.toRingedToposSiteHom.pushforwardTopos :=
  NatIso.ofComponents (fun F => f.pushforwardToposObjIsoGeneral F)
    fun _ => hom_ext_moduleSheafFunctor rfl

/-- The pushforward of sheaves of modules of the modules development, taken along the four-field
morphism of ringed topoi attached to a morphism of ringed sites at independent universes, is the
pushforward along the functor of the underlying sites.

This composes `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`, which compares the
four-field and the two-field presentations, with
`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposIsoGeneral`. -/
public def HomGeneral.pushforwardModulesToposIsoGeneral :
    pushforwardModules f.toRingedToposHom.toRingedToposModulesHom ≅
      f.toRingedToposSiteHom.pushforwardTopos :=
  AlgebraicGeometry.RingedToposHom.pushforwardModulesIso f.toRingedToposHom ≪≫
    f.pushforwardToposIsoGeneral

variable [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D6 part (2) is independent of the presentation of the morphism of ringed topoi, at
independent universes.**  The pullback of sheaves of modules of the modules development, taken
along the four-field morphism of ringed topoi attached to a morphism of ringed sites, is the
pullback along the functor of the underlying sites.

Both are left adjoints of the two pushforwards, which agree by
`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral`, so this is
uniqueness of left adjoints.  It is what carries a property of one pullback — exactness, for
instance — to the other.

This is `AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso` with the two object and
morphism universes of the underlying sites no longer forced to agree with each other or with the
universe of the sections of the structure sheaves; the source site is asked to be essentially
small in that universe rather than small. -/
public def HomGeneral.pullbackModulesToposIsoGeneral :
    f.toRingedToposHom.toRingedToposModulesHom.pullbackModules ≅
      f.toRingedToposSiteHom.pullbackToposGeneral :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules
      f.toRingedToposHom.toRingedToposModulesHom).ofNatIsoRight
        f.pushforwardModulesToposIsoGeneral)
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral

end AlgebraicGeometry.RingedSite

end
