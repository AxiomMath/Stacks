module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleRingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtalePushforwardModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOnRingedTopoiUnconditional
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image of modules on the big and small étale sites (Stacks 0DGA, part 2)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and let `f : Y ⟶ X` be a
morphism of its objects. Restriction to the spaces-étale site commutes with the unbounded
derived direct image of sheaves of `𝒪`-modules: this is part (2) of the source, stated as a
natural isomorphism of functors between unbounded derived categories rather than only an
isomorphism at each object.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleRestrictionRingedHom`,
  `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedSiteHom` and
  `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleRingedSiteHom` — the comparison morphism `π_X`
  and the morphisms `f_big` and `f_small`, as morphisms of ringed topoi. Their direct images of
  sheaves of modules are, on the nose, the three functors of Tag 0DG9; that is
  `spacesEtaleRestrictionRingedHom_pushforwardTopos` and its two companions.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.derivedBigSmallEtaleModulePushforwardIso` — part (2) of
  the source.
* `AlgebraicGeometry.BigEtaleSpaceSite.restrictModules_preservesFiniteLimits` and
  `AlgebraicGeometry.BigEtaleSpaceSite.restrictModules_preservesFiniteColimits` — restriction of
  sheaves of modules to the spaces-étale site is exact, which is the source's reason for
  `Rπ_{X,*} = π_{X,*}`.

## Implementation notes

The source's argument is used unchanged: `π_X ∘ f_big = f_small ∘ π_Y` as morphisms of ringed
sites, so `Rπ_{X,*} ∘ Rf_{big,*} = Rf_{small,*} ∘ Rπ_{Y,*}` by Tag 0D6E (Cohomology on Sites,
Lemma 21.19.2), and the restriction functors are exact, so their derived functors are
themselves. In Lean both composites are exhibited as right derived functors of the direct image
along the composite morphism of ringed topoi — that is
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.isRightDerivedFunctor_comp`, whose
hypothesis is discharged on the left by exactness of `π_{X,*}` and on the right by the
unconditional form of Tag 0D6E,
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardComputesDerived` — and the
two underlying functors are identified by the underived comparison of Tag 0DG9 for sheaves of
modules. `CategoryTheory.Functor.rightDerivedNatIso` then transports that identification.

Note that the K-injectivity argument of part (1) is *not* available here: Tag 0DG8 fails for
sheaves of modules, as the source itself records. The composition formula of Tag 0D6E, which
for modules is proved by uniqueness of adjoints rather than by preservation of K-injectives, is
what replaces it; its hypotheses are the two morphism-of-sites assertions
`AlgebraicGeometry.BigEtaleSpaceSite.inclusion_isMorphismOfSites` (Tag 0DF3) and
`AlgebraicGeometry.Space.spacesBaseChange_isMorphismOfSites`.

The statement is written with the direct images of the three morphisms of ringed topoi rather
than with the abbreviations of Tag 0DG9, because that is the spelling the composition machinery
produces and the two agree by `rfl`; the three identification lemmas record that agreement.

## References

* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
* [Stacks Project, Tag 0DG9](https://stacks.math.columbia.edu/tag/0DG9)
* [Stacks Project, Tag 0DG8](https://stacks.math.columbia.edu/tag/0DG8)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi (isRightDerivedFunctor_comp
  derivedPushforwardCompUnit pushforwardComputesDerived pushforwardComputesDerived_of_isIso)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPushforward
  derivedPushforwardUnit)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### The three morphisms of ringed topoi -/

/-- The comparison morphism `π_X` from the big étale ringed topos of `X` to its spaces-étale
ringed topos: the inclusion of the spaces-étale site, with the identity structure map. -/
def spacesEtaleRestrictionRingedHom (X : T.Spaces) :
    RingedToposSiteHom (bigEtaleRingedTopos T X)
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X) where
  u := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X
  fSharp := 𝟙 _

variable {X Y : T.Spaces}

/-- The morphism of big étale ringed topoi `f_big` attached to `f : Y ⟶ X`. -/
def bigEtaleRingedSiteHom (f : Y ⟶ X) :
    RingedToposSiteHom (bigEtaleRingedTopos T Y) (bigEtaleRingedTopos T X) where
  u := Over.pullback f
  fSharp := ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op (overPullbackProjection T f))
      (Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem))

/-- The morphism of spaces-étale ringed topoi `f_small` attached to `f : Y ⟶ X`. -/
def smallEtaleRingedSiteHom (f : Y ⟶ X) :
    RingedToposSiteHom (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X) where
  u := (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
  isContinuous := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
  fSharp := ObjectProperty.homMk
    (Functor.whiskerRight
      (NatTrans.op (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).projection)
      (Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem))

/-- The direct image of modules along `π_X` is restriction to the spaces-étale site. -/
theorem spacesEtaleRestrictionRingedHom_pushforwardTopos (X : T.Spaces) :
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos = restrictModules.{u, u + 1} T X :=
  rfl

/-- The direct image of modules along `f_big` is the big étale direct image of modules. -/
theorem bigEtaleRingedSiteHom_pushforwardTopos (f : Y ⟶ X) :
    (bigEtaleRingedSiteHom T f).pushforwardTopos = bigEtaleModulePushforward.{u, u + 1} T f :=
  rfl

/-- The direct image of modules along `f_small` is the small étale direct image of modules. -/
theorem smallEtaleRingedSiteHom_pushforwardTopos (f : Y ⟶ X) :
    (smallEtaleRingedSiteHom T f).pushforwardTopos = smallEtaleModulePushforward.{u, u + 1} T f :=
  rfl

/-! ### Additivity of the three direct images -/

/-- The direct image of modules along `π_X` is additive. -/
instance spacesEtaleRestrictionRingedHom_additive (X : T.Spaces) :
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive (spacesEtaleRestrictionRingedHom T X)

/-- The direct image of modules along `f_big` is additive. -/
instance bigEtaleRingedSiteHom_additive (f : Y ⟶ X) :
    (bigEtaleRingedSiteHom T f).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive (bigEtaleRingedSiteHom T f)

/-- The direct image of modules along `f_small` is additive. -/
instance smallEtaleRingedSiteHom_additive (f : Y ⟶ X) :
    (smallEtaleRingedSiteHom T f).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive (smallEtaleRingedSiteHom T f)

/-- The direct image of modules along `π_X ∘ f_big` is additive. -/
instance bigThenRestrict_additive (f : Y ⟶ X) :
    ((spacesEtaleRestrictionRingedHom T X).comp
      (bigEtaleRingedSiteHom T f)).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive
    ((spacesEtaleRestrictionRingedHom T X).comp (bigEtaleRingedSiteHom T f))

/-- The direct image of modules along `f_small ∘ π_Y` is additive. -/
instance restrictThenSmall_additive (f : Y ⟶ X) :
    ((smallEtaleRingedSiteHom T f).comp
      (spacesEtaleRestrictionRingedHom T Y)).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive
    ((smallEtaleRingedSiteHom T f).comp (spacesEtaleRestrictionRingedHom T Y))

/-! ### Exactness of restriction to the small étale site -/

/-- The inclusion of the spaces-étale site into the big étale site is cocontinuous, being the
`f = 𝟙 X` case of the functor of Tag 0DF2. -/
instance spacesEtaleInclusion_isCocontinuous (X : T.Spaces) :
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).IsCocontinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X) :=
  Functor.IsCocontinuous.of_iso (inclusionFunctorIdIso T X)

/-- Restriction of sheaves of modules to the spaces-étale site is left exact. -/
instance restrictModules_preservesFiniteLimits (X : T.Spaces) :
    PreservesFiniteLimits (restrictModules.{u, u + 1} T X) :=
  Stacks.SheafOfModules.restriction_preservesFiniteLimits
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (bigEtaleRingSheaf T X)

/-- Restriction of sheaves of modules to the spaces-étale site is right exact. -/
instance restrictModules_preservesFiniteColimits (X : T.Spaces) :
    PreservesFiniteColimits (restrictModules.{u, u + 1} T X) :=
  Stacks.SheafOfModules.restriction_preservesFiniteColimits
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (bigEtaleRingSheaf T X)

/-- The direct image of modules along `π_X` is left exact. -/
instance spacesEtaleRestrictionRingedHom_preservesFiniteLimits (X : T.Spaces) :
    PreservesFiniteLimits (spacesEtaleRestrictionRingedHom T X).pushforwardTopos :=
  restrictModules_preservesFiniteLimits T X

/-- The direct image of modules along `π_X` is right exact. -/
instance spacesEtaleRestrictionRingedHom_preservesFiniteColimits (X : T.Spaces) :
    PreservesFiniteColimits (spacesEtaleRestrictionRingedHom T X).pushforwardTopos :=
  restrictModules_preservesFiniteColimits T X

/-! ### The derived direct images -/

attribute [local instance] HasDerivedCategory.standard

/-- Restriction to the spaces-étale site is exact, so the functor it induces on unbounded
derived categories of sheaves of modules is its own total right derived functor. -/
instance restrictModules_mapDerivedCategory_isRightDerivedFunctor (X : T.Spaces) :
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategory.IsRightDerivedFunctor
      (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T X).O))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategoryFactorsh

/-- **Stacks 0DG9 for sheaves of modules**, read on the direct images of the three morphisms of
ringed topoi: `π_X ∘ f_big = f_small ∘ π_Y` on sheaves of `𝒪`-modules. -/
def moduleRestrictionCommIso (f : Y ⟶ X) :
    (bigEtaleRingedSiteHom T f).pushforwardTopos ⋙
        (spacesEtaleRestrictionRingedHom T X).pushforwardTopos ≅
      (spacesEtaleRestrictionRingedHom T Y).pushforwardTopos ⋙
        (smallEtaleRingedSiteHom T f).pushforwardTopos :=
  bigSmallEtale_restrictPushforwardModulesIso.{u, u + 1} T f

/-- The comparison of the two composite direct images of sheaves of modules, read on the
unbounded homotopy categories. -/
def moduleRestrictionCommIsoHomotopy (f : Y ⟶ X) :
    ((spacesEtaleRestrictionRingedHom T X).comp
          (bigEtaleRingedSiteHom T f)).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) ≅
      ((smallEtaleRingedSiteHom T f).comp
          (spacesEtaleRestrictionRingedHom T Y)).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (RingedToposSiteHom.pushforwardToposCompIso (bigEtaleRingedSiteHom T f)
        (spacesEtaleRestrictionRingedHom T X)).symm (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomotopyCategoryCompIso (moduleRestrictionCommIso T f) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((spacesEtaleRestrictionRingedHom T Y).pushforwardTopos ⋙
        (smallEtaleRingedSiteHom T f).pushforwardTopos)) (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomotopyCategoryCompIso
      (RingedToposSiteHom.pushforwardToposCompIso (spacesEtaleRestrictionRingedHom T Y)
        (smallEtaleRingedSiteHom T f)).symm (ComplexShape.up ℤ)

/-- The comparison of the two composite direct images of sheaves of modules, read on the
unbounded derived categories: this is the functor on homotopy categories of which both sides of
part (2) are right derived functors. -/
def moduleRestrictionCommIsoDerived (f : Y ⟶ X) :
    Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardToDerivedCategory.{u + 1,
        u + 2} ((spacesEtaleRestrictionRingedHom T X).comp (bigEtaleRingedSiteHom T f)) ≅
      Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardToDerivedCategory.{u + 1,
        u + 2} ((smallEtaleRingedSiteHom T f).comp (spacesEtaleRestrictionRingedHom T Y)) :=
  Functor.isoWhiskerRight (moduleRestrictionCommIsoHomotopy T f) DerivedCategory.Qh

/-- The comparison transformation of the left-hand composite of part (2): derived big étale
direct image followed by restriction to the small étale site of `X`. -/
abbrev derivedRestrictAfterBigUnit (f : Y ⟶ X) :=
  derivedPushforwardCompUnit (bigEtaleRingedSiteHom T f)
    (spacesEtaleRestrictionRingedHom T X)
    (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategory
    (derivedPushforwardUnit.{u + 1} (bigEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategoryFactorsh.inv

/-- The comparison transformation of the right-hand composite of part (2): restriction to the
small étale site of `Y` followed by derived small étale direct image. -/
abbrev derivedSmallAfterRestrictUnit (f : Y ⟶ X) :=
  derivedPushforwardCompUnit (spacesEtaleRestrictionRingedHom T Y)
    (smallEtaleRingedSiteHom T f)
    (spacesEtaleRestrictionRingedHom T Y).pushforwardTopos.mapDerivedCategory
    (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionRingedHom T Y).pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f))

/-- The left-hand composite of part (2) is a right derived functor of the direct image along
`π_X ∘ f_big`: the restriction functor is exact, so its comparison transformation is already
invertible and the hypothesis of the composition formula is automatic. -/
instance derivedRestrictAfterBig_isRightDerivedFunctor (f : Y ⟶ X) :
    (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f) ⋙
        (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategory
      ).IsRightDerivedFunctor (derivedRestrictAfterBigUnit T f)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
          (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp (bigEtaleRingedSiteHom T f) (spacesEtaleRestrictionRingedHom T X)
    (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategory
    (derivedPushforwardUnit.{u + 1} (bigEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (pushforwardComputesDerived_of_isIso
      (bigEtaleRingedSiteHom T f) (spacesEtaleRestrictionRingedHom T X)
      (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategory
      (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (Iso.isIso_inv _))

/-- The right-hand composite of part (2) is a right derived functor of the direct image along
`f_small ∘ π_Y`: this is the composition formula of Tag 0D6E, whose hypothesis holds
unconditionally for morphisms of ringed topoi. -/
instance derivedSmallAfterRestrict_isRightDerivedFunctor (f : Y ⟶ X) :
    ((spacesEtaleRestrictionRingedHom T Y).pushforwardTopos.mapDerivedCategory ⋙
        derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f)
      ).IsRightDerivedFunctor (derivedSmallAfterRestrictUnit T f)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
          (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp (spacesEtaleRestrictionRingedHom T Y)
    (smallEtaleRingedSiteHom T f)
    (spacesEtaleRestrictionRingedHom T Y).pushforwardTopos.mapDerivedCategory
    (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionRingedHom T Y).pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f))
    (pushforwardComputesDerived
      (spacesEtaleRestrictionRingedHom T Y) (smallEtaleRingedSiteHom T f)
      (inclusion_isMorphismOfSites T Y)
      (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f)
      (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f))
      (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f)))

/-- **Stacks Project, Tag 0DGA, part (2).** Derived big étale direct image of sheaves of
`𝒪`-modules followed by restriction to the small étale site of `X` agrees naturally with
restriction to the small étale site of `Y` followed by derived small étale direct image. -/
@[stacks 0DGA "big_small_modules"]
def derivedBigSmallEtaleModulePushforwardIso (f : Y ⟶ X) :
    derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f) ⋙
        (spacesEtaleRestrictionRingedHom T X).pushforwardTopos.mapDerivedCategory ≅
      (spacesEtaleRestrictionRingedHom T Y).pushforwardTopos.mapDerivedCategory ⋙
        derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f) :=
  Functor.rightDerivedNatIso _ _
    (derivedRestrictAfterBigUnit T f) (derivedSmallAfterRestrictUnit T f)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
      (ComplexShape.up ℤ))
    (moduleRestrictionCommIsoDerived T f)

end AlgebraicGeometry.BigEtaleSpaceSite

end
