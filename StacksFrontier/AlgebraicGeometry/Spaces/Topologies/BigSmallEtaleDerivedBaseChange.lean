module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforwardModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtalePushforwardModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtaleToposFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedBaseChangeOfModules
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change for derived direct image on big and small étale sites (0DGA, parts 3, 4, 5, 6)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and let
```
  Y' --g'--> Y
  |f'        |f
  V          V
  X' --g---> X
```
be a cartesian square of its objects, so `Y' = Y ×_X X'`. The unbounded derived direct image
along `f` commutes with base change along `g`, in four forms:

* inverse image on the big étale sites, for abelian sheaves — part (5) of the source;
* the same for sheaves of `𝒪`-modules — part (6);
* restriction to the spaces-étale site of `X'`, for abelian sheaves — part (3);
* the same for sheaves of `𝒪`-modules — part (4).

The derived direct images are total right derived functors, and the exact inverse images are
presented by `CategoryTheory.Functor.mapDerivedCategory`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.derivedBigEtaleBaseChangeIso` — part (5): the inverse
  image along `g_{big}` of `Rf_{big,*}` is `Rf'_{big,*}` of the inverse image along `g'_{big}`,
  for abelian sheaves.
* `AlgebraicGeometry.BigEtaleSpaceSite.derivedSmallEtaleBaseChangeIso` — part (3): the
  restriction `i_g^{-1}` of `Rf_{big,*}` is `Rf'_{small,*}` of `i_{g'}^{-1}`, for abelian sheaves.
* `AlgebraicGeometry.BigEtaleSpaceSite.derivedBigEtaleModuleBaseChangeIso` — part (6): the
  statement of part (5) for sheaves of `𝒪`-modules.
* `AlgebraicGeometry.BigEtaleSpaceSite.derivedSmallEtaleModuleBaseChangeIso` — part (4): the
  statement of part (3) for sheaves of `𝒪`-modules, with `i_g^*` and `i_{g'}^*`.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleRestrictionAlongRingedHom` — the comparison
  morphism `i_g` of Tag 0DF2 as a morphism of ringed topoi; its direct image of sheaves of
  modules is `AlgebraicGeometry.BigEtaleSpaceSite.restrictModulesAlong`, that is `i_g^*`.
* `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_bigEtaleModuleRestriction` — Tag 08FI for
  the big étale sites: `g_{big}^*` preserves K-injective complexes of `𝒪`-modules.
* `AlgebraicGeometry.BigEtaleSpaceSite.globalRingSheaf` and
  `.globalRingSheaf_over` — the sheaf of rings of global regular functions on the big étale
  site of all algebraic spaces over `S`, whose restriction to the big étale site of `X` is the
  structure sheaf of `X`.

## References

* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
* [Stacks Project, Tag 0EZ0](https://stacks.math.columbia.edu/tag/0EZ0), base change for a
  localized site, abelian sheaves
* [Stacks Project, Tag 0FN5](https://stacks.math.columbia.edu/tag/0FN5), the same for sheaves
  of modules
* [Stacks Project, Tag 0DF2](https://stacks.math.columbia.edu/tag/0DF2)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 0DF8](https://stacks.math.columbia.edu/tag/0DF8)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E), the composition formula
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.Localization (overPullback overPushforward homotopyToDerived
  derivedOverPushforwardBaseChangeIso derivedModulesPushforwardBaseChangeIso isKInjective_overMap)
open Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi (isRightDerivedFunctor_comp
  derivedPushforwardCompUnit PushforwardComputesDerived pushforwardComputesDerived
  pushforwardComputesDerived_of_isIso)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPushforward
  derivedPushforwardUnit)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard

/-- Inverse image of abelian sheaves along the big étale morphism `g_big` of `g : X' ⟶ X`:
restriction of a sheaf on the big étale site of `X` along composition with `g`. -/
abbrev bigEtalePullback {X X' : T.Spaces} (g : X' ⟶ X) :
    Sheaf (T.bigEtaleTopology X) Ab.{u + 1} ⥤ Sheaf (T.bigEtaleTopology X') Ab.{u + 1} :=
  overPullback T.topology g

/-- Inverse image of abelian sheaves between big étale sites is exact, so the functor it
induces on unbounded derived categories is its own total right derived functor. -/
instance bigEtalePullback_mapDerivedCategory_isRightDerivedFunctor {X X' : T.Spaces}
    (g : X' ⟶ X) :
    (bigEtalePullback T g).mapDerivedCategory.IsRightDerivedFunctor
      (bigEtalePullback T g).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (bigEtalePullback T g).mapDerivedCategoryFactorsh

/-- For a cartesian square of algebraic spaces of the big étale site, the inverse image along
`g_big` of the derived big étale direct image along `f` agrees naturally with the derived big
étale direct image along `f'` of the inverse image along `g'_big`. -/
@[stacks 0DGA "big_base_change_abelian"]
def derivedBigEtaleBaseChangeIso {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (h : IsPullback g' f' f g) :
    ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ)) ⋙
        (bigEtalePullback T g).mapDerivedCategory ≅
      (bigEtalePullback T g').mapDerivedCategory ⋙
        ((bigEtalePushforward T f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology Y') Ab.{u + 1}) (ComplexShape.up ℤ)) :=
  derivedOverPushforwardBaseChangeIso T.topology g' f' f g h _ _ _ _
    (((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ)))
    (((bigEtalePushforward T f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (T.bigEtaleTopology Y') Ab.{u + 1}) (ComplexShape.up ℤ)))
    (bigEtalePullback T g').mapDerivedCategoryFactorsh.inv
    (bigEtalePullback T g).mapDerivedCategoryFactorsh.inv

/-! ### Part (3): restriction of the base change to the small étale site -/

/-- Restriction of abelian sheaves from the big étale site of `Z` to its spaces-étale site,
that is, the direct image along the comparison morphism `π_Z` of Tag 0DF3. -/
abbrev spacesEtaleRestrictionAb (Z : T.Spaces) :
    Sheaf (T.bigEtaleTopology Z) Ab.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) Ab.{u + 1} :=
  (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z).sheafPushforwardContinuous
    Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) (T.bigEtaleTopology Z)

/-- For a cartesian square of algebraic spaces of the big étale site, the restriction to the
spaces-étale site of `X'` of the derived big étale direct image along `f` agrees naturally with
the derived small étale direct image along `f'` of the restriction to the spaces-étale site of
`Y'`. Both restrictions are the inverse image `i_g^{-1}` resp. `i_{g'}^{-1}` of Tag 0DF2,
written as the inverse image along `g_big` resp. `g'_big` followed by restriction to the
spaces-étale site. -/
@[stacks 0DGA "small_base_change_abelian"]
def derivedSmallEtaleBaseChangeIso {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (h : IsPullback g' f' f g) :
    ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ)) ⋙
        (bigEtalePullback T g).mapDerivedCategory ⋙
          (spacesEtaleRestrictionAb T X').mapDerivedCategory ≅
      (bigEtalePullback T g').mapDerivedCategory ⋙
        (spacesEtaleRestrictionAb T Y').mapDerivedCategory ⋙
          ((smallEtalePushforward T f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
                  Ab.{u + 1}) (ComplexShape.up ℤ)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedBigEtaleBaseChangeIso T f g g' f' h)
      (spacesEtaleRestrictionAb T X').mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (bigEtalePullback T g').mapDerivedCategory
      (derivedBigSmallEtalePushforwardIso T f')

/-! ### The sheaf of rings of global regular functions on the whole big étale site -/

/-- The sheaf of commutative rings of global regular functions on the big étale site of the
algebraic spaces over `S`. Its restriction to the big étale site of an algebraic space `X` is
the structure sheaf of `X`. -/
def globalFunctionsSheaf : Sheaf T.topology CommRingCat.{u + 1} :=
  ⟨Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem, globalFunctionsPresheaf_isSheaf T⟩

/-- The sheaf of rings of global regular functions on the big étale site of the algebraic
spaces over `S`, with commutativity forgotten. -/
abbrev globalRingSheaf : Sheaf T.topology RingCat.{u + 1} :=
  (sheafCompose T.topology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (globalFunctionsSheaf T)

/-- The restriction of the sheaf of rings of global regular functions to the big étale site of
`X` is the big étale structure sheaf of `X`. -/
theorem globalRingSheaf_over (X : T.Spaces) :
    (globalRingSheaf T).over X = bigEtaleRingSheaf T X :=
  rfl

/-! ### Exactness of the inverse image of modules between big étale sites -/

/-- Inverse image of sheaves of modules along the big étale morphism `g_big` of `g : X' ⟶ X`:
restriction of a sheaf of modules on the big étale site of `X` along composition with `g`. -/
abbrev bigEtaleModulePullback {X X' : T.Spaces} (g : X' ⟶ X) :
    SheafOfModules.{u + 1} ((globalRingSheaf T).over X) ⥤
      SheafOfModules.{u + 1} ((globalRingSheaf T).over X') :=
  SheafOfModules.overMap.{u + 1} (globalRingSheaf T) g

/-- The inverse image of sheaves of modules between big étale sites is additive. -/
instance bigEtaleModulePullback_additive {X X' : T.Spaces} (g : X' ⟶ X) :
    (bigEtaleModulePullback T g).Additive :=
  ⟨by intros; ext W; rfl⟩

/-- The inverse image of sheaves of modules between big étale sites is left exact. -/
instance bigEtaleModulePullback_preservesFiniteLimits {X X' : T.Spaces} (g : X' ⟶ X) :
    PreservesFiniteLimits (bigEtaleModulePullback T g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits.{u + 1, u + 1,
    u + 1} g

/-- The inverse image of sheaves of modules between big étale sites is right exact. -/
instance bigEtaleModulePullback_preservesFiniteColimits {X X' : T.Spaces} (g : X' ⟶ X) :
    PreservesFiniteColimits (bigEtaleModulePullback T g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits.{u + 1, u + 1,
    u + 1} g

/-- The inverse image of sheaves of modules between big étale sites is exact, so the functor it
induces on unbounded derived categories is its own total right derived functor. -/
instance bigEtaleModulePullback_mapDerivedCategory_isRightDerivedFunctor {X X' : T.Spaces}
    (g : X' ⟶ X) :
    (bigEtaleModulePullback T g).mapDerivedCategory.IsRightDerivedFunctor
      (bigEtaleModulePullback T g).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} ((globalRingSheaf T).over X)) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (bigEtaleModulePullback T g).mapDerivedCategoryFactorsh

/-! ### The derived direct image of modules between big étale sites -/

/-- Direct image of sheaves of modules along the big étale morphism `f_big` of `f : Y ⟶ X`,
in the relocalization presentation of Tag 0FN3. -/
abbrev bigEtaleRelocalizationPushforward {X Y : T.Spaces} (f : Y ⟶ X) :
    SheafOfModules.{u + 1} ((globalRingSheaf T).over Y) ⥤
      SheafOfModules.{u + 1} ((globalRingSheaf T).over X) :=
  Stacks.SheafOfModules.Relocalization.pushforward T.topology (globalRingSheaf T) f

/-- The direct image of sheaves of modules between big étale sites has a total right derived
functor. -/
instance bigEtaleRelocalizationPushforward_hasRightDerivedFunctor {X Y : T.Spaces} (f : Y ⟶ X) :
    (homotopyToDerived (bigEtaleRelocalizationPushforward T f)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} ((globalRingSheaf T).over Y)) (ComplexShape.up ℤ)) :=
  Stacks.DerivedCategory.hasRightDerivedFunctor
    (inferInstance : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} ((globalRingSheaf T).over Y))) _

/-- For a cartesian square of algebraic spaces of the big étale site, the inverse image of
sheaves of `𝒪`-modules along `g_big` of the derived big étale direct image along `f` agrees
naturally with the derived big étale direct image along `f'` of the inverse image along
`g'_big`. -/
@[stacks 0DGA "big_base_change_modules"]
def derivedBigEtaleModuleBaseChangeIso {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (h : IsPullback g' f' f g) :
    (homotopyToDerived (bigEtaleRelocalizationPushforward T f)).totalRightDerived
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u + 1} ((globalRingSheaf T).over Y)) (ComplexShape.up ℤ)) ⋙
        (bigEtaleModulePullback T g).mapDerivedCategory ≅
      (bigEtaleModulePullback T g').mapDerivedCategory ⋙
        (homotopyToDerived (bigEtaleRelocalizationPushforward T f')).totalRightDerived
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u + 1} ((globalRingSheaf T).over Y')) (ComplexShape.up ℤ)) :=
  derivedModulesPushforwardBaseChangeIso T.topology (globalRingSheaf T) g' f' f g h _ _ _ _
    ((homotopyToDerived (bigEtaleRelocalizationPushforward T f)).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} ((globalRingSheaf T).over Y)) (ComplexShape.up ℤ)))
    ((homotopyToDerived (bigEtaleRelocalizationPushforward T f')).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} ((globalRingSheaf T).over Y')) (ComplexShape.up ℤ)))
    (bigEtaleModulePullback T g').mapDerivedCategoryFactorsh.inv
    (bigEtaleModulePullback T g).mapDerivedCategoryFactorsh.inv

/-! ### Part (4): the comparison `i_g` as a morphism of ringed topoi -/

/-- The comparison morphism `i_g` of Tag 0DF2 from the big étale ringed topos of `X` to the
spaces-étale ringed topos of `X'`, attached to `g : X' ⟶ X`: the inclusion functor of Tag 0DF2,
with the identity structure map. For `g = 𝟙 X` this is
`AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleRestrictionRingedHom`. -/
def spacesEtaleRestrictionAlongRingedHom {X X' : T.Spaces} (g : X' ⟶ X) :
    RingedToposSiteHom (bigEtaleRingedTopos T X)
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X') where
  u := inclusionFunctor T g
  fSharp := 𝟙 _

/-- The direct image of modules along `i_g` is restriction of modules to the spaces-étale site
of `X'` along `g`, that is the `i_g^*` of the source's part (4). -/
theorem spacesEtaleRestrictionAlongRingedHom_pushforwardTopos {X X' : T.Spaces} (g : X' ⟶ X) :
    (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos = restrictModulesAlong T g :=
  rfl

/-- The direct image of modules along `i_g` is additive. -/
instance spacesEtaleRestrictionAlongRingedHom_additive {X X' : T.Spaces} (g : X' ⟶ X) :
    (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive (spacesEtaleRestrictionAlongRingedHom T g)

/-- Restriction of sheaves of modules along `i_g` is left exact. -/
instance restrictModulesAlong_preservesFiniteLimits {X X' : T.Spaces} (g : X' ⟶ X) :
    PreservesFiniteLimits (restrictModulesAlong T g) :=
  Stacks.SheafOfModules.restriction_preservesFiniteLimits
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') (T.bigEtaleTopology X)
    (inclusionFunctor T g) (bigEtaleRingSheaf T X)

/-- Restriction of sheaves of modules along `i_g` is right exact. -/
instance restrictModulesAlong_preservesFiniteColimits {X X' : T.Spaces} (g : X' ⟶ X) :
    PreservesFiniteColimits (restrictModulesAlong T g) :=
  Stacks.SheafOfModules.restriction_preservesFiniteColimits
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') (T.bigEtaleTopology X)
    (inclusionFunctor T g) (bigEtaleRingSheaf T X)

/-- The direct image of modules along `i_g` is left exact. -/
instance spacesEtaleRestrictionAlongRingedHom_preservesFiniteLimits {X X' : T.Spaces}
    (g : X' ⟶ X) :
    PreservesFiniteLimits (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos :=
  restrictModulesAlong_preservesFiniteLimits T g

/-- The direct image of modules along `i_g` is right exact. -/
instance spacesEtaleRestrictionAlongRingedHom_preservesFiniteColimits {X X' : T.Spaces}
    (g : X' ⟶ X) :
    PreservesFiniteColimits (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos :=
  restrictModulesAlong_preservesFiniteColimits T g

/-- The structure map of `g_{big}` on the big étale sites: the sections of the direct image of
the big étale structure sheaf of `X` over an algebraic space over `X'` are its own global
regular functions, so the structure map is the identity. -/
def bigEtaleLocalizationSharp {X X' : T.Spaces} (g : X' ⟶ X) :
    bigEtaleRingSheaf T X' ⟶
      ((Over.map g).sheafPushforwardContinuous RingCat.{u + 1}
        (T.bigEtaleTopology X') (T.bigEtaleTopology X)).obj (bigEtaleRingSheaf T X) :=
  𝟙 _

/-- Restriction of a sheaf of `𝒪`-modules between big étale sites along `Over.map g`, that is
the inverse image `g_{big}^*`. -/
abbrev bigEtaleModuleRestriction {X X' : T.Spaces} (g : X' ⟶ X) :
    BigEtaleModules.{u, u + 1} T X ⥤ BigEtaleModules.{u, u + 1} T X' :=
  SheafOfModules.pushforward.{u + 1} (bigEtaleLocalizationSharp T g)

/-- Mathlib's `SheafOfModules.overMap`, read with the big étale structure sheaves spelled as in
`bigEtaleRingSheaf`, is additive. -/
instance overMapPullback_additive' {X X' : T.Spaces} (g : X' ⟶ X) :
    (SheafOfModules.pushforward.{u + 1}
        (Sheaf.pushforwardOverMapIso (globalRingSheaf T) g).inv :
      BigEtaleModules.{u, u + 1} T X ⥤ BigEtaleModules.{u, u + 1} T X').Additive :=
  ⟨by intros; rfl⟩

/-- `g_{big}^*` is isomorphic to Mathlib's `SheafOfModules.overMap`. -/
def bigEtaleModuleRestrictionIsoPullback {X X' : T.Spaces} (g : X' ⟶ X) :
    bigEtaleModuleRestriction T g ≅
      SheafOfModules.pushforward.{u + 1}
        (Sheaf.pushforwardOverMapIso (globalRingSheaf T) g).inv :=
  SheafOfModules.pushforwardCongr.{u + 1}
    (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl)))

/-- **Stacks 08FI for the big étale sites.** The inverse image `g_{big}^*` of sheaves of
`𝒪`-modules carries K-injective complexes to K-injective complexes. -/
theorem isKInjective_bigEtaleModuleRestriction {X X' : T.Spaces} (g : X' ⟶ X)
    (I : CochainComplex (BigEtaleModules.{u, u + 1} T X) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((bigEtaleModuleRestriction T g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (CochainComplex.isKInjective_iff_of_iso
    ((NatIso.mapHomologicalComplex (bigEtaleModuleRestrictionIsoPullback T g)
      (ComplexShape.up ℤ)).app I)).2
    (@isKInjective_overMap _ _ T.topology (globalRingSheaf T) _ _ g I hI)

/-- The factorization `i_g = i_{X'} ∘ g_{big}` of Tag 0DF2 on sheaves of `𝒪`-modules. -/
def restrictModulesAlongFactors {X X' : T.Spaces} (g : X' ⟶ X) :
    restrictModulesAlong T g ≅
      bigEtaleModuleRestriction T g ⋙ restrictModules.{u, u + 1} T X' :=
  (SheafOfModules.pushforwardComp.{u + 1} (restrictSharp T X')
      (bigEtaleLocalizationSharp T g) ≪≫
    SheafOfModules.pushforwardCongr.{u + 1}
      (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl)))).symm

/-! ### Part (4): the derived comparison -/

variable {X Y X' Y' : T.Spaces}

/-- `g_{big}^*` on sheaves of `𝒪`-modules, with the structure sheaves spelled as the ring
sheaves of the big étale ringed topoi. -/
abbrev bigEtaleModuleRestrictionTopos (g : X' ⟶ X) :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T X).O) ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T X').O) :=
  bigEtaleModuleRestriction T g

/-- `g_{big}^*` is additive, in that spelling. -/
instance bigEtaleModuleRestrictionTopos_additive (g : X' ⟶ X) :
    (bigEtaleModuleRestrictionTopos T g).Additive :=
  ⟨by intros; rfl⟩

/-- **Stacks 08FI for the big étale sites**, in that spelling. -/
theorem isKInjective_bigEtaleModuleRestrictionTopos (g : X' ⟶ X)
    (I : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T X).O)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((bigEtaleModuleRestrictionTopos T g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  isKInjective_bigEtaleModuleRestriction T g I hI

/-- The factorization `i_g = i_{X'} ∘ g_{big}`, in that spelling. -/
def restrictModulesAlongFactorsTopos (g : X' ⟶ X) :
    (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos ≅
      bigEtaleModuleRestrictionTopos T g ⋙
        (spacesEtaleRestrictionRingedHom T X').pushforwardTopos :=
  restrictModulesAlongFactors T g

/-- The direct image of modules along `i_g ∘ f_big` is additive. -/
instance bigThenRestrictAlong_additive (f : Y ⟶ X) (g : X' ⟶ X) :
    ((spacesEtaleRestrictionAlongRingedHom T g).comp
      (bigEtaleRingedSiteHom T f)).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive
    ((spacesEtaleRestrictionAlongRingedHom T g).comp (bigEtaleRingedSiteHom T f))

/-- The direct image of modules along `f'_small ∘ i_{g'}` is additive. -/
instance restrictAlongThenSmall_additive (g' : Y' ⟶ Y) (f' : Y' ⟶ X') :
    ((smallEtaleRingedSiteHom T f').comp
      (spacesEtaleRestrictionAlongRingedHom T g')).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive
    ((smallEtaleRingedSiteHom T f').comp (spacesEtaleRestrictionAlongRingedHom T g'))

/-- Restriction of modules along `i_g` is exact, so the functor it induces on unbounded derived
categories is its own total right derived functor. -/
instance restrictModulesAlong_mapDerivedCategory_isRightDerivedFunctor (g : X' ⟶ X) :
    (spacesEtaleRestrictionAlongRingedHom T
        g).pushforwardTopos.mapDerivedCategory.IsRightDerivedFunctor
      (spacesEtaleRestrictionAlongRingedHom T
        g).pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T X).O))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategoryFactorsh

/-- The factorization `i_{g'} = i_{Y'} ∘ g'_{big}` at a single cochain complex, on the unbounded
homotopy categories. -/
def restrictAlongHomotopyIso (g' : Y' ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O)) ℤ) :
    ((spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
        (ComplexShape.up ℤ)).obj I) ≅
      ((spacesEtaleRestrictionRingedHom T Y').pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y').O))
        (ComplexShape.up ℤ)).obj
        (((bigEtaleModuleRestrictionTopos T g').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :=
  (Functor.mapHomotopyCategoryCompIso (restrictModulesAlongFactorsTopos T g').symm
      (ComplexShape.up ℤ)).symm.app _ ≪≫
    ((spacesEtaleRestrictionRingedHom T Y').pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ)).mapIso
      (((bigEtaleModuleRestrictionTopos T g').mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app I)

/-- Restriction of modules to the spaces-étale site of `Y'` carries a K-injective complex of
`𝒪`-modules on the big étale site of `Y'` to a complex computing the derived small étale direct
image along `f'`. -/
theorem pushforwardComputesDerived_restriction (f' : Y' ⟶ X') :
    PushforwardComputesDerived.{u + 1, u + 2, u + 2} (spacesEtaleRestrictionRingedHom T Y')
      (smallEtaleRingedSiteHom T f')
      (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f'))
      (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f')) :=
  pushforwardComputesDerived (spacesEtaleRestrictionRingedHom T Y')
    (smallEtaleRingedSiteHom T f') (inclusion_isMorphismOfSites T Y')
    (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f')
    (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f'))
    (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f'))

/-- Restriction of modules along `i_{g'}` carries a K-injective complex of `𝒪`-modules on the
big étale site of `Y` to a complex computing the derived small étale direct image along `f'`. -/
theorem pushforwardComputesDerived_restrictAlong (f' : Y' ⟶ X') (g' : Y' ⟶ Y) :
    PushforwardComputesDerived.{u + 1, u + 2, u + 2}
      (spacesEtaleRestrictionAlongRingedHom T g')
      (smallEtaleRingedSiteHom T f')
      (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f'))
      (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f')) := fun I hI =>
  (NatTrans.isIso_app_iff_of_iso
    (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f'))
    (restrictAlongHomotopyIso T g' I)).2
    (pushforwardComputesDerived_restriction T f'
      (((bigEtaleModuleRestrictionTopos T g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (isKInjective_bigEtaleModuleRestrictionTopos T g' I hI))

/-- The left-hand composite of part (4) is a right derived functor of the direct image along
`i_g ∘ f_big`. -/
instance derivedRestrictAlongAfterBig_isRightDerivedFunctor (f : Y ⟶ X) (g : X' ⟶ X) :
    (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f) ⋙
        (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategory
      ).IsRightDerivedFunctor
        (derivedPushforwardCompUnit (bigEtaleRingedSiteHom T f)
          (spacesEtaleRestrictionAlongRingedHom T g)
          (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f))
          (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategory
          (derivedPushforwardUnit.{u + 1} (bigEtaleRingedSiteHom T f))
          (spacesEtaleRestrictionAlongRingedHom T
            g).pushforwardTopos.mapDerivedCategoryFactorsh.inv)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
          (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp (bigEtaleRingedSiteHom T f)
    (spacesEtaleRestrictionAlongRingedHom T g)
    (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategory
    (derivedPushforwardUnit.{u + 1} (bigEtaleRingedSiteHom T f))
    (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (pushforwardComputesDerived_of_isIso (bigEtaleRingedSiteHom T f)
      (spacesEtaleRestrictionAlongRingedHom T g)
      (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategory
      (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (Iso.isIso_inv _))

/-- The right-hand composite of part (4) is a right derived functor of the direct image along
`f'_small ∘ i_{g'}`. -/
instance derivedSmallAfterRestrictAlong_isRightDerivedFunctor (f' : Y' ⟶ X') (g' : Y' ⟶ Y) :
    ((spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategory ⋙
        derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f')
      ).IsRightDerivedFunctor
        (derivedPushforwardCompUnit (spacesEtaleRestrictionAlongRingedHom T g')
          (smallEtaleRingedSiteHom T f')
          (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategory
          (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f'))
          (spacesEtaleRestrictionAlongRingedHom T
            g').pushforwardTopos.mapDerivedCategoryFactorsh.inv
          (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f')))
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
          (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp (spacesEtaleRestrictionAlongRingedHom T g')
    (smallEtaleRingedSiteHom T f')
    (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategory
    (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f'))
    (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f'))
    (pushforwardComputesDerived_restrictAlong T f' g')

/-- **Stacks 0DF8 for sheaves of `𝒪`-modules**, read on the direct images of the four morphisms
of ringed topoi of the cartesian square. -/
def moduleBaseChangeCommIso (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (h : IsPullback g' f' f g) :
    (bigEtaleRingedSiteHom T f).pushforwardTopos ⋙
        (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos ≅
      (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos ⋙
        (smallEtaleRingedSiteHom T f').pushforwardTopos :=
  smallEtaleModulePushforwardBaseChangeIso T g' f' f g h

/-- The comparison of the two composite direct images of part (4), on the unbounded homotopy
categories. -/
def moduleBaseChangeCommIsoHomotopy (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (h : IsPullback g' f' f g) :
    ((spacesEtaleRestrictionAlongRingedHom T g).comp
          (bigEtaleRingedSiteHom T f)).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) ≅
      ((smallEtaleRingedSiteHom T f').comp
          (spacesEtaleRestrictionAlongRingedHom T g')).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (RingedToposSiteHom.pushforwardToposCompIso (bigEtaleRingedSiteHom T f)
        (spacesEtaleRestrictionAlongRingedHom T g)).symm (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomotopyCategoryCompIso (moduleBaseChangeCommIso T f g g' f' h)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos ⋙
        (smallEtaleRingedSiteHom T f').pushforwardTopos)) (ComplexShape.up ℤ)).symm ≪≫
    Functor.mapHomotopyCategoryCompIso
      (RingedToposSiteHom.pushforwardToposCompIso (spacesEtaleRestrictionAlongRingedHom T g')
        (smallEtaleRingedSiteHom T f')).symm (ComplexShape.up ℤ)

/-- The same comparison, on the unbounded derived categories. -/
def moduleBaseChangeCommIsoDerived (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (h : IsPullback g' f' f g) :
    Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardToDerivedCategory.{u + 1,
        u + 2} ((spacesEtaleRestrictionAlongRingedHom T g).comp (bigEtaleRingedSiteHom T f)) ≅
      Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.pushforwardToDerivedCategory.{u + 1,
        u + 2} ((smallEtaleRingedSiteHom T f').comp
          (spacesEtaleRestrictionAlongRingedHom T g')) :=
  Functor.isoWhiskerRight (moduleBaseChangeCommIsoHomotopy T f g g' f' h) DerivedCategory.Qh

/-- For a cartesian square of algebraic spaces of the big étale site, the restriction to the
spaces-étale site of `X'` of the derived big étale direct image of sheaves of `𝒪`-modules along
`f` agrees naturally with the derived small étale direct image along `f'` of the restriction to
the spaces-étale site of `Y'`. The two restrictions are the inverse images `i_g^*` and
`i_{g'}^*` of Tag 0DF2 on sheaves of `𝒪`-modules. -/
@[stacks 0DGA "small_base_change_modules"]
def derivedSmallEtaleModuleBaseChangeIso (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (h : IsPullback g' f' f g) :
    derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f) ⋙
        (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategory ≅
      (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategory ⋙
        derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f') :=
  Functor.rightDerivedNatIso _ _
    (derivedPushforwardCompUnit (bigEtaleRingedSiteHom T f)
      (spacesEtaleRestrictionAlongRingedHom T g)
      (derivedPushforward.{u + 1} (bigEtaleRingedSiteHom T f))
      (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategory
      (derivedPushforwardUnit.{u + 1} (bigEtaleRingedSiteHom T f))
      (spacesEtaleRestrictionAlongRingedHom T g).pushforwardTopos.mapDerivedCategoryFactorsh.inv)
    (derivedPushforwardCompUnit (spacesEtaleRestrictionAlongRingedHom T g')
      (smallEtaleRingedSiteHom T f')
      (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategory
      (derivedPushforward.{u + 1} (smallEtaleRingedSiteHom T f'))
      (spacesEtaleRestrictionAlongRingedHom T g').pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (derivedPushforwardUnit.{u + 1} (smallEtaleRingedSiteHom T f')))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedTopos T Y).O))
      (ComplexShape.up ℤ))
    (moduleBaseChangeCommIsoDerived T f g g' f' h)

end AlgebraicGeometry.BigEtaleSpaceSite

end
