module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleKInjective
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image on big and small étale sites of algebraic spaces (Stacks 0DGA)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and let `f : Y ⟶ X` be a
morphism of its objects. Restriction to the spaces-étale site commutes with the unbounded
derived direct image of abelian sheaves (part (1) of Stacks 0DGA), as a natural isomorphism of
functors between unbounded derived categories.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.derivedBigSmallEtalePushforwardIso` — derived direct
  image commutes with restriction to the small étale site.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtalePushforwardIso` — the underived square it
  derives from, which is the composition isomorphism of pushforwards along the commuting
  square of site functors of Tag 0DF6.
* `Stacks.DerivedCategory.rightDerivedUnit_isIso` and
  `Stacks.DerivedCategory.rightDerived_of_KInjective` — two general facts about total right derived
  functors on an unbounded derived category: the comparison transformation of a right derived
  functor is invertible at a K-injective complex, and conversely a transformation invertible at
  every K-injective complex exhibits a right derived functor.
* `Stacks.DerivedCategory.hasRightDerivedFunctor` — every functor out of the homotopy category
  of a Grothendieck abelian category has a total right derived functor; in particular
  `AlgebraicGeometry.BigEtaleSpaceSite.bigEtalePushforward_hasRightDerivedFunctor` and
  `.smallEtalePushforward_hasRightDerivedFunctor` are instances.

## Implementation notes

The derived comparison is `CategoryTheory.Functor.rightDerivedNatIso`: both composites are
right derived functors of the same functor on homotopy categories, because the underived
square makes the two underlying functors isomorphic and restriction preserves K-injectivity
(Tag 0DG8, `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_spacesEtaleRestriction`).

K-injective resolutions are `Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso`
(Tag 079P). The restriction functor is `sheafPushforwardContinuous` for the inclusion of the
spaces-étale site.

The Grothendieck-abelian hypothesis of the three general lemmas is an explicit argument, not
an instance binder: its universe occurs nowhere else in their statements, so as an instance
binder it is not determined by the caller and instance search stops at an unassigned
universe metavariable.

## References

* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
* [Stacks Project, Tag 0DG8](https://stacks.math.columbia.edu/tag/0DG8)
* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.CechAugmentation (exists_isKInjective_quasiIso)

universe v vH w wD uu uH u

namespace Stacks.DerivedCategory

section Generic
variable {C : Type uu} {H : Type uH} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{wD} C] [Category.{vH} H]

/-- For a Grothendieck abelian `C`, the unit `α : F ⟶ Qh ⋙ RF` of a right derived functor of
`F : K(C) ⥤ H` along the quasi-isomorphisms is invertible at every K-injective complex. -/
public theorem rightDerivedUnit_isIso (hGA : IsGrothendieckAbelian.{w} C)
    (F : HomotopyCategory C (.up ℤ) ⥤ H) (RF : DerivedCategory C ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ))]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) :=
  let := hGA
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v,
    vH, wD, uu, uH, max uu v} F exists_isKInjective_quasiIso).2 _ RF α I
      inferInstance

/-- For a Grothendieck abelian `C`, a natural transformation of functors out of `D(C)` that is
invertible at every K-injective complex is an isomorphism. -/
private theorem natTrans_isIso (hGA : IsGrothendieckAbelian.{w} C)
    {F G : DerivedCategory C ⥤ H} (τ : F ⟶ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (τ.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj I)))) : IsIso τ := by
  let := hGA
  suffices ∀ K, IsIso (τ.app K) by
    let := this
    exact NatIso.isIso_of_isIso_app τ
  intro K
  rw [← NatTrans.isIso_app_iff_of_iso τ (DerivedCategory.Qh.objObjPreimageIso K)]
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective
    (DerivedCategory.Qh.objPreimage K)
  rw [← hL]
  obtain ⟨I, q, hI, hq⟩ := exists_isKInjective_quasiIso L
  let := hI
  let := hq
  have hqi : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (.up ℤ)).map q)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  rw [NatTrans.isIso_app_iff_of_iso τ (asIso
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map q)))]
  exact h I

omit [HasDerivedCategory.{wD} C] in
/-- Every functor out of the homotopy category of a Grothendieck abelian category has a total
right derived functor on the unbounded derived category. -/
@[sga "4 XVII 4.1.2" "partial"]
public theorem hasRightDerivedFunctor (hGA : IsGrothendieckAbelian.{w} C)
    (F : HomotopyCategory C (.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso C (.up ℤ)) := by
  let := hGA
  let := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v,
    vH, 0, uu, uH, 0} F exists_isKInjective_quasiIso).1
  infer_instance

/-- For a Grothendieck abelian `C`, a natural transformation `α : F ⟶ Qh ⋙ RF` that is invertible
at every K-injective complex exhibits `RF` as a right derived functor of `F : K(C) ⥤ H` along the
quasi-isomorphisms. -/
public theorem rightDerived_of_KInjective (hGA : IsGrothendieckAbelian.{w} C)
    (F : HomotopyCategory C (.up ℤ) ⥤ H) (RF : DerivedCategory C ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I))) :
    RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ)) := by
  have := hasRightDerivedFunctor hGA F
  let R := F.totalRightDerived DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  let β := F.totalRightDerivedUnit DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc R β]
  apply natTrans_isIso hGA (R.rightDerivedDesc β (HomotopyCategory.quasiIso C (.up ℤ)) RF α)
  intro I hI
  let := hI
  have := rightDerivedUnit_isIso hGA F R β I
  have := h I
  have heq := R.rightDerived_fac_app β (HomotopyCategory.quasiIso C (.up ℤ)) RF α
    ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  exact (isIso_comp_left_iff (β.app _) _).mp (heq ▸ inferInstance)

end Generic

end Stacks.DerivedCategory

open Stacks.DerivedCategory

namespace AlgebraicGeometry.BigEtaleSpaceSite

noncomputable section
variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

attribute [local instance] HasDerivedCategory.standard

/-- Direct image of abelian sheaves on the big étale sites. -/
public abbrev bigEtalePushforward (f : Y ⟶ X) :
    Sheaf (T.bigEtaleTopology Y) Ab.{u + 1} ⥤ Sheaf (T.bigEtaleTopology X) Ab.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous Ab.{u + 1}
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X)

/-- Direct image of abelian sheaves on the small étale sites. -/
public abbrev smallEtalePushforward (f : Y ⟶ X) :
    Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1} :=
  letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
  (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
    |>.sheafPushforwardContinuous Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)

/-- Direct image on the big étale sites is additive, being a right adjoint. -/
public instance bigEtalePushforward_additive : (bigEtalePushforward T f).Additive := by
  let _ := ((Over.map f).sheafAdjunctionCocontinuous Ab.{u + 1}
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- Direct image on the small étale sites is additive. -/
public instance smallEtalePushforward_additive : (smallEtalePushforward T f).Additive := ⟨rfl⟩

/-- Restriction to the spaces-étale site of `Z` is additive. -/
public instance spacesEtaleRestriction_additive (Z : T.Spaces) :
    ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z).sheafPushforwardContinuous
      Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z)
      (T.bigEtaleTopology Z)).Additive := ⟨rfl⟩

/-- Restriction to the spaces-étale site of `Z` preserves finite limits, being a right
adjoint. -/
public instance spacesEtaleRestriction_preservesFiniteLimits (Z : T.Spaces) :
    PreservesFiniteLimits
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z)
        (T.bigEtaleTopology Z)) := by
  let := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z) Ab.{u + 1}
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z)
    (T.bigEtaleTopology Z)).rightAdjoint_preservesLimits
  exact inferInstance

/-- Restriction to the spaces-étale site of `Z` preserves finite colimits, being a left
adjoint. -/
public instance spacesEtaleRestriction_preservesFiniteColimits (Z : T.Spaces) :
    PreservesFiniteColimits
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z)
        (T.bigEtaleTopology Z)) := by
  let : (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z).IsCocontinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) (T.bigEtaleTopology Z) :=
    Functor.IsCocontinuous.of_iso (inclusionFunctorIdIso T Z)
  let := (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Z
    |>.sheafAdjunctionCocontinuous Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z)
      (T.bigEtaleTopology Z)).leftAdjoint_preservesColimits
  exact inferInstance

/-- Direct image on the big étale sites has a total right derived functor on the unbounded
derived categories. -/
public instance bigEtalePushforward_hasRightDerivedFunctor :
    ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor (Sheaf.instIsGrothendieckAbelian _ Ab.{u + 1}) _

/-- Direct image on the small étale sites has a total right derived functor on the unbounded
derived categories. -/
public instance smallEtalePushforward_hasRightDerivedFunctor :
    ((smallEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            Ab.{u + 1}) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor (Sheaf.instIsGrothendieckAbelian _ Ab.{u + 1}) _

/-- The underived comparison square: direct image on the big étale sites followed by
restriction to the small étale site of `X` agrees with restriction to the small étale site
of `Y` followed by small-site direct image. This is the composition isomorphism of
pushforwards along the commuting square of site functors of Tag 0DF6. -/
public def bigSmallEtalePushforwardIso (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X) :
    (((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology Y)) ⋙ smallEtalePushforward T f) ≅
      (bigEtalePushforward T f ⋙
        ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X))) := by
  letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
  letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  letI := Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology Y)
  letI := Functor.isContinuous_comp
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)
    (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (T.bigEtaleTopology X)
    (T.bigEtaleTopology Y)
  dsimp only [smallEtalePushforward, bigEtalePushforward]
  exact Functor.sheafPushforwardContinuousComp
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      (T.bigEtaleTopology Y) ≪≫
    Functor.sheafPushforwardContinuousIso
      (smallBaseChange_comp_inclusionIso T f) Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)
      (Over.pullback f) Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology X)
      (T.bigEtaleTopology Y)).symm ≪≫
    Functor.isoWhiskerRight
      ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1}).symm
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X))

/-- **Derived direct image commutes with restriction to the small étale site.** Derived big-site
direct image followed by restriction to the small étale site agrees naturally with restriction
followed by derived small-site direct image. -/
@[stacks 0DGA "big_small_abelian"]
public def derivedBigSmallEtalePushforwardIso :
    (((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1})
          (ComplexShape.up ℤ))) ⋙
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X)).mapDerivedCategory ≅
    ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology Y)).mapDerivedCategory ⋙
      (((smallEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
              Ab.{u + 1}) (ComplexShape.up ℤ))) := by
  let A := Sheaf (T.bigEtaleTopology Y) Ab.{u + 1}
  let B := Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}
  let P := bigEtalePushforward T f
  let Q := ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology Y))
  let R := ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X))
  let Hf := smallEtalePushforward T f
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Wh := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
  let Fp := P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let Fh := (Q ⋙ Hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let Rp := Fp.totalRightDerived DerivedCategory.Qh W
  let Rh := (Hf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh Wh
  let ap := Fp.totalRightDerivedUnit DerivedCategory.Qh W
  let ah := (Hf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh Wh
  let FL := Fp ⋙ R.mapDerivedCategory
  let FR := Fh
  let RFL := Rp ⋙ R.mapDerivedCategory
  let RFR := Q.mapDerivedCategory ⋙ Rh
  let aL : FL ⟶ DerivedCategory.Qh ⋙ RFL :=
    Functor.whiskerRight ap R.mapDerivedCategory ≫ (Functor.associator _ _ _).hom
  let eComp := Functor.mapHomotopyCategoryCompIso
    (bigSmallEtalePushforwardIso T f).symm (ComplexShape.up ℤ)
  let eBase : FL ≅ FR :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (P.mapHomotopyCategory (ComplexShape.up ℤ))
        R.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eComp DerivedCategory.Qh
  let eCompQH := Functor.mapHomotopyCategoryCompIso (Iso.refl (Q ⋙ Hf))
    (ComplexShape.up ℤ)
  let aR : FR ⟶ DerivedCategory.Qh ⋙ RFR :=
    Functor.whiskerRight eCompQH.inv DerivedCategory.Qh ≫
      Functor.whiskerLeft (Q.mapHomotopyCategory (ComplexShape.up ℤ)) ah ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight Q.mapDerivedCategoryFactorsh.inv Rh ≫
      (Functor.associator _ _ _).hom
  have hL : RFL.IsRightDerivedFunctor aL W := by
    apply rightDerived_of_KInjective (Sheaf.instIsGrothendieckAbelian _ Ab.{u + 1}) FL RFL aL
    intro I hI
    let := hI
    have ha := rightDerivedUnit_isIso (Sheaf.instIsGrothendieckAbelian _ Ab.{u + 1}) Fp Rp ap I
    dsimp [aL]
    infer_instance
  have hR : RFR.IsRightDerivedFunctor aR W := by
    apply rightDerived_of_KInjective (Sheaf.instIsGrothendieckAbelian _ Ab.{u + 1}) FR RFR aR
    intro I hI
    let := hI
    have hQI : CochainComplex.IsKInjective
        ((Q.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
      isKInjective_spacesEtaleRestriction T Y I hI
    let := hQI
    have ha := rightDerivedUnit_isIso (Sheaf.instIsGrothendieckAbelian _ Ab.{u + 1})
      (Hf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Rh ah
      ((Q.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    have ha' : IsIso (ah.app
        ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) := by
      let e := (Q.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I
      have hcomp : IsIso
          (((Hf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map e.hom) ≫
            ah.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((Q.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
        infer_instance
      have hcomp' : IsIso
          (ah.app ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) ≫
            (DerivedCategory.Qh ⋙ Rh).map e.hom) := by
        exact ah.naturality e.hom ▸ hcomp
      exact (isIso_comp_right_iff _ _).mp hcomp'
    dsimp [aR]
    infer_instance
  let := hL
  let := hR
  exact Functor.rightDerivedNatIso RFL RFR aL aR W eBase

end

end AlgebraicGeometry.BigEtaleSpaceSite

end
