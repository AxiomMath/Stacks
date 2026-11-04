module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficientsDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology

/-!
# Inverse image, surjective descent and finite étale direct image of constructible sheaves on
Mathlib's small étale site

`Stacks.EtaleCohomology.IsBigSiteConstructibleEtaleModule` is constructibility (Stacks 03RW (3))
of a sheaf of `Λ`-modules on Mathlib's small étale site, read through the comparison
`Stacks.EtaleCohomology.etaleModulesToSmallEtale` with the small étale site of Stacks 021B. This
file transports to it the three functoriality statements proved on the latter site:

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_inverseImage` — **Stacks 095G**: inverse
  image preserves constructibility.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_inverseImage` — **Stacks 095Q**, descent
  half: constructibility descends along a surjective morphism of quasi-compact and
  quasi-separated schemes.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_directImage_of_finite_of_etale` —
  **Stacks 095H**: direct image along a finite étale morphism preserves constructibility.

The comparison of direct images, `Stacks.EtaleCohomology.etaleModulesToSmallEtaleDirectImageIso`,
is the module form of `AlgebraicGeometry.SmallEtale.sheafEquivInverseSmallPushforwardIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section General

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- **The bounded direct image is Mathlib's, through the comparison of sites**, for sheaves of
`Λ`-modules: restricting from Mathlib's small étale site and taking the bounded direct image is
taking Mathlib's direct image and restricting. -/
def etaleModulesToSmallEtaleDirectImageIso {S T : B.Scheme} (f : T ⟶ S) :
    etaleModulesToSmallEtale B T Λ ⋙ B.smallPushforward f (ModuleCat.{max (u + 1) r} Λ) ≅
      etaleModuleDirectImage.{u, r} Λ (B.inclusion.map f) ⋙ etaleModulesToSmallEtale B S Λ :=
  haveI : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  haveI : (SmallEtale.toEtaleSite B S.obj S.property).IsContinuous
      (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology :=
    SmallEtale.isContinuous_toEtaleSite B S.obj S.property
  haveI : (SmallEtale.toEtaleSite B T.obj T.property).IsContinuous
      (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology :=
    SmallEtale.isContinuous_toEtaleSite B T.obj T.property
  haveI : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (B.inclusion.obj S).smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  haveI : (SmallEtale.toEtaleSite B S.obj S.property).IsContinuous
      (SmallEtale.topology B S.obj S.property) (B.inclusion.obj S).smallEtaleTopology :=
    SmallEtale.isContinuous_toEtaleSite B S.obj S.property
  haveI := Functor.isContinuous_comp (AlgebraicGeometry.smallEtaleBaseChange B f)
    (SmallEtale.toEtaleSite B T.obj T.property) (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property) T.obj.smallEtaleTopology
  haveI := Functor.isContinuous_comp (SmallEtale.toEtaleSite B S.obj S.property)
    (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
    (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology T.obj.smallEtaleTopology
  Functor.sheafPushforwardContinuousComp' (SmallEtale.toEtaleSiteBaseChangeIso B f) _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

variable [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- Constructibility on Mathlib's small étale site is invariant under isomorphism. -/
theorem IsBigSiteConstructibleEtaleModule.of_iso {X : B.Scheme} {F G : EtaleModules.{u, r} Λ X.obj}
    (e : F ≅ G) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    IsBigSiteConstructibleEtaleModule B X Λ G :=
  isConstructibleModuleSheaf_congr B Λ X ((etaleModulesToSmallEtale B X Λ).mapIso e) hF

omit [IsNoetherianRing Λ] in
/-- **Stacks 095G on Mathlib's small étale site.** The inverse image of a constructible sheaf of
`Λ`-modules along a morphism of `B` is constructible. -/
theorem isConstructibleEtaleModule_inverseImage {X Y : B.Scheme} (f : Y ⟶ X)
    {F : EtaleModules.{u, r} Λ X.obj} (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).obj F) :=
  isConstructibleModuleSheaf_congr B Λ Y (etaleModulesToSmallEtalePullbackIso B Λ f F).symm
    (isConstructibleModuleSheaf_pullback B Λ f _ hF)

end General

section Small

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 095Q on Mathlib's small étale site, descent half.** Let `f : Y ⟶ X` be a surjective
morphism of quasi-compact and quasi-separated schemes of `B`. A sheaf of `Λ`-modules on `X` whose
inverse image along `f` is constructible is constructible. -/
theorem isConstructibleEtaleModule_of_inverseImage {X Y : B.Scheme} (f : Y ⟶ X)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [CompactSpace Y.obj]
    [QuasiSeparatedSpace Y.obj] (hf : Function.Surjective (B.inclusion.map f).base)
    {F : EtaleModules.{u, 0} Λ X.obj}
    (hF : IsBigSiteConstructibleEtaleModule B Y Λ
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map f)).obj F)) :
    IsBigSiteConstructibleEtaleModule B X Λ F :=
  isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback' B Λ f inferInstance
    inferInstance inferInstance inferInstance hf _
    (isConstructibleModuleSheaf_congr B Λ Y (etaleModulesToSmallEtalePullbackIso B Λ f F) hF)

/-- **Stacks 095H on Mathlib's small étale site.** The direct image along a finite étale
morphism of `B` of a constructible sheaf of `Λ`-modules is constructible. -/
theorem isConstructibleEtaleModule_directImage_of_finite_of_etale {S T : B.Scheme} (f : T ⟶ S)
    [IsFinite (B.inclusion.map f)] [Etale (B.inclusion.map f)]
    {F : EtaleModules.{u, 0} Λ T.obj} (hF : IsBigSiteConstructibleEtaleModule B T Λ F) :
    IsBigSiteConstructibleEtaleModule B S Λ
      ((etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map f)).obj F) :=
  isConstructibleModuleSheaf_congr B Λ S
    ((etaleModulesToSmallEtaleDirectImageIso B Λ f).app F)
    (isConstructibleModuleSheaf_pushforward' B Λ f _ hF)

end Small

end Stacks.EtaleCohomology

end
