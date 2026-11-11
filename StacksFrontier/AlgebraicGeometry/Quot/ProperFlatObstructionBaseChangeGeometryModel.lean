module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeGeometry
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartConormalTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeAdjunction

/-!
# The direct image of `𝒪_{X₀} ⊗_k I` along the special fibre of a deformation

Let `x = (X ⟶ Spec A)` be a deformation of `x₀ = (X₀ ⟶ Spec k)` over an object `A` of `𝒞_Λ`, and
let `I` be an `A`-module killed by `𝔪_A`, read as the `k`-vector space `I_k`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.residueModule`). Along the closed immersion
`j : X₀ ⟶ X` of the special fibre, `j_*(𝒪_{X₀} ⊗_k I_k) ≅ 𝒪_X ⊗_A I`. This file proves it on the
small étale sites and on the `Type u` models `AlgebraicGeometry.Space.modelTopos`, for the
morphism of ringed topoi `j_m`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreModelHom`).
With the identification of `Ext` groups into a direct image along a morphism with exact direct
image, it turns `T²_{X/A}(I)` into `Hom(Lj_m^* L_{X/A}, (𝒪_{X₀} ⊗_k I_k)[2])`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibrePushforwardChartTensorIso`: on the
  small étale sites, `j_*(𝒪_{X₀} ⊗_k I_k) ≅ 𝒪_X ⊗_A I`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreModelPushforwardTensorIso`: the same
  on the models, along `j_m`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.cotangentExtTwoSpecialFibreAddEquiv`:
  `T²_{X/A}(I) ≃+ Hom(Lj_m^* L_{X/A}, (𝒪_{X₀} ⊗_k I_k)[2])`.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin

attribute [-instance] AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

universe u

namespace CategoryTheory.Equivalence

variable {C D : Type*} [Category C] [Category D]

/-- Two equivalences with isomorphic functors have isomorphic inverses. -/
def inverseIsoOfFunctorIso (e₁ e₂ : C ≌ D) (α : e₁.functor ≅ e₂.functor) :
    e₁.inverse ≅ e₂.inverse :=
  e₁.inverse.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft e₁.inverse e₂.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft e₁.inverse α.symm ≪≫ e₁.counitIso)
      e₂.inverse ≪≫ e₂.inverse.leftUnitor

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The two presentations of the Comparison Lemma for `𝒪_X`-modules and the model have the same
functor: restriction along the comparison of the model with the small étale site. -/
def modulesEquivModelModulesFunctorIso :
    (modulesEquivModelModules B S hS X.1 X.2).functor ≅
      (smallEtaleModelModulesEquiv B S hS X).functor :=
  Iso.refl _

/-- The direct image of modules along `ρ_X : X_étale ⟶ model(X)` is the functor of the Comparison
Lemma. -/
def smallEtaleModelInversePushforwardModulesIso :
    (smallEtaleModelInverseRingedToposHom B S hS X).pushforwardModules ≅
      (smallEtaleModelModulesEquiv B S hS X).functor :=
  (smallEtaleModelInverseRingedSiteHom B S hS X).pushforwardToposIsoGeneral ≪≫ Iso.refl _

/-- The direct image of modules along `π_X : model(X) ⟶ X_étale` is the inverse of the
Comparison Lemma. -/
def smallEtaleModelPushforwardModulesIso :
    (smallEtaleModelRingedToposHom B S hS X).pushforwardModules ≅
      (smallEtaleModelModulesEquiv B S hS X).inverse :=
  smallEtaleModelPushforwardIso B S hS X ≪≫
    Equivalence.inverseIsoOfFunctorIso _ _ (modulesEquivModelModulesFunctorIso B S hS X)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
    hx₀)

/-! ### Changing the base ring -/

/-- `Γ(Spec A) ≅ A`, as a ring map out of the base ring of the chart of a deformation. -/
abbrev chartGammaHom : Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains) →+*
    a.algebra :=
  (Scheme.ΓSpecIso (CommRingCat.of a.algebra)).hom.hom

/-- `Γ(Spec A) ⟶ Γ(Spec k) ≅ k` is the residue map, read through `Γ(Spec A) ≅ A`. -/
theorem chartThickeningRingHom_closedPointMap :
    Space.ProperFlatLift.chartThickeningRingHom (closedPointMap a) =
      (residueMap a.algebra).comp (chartGammaHom a) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (residueMap a.algebra))
  unfold Space.ProperFlatLift.chartThickeningRingHom
  rw [toScheme_map_closedPointMap]
  exact congrArg CommRingCat.Hom.hom h

/-- `Γ(Spec A) ⟶ k` is surjective. -/
theorem surjective_chartThickeningRingHom_closedPointMap :
    Function.Surjective (Space.ProperFlatLift.chartThickeningRingHom (closedPointMap a)) := by
  rw [chartThickeningRingHom_closedPointMap]
  exact (residueMap_surjective_of_artinian a.algebra).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of a.algebra)).hom).2

/-- The base-ring datum of `X ⟶ Spec A`, read through `Γ(Spec A) ≅ A`, is that of the chart. -/
theorem chartBaseRingHom_comp_chartGammaHom :
    (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq).comp (chartGammaHom a) =
      Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq) :=
  RingHom.ext fun g => congrArg
    (Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq))
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of a.algebra)).hom_inv_id g)

variable (I : ModuleCat.{u} a.algebra)
  (hI : ∀ r ∈ IsLocalRing.maximalIdeal a.algebra, ∀ i : I, r • i = 0)

/-- **`I` as a `Γ(Spec A)`-module, in two ways**: through `Γ(Spec A) ≅ A`, and as the
`k`-vector space `I_k` through `Γ(Spec A) ⟶ k`. They agree, `𝔪_A` killing `I`. -/
def chartGammaLinearEquiv :
    ((ModuleCat.restrictScalars.{u} (chartGammaHom a)).obj I) ≃ₗ[Space.baseRing B S hS
      (algebraOver a.algebra B S hS a.toS a.contains)]
      ((ModuleCat.restrictScalars.{u} (Space.ProperFlatLift.chartThickeningRingHom
        (closedPointMap a))).obj (residueModule I hI)) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' g x := by
    change (show residueModule I hI from (chartGammaHom a g • x)) =
      Space.ProperFlatLift.chartThickeningRingHom (closedPointMap a) g •
        (show residueModule I hI from x)
    rw [chartThickeningRingHom_closedPointMap, RingHom.comp_apply]
    exact (residueModule_smul I hI _ x).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- `chartGammaLinearEquiv` as an isomorphism of `Γ(Spec A)`-modules. -/
def chartGammaModuleIso :
    (ModuleCat.restrictScalars.{u} (chartGammaHom a)).obj I ≅
      (ModuleCat.restrictScalars.{u} (Space.ProperFlatLift.chartThickeningRingHom
        (closedPointMap a))).obj (residueModule I hI) :=
  (chartGammaLinearEquiv a I hI).toModuleIso

/-- `𝔪_A` kills `I_k` read as a `Γ(Spec A)`-module. -/
theorem smul_restrictScalars_residueModule_eq_zero
    (c : Space.baseRing B S hS (algebraOver a.algebra B S hS a.toS a.contains))
    (hc : c ∈ Space.siteMapKer B S hS (closedPointMap a))
    (i : (ModuleCat.restrictScalars.{u} (Space.ProperFlatLift.chartThickeningRingHom
      (closedPointMap a))).obj (residueModule I hI)) : c • i = 0 := by
  change Space.ProperFlatLift.chartThickeningRingHom (closedPointMap a) c •
    (show residueModule I hI from i) = 0
  have h0 : Space.ProperFlatLift.chartThickeningRingHom (closedPointMap a) c = 0 := by
    exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      (RingHom.mem_ker.mp hc)).trans (map_zero _)
  rw [h0, zero_smul]

/-! ### The direct image on the small étale sites -/

/-- **`j_*(𝒪_{X₀} ⊗_k I_k) ≅ 𝒪_X ⊗_A I`** on the small étale sites, for an `A`-module `I` killed
by `𝔪_A`, the base rings acting through the charts `X₀ ⟶ Spec k` and `X ⟶ Spec A`. -/
def specialFibrePushforwardChartTensorIso :
    (Space.modulePushforward B S hS (specialFibreMap a)).obj
        ((Space.baseRingTensorModule B S hS x₀.obj.obj.left
          (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
            (residueModule I hI)) ≅
      (Space.baseRingTensorModule B S hS a.point.obj.obj.left
        (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)).obj I :=
  (Space.modulePushforward B S hS (specialFibreMap a)).mapIso
      (((Space.baseRingTensorModuleRestrictScalarsIso B S hS x₀.obj.obj.left
          (Space.ProperFlatLift.chartThickeningRingHom (closedPointMap a))
          (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))
          (surjective_chartThickeningRingHom_closedPointMap a)).app (residueModule I hI)).symm ≪≫
        eqToIso (congrArg (fun φ => (Space.baseRingTensorModule B S hS x₀.obj.obj.left φ).obj
          ((ModuleCat.restrictScalars.{u} (Space.ProperFlatLift.chartThickeningRingHom
            (closedPointMap a))).obj (residueModule I hI)))
          (Space.ProperFlatLift.baseRingHomOfMap_chartStructureMap_comp x₀
            (obj_eq_specialFibre x₀ hx₀) (closedPointMap a)).symm)) ≪≫
    specialFibrePushforwardTensorIso a _ (smul_restrictScalars_residueModule_eq_zero a I hI) ≪≫
    (Space.baseRingTensorModule B S hS a.point.obj.obj.left
      (Space.baseRingHomOfMap (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq))).mapIso
        (chartGammaModuleIso a I hI).symm ≪≫
    eqToIso (congrArg (fun φ => (Space.baseRingTensorModule B S hS a.point.obj.obj.left φ).obj
      ((ModuleCat.restrictScalars.{u} (chartGammaHom a)).obj I))
      (chartBaseRingHom_comp_chartGammaHom a).symm) ≪≫
    (Space.baseRingTensorModuleRestrictScalarsIso B S hS a.point.obj.obj.left (chartGammaHom a)
      (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of a.algebra)).hom).2).app I

/-! ### The direct image on the models -/

/-- **`j_{m*}(𝒪_{X₀} ⊗_k I_k) ≅ 𝒪_X ⊗_A I`** on the `Type u` models of the small étale ringed
topoi, for an `A`-module `I` killed by `𝔪_A`: `j_m = ρ_X ∘ j ∘ π_{X₀}`, the direct images along
`π_{X₀}` and `ρ_X` are the two halves of the Comparison Lemma, and on the small étale sites this
is `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibrePushforwardChartTensorIso`. The
direct image of modules along `j_m` is `AlgebraicGeometry.RingedToposHom.pushforwardModules`,
which restricts scalars along the structure map of `j_m`. -/
def specialFibreModelPushforwardTensorIso :
    (specialFibreModelHom a).pushforwardModules.obj
        ((Space.modelTensorFunctor (Space.ProperFlatLift.chartBaseRingHom x₀
          (obj_eq_specialFibre x₀ hx₀))).obj (residueModule I hI)) ≅
      (Space.modelTensorFunctor (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)).obj I :=
  let X₀ := x₀.obj.obj.left
  let X := a.point.obj.obj.left
  let φ₀ := Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀)
  let φ := Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq
  let N₀ := (Space.modelTensorFunctor φ₀).obj (residueModule I hI)
  let E₀ := Space.smallEtaleModelModulesEquiv B S hS X₀
  let E := Space.smallEtaleModelModulesEquiv B S hS X
  (RingedToposHom.pushforwardModulesCompIso (Space.smallEtaleModelCompRingedToposHom
      (specialFibreMap a)) (Space.smallEtaleModelInverseRingedToposHom B S hS X)).app N₀ ≪≫
    (Space.smallEtaleModelInverseRingedToposHom B S hS X).pushforwardModules.mapIso
      ((RingedToposHom.pushforwardModulesCompIso
          (Space.smallEtaleModelRingedToposHom B S hS X₀)
          (Space.smallEtaleRingedToposHom B S hS (specialFibreMap a))).app N₀ ≪≫
        (Space.smallEtaleRingedToposHom B S hS (specialFibreMap a)).pushforwardModules.mapIso
          ((Space.smallEtaleModelPushforwardModulesIso B S hS X₀).app N₀) ≪≫
        (Space.pushforwardModulesIsoModulePushforward B S hS (specialFibreMap a)).app
          (E₀.inverse.obj N₀) ≪≫
        specialFibrePushforwardChartTensorIso a I hI) ≪≫
    (Space.smallEtaleModelInversePushforwardModulesIso B S hS X).app _ ≪≫
    E.counitIso.app ((Space.modelTensorFunctor φ).obj I)

/-! ### The obstruction groups, read on the special fibre -/

section ObstructionGroups

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived pullback along `j_m` exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_specialFibreModelHom :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
      (specialFibreModelHom a)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget
        (Y := Space.modelTopos a.point.obj.obj.left)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (specialFibreModelHom a)

/-- **`T²_{X/A}(I) = Hom(Lj_m^* L_{X/A}, (𝒪_{X₀} ⊗_k I_k)[2])`** for an `A`-module `I` killed by
`𝔪_A`: `T²_{X/A}(I) = Ext²(L_{X/A}, 𝒪_X ⊗_A I)`
(`AlgebraicGeometry.Space.cotangentExtFunctorObjEquiv`), `𝒪_X ⊗_A I ≅ j_{m*}(𝒪_{X₀} ⊗_k I_k)`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreModelPushforwardTensorIso`), and
`Hom(K, (j_{m*}G)[2]) = Hom(Lj_m^* K, G[2])`, the direct image along `j_m` being exact
(`Stacks.Cohomology.DerivedPushforward.homShiftSingleAddEquivOfIsEquivalence`). The derived
categories are the standard ones. -/
def cotangentExtTwoSpecialFibreAddEquiv :
    (Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
        (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)).obj I ≃+
      ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback (specialFibreModelHom a)).obj
          (Space.modelRingedToposHom
            (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)).cotangentComplexDerived ⟶
        ((DerivedCategory.singleFunctor _ 0).obj ((Space.modelTensorFunctor
          (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
            (residueModule I hI)))⟦(2 : ℤ)⟧) :=
  (Space.cotangentExtFunctorObjEquiv (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
      (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq) 2 I).trans
    ((AddEquiv.mk ((Iso.refl _).homCongr ((shiftFunctor _ (2 : ℤ)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (specialFibreModelPushforwardTensorIso a I hI).symm)))
      (fun f g => by simp [Iso.homCongr_apply, Preadditive.add_comp])).trans
    (Stacks.Cohomology.DerivedPushforward.homShiftSingleAddEquivOfIsEquivalence
      (specialFibreModelHom a) _ _ 2))

end ObstructionGroups

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
