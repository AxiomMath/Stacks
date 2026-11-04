module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineBaseInduction
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeTensorComparisonOnModels

/-!
# The base-change composition at a derived tensor product with a K-flat factor

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes, `P` a K-flat complex of `𝒪_X`-modules and `G` an arbitrary
complex of `𝒪_X`-modules. The composition

`Lg^*Rf_*(P ⊗^L G) ⟶ Rf'_*L(g')^*(P ⊗^L G) ⟶ Rf'_*(L(g')^*P ⊗^L (g')^*G)`

of the derived base-change map with the base-change comparison of the derived tensor product is
invertible exactly when the composition

`Lg^*Rf_*Tot(P ⊗ G) ⟶ Rf'_*L(g')^*Tot(P ⊗ G) ⟶ Rf'_*(g')^*Tot(P ⊗ G)`

is. The same composition only depends on the first factor of the derived tensor product up to
isomorphism.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeComp_tensor_iff_of_iso`: the composition depends on
  the first tensor factor only up to isomorphism.
* `AlgebraicGeometry.isIso_derivedBaseChangeComp_tensor_iff_of_kFlat`: for a K-flat first factor
  it is the composition at the total tensor complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex
  pullbackTensorComplexNatIso totalComplexPair_map)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedPullbackTensor (baseChangeTensorComparison_comp_toTensor
  leftComparison_app_eq isIso_toTensor_of_kFlat isIso_tensorMap_toTensor_of_kFlat)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)

/-- `btc_naturality` with the composite maps on the two sides named. -/
private theorem btc_naturality_of_eq {E₁ E₂ K₁ K₂ :
      DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)}
    {K₁' K₂' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace)}
    (u : E₁ ⟶ E₂) (v : K₁ ⟶ K₂) (v' : K₁' ⟶ K₂')
    (φ₁ : (derivedPullback g'.toLRSHom.toShHom).obj K₁ ⟶ K₁')
    (φ₂ : (derivedPullback g'.toLRSHom.toShHom).obj K₂ ⟶ K₂')
    (hφ : (derivedPullback g'.toLRSHom.toShHom).map v ≫ φ₂ = φ₁ ≫ v')
    (a : ((derivedTensorProductFunctor X.sheaf).obj E₁).obj K₁ ⟶
      ((derivedTensorProductFunctor X.sheaf).obj E₂).obj K₂)
    (b : ((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E₁)).obj K₁' ⟶
      ((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E₂)).obj K₂')
    (ha : ((derivedTensorProductFunctor X.sheaf).map u).app K₁ ≫
      ((derivedTensorProductFunctor X.sheaf).obj E₂).map v = a)
    (hb : ((derivedTensorProductFunctor X'.sheaf).map
        ((derivedPullback g'.toLRSHom.toShHom).map u)).app K₁' ≫
      ((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E₂)).map v' = b) :
    (derivedPullback g'.toLRSHom.toShHom).map a ≫
        baseChangeTensorComparison g'.toLRSHom.toShHom E₂ K₂ K₂' φ₂ =
      baseChangeTensorComparison g'.toLRSHom.toShHom E₁ K₁ K₁' φ₁ ≫ b := by
  subst ha hb
  exact btc_naturality (g' := g') u v v' φ₁ φ₂ hφ

/-- **The composition only depends on the first tensor factor up to isomorphism.** -/
theorem isIso_derivedBaseChangeComp_tensor_iff_of_iso
    {E₁ E₂ : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)}
    (e : E₁ ≅ E₂) (K : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace))
    (K' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom sq (((derivedTensorProductFunctor X.sheaf).obj E₁).obj K) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        (baseChangeTensorComparison g'.toLRSHom.toShHom E₁ K K' φ)) ↔
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom sq (((derivedTensorProductFunctor X.sheaf).obj E₂).obj K) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        (baseChangeTensorComparison g'.toLRSHom.toShHom E₂ K K' φ)) := by
  have hu : IsIso (((derivedTensorProductFunctor X.sheaf).map e.hom).app K) :=
    (((derivedTensorProductFunctor X.sheaf).mapIso e).app K).isIso_hom
  have hv : IsIso (((derivedTensorProductFunctor X'.sheaf).map
      ((derivedPullback g'.toLRSHom.toShHom).map e.hom)).app K') :=
    (((derivedTensorProductFunctor X'.sheaf).mapIso
      ((derivedPullback g'.toLRSHom.toShHom).mapIso e)).app K').isIso_hom
  refine @Stacks.Cohomology.BaseChangeCover.isIso_bc_iff_of_iso _ _ _ _ _ _ _ _ sq _ _ _ _ _ _
    (((derivedTensorProductFunctor X.sheaf).map e.hom).app K)
    (((derivedTensorProductFunctor X'.sheaf).map
      ((derivedPullback g'.toLRSHom.toShHom).map e.hom)).app K') hu hv ?_
  exact btc_naturality_of_eq (g' := g') e.hom (𝟙 K) (𝟙 K') φ φ
    (by erw [(derivedPullback g'.toLRSHom.toShHom).map_id K, Category.id_comp, Category.comp_id])
    _ _ (by simp) (by simp)

/-- `btc_naturality` with the first tensor factor fixed. -/
theorem btc_naturality_right
    (E : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace))
    {K₁ K₂ : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)}
    {K₁' K₂' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace)}
    (v : K₁ ⟶ K₂) (v' : K₁' ⟶ K₂')
    (φ₁ : (derivedPullback g'.toLRSHom.toShHom).obj K₁ ⟶ K₁')
    (φ₂ : (derivedPullback g'.toLRSHom.toShHom).obj K₂ ⟶ K₂')
    (hφ : (derivedPullback g'.toLRSHom.toShHom).map v ≫ φ₂ = φ₁ ≫ v') :
    (derivedPullback g'.toLRSHom.toShHom).map
          (((derivedTensorProductFunctor X.sheaf).obj E).map v) ≫
        baseChangeTensorComparison g'.toLRSHom.toShHom E K₂ K₂' φ₂ =
      baseChangeTensorComparison g'.toLRSHom.toShHom E K₁ K₁' φ₁ ≫
        ((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).map v' :=
  btc_naturality_of_eq (g' := g') (𝟙 E) v v' φ₁ φ₂ hφ _ _ (by simp)
    (by
      erw [(derivedPullback g'.toLRSHom.toShHom).map_id E]
      exact (congrArg (· ≫ _) (NatTrans.congr_app
        ((derivedTensorProductFunctor X'.sheaf).map_id _) K₁')).trans (Category.id_comp _))

/-- The base-change composition is unchanged by an isomorphism of data. -/
theorem isIso_derivedBaseChangeComp_iff_of_iso (w : g' ≫ f = f' ≫ g)
    {L₁ L₂ : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace)}
    {L₁' L₂' : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace)}
    (φ₁ : (derivedPullback g'.toLRSHom.toShHom).obj L₁ ⟶ L₁')
    (φ₂ : (derivedPullback g'.toLRSHom.toShHom).obj L₂ ⟶ L₂')
    (u : L₁ ⟶ L₂) (v : L₁' ⟶ L₂') (hu : IsIso u) (hv : IsIso v)
    (h : (derivedPullback g'.toLRSHom.toShHom).map u ≫ φ₂ = φ₁ ≫ v) :
    IsIso (derivedBaseChangeComp f g f' g' w L₁ L₁' φ₁) ↔
      IsIso (derivedBaseChangeComp f g f' g' w L₂ L₂' φ₂) :=
  @Stacks.Cohomology.BaseChangeCover.isIso_bc_iff_of_iso _ _ _ _ _ _ _ _ _ _ _ _ _ φ₁ φ₂ u v
    hu hv h

/-- Replacing the second tensor factor along a quasi-isomorphism `r : N ⟶ G` of complexes. -/
theorem isIso_derivedBaseChangeComp_tensor_resolution_iff (w : g' ≫ f = f' ≫ g)
    (E : DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace))
    {N G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ}
    (r : N ⟶ G) [QuasiIso r] :
    IsIso (derivedBaseChangeComp f g f' g' w
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj N)) _
        (baseChangeTensorComparison g'.toLRSHom.toShHom E (DerivedCategory.Q.obj N)
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
          ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫
            DerivedCategory.Q.map ((pullbackComplex g'.toLRSHom.toShHom).map r)))) ↔
    IsIso (derivedBaseChangeComp f g f' g' w
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G)) _
        (baseChangeTensorComparison g'.toLRSHom.toShHom E (DerivedCategory.Q.obj G)
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
          ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G))) := by
  have hnat : (derivedPullback g'.toLRSHom.toShHom).map (DerivedCategory.Q.map r) ≫
      (derivedPullbackNatTrans g'.toLRSHom.toShHom).app G =
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫
        DerivedCategory.Q.map ((pullbackComplex g'.toLRSHom.toShHom).map r)) ≫ 𝟙 _ :=
    ((derivedPullbackNatTrans g'.toLRSHom.toShHom).naturality r).trans (Category.comp_id _).symm
  have hQ : IsIso (DerivedCategory.Q.map r) := inferInstance
  have hu : IsIso (((derivedTensorProductFunctor X.sheaf).obj E).map (DerivedCategory.Q.map r)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hQ
  have hv : IsIso (((derivedTensorProductFunctor X'.sheaf).obj
      ((derivedPullback g'.toLRSHom.toShHom).obj E)).map
        (𝟙 (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G)))) :=
    Functor.map_isIso _ _
  exact isIso_derivedBaseChangeComp_iff_of_iso f g f' g' w _ _ _ _ hu hv
    (btc_naturality_right (g' := g') _ _ _ _ _ hnat)

/-- On K-flat representatives the base-change comparison of the derived tensor product is the
comparison of the total tensor complex. -/
theorem isIso_derivedBaseChangeComp_tensor_iff_totalTensor (w : g' ≫ f = f' ≫ g)
    (P N : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
    (hP : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P)
    (hN : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace N)
    (W : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace) ℤ)
    (a : (pullbackComplex g'.toLRSHom.toShHom).obj N ⟶ W) :
    IsIso (derivedBaseChangeComp f g f' g' w
        (((derivedTensorProductFunctor X.sheaf).obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj N)) _
        (baseChangeTensorComparison g'.toLRSHom.toShHom (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj W)
          ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫ DerivedCategory.Q.map a))) ↔
    IsIso (derivedBaseChangeComp f g f' g' w
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))) _
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso g'.toLRSHom.toShHom).hom.app (P, N) ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) a
              (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)))) := by
  have hθ := isIso_toTensor_of_kFlat (Y := X.toRingedSpace) P N hP
  have hψ := isIso_tensorMap_toTensor_of_kFlat g'.toLRSHom.toShHom P hP W
  have e := (baseChangeTensorComparison_comp_toTensor g'.toLRSHom.toShHom P N hP hN W a).trans
    ((congrArg (fun t ↦ t ≫ _) (leftComparison_app_eq g'.toLRSHom.toShHom P N)).trans
      (Category.assoc _ _ _))
  exact isIso_derivedBaseChangeComp_iff_of_iso f g f' g' w _ _ _ _ hθ hψ e.symm

/-- The degreewise pullback of `Tot(𝟙 ⊗ r)`, through the comparison of Stacks 01CD. -/
theorem pullbackComplex_map_mapBifunctorMap_id {Y Z : RingedSpace.{u, u}} (h : Z ⟶ Y)
    (P : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    {N G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules Y) ℤ} (r : N ⟶ G) :
    (pullbackComplex h).map (HomologicalComplex.mapBifunctorMap (𝟙 P) r
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ)) ≫
      (pullbackTensorComplexNatIso h).hom.app (P, G) =
    (pullbackTensorComplexNatIso h).hom.app (P, N) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 _) ((pullbackComplex h).map r)
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) (ComplexShape.up ℤ) := by
  calc _ = (pullbackComplex h).map ((Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).map (𝟙 P ×ₘ r)) ≫
        (pullbackTensorComplexNatIso h).hom.app (P, G) :=
          congrArg (fun t ↦ (pullbackComplex h).map t ≫
            (pullbackTensorComplexNatIso h).hom.app (P, G))
            (totalComplexPair_map (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (𝟙 P) r).symm
    _ = (pullbackTensorComplexNatIso h).hom.app (P, N) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).map
            ((pullbackComplex h).map (𝟙 P) ×ₘ (pullbackComplex h).map r) :=
          (pullbackTensorComplexNatIso h).hom.naturality (X := (P, N)) (Y := (P, G)) (𝟙 P ×ₘ r)
    _ = _ := congrArg (fun t ↦ (pullbackTensorComplexNatIso h).hom.app (P, N) ≫ t)
          ((totalComplexPair_map (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)
            ((pullbackComplex h).map (𝟙 P)) ((pullbackComplex h).map r)).trans
              (by rw [(pullbackComplex h).map_id P]; rfl))

/-- The comparison of the derived pullback with the degreewise one, at `Tot(𝟙 ⊗ r)`. -/
theorem derivedPullbackNatTrans_mapBifunctorMap_id {Y Z : RingedSpace.{u, u}} (h : Z ⟶ Y)
    (P : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    {N G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules Y) ℤ} (r : N ⟶ G) :
    (derivedPullback h).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) r
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))) ≫
      (derivedPullbackNatTrans h).app (HomologicalComplex.mapBifunctor P G
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ)) =
    ((derivedPullbackNatTrans h).app (HomologicalComplex.mapBifunctor P N
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ)) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso h).hom.app (P, N) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 _) ((pullbackComplex h).map r)
          (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) (ComplexShape.up ℤ))) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso h).inv.app (P, G)) := by
  have hn := (derivedPullbackNatTrans h).naturality
    (HomologicalComplex.mapBifunctorMap (𝟙 P) r
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))
  have hp := pullbackComplex_map_mapBifunctorMap_id h P r
  have hp' := ((Iso.app (pullbackTensorComplexNatIso h) (P, G)).eq_comp_inv).2 hp
  refine hn.trans ?_
  refine (congrArg (fun t ↦ (derivedPullbackNatTrans h).app (HomologicalComplex.mapBifunctor P N
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ)) ≫
      DerivedCategory.Q.map t) hp').trans ?_
  exact (congrArg (fun t ↦ (derivedPullbackNatTrans h).app (HomologicalComplex.mapBifunctor P N
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ)) ≫ t)
    (DerivedCategory.Q.map_comp _ _)).trans (Category.assoc _ _ _).symm

/-- Along a quasi-isomorphism `r : N ⟶ G`, a K-flat first factor `P` and the degreewise pullback
of the total tensor complex. -/
theorem isIso_derivedBaseChangeComp_totalTensor_resolution_iff (w : g' ≫ f = f' ≫ g)
    (P : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
    (hP : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P)
    {N G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ}
    (r : N ⟶ G) (hr : QuasiIso r) :
    IsIso (derivedBaseChangeComp f g f' g' w
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))) _
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso g'.toLRSHom.toShHom).hom.app (P, N) ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) ((pullbackComplex g'.toLRSHom.toShHom).map r)
              (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)))) ↔
    IsIso (derivedBaseChangeComp f g f' g' w
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P G
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))) _
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (HomologicalComplex.mapBifunctor P G
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)))) := by
  have hq : QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 P) r
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) :=
    Stacks.SheafOfModules.IsKFlat.quasiIso_mapBifunctorMap_id_left X.sheaf P hP r hr
  have hu : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) r
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hv : IsIso (DerivedCategory.Q.map
      ((pullbackTensorComplexNatIso g'.toLRSHom.toShHom).inv.app (P, G))) := inferInstance
  exact isIso_derivedBaseChangeComp_iff_of_iso f g f' g' w _ _ _ _ hu hv
    (derivedPullbackNatTrans_mapBifunctorMap_id g'.toLRSHom.toShHom P r)

/-- **The base-change composition at a derived tensor product with a K-flat first factor**: it is
invertible exactly when the composition at the total tensor complex, with the comparison of the
derived pullback with the degreewise one, is. -/
theorem isIso_derivedBaseChangeComp_tensor_iff_of_kFlat (w : g' ≫ f = f' ≫ g)
    (P G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
    (hP : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P) :
    IsIso (derivedBaseChangeComp f g f' g' w
        (((derivedTensorProductFunctor X.sheaf).obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj G)) _
        (baseChangeTensorComparison g'.toLRSHom.toShHom (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj G)
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
          ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G))) ↔
    IsIso (derivedBaseChangeComp f g f' g' w
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P G
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))) _
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (HomologicalComplex.mapBifunctor P G
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)))) := by
  obtain ⟨N, r, hN, -, hr, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution X.toRingedSpace G
  exact (isIso_derivedBaseChangeComp_tensor_resolution_iff f g f' g' w _ r).symm.trans
    ((isIso_derivedBaseChangeComp_tensor_iff_totalTensor f g f' g' w P N hP hN _
      ((pullbackComplex g'.toLRSHom.toShHom).map r)).trans
      (isIso_derivedBaseChangeComp_totalTensor_resolution_iff f g f' g' w P hP r hr))

end AlgebraicGeometry
