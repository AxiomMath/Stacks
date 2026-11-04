module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleRelativeBoxMap

/-!
# The Künneth map along a morphism of diagrams, at complexes identified with direct images

Let `τ_X : X ⟶ X'`, `τ_Y : Y ⟶ Y'`, `τ_W : W ⟶ W'` be morphisms of ringed spaces over a crossing
of two Künneth squares, with exact direct images.  If the Künneth map of the square over `X, Y, W`
at `𝒦, ℳ` followed by the derived-to-total comparison is invertible, and a map `b` out of the total
complex of the degreewise pullbacks of complexes `𝒦' ≅ τ_{X,*}𝒦`, `ℳ' ≅ τ_{Y,*}ℳ` agrees with the
naive crossing map up to an isomorphism, then the Künneth map of the square over `X', Y', W'` at
`𝒦', ℳ'` followed by `Rf'_*` of the derived-to-total comparison and `b` is invertible.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_kunnethMap_of_crossing`.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open scoped CategoryTheory.Prod

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace Stacks.Cohomology.BoxKunnethFlat

variable {S X X' Y Y' W W' : RingedSpace.{u, u}}
  (τX : X ⟶ X') (a' : X' ⟶ S) (τY : Y ⟶ Y') (b' : Y' ⟶ S) (τW : W ⟶ W') (f' : W' ⟶ S)
  (p : W ⟶ X) (q : W ⟶ Y) (p' : W' ⟶ X') (q' : W' ⟶ Y')
  (hp' : p' ≫ a' = f') (hq' : q' ≫ b' = f') (hpsq : τW ≫ p' = p ≫ τX) (hqsq : τW ≫ q' = q ≫ τY)
  (hp : p ≫ τX ≫ a' = τW ≫ f') (hq : q ≫ τY ≫ b' = τW ≫ f')
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The Künneth map along a crossing, at complexes identified with direct images.** -/
theorem isIso_kunnethMap_of_crossing
    (K₀ : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (M₀ : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (K₂ : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X') ℤ)
    (M₂ : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y') ℤ)
    [IsIso (pushforwardComparisonQ τX K₀)] [IsIso (pushforwardComparisonQ τY M₀)]
    [IsIso (pushforwardComparisonQ τW ((totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)).obj
        ((pullbackComplex p).obj K₀, (pullbackComplex q).obj M₀)))]
    (ψX : (pushforwardComplex τX).obj K₀ ≅ K₂) (ψY : (pushforwardComplex τY).obj M₀ ≅ M₂)
    {A₃ : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W') ℤ}
    (θ : (pushforwardComplex τW).obj ((totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)).obj
        ((pullbackComplex p).obj K₀, (pullbackComplex q).obj M₀)) ≅ A₃)
    (bb : (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W'.sheaf)).obj
      ((pullbackComplex p').obj K₂, (pullbackComplex q').obj M₂) ⟶ A₃)
    (hc : HomologicalComplex.mapBifunctorMap ((pullbackComplex p').map ψX.hom)
        ((pullbackComplex q').map ψY.hom)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W'.sheaf) (ComplexShape.up ℤ) ≫ bb
            =
      Stacks.Cohomology.KunnethNaive.naiveCrossing τX τY τW p q p' q' hpsq hqsq K₀ M₀ ≫ θ.hom)
    (hS : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap (τX ≫ a') (τY ≫ b') p q (τW ≫ f') hp hq
        (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj M₀) ≫
      (derivedPushforward (τW ≫ f')).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullbackNatTrans p).app K₀ ×ₘ (derivedPullbackNatTrans q).app M₀) ≫
          (derivedToTensorNatTrans W).app ((pullbackComplex p).obj K₀, (pullbackComplex q).obj
              M₀))))
    (B : ((derivedTensorProductFunctor W'.sheaf).obj ((derivedPullback p').obj
      (DerivedCategory.Q.obj K₂))).obj ((derivedPullback q').obj (DerivedCategory.Q.obj M₂)) ⟶
        DerivedCategory.Q.obj A₃)
    (hB : B = ((Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf)).map
          ((derivedPullbackNatTrans p').app K₂ ×ₘ (derivedPullbackNatTrans q').app M₂) ≫
        (derivedToTensorNatTrans W').app ((pullbackComplex p').obj K₂, (pullbackComplex q').obj M₂))
            ≫
      DerivedCategory.Q.map bb) :
    IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a' b' p' q' f' hp' hq'
        (DerivedCategory.Q.obj K₂) (DerivedCategory.Q.obj M₂) ≫ (derivedPushforward f').map B) :=
  isIso_of_crossing_chain (derivedPushforward f') (derivedPushforward τW)
    (derivedPushforward (τW ≫ f')) (derivedPushforwardCompIso τW f') _ _ hS
    ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).mapIso
      (Iso.prod ((derivedPushforwardCompIso τX a').app (DerivedCategory.Q.obj K₀))
        ((derivedPushforwardCompIso τY b').app (DerivedCategory.Q.obj M₀)))) _ _
    (Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap_crossing τX a' τY b' τW f' p q p' q' hp'
      hq' hpsq hqsq hp hq (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj M₀))
    ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).mapIso
      (Iso.prod ((derivedPushforward a').mapIso
          ((asIso (pushforwardComparisonQ τX K₀)).symm ≪≫ DerivedCategory.Q.mapIso ψX))
        ((derivedPushforward b').mapIso
          ((asIso (pushforwardComparisonQ τY M₀)).symm ≪≫ DerivedCategory.Q.mapIso ψY)))) _ _
    ((Category.assoc _ _ _).trans (kunnethMap_natural_both p' q' a' b' f' hp' hq'
      ((asIso (pushforwardComparisonQ τX K₀)).symm ≪≫ DerivedCategory.Q.mapIso ψX).hom
      ((asIso (pushforwardComparisonQ τY M₀)).symm ≪≫ DerivedCategory.Q.mapIso ψY).hom))
    _ ((asIso (pushforwardComparisonQ τW _)).symm ≪≫ DerivedCategory.Q.mapIso θ)
    (comp_eq_of_crossing_naive DerivedCategory.Q (derivedPushforward τW) _ _
      (asIso (pushforwardComparisonQ τW _))
      ((Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf)).mapIso
        (Iso.prod ((derivedPullback p').mapIso (asIso (pushforwardComparisonQ τX K₀)))
          ((derivedPullback q').mapIso (asIso (pushforwardComparisonQ τY M₀))))) _ _
      (Stacks.Cohomology.KunnethNaive.crossingKunneth_naive τX τY τW p q p' q' hpsq hqsq K₀ M₀)
      _ _ _ (pullbackToTensor_naturality' p' q' ψX.hom ψY.hom) _ _ hB _
      (map_prod_comp_inv (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf))
        (derivedPullback p') (derivedPullback q') (asIso (pushforwardComparisonQ τX K₀))
        (asIso (pushforwardComparisonQ τY M₀)) (DerivedCategory.Q.map ψX.hom)
        (DerivedCategory.Q.map ψY.hom))
      _ hc)

end Stacks.Cohomology.BoxKunnethFlat

end
