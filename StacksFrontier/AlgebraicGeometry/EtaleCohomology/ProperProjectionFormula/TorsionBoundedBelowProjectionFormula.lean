module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionBoundedBelowRingedBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.GeometricPointConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.ProjectionMapComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointProjectionFormulaBoundedBelow.Main
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.BoundedBelowInputs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaBaseChangeAtObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TransportedProjectionMap

/-!
# The projection formula for a proper morphism and a bounded below torsion object

## Main results

* `Stacks.EtaleCohomology.isIso_projectionFormulaMap_etaleRingedToposHom_of_isGE_of_tensor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard
-- (no HasSheafify override here)
attribute [local instance]
  Stacks.EtaleCohomology.etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor

universe u

namespace Stacks.EtaleCohomology

/-- The projection formula on the constant ringed topoi for a proper morphism, a bounded below
`E` with torsion cohomology sheaves and a bounded below `K`, given that `E ⊗^L f^{-1}K` is bounded
below with torsion cohomology sheaves. -/
theorem isIso_projectionFormulaMap_etaleRingedToposHom_of_isGE_of_tensor
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : DerivedCategory (EtaleModules.{u, 0} ℤ X)) (a : ℤ) (hE : E.IsGE a)
    (hT : ∀ n, IsTorsionEtaleModule.{u, 0} ℤ X ((DerivedCategory.homologyFunctor _ n).obj E))
    (K : DerivedCategory (EtaleModules.{u, 0} ℤ Y)) (b : ℤ) (hK : K.IsGE b) (c : ℤ)
    (hEK : (((etaleDerivedTensor.{u, 0} ℤ X).obj E).obj
      ((etaleModuleDerivedInverseImage.{u, 0} ℤ f).obj K)).IsGE c)
    (hTK : ∀ n, IsTorsionEtaleModule.{u, 0} ℤ X ((DerivedCategory.homologyFunctor _ n).obj
      (((etaleDerivedTensor.{u, 0} ℤ X).obj E).obj
        ((etaleModuleDerivedInverseImage.{u, 0} ℤ f).obj K)))) :
    IsIso (projectionFormulaMap (etaleRingedToposHom.{u, 0} ℤ f)
      ((etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj E)
      ((etaleDerivedEquivalence.{u, 0} ℤ Y).functor.obj K)) := by
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ X)
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ Y)
  refine isIso_of_forall_isIso_etaleRingedDerivedPullback_map ℤ _ fun y => ?_
  have hP : IsProper (pullback.snd f y.hom) := inferInstance
  have : QuasiCompact (pullback.snd f y.hom) :=
    @AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ _ hP.toUniversallyClosed
  have : QuasiSeparated (pullback.snd f y.hom) :=
    @AlgebraicGeometry.IsSeparated.instQuasiSeparated _ _ _ hP.toIsSeparated
  have sq := IsPullback.of_hasPullback f y.hom
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ (pullback f y.hom))
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ (Spec (.of y.residueField)))
  let eT : (etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj
      (((etaleDerivedTensor.{u, 0} ℤ X).obj E).obj
        ((etaleModuleDerivedInverseImage.{u, 0} ℤ f).obj K)) ≅
      ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O).obj
        ((etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj E)).obj
        ((derivedPullback (etaleRingedToposHom.{u, 0} ℤ f)).obj
          ((etaleDerivedEquivalence.{u, 0} ℤ Y).functor.obj K)) :=
    (Stacks.CategoryTheory.ProjectionMapTransport.transportTensorCompIso
      (etaleDerivedEquivalence.{u, 0} ℤ X)
      (derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O)).app
        (E, (etaleModuleDerivedInverseImage.{u, 0} ℤ f).obj K) ≪≫
    ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O).obj
        ((etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj E)).mapIso
      ((etaleRingedDerivedPullbackIso.{u, 0} ℤ f).app K).symm
  have h1 := isIso_squareBaseChangeMap_of_isGE_of_isProper ℤ f sq E a hE hT
  have h2₀ := isIso_squareBaseChangeMap_of_isGE_of_isProper ℤ f sq _ c hEK hTK
  have h3₀ := isIso_etalePushforwardProjectionMap_of_isGE_of_isSepClosed y.residueField
    (pullback.snd f y.hom)
    ((etaleModuleDerivedInverseImage.{u, 0} ℤ (pullback.fst f y.hom)).obj E) a
    (isGE_etaleModuleDerivedInverseImage_obj ℤ (pullback.fst f y.hom) E a hE)
    ((etaleModuleDerivedInverseImage.{u, 0} ℤ y.hom).obj K) b
    (isGE_etaleModuleDerivedInverseImage_obj ℤ y.hom K b hK)
  have h3₁ := (isIso_etalePushforwardProjectionMap_iff ℤ (pullback.snd f y.hom) _ _).1 h3₀
  have h3 := (isIso_projectionFormulaMap_iff_of_iso.{u + 1}
    (X := (etaleRingedSite.{u, 0} ℤ (pullback f y.hom)).ringedTopos)
    (Y := (etaleRingedSite.{u, 0} ℤ (Spec (.of y.residueField))).ringedTopos)
    (f := etaleRingedToposHom.{u, 0} ℤ (pullback.snd f y.hom))
    ((etaleRingedDerivedPullbackIso.{u, 0} ℤ (pullback.fst f y.hom)).app E)
    ((etaleRingedDerivedPullbackIso.{u, 0} ℤ y.hom).app K)).2 h3₁
  exact isIso_derivedPullback_map_projectionFormulaMap_of_isIso.{u + 1}
    (etaleRingedToposHomSquareTwoIso.{u, 0} ℤ f y.hom (pullback.snd f y.hom) (pullback.fst f y.hom)
      pullback.condition) _ _ h1
    ((Stacks.CategoryTheory.BaseChange.isIso_map_iff_of_iso _ _ _ _ eT).1 h2₀) h3

end Stacks.EtaleCohomology

end
