module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.TensorStalkSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeTensorComparisonOnModels
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkLocalization
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion

/-!
# Stacks 0DJA (1) on K-flat representatives

For a cartesian square of schemes, K-flat complexes `P`, `N` of `𝒪_X`-modules and a map of
complexes `a : g'^*N ⟶ W` such that the map of Stacks 0DJ7 at `L(g')^*N ⟶ W` is invertible at
every point and in every degree, the map of Stacks 0DJ7 at the base-change comparison
`L(g')^*(P ⊗^L N) ⟶ L(g')^*P ⊗^L W` is invertible at every point and in every degree.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_totalTensor`
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_tensor_of_kFlat`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u



namespace AlgebraicGeometry

open Stacks.ModuleSkyscraper Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- If two maps `φ₁ = φ₂ : L(g')^*K ⟶ K'` are equal and the base-change cohomology map of `φ₂`
at `x'` in degree `n` is an isomorphism, then so is that of `φ₁`. -/
theorem isIso_baseChangeCohomologyMap_of_eq (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ₁ φ₂ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g'.toLRSHom.toShHom).obj K ⟶ K') (e : φ₁ = φ₂) (x' : X') (n : ℤ)
    (h : IsIso (baseChangeCohomologyMap f g f' g' w K K' φ₂ x' n)) :
    IsIso (baseChangeCohomologyMap f g f' g' w K K' φ₁ x' n) := by
  subst e; exact h

/-- **Stacks 0DJA (1) on total tensor complexes of K-flat representatives.** -/
theorem isIso_baseChangeCohomologyMap_totalTensor (hpb : IsPullback g' f' f g)
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X'.toRingedSpace) ℤ)
    (a : (pullbackComplex g'.toLRSHom.toShHom).obj N ⟶ W)
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj W)
      (pullbackComparisonOnComplex g' N ≫ DerivedCategory.Q.map a) x' n))
    (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P N
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)))
      (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor
        ((pullbackComplex g'.toLRSHom.toShHom).obj P) W
        (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)))
      (pullbackComparisonOnComplex g' (HomologicalComplex.mapBifunctor P N
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso g'.toLRSHom.toShHom).hom.app (P, N) ≫
          HomologicalComplex.mapBifunctorMap (𝟙 _) a
            (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ))) x' n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' hpb.w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w x')
  obtain ⟨M, hM⟩ := exists_isLocalization_stalk hpb x'
  have hN' : ∀ m, IsIso (ringBaseChangeCohomologyMap (R := S.presheaf.stalk (f (g' x')))
        (R' := S'.presheaf.stalk (f' x'))
        (DerivedCategory.Q.obj ((stk (g' x')).obj N)) (DerivedCategory.Q.obj ((stk x').obj W))
        (alphaH _ _ _ ≫ DerivedCategory.Q.map ((pullbackStalkComplex g' x' N).hom ≫
          (stk x').map a)) m) := fun m =>
    (isIso_baseChangeCohomologyMap_complex_iff f g f' g' hpb.w N W a x' m).1 (h x' m)
  have hP' : CochainComplex.KFlat ((stk (g' x')).obj P) := kFlat_modulesStalkFunctor (g' x') P hP
  have key := isIso_ring_tensor_stalk g' x' hpb.w P N W a hP' M hM hN' n
  exact (isIso_baseChangeCohomologyMap_complex_iff f g f' g' hpb.w
    (HomologicalComplex.mapBifunctor P N (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
      (ComplexShape.up ℤ))
    (HomologicalComplex.mapBifunctor ((pullbackComplex g'.toLRSHom.toShHom).obj P) W
      (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ))
    ((pullbackTensorComplexNatIso g'.toLRSHom.toShHom).hom.app (P, N) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 _) a
        (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)) x' n).2 key

/-- **Stacks 0DJA (1) on K-flat representatives.** -/
theorem isIso_baseChangeCohomologyMap_tensor_of_kFlat (hpb : IsPullback g' f' f g)
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P)
    (hN : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace N)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X'.toRingedSpace) ℤ)
    (a : (pullbackComplex g'.toLRSHom.toShHom).obj N ⟶ W)
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj W)
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫ DerivedCategory.Q.map a) x' n))
    (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N))
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g'.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj P))).obj
          (DerivedCategory.Q.obj W))
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj W)
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app N ≫ DerivedCategory.Q.map a)) x' n) := by
  have hψ := isIso_tensorMap_toTensor_of_kFlat g'.toLRSHom.toShHom P hP W
  have hθ := isIso_toTensor_of_kFlat (Y := X.toRingedSpace) P N hP
  have key := isIso_baseChangeCohomologyMap_totalTensor hpb P N hP W a h x' n
  refine (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ _ _ hψ x' n).1 ?_
  have e := (baseChangeTensorComparison_comp_toTensor g'.toLRSHom.toShHom P N hP hN W a).trans
    ((congrArg (fun t => t ≫ _) (leftComparison_app_eq g'.toLRSHom.toShHom P N)).trans
      (Category.assoc _ _ _))
  exact isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _ e x' n
    ((isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hpb.w _ _ _
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor P N) hθ
      _ x' n).2 key)

end AlgebraicGeometry
