module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorOnModels
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion

/-!
# The base-change comparison for a derived tensor product on K-flat representatives

For a morphism of ringed spaces `h : X ⟶ Y`, K-flat complexes `P`, `N` on `Y` and a map of
complexes `a : h^*N ⟶ W`, the comparison `Lh^*(P ⊗^L N) ⟶ Lh^*P ⊗^L W` of Tag 079U followed by
the map induced by `a` is computed by the comparison `h^*Tot(P ⊗ N) ≅ Tot(h^*P ⊗ h^*N)` of
Stacks 01CD followed by `h^*P ⊗ a`, through the canonical maps to total tensor complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.baseChangeTensorComparison_comp_toTensor`: on K-flat
  representatives, the base-change comparison followed by the canonical map to the total tensor
  complex equals the left comparison followed by `h^*Tot(P ⊗ N) ≅ Tot(h^*P ⊗ h^*N)` and `h^*P ⊗ a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace CategoryTheory

private theorem chase_btc {C : Type*} [Category C] {A₀ A₁ A₂ B₁ B₂ B₃ D₁ D₂ T₁ E₀ : C}
    (btc : A₀ ⟶ B₂) (u79 : A₀ ⟶ A₂) (lC : A₀ ⟶ A₁) (rC : A₂ ⟶ A₁) (iR : A₁ ⟶ A₂)
    (φ₁ : A₂ ⟶ B₁) (φ₂ : B₁ ⟶ B₂) (dP : B₂ ⟶ B₃)
    (tt : B₃ ⟶ E₀) (dP' : A₂ ⟶ D₁) (φ₁' : D₁ ⟶ D₂) (dP'' : B₁ ⟶ D₂) (φ₂' : D₂ ⟶ B₃)
    (t₁ : D₂ ⟶ T₁) (pinv : T₁ ⟶ A₁) (qm : T₁ ⟶ E₀) (ph : A₁ ⟶ T₁) (φ₀ : A₂ ⟶ B₂)
    (Qmm : A₁ ⟶ E₀)
    (hbtc : btc = u79 ≫ φ₀) (hu : u79 = lC ≫ iR)
    (hφ : φ₀ = φ₁ ≫ φ₂) (hir : iR ≫ rC = 𝟙 _) (hr : rC = dP' ≫ φ₁' ≫ t₁ ≫ pinv)
    (n1 : φ₂ ≫ dP = dP'' ≫ φ₂')
    (n2 : φ₁ ≫ dP'' = dP' ≫ φ₁') (tn : φ₂' ≫ tt = t₁ ≫ qm) (hp : pinv ≫ ph = 𝟙 _)
    (hq : Qmm = ph ≫ qm) :
    btc ≫ dP ≫ tt = lC ≫ Qmm := by
  subst hbtc hu hφ hq
  have h3 : dP' ≫ φ₁' ≫ t₁ = rC ≫ ph := by
    rw [hr]; simp only [Category.assoc, hp, Category.comp_id]
  simp only [Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, tn, reassoc_of% h3, reassoc_of% hir]

end CategoryTheory

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Presheaf.IsSheaf TopCat.Sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The base-change comparison for a derived tensor product, on K-flat representatives.** -/
theorem baseChangeTensorComparison_comp_toTensor
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y P)
    (hN : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y N)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (a : (pullbackComplex f).obj N ⟶ W) :
    Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison f
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj W)
        ((derivedPullbackNatTrans f).app N ≫ DerivedCategory.Q.map a) ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        ((derivedPullbackNatTrans f).app P)).app (DerivedCategory.Q.obj W) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        ((pullbackComplex f).obj P) W =
    (leftComparison f).app (P, N) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (P, N) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 _) a
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) := by
  have e1 := derivedPullbackTensorIso_hom_app_of_kFlat f P N hP hN
  have n1 := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
    ((derivedPullbackNatTrans f).app P)).naturality (DerivedCategory.Q.map a)
  have n2 := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
    ((derivedPullbackNatTrans f).app P)).naturality ((derivedPullbackNatTrans f).app N)
  have tn :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor_naturality
      (𝟙 ((pullbackComplex f).obj P)) a
  have tn' : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map (DerivedCategory.Q.map a) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        ((pullbackComplex f).obj P) W =
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 _) a
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) := by
    rw [← tn, DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
  have hr : (rightComparison f).app (P, N) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        ((derivedPullbackNatTrans f).app P)).app _ ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
          ((derivedPullbackNatTrans f).app N) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (P, N)) := by
    dsimp only [rightComparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, derivedToTensorNatTrans, NatTrans.prod, Functor.prod_obj]
    exact Category.assoc _ _ _
  have := isIso_rightComparison_app f P N hP hN
  have hu : (derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (leftComparison f).app (P, N) ≫ inv ((rightComparison f).app (P, N)) := by
    rw [e1]; rfl
  have hp : DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (P, N)) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (P, N)) = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app, DerivedCategory.Q.map_id]
  exact chase_btc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl hu (Functor.map_comp _ _ _)
    (IsIso.inv_hom_id _) hr n1 n2 tn' hp (DerivedCategory.Q.map_comp _ _)

/-- For a K-flat complex `P` on `Y`, the canonical map `P ⊗^L N ⟶ Tot(P ⊗ N)` is an isomorphism. -/
theorem isIso_toTensor_of_kFlat
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y P) :
    IsIso ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).toTensor
      P N) := by
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Y.sheaf).toTensor_eq_comparisonLeft _ _ hP]
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- For a K-flat complex `P` on `Y`, the map `Lh^*P ⊗^L W ⟶ h^*P ⊗^L W ⟶ Tot(h^*P ⊗ W)` induced
by `Lh^*P ⟶ h^*P` followed by the canonical map to the total tensor complex is an isomorphism. -/
theorem isIso_tensorMap_toTensor_of_kFlat
    (P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hP : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y P)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    IsIso (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        ((derivedPullbackNatTrans f).app P)).app (DerivedCategory.Q.obj W) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        ((pullbackComplex f).obj P) W) := by
  have hpc : IsIso ((derivedPullbackNatTrans f).app P) := isIso_derivedPullbackNatTrans_app f P hP
  have hgP := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f P hP
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    X.sheaf).toTensor_eq_comparisonLeft _ _ hgP]
  infer_instance

/-- The left comparison on K-flat representatives, as a composite. -/
theorem leftComparison_app_eq
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (leftComparison f).app (P, N) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).toTensor P N) ≫
      (derivedPullbackNatTrans f).app
        (HomologicalComplex.mapBifunctor P N (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
          (ComplexShape.up ℤ)) := rfl

end Stacks.Cohomology.DerivedPullbackTensor
