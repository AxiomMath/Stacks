module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.PullbackStalkTensorCohomology

/-!
# The map of Stacks 0DJ7 at a tensor product, on stalks

The ring-level map of Stacks 0DJ7 at the stalks of the total tensor complex of K-flat complexes
`P`, `N` and a map `g'^*N ⟶ W` is the ring-level map for the tensor product of the stalk of `P`
with the one for `N`; with `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_tensor` it
is invertible when the one for `N` is.

## Main results

* `Stacks.ModuleSkyscraper.tensor_stalk_square`: the ring-level comparison map at the stalk of a
  total tensor complex is, up to the stalk isomorphisms, the one for the tensor product of stalks.
* `Stacks.ModuleSkyscraper.isIso_ring_tensor_stalk`: the ring-level base change map on cohomology
  at the stalk of `P ⊗ N` is invertible when the one at the stalk of `N` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-- The comparison `alphaH A A'` is natural: for a map `φ : K ⟶ L` of complexes of `A`-modules it
intertwines the derived extension of scalars of `φ` with the termwise extension of scalars of `φ`.
-/
theorem alphaH_naturality {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A A')).functor.map (DerivedCategory.Q.map φ) ≫ alphaH A A' L =
      alphaH A A' K ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A A')).comparison.naturality φ

/-- Naturality of `alphaH A A'` for a map `φ : K ⟶ P ⊗ N` into a tensor product of complexes. -/
theorem alphaH_naturality_tensor {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {K P N : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ P ⊗ N) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A A')).functor.map (DerivedCategory.Q.map φ) ≫ alphaH A A' (P ⊗ N) =
      alphaH A A' K ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  alphaH_naturality φ

end RingTheory.TorIndependence

namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

variable {X X' : Scheme.{u}} (g' : X' ⟶ X) (x' : X')

/-- The isomorphism between the stalk at `x'` of the total tensor complex of `g'^*P` and `W` and
the tensor product of the base change of the stalk of `P` at `g' x'` with the stalk of `W`. -/
def targetStalkIso
    (P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X'.toRingedSpace) ℤ) :
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    (stk x').obj (HomologicalComplex.mapBifunctor
        ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj P) W
        (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)) ≅
      ((baseChangeFunctor (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((stk (g' x')).obj P) ⊗ (stk x').obj W :=
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  modulesStalkTotalIso x' _ W ≪≫ whiskerRightIso ((pullbackStalkComplex g' x' P).symm ≪≫
    (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x')) (ComplexShape.up ℤ)).symm.app ((stk (g' x')).obj P)) ((stk x').obj W)

/-- In a category, `p ≫ m₁ ≫ m₂ ≫ τ ≫ v = (p ≫ m) ≫ T` whenever `m = m₁ ≫ m₂` and `T = τ ≫ v`.
-/
theorem reassoc_five {C : Type*} [Category C] {A B D E F G : C} (p : A ⟶ B) (m₁ : B ⟶ D)
    (m₂ : D ⟶ E) (τ : E ⟶ F) (v : F ⟶ G) (m : B ⟶ E) (T : E ⟶ G) (hm : m = m₁ ≫ m₂)
    (hT : T = τ ≫ v) : p ≫ m₁ ≫ m₂ ≫ τ ≫ v = (p ≫ m) ≫ T := by
  subst hm hT
  simp only [Category.assoc]

/-- Pasting of two commutative squares: if `Tθ ≫ α₂ = α₁ ≫ eσ` and `eσ ≫ u₂ = u₁ ≫ τ`, then
`Tθ ≫ α₂ ≫ u₂ = (α₁ ≫ u₁) ≫ τ`. -/
theorem comparison_chase {C : Type*} [Category C] {A₀ A₁ B₀ B₁ C₀ C₁ : C}
    (Tθ : A₀ ⟶ A₁) (α₂ : A₁ ⟶ B₁) (α₁ : A₀ ⟶ B₀) (eσ : B₀ ⟶ B₁) (u₂ : B₁ ⟶ C₁) (u₁ : B₀ ⟶ C₀)
    (τ : C₀ ⟶ C₁) (hn : Tθ ≫ α₂ = α₁ ≫ eσ) (hc : eσ ≫ u₂ = u₁ ≫ τ) :
    Tθ ≫ α₂ ≫ u₂ = (α₁ ≫ u₁) ≫ τ := by
  rw [reassoc_of% hn, hc, Category.assoc]

/-- Under the isomorphisms `modulesStalkTotalIso` and `targetStalkIso`, the map `alphaH` for the
stalk of the total tensor complex of `P` and `N`, followed by the stalk of the map
`g'^*(P ⊗ N) ⟶ g'^*P ⊗ W` induced by `a`, agrees with `alphaH` for the tensor product of the stalks
of `P` and `N`, followed by the stalk of `P` tensored with the stalk of `a`. -/
theorem tensor_stalk_square
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X'.toRingedSpace) ℤ)
    (a : (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj N ⟶ W) :
    (letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x'))).functor.map
        (DerivedCategory.Q.map (modulesStalkTotalIso (g' x') P N).hom) ≫
      (alphaH (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')
        ((stk (g' x')).obj P ⊗ (stk (g' x')).obj N) ≫
        DerivedCategory.Q.map ((extTensorIso ((stk (g' x')).obj P)
        ((stk (g' x')).obj N)).hom ≫
        (((baseChangeFunctor (X.presheaf.stalk (g' x'))
          (X'.presheaf.stalk x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((stk (g' x')).obj P) ◁
          ((pullbackStalkComplex g' x' N).hom ≫ (stk x').map a)))) =
    (alphaH (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') ((stk (g' x')).obj
          (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))) ≫
        DerivedCategory.Q.map ((pullbackStalkComplex g' x'
          (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))).hom ≫
          (stk x').map ((Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
            g'.toLRSHom.toShHom).hom.app (P, N) ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) a
              (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)))) ≫
      DerivedCategory.Q.map (targetStalkIso g' x' P W).hom) := by
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  have HC : ((ModuleCat.extendScalars (algebraMap (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (modulesStalkTotalIso (g' x') P N).hom ≫
      (extTensorIso ((stk (g' x')).obj P) ((stk (g' x')).obj N)).hom ≫
      (((baseChangeFunctor (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((stk (g' x')).obj P) ◁
        ((pullbackStalkComplex g' x' N).hom ≫ (stk x').map a)) =
      ((pullbackStalkComplex g' x' (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))).hom ≫
        (stk x').map ((Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
            g'.toLRSHom.toShHom).hom.app (P, N) ≫
          HomologicalComplex.mapBifunctorMap (𝟙 _) a
            (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ))) ≫
        (targetStalkIso g' x' P W).hom :=
    (pullbackStalk_tensor_coh g' x' P N W a).trans (reassoc_five _ _ _ _ _ _ _
      (Functor.map_comp _ _ _) rfl)
  have hn := alphaH_naturality_tensor (A := X.presheaf.stalk (g' x'))
    (A' := X'.presheaf.stalk x') (P := (stk (g' x')).obj P) (N := (stk (g' x')).obj N)
    (modulesStalkTotalIso (g' x') P N).hom
  have hq := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map HC).trans
      (DerivedCategory.Q.map_comp _ _))
  exact comparison_chase _ _ _ _ _ _ _ hn hq

variable {S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'}

/-- Let `P` be a complex whose stalk at `g' x'` is K-flat, and suppose `X'_{x'}` is a localization
of `X_{g' x'} ⊗ S'_{f' x'}`. If the ring-level base change map on cohomology for the stalks of `N`
and `W` along `a` is an isomorphism in every degree, then so is the one for the stalks of the
total tensor complexes of `P`, `N` and of `g'^*P`, `W`. -/
theorem isIso_ring_tensor_stalk (w : g' ≫ f = f' ≫ g)
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X'.toRingedSpace) ℤ)
    (a : (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj N ⟶ W)
    (hP : CochainComplex.KFlat ((stk (g' x')).obj P)) :
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' w x').toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
      (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    letI : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
      ((f'.stalkMap x').hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
    ∀ (M : Submonoid (X.presheaf.stalk (g' x') ⊗[S.presheaf.stalk (f (g' x'))]
        S'.presheaf.stalk (f' x'))),
      (letI := (baseChangeTensorRingMap (R := S.presheaf.stalk (f (g' x')))
        (A := X.presheaf.stalk (g' x')) (R' := S'.presheaf.stalk (f' x'))
        (A' := X'.presheaf.stalk x')).toAlgebra
      IsLocalization M (X'.presheaf.stalk x')) →
      (∀ n, IsIso (ringBaseChangeCohomologyMap (R := S.presheaf.stalk (f (g' x')))
        (R' := S'.presheaf.stalk (f' x'))
        (DerivedCategory.Q.obj ((stk (g' x')).obj N)) (DerivedCategory.Q.obj ((stk x').obj W))
        (alphaH _ _ _ ≫ DerivedCategory.Q.map ((pullbackStalkComplex g' x' N).hom ≫
          (stk x').map a)) n)) →
      ∀ n, IsIso (ringBaseChangeCohomologyMap (R := S.presheaf.stalk (f (g' x')))
        (R' := S'.presheaf.stalk (f' x'))
        (DerivedCategory.Q.obj ((stk (g' x')).obj (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))))
        (DerivedCategory.Q.obj ((stk x').obj (HomologicalComplex.mapBifunctor
          ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj P) W
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ))))
        (alphaH _ _ _ ≫ DerivedCategory.Q.map ((pullbackStalkComplex g' x'
          (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))).hom ≫
          (stk x').map ((Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
            g'.toLRSHom.toShHom).hom.app (P, N) ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) a
              (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)))) n) := by
  intro M hloc h n
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  have key := isIso_ringBaseChangeCohomologyMap_tensor M hloc ((stk (g' x')).obj P) hP
    ((stk (g' x')).obj N) ((stk x').obj W)
    ((pullbackStalkComplex g' x' N).hom ≫ (stk x').map a) h n
  rw [← isIso_choose_ringBaseChangeCohomologyMap_iff] at key ⊢
  exact (isIso_chosenBaseChangeMap_iff_of_iso
    (DerivedCategory.Q.mapIso (modulesStalkTotalIso (g' x') P N))
    (DerivedCategory.Q.mapIso (targetStalkIso g' x' P W)) _ _
    (tensor_stalk_square g' x' P N W a) n).2 key

end Stacks.ModuleSkyscraper
