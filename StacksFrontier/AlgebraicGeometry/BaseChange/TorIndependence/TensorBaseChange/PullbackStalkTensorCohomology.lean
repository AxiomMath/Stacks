module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.PullbackStalkTensorComplex

/-!
# Stacks 01CD on stalks, followed by a map of complexes

The stalk identification of `PullbackStalkTensorComplex`, composed with the stalk of a map of
complexes out of the second factor, in the form used to compute the map of Stacks 0DJ7 at a
tensor product.

## Main results

* `Stacks.ModuleSkyscraper.pullbackStalk_tensor_coh`: the stalk identification of the pullback of
  a total tensor complex, composed with the stalk of a map of complexes out of the second factor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u

namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

variable {X X' : Scheme.{u}} (g' : X' ⟶ X) (x' : X')

/-- In a monoidal category, if `v ≫ w = a'`, then `(u ⊗ₘ v) ≫ (K₂ ◁ w)` equals
`(K₁ ◁ a') ≫ (u ▷ L₃)`. -/
theorem tensorHom_comp_whiskerLeft_eq {C : Type*} [Category C] [MonoidalCategory C]
    {K₁ K₂ L₁ L₂ L₃ : C} (u : K₁ ⟶ K₂) (v : L₁ ⟶ L₂) (w : L₂ ⟶ L₃) (a' : L₁ ⟶ L₃)
    (h : v ≫ w = a') : (u ⊗ₘ v) ≫ (K₂ ◁ w) = (K₁ ◁ a') ≫ (u ▷ L₃) := by
  rw [← h, tensorHom_def', Category.assoc, ← whisker_exchange, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-- Given commuting relations `p₁ ≫ p₂ ≫ t₁ ≫ m = E' ≫ Xx`, `s ≫ t₂ = t₁ ≫ wa'` and
`m ≫ wl = wa ≫ ur` with `wa' = wa`, the composites `E' ≫ Xx ≫ wl` and
`p₁ ≫ p₂ ≫ s ≫ t₂ ≫ ur` agree. -/
theorem chase_coh {C : Type*} [Category C] {A B Cc D E F G H I : C} (p₁ : A ⟶ B) (p₂ : B ⟶ Cc)
    (t₁ : Cc ⟶ D) (m : D ⟶ E) (E' : A ⟶ F) (Xx : F ⟶ E) (wl : E ⟶ G) (wa' wa : D ⟶ H)
    (ur : H ⟶ G) (s : Cc ⟶ I) (t₂ : I ⟶ H)
    (h1 : p₁ ≫ p₂ ≫ t₁ ≫ m = E' ≫ Xx) (h2 : s ≫ t₂ = t₁ ≫ wa') (hw : wa' = wa)
    (h3 : m ≫ wl = wa ≫ ur) :
    E' ≫ Xx ≫ wl = p₁ ≫ p₂ ≫ s ≫ t₂ ≫ ur := by
  rw [← reassoc_of% h1, h3, reassoc_of% h2, hw]

/-- **Stacks 01CD on the stalks of total tensor complexes, followed by a map of complexes.** -/
theorem pullbackStalk_tensor_coh
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X'.toRingedSpace) ℤ)
    (a : (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj N ⟶ W) :
    (letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    ((ModuleCat.extendScalars (algebraMap (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (modulesStalkTotalIso (g' x') P N).hom ≫
      (extTensorIso ((stk (g' x')).obj P) ((stk (g' x')).obj N)).hom ≫
      (((baseChangeFunctor (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((stk (g' x')).obj P) ◁
        ((pullbackStalkComplex g' x' N).hom ≫ (stk x').map a)) =
    (pullbackStalkComplex g' x' (HomologicalComplex.mapBifunctor P N
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))).hom ≫
      (stk x').map ((Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
          g'.toLRSHom.toShHom).hom.app (P, N)) ≫
      (stk x').map (HomologicalComplex.mapBifunctorMap (𝟙 _) a
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf) (ComplexShape.up ℤ)) ≫
      (modulesStalkTotalIso x' _ W).hom ≫
      (((pullbackStalkComplex g' x' P).inv ≫
          (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
            (X'.presheaf.stalk x')) (ComplexShape.up ℤ)).inv.app ((stk (g' x')).obj P)) ▷
        (stk x').obj W)) := by
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  have h1 := pullbackStalk_tensorComplex g' x' P N
  have h2 := CategoryTheory.Functor.mapBifunctorTotalIso_hom_naturality
    (Stacks.SheafOfModules.Tensor.sheafTensor X'.sheaf)
    (curriedTensor (ModuleCat.{u} (X'.presheaf.stalk x'))) (tensorModulesStalkFunctor x')
    (tensorModulesStalkFunctor x') (tensorModulesStalkFunctor x') (modulesStalkTensorIso x')
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ)
    (fun φ N => modulesStalkTensorIso_naturality_left x' φ N)
    (fun M _ _ ψ => modulesStalkTensorIso_naturality_right x' M ψ)
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj P)
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj P)
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj N) W
    (𝟙 _) a
  have h3 := tensorHom_comp_whiskerLeft_eq ((pullbackStalkComplex g' x' P).inv ≫
          (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
            (X'.presheaf.stalk x')) (ComplexShape.up ℤ)).inv.app ((stk (g' x')).obj P))
    (pullbackStalkComplex g' x' N).inv ((pullbackStalkComplex g' x' N).hom ≫ (stk x').map a)
    ((stk x').map a) (Iso.inv_hom_id_assoc _ _)
  have h4 : HomologicalComplex.mapBifunctorMap
      ((stk x').map (𝟙 ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex
        g'.toLRSHom.toShHom).obj P))) ((stk x').map a)
      (curriedTensor (ModuleCat.{u} (X'.presheaf.stalk x'))) (ComplexShape.up ℤ) =
      (stk x').obj ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex
        g'.toLRSHom.toShHom).obj P) ◁ (stk x').map a := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact chase_coh _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h4 h3

end Stacks.ModuleSkyscraper
