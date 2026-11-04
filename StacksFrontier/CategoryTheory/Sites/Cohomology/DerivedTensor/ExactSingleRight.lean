module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# Derived tensor product with a module whose tensor functor is exact

Let `L` be a sheaf of modules on a ringed site such that `- ⊗ L` is an exact functor `F`. Then
`L`, placed in degree zero, is K-flat, and for every `K ∈ D(𝒪)` the derived tensor product
`K ⊗^𝐋 L[0]` is `F` applied to `K` degreewise: `K ⊗^𝐋 L[0] ≅ F(K)`. This applies to every
invertible module, for which `- ⊗ L` is an autoequivalence.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.kFlat_single_of_tensor_eq`
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleRightIsoOfExact`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O) (L : Modules X.O) (F : Modules X.O ⥤ Modules X.O)
  [hFa : F.Additive] [hFl : PreservesFiniteLimits F] [hFc : PreservesFiniteColimits F]
  (hF : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj L = F)

include hF in
/-- A module `L` for which `- ⊗ L` is exact is K-flat when placed in degree zero. -/
theorem kFlat_single_of_tensor_eq :
    Stacks.SheafOfModules.KFlat.KFlat X.O
      ((HomologicalComplex.single (Modules X.O) (ComplexShape.up ℤ) 0).obj L) := by
  subst hF
  exact CochainComplex.KFlatBifunctor.kFlat_single_of_exact
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) _ 0
    (fun G hG k =>
      (hG k).map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj L))

/-- **Derived tensor product with a module with exact tensor functor.** If `- ⊗ L` is the exact
functor `F`, then `K ⊗^𝐋 L[0] ≅ F(K)`, with `F` extended to the derived category. -/
def singleRightIsoOfExact (K : DerivedModules X.O) :
    (T.tensor.obj K).obj ((DerivedCategory.singleFunctor (Modules X.O) 0).obj L) ≅
      F.mapDerivedCategory.obj K :=
  ((T.tensor.mapIso (RingedSite.kFlatModelIso X K)).app _).symm ≪≫
    T.comparisonRight (RingedSite.kFlatModel X K) _ (kFlat_single_of_tensor_eq X L F hF) ≪≫
    DerivedCategory.Q.mapIso
      (CochainComplex.KFlatBifunctor.totalSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (RingedSite.kFlatModel X K) L ≪≫
       eqToIso (by subst hF; rfl)) ≪≫
    (F.mapDerivedCategoryFactors.app (RingedSite.kFlatModel X K)).symm ≪≫
    F.mapDerivedCategory.mapIso (RingedSite.kFlatModelIso X K)

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
