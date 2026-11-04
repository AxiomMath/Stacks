module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.ConstantIntTwoTermFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude

/-!
# The derived tensor product of bounded below objects of `D(X_étale, ℤ)`

Let `X` be a scheme. For objects `E` and `F` of `D(X_étale, ℤ)` whose cohomology sheaves vanish
below `a` and below `b`, the cohomology sheaves of `E ⊗^L_ℤ F` vanish below `a + b - 1`.

Every sheaf of modules over the constant sheaf of rings `ℤ̲` has a resolution by two flat sheaves
of modules (`AlgebraicGeometry.RingedSite.hasTwoTermFlatResolutions_constant_int`), so the bound
holds on the constant ringed site `(X_étale, ℤ̲)`
(`Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_isGE_of_twoTermFlat`). It is read on
`D(X_étale, ℤ)` through the equivalence `Stacks.EtaleCohomology.etaleDerivedEquivalence`, which is
induced by an exact equivalence of abelian categories and so preserves lower bounds on cohomology.

## Main results

* `Stacks.EtaleCohomology.isGE_etaleDerivedTensor_of_isGE`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product of `D^{≥ a}` and `D^{≥ b}` lies in `D^{≥ a + b - 1}`** on
`D(X_étale, ℤ)`. The loss of one degree is the flat dimension of sheaves of `ℤ̲`-modules. -/
theorem isGE_etaleDerivedTensor_of_isGE {X : Scheme.{u}}
    (E F : DerivedCategory (EtaleModules.{u, 0} ℤ X)) (a b : ℤ) (hE : E.IsGE a)
    (hF : F.IsGE b) :
    (((etaleDerivedTensor.{u, 0} ℤ X).obj E).obj F).IsGE (a + b - 1) := by
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ X)
  have hG : ∀ (G : DerivedCategory (EtaleModules.{u, 0} ℤ X)) (n : ℤ), G.IsGE n →
      ((etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj G).IsGE n :=
    Stacks.Cohomology.DerivedInternalHomPullback.isGE_mapDerivedCategory_obj
      (etaleModulesEquivalence.{u, 0} ℤ X).functor
  have hT := Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_isGE_of_twoTermFlat
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (etaleRingedSite.{u, 0} ℤ X))
    (AlgebraicGeometry.RingedSite.hasTwoTermFlatResolutions_constant_int _) _ _ a b
    (hG E a hE) (hG F b hF)
  have hT' : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (etaleRingedSite.{u, 0} ℤ X).O).obj ((etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj E)).obj
        ((etaleDerivedEquivalence.{u, 0} ℤ X).functor.obj F)).IsGE (a + b - 1) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
        (etaleRingedSite.{u, 0} ℤ X)).app _).app _).symm (a + b - 1)
  exact Stacks.Cohomology.DerivedInternalHomPullback.isGE_mapDerivedCategory_obj
    (etaleModulesEquivalence.{u, 0} ℤ X).inverse _ _ hT'

end Stacks.EtaleCohomology

end
