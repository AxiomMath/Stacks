module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison

/-!
# Stacks 07A4 is the tensorator of `f^*` applied termwise
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.SheafOfModules.DerivedMonoidal

section Bookkeeping

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- **The comparison of the monoidal tensor product of Stacks 0FPT with the canonical derived
tensor product carries the K-flat comparison of the latter back to `derivedTensorIso`.** -/
theorem monoidalTensorCanonicalIso_hom_app_app_comp_comparison (K L : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    ((monoidalTensorCanonicalIso R).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison K L
          hK hL).hom =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R)
        hK hL).hom := by
  rw [monoidalTensorCanonicalIso, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    Category.assoc, canonicalTensorIso, derivedBifunctorTensorIso_comp_comparison,
    derivedTensorBifunctorIso_hom_app_app_eq]
  exact CochainComplex.KFlatMonoidal.derivedTensorCompare_comp_comparison (Mod R)
    (exists_kFlat_resolution R) hK hL

end Bookkeeping

end Stacks.SheafOfModules.DerivedMonoidal

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The two identifications of the derived tensor product of Stacks 08J8 with the canonical
one are the same.** Both are the comparison of `CochainComplex.KFlatBifunctor.derivedBifunctor`
with the derived tensor product of the ringed site, descended from the same K-flat comparison,
followed by `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`. -/
theorem interfaceTensorCanonicalIso_eq_derivedTensorFunctorIso :
    Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X =
      derivedTensorFunctorIso X :=
  rfl

end AlgebraicGeometry.RingedSite

end
