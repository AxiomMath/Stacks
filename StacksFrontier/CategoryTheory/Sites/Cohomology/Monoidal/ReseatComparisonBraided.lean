module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorConstraints
public import StacksFrontier.CategoryTheory.Monoidal.ReseatBraiding
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedTwoSided

/-!
# The comparison of Tag 0FPT's tensor product with the derived bifunctor, on the nose

`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso` identifies the tensor product
of the monoidal derived category of Tag 0FPT with the derived tensor bifunctor of Tag 06YU.  It
is built as `CategoryTheory.eqToIso` of an equality of bifunctors that holds by `rfl`, followed
by `CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso`; the `eqToIso` is therefore the
identity, but not syntactically so, and `rfl` does not see it because the equality's two sides
only agree past the unfolding of `DerivedCategory.Qh`, whose definition is not exposed.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso_hom_app_app`: on a pair of
  objects the comparison is `derivedLocalizedTensorIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

attribute [local instance] homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided
  kFlatQuotientMonoidal kFlatQuotientLaxBraided kFlatComplexQMonoidal kFlatComplexQLaxBraided

attribute [local instance] kFlatQLeft_isLocalization

/-- **The comparison of the tensor product of Tag 0FPT with the derived bifunctor of Tag 06YU
is the comparison of the localized tensor product**: the equality of functors that the former
is composed with is `rfl`, so the `eqToIso` it carries is the identity. -/
theorem derivedTensorBifunctorIso_hom_app_app (A B : DerivedModules R) :
    ((derivedTensorBifunctorIso R).hom.app A).app B =
      ((CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso (Mod R)).hom.app A).app B := by
  dsimp only [derivedTensorBifunctorIso, CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  exact Category.id_comp _

end Stacks.SheafOfModules.DerivedMonoidal

end
