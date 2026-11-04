module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Homology.DerivedCategory.Monoidal.ModelComparisonMonoidal
public import StacksFrontier.Homology.DerivedCategory.Monoidal.ModelComparisonLocalizedMonoidal

/-!
# The monoidal derived category of a ringed site does not depend on the model

For two models `h₁`, `h₂` of `D(Mod(O))` and a functor `Φ : D₁ ⥤ D₂` compatible with the
localization functors, `Φ` is monoidal for the derived monoidal structures
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` at the two models.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidalModelComparison`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d₁ d₂ u

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (h₁ : HasDerivedCategory.{d₁} (Mod R)) (h₂ : HasDerivedCategory.{d₂} (Mod R))
  (Φ : @DerivedCategory (Mod R) _ _ h₁ ⥤ @DerivedCategory (Mod R) _ _ h₂)
  (e : @DerivedCategory.Qh (Mod R) _ _ h₁ ⋙ Φ ≅ @DerivedCategory.Qh (Mod R) _ _ h₂)

/-- **A comparison of two models of `D(Mod(O))` is monoidal** for the derived tensor product of
Tag 0FPT at both models. -/
@[instance_reducible]
def derivedMonoidalModelComparison :
    letI := @derivedMonoidal C _ J R _ _ h₁
    letI := @derivedMonoidal C _ J R _ _ h₂
    Φ.Monoidal :=
  CochainComplex.KFlatMonoidal.modelComparisonMonoidal h₁ h₂ (exists_kFlat_resolution R) Φ e

end Stacks.SheafOfModules.DerivedMonoidal

end
