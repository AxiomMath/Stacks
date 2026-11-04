module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Homology.DerivedCategory.Monoidal.ModelComparisonMonoidal

/-!
# The derived tensor product does not depend on the model of `D(Mod(O))`

For a ringed site `(C, O)` the monoidal structure
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` of [Stacks, Tag 0FPT] is defined at any
chosen model of the derived category `D(Mod(O))`. The comparison equivalence
`StacksDraft.DerivedModel.modelEquiv` of two models is a strong monoidal functor for the two
structures.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.modelEquivMonoidal` — the comparison is monoidal.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory StacksDraft.DerivedModel

universe w w' u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **The comparison of two models of `D(Mod(O))` is a strong monoidal functor** for the derived
tensor products `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` at the two models. -/
@[instance_reducible]
def modelEquivMonoidal (h₁ : HasDerivedCategory.{w} (Mod R))
    (h₂ : HasDerivedCategory.{w'} (Mod R)) :
    @Functor.Monoidal _ _ (@derivedMonoidal _ _ _ R _ _ h₁) _ _ (@derivedMonoidal _ _ _ R _ _ h₂)
      (modelEquiv h₁ h₂).functor :=
  modelEquivFunctorMonoidal (exists_kFlat_resolution R) h₁ h₂

end Stacks.SheafOfModules.DerivedMonoidal

end
