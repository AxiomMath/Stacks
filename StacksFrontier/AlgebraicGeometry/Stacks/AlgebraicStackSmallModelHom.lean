module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel

/-!
# 1-morphisms between the small models of algebraic stacks

`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` presents an algebraic stack whose hom types
live above the universe of the schemes as an object of the 2-category of algebraic stacks of
Stacks 03YP. This file completes that construction on 1-morphisms: a based functor between two
such algebraic stacks is read between their small models, by undoing the shrinking of the hom
types of the source, applying the functor, and shrinking again.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.smallModelHom`: a based functor between two algebraic
  stacks, read as a 1-morphism between their small models.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.smallModelHom_toFunctor_comp_shrinkHoms_inverse`: the
  square comparing a based functor with its small model commutes on the nose.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v₁ v₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : BasedCategory.{v₁, u + 1} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, u + 1} (BigFppfOver B S hS)}

/-- **A based functor between two algebraic stacks, read between their small models**, as a
1-morphism of the 2-category of algebraic stacks of Stacks 03YP: undo the shrinking of the hom
types of the source, apply the functor, and shrink the hom types of the target. -/
noncomputable def AlgebraicStacks.smallModelHom
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴)
    (f : 𝒳 ⥤ᵇ 𝒴) :
    AlgebraicStacks.smallModel B S hS 𝒳 h𝒳 ⟶ AlgebraicStacks.smallModel B S hS 𝒴 h𝒴 :=
  letI := locallySmall_of_isAlgebraicStack B S hS h𝒳
  letI := locallySmall_of_isAlgebraicStack B S hS h𝒴
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp
      (BasedFunctor.comp (⟨ShrinkHoms.inverse.{u} 𝒳.obj, rfl⟩ : 𝒳.shrinkHoms.{u} ⥤ᵇ 𝒳) f)
      (⟨ShrinkHoms.functor.{u} 𝒴.obj, BasedCategory.shrinkHoms_functor_comp 𝒴⟩ :
        𝒴 ⥤ᵇ 𝒴.shrinkHoms.{u})))

/-- **The square comparing a based functor with its small model commutes on the nose**: following
the small model of the functor by the comparison out of the small model of the target is the
comparison out of the small model of the source followed by the functor. -/
theorem AlgebraicStacks.smallModelHom_toFunctor_comp_shrinkHoms_inverse
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴)
    (f : 𝒳 ⥤ᵇ 𝒴) :
    letI := locallySmall_of_isAlgebraicStack B S hS h𝒳
    letI := locallySmall_of_isAlgebraicStack B S hS h𝒴
    (AlgebraicStacks.smallModelHom B S hS h𝒳 h𝒴 f).hom.hom.toFunctor ⋙
        ShrinkHoms.inverse.{u} 𝒴.obj =
      ShrinkHoms.inverse.{u} 𝒳.obj ⋙ f.toFunctor := by
  let := locallySmall_of_isAlgebraicStack B S hS h𝒳
  let := locallySmall_of_isAlgebraicStack B S hS h𝒴
  change ShrinkHoms.inverse.{u} 𝒳.obj ⋙ f.toFunctor ⋙
    (ShrinkHoms.functor.{u} 𝒴.obj ⋙ ShrinkHoms.inverse.{u} 𝒴.obj) = _
  rw [BasedCategory.shrinkHoms_functor_comp_inverse 𝒴, Functor.comp_id]

end AlgebraicGeometry.Stack

end
