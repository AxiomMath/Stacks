module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Product
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a product of abelian sheaves

Let `(C, J)` be a site, `(F i)_{i ∈ I}` a family of abelian sheaves on it admitting a product,
and `U` an object of `C`. The projections `∏ F ⟶ F i` induce a canonical map
`H^p(U, ∏ F) ⟶ ∏ H^p(U, F i)`, which is an isomorphism for `p = 0` and injective for `p = 1`.

Cohomology here is the `Ext`-group out of the free abelian sheaf on the Yoneda presheaf of `U`,
so the canonical map is the corestriction of extension classes along the projections, and both
assertions are the corresponding statements about extension groups.

## Main results

* `Stacks.Cohomology.SheafProducts.isIso_piComparison_cohomology_zero`: the comparison in
  degree zero is an isomorphism.
* `Stacks.Cohomology.SheafProducts.mono_piComparison_cohomology_one`: the comparison in degree
  one is a monomorphism.
-/

@[expose] public noncomputable section

universe x w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SheafProducts

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

/-- **Degree-zero cohomology commutes with arbitrary products of abelian sheaves**: for a family
`(F i)` of abelian sheaves on a site and an object `U`, the canonical map
`H^0(U, ∏ F) ⟶ ∏ H^0(U, F i)` is an isomorphism. -/
@[stacks 060L "degree zero"]
public theorem isIso_piComparison_cohomology_zero {I : Type x}
    (F : I → Sheaf J AddCommGrpCat.{v}) (U : C) [HasProduct F]
    [HasProduct fun i ↦
      (Sheaf.cohomologyPresheafFunctor J 0 ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U)).obj (F i)] :
    IsIso (piComparison
      (Sheaf.cohomologyPresheafFunctor J 0 ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U)) F) := by
  let : HasProduct fun i ↦ (Abelian.extFunctorObj.{w'}
      ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat).obj U) 0).obj (F i) := by
    change HasProduct fun i ↦
      (Sheaf.cohomologyPresheafFunctor J 0 ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U)).obj (F i)
    infer_instance
  have key : IsIso (piComparison (Abelian.extFunctorObj.{w'}
      ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat).obj U) 0) F) :=
    Abelian.isIso_piComparison_extFunctorObj_zero F _
  exact key

/-- **Degree-one cohomology of a product of abelian sheaves injects into the product**: for a
family `(F i)` of abelian sheaves on a site and an object `U`, the canonical map
`H^1(U, ∏ F) ⟶ ∏ H^1(U, F i)` is a monomorphism. -/
@[stacks 060L "degree one"]
public theorem mono_piComparison_cohomology_one {I : Type x}
    (F : I → Sheaf J AddCommGrpCat.{v}) (U : C) [HasProduct F]
    [HasProduct fun i ↦
      (Sheaf.cohomologyPresheafFunctor J 1 ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U)).obj (F i)] :
    Mono (piComparison
      (Sheaf.cohomologyPresheafFunctor J 1 ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U)) F) := by
  let : HasProduct fun i ↦ (Abelian.extFunctorObj.{w'}
      ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat).obj U) 1).obj (F i) := by
    change HasProduct fun i ↦
      (Sheaf.cohomologyPresheafFunctor J 1 ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w'}).obj (op U)).obj (F i)
    infer_instance
  have key : Mono (piComparison (Abelian.extFunctorObj.{w'}
      ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat).obj U) 1) F) :=
    Abelian.mono_piComparison_extFunctorObj_one F _
  exact key

end Stacks.Cohomology.SheafProducts

end
