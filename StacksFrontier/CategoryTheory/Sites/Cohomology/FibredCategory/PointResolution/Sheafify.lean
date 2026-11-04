module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriek

/-!
# The sheafified degree-zero functor of a fibrewise point resolution is lower shriek

Let `p : C ⥤ D` be a fibred category and `A_{•,V}` a family of point resolutions of its fibres,
as in `Stacks.Sites.FibredCategory.FibredCategorySituation.pointZeroAdjunction`. The
sheafification of `V ↦ H_0(G(A_{•,V}))` is `π_!` of the sheafification of `G`: both functors are
left adjoint to `π⁻¹` followed by the inclusion of sheaves into presheaves.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.pointZeroSheafifyIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
    ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
      SimplicialObject.homotopyEquivalences (Type vC) f)

/-- **The sheafification of `V ↦ H_0(G(A_{•,V}))` is `π_!` of the sheafification of `G`.** Both
are left adjoint to `π⁻¹` followed by the forgetful functor to presheaves. -/
def pointZeroSheafifyIso :
    pointZero s A ⋙ presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC vC} ≅
      presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC vC} ⋙ s.abelianLowerShriek :=
  ((pointZeroAdjunction s hA hres).comp
      (sheafificationAdjunction s.base.J AddCommGrpCat.{max w uD vD uC vC})).leftAdjointUniq
    (((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC vC}).comp
      s.abelianLowerShriekAdjunction).ofNatIsoRight
        (s.p.sheafPushforwardContinuousCompSheafToPresheafIso
          AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J))

end Stacks.Sites.FibredCategory.FibredCategorySituation
