module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductComparison

/-!
# The projections of the comparison out of a colimit of stagewise 2-fibre products

The stagewise 2-fibre product `CategoryTheory.Cat.twoFibreProductDiagram` of a cospan of diagrams
of categories carries two projections to the diagrams it is built from, and the comparison
`CategoryTheory.Cat.colimitTwoFibreProductComparison` out of its colimit intertwines them with the
projections of the 2-fibre product of the colimits. This file builds the two projections as
morphisms of diagrams and proves those two identities.

They are what identifies the comparison out of the colimit as the comparison functor of a
2-commutative square whose legs are colimits of morphisms of diagrams: the square whose
2-cartesianness is "filtered colimits of categories commute with 2-fibre products". Nothing here
needs filteredness, nor that the comparison be an equivalence.

## Main definitions

* `CategoryTheory.Cat.twoFibreProductDiagramFst`: the first projection of the stagewise 2-fibre
  product, as a morphism of diagrams.
* `CategoryTheory.Cat.twoFibreProductDiagramSnd`: the second projection of the stagewise 2-fibre
  product, as a morphism of diagrams.

## Main results

* `CategoryTheory.Cat.colimitTwoFibreProductComparison_comp_π₁`: the comparison out of the colimit
  followed by the first projection is the colimit of the first projections.
* `CategoryTheory.Cat.colimitTwoFibreProductComparison_comp_π₂`: the comparison out of the colimit
  followed by the second projection is the colimit of the second projections.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe t v w

variable {J : Type v} [Category.{w} J] {X Y Z : J ⥤ Cat.{t, t}} (α : X ⟶ Y) (γ : Z ⟶ Y)

/-- **The first projection of the stagewise 2-fibre product, as a morphism of diagrams.** Its
component at a stage is the first projection of the 2-fibre product there. -/
def twoFibreProductDiagramFst : twoFibreProductDiagram α γ ⟶ X where
  app j := (CategoricalPullback.π₁ (α.app j).toFunctor (γ.app j).toFunctor).toCatHom
  naturality _ _ _ := Cat.Hom.ext rfl

/-- **The second projection of the stagewise 2-fibre product, as a morphism of diagrams.** Its
component at a stage is the second projection of the 2-fibre product there. -/
def twoFibreProductDiagramSnd : twoFibreProductDiagram α γ ⟶ Z where
  app j := (CategoricalPullback.π₂ (α.app j).toFunctor (γ.app j).toFunctor).toCatHom
  naturality _ _ _ := Cat.Hom.ext rfl

/-- The component of `twoFibreProductDiagramFst α γ` at `j` is the first projection of the
2-fibre product of `α.app j` and `γ.app j`. -/
@[simp]
lemma twoFibreProductDiagramFst_app (j : J) :
    ((twoFibreProductDiagramFst α γ).app j).toFunctor =
      CategoricalPullback.π₁ (α.app j).toFunctor (γ.app j).toFunctor := rfl

/-- The component of `twoFibreProductDiagramSnd α γ` at `j` is the second projection of the
2-fibre product of `α.app j` and `γ.app j`. -/
@[simp]
lemma twoFibreProductDiagramSnd_app (j : J) :
    ((twoFibreProductDiagramSnd α γ).app j).toFunctor =
      CategoricalPullback.π₂ (α.app j).toFunctor (γ.app j).toFunctor := rfl

variable [HasColimit X] [HasColimit Y] [HasColimit Z]
  [HasColimit (twoFibreProductDiagram α γ)]

/-- The stagewise comparison followed by the first projection is the first projection followed by
a colimit inclusion. -/
lemma twoFibreProductStage_comp_π₁ (j : J) :
    twoFibreProductStage α γ j ⋙
        CategoricalPullback.π₁ (colimMap α).toFunctor (colimMap γ).toFunctor =
      CategoricalPullback.π₁ (α.app j).toFunctor (γ.app j).toFunctor ⋙
        (colimit.ι X j).toFunctor := rfl

/-- The stagewise comparison followed by the second projection is the second projection followed
by a colimit inclusion. -/
lemma twoFibreProductStage_comp_π₂ (j : J) :
    twoFibreProductStage α γ j ⋙
        CategoricalPullback.π₂ (colimMap α).toFunctor (colimMap γ).toFunctor =
      CategoricalPullback.π₂ (α.app j).toFunctor (γ.app j).toFunctor ⋙
        (colimit.ι Z j).toFunctor := rfl

/-- A functor between colimits of diagrams of categories is the colimit of a morphism of diagrams
as soon as it agrees with it after precomposing with each colimit inclusion. -/
private theorem functor_eq_colimMap_of_ι_comp {D W : J ⥤ Cat.{t, t}} [HasColimit D] [HasColimit W]
    (F : (colimit D : Cat.{t, t}) ⥤ (colimit W : Cat.{t, t})) (φ : D ⟶ W)
    (h : ∀ j : J, (colimit.ι D j).toFunctor ⋙ F = (colimit.ι D j).toFunctor ⋙
      (colimMap φ).toFunctor) :
    F = (colimMap φ).toFunctor :=
  congrArg Cat.Hom.toFunctor
    (colimit.hom_ext fun j => Cat.Hom.ext (by
      rw [Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor]; exact h j) :
      F.toCatHom = colimMap φ)

/-- **The comparison out of the colimit followed by the first projection is the colimit of the
first projection.** -/
lemma colimitTwoFibreProductComparison_comp_π₁ :
    colimitTwoFibreProductComparison α γ ⋙
        CategoricalPullback.π₁ (colimMap α).toFunctor (colimMap γ).toFunctor =
      (colimMap (twoFibreProductDiagramFst α γ)).toFunctor :=
  functor_eq_colimMap_of_ι_comp _ _ fun j => by
    rw [← Functor.assoc, colimitTwoFibreProductComparison_ι,
      ι_colimMap_toFunctor (twoFibreProductDiagramFst α γ) j]
    exact twoFibreProductStage_comp_π₁ α γ j

/-- **The comparison out of the colimit followed by the second projection is the colimit of the
second projection.** -/
lemma colimitTwoFibreProductComparison_comp_π₂ :
    colimitTwoFibreProductComparison α γ ⋙
        CategoricalPullback.π₂ (colimMap α).toFunctor (colimMap γ).toFunctor =
      (colimMap (twoFibreProductDiagramSnd α γ)).toFunctor :=
  functor_eq_colimMap_of_ι_comp _ _ fun j => by
    rw [← Functor.assoc, colimitTwoFibreProductComparison_ι,
      ι_colimMap_toFunctor (twoFibreProductDiagramSnd α γ) j]
    exact twoFibreProductStage_comp_π₂ α γ j

end CategoryTheory.Cat

end
