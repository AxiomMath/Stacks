module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.MorphismTransport

/-!
# The composition law of the projection-formula map at a whiskered comparison

`Stacks.AffineProjectionFormula.adjunctionTensorMap_comp` factors the canonical map of a
composite of adjunctions through the comparison `Stacks.AffineProjectionFormula.comparisonComp`.
The geometric comparisons of a composite are built as whiskered composites instead; this file
records that the two agree and restates the composition law in the whiskered shape.

## Main results

* `Stacks.AffineProjectionFormula.comparisonComp_eq_whiskered`: `comparisonComp` is the whiskered
  composite of the two comparisons.
* `Stacks.AffineProjectionFormula.adjunctionTensorMap_comp_whiskered`: the factorisation of the
  canonical map of a composite of adjunctions, with the comparison of the composite written as a
  whiskering.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

variable {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D] [Category E]

variable {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
  {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
  {A : C × C ⥤ C} {B : D × D ⥤ D} {K : E × E ⥤ E}
  (α : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (β : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ K)

/-- **`comparisonComp` is the whiskered composite of the two comparisons.**  Both have component
`L₂(α_P) ≫ β_{(L₁P₁, L₁P₂)}` at a pair `P`, so this is `rfl`.

It is stated because the two spellings are *not* interchangeable in practice.  A consumer whose
comparison is given in whiskered form must not let the unifier compare the two underneath an
`adjunctionTensorMap` whose bifunctor arguments are the derived tensor products of a ringed
space: the check is a deterministic heartbeat overrun there, while at these binders it is
immediate.  `adjunctionTensorMap_comp_whiskered` below is the composition law already in the
whiskered shape, so that no such check ever arises. -/
lemma comparisonComp_eq_whiskered :
    comparisonComp α β = Functor.whiskerRight α L₂ ≫ Functor.whiskerLeft (L₁.prod L₁) β :=
  rfl

/-- **The canonical map of a composite of adjunctions factors, at the whiskered comparison.**
`adjunctionTensorMap_comp` with the comparison of the composite written as
`Functor.whiskerRight α L₂ ≫ Functor.whiskerLeft (L₁.prod L₁) β`, which is the shape in which the
geometric comparisons of a composite are built. -/
lemma adjunctionTensorMap_comp_whiskered (G : E) (H : C) :
    adjunctionTensorMap (adj₁.comp adj₂) A K
        (Functor.whiskerRight α L₂ ≫ Functor.whiskerLeft (L₁.prod L₁) β) G H =
      adjunctionTensorMap adj₁ A B α (R₂.obj G) H ≫
        R₁.map (adjunctionTensorMap adj₂ B K β G (L₁.obj H)) := by
  rw [← comparisonComp_eq_whiskered]
  exact adjunctionTensorMap_comp adj₁ adj₂ α β G H

end Stacks.AffineProjectionFormula

end
