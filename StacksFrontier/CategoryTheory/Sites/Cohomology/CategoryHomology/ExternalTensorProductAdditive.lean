module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExternalTensorProduct

/-!
# The inverse images along the projections of a product of chaotic sites are additive

`Stacks.CategoryHomology.projFstInverseImage` and `Stacks.CategoryHomology.projSndInverseImage`
are restriction of diagrams of `B`-modules along the two projections of `C₁ × C₂`.  Being computed
pointwise they are additive; this is recorded as instances so that the functors they induce on
derived categories are available.

## Main results

* `Stacks.CategoryHomology.projFstInverseImage_additive` and
  `Stacks.CategoryHomology.projSndInverseImage_additive`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryHomology

universe u₁ u₂ w

variable (C₁ : Type u₁) (C₂ : Type u₂) [SmallCategory C₁] [SmallCategory C₂]
  (B : Type w) [CommRing B]

/-- Restriction along the first projection is additive, being computed pointwise. -/
instance projFstInverseImage_additive : (projFstInverseImage C₁ C₂ B).Additive :=
  inferInstanceAs
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C₁ C₂).op).Additive

/-- Restriction along the second projection is additive, being computed pointwise. -/
instance projSndInverseImage_additive : (projSndInverseImage C₁ C₂ B).Additive :=
  inferInstanceAs
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C₁ C₂).op).Additive

end Stacks.CategoryHomology

end
