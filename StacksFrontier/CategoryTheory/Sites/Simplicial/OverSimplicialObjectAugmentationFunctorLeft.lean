module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite

/-!
# The augmentation functor of a simplicial object of a site on underlying morphisms

Let `U` be a simplicial object of a site `(C, J)` with an augmentation `a : U → X`. The functor
`(C/U)_total ⥤ C/X`, `V/U_n ↦ V/X`, of `CategoryTheory.SimplicialOver.augmentationFunctor` does
not change the morphism of `C` underlying the fibre of a morphism of the total site.

## Main results

* `augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft`: the image of a
  morphism `f` under `augmentationFunctor U a` has underlying morphism that of the fibre of `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

namespace SimplicialOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {U : SimplicialObject C}
  {X : C} (a : U ⟶ (SimplicialObject.const C).obj X)

omit [HasPullbacks C] in
/-- The functor `V/U_n ↦ V/X` does not change the underlying morphism of a fibre. -/
theorem augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft
    {A A' : Grothendieck (slices U)} (f : A ⟶ A') :
    ((augmentationFunctor U a).map f).left = (Grothendieck.Hom.fiber f).left := by
  change ((eqToHom (augmentationFibre_eq U a f.base)).app A.fiber ≫
    (augmentationFibre U a A'.base).map f.fiber).left = _
  exact (congrArg (· ≫ (Grothendieck.Hom.fiber f).left) ((congrArg Over.Hom.left
    (eqToHom_app (augmentationFibre_eq U a f.base) A.fiber)).trans
      ((Comma.eqToHom_left (H := _)).trans (eqToHom_refl _ _)))).trans (Category.id_comp _)

end SimplicialOver

end CategoryTheory

end
