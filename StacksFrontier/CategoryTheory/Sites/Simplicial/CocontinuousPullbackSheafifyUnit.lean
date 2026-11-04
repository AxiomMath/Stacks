module

public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormulaLegCocontinuous

/-!
# Stacks 00XR (1) on sections

For a functor of sites `u` that is both continuous and cocontinuous,
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` removes the
sheafification from `g^{-1} = (u^p\ )^#`, the restricted presheaf being already a sheaf.  This
file records what that comparison is on sections: it is inverse to the sheafification unit of the
restricted presheaf, so composing the unit with it gives the identity.

Since a morphism out of a sheafification is determined by its composite with the unit, this
characterizes the comparison on sections.

## Main results

* `CategoryTheory.Functor`
  `.toSheafify_comp_sheafPullbackCocontinuousIsoSheafPushforwardContinuous_hom_app`

## Implementation notes

The comparison is `CategoryTheory.Adjunction.leftAdjointUniq` of the adjunction of Stacks 00XL
with Mathlib's `sheafAdjunctionCocontinuous`, so by
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` it is the inverse transpose, along
the first adjunction, of the unit of the second.  Composing the sheafification unit with an
inverse transpose along the adjunction of Stacks 00XL is an inverse transpose along the right Kan
extension (`sheafAdjunctionPullbackCocontinuous_homEquiv_symm_hom`), and the unit of
`sheafAdjunctionCocontinuous` is on sections the unit of that Kan extension
(Mathlib's `sheafAdjunctionCocontinuous_unit_app_hom`), whose inverse transpose is the identity.

## References

* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
  (A : Type w) [Category.{w'} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsCocontinuous J K] [u.IsContinuous J K] [HasWeakSheafify J A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]

/-- **Stacks 00XR (1) on sections.**  The comparison removing the sheafification from the sheaf
pullback along a continuous and cocontinuous functor of sites is, on underlying presheaves,
inverse to the sheafification unit of the restricted presheaf. -/
theorem toSheafify_comp_sheafPullbackCocontinuousIsoSheafPushforwardContinuous_hom_app
    (X : Sheaf K A) :
    toSheafify J (u.op ⋙ X.obj) ≫
        ((u.sheafPullbackCocontinuousIsoSheafPushforwardContinuous A J K).hom.app X).hom =
      𝟙 (u.op ⋙ X.obj) := by
  have hiso : (u.sheafPullbackCocontinuousIsoSheafPushforwardContinuous A J K).hom.app X =
      ((u.sheafAdjunctionPullbackCocontinuous A J K).homEquiv X
          ((u.sheafPushforwardContinuous A J K).obj X)).symm
        ((u.sheafAdjunctionCocontinuous A J K).unit.app X) :=
    (Equiv.eq_symm_apply _).mpr
      (Adjunction.homEquiv_leftAdjointUniq_hom_app
        (u.sheafAdjunctionPullbackCocontinuous A J K)
        (u.sheafAdjunctionCocontinuous A J K) X)
  rw [hiso, toSheafify_comp_sheafAdjunctionPullbackCocontinuous_homEquiv_symm_hom,
    sheafAdjunctionCocontinuous_unit_app_hom]
  exact (u.op.ranAdjunction A).homEquiv_symm_unit X.obj

end CategoryTheory.Functor

end
