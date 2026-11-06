module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.MateCompatibility
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare

/-!
# The exchange of Stacks 0FN1 is the mate of the square of restrictions

Let `w : v' ⋙ u ⟶ u' ⋙ v` be a `2`-square of functors of sites, with `u`, `u'` continuous and
cocontinuous and `v`, `v'` continuous. Restriction of sheaves along the four functors gives a
square `v^p ⋙ u'^p ⟶ u^p ⋙ v'^p`, and its mate under the two adjunctions
`u^p ⊣ u_*`, `u'^p ⊣ u'_*` of a continuous and cocontinuous functor is a comparison
`u_* ⋙ v^p ⟶ v'^p ⋙ u'_*` of direct images. This file identifies that mate with the base-change
transformation of Stacks 0FN1, so that it is invertible when `w` is Guitart exact.

## Main definitions

* `restrictionTwoSquareRestrictionSquareMate`: the square of restrictions of `w`.

## Main results

* `mateEquiv_restrictionTwoSquare_restrictionSquareMate`: the mate of the square of restrictions
  is the inverse of `sheafIsoOfTwoSquareAndMorphismsTwoSquare`.
* `isIso_mateEquiv_restrictionTwoSquare_restrictionSquareMate`: it is invertible.

## References

* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.CocontinuousExchange

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (A : Type u₅) [Category.{v₅} A]
  (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (K' : GrothendieckTopology D')
  (K : GrothendieckTopology D) {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}
  [u.IsContinuous J K] [u'.IsContinuous J' K'] [v.IsContinuous K' K] [v'.IsContinuous J' J]
  (w : TwoSquare v' u' u v)

/-- The square of restrictions of sheaves `v^p ⋙ u'^p ⟶ u^p ⋙ v'^p` of a `2`-square
`w : v' ⋙ u ⟶ u' ⋙ v` of continuous functors of sites. -/
def restrictionTwoSquareRestrictionSquareMate :
    TwoSquare (v.sheafPushforwardContinuous A K' K) (u.sheafPushforwardContinuous A J K)
      (u'.sheafPushforwardContinuous A J' K') (v'.sheafPushforwardContinuous A J' J) :=
  have := Functor.isContinuous_comp u' v J' K' K
  have := Functor.isContinuous_comp v' u J' J K
  TwoSquare.mk _ _ _ _ (Functor.sheafPushforwardContinuousNatTrans w.natTrans A J' K)

/-- The square of restrictions, read on a section: restriction along the component of `w`. -/
theorem restrictionTwoSquare_app_hom_app_restrictionSquareMate (F : Sheaf K A) (V : C'ᵒᵖ) :
    ((restrictionTwoSquareRestrictionSquareMate A J' J K' K w).natTrans.app F).hom.app V =
      F.obj.map (w.natTrans.app V.unop).op :=
  rfl

variable [u.IsCocontinuous J K] [u'.IsCocontinuous J' K']
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
  [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F]

/-- **The mate of the square of restrictions is the exchange of Stacks 0FN1.** Under the
adjunctions `u^p ⊣ u_*` and `u'^p ⊣ u'_*`, the square of restrictions of a Guitart exact
`2`-square `w` has as mate the inverse of
`Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare`: both are the
transpose under `u'^p ⊣ u'_*` of the counit of `u^p ⊣ u_*` restricted along `w`. -/
theorem mateEquiv_restrictionTwoSquare_restrictionSquareMate [w.GuitartExact] :
    (mateEquiv (u.sheafAdjunctionCocontinuous A J K) (u'.sheafAdjunctionCocontinuous A J' K')
      (restrictionTwoSquareRestrictionSquareMate A J' J K' K w)).natTrans =
      (sheafIsoOfTwoSquareAndMorphismsTwoSquare A J' J K' K w).inv := by
  ext F : 2
  refine ObjectProperty.hom_ext _ ?_
  rw [sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare]
  show ((mateEquiv (u.sheafAdjunctionCocontinuous A J K) (u'.sheafAdjunctionCocontinuous A J' K')
      (restrictionTwoSquareRestrictionSquareMate A J' J K' K w)).app F).hom = _
  rw [Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv,
    Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom, TwoSquare.ranBaseChange_app]
  congr 1
  ext V
  simp only [Functor.id_obj, Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, restrictionTwoSquare_app_hom_app_restrictionSquareMate,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit,
    Functor.RightExtension.mk_hom, Functor.RightExtension.mk_left,
    Functor.op_obj, Functor.associator_inv_app, Functor.whiskerRight_app, NatTrans.op_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

/-- The mate of the square of restrictions of a Guitart exact `2`-square is invertible. -/
instance isIso_mateEquiv_restrictionTwoSquare_restrictionSquareMate [w.GuitartExact] :
    IsIso (mateEquiv (u.sheafAdjunctionCocontinuous A J K) (u'.sheafAdjunctionCocontinuous A J' K')
      (restrictionTwoSquareRestrictionSquareMate A J' J K' K w)).natTrans := by
  rw [mateEquiv_restrictionTwoSquare_restrictionSquareMate]
  infer_instance

end Stacks.Sites.CocontinuousExchange

end
