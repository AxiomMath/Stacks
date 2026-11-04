module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Sheaves on an essentially small site form a Grothendieck abelian category

Mathlib's `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall` asks for
sheafification on the *small model* of the site. On an essentially small site that is implied
by sheafification on the site itself, because the equivalence with the small model is a dense
subsite inclusion. This module records the resulting criterion.

## Main results

* `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify`.

## Implementation notes

The small-model sheafification is obtained from
`CategoryTheory.Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` for the functor
`(equivSmallModel C).functor`, which is an equivalence and therefore a dense subsite
inclusion for the induced topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory.Sheaf

/-- Sheaves with values in a Grothendieck abelian category on an essentially small site which
admits sheafification form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify
    {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{v} C] (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A]
    [∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A] :
    IsGrothendieckAbelian.{v} (Sheaf J A) := by
  set K := (equivSmallModel C).inverse.inducedTopology J
  have : ((equivSmallModel C).functor.sheafPushforwardContinuous A J K).IsEquivalence := by
    show (((equivSmallModel C).sheafCongr J K A).inverse).IsEquivalence
    infer_instance
  have : HasSheafify K A :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K (equivSmallModel C).functor
  exact isGrothendieckAbelian_of_essentiallySmall J A

end CategoryTheory.Sheaf

end
