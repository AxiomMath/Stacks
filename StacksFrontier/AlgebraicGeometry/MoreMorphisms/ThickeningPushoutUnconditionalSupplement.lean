module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Supplement to `ThickeningPushoutUnconditional`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isThickening_of_isPushout_of_isThickening`
* `isAffineHom_of_isPushout_of_isThickening`
* `isPullback_of_isPushout_of_isThickening`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y : Scheme.{u}}

/-! ### An arbitrary scheme carrying the pushout square -/

variable {Q : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {A : X' ⟶ Q} {B : Y ⟶ Q}

/-- **Stacks 07RT, second assertion, for an arbitrary scheme carrying the pushout square.**  If
`i` is a thickening, `f` is affine and the square `i, f, A, B` is cocartesian, then `B` is a
thickening. -/
theorem isThickening_of_isPushout_of_isThickening (hpo : IsPushout i f A B)
    (hi : IsThickening i) [IsAffineHom f] : IsThickening B := by
  have : HasPushout i f := hpo.hasPushout
  have h1 : IsThickening (pushout.inr i f) := pushout_inr_isThickening' i f hi
  have hB : B = pushout.inr i f ≫ hpo.isoPushout.inv := by
    rw [← hpo.inr_isoPushout_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have := h1.1
  have : Surjective (pushout.inr i f) := ⟨h1.2⟩
  rw [hB]
  exact ⟨inferInstance, (pushout.inr i f ≫ hpo.isoPushout.inv).surjective⟩

/-- **Affineness of `X' ⟶ Y'`, for an arbitrary scheme carrying the pushout square.**  This is
not one of the assertions of [Stacks Project, Tag 07RT]: it follows from them, since `Y ⟶ Y'` is
a thickening and therefore affine, so that `X ⟶ X' ⟶ Y'` is affine. -/
theorem isAffineHom_of_isPushout_of_isThickening (hpo : IsPushout i f A B)
    (hi : IsThickening i) [IsAffineHom f] : IsAffineHom A := by
  have hB : IsThickening B := isThickening_of_isPushout_of_isThickening hpo hi
  have := hB.1
  have : IsAffineHom (i ≫ A) := by rw [hpo.w]; infer_instance
  exact isAffineHom_of_isThickening_comp forall_isAffine_of_isThickening i A hi

/-- **Stacks 07RT, third assertion, for an arbitrary scheme carrying the pushout square.**  A
cocartesian square of a thickening and an affine morphism is also cartesian. -/
theorem isPullback_of_isPushout_of_isThickening (hpo : IsPushout i f A B)
    (hi : IsThickening i) [IsAffineHom f] : IsPullback i f A B := by
  have : HasPushout i f := hpo.hasPushout
  exact (isPullback_pushout_of_isThickening_of_isAffineHom' i f hi).of_iso'
    (Iso.refl X) (Iso.refl X') (Iso.refl Y) hpo.isoPushout (by simp) (by simp)
    (by simp [hpo.inl_isoPushout_hom]) (by simp [hpo.inr_isoPushout_hom])

end Stacks.Pushout

end
