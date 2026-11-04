module

public import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# A morphism into a single object, read through the postcomposed shift isomorphism

Let `F : SingleFunctors C D A` be a family of single-object functors compatible with the shift,
and let `G : D ⥤ E` commute with the shift. `CategoryTheory.SingleFunctors.postcomp` builds the
family `a ↦ F.functor a ⋙ G`, whose shift isomorphism is assembled from the commutation
isomorphism of `G` and the shift isomorphism of `F`.

This file records the one consequence that makes the postcomposed shift isomorphism *computable*:
when a morphism `τ : K ⟶ (F.functor a').obj M` of `D` is pushed into `E` by `G`, shifted, and
read by the postcomposed shift isomorphism, the commutation isomorphism of `G` cancels against
its own inverse and what is left is `G` applied to the shifted composite formed inside `D`.

This is what turns a comparison map built in a localized category — where the commutation
isomorphism of the localization functor has no formula — into the image of a single morphism of
complexes.

## Main results

* `CategoryTheory.SingleFunctors.postcomp_shiftIso_hom_app_comp`
-/

@[expose] public noncomputable section

namespace CategoryTheory.SingleFunctors

open Category

variable {C D E : Type*} [Category C] [Category D] [Category E] {A : Type*} [AddMonoid A]
  [HasShift D A] [HasShift E A]

/-- **The postcomposed shift isomorphism absorbs the commutation isomorphism of `G`.** The
shifted image under `G` of a morphism into a single object, read by the shift isomorphism of the
postcomposed single functors, is `G` applied to the corresponding composite formed in `D`. -/
theorem postcomp_shiftIso_hom_app_comp (F : SingleFunctors C D A) (G : D ⥤ E) [G.CommShift A]
    (n a a' : A) (ha' : n + a = a') (M : C) {K : D} (τ : K ⟶ (F.functor a').obj M) :
    (G.commShiftIso n).hom.app K ≫
        (shiftFunctor E n).map (G.map τ) ≫
          ((F.postcomp G).shiftIso n a a' ha').hom.app M =
      G.map ((shiftFunctor D n).map τ ≫ (F.shiftIso n a a' ha').hom.app M) := by
  rw [Functor.map_comp, postcomp_shiftIso_hom_app, ← assoc, ← assoc,
    ← G.commShiftIso_hom_naturality, assoc, assoc, Iso.hom_inv_id_app_assoc]

end CategoryTheory.SingleFunctors

end
