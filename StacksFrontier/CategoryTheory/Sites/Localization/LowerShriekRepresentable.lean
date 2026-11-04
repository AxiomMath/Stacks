module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable

/-!
# Lower shriek of a representable sheaf on a localized site

Let `(C, J)` be a site, let `U` be an object of `C` and let `X/U` be an object of the localized
site `C/U`. Stacks 03HU asserts `j_{U!}(h_{X/U}^#) = h_X^#`: the lower-shriek extension of the
sheaf associated to the presheaf represented by `X/U` on `C/U` is the sheaf associated to the
presheaf represented by `X` on `C`.

As in `StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable`, the localization
functor `j_U` is Mathlib's
`CategoryTheory.Over.forget U`, which is continuous for `J.over U` and `J`, and `j_{U!}` is its
`Functor.sheafPullback`, the chosen left adjoint of `j_U^{-1} = J.overPullback`. The source states
the conclusion as an equality of sheaves, identifying objects defined up to canonical isomorphism;
the faithful rendering is a canonical isomorphism in `Sh(C)`, and it is natural in `X/U`.

The source derives the formula from the explicit description of `j_{U!}` in Stacks 03CD. Here it is
instead the special case `u := j_U` of Stacks 04D3 (`u_s h_W^# = h_{u(W)}^#` for a continuous `u`),
which is already proved in this repository as `sheafPullback_sheafify_yoneda_iso`, together with
the definitional identity `j_U(X/U) = X`.

## Main results

* `overShriekSheafifyYonedaIso`: the isomorphism `j_{U!}(h_{X/U}^#) ≅ h_X^#` (Stacks 03HU).
* `overShriek_sheafify_yoneda_natIso`: the same isomorphism, natural in `X/U`.

Tags covered: 03HU.
-/

@[expose] public section

open CategoryTheory
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
variable [HasWeakSheafify (J.over U) (Type v)] [HasWeakSheafify J (Type v)]
variable [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- **Stacks 03HU.** For an object `X/U` of the localized site `C/U`, the lower shriek
`j_{U!} = (Over.forget U).sheafPullback` of the sheaf `h_{X/U}^#` associated to the presheaf on
`C/U` represented by `X/U` is the sheaf `h_X^#` associated to the presheaf on `C` represented by
the underlying object `X = j_U(X/U)`. -/
@[stacks 03HU]
noncomputable def overShriekSheafifyYonedaIso (X : Over U) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).obj
        ((presheafToSheaf (J.over U) (Type v)).obj (yoneda.obj X)) ≅
      (presheafToSheaf J (Type v)).obj (yoneda.obj X.left) :=
  sheafPullbackSheafifyYonedaIso (Over.forget U) (J.over U) J X

/-- The isomorphism `j_{U!}(h_{X/U}^#) ≅ h_X^#` of Stacks 03HU is natural in `X/U`: an
isomorphism of functors `C/U ⥤ Sh(C)`. -/
theorem overShriek_sheafify_yoneda_natIso :
    Nonempty
      ((yoneda ⋙
          presheafToSheaf (J.over U) (Type v) ⋙
          (Over.forget U).sheafPullback (Type v) (J.over U) J) ≅
        (Over.forget U ⋙ yoneda ⋙ presheafToSheaf J (Type v))) :=
  sheafPullback_sheafify_yoneda_natIso (Over.forget U) (J.over U) J

end CategoryTheory
