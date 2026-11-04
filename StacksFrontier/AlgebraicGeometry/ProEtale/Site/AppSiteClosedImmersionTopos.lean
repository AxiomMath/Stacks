module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteContinuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful

/-!
# The morphism of topoi of a closed immersion of affine schemes

Let `i : Z ⟶ X` be a closed immersion of affine schemes. On the sites of ind-étale affines the
base change functor `u : X_app ⥤ Z_app`, `U ↦ U ×_X Z`, has a fully faithful left adjoint
`v : Z_app ⥤ X_app`, and `v` is cocontinuous; both facts are Stacks 09BK and both are already
available, as `AlgebraicGeometry.ProEtale.appProetaleBaseChange_hasLeftAdjoint`,
`AlgebraicGeometry.ProEtale.appProetaleLift_fullyFaithful` and
`AlgebraicGeometry.ProEtale.appProetaleLift_isCocontinuous`.

A cocontinuous functor carries a morphism of topoi all by itself: its direct image is the right
Kan extension `{}_s v`, and its inverse image is the sheafification of restriction along `v`.
This file instantiates that morphism of topoi for `v` and proves those of the consequences of
Stacks 09BL which follow from full faithfulness and cocontinuity of `v` alone — clauses (1),
(5) for the direct image, and (6) for the direct image.

## Main definitions

* `AlgebraicGeometry.ProEtale.appProetalePushforward` — the direct image `i_*`.
* `AlgebraicGeometry.ProEtale.appProetaleInverseImage` — the inverse image `i^{-1}`.
* `AlgebraicGeometry.ProEtale.appProetaleLiftAdjunction` — a chosen adjunction `v ⊣ u`.

## Main results

* `AlgebraicGeometry.ProEtale.appProetaleInverseImage_eq` and
  `AlgebraicGeometry.ProEtale.appProetaleInverseImageAdjunction` — Stacks 09BL (1): the
  inverse image is the sheaf associated to the presheaf `V ↦ F(v(V))`.
* `AlgebraicGeometry.ProEtale.appProetalePushforwardIsoRestriction` — the direct image is
  restriction along the base change functor `u`, so `(i_*F)(U) = F(u(U))`.
* `AlgebraicGeometry.ProEtale.appProetalePushforwardFullyFaithful` — Stacks 09BL (6) for the
  direct image: `i_*` is fully faithful.
* `AlgebraicGeometry.ProEtale.appProetale_isIso_counit` — Stacks 09BL (5) for the direct
  image: `i^{-1}i_* → id` is an isomorphism.

## Implementation notes

The morphism of topoi here is the one *induced by* `v`; that it agrees with `i_proetale` is the
first assertion of Stacks 09BL and is **not** proved, because it rests on Stacks 098X, whose
reduction in `StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSite` needs cover density of the
inclusion of `S_app` (`AppSmallProetale.HasAppCover`, Stacks 097Z). Nothing below asserts that
agreement; each tagged statement names `v` in its clause string.

The direct image is identified with restriction along `u` so that full faithfulness can be read
off on underlying presheaves: there the left adjoint of restriction along `u` is restriction
along `v`, and the unit `𝟭 ⟶ v ⋙ u` is invertible because `v` is fully faithful. That argument
is `CategoryTheory.Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint`, and continuity of
`u` — which it needs — is cocontinuity of `v` read through the adjunction. Full faithfulness of
the direct image then makes the counit of `i^{-1} ⊣ i_*` invertible, which is clause (5) for
`i^{-1}i_*`.

Coefficients are sheaves of sets in `Type (u + 1)`: the objects of `Z_app` lie in `Type (u + 1)`
and its morphisms in `Type u`, so `Type (u + 1)` is the universe in which sheafification and the
pointwise Kan extensions of the general theory are available without further hypotheses.

The clauses not proved here are (2), (3), (4), and the parts of (5) and (6) that speak about
`i^{Sh}_!` and `i_!`. Stacks derives them from Lemma 0990 (every object of `Z_app` is covered by
weakly contractible ones) together with Lemma 09YX and Homology Lemma 0793; neither 0990 nor
09YX is available, and the shortest route through the general theory would instead need `v`
itself to be continuous, which the sheafification in clause (1) says it is not.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] [IsAffine Z]

/-- Cocontinuity of the left adjoint `v` of Stacks 09BK, as an instance. -/
instance isCocontinuous_appProetaleLift :
    (appProetaleLift i).IsCocontinuous (AppSmallProetale.topology Z)
      (AppSmallProetale.topology X) :=
  appProetaleLift_isCocontinuous i

/-- Fullness of the left adjoint `v` of Stacks 09BK, as an instance. -/
instance full_appProetaleLift : (appProetaleLift i).Full := by
  obtain ⟨hv⟩ := appProetaleLift_fullyFaithful i
  exact hv.full

/-- Faithfulness of the left adjoint `v` of Stacks 09BK, as an instance. -/
instance faithful_appProetaleLift : (appProetaleLift i).Faithful := by
  obtain ⟨hv⟩ := appProetaleLift_fullyFaithful i
  exact hv.faithful

/-- A chosen adjunction `v ⊣ u` between the left adjoint of Stacks 09BK and base change. -/
public noncomputable def appProetaleLiftAdjunction :
    appProetaleLift i ⊣ appProetaleBaseChange i :=
  Classical.choice (appProetaleBaseChange_hasLeftAdjoint i)

/-- Continuity of the base change functor `u`: it is the right adjoint of the cocontinuous
functor `v`. -/
instance isContinuous_appProetaleBaseChange :
    (appProetaleBaseChange i).IsContinuous (AppSmallProetale.topology X)
      (AppSmallProetale.topology Z) :=
  (appProetaleLiftAdjunction i).isContinuous_of_isCocontinuous _ _

/-- The direct image `i_*` of the morphism of topoi induced by the cocontinuous functor `v` of
Stacks 09BK: the right Kan extension `{}_s v` of Stacks 00XO. -/
public noncomputable abbrev appProetalePushforward :
    Sheaf (AppSmallProetale.topology Z) (Type (u + 1)) ⥤
      Sheaf (AppSmallProetale.topology X) (Type (u + 1)) :=
  (appProetaleLift i).sheafPushforwardCocontinuous (Type (u + 1))
    (AppSmallProetale.topology Z) (AppSmallProetale.topology X)

/-- The inverse image `i^{-1}` of the morphism of topoi induced by the cocontinuous functor `v`
of Stacks 09BK: restriction along `v` followed by sheafification. -/
public noncomputable abbrev appProetaleInverseImage :
    Sheaf (AppSmallProetale.topology X) (Type (u + 1)) ⥤
      Sheaf (AppSmallProetale.topology Z) (Type (u + 1)) :=
  (appProetaleLift i).sheafPullbackCocontinuous (Type (u + 1))
    (AppSmallProetale.topology Z) (AppSmallProetale.topology X)

/-- **Stacks 09BL (1), the formula.** The inverse image of the morphism of topoi induced by `v`
is the sheafification of the presheaf `V ↦ F(v(V))` on `Z_app`: it is restriction along `v.op`
sandwiched between the inclusion of sheaves into presheaves and sheafification. -/
@[stacks 09BL "(1), the inverse image is the sheafification of the presheaf V -> F(v(V)), for \
the morphism of topoi induced by the fully faithful cocontinuous functor v of Tag 09BK"]
public theorem appProetaleInverseImage_eq :
    appProetaleInverseImage i =
      sheafToPresheaf (AppSmallProetale.topology X) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft (AppSmallProetale Z)ᵒᵖ (AppSmallProetale X)ᵒᵖ
            (Type (u + 1))).obj (appProetaleLift i).op ⋙
          presheafToSheaf (AppSmallProetale.topology Z) (Type (u + 1)) :=
  rfl

/-- **Stacks 09BL (1), that this is the inverse image.** The sheafification of `V ↦ F(v(V))` is
left adjoint to the direct image, so it is the inverse image of the morphism of topoi induced
by `v`. -/
@[stacks 09BL "(1), the sheafification of V -> F(v(V)) is the inverse image, being left adjoint \
to the direct image of the morphism of topoi induced by the cocontinuous functor v of Tag 09BK"]
public noncomputable def appProetaleInverseImageAdjunction :
    appProetaleInverseImage i ⊣ appProetalePushforward i :=
  (appProetaleLift i).sheafAdjunctionPullbackCocontinuous (Type (u + 1))
    (AppSmallProetale.topology Z) (AppSmallProetale.topology X)

/-- **The direct image is restriction along base change.** For a sheaf `F` on `Z_app` and an
object `U` of `X_app` we have `(i_*F)(U) = F(u(U))`, where `u` is base change along `i`: the
right Kan extension along `v.op` is restriction along the right adjoint `u.op`, both being
right adjoint to restriction along `v.op`. This is Stacks 00XX (1) in this situation. -/
public noncomputable def appProetalePushforwardIsoRestriction :
    appProetalePushforward i ≅
      (appProetaleBaseChange i).sheafPushforwardContinuous (Type (u + 1))
        (AppSmallProetale.topology X) (AppSmallProetale.topology Z) :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf (AppSmallProetale.topology X) (Type (u + 1)))
    (Functor.sheafPushforwardCocontinuousIsoRestriction (A := Type (u + 1))
        (J := AppSmallProetale.topology Z) (K := AppSmallProetale.topology X)
        (adj := appProetaleLiftAdjunction i) ≪≫
      ((appProetaleBaseChange i).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) (AppSmallProetale.topology X) (AppSmallProetale.topology Z)).symm)

/-- **Stacks 09BL (6) for the direct image.** The direct image `i_*` of the morphism of topoi
induced by `v` is fully faithful.

On underlying presheaves `i_*` is restriction along the base change functor `u`, whose left
adjoint is restriction along `v`; the composite of the two is restriction along `v ⋙ u`, which
is the identity because `v` is fully faithful. -/
@[stacks 09BL "(6), full faithfulness of the direct image i_*, for the morphism of topoi \
induced by the fully faithful cocontinuous functor v of Tag 09BK"]
public noncomputable def appProetalePushforwardFullyFaithful :
    (appProetalePushforward i).FullyFaithful := by
  have hff := Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint (Type (u + 1))
    (appProetaleBaseChange i) (appProetaleLiftAdjunction i)
    (AppSmallProetale.topology X) (AppSmallProetale.topology Z)
  have := hff.full
  have := hff.faithful
  have : (appProetalePushforward i).Full :=
    Functor.Full.of_iso (appProetalePushforwardIsoRestriction i).symm
  have : (appProetalePushforward i).Faithful :=
    Functor.Faithful.of_iso (appProetalePushforwardIsoRestriction i).symm
  exact .ofFullyFaithful _

/-- **Stacks 09BL (5) for the direct image.** The counit `i^{-1}i_* ⟶ id` of the morphism of
topoi induced by `v` is an isomorphism, because its right adjoint `i_*` is fully faithful. -/
@[stacks 09BL "(5), the map i^{-1} i_* -> id is an isomorphism, for the morphism of topoi \
induced by the fully faithful cocontinuous functor v of Tag 09BK"]
public theorem appProetale_isIso_counit :
    IsIso (appProetaleInverseImageAdjunction i).counit := by
  have hff := appProetalePushforwardFullyFaithful i
  have := hff.full
  have := hff.faithful
  exact (appProetaleInverseImageAdjunction i).counit_isIso_of_R_fully_faithful

end AlgebraicGeometry.ProEtale

end
