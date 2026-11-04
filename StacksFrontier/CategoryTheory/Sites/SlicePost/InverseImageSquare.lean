module

public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Restriction to a slice commutes with inverse image

Let `u : C ⥤ D` be a continuous left exact functor of sites `(C, J)`, `(D, K)` between categories
with finite limits, let `V : C` and put `U = u.obj V`. Localizing gives the continuous functor
`u' = Over.post u : Over V ⥤ Over U`, and the square of inverse images

```
  j_U⁻¹ ∘ u⁻¹  ≅  (u')⁻¹ ∘ j_V⁻¹
```

commutes, for sheaves valued in an arbitrary category `A`.

Both composites are left adjoints: the left-hand one of
`(Over.star U)_* ∘ u_*` and the right-hand one of `(u')_* ∘ (Over.star V)_*`, the direct images
being paired with the restrictions `j_V⁻¹ = (Over.forget V)_*` and `j_U⁻¹ = (Over.forget U)_*`
through the adjunctions `Over.forget ⊣ Over.star`. Those two right adjoints are identified by
`CategoryTheory.sheafPushforwardContinuousStarOverPostIso`, which is the pushforward form of the
same square, so uniqueness of left adjoints identifies the composites.

## Main results

* `CategoryTheory.overPullbackCompSheafPullbackOverPostIso` — the comparison isomorphism
  `j_V⁻¹ ⋙ (u')⁻¹ ≅ u⁻¹ ⋙ j_U⁻¹`.

## Implementation notes

For sheaves of sets on small sites this is Stacks 03CF (b), which the library already proves as
`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso` by way of 03CF (c) and the
description of a slice topos as a slice category of sheaves. That route gives the statement only
at coefficient category `Type u` on a small site, because the identification of `Sh(C/V)` with
`Sh(C)/h_V^#` is available only there; the proof below uses no such description and so applies to
any coefficient category and any universes, which is what a sheaf of abelian groups on the small
étale site of a scheme needs. The two are kept apart: the `Type u` version is the site carrying
the 03CF tag and records the slice-topos proof.

## References

* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits u]
  [u.IsContinuous J K] (A : Type u₃) [Category.{v₃} A] (V : C)
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous A (J.over V)
    (K.over (u.obj V))).IsRightAdjoint]

/-- **Restriction to a slice commutes with inverse image.** For a continuous left exact functor
`u : C ⥤ D` of sites between categories with finite limits and `V : C`, restricting a sheaf on
`(C, J)` to the localized site `C/V` and then taking the inverse image along
`Over.post u : Over V ⥤ Over (u.obj V)` is the same as taking the inverse image along `u` and then
restricting to `D/(u.obj V)`.

Both sides are left adjoint to the two composites of direct images identified by
`CategoryTheory.sheafPushforwardContinuousStarOverPostIso`. -/
public def overPullbackCompSheafPullbackOverPostIso :
    J.overPullback A V ⋙
        (Over.post (X := V) u).sheafPullback A (J.over V) (K.over (u.obj V)) ≅
      u.sheafPullback A J K ⋙ K.overPullback A (u.obj V) :=
  haveI := Functor.isContinuous_overPost_of_flat J K u V
  (((Over.forgetAdjStar V).sheafPushforwardAdjunction (J := J.over V) (K := J) A).comp
      ((Over.post (X := V) u).sheafAdjunctionContinuous A (J.over V)
        (K.over (u.obj V)))).leftAdjointUniq
    (((u.sheafAdjunctionContinuous A J K).comp
      ((Over.forgetAdjStar (u.obj V)).sheafPushforwardAdjunction
        (J := K.over (u.obj V)) (K := K) A)).ofNatIsoRight
      (sheafPushforwardContinuousStarOverPostIso J K u V A).symm)

end CategoryTheory

end
