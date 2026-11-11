module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-! # The square of topoi of a localized special cocontinuous functor

Let `u : C ⥤ D` be a special cocontinuous functor between sites (Stacks 03CG) and `U` an
object of `C`.  Write `j_U : C/U ⥤ C` for `Over.forget U`, `j_{u(U)}` for
`Over.forget (u.obj U)` and `u' : C/U ⥤ D/u(U)` for `Over.post u`.  Each of these four functors
is cocontinuous, so it has the morphism of topoi of Stacks 00XO, with inverse image `gInv` and
direct image `gStar`.

## Main results

* `overPost_comp_forget`: the square of sites `j_{u(U)} ∘ u' = u ∘ j_U` commutes.
* `isSpecialCocontinuous_overPost`: `u'` is again special cocontinuous.
* `gInvOverSquareIso`, `gStarOverSquareIso`: the square of topoi commutes, on inverse images
  and on direct images.
* `isSpecialCocontinuous_overPost_and_isEquivalence` (**Stacks 03CH**): all of the above, and
  the two vertical morphisms of topoi, attached to `u` and to `u'`, are equivalences.

## References

* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
-/

@[expose] public section

open CategoryTheory

universe t

namespace CategoryTheory.Sites.LocalizedToposSquare

variable {C : Type t} [SmallCategory C] {D : Type t} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (U : C)

/-- A special cocontinuous functor (Stacks 03CG) is the same thing as a dense subsite
inclusion: cocontinuity is implied by the dense-subsite condition. -/
theorem isSpecialCocontinuous_iff_isDenseSubsite :
    IsSpecialCocontinuous J K u ↔ u.IsDenseSubsite J K := by
  unfold IsSpecialCocontinuous
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩

/-- The square of sites of Stacks 03CH (as in Stacks 03EG) commutes on the nose:
`j_{u(U)} ∘ u' = u ∘ j_U`. -/
theorem overPost_comp_forget :
    Over.post (X := U) u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u := rfl

variable [u.IsDenseSubsite J K]

/-- **Stacks 03CH**, the left vertical arrow: the localization `u' = Over.post u` of a
special cocontinuous functor `u` at `U` is again special cocontinuous. -/
theorem isSpecialCocontinuous_overPost :
    IsSpecialCocontinuous (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) :=
  (isSpecialCocontinuous_iff_isDenseSubsite _ _ _).2
    (Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) u U)

/-- The square of topoi of Stacks 03CH commutes, on inverse images: for a sheaf `G` on `D`,
restricting along `u` and then to `C/U` agrees with restricting to `D/u(U)` and then along
`u'`.  Every functor in the square is continuous and cocontinuous, so its inverse image is
plain restriction (Stacks 00XR), and the two composite restrictions are restriction along
`u ∘ j_U = j_{u(U)} ∘ u'`. -/
noncomputable def gInvOverSquareIso :
    gInv C D J K u ⋙ gInv (Over U) C (J.over U) J (Over.forget U) ≅
      gInv (Over (u.obj U)) D (K.over (u.obj U)) K (Over.forget (u.obj U)) ⋙
        gInv (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) :=
  haveI := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) u U
  (Functor.isoWhiskerRight
      (u.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type t) J K) _ ≪≫
    Functor.isoWhiskerLeft _
      ((Over.forget U).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type t) (J.over U) J)) ≪≫
  (Functor.isoWhiskerRight
      ((Over.forget (u.obj U)).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type t) (K.over (u.obj U)) K) _ ≪≫
    Functor.isoWhiskerLeft _
      ((Over.post (X := U) u).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type t) (J.over U) (K.over (u.obj U)))).symm

/-- The square of topoi of Stacks 03CH commutes, on direct images:
`u_* ∘ j_{U,*} ≅ j_{u(U),*} ∘ u'_*`.  Both sides are right adjoint to the two composite inverse
images, which agree by `gInvOverSquareIso`. -/
noncomputable def gStarOverSquareIso :
    gStar (Over U) C (J.over U) J (Over.forget U) ⋙ gStar C D J K u ≅
      gStar (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) ⋙
        gStar (Over (u.obj U)) D (K.over (u.obj U)) K (Over.forget (u.obj U)) :=
  Adjunction.rightAdjointUniq
    (((gAdjunction C D J K u).comp
      (gAdjunction (Over U) C (J.over U) J (Over.forget U))).ofNatIsoLeft
        (gInvOverSquareIso J K u U))
    ((gAdjunction (Over (u.obj U)) D (K.over (u.obj U)) K (Over.forget (u.obj U))).comp
      (gAdjunction (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U))
        (Over.post (X := U) u)))

/-- **Stacks 03CH.** Let `u : C ⥤ D` be a special cocontinuous functor between sites, which
is the instance `[u.IsDenseSubsite J K]` (equivalently `IsSpecialCocontinuous J K u`, by
`isSpecialCocontinuous_iff_isDenseSubsite`), and let `U` be an object of `C`.  Then

1. the square of sites `j_{u(U)} ∘ u' = u ∘ j_U` commutes, where `j_U = Over.forget U`,
   `j_{u(U)} = Over.forget (u.obj U)` and `u' = Over.post u : C/U ⥤ D/u(U)`;
2. the left vertical arrow `u'` is a special cocontinuous functor;
3. the square of topoi `Sh(C/U) → Sh(C) → Sh(D)`, `Sh(C/U) → Sh(D/u(U)) → Sh(D)` commutes,
   formed with the morphisms of topoi of Stacks 00XO attached to the four cocontinuous
   functors: the composite inverse images are isomorphic and so are the composite direct
   images;
4. the vertical morphisms of topoi, attached to `u` and to `u'`, are equivalences: both their
   inverse images and their direct images are equivalences of categories.

Sites are small categories and topoi are categories of sheaves of sets in the same universe,
as in the source. -/
@[stacks 03CH]
theorem isSpecialCocontinuous_overPost_and_isEquivalence :
    Over.post (X := U) u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u ∧
      IsSpecialCocontinuous (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) ∧
      Nonempty (gInv C D J K u ⋙ gInv (Over U) C (J.over U) J (Over.forget U) ≅
        gInv (Over (u.obj U)) D (K.over (u.obj U)) K (Over.forget (u.obj U)) ⋙
          gInv (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U))
            (Over.post (X := U) u)) ∧
      Nonempty (gStar (Over U) C (J.over U) J (Over.forget U) ⋙ gStar C D J K u ≅
        gStar (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U))
            (Over.post (X := U) u) ⋙
          gStar (Over (u.obj U)) D (K.over (u.obj U)) K (Over.forget (u.obj U))) ∧
      (gInv C D J K u).IsEquivalence ∧ (gStar C D J K u).IsEquivalence ∧
      (gInv (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U))
        (Over.post (X := U) u)).IsEquivalence ∧
      (gStar (Over U) (Over (u.obj U)) (J.over U) (K.over (u.obj U))
        (Over.post (X := U) u)).IsEquivalence :=
  haveI := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) u U
  ⟨overPost_comp_forget u U, isSpecialCocontinuous_overPost J K u U,
    ⟨gInvOverSquareIso J K u U⟩, ⟨gStarOverSquareIso J K u U⟩,
    gInv_isEquivalence_of_isDenseSubsite C D J K u,
    gStar_isEquivalence_of_isDenseSubsite C D J K u,
    gInv_isEquivalence_of_isDenseSubsite _ _ _ _ _,
    gStar_isEquivalence_of_isDenseSubsite _ _ _ _ _⟩

end CategoryTheory.Sites.LocalizedToposSquare
