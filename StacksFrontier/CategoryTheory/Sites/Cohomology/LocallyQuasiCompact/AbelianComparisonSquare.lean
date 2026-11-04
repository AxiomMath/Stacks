module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PushforwardInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality

/-!
# The Zariski comparison square on abelian sheaves, and the open objects of the big site

Let `f : X ⟶ Y` be a morphism of the locally quasi-compact Zariski site, with underlying
continuous map `g`. The comparison morphisms `π_X : Sh(LC_Zar/X) → Sh(X_Zar)` commute with the
morphism of slice topoi induced by `f`; for sheaves of abelian groups, on inverse images, this is
an isomorphism

`g^{-1} ⋙ π_X^{-1} ≅ π_Y^{-1} ⋙ (−)|_{Over.map f}`.

Read at a morphism `h : T.left ⟶ X`, that is, at an object `T` of `LC_Zar/X`, the square is the
compatibility `(π_X^{-1} J)|_{T.left} ≅ π_{T.left}^{-1}(h^{-1} J)` of the comparison morphism with
localization.

For `J` an injective abelian sheaf on `X_Zar` and `p > 0`, the `p`-th cohomology presheaf of
`π_X^{-1} J` on the big site over `X`, read at the fibre products along `f`, and the `p`-th
cohomology presheaf of `π_Y^{-1}(g_* J)` both vanish at the objects of `LC_Zar/Y` that come from
open subsets of `Y`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianZariskiComparisonSquareIso`: the
  comparison square on abelian sheaves.
* `restrictedCohomologyPresheafIsoOpensToSlice`, in the same namespace: the isomorphism of these
  two cohomology presheaves, restricted to the open subsets of `Y`.

## Main results

* `isZero_restrictedCohomologyPresheaf_inverseImage_opensToSlice`, in the same namespace: for `J`
  injective and `p > 0` the `p`-th cohomology presheaf of `π_X^{-1} J` on the big site over `X`
  vanishes at the fibre product of an open subset of `Y` along `f`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

section Square

variable [HasSheafify (Opens.grothendieckTopology
    ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X))
    AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology
    ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
    AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]

/-- **The comparison square on abelian sheaves.** The comparison morphisms to the Zariski topoi
of the underlying spaces commute with the morphism of slice topoi induced by `f`, on sheaves of
abelian groups: `g^{-1} ⋙ π_X^{-1} ≅ π_Y^{-1} ⋙ (−)|_{Over.map f}`.

At `f := h : T.left ⟶ X` this is the compatibility `(π_X^{-1} J)|_{T.left} ≅
π_{T.left}^{-1}(h^{-1} J)` of the comparison morphism with localization of the big site. -/
def abelianZariskiComparisonSquareIso :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
        AddCommGrpCat.{max (u + 1) v}
        (Opens.grothendieckTopology
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
        (Opens.grothendieckTopology
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)) ⋙
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ≅
    S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ⋙
      (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over X) (S.zariskiTopology.over Y) := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let g := I.map f
  let A := AddCommGrpCat.{max (u + 1) v}
  let JX := Opens.grothendieckTopology (I.obj X)
  let JY := Opens.grothendieckTopology (I.obj Y)
  let KX := S.zariskiTopology.over X
  let KY := S.zariskiTopology.over Y
  let uX := (S.opensToSlice X).1
  let uY := (S.opensToSlice Y).1
  let vOpen := Opens.map g
  let pOver := Over.pullback f
  let _ : uX.IsContinuous JX KX := S.opensToSlice_isContinuous X
  let _ : uY.IsContinuous JY KY := S.opensToSlice_isContinuous Y
  let _ : vOpen.IsContinuous JY JX := inferInstance
  let _ : pOver.IsContinuous KY KX := inferInstance
  let _ : (vOpen ⋙ uX).IsContinuous JY KX := Functor.isContinuous_comp vOpen uX JY JX KX
  let _ : (uY ⋙ pOver).IsContinuous JY KX := Functor.isContinuous_comp uY pOver JY KY KX
  let adjOpen := vOpen.sheafAdjunctionContinuous A JY JX
  let adjX := uX.sheafAdjunctionContinuous A JX KX
  let adjY := uY.sheafAdjunctionContinuous A JY KY
  let adjP := pOver.sheafAdjunctionContinuous A KY KX
  let eRight := zariskiComparisonDirectImageSquareIso S f A
  let eSquarePullback :=
    (adjOpen.comp adjX).leftAdjointUniq ((adjY.comp adjP).ofNatIsoRight eRight.symm)
  let eX : S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ≅ uX.sheafPullback A JX KX :=
    Adjunction.leftAdjointUniq (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X) adjX
  let eY : S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ≅ uY.sheafPullback A JY KY :=
    Adjunction.leftAdjointUniq (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y) adjY
  let eP : pOver.sheafPullback A KY KX ≅
      (Over.map f).sheafPushforwardContinuous A KX KY :=
    (Over.mapPullbackAdj f).sheafPullbackIso A
  exact Functor.isoWhiskerLeft (vOpen.sheafPullback A JY JX) eX ≪≫
    eSquarePullback ≪≫
      Functor.isoWhiskerRight eY.symm (pOver.sheafPullback A KY KX) ≪≫
        Functor.isoWhiskerLeft (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y) eP

end Square

section OpenObjects

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})]

omit [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})] in
/-- **The higher cohomology of `π_X^{-1} J` vanishes at the fibre product of an open subset of
`Y` along `f`, for `J` injective.** For `p > 0` and `V` open in `Y`, the `p`-th cohomology
presheaf of `π_X^{-1} J` on the big site over `X` vanishes at `V ×_Y X`. -/
theorem isZero_restrictedCohomologyPresheaf_inverseImage_opensToSlice
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    [Injective J] (p : ℕ) (hp : 0 < p) (V : Opens Y.obj) :
    IsZero ((((sheafToPresheaf (S.zariskiTopology.over X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)).obj
        (op ((Over.pullback f).obj ((S.opensToSlice Y).1.obj V)))) :=
  (isZero_zariskiRightDerivedPresheaf_inverseImage_opensToSlice.{u, w, v} S X J p hp
      ((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj
        V)).of_iso
    ((((sheafToPresheaf (S.zariskiTopology.over X)
      AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)).mapIso
      ((zariskiOpenPullbackIso S f).app V).op)

/-- **The two cohomology presheaves agree at the open objects of the big site over `Y`.** For `J`
injective and `p > 0`, the cohomology presheaf `W ↦ H^p(W ×_Y X, π_X^{-1} J)` and the cohomology
presheaf `W ↦ H^p(W, π_Y^{-1}(g_* J))` are isomorphic after restriction along
`ι_Y : Opens Y ⥤ LC_Zar/Y`, both being zero there. -/
def restrictedCohomologyPresheafIsoOpensToSlice
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    [Injective J] (p : ℕ) (hp : 0 < p) :
    (S.opensToSlice Y).1.op ⋙ (Over.pullback f).op ⋙
        ((sheafToPresheaf (S.zariskiTopology.over X)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J) ≅
      (S.opensToSlice Y).1.op ⋙
        ((sheafToPresheaf (S.zariskiTopology.over Y)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).obj
            ((topologicalPushforward.{u, w, v} S f).obj J)) :=
  NatIso.ofComponents
    (fun V ↦ (isZero_restrictedCohomologyPresheaf_inverseImage_opensToSlice.{u, w, v}
        S f J p hp V.unop).iso
      (isZero_zariskiRightDerivedPresheaf_pushforward_opensToSlice.{u, w, v} S f J p hp V.unop))
    (fun {V _} _ ↦ (isZero_restrictedCohomologyPresheaf_inverseImage_opensToSlice.{u, w, v}
      S f J p hp V.unop).eq_of_src _ _)

end OpenObjects

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
