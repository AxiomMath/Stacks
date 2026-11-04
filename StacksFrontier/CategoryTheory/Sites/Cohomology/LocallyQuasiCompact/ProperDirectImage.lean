module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Direct image and the Zariski comparison morphism

Let `f : X ⟶ Y` be a morphism of the Zariski site `LC_Zar` of Hausdorff, locally quasi-compact
spaces, let `g : X → Y` be the underlying continuous map, and let
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)`, `π_Y : Sh(LC_Zar/Y) → Sh(Y_Zar)` be the comparison morphisms of
topoi of `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonAdjunction`. Writing
`f_Zar : Sh(LC_Zar/X) → Sh(LC_Zar/Y)` for the morphism of slice topoi induced by `f`, this file
constructs the canonical base-change map

`π_Y^{-1} ∘ g_* ⟶ f_{Zar,*} ∘ π_X^{-1}`

on sheaves of sets and characterizes its invertibility.

The map is the adjoint mate of the commutative square on direct images
`zariskiComparisonDirectImageSquareIso`: insert the unit of `π_X^{-1} ⊣ π_{X,*}`, transport across
the square, and contract with the counit of `π_Y^{-1} ⊣ π_{Y,*}`. The unit is invertible, because
the open-subset functor is continuous, cocontinuous, full and faithful, so `π_X^{-1}` is fully
faithful; this is `comparisonAdjunction_unit_isIso`, the sheaves-of-sets form of the invertible
unit. Consequently the base-change map is invertible exactly where the counit of the `Y`-side
adjunction is, which is the content of `isIso_properDirectImageComparison_iff`: the comparison is
an isomorphism if and only if `f_{Zar,*} π_X^{-1} F` lies in the part of `Sh(LC_Zar/Y)` on which
the counit is invertible, i.e. in the essential image of `π_Y^{-1}`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.slicePushforwardIso`: the direct image of
  the morphism of slice topoi induced by `f` is restriction along `Over.pullback f`, so it sends a
  sheaf `G` on `LC_Zar/X` to `Z/Y ↦ G(Z ×_Y X / X)`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDirectImageComparison`: the canonical
  base-change map on sheaves of sets. No hypothesis on `f` is needed to construct it.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianProperDirectImageComparison`: the
  same map on abelian sheaves, which is the underived input for the comparison of derived direct
  images on bounded below derived categories.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_properDirectImageComparison_iff`: the
  base-change map is an isomorphism if and only if the counit of the `Y`-side comparison
  adjunction is an isomorphism at every `f_{Zar,*} π_X^{-1} F`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDirectImageComparisonIso`: the
  resulting isomorphism of functors, under that condition.
* `isIso_abelianProperDirectImageComparison_iff`: the same criterion on abelian sheaves, in the
  same namespace.

## Implementation notes

The comparison is built from `zariskiComparisonDirectImageSquareIso` rather than from
`zariskiComparisonSquareIso`: the latter is the mate of the former on *inverse* images, which is an
isomorphism for every `f`, while the mate taken here is the one whose invertibility is a genuine
condition on `f`.

For a proper `f` the condition of `isIso_properDirectImageComparison_iff` holds, by proper base
change for sheaves of sets (Stacks 0D90): that is `isIso_properBaseChangeCounit` of
`ProperBaseChangeSurjective.lean`. The declarations here therefore carry no properness
hypothesis and no tag; clause (7a) of Stacks 0DCU is
`properDirectImageComparisonIsoOfProperMap` in that file, which feeds the condition to
`properDirectImageComparisonIso` below and carries the tag.

On abelian sheaves the unit is invertible by `abelianComparisonAdjunction_unit_isIso`, so only the
third factor of the mate is in question there too, and the abelian base-change map is stated with
restriction along `Over.pullback f` as its target, which is the shape in which the derived
comparison consumes it.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

/-- The direct image of the morphism of slice topoi induced by `f` is restriction along
`Over.pullback f`: both are right adjoint to restriction along `Over.map f`, and `Over.map f` is
left adjoint to `Over.pullback f`. Concretely, it sends a sheaf `G` on `LC_Zar/X` to
`Z/Y ↦ G(Z ×_Y X / X)`. -/
def slicePushforwardIso :
    (zariskiSliceMorphism.{u, w, v} S f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (max u v))
        (S.zariskiTopology.over Y) (S.zariskiTopology.over X) :=
  letI := hasPointwiseRightKanExtension_overMap.{u, w, v} S f
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (max u v))

/-- The composite of the two isomorphisms through which the base-change map factors: the
invertible unit of the `X`-side comparison adjunction, followed by the commutative square on
direct images. -/
def properDirectImageComparisonLeft :
    TopCat.Sheaf.pushforward (Type (max u v))
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
        S.comparisonInverseImage.{u, w, v} Y ≅
      S.comparisonInverseImage.{u, w, v} X ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (max u v))
            (S.zariskiTopology.over Y) (S.zariskiTopology.over X) ⋙
          S.comparisonDirectImage Y (Type (max u v)) ⋙
            S.comparisonInverseImage.{u, w, v} Y :=
  haveI := comparisonAdjunction_unit_isIso.{u, w, v} S X
  Functor.isoWhiskerRight (asIso (S.comparisonAdjunction.{u, w, v} X).unit)
      (TopCat.Sheaf.pushforward (Type (max u v))
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
        S.comparisonInverseImage.{u, w, v} Y) ≪≫
    Functor.isoWhiskerLeft (S.comparisonInverseImage.{u, w, v} X)
      (Functor.isoWhiskerRight (zariskiComparisonDirectImageSquareIso S f
        (Type (max u v))) (S.comparisonInverseImage.{u, w, v} Y))

/-- The canonical base-change map `π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}` on sheaves of sets, the
adjoint mate of `zariskiComparisonDirectImageSquareIso`. It is defined for every `f`. -/
def properDirectImageComparison :
    TopCat.Sheaf.pushforward (Type (max u v))
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
      S.comparisonInverseImage.{u, w, v} Y ⟶
    S.comparisonInverseImage.{u, w, v} X ⋙ (zariskiSliceMorphism.{u, w, v} S f).pushforward :=
  (properDirectImageComparisonLeft.{u, w, v} S f).hom ≫
    Functor.whiskerLeft (S.comparisonInverseImage.{u, w, v} X ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (max u v))
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X))
      (S.comparisonAdjunction.{u, w, v} Y).counit ≫
    (Functor.isoWhiskerLeft (S.comparisonInverseImage.{u, w, v} X)
      (slicePushforwardIso.{u, w, v} S f).symm).hom

/-- Conjugating a morphism by isomorphisms does not change whether it is an isomorphism. -/
private lemma isIso_conj_iff {C : Type*} [Category* C] {A A' B B' : C}
    (e : A ≅ A') (e' : B' ≅ B) (β : A' ⟶ B') :
    IsIso (e.hom ≫ β ≫ e'.hom) ↔ IsIso β := by
  simp

/-- The base-change map is an isomorphism exactly when the counit of the `Y`-side comparison
adjunction is an isomorphism at each `f_{Zar,*} π_X^{-1} F`, i.e. exactly when each such sheaf
lies in the essential image of `π_Y^{-1}`.

The two remaining factors of `properDirectImageComparison` are isomorphisms: the first because the
unit of the `X`-side adjunction is invertible and the square on direct images is an isomorphism,
the last because the slice direct image is restriction along `Over.pullback f`. -/
theorem isIso_properDirectImageComparison_iff :
    IsIso (properDirectImageComparison.{u, w, v} S f) ↔
      ∀ F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u v)),
        IsIso ((S.comparisonAdjunction.{u, w, v} Y).counit.app
          (((Over.pullback f).sheafPushforwardContinuous (Type (max u v))
              (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).obj
            ((S.comparisonInverseImage.{u, w, v} X).obj F))) :=
  (isIso_conj_iff (properDirectImageComparisonLeft.{u, w, v} S f)
      (Functor.isoWhiskerLeft (S.comparisonInverseImage.{u, w, v} X)
        (slicePushforwardIso.{u, w, v} S f).symm) _).trans
    (NatTrans.isIso_iff_isIso_app _)

/-- Under the condition of `isIso_properDirectImageComparison_iff`, the base-change map is an
isomorphism of functors: ordinary direct image followed by the Zariski comparison agrees with the
comparison followed by slice direct image.

This is not clause (7a) of Stacks 0DCU, because `hc` assumes what properness is there to give.
Clause (7a) is `properDirectImageComparisonIsoOfProperMap` of
`ProperBaseChangeSurjective.lean`, which specializes this and carries the tag. -/
def properDirectImageComparisonIso
    (hc : ∀ F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u v)),
      IsIso ((S.comparisonAdjunction.{u, w, v} Y).counit.app
        (((Over.pullback f).sheafPushforwardContinuous (Type (max u v))
            (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).obj
          ((S.comparisonInverseImage.{u, w, v} X).obj F)))) :
    TopCat.Sheaf.pushforward (Type (max u v))
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
      S.comparisonInverseImage.{u, w, v} Y ≅
    S.comparisonInverseImage.{u, w, v} X ⋙ (zariskiSliceMorphism.{u, w, v} S f).pushforward :=
  haveI : IsIso (properDirectImageComparison.{u, w, v} S f) :=
    (isIso_properDirectImageComparison_iff.{u, w, v} S f).2 hc
  asIso (properDirectImageComparison.{u, w, v} S f)


section Abelian

/-- The abelian companion of `properDirectImageComparisonLeft`. -/
def abelianProperDirectImageComparisonLeft :
    TopCat.Sheaf.pushforward AddCommGrpCat.{max (u + 1) v}
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ≅
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
            (S.zariskiTopology.over Y) (S.zariskiTopology.over X) ⋙
          S.comparisonDirectImage Y AddCommGrpCat.{max (u + 1) v} ⋙
            S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y :=
  haveI := abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  Functor.isoWhiskerRight
      (asIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit)
      (TopCat.Sheaf.pushforward AddCommGrpCat.{max (u + 1) v}
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y) ≪≫
    Functor.isoWhiskerLeft (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X)
      (Functor.isoWhiskerRight (zariskiComparisonDirectImageSquareIso S f
        AddCommGrpCat.{max (u + 1) v}) (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y))

/-- The canonical base-change map `π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}` on abelian sheaves. It is
defined for every `f`, and it is the underived input for the derived comparison on `D⁺`. -/
def abelianProperDirectImageComparison :
    TopCat.Sheaf.pushforward AddCommGrpCat.{max (u + 1) v}
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ⟶
    S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
      (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over Y) (S.zariskiTopology.over X) :=
  (abelianProperDirectImageComparisonLeft.{u, w, v} S f).hom ≫
    Functor.whiskerLeft (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X))
      (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y).counit

/-- The abelian base-change map is an isomorphism exactly when the counit of the `Y`-side
comparison adjunction is an isomorphism at each `f_{Zar,*} π_X^{-1} F`. -/
theorem isIso_abelianProperDirectImageComparison_iff :
    IsIso (abelianProperDirectImageComparison.{u, w, v} S f) ↔
      ∀ F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
        IsIso ((S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y).counit.app
          (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
              (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).obj
            ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F))) :=
  (isIso_comp_left_iff (abelianProperDirectImageComparisonLeft.{u, w, v} S f).hom _).trans
    (NatTrans.isIso_iff_isIso_app _)

end Abelian

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
