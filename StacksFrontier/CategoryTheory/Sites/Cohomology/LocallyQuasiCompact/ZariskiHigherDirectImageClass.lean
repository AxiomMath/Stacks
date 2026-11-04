module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.AcyclicityReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDerivedImageIso
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedProperBaseChange
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images along a proper arrow stay pulled back from the space

Stacks 0EZI chooses, for the comparison of the quasi-compact topology on locally quasi-compact
Hausdorff spaces with the Zariski topology on the same category, the proper arrows as the
distinguished class `P` and the sheaves `π_X^{-1}G` pulled back from the space as the class
`A'_X`. The fourth of the five conditions of Situation 0EZ3 asks that `A'` be stable under *all*
higher direct images along an arrow of `P`:

`R^i f_{Zar,*}` of an object of `A'_X` lies in `A'_Y`, for every proper `f : X ⟶ Y` and `i : ℕ`.

This file proves that condition, with the explicit witness `R^i g_* G` for the underlying
continuous map `g` of `f`.

## Main results

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `isProperMap_of_properMorphisms`: an arrow of the distinguished class is proper in the sense of
  Stacks 005O (5).
* `isZero_rightDerived_sliceDirectImage_abelianComparisonInverseImage`:
  `R^p f_{Zar,*}(π_X^{-1}J) = 0` for `p > 0`, `J` injective and `f` proper — that is,
  `π_X^{-1}` carries injective abelian sheaves on the space to `f_{Zar,*}`-acyclic sheaves.
* `rightDerivedZariskiBaseChangeIso`: **clause (7b) of Stacks 0DCU in degree `i`**, in the
  `ℕ`-indexing: `R^i f_{Zar,*}(π_X^{-1}G) ≅ π_Y^{-1}(R^i g_* G)` for a proper `f`.
* `zariskiPullbackClass_rightDerived_overMapPushforward`: **condition (4) of Situation 0EZ3 for
  this situation.**

## Implementation notes

The coefficient category is `AddCommGrpCat.{max (u + 1) v}`: the objects of the site lie one
universe above the spaces. The sheafification and enough-injectives hypotheses are instance
arguments; they are needed to write `Functor.rightDerived` at all.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

/-- **An arrow of the distinguished class of Stacks 0EZI is proper in the sense of Stacks
005O (5).** `properMorphisms` is Mathlib's `IsProperMap` of the underlying continuous map, and
the source's notion is separatedness together with universal closedness in the fibre-product
sense. This is the converse of `isProperMap_site`. -/
theorem isProperMap_of_properMorphisms (hf : S.properMorphisms f) :
    StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) :=
  have _ht2 : T2Space ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X) := by
    show T2Space X.obj
    infer_instance
  ⟨T2Space.isSeparatedMap _, hf.isUniversallyClosedMap⟩

section Acyclicity

variable [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **`π_X^{-1}` carries injectives to `f_{Zar,*}`-acyclic sheaves, for `f` proper.** That is,
`R^p f_{Zar,*}(π_X^{-1}J) = 0` for every `p > 0` and every injective abelian sheaf `J` on the
small Zariski site of `X`. -/
theorem isZero_rightDerived_sliceDirectImage_abelianComparisonInverseImage
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    (hJ : Injective J) (p : ℕ) (hp : 0 < p) :
    IsZero (((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)) :=
  isZero_rightDerived_pushforward_of_isZero_sheafify AddCommGrpCat.{max (u + 1) v}
    (Over.pullback f) p _
    (IsZero.of_iso
      (isZero_presheafToSheaf_of_locallyZero (S.zariskiTopology.over Y) _
        (equalizerSieve_mem_over_of_isProperMap.{u, w, v} S f hf J hJ p hp))
      ((presheafToSheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}).mapIso
        ((pushforwardCohomologyPresheafRestrictionIso AddCommGrpCat.{max (u + 1) v}
          (Over.pullback f) p).app _)))

end Acyclicity

section BaseChange

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **Clause (7b) of Stacks 0DCU in degree `i`, in Mathlib's `ℕ`-indexing.** For a proper arrow
`f : X ⟶ Y` of the site, with underlying continuous map `g`,

`R^i f_{Zar,*}(π_X^{-1}G) ≅ π_Y^{-1}(R^i g_* G)`.

It is the composite of the collapse `Stacks.RightDerivedComp.objIsoOfAcyclicImage`, the underived
base-change isomorphism `isIso_zariskiBaseChange_of_properMap` transported through `R^i` by
`CategoryTheory.Functor.rightDerivedIsoOfNatIso`, and `CategoryTheory.Functor.rightDerivedCompIso`
for the exact functor `π_Y^{-1}`. -/
def rightDerivedZariskiBaseChangeIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (G : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) (i : ℕ) :
    ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G) ≅
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).obj
        (((topologicalPushforward.{u, w, v} S f).rightDerived i).obj G) :=
  have _hcolim : PreservesFiniteColimits
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X) :=
    ((exactFunctor_iff _).1 (S.abelianComparisonInverseImage_exact.{u, w, max (u + 1) v} X)).2
  have _hlim : PreservesFiniteLimits (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}) :=
    preservesFiniteLimits_zariskiSlicePushforward.{u, w, v} S f
  have _hbc : IsIso (zariskiBaseChange.{u, w, v} S f) :=
    isIso_zariskiBaseChange_of_properMap.{u, w, v} S f hf
  (Stacks.RightDerivedComp.objIsoOfAcyclicImage
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X)
      (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v})
      (fun n hn => Functor.isZero_rightDerived_of_exact _ G n hn)
      (fun Z hZ n hn =>
        isZero_rightDerived_sliceDirectImage_abelianComparisonInverseImage.{u, w, v} S f hf Z hZ
          n hn)
      i).symm ≪≫
    ((Functor.rightDerivedIsoOfNatIso (asIso (zariskiBaseChange.{u, w, v} S f)) i).app G).symm ≪≫
    (Functor.rightDerivedCompIso (topologicalPushforward.{u, w, v} S f)
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y) i).app G

end BaseChange

section Condition

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- The direct image of the morphism of localized Zariski topoi attached to cocontinuity of
`Over.map f` is additive. -/
instance overMapSheafPushforwardCocontinuous_additive :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) v}
      (S.zariskiTopology.over X) (S.zariskiTopology.over Y)).Additive :=
  have _ := ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{max (u + 1) v}
    (S.zariskiTopology.over X) (S.zariskiTopology.over Y)).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- Every higher direct image along a proper arrow `f : X ⟶ Y` of a sheaf pulled back from the
space `X` is again pulled back from the space `Y`: if `F` lies in `zariskiPullbackClass X` then
`R^i f_{Zar,*}F` lies in `zariskiPullbackClass Y`, for every `i : ℕ`. -/
@[stacks 0EZI "condition (4) of Situation 0EZ3 for this situation: all higher direct images \
along a proper arrow of a sheaf pulled back from the space are again pulled back from the \
space.  This is the field \
`ComparingTopologies.CohomologyComparison.weakSerre_rightDerived_relocalizationPushforward`, \
proved outright for every i, with the witness `R^i g_* G` specified rather than obtained from \
the existential.  The five conditions of Situation 0EZ3 are items (1)-(5) of that tag; the \
`(0EZ4)`/`(0EZ5)`/`(0EZ6)`/`(0EZ7)` names used elsewhere in this directory are this \
development's own, and this is `(0EZ7)`.  ALL FIVE CONDITIONS ARE NOW PROVED: the other four \
are `morphismProperty_baseChange` and `weakSerre_relocalizationInverseImage` \
(ZariskiComparisonSituationData.lean), `weakSerre_isSheaf_fine` \
(`isSheaf_qc_zariskiPullbackClass`, ZariskiPullbackClassQcSheaf.lean) and \
`covering_refinement` (`exists_zariskiRefinement_properMorphisms`, \
ZariskiQcCoveringRefinement.lean).  SITUATION 0EZ3 IS STILL NOT INSTANTIATED HERE, AND THIS \
CONDITION IS WHAT BLOCKS IT.  The carrier is settled: `CohomologyComparison` is declared for \
`[SmallCategory C]` with coefficients `Ab` in the carrier's own universe, `S.category` is \
`Type (u+1)` with morphisms in `Type u`, and the carrier is \
`CategoryTheory.SmallModel S.category` in `Type u`, `EssentiallySmall.{u} S.category` being the \
instance `LocallyQuasiCompactQcSite.category_essentiallySmall`.  That fixes the coefficients at \
`AddCommGrpCat.{u}`, where the sheaf condition is proved and where the restriction condition \
`zariskiPullbackClass_overMapPullback` now also holds, being stated for every \
`AddCommGrpCat.{max u t}`.  THIS condition is stated only at `AddCommGrpCat.{max (u+1) v}`.  ONE \
of the seven inputs of its proof now reaches `AddCommGrpCat.{u}`, being stated for every \
`AddCommGrpCat.{max u t}`: `abelianComparisonInverseImage_exact` (ZariskiSite.lean).  That was \
the input believed OBSTRUCTED rather than merely unrestated, because it went through \
`Small.{max (u+1) v} ((S.zariskiTopology.over X).Cover Y)ᵒᵖ` and the slice's covering sieves do \
live in `Type (u+1)`; it turns out not to need them, and now takes the `essentiallySmall_over` \
route, its Kan-extension shapes being `u`-small by `small_costructuredArrow_opensToSlice`.  The \
other six still carry `max (u+1) v` -- `topologicalPushforward` and `zariskiBaseChange` \
(ProperDerivedImage.lean), `isIso_zariskiBaseChange_of_properMap` \
(AbelianProperDirectImage.lean), `preservesFiniteLimits_zariskiSlicePushforward` \
(AcyclicityReduction.lean), and \
`isZero_rightDerived_sliceDirectImage_abelianComparisonInverseImage` with \
`rightDerivedZariskiBaseChangeIso` here.  THE NEXT ONE NEEDS A LEMMA THAT DOES NOT EXIST: \
restating `preservesFiniteLimits_zariskiSlicePushforward` at `max u t` fails even with both \
sheafifications built from `essentiallySmall_over`, because \
`(Over.pullback f).sheafPushforwardContinuous` is a right adjoint only when the left Kan \
extension along `(Over.pullback f).op` exists, which needs \
`Small.{max u t} (CostructuredArrow (Over.pullback f).op Z)`.  Those comma categories are \
indexed by `Over Y`, in `Type (u+1)`; at `max (u+1) v` their smallness is free from \
`Small.{max (u+1) v} α` for every `α : Type (max (u+1) v)` (Sheafification.lean), the one step \
that really uses `u+1 ≤ max (u+1) v`, and at `max u t` there is no such instance.  What is owed \
is the analogue of `small_costructuredArrow_opensToSlice` for `Over.pullback f`.  Past it the \
rest is RESTATEMENT, made large only because these facts are supplied as INSTANCES and an \
instance generalized to `max u t` is unusable -- `max u ?t =?= max (u+1) v` is not solvable by \
instance synthesis -- so each remaining input must take them as local `have`s, across the 32 \
files here that mention `max (u+1) v`.  Transporting the conditions along `equivSmallModel` is \
also not done"]
theorem zariskiPullbackClass_rightDerived_overMapPushforward (hf : S.properMorphisms f)
    (F : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (hF : S.zariskiPullbackClass.{u, w, v} X F) (i : ℕ) :
    S.zariskiPullbackClass.{u, w, v} Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over X) (S.zariskiTopology.over Y)).rightDerived i).obj F) := by
  have hproper := isProperMap_of_properMorphisms S f hf
  rw [zariskiPullbackClass, ObjectProperty.prop_map_iff] at hF ⊢
  obtain ⟨G, -, ⟨e⟩⟩ := hF
  have ecoc : (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over X) (S.zariskiTopology.over Y) ≅
      sliceDirectImage S f AddCommGrpCat.{max (u + 1) v} :=
    (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso AddCommGrpCat.{max (u + 1) v}
  refine ⟨((topologicalPushforward.{u, w, v} S f).rightDerived i).obj G, trivial, ⟨?_⟩⟩
  exact (rightDerivedZariskiBaseChangeIso.{u, w, v} S f hproper G i).symm ≪≫
    ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).mapIso e ≪≫
    ((Functor.rightDerivedIsoOfNatIso ecoc i).app F).symm

end Condition

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
