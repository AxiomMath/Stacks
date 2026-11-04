module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.AbelianProperDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves pulled back from the space are sheaves for the quasi-compact topology

Over an object `X` of the site `LC_α` of Hausdorff, locally quasi-compact spaces, the class `A'_X`
of Stacks 0EZI consists of the abelian sheaves on the localized Zariski site of the form
`π_X^{-1}G` for `G` an abelian sheaf on the space underlying `X`. Every member of that class
already satisfies the sheaf condition for the *finer* quasi-compact topology, which is condition
(3) of Situation 0EZ3.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isSheaf_qc_zariskiPullbackClass`: condition
  (3) of Situation 0EZ3 for this situation, that an abelian sheaf on the localized Zariski site
  over `X` pulled back from the space underlying `X` satisfies the sheaf condition for the
  quasi-compact topology, at coefficients `AddCommGrpCat.{u}`.

## Implementation notes

The condition is proved at `AddCommGrpCat.{u}`, the universe of the spaces. `CohomologyComparison`
is stated for a carrier `C : Type u'` with `[SmallCategory C]` and takes its coefficients in
`Ab.{u'}`, so a carrier which is a small model of `S.category`, essentially small in `u` itself by
`LocallyQuasiCompactQcSite.category_essentiallySmall`, forces the coefficients to be
`AddCommGrpCat.{u}`. The abelian comparison adjunction itself exists at every coefficient universe
containing `u`, by `abelianComparisonDirectImage_isRightAdjoint`, the slice being essentially
`u`-small.

At `AddCommGrpCat.{max (u + 1) v}` the condition cannot be stated at all: `TopCat.Presheaf.stalk`
is declared for a space and coefficients in one and the same universe, so `GermPullback.Germs` is
unavailable for a `Type (max (u + 1) v)`-valued presheaf on a `TopCat.{u}` space, and the germ
model from which the condition is read off has no analogue there.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Lemma 18.31.2 (Tag 04JC)](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- **Stacks 0EZI.** An abelian sheaf on the localized Zariski site over `X` which is pulled back
from the space underlying `X` satisfies the sheaf condition for the quasi-compact topology over
`X`. -/
@[stacks 0EZI "condition (3) of Situation 0EZ3 for this situation: every abelian sheaf on the \
localized Zariski site that is pulled back from the space satisfies the sheaf condition for \
quasi-compact coverings.  This is the field \
`ComparingTopologies.CohomologyComparison.weakSerre_isSheaf_fine`, proved outright, with the \
sheaf on the space and the isomorphism to it taken from the essential image rather than from a \
choice.  The five conditions of Situation 0EZ3 are items (1)-(5) of that tag; the \
`(0EZ4)`/`(0EZ5)`/`(0EZ6)`/`(0EZ7)` names used elsewhere in this directory are this \
development's own, and this is `(0EZ6)`.  ALL FIVE CONDITIONS ARE NOW PROVED for this \
situation, but SITUATION 0EZ3 IS STILL NOT INSTANTIATED HERE.  `CohomologyComparison` is \
declared `(C : Type u') [SmallCategory C]` (ChangeOfTopology/ComparisonSituation.lean:117) and \
takes its coefficients in `Ab.{u'}`, so the carrier's universe fixes the coefficient universe.  \
`S.category` is `Type (u+1)` with morphisms in `Type u`, so `SmallCategory S.category` does not \
synthesize and the carrier is `CategoryTheory.SmallModel S.category`, in `Type u`; \
`EssentiallySmall.{u} S.category` IS now an instance, \
`LocallyQuasiCompactQcSite.category_essentiallySmall`.  The coefficients are therefore \
`AddCommGrpCat.{u}`, which is where this condition is proved and is why the carrier cannot be \
`AsSmall.{v} S.category`: that one would want `AddCommGrpCat.{max (u+1) v}`, where the germ \
model this condition is read off cannot even be stated.  Condition `(0EZ5)` \
(`zariskiPullbackClassOfSize_overMapPullback`) is now stated for every \
`AddCommGrpCat.{max u t}` and so holds at `AddCommGrpCat.{u}`.  WHAT BLOCKS THE BRIDGE is \
condition `(0EZ7)` (`zariskiPullbackClass_rightDerived_overMapPushforward`), still stated only at \
`AddCommGrpCat.{max (u+1) v}`.  ONE of the seven inputs of its proof now reaches \
`AddCommGrpCat.{u}`: `abelianComparisonInverseImage_exact`, which was the one believed obstructed \
rather than merely unrestated and turns out not to need the slice's covering sieves at all.  The \
next to move, `preservesFiniteLimits_zariskiSlicePushforward`, needs a lemma the library does not \
have -- `Small.{max u t} (CostructuredArrow (Over.pullback f).op Z)`, the analogue of \
`small_costructuredArrow_opensToSlice` for `Over.pullback f`, without which \
`(Over.pullback f).sheafPushforwardContinuous` is not known to be a right adjoint at `max u t`.  \
Past that the remaining five are a RESTATEMENT rather than new proper-base-change mathematics, \
made large only because the smallness and sheafification facts are supplied as INSTANCES, which \
cannot be generalized to `max u t` because `max u ?t =?= max (u+1) v` is not solvable by instance \
synthesis.  See `ZariskiHigherDirectImageClass.lean` for the list.  Transport of both \
precoverages and of the class along `equivSmallModel` is also not done"]
theorem isSheaf_qc_zariskiPullbackClass
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{u})
    (hG : S.zariskiPullbackClassOfSize.{u, w, u} X G) :
    Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X) G.obj := by
  rw [zariskiPullbackClassOfSize, ObjectProperty.prop_map_iff] at hG
  obtain ⟨F, -, ⟨e⟩⟩ := hG
  let : ReflectsLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u}) :=
    StrictlyPerfect.groupForget_reflectsLimitsOfSize
  refine Presheaf.isSheaf_of_isSheaf_comp (S.qcSite.grothendieckTopology.over X) G.obj
    (forget AddCommGrpCat.{u}) ?_
  exact (Presheaf.isSheaf_of_iso_iff
    ((sheafToPresheaf (S.zariskiTopology.over X) (Type u)).mapIso
      (((sheafCompose (S.zariskiTopology.over X)
          (forget AddCommGrpCat.{u})).mapIso e).symm ≪≫
        (abelianComparisonInverseImageForgetIsoOfSize.{u, w, u} S X).app F))).mpr
    (isSheaf_qc_comparisonInverseImage S X _)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
