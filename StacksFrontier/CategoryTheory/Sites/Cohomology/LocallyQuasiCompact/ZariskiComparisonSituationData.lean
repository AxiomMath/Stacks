module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PullbackProperness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiRelativeCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Proper maps and pullbacks from the space as data for the comparison situation

Comparing cohomology on the quasi-compact site of Hausdorff, locally quasi-compact spaces with
cohomology on the Zariski site of the same category requires a distinguished class of arrows and,
over every object, a class of abelian sheaves on the localized Zariski site which is well behaved
for that class. Stacks 0EZI makes the choice: the arrows are the proper maps, and over `X` the
sheaves are those pulled back from the space `X` along the comparison morphism
`π_X : Sh(LC_Zar/X) → Sh(X)`.

This file makes both choices and proves two of the five conditions the choice has to satisfy:
the class of proper arrows is stable under arbitrary base change, and the class of sheaves pulled
back from the space is stable under restriction along an arbitrary arrow of the site.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properMorphisms`: the proper arrows of the
  site, as a class of morphisms.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackClass`: the abelian sheaves
  on the localized Zariski site of the form `π_X^{-1}G` for `G` an abelian sheaf on the space.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_isPullback_properMorphisms`: a
  proper arrow has a base change along any arrow, and that base change is proper.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackClass_overMapPullback`:
  restriction along an arrow of the site carries sheaves pulled back from the space to sheaves
  pulled back from the space.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 09WZ](https://stacks.math.columbia.edu/tag/09WZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The proper arrows of the site: those whose underlying continuous map is proper. This is the
class `P` of Stacks 0EZI. -/
def properMorphisms (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    MorphismProperty S.category :=
  fun _ _ f => _root_.IsProperMap (((siteToTop S).map f).hom : _ → _)

/-- A proper arrow of the site is proper in the sense of Stacks 005O (5),
`StacksDraft.Topology.IsProperMap`: its underlying map is separated and universally closed in the
fibre-product sense. -/
theorem stacksIsProperMap_of_properMorphisms
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    ⦃X Y : S.category⦄ (f : X ⟶ Y) (hf : S.properMorphisms f) :
    StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) := by
  have _ : T2Space ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X) :=
    inferInstanceAs (T2Space X.obj)
  exact ⟨T2Space.isSeparatedMap _, _root_.IsProperMap.isUniversallyClosedMap hf⟩

/-- A proper arrow of the site admits a base change along an arbitrary arrow, and that base change
is again proper. -/
@[stacks 0EZI "condition (0EZ4) of Situation 0EZ3 for the proper maps of LC"]
theorem exists_isPullback_properMorphisms
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    ⦃X Y Y' : S.category⦄ (f : X ⟶ Y) (hf : S.properMorphisms f) (g : Y' ⟶ Y) :
    ∃ (Z : S.category) (q : Z ⟶ X) (p : Z ⟶ Y'),
      IsPullback q p f g ∧ S.properMorphisms p :=
  ⟨pullback g f, pullback.snd g f, pullback.fst g f,
    (IsPullback.of_hasPullback g f).flip, S.isProperMap_pullback_fst f g hf⟩

/-- The abelian sheaves on the localized Zariski site over `X` of the form `π_X^{-1}G` with `G` an
abelian sheaf on the space `X`, with coefficients in `AddCommGrpCat.{max u t}`. This is the class
`A'_X` of Stacks 0EZI. -/
noncomputable def zariskiPullbackClassOfSize.{t}
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    ObjectProperty (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max u t}) :=
  (⊤ : ObjectProperty (Sheaf (Opens.grothendieckTopology X.obj)
      AddCommGrpCat.{max u t})).map
    (S.abelianComparisonInverseImageOfSize.{u, w, t} X)

/-- The abelian sheaves on the localized Zariski site over `X` of the form `π_X^{-1}G` with `G` an
abelian sheaf on the space `X`. This is the class `A'_X` of Stacks 0EZI. -/
noncomputable def zariskiPullbackClass
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    ObjectProperty (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) :=
  (⊤ : ObjectProperty (Sheaf (Opens.grothendieckTopology X.obj)
      AddCommGrpCat.{max (u + 1) v})).map
    (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X)

/-- The restriction condition of Stacks 0EZI with coefficients in `AddCommGrpCat.{max u t}`:
restriction along an arrow `f : X ⟶ Y` of the site carries the sheaves pulled back from `Y` to the
sheaves pulled back from `X`, a restriction of `π_Y^{-1}G` being `π_X^{-1}` of the inverse image
of `G` along the underlying map of `f`. -/
theorem zariskiPullbackClassOfSize_overMapPullback.{t}
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    ⦃X Y : S.category⦄ (f : X ⟶ Y)
    (F : Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max u t})
    (hF : S.zariskiPullbackClassOfSize.{u, w, t} Y F) :
    S.zariskiPullbackClassOfSize.{u, w, t} X
      ((S.zariskiTopology.overMapPullback AddCommGrpCat.{max u t} f).obj F) := by
  have hover (Z : S.category) : HasSheafify (S.zariskiTopology.over Z) AddCommGrpCat.{max u t} :=
    have := essentiallySmall_over.{u, w, t} S Z
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _
  have hopens (Z : S.category) :
      HasSheafify (Opens.grothendieckTopology Z.obj) AddCommGrpCat.{max u t} :=
    have : EssentiallySmall.{max u t} (Opens Z.obj) :=
      EssentiallySmall.mk' (AsSmall.equiv.{u, u, max u t} (C := Opens Z.obj))
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _
  have _ := hover X
  have _ := hover Y
  have _ := hopens X
  have _ := hopens Y
  rw [zariskiPullbackClassOfSize, ObjectProperty.prop_map_iff] at hF ⊢
  obtain ⟨G, -, ⟨e⟩⟩ := hF
  refine ⟨((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
      AddCommGrpCat.{max u t} (Opens.grothendieckTopology Y.obj)
      (Opens.grothendieckTopology X.obj)).obj G, trivial, ⟨?_⟩⟩
  exact (abelianComparisonSquareIsoOfSize.{u, w, t} S f).app G ≪≫
    (S.zariskiTopology.overMapPullback AddCommGrpCat.{max u t} f).mapIso e

/-- Restriction along an arrow `f : X ⟶ Y` of the site carries the sheaves pulled back from `Y`
to the sheaves pulled back from `X`: a restriction of `π_Y^{-1}G` is `π_X^{-1}` of the inverse
image of `G` along the underlying map of `f`. -/
@[stacks 0EZI "condition (0EZ5) of Situation 0EZ3 for the sheaves pulled back from the space"]
theorem zariskiPullbackClass_overMapPullback
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    ⦃X Y : S.category⦄ (f : X ⟶ Y)
    (F : Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})
    (hF : S.zariskiPullbackClass.{u, w, v} Y F) :
    S.zariskiPullbackClass.{u, w, v} X
      ((S.zariskiTopology.overMapPullback AddCommGrpCat.{max (u + 1) v} f).obj F) :=
  zariskiPullbackClassOfSize_overMapPullback.{u, w, max (u + 1) v} S f F hF

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
