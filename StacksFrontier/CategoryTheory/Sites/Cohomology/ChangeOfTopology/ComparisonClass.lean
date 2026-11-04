module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonSituation
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison class of abelian sheaves on the finer site

In the situation of Stacks 0EZ3 we are given, for every object `X` of the site, a weak Serre
class `𝒜'_X` of abelian sheaves on the coarser site localized at `X`. The class `𝒜_X` on the
finer localized site consists of the sheaves of the form `ε⁻¹ F` for `F` in `𝒜'_X`, where `ε`
is the change-of-topology morphism.

This file defines `𝒜_X` and proves the two basic properties of Stacks 0EZ9: an abelian sheaf
on the finer localized site lies in `𝒜_X` exactly when its change-of-topology direct image
lies in `𝒜'_X`, and `𝒜_X` is stable under restriction along an arbitrary morphism of the site.

The membership criterion holds because an object of `𝒜'_X` is, by assumption, already a sheaf
for the finer topology, so that sheafifying it changes nothing; and conversely because
`ε_* ε⁻¹` is the identity on the underlying presheaf of a fine sheaf. Stability under
restriction comes from the commutativity of the square of topoi, Stacks 0EZ2, in its abelian
form: restriction commutes with change of topology up to canonical isomorphism, so it carries
an essential image into an essential image.

## Main definitions

* `Stacks.ComparingTopologies.CohomologyComparison.fineWeakSerre`: the class `𝒜_X`, as the
  essential image of `𝒜'_X` under change of topology.

## Main results

* `Stacks.ComparingTopologies.CohomologyComparison.fineWeakSerre_iff_weakSerre_pushforward`:
  membership in `𝒜_X` is detected by change-of-topology direct image.
* `Stacks.ComparingTopologies.CohomologyComparison.fineWeakSerre_overMapPullback`: `𝒜_X` is
  stable under restriction along a morphism `X ⟶ Y`.

## Implementation notes

The phrase "of the form `ε⁻¹ F`" is represented by `ObjectProperty.map`, hence by the
essential image rather than the strict image. The resulting class is therefore automatically
invariant under replacing a sheaf by an isomorphic one, as is appropriate for a class of
objects in an abelian category, and the membership criterion can be stated for objects
without choosing a representative.

The abelian analogue of the square of topoi is built here rather than reused from
`StacksDraft.Ch21.Sec30.ComparingTopologies`, whose `comparisonPullbackOverMapPullbackIso` is
the same argument carried out for sheaves of types; the two could be unified by stating that
file's results for an arbitrary target category.

## References

* [Stacks Project, Tag 0EZ9](https://stacks.math.columbia.edu/tag/0EZ9)
-/

@[expose] public section

universe v u

open CategoryTheory

namespace Stacks.ComparingTopologies

variable {C : Type u} [Category.{v} C]

namespace CohomologyComparison

/-- **Stacks 0EZ9.** The class `𝒜_X` of abelian sheaves on the finer localized site: those of
the form `ε⁻¹ F` for `F` in the given weak Serre class `𝒜'_X` on the coarser localized site,
with `ε` the change-of-topology morphism. -/
@[stacks 0EZ9 "the category `𝒜_X`"]
noncomputable abbrev fineWeakSerre (S : CohomologyComparison C) (X : C) :
    ObjectProperty (Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) :=
  (S.weakSerre X).map (abelianComparisonPullback S.fineCoverage S.coarseCoverage X)

/-- **Stacks 0EZ9.** A sheaf on the finer localized site belongs to `𝒜_X` if and only if its
change-of-topology direct image belongs to `𝒜'_X`. -/
@[stacks 0EZ9 "the membership criterion for `𝒜_X`"]
theorem fineWeakSerre_iff_weakSerre_pushforward
    (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) :
    S.fineWeakSerre X F ↔
      S.weakSerre X
        ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).obj F) := by
  simp only [fineWeakSerre, ObjectProperty.prop_map_iff]
  constructor
  · rintro ⟨G, hG, ⟨e⟩⟩
    let Gfine : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v} :=
      ⟨G.obj, S.weakSerre_isSheaf_fine X G hG⟩
    have eG : Gfine ≅
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj G := by
      simpa [abelianComparisonPullback] using sheafificationIso Gfine
    exact (S.weakSerreClass X).toIsClosedUnderIsomorphisms.of_iso
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapIso (eG ≪≫ e)) hG
  · exact fun hF ↦ ⟨_, hF, ⟨by simpa [abelianComparisonPullback,
      abelianComparisonPushforward] using (sheafificationIso F).symm⟩⟩

/-- The identity functor of a localized site is continuous from the coarser to the finer
topology. -/
private theorem id_isContinuous_over (S : CohomologyComparison C) (Z : C) :
    (Functor.id (Over Z)).IsContinuous (S.coarseCoverage.toGrothendieck.over Z)
      (S.fineCoverage.toGrothendieck.over Z) :=
  { op_comp_isSheaf_of_types := fun F ↦ (isSheaf_iff_isSheaf_of_type _ _).1
      (F.property.of_le
        (over_le_over (Precoverage.toGrothendieck_mono S.coarse_le_fine) Z)) }

/-- The abelian form of the square of topoi of Stacks 0EZ2: change of topology commutes with
restriction along a morphism of the site, up to canonical isomorphism of inverse images. -/
private noncomputable def abelianComparisonPullbackOverMapPullbackIso
    (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    abelianComparisonPullback S.fineCoverage S.coarseCoverage Y ⋙
        S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} f ≅
      S.coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} f ⋙
        abelianComparisonPullback S.fineCoverage S.coarseCoverage X := by
  haveI := id_isContinuous_over S X
  haveI := id_isContinuous_over S Y
  let adjY := (Functor.id (Over Y)).sheafAdjunctionContinuous Ab
    (S.coarseCoverage.toGrothendieck.over Y) (S.fineCoverage.toGrothendieck.over Y)
  let adjX := (Functor.id (Over X)).sheafAdjunctionContinuous Ab
    (S.coarseCoverage.toGrothendieck.over X) (S.fineCoverage.toGrothendieck.over X)
  let rightEq :
      (Over.map f).sheafPushforwardCocontinuous Ab
          (S.fineCoverage.toGrothendieck.over X)
          (S.fineCoverage.toGrothendieck.over Y) ⋙
        (Functor.id (Over Y)).sheafPushforwardContinuous Ab
          (S.coarseCoverage.toGrothendieck.over Y)
          (S.fineCoverage.toGrothendieck.over Y) =
      (Functor.id (Over X)).sheafPushforwardContinuous Ab
          (S.coarseCoverage.toGrothendieck.over X)
          (S.fineCoverage.toGrothendieck.over X) ⋙
        (Over.map f).sheafPushforwardCocontinuous Ab
          (S.coarseCoverage.toGrothendieck.over X)
          (S.coarseCoverage.toGrothendieck.over Y) := rfl
  let adj₁ := adjY.comp
    ((Over.map f).sheafAdjunctionCocontinuous Ab
      (S.fineCoverage.toGrothendieck.over X)
      (S.fineCoverage.toGrothendieck.over Y))
  let adj₂ :=
    ((Over.map f).sheafAdjunctionCocontinuous Ab
      (S.coarseCoverage.toGrothendieck.over X)
      (S.coarseCoverage.toGrothendieck.over Y)).comp adjX
  let square := adj₁.leftAdjointUniq (adj₂.ofNatIsoRight (eqToIso rightEq).symm)
  exact Functor.isoWhiskerRight (abelianComparisonPullbackIsoSheafPullback S Y)
      (S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} f) ≪≫
    square ≪≫
    Functor.isoWhiskerLeft
      (S.coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} f)
      (abelianComparisonPullbackIsoSheafPullback S X).symm

/-- **Stacks 0EZ9.** Restriction along a morphism of the site preserves the class `𝒜` of
abelian sheaves on the finer localized sites. -/
@[stacks 0EZ9 "stability of `𝒜_X` under restriction"]
theorem fineWeakSerre_overMapPullback (S : CohomologyComparison C)
    {X Y : C} (f : X ⟶ Y)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over Y) Ab.{max u v})
    (hF : S.fineWeakSerre Y F) :
    S.fineWeakSerre X
      ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} f).obj F) := by
  simp only [fineWeakSerre, ObjectProperty.prop_map_iff] at hF ⊢
  obtain ⟨G, hG, ⟨e⟩⟩ := hF
  exact ⟨(S.coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} f).obj G,
    S.weakSerre_relocalizationInverseImage f G hG,
    ⟨((abelianComparisonPullbackOverMapPullbackIso S f).app G).symm ≪≫
      (S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} f).mapIso e⟩⟩

end CohomologyComparison

end Stacks.ComparingTopologies
