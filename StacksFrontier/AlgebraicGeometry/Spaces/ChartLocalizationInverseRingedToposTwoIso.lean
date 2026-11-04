module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoUnitor
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalizationRingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleRingedToposConjugate
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId

/-!
# The inverse chart identification over the localization, as a square of ringed topoi

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `U` be
an étale scheme chart of `X`. `AlgebraicGeometry.Space.chartLocalizationRestrictionTwoIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartLocalizationRingedToposTwoIso.lean` says that the
morphism of small étale ringed topoi of the chart factors, up to 2-isomorphism, through the
localization of the small étale ringed topos of `X` at the sheaf represented by the chart. This
file records the same for the identification read in the other direction, which is the form the
chartwise comparison of [Stacks Project, Tag 04KL] consumes.

## Main results

* `AlgebraicGeometry.Space.chartLocalizationRingedToposCompTwoIso`: the identification after its
  inverse is 2-isomorphic to the identity of the localization.
* `AlgebraicGeometry.Space.chartLocalizationInverseRestrictionTwoIso`: the inverse
  identification followed by the chart's morphism of small étale ringed topoi is 2-isomorphic to
  the localization morphism of [Stacks Project, Tag 04IE].

## Implementation notes

The comparison does **not** go through a triangle identity, and
`AlgebraicGeometry.RingedToposHom.TwoIso.ofCommonRightAdjoint` is not used. The reason is that
both structure maps are known outright on underlying sheaves of sets: the identification's is
`AlgebraicGeometry.Space.forget_map_chartLocalizationStructureSheafIso_hom` and the inverse
identification's is that lemma inverted, transported along the functor of the equivalence and
followed by the counit — which is forced, since the inverse identification's structure map is
*defined* to be the inverse comparison of structure sheaves. The two then cancel, and what is
left is that the counit of an equivalence cancels its own inverse.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasSheafCompose_forget_ringCat
  AlgebraicGeometry.hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- **The inverse of the comparison of structure sheaves induces the inverse of the comparison of
inverse images.**  `AlgebraicGeometry.Space.forget_map_chartLocalizationStructureSheafIso_hom`
read as an equality of isomorphisms, and inverted. -/
theorem forget_map_chartLocalizationStructureSheafIso_inv :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationStructureSheafIso B S hS X U).inv =
      (chartLocalizationInverseImageIso' B S hS X U).inv.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj
          (smallEtaleRingedTopos B S hS X).O) :=
  congrArg Iso.inv
    (Iso.ext (forget_map_chartLocalizationStructureSheafIso_hom B S hS X U) :
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.mapIso
          (chartLocalizationStructureSheafIso B S hS X U) =
        (chartLocalizationInverseImageIso' B S hS X U).app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj
            (smallEtaleRingedTopos B S hS X).O))

/-- **The inverse-image form of the structure map of the identification read from the
localization.**  Its structure map is the inverse of the comparison of structure sheaves, and the
inverse image of the identification is the functor of the equivalence, so by adjointness the
inverse-image form is that inverse transported along the functor and followed by the counit. -/
theorem forgetRing_map_chartLocalizationRingedToposInverse_fSharpInverseImage :
    ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).forgetRing.map
        (chartLocalizationRingedToposInverse B S hS X U).fSharpInverseImage =
      (chartLocalizationToposEquivalence B S hS X U).functor.map
          ((chartLocalizationInverseImageIso' B S hS X U).inv.app
            ((smallEtaleRingedTopos B S hS X).forgetRing.obj
              (smallEtaleRingedTopos B S hS X).O)) ≫
        (chartLocalizationToposInverse B S hS X U).adj.counit.app
          (((smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U)).forgetRing.obj
            ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
              (smallEtaleChartSheaf B S hS X U)).O) := by
  refine (RingedToposHom.fSharpInverseImage_forget
    (chartLocalizationRingedToposInverse B S hS X U)).trans ?_
  exact congrArg (fun z ↦ (chartLocalizationToposEquivalence B S hS X U).functor.map z ≫
      (chartLocalizationToposInverse B S hS X U).adj.counit.app
        (((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).forgetRing.obj
          ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U)).O))
    (forget_map_chartLocalizationStructureSheafIso_inv B S hS X U)

/-- **The inverse-image form of the structure map of the identification read from the chart is
the comparison of inverse images at `𝒪_X`.** -/
theorem forgetRing_map_chartLocalizationRingedToposHom_fSharpInverseImage :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationRingedToposHom B S hS X U).fSharpInverseImage =
      (chartLocalizationInverseImageIso' B S hS X U).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj
          (smallEtaleRingedTopos B S hS X).O) :=
  (congrArg (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
      (chartLocalizationRingedToposHom_fSharpInverseImage B S hS X U)).trans
    (forget_map_chartLocalizationStructureSheafIso_hom B S hS X U)

/-- **The structure map of the identification after its inverse is the counit of the
equivalence**, on underlying sheaves of sets.

The two structure maps contribute the comparison of inverse images at `𝒪_X` and its inverse, and
those cancel, leaving only the counit that the second one's adjointness introduced.  This is the
whole content of the comparison of the identification's two directions: no triangle identity is
needed, because both structure maps are *known* on underlying sheaves of sets. -/
theorem forgetRing_map_chartLocalizationComp_fSharpInverseImage :
    ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).forgetRing.map
        (RingedToposHom.comp
          (X := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U))
          (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
          (Z := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U))
          (chartLocalizationRingedToposHom B S hS X U)
          (chartLocalizationRingedToposInverse B S hS X U)).fSharpInverseImage =
      (chartLocalizationToposInverse B S hS X U).adj.counit.app
        (((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).forgetRing.obj
          ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U)).O) := by
  refine (RingedToposHom.comp_fSharpInverseImage_forget
    (chartLocalizationRingedToposHom B S hS X U)
    (chartLocalizationRingedToposInverse B S hS X U)).trans ?_
  rw [forgetRing_map_chartLocalizationRingedToposHom_fSharpInverseImage,
    forgetRing_map_chartLocalizationRingedToposInverse_fSharpInverseImage]
  refine (Category.assoc _ _ _).symm.trans ?_
  erw [← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The structure map of the identity morphism of the localized ringed topos is the identity**,
in inverse-image form and on underlying sheaves of sets. -/
theorem forgetRing_map_localizedId_fSharpInverseImage :
    ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).forgetRing.map
        (RingedToposHom.id ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U))).fSharpInverseImage =
      𝟙 (((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U)).forgetRing.obj
        ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).O) := by
  refine (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (RingedToposHom.id ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
      (smallEtaleChartSheaf B S hS X U)))).trans ?_
  exact RingedToposHom.fSharpInverseImageForget_id
    ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
      (smallEtaleChartSheaf B S hS X U))

/-- **The identification of the two localized topoi, after its inverse, is 2-isomorphic to the
identity of the localization.**

Its comparison of inverse images is the counit of the equivalence, and the compatibility with
the two structure maps is
`AlgebraicGeometry.Space.forgetRing_map_chartLocalizationComp_fSharpInverseImage` against the
identity's, so the whole statement is that the counit cancels its own inverse. -/
noncomputable def chartLocalizationRingedToposCompTwoIso :
    RingedToposHom.TwoIso
      (A := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U))
      (B := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U))
      (RingedToposHom.comp
        (X := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U))
        (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
        (Z := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U))
        (chartLocalizationRingedToposHom B S hS X U)
        (chartLocalizationRingedToposInverse B S hS X U))
      (RingedToposHom.id ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U))) :=
  RingedToposHom.TwoIso.ofInverseImageIso
    (A := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
      (smallEtaleChartSheaf B S hS X U))
    (B := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
      (smallEtaleChartSheaf B S hS X U))
    (chartLocalizationToposEquivalence B S hS X U).counitIso.symm
    ((congrArg (fun z ↦ (chartLocalizationToposEquivalence B S hS X U).counitIso.symm.hom.app
            (((smallEtaleRingedTopos B S hS X).localizedRingedTopos
              (smallEtaleChartSheaf B S hS X U)).forgetRing.obj
              ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
                (smallEtaleChartSheaf B S hS X U)).O) ≫ z)
        (forgetRing_map_chartLocalizationComp_fSharpInverseImage B S hS X U)).trans
      (((chartLocalizationToposEquivalence B S hS X U).counitIso.inv_hom_id_app
            (((smallEtaleRingedTopos B S hS X).localizedRingedTopos
              (smallEtaleChartSheaf B S hS X U)).forgetRing.obj
              ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
                (smallEtaleChartSheaf B S hS X U)).O)).trans
        (forgetRing_map_localizedId_fSharpInverseImage B S hS X U).symm))

/-- **The identification of the two localized topoi read from the localization, followed by the
morphism of small étale ringed topoi of the chart, is 2-isomorphic to the localization morphism
of [Stacks Project, Tag 04IE].**

This is the second of the two comparisons the chartwise 2-isomorphism of [Stacks Project,
Tag 04KL] is assembled from, and it is deduced from the first —
`AlgebraicGeometry.Space.chartLocalizationRestrictionTwoIso` — by whiskering with the inverse
identification and cancelling it against the identification by
`AlgebraicGeometry.Space.chartLocalizationRingedToposCompTwoIso`.  No second comparison of
inverse images and no triangle identity enters. -/
noncomputable def chartLocalizationInverseRestrictionTwoIso :
    RingedToposHom.TwoIso
      (A := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U))
      (B := smallEtaleRingedTopos B S hS X)
      (RingedToposHom.comp
        (X := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U))
        (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
        (Z := smallEtaleRingedTopos B S hS X)
        (smallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U))
        (chartLocalizationRingedToposInverse B S hS X U))
      (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)) :=
  (RingedToposHom.TwoIso.whiskerLeft (chartLocalizationRingedToposInverse B S hS X U)
      (chartLocalizationRestrictionTwoIso B S hS X U)).trans
    ((RingedToposHom.TwoIso.associator (chartLocalizationRingedToposInverse B S hS X U)
        (chartLocalizationRingedToposHom B S hS X U)
        (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U))).symm.trans
      ((RingedToposHom.TwoIso.whiskerRight (chartLocalizationRingedToposCompTwoIso B S hS X U)
          (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U))).trans
        (RingedToposHom.TwoIso.compId
          (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U)))))

end AlgebraicGeometry.Space

end
