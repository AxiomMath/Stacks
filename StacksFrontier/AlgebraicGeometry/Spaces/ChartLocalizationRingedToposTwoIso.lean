module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalizationToposEquivalence

/-!
# The chart of an algebraic space over its localization, as a square of ringed topoi

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `U` be
an étale scheme chart of `X`. `AlgebraicGeometry.Space.chartLocalizationRingedToposHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartLocalizationToposEquivalence.lean` identifies the
small étale ringed topos of the chart with the localization of the small étale ringed topos of
`X` at the sheaf represented by the chart. This file records that the identification is
compatible with the two morphisms down to the small étale ringed topos of `X`.

## Main results

* `AlgebraicGeometry.Space.forget_map_chartLocalizationStructureSheafIso_hom`: on underlying
  sheaves of sets, the comparison of the two structure sheaves is the comparison of the two
  inverse images evaluated at `𝒪_X`.
* `AlgebraicGeometry.Space.chartLocalizationRestrictionTwoIso`: the morphism of small étale
  ringed topoi of the chart, in its restriction presentation, is 2-isomorphic to the
  localization morphism of [Stacks Project, Tag 04IE] composed with the identification.

## Implementation notes

The computation of the underlying map of sheaves of sets of
`AlgebraicGeometry.Space.chartLocalizationStructureSheafIso` follows
`AlgebraicGeometry.RingedSite.representableLocalizationStructureSheafIso_hom_forget` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/StructureSheafComparison.lean`, which is
the same computation for a ringed site localized at a representable sheaf. Two discipline points
carry over from there, and both apply here:

* the comparison of the inverse image along a composite morphism of topoi with the iterated
  inverse image is eaten by
  `Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingCompIso_inv_app_comp`, which
  keeps the remaining factor at its type on underlying sheaves of sets. Its own statement —
  that the comparison is an identity — cannot be stated here at all: deciding that its domain
  and codomain are the same sheaf exhausts the elaborator's budget at this morphism of topoi;
* the generic category and isomorphism rewrites (`CategoryTheory.Category.comp_id`,
  `CategoryTheory.Iso.trans_hom`, `CategoryTheory.Functor.map_comp`) do not fire by `rw` or
  `simp only` on the sheaves of commutative rings of these sites, so every step is taken in term
  mode or by `apply`, whose unification succeeds where keyed matching does not.

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

/-- **The identification of the inverse image of `𝒪_X` along the localization with the
localized structure sheaf is the identity on underlying sheaves of sets.**

The structure sheaf of `AlgebraicGeometry.RingedTopos.localizedRingedTopos` *is* the restriction
of `𝒪_X` to the site of elements, so
`AlgebraicGeometry.RingedTopos.localizationInverseImageCommRingIso` is
`Stacks.Sheaves.ToposCommRingImageAdjunction.restrictionCommRingIso`, whose two directions are
both the identity on underlying sheaves of sets. -/
theorem forget_map_localizationInverseImageCommRingIso_inv :
    (sheafCompose ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).J (forget CommRingCat.{u})).map
        (RingedTopos.localizationInverseImageCommRingIso (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U)).inv = 𝟙 _ := rfl

/-- **Read through the identification of the two localized topoi it is still the identity.**
The inverse image of an identity is an identity. -/
theorem inverseImage_map_forget_localizationInverseImageCommRingIso_inv :
    (chartLocalizationToposHom' B S hS X U).inverseImage.map
        ((sheafCompose ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U)).J (forget CommRingCat.{u})).map
          (RingedTopos.localizationInverseImageCommRingIso (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U)).inv) = 𝟙 _ := by
  rw [forget_map_localizationInverseImageCommRingIso_inv]
  exact CategoryTheory.Functor.map_id _ _

/-- **The first two factors of the comparison of structure sheaves drop out of any composite, on
underlying sheaves of sets.**

`AlgebraicGeometry.Space.chartLocalizationStructureSheafIso` is a composite of four
isomorphisms, of which the first two — the inverse image along the identification of the
localized structure sheaf, and the comparison of the inverse image along a composite morphism of
topoi with the iterated inverse image — are the identity on underlying sheaves of sets.

The remaining factor is kept as the variable `b`, in the result type it has on underlying sheaves
of sets, so that no later step has to decide the type of the inverse image of sheaves of
commutative rings along the composite morphism of topoi: deciding it is what exhausts the
elaborator's budget here. -/
theorem forget_map_chartLocalizationStructureSheafIso_prefix_comp
    {Bsh : Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) CommRingCat.{u}}
    (b : (inverseImageCommRingFunctor
        ((RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U)).toToposHom.comp
          (chartLocalizationToposHom' B S hS X U))).obj
        (smallEtaleRingedTopos B S hS X).O ⟶ Bsh) :
    (sheafCompose (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).J
          (forget CommRingCat.{u})).map
        ((inverseImageCommRingFunctor (chartLocalizationToposHom' B S hS X U)).map
            (RingedTopos.localizationInverseImageCommRingIso (smallEtaleRingedTopos B S hS X)
              (smallEtaleChartSheaf B S hS X U)).inv ≫
          (MorphismOfTopoi.inverseImageCommRingCompIso (chartLocalizationToposHom' B S hS X U)
                (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
                  (smallEtaleChartSheaf B S hS X U)).toToposHom).inv.app
              (smallEtaleRingedTopos B S hS X).O ≫
            b) =
      (sheafCompose (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).J
        (forget CommRingCat.{u})).map b := by
  refine (forget_map_inverseImageCommRing_map_comp (chartLocalizationToposHom' B S hS X U)
    (RingedTopos.localizationInverseImageCommRingIso (smallEtaleRingedTopos B S hS X)
      (smallEtaleChartSheaf B S hS X U)).inv _).trans ?_
  rw [inverseImage_map_forget_localizationInverseImageCommRingIso_inv]
  refine (Category.id_comp _).trans ?_
  apply forget_map_inverseImageCommRingCompIso_inv_app_comp

/-- **The third factor is the comparison of inverse images itself**, on underlying sheaves of
sets.  `AlgebraicGeometry.Space.chartLocalizationCommRingInverseImageIso` is the lift of
`AlgebraicGeometry.Space.chartLocalizationInverseImageIso'` to sheaves of commutative rings by
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso`, and that lift is the
original natural isomorphism on underlying sheaves of sets on the nose. -/
theorem forget_map_chartLocalizationCommRingInverseImageIso_app_hom :
    (sheafCompose (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          (forget CommRingCat.{u})).map
        ((chartLocalizationCommRingInverseImageIso B S hS X U).app
          (smallEtaleRingedTopos B S hS X).O).hom =
      (chartLocalizationInverseImageIso' B S hS X U).hom.app
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X).O) := rfl

/-- **The comparison of the two structure sheaves at a chart induces the canonical comparison of
the two inverse images.**

This is the one equation the chartwise 2-isomorphism of [Stacks Project, Tag 04KL] needs from
the identification of the two localized topoi: on underlying sheaves of sets,
`AlgebraicGeometry.Space.chartLocalizationStructureSheafIso` is
`AlgebraicGeometry.Space.chartLocalizationInverseImageIso'` evaluated at `𝒪_X`.

Three of the four factors contribute nothing: the first two by
`AlgebraicGeometry.Space.forget_map_chartLocalizationStructureSheafIso_prefix_comp` and the last
by `AlgebraicGeometry.Space.forgetRing_map_chartRestrictionStructureSheafIso_hom`, which is the
reason that factor was taken to be the structure map of the chart in its restriction
presentation. -/
theorem forget_map_chartLocalizationStructureSheafIso_hom :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationStructureSheafIso B S hS X U).hom =
      (chartLocalizationInverseImageIso' B S hS X U).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj
          (smallEtaleRingedTopos B S hS X).O) := by
  have key : (sheafCompose (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).J
        (forget CommRingCat.{u})).map
      ((inverseImageCommRingFunctor (chartLocalizationToposHom' B S hS X U)).map
          (RingedTopos.localizationInverseImageCommRingIso (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U)).inv ≫
        (MorphismOfTopoi.inverseImageCommRingCompIso (chartLocalizationToposHom' B S hS X U)
              (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
                (smallEtaleChartSheaf B S hS X U)).toToposHom).inv.app
            (smallEtaleRingedTopos B S hS X).O ≫
          ((chartLocalizationCommRingInverseImageIso B S hS X U).app
                (smallEtaleRingedTopos B S hS X).O).hom ≫
            (chartRestrictionStructureSheafIso B S hS X U).hom) =
      (chartLocalizationInverseImageIso' B S hS X U).hom.app
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X).O) := by
    refine (forget_map_chartLocalizationStructureSheafIso_prefix_comp B S hS X U _).trans ?_
    rw [CategoryTheory.Functor.map_comp,
      forget_map_chartLocalizationCommRingInverseImageIso_app_hom,
      forgetRing_map_chartRestrictionStructureSheafIso_hom]
    exact Category.comp_id _
  exact key

/-- **The inverse-image structure map of the localization morphism after the identification is
the comparison of structure sheaves**, on underlying sheaves of sets.

The structure map of a composite is the inverse image of the second factor's followed by the
first factor's, and the localization morphism's is the identity on underlying sheaves of sets,
so only the identification's survives — and that one is the comparison of structure sheaves by
`AlgebraicGeometry.Space.chartLocalizationRingedToposHom_fSharpInverseImage`. -/
theorem forgetRing_map_comp_localizationMorphism_chartLocalization_fSharpInverseImage :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (RingedToposHom.comp
          (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
          (Y := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X U))
          (Z := smallEtaleRingedTopos B S hS X)
          (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U))
          (chartLocalizationRingedToposHom B S hS X U)).fSharpInverseImage =
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationStructureSheafIso B S hS X U).hom := by
  refine (RingedToposHom.comp_fSharpInverseImage_forget
    (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
      (smallEtaleChartSheaf B S hS X U))
    (chartLocalizationRingedToposHom B S hS X U)).trans ?_
  refine Eq.trans (congrArg (fun z ↦ (chartLocalizationToposHom' B S hS X U).inverseImage.map z ≫
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationRingedToposHom B S hS X U).fSharpInverseImage)
    (RingedToposHom.forgetRing_localizationMorphism_fSharpInverseImage
      (smallEtaleRingedTopos B S hS X) (smallEtaleChartSheaf B S hS X U))) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationRingedToposHom B S hS X U).fSharpInverseImage)
    (CategoryTheory.Functor.map_id (chartLocalizationToposHom' B S hS X U).inverseImage _)) ?_
  refine (Category.id_comp _).trans ?_
  exact congrArg _ (chartLocalizationRingedToposHom_fSharpInverseImage B S hS X U)

/-- **The morphism of small étale ringed topoi of a chart, in its restriction presentation, is
2-isomorphic to the localization morphism of [Stacks Project, Tag 04IE] after the identification
of the two localized topoi.**

This is the first of the two comparisons the chartwise 2-isomorphism of [Stacks Project,
Tag 04KL] is assembled from: it says that the square identifying the small étale topos of a
chart with the localization at the chart commutes over the small étale topos of `X`, as a square
of *ringed* topoi.

Both sides have `AlgebraicGeometry.Space.chartLocalizationInverseImageIso'` for their comparison
of inverse images, and the compatibility of that comparison with the two structure maps is
`AlgebraicGeometry.Space.forget_map_chartLocalizationStructureSheafIso_hom` together with the
two structure maps that are identities on underlying sheaves of sets, namely the chart's in its
restriction presentation and the localization morphism's. -/
noncomputable def chartLocalizationRestrictionTwoIso :
    RingedToposHom.TwoIso
      (A := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
      (B := smallEtaleRingedTopos B S hS X)
      (smallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U))
      (RingedToposHom.comp
        (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
        (Y := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U))
        (Z := smallEtaleRingedTopos B S hS X)
        (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U))
        (chartLocalizationRingedToposHom B S hS X U)) :=
  RingedToposHom.TwoIso.ofInverseImageIso
    (A := smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
    (B := smallEtaleRingedTopos B S hS X)
    (chartLocalizationInverseImageIso' B S hS X U)
    ((congrArg (fun z ↦ (chartLocalizationInverseImageIso' B S hS X U).hom.app
            ((smallEtaleRingedTopos B S hS X).forgetRing.obj
              (smallEtaleRingedTopos B S hS X).O) ≫ z)
        (forgetRing_map_smallEtaleRestriction_fSharpInverseImage B S hS
          (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U))).trans
      ((Category.comp_id _).trans
        ((forget_map_chartLocalizationStructureSheafIso_hom B S hS X U).symm.trans
          (forgetRing_map_comp_localizationMorphism_chartLocalization_fSharpInverseImage
            B S hS X U).symm)))

end AlgebraicGeometry.Space

end
