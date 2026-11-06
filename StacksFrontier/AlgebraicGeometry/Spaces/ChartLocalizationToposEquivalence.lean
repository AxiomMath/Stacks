module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartFamilyInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartLocalizedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.ToposComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceEquivalence

/-!
# The small étale topos of a chart is the localization at the chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `U` be
an étale scheme chart of `X`. There are two ways to localize the small étale topos of `X` at
`U`: localize the ringed *topos* at the sheaf `h_U` represented by the chart, which is
`AlgebraicGeometry.RingedTopos.localizedRingedTopos` of Stacks 04IE, or pass to the small étale
topos of the algebraic space `AlgebraicGeometry.Space.chartSpace` represented by the chart. This
file identifies the two topoi.

## Main definitions

* `AlgebraicGeometry.Space.chartSheafifyIso`: the sheafification of the presheaf represented by
  a chart is the sheaf `AlgebraicGeometry.Space.smallEtaleChartSheaf` represented by it, the
  small étale topology being subcanonical.
* `AlgebraicGeometry.Space.chartLocalizationToposEquivalence`: the identification of the two
  localized topoi.
* `AlgebraicGeometry.Space.chartLocalizationToposHom'` and
  `AlgebraicGeometry.Space.chartLocalizationToposInverse`: that identification read as a
  morphism of topoi, in each direction.
* `AlgebraicGeometry.Space.chartLocalizationStructureSheafIso`: the two structure sheaves agree.
* `AlgebraicGeometry.Space.chartLocalizationRingedToposHom` and
  `AlgebraicGeometry.Space.chartLocalizationRingedToposInverse`: the identification as a
  morphism of **ringed** topoi, in each direction.

## Main results

* `AlgebraicGeometry.Space.isLocallyRinged_chartLocalizationRingedToposHom` and
  `AlgebraicGeometry.Space.isLocallyRinged_chartLocalizationRingedToposInverse`: both
  directions are morphisms of *locally* ringed topoi, so composing with either preserves
  local-ringedness.
* `AlgebraicGeometry.Space.isRightAdjoint_overForget_sheafPushforwardContinuous`: the slice
  pullback on the small étale site has a left adjoint at `Type u`.

## Implementation notes

The identification is a composite of three equivalences and one isomorphism of sheaves:

* Stacks 04M0 on sheaves, `AlgebraicGeometry.Space.chartSliceSheafEquivOfCoefficients`,
  identifies sheaves on the small étale site of the chart with sheaves on the localization
  `X_étale/U` of the site;
* Stacks 00Y1, `CategoryTheory.OverShriek.sheafEquivalence`, identifies those with the slice
  topos over the sheafification of `h_U`;
* `AlgebraicGeometry.Space.chartSheafifyIso` replaces that sheafification by
  `AlgebraicGeometry.Space.smallEtaleChartSheaf`, which is legitimate because the small étale
  topology is subcanonical;
* Stacks 04IE's slice identification,
  `AlgebraicGeometry.RingedTopos.localizationEquivalence`, identifies the slice topos with the
  localization of the ringed topos at that sheaf.

The site of elements of `h_U` is not compared with the slice `X_étale/U` directly; the
comparison goes through the two slice topoi.

The coefficient universe of `chartSliceSheafEquivOfCoefficients` is used here at `u`, the
universe of the sections of the structure sheaf, rather than at `u + 1`, the universe of the
sheaves of the spaces-étale site.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IQ](https://stacks.math.columbia.edu/tag/04IQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

/-- **Moving the base of `CategoryTheory.toOver` along an isomorphism.**  For an isomorphism
`i : A ≅ A'` of a cartesian monoidal category, the functor `G ↦ (G ⊗ A, snd ≫ i)` into the slice
over `A'` is the functor `G ↦ (G ⊗ A', snd)`: the two differ by `G ◁ i`, which commutes with the
second projections. -/
noncomputable def toOverMapIso {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A A' : C} (i : A ≅ A') : toOver A ⋙ Over.map i.hom ≅ toOver A' :=
  NatIso.ofComponents
    (fun G => Over.isoMk (MonoidalCategory.whiskerLeftIso G i)
      (CartesianMonoidalCategory.whiskerLeft_snd G i.hom))
    (fun f => Over.OverMorphism.ext (MonoidalCategory.whisker_exchange f i.hom).symm)

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasSheafCompose_forget_ringCat
  AlgebraicGeometry.hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-! ### The sheafification of a representable chart -/

/-- The presheaf represented by an étale scheme chart of `X` is a sheaf for the small étale
topology, which is subcanonical. -/
theorem isSheaf_yoneda_chart :
    Presheaf.IsSheaf (SmallEtale.topology B S hS X.1) (yoneda.obj U) :=
  (smallEtaleChartSheaf B S hS X U).property

/-- **The sheafification of the presheaf represented by a chart is the sheaf represented by
it.**  The presheaf is already a sheaf, so the unit of the sheafification adjunction at it is an
isomorphism, and `CategoryTheory.sheafToPresheaf` is fully faithful, so that isomorphism of
presheaves is an isomorphism of sheaves. -/
noncomputable def chartSheafifyIso :
    (presheafToSheaf (SmallEtale.topology B S hS X.1) (Type u)).obj (yoneda.obj U) ≅
      smallEtaleChartSheaf B S hS X U :=
  ((fullyFaithfulSheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).preimageIso
    (X := smallEtaleChartSheaf B S hS X U)
    (Y := (presheafToSheaf (SmallEtale.topology B S hS X.1) (Type u)).obj (yoneda.obj U))
    (@asIso _ _ _ _ (toSheafify (SmallEtale.topology B S hS X.1) (yoneda.obj U))
      (isIso_toSheafify _ (isSheaf_yoneda_chart B S hS X U)))).symm

/-! ### The identification of the two localized topoi -/

/-- **The small étale topos of an étale scheme chart `U` of `X` is the localization of the small
étale topos of `X` at the sheaf represented by `U`.** -/
noncomputable def chartLocalizationToposEquivalence :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).Topos ≌
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U)).Topos :=
  (chartSliceSheafEquivOfCoefficients.{u} B S hS X U).symm.trans
    ((CategoryTheory.OverShriek.sheafEquivalence (U := U)
        (SmallEtale.topology B S hS X.1)).trans
      ((Over.mapIso (chartSheafifyIso B S hS X U)).trans
        (RingedTopos.localizationEquivalence (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U)).symm))

/-- The identification of the two localized topoi, read as a morphism of topoi from the small
étale topos of the chart: its inverse image is the inverse of the equivalence, which is left
exact because an equivalence is.

It differs from `AlgebraicGeometry.Space.chartLocalizationToposHom`, whose inverse image is
`AlgebraicGeometry.Space.chartElementEquivalence`'s continuous pushforward rather than the inverse
of the equivalence above. -/
noncomputable def chartLocalizationToposHom' :
    MorphismOfTopoi (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).Topos
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U)).Topos where
  pushforward := (chartLocalizationToposEquivalence B S hS X U).functor
  inverseImage := (chartLocalizationToposEquivalence B S hS X U).inverse
  adj := (chartLocalizationToposEquivalence B S hS X U).symm.toAdjunction
  preservesFiniteLimits :=
    haveI := Adjunction.rightAdjoint_preservesLimits
      (chartLocalizationToposEquivalence B S hS X U).toAdjunction
    ⟨fun _ _ _ ↦ inferInstance⟩

/-- The identification of the two localized topoi, read as a morphism of topoi from the
localization: its inverse image is the functor of the equivalence. -/
noncomputable def chartLocalizationToposInverse :
    MorphismOfTopoi
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U)).Topos
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).Topos where
  pushforward := (chartLocalizationToposEquivalence B S hS X U).inverse
  inverseImage := (chartLocalizationToposEquivalence B S hS X U).functor
  adj := (chartLocalizationToposEquivalence B S hS X U).toAdjunction
  preservesFiniteLimits :=
    haveI := Adjunction.rightAdjoint_preservesLimits
      (chartLocalizationToposEquivalence B S hS X U).symm.toAdjunction
    ⟨fun _ _ _ ↦ inferInstance⟩

/-- The inverse image of the identification, read from the small étale topos of the chart, is
the inverse of the equivalence. -/
@[simp]
theorem chartLocalizationToposHom_inverseImage :
    (chartLocalizationToposHom' B S hS X U).inverseImage =
      (chartLocalizationToposEquivalence B S hS X U).inverse :=
  rfl

/-- The inverse image of the identification, read from the localization, is the functor of the
equivalence. -/
@[simp]
theorem chartLocalizationToposInverse_inverseImage :
    (chartLocalizationToposInverse B S hS X U).inverseImage =
      (chartLocalizationToposEquivalence B S hS X U).functor :=
  rfl

/-- The inverse image of the identification, read from the small étale topos of the chart, is an
equivalence. -/
instance isEquivalence_chartLocalizationToposHom_inverseImage :
    (chartLocalizationToposHom' B S hS X U).inverseImage.IsEquivalence :=
  inferInstanceAs ((chartLocalizationToposEquivalence B S hS X U).inverse.IsEquivalence)

/-- The inverse image of the identification, read from the localization, is an equivalence. -/
instance isEquivalence_chartLocalizationToposInverse_inverseImage :
    (chartLocalizationToposInverse B S hS X U).inverseImage.IsEquivalence :=
  inferInstanceAs ((chartLocalizationToposEquivalence B S hS X U).functor.IsEquivalence)

/-! ### The two inverse images from the small étale topos of `X` -/

/-- **Restriction to an étale scheme chart is the slice pullback, at the universe of the
sections of the structure sheaf.**  This is
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso` with `Type u` coefficients instead of
`Type (u + 1)`, and with the chart restriction spelled as restriction along small étale
postcomposition rather than as the inverse image of Stacks 03G2. -/
noncomputable def chartSetRestriction_overPullbackIso :
    smallEtaleSetRestriction B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U) ≅
      (SmallEtale.topology B S hS X.1).overPullback (Type u) U ⋙
        (chartSliceSheafEquivOfCoefficients.{u} B S hS X U).functor := by
  have hu := isContinuous_chartLocalization_chartSpace B S hS X U
  have hfg : (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (SmallEtale.topology B S hS X.1) :=
    smallEtalePostcomp_isContinuous B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)
  exact (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Iso.refl (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U)) (Type u) _
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    ((SmallEtale.topology B S hS X.1).over U) (SmallEtale.topology B S hS X.1) hu _ hfg).symm

/-- Restriction to a chart, followed by the inverse of Stacks 04M0 on sheaves, is the slice
pullback: `AlgebraicGeometry.Space.chartSetRestriction_overPullbackIso` with the equivalence
cancelled against its inverse. -/
noncomputable def chartSetRestrictionCompSliceInverseIso :
    smallEtaleSetRestriction B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U) ⋙
        (chartSliceSheafEquivOfCoefficients.{u} B S hS X U).inverse ≅
      (SmallEtale.topology B S hS X.1).overPullback (Type u) U :=
  Functor.isoWhiskerRight (chartSetRestriction_overPullbackIso B S hS X U)
      (chartSliceSheafEquivOfCoefficients.{u} B S hS X U).inverse ≪≫
    Functor.isoWhiskerLeft ((SmallEtale.topology B S hS X.1).overPullback (Type u) U)
      (chartSliceSheafEquivOfCoefficients.{u} B S hS X U).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The comma categories indexing the left Kan extension along the slice projection of the
small étale site have colimits of sets in the universe of the sections of the structure sheaf:
they are essentially small there, because the small étale site is
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`) and hence so is its slice. -/
instance hasColimitsOfShape_costructuredArrow_overForget
    (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (Over.forget U).op W) (Type u) :=
  have : EssentiallySmall.{u} (CostructuredArrow (Over.forget U).op W) := inferInstance
  hasColimitsOfShape_of_essentiallySmall _ _

/-- Left Kan extensions of presheaves of sets valued in the universe of the sections exist along
the slice projection of the small étale site. -/
instance hasPointwiseLeftKanExtension_overForget (F : (Over U)ᵒᵖ ⥤ Type u) :
    (Over.forget U).op.HasPointwiseLeftKanExtension F :=
  fun _ => inferInstance

/-- **The slice pullback on the small étale site has a left adjoint**, the lower shriek `j_{U!}`
of [Stacks Project, Tag 00Y1]: the left Kan extensions computing it exist and the site admits
sheafification of `Type u`-valued presheaves. -/
theorem isRightAdjoint_overForget_sheafPushforwardContinuous :
    ((Over.forget U).sheafPushforwardContinuous (Type u)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.topology B S hS X.1)).IsRightAdjoint :=
  inferInstance

/-- **The two inverse images from the small étale topos of `X` agree.**  Restriction to the
chart, pushed through the identification of the two localized topoi, is the inverse image of the
localization morphism of Stacks 04IE.

Reading from the left: restriction to the chart is the slice pullback (Stacks 04M0 on sheaves),
the slice pullback followed by Stacks 00Y1 is `toOver` of the sheafification of `h_U`
(Stacks 04IQ), moving the base along `AlgebraicGeometry.Space.chartSheafifyIso` makes that
`toOver h_U`, and `toOver h_U` is the inverse image of the localization at `h_U`
(Stacks 04IE).  Both of the last two steps use Mathlib's cartesian monoidal structure on
sheaves of sets, so they compose directly. -/
noncomputable def chartLocalizationForwardInverseImageIso :
    smallEtaleSetRestriction B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U) ⋙
        (chartLocalizationToposEquivalence B S hS X U).functor ≅
      (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).toToposHom.inverseImage :=
  haveI := isRightAdjoint_overForget_sheafPushforwardContinuous B S hS X U
  Functor.isoWhiskerRight (chartSetRestrictionCompSliceInverseIso B S hS X U)
      (CategoryTheory.OverShriek.sheafFunctorToOver (U := U)
          (SmallEtale.topology B S hS X.1) ⋙
        Over.map (chartSheafifyIso B S hS X U).hom ⋙
        (RingedTopos.localizationEquivalence (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U)).inverse) ≪≫
    Functor.isoWhiskerRight
      (CategoryTheory.OverShriek.overPullbackCompSheafFunctorToOverIso
          (U := U) (SmallEtale.topology B S hS X.1))
      (Over.map (chartSheafifyIso B S hS X U).hom ⋙
        (RingedTopos.localizationEquivalence (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U)).inverse) ≪≫
    Functor.isoWhiskerRight
      (@CategoryTheory.toOverMapIso _ _ CartesianMonoidalCategory.fullSubcategory _ _
        (chartSheafifyIso B S hS X U))
      (RingedTopos.localizationEquivalence (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).inverse ≪≫
    Functor.isoWhiskerRight
      (RingedTopos.localizationInverseImageIso (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).symm
      (RingedTopos.localizationEquivalence (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).inverse ≪≫
    Functor.isoWhiskerLeft
      (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).toToposHom.inverseImage
      (RingedTopos.localizationEquivalence (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- **The canonical comparison of the two inverse images**: the inverse image of the
localization at `h_U`, read through the identification of the two localized topoi, is
restriction to the chart.  This is
`AlgebraicGeometry.Space.chartLocalizationForwardInverseImageIso` with the equivalence
cancelled against its inverse.

It is stated for `AlgebraicGeometry.Space.chartLocalizationToposHom'`;
`AlgebraicGeometry.Space.chartLocalizationInverseImageIso` is the comparison for
`AlgebraicGeometry.Space.chartLocalizationToposHom`, in the opposite orientation. -/
noncomputable def chartLocalizationInverseImageIso' :
    (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U)).toToposHom.inverseImage ⋙
        (chartLocalizationToposHom' B S hS X U).inverseImage ≅
      smallEtaleSetRestriction B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U) :=
  Functor.isoWhiskerRight (chartLocalizationForwardInverseImageIso B S hS X U).symm
      (chartLocalizationToposEquivalence B S hS X U).inverse ≪≫
    Functor.isoWhiskerLeft
      (smallEtaleSetRestriction B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U))
      (chartLocalizationToposEquivalence B S hS X U).unitIso.symm ≪≫
    Functor.rightUnitor _

/-! ### The identification of the two structure sheaves -/

/-- **The structure map of an étale morphism in its restriction presentation is an
isomorphism.**  Its inverse-image form is the identity on underlying sheaves of sets
(`AlgebraicGeometry.Space.forgetRing_map_smallEtaleRestriction_fSharpInverseImage`), and
`AlgebraicGeometry.RingedTopos.forgetRing` reflects isomorphisms. -/
instance isIso_smallEtaleRestriction_fSharpInverseImage {U' V' : AlgebraicSpaces B S hS}
    (h : U' ⟶ V') (hh : IsEtale B S hS h.hom) :
    IsIso (smallEtaleRestrictionRingedToposHom B S hS h hh).fSharpInverseImage := by
  suffices IsIso ((smallEtaleRingedTopos B S hS U').forgetRing.map
      (smallEtaleRestrictionRingedToposHom B S hS h hh).fSharpInverseImage) from
    isIso_of_reflects_iso _ (smallEtaleRingedTopos B S hS U').forgetRing
  rw [forgetRing_map_smallEtaleRestriction_fSharpInverseImage]
  exact IsIso.id _

/-- **The comparison of structure sheaves at a chart, in the restriction presentation**: the
inverse image of `𝒪_X` along the morphism of small étale ringed topoi of the structure morphism
of a chart is `𝒪_U`.

This is the structure map of that morphism itself, which is an isomorphism and is the identity
on underlying sheaves of sets. -/
noncomputable def chartRestrictionStructureSheafIso :
    (inverseImageCommRingFunctor
        (smallEtaleRestrictionToposHom B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U))).obj
        (smallEtaleRingedTopos B S hS X).O ≅
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).O :=
  asIso (smallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)).fSharpInverseImage

/-- The comparison of structure sheaves at a chart is the identity on underlying sheaves of
sets. -/
theorem forgetRing_map_chartRestrictionStructureSheafIso_hom :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartRestrictionStructureSheafIso B S hS X U).hom = 𝟙 _ :=
  forgetRing_map_smallEtaleRestriction_fSharpInverseImage B S hS
    (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)

/-- **The canonical comparison of the two inverse images, on sheaves of commutative rings.**
The unique lift of `AlgebraicGeometry.Space.chartLocalizationInverseImageIso'` to sheaves of
commutative rings, by `Stacks.Sheaves.ToposPushforward.pullbackCommRingSheafFunctorIsoOfNatIso`;
uniqueness is `Stacks.Sheaves.ToposPushforward.inverseImageCommRingIsoOfToposIso_existsUnique`. -/
noncomputable def chartLocalizationCommRingInverseImageIso :
    inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        ((RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
            (smallEtaleChartSheaf B S hS X U)).toToposHom.comp
          (chartLocalizationToposHom' B S hS X U)) ≅
      inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRestrictionToposHom B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)) :=
  -- instance search for these times out
  letI : PreservesFiniteProducts ((RingedTopos.localizationMorphism
      (smallEtaleRingedTopos B S hS X) (smallEtaleChartSheaf B S hS X U)).toToposHom.comp
        (chartLocalizationToposHom' B S hS X U)).inverseImage :=
    letI := ((RingedTopos.localizationMorphism
      (smallEtaleRingedTopos B S hS X) (smallEtaleChartSheaf B S hS X U)).toToposHom.comp
        (chartLocalizationToposHom' B S hS X U)).preservesFiniteLimits
    instPreservesFiniteProductsOfPreservesFiniteLimits _
  letI : PreservesFiniteProducts (smallEtaleRestrictionToposHom B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).inverseImage :=
    letI := (smallEtaleRestrictionToposHom B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).preservesFiniteLimits
    instPreservesFiniteProductsOfPreservesFiniteLimits _
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (chartLocalizationInverseImageIso' B S hS X U)

/-- **The canonical comparison of the two structure sheaves.**  Read through the identification
of the two localized topoi, the structure sheaf of the localization of the small étale ringed
topos of `X` at the sheaf represented by a chart `U` is the structure sheaf of the small étale
ringed topos of `U`.

Both are inverse images of `𝒪_X`: the first along the localization morphism of Stacks 04IE
followed by the identification, the second along the morphism of small étale ringed topoi of the
chart in its restriction presentation, and
`AlgebraicGeometry.Space.chartLocalizationCommRingInverseImageIso` identifies those two inverse
images.  The last step is `AlgebraicGeometry.Space.chartRestrictionStructureSheafIso`. -/
noncomputable def chartLocalizationStructureSheafIso :
    (inverseImageCommRingFunctor (chartLocalizationToposHom' B S hS X U)).obj
        ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X U)).O ≅
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).O :=
  (inverseImageCommRingFunctor (chartLocalizationToposHom' B S hS X U)).mapIso
      (RingedTopos.localizationInverseImageCommRingIso (smallEtaleRingedTopos B S hS X)
        (smallEtaleChartSheaf B S hS X U)).symm ≪≫
    ((MorphismOfTopoi.inverseImageCommRingCompIso
        (chartLocalizationToposHom' B S hS X U)
        (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
          (smallEtaleChartSheaf B S hS X U)).toToposHom).app
      (smallEtaleRingedTopos B S hS X).O).symm ≪≫
    (chartLocalizationCommRingInverseImageIso B S hS X U).app
      (smallEtaleRingedTopos B S hS X).O ≪≫
    chartRestrictionStructureSheafIso B S hS X U

/-! ### The identification as a morphism of ringed topoi, in both directions -/

/-- **The identification of the two localized topoi, as a morphism of ringed topoi from the
small étale ringed topos of the chart.**  Its structure map is the adjunct of the comparison of
structure sheaves. -/
noncomputable def chartLocalizationRingedToposHom :
    RingedToposHom (smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U)) where
  toToposHom := chartLocalizationToposHom' B S hS X U
  fSharp := (commRingImageAdjunction (chartLocalizationToposHom' B S hS X U)).homEquiv _ _
    (chartLocalizationStructureSheafIso B S hS X U).hom

/-- The structure map of the identification, in inverse-image form, is the comparison of
structure sheaves. -/
theorem chartLocalizationRingedToposHom_fSharpInverseImage :
    (chartLocalizationRingedToposHom B S hS X U).fSharpInverseImage =
      (chartLocalizationStructureSheafIso B S hS X U).hom :=
  ((commRingImageAdjunction (chartLocalizationToposHom' B S hS X U)).homEquiv _ _).symm_apply_apply
    _

/-- The structure map of the identification, in inverse-image form, is an isomorphism. -/
instance isIso_chartLocalizationRingedToposHom_fSharpInverseImage :
    IsIso (chartLocalizationRingedToposHom B S hS X U).fSharpInverseImage := by
  rw [chartLocalizationRingedToposHom_fSharpInverseImage]
  exact (chartLocalizationStructureSheafIso B S hS X U).isIso_hom

/-- **The identification is a morphism of locally ringed topoi.**  Its inverse-image structure
map is an isomorphism, so Stacks 04HA's square of units subsheaves has two invertible horizontal
arrows and is cartesian. -/
theorem isLocallyRinged_chartLocalizationRingedToposHom :
    (chartLocalizationRingedToposHom B S hS X U).IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage
    (chartLocalizationRingedToposHom B S hS X U)

/-- The direct image of the identification read from the localization is an equivalence: it is
the inverse of the equivalence of topoi. -/
instance isEquivalence_chartLocalizationToposInverse_pushforward :
    (chartLocalizationToposInverse B S hS X U).pushforward.IsEquivalence :=
  inferInstanceAs ((chartLocalizationToposEquivalence B S hS X U).inverse.IsEquivalence)

/-- **The identification of the two localized topoi, as a morphism of ringed topoi from the
localization.**

Its structure map is the *inverse* of the forward comparison of structure sheaves: the direct
image of this morphism of topoi is the inverse image of
`AlgebraicGeometry.Space.chartLocalizationToposHom'`, both being the inverse of the equivalence,
so `(E')_*𝒪_Loc` and `E⁻¹𝒪_Loc` are the same sheaf of commutative rings. -/
noncomputable def chartLocalizationRingedToposInverse :
    RingedToposHom
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos
        (smallEtaleChartSheaf B S hS X U))
      (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)) where
  toToposHom := chartLocalizationToposInverse B S hS X U
  fSharp := (chartLocalizationStructureSheafIso B S hS X U).inv

/-- The structure map of the identification read from the localization is an isomorphism. -/
instance isIso_chartLocalizationRingedToposInverse_fSharp :
    IsIso (chartLocalizationRingedToposInverse B S hS X U).fSharp :=
  (chartLocalizationStructureSheafIso B S hS X U).isIso_inv

/-- **The identification read from the localization is a morphism of locally ringed topoi.**  Its
direct image is an equivalence and its structure map is an isomorphism, so it is an isomorphism
of ringed topoi. -/
theorem isLocallyRinged_chartLocalizationRingedToposInverse :
    (chartLocalizationRingedToposInverse B S hS X U).IsLocallyRinged :=
  have : (chartLocalizationRingedToposInverse B S hS X U).toToposHom.pushforward.IsEquivalence :=
    isEquivalence_chartLocalizationToposInverse_pushforward B S hS X U
  RingedToposHom.isLocallyRinged_of_isEquivalence_of_isIso_fSharp
    (chartLocalizationRingedToposInverse B S hS X U)

end AlgebraicGeometry.Space

end
