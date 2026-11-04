module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationLift

/-!
# The small étale topos of an étale scheme chart as a localization

Let `X` be an algebraic space and `U ⟶ X` an étale morphism from a scheme, that is, an object of
the small étale site `X_étale`. By Stacks 04M1 the small étale ringed site of `U` is the
localization `(X_étale/U, 𝒪_X|_U)`, and by Stacks 0791 the topos of sheaves on `X_étale/U` is the
localization `Sh(X_étale)/h_U` of the small étale topos of `X` at the sheaf `h_U` represented by
`U`. This file records the resulting identification as a morphism of ringed topoi

```
  (Sh(U_étale), 𝒪_U) ⟶ (Sh(X_étale)/h_U, 𝒪_X|_{h_U}) ,
```

an equivalence of topoi whose composite with the localization morphism is the morphism of small
étale ringed topoi of `U ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.chartSheaf`: the sheaf `h_U` on `X_étale` represented by a chart `U`.
* `AlgebraicGeometry.Space.chartElementEquivalence`: the equivalence of sites
  `U_étale ≌ X_étale/h_U` composed of Stacks 04M0 and the Yoneda lemma.
* `AlgebraicGeometry.Space.chartLocalizationHom`: the identification of Stacks 04M1, as a morphism
  of ringed topoi from the small étale ringed topos of the chart to the localization of the small
  étale ringed topos of `X` at `h_U`.

## Main results

* `AlgebraicGeometry.Space.chartElementEquivalence_inducedTopology`: the equivalence of sites
  carries the topology of the localization back to the small étale topology of the chart.
* `AlgebraicGeometry.Space.chartLocalizationTwoIso`: the identification followed by the
  localization morphism is the morphism of small étale ringed topoi of `U ⟶ X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u' u

namespace CategoryTheory

/-- **The localization of a site at an object is its site of elements at the represented
presheaf.** Under the equivalence `Over T ≌ C/h_T` of the Yoneda lemma, the topology of Stacks
0791 on the site of elements of `h_T` is carried back to the localization `J.over T`. -/
theorem inducedTopology_yonedaCostructuredArrowOverEquiv_inverse {C : Type u'} [Category.{v} C]
    (J : GrothendieckTopology C) (T : C) :
    (yonedaCostructuredArrowOverEquiv T).inverse.inducedTopology
        ((CostructuredArrow.proj yoneda (yoneda.obj T)).restrictedTopology J) =
      J.over T := by
  ext Y S
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    CategoryTheory.Stacks.Topos.Localized.mem_restrictedTopology_iff,
    ← Sieve.functorPushforward_comp, GrothendieckTopology.mem_over_iff]
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

attribute [local instance] smallEtaleTopology_subcanonical

/-- The sheaf `h_U` on the small étale site of `X` represented by an étale scheme chart `U`. The
small étale topology is subcanonical, so the represented presheaf is a sheaf. -/
noncomputable abbrev chartSheaf (U : SmallEtale B S hS X.1) :
    (smallEtaleRingedTopos B S hS X).Topos :=
  (SmallEtale.topology B S hS X.1).yoneda.obj U

/-- **The site of an étale scheme chart is the site of elements of the sheaf it represents.** The
equivalence of Stacks 04M0 between the small étale site of a chart `U` and the slice `X_étale/U`,
followed by the Yoneda identification of the slice with the site of elements of `h_U`. -/
noncomputable def chartElementEquivalence (U : SmallEtale B S hS X.1) :
    SmallEtale B S hS (chartSpace B S hS X U).1 ≌
      RingedTopos.elementSite (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U) :=
  (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).trans
    (yonedaCostructuredArrowOverEquiv U).symm

/-- The equivalence of sites followed by the projection of the site of elements is
postcomposition with the structure morphism of the chart. -/
theorem chartElementEquivalence_functor_comp_proj (U : SmallEtale B S hS X.1) :
    (chartElementEquivalence B S hS X U).functor ⋙
        RingedTopos.elementProjection (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U) =
      smallEtalePostcomp B S hS (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U) :=
  rfl

/-- **The topology clause of Stacks 04M1 at the site of elements.** The small étale topology of a
chart `U` is induced, along the equivalence of sites with the site of elements of `h_U`, from the
topology of Stacks 0791 there. -/
theorem chartElementEquivalence_inducedTopology (U : SmallEtale B S hS X.1) :
    (chartElementEquivalence B S hS X U).functor.inducedTopology
        (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U)) =
      SmallEtale.topology B S hS (chartSpace B S hS X U).1 := by
  refine Eq.trans ?_ (SmallEtale.chartLocalization_inducedTopology B S hS X.1 U)
  ext A R
  have h1 := Functor.mem_inducedTopology_iff_of_isCoverDense
    (G := (chartElementEquivalence B S hS X U).functor)
    (K := RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U)) R
  have h2 := Functor.mem_inducedTopology_iff_of_isCoverDense
    (G := SmallEtale.chartLocalization B S hS X.1 U)
    (K := (SmallEtale.topology B S hS X.1).over U) R
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [← inducedTopology_yonedaCostructuredArrowOverEquiv_inverse,
    Functor.mem_inducedTopology_iff_of_isCoverDense]
  exact Iff.of_eq (congrArg (· ∈ _) (Sieve.functorPushforward_comp
    (SmallEtale.chartLocalization B S hS X.1 U) (yonedaCostructuredArrowOverEquiv U).inverse R))

/-- The equivalence of sites of a chart with the site of elements is a dense subsite inclusion. -/
instance isDenseSubsite_chartElementEquivalence (U : SmallEtale B S hS X.1) :
    (chartElementEquivalence B S hS X U).functor.IsDenseSubsite
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U)) := by
  rw [← chartElementEquivalence_inducedTopology]
  infer_instance

/-- The equivalence of sites of a chart with the site of elements is a continuous functor. -/
instance isContinuous_chartElementEquivalence (U : SmallEtale B S hS X.1) :
    (chartElementEquivalence B S hS X U).functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U)) :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartElementEquivalence B S hS X U)

/-- The equivalence of sites of a chart with the site of elements is a cocontinuous functor. -/
instance isCocontinuous_chartElementEquivalence (U : SmallEtale B S hS X.1) :
    (chartElementEquivalence B S hS X U).functor.IsCocontinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U)) :=
  @Functor.IsDenseSubsite.instIsCocontinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartElementEquivalence B S hS X U)

attribute [local instance] RingedTopos.hasPointwiseRightKanExtension_of_essentiallySmall

/-- The morphism of topoi underlying the identification of Stacks 04M1: its inverse image is
restriction along the equivalence of sites `U_étale ≌ X_étale/h_U`. -/
noncomputable def chartLocalizationToposHom (U : SmallEtale B S hS X.1) :
    MorphismOfTopoi (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).Topos
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos (chartSheaf B S hS X U)).Topos where
  inverseImage := (chartElementEquivalence B S hS X U).functor.sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
  pushforward := (chartElementEquivalence B S hS X U).functor.sheafPushforwardCocontinuous (Type u)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
  adj := (chartElementEquivalence B S hS X U).functor.sheafAdjunctionCocontinuous (Type u)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
  preservesFiniteLimits :=
    CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ (Type u)

/-- **The identification of Stacks 04M1**, as a morphism of ringed topoi from the small étale
ringed topos of an étale scheme chart `U` of `X` to the localization of the small étale ringed
topos of `X` at the sheaf `h_U`. Its inverse image is restriction along the equivalence of sites
of Stacks 04M0 composed with the Yoneda lemma, and its structure map is the identification of the
restricted structure sheaf with `𝒪_U`, both being the global regular functions of the same
schemes. -/
noncomputable def chartLocalizationHom (U : SmallEtale B S hS X.1) :
    RingedToposHom (smallEtaleRingedTopos B S hS (chartSpace B S hS X U))
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos (chartSheaf B S hS X U)) where
  toToposHom := chartLocalizationToposHom B S hS X U
  fSharp := (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (chartLocalizationToposHom B S hS X U)).homEquiv _ _
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso.{u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
      (chartElementEquivalence B S hS X U).functor
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos (chartSheaf B S hS X U)).O).hom

/-- The structure map of the identification of Stacks 04M1 is the identity on underlying sheaves
of sets. -/
theorem forgetRing_chartLocalizationHom_fSharpInverseImage (U : SmallEtale B S hS X.1) :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationHom B S hS X U).fSharpInverseImage = 𝟙 _ :=
  (congrArg (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
    (Equiv.symm_apply_apply _ _)).trans
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
      (chartElementEquivalence B S hS X U).functor
      ((smallEtaleRingedTopos B S hS X).localizedRingedTopos (chartSheaf B S hS X U)).O)

/-- The structure map of the identification of Stacks 04M1 is the identity of the restriction of
the underlying sheaf of sets of `𝒪_X` along postcomposition with `U ⟶ X`. -/
theorem forgetRing_chartLocalizationHom_fSharpInverseImage' (U : SmallEtale B S hS X.1) :
    (smallEtaleRingedTopos B S hS (chartSpace B S hS X U)).forgetRing.map
        (chartLocalizationHom B S hS X U).fSharpInverseImage =
      𝟙 ((smallEtaleSetRestriction B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj (structureSetSheaf B S hS X)) :=
  forgetRing_chartLocalizationHom_fSharpInverseImage B S hS X U

/-- The inverse image of the identification of Stacks 04M1 followed by the localization at `h_U`
is the inverse image of the morphism of small étale topoi of the structure morphism of the chart:
both are restriction along postcomposition with that étale morphism (Stacks 03LQ). -/
noncomputable def chartLocalizationInverseImageIso (U : SmallEtale B S hS X.1) :
    (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X U)).toToposHom.inverseImage ≅
      ((smallEtaleRingedTopos B S hS X).localizationMorphism
          (chartSheaf B S hS X U)).toToposHom.inverseImage ⋙
        (chartLocalizationHom B S hS X U).toToposHom.inverseImage :=
  smallToposMorphismTypeU_inverseImageIso B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)

/-- **The identification of Stacks 04M1 lies over `X`.** Followed by the localization morphism of
the small étale ringed topos of `X` at `h_U`, the identification of the small étale ringed topos of
an étale scheme chart `U` with that localization is the morphism of small étale ringed topoi of
the structure morphism `U ⟶ X`. -/
noncomputable def chartLocalizationTwoIso (U : SmallEtale B S hS X.1) :=
  RingedTopos.compLocalizationMorphismTwoIsoOfInverseImageIso (chartLocalizationHom B S hS X U)
    (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X U))
    (chartLocalizationInverseImageIso B S hS X U)
    ((congrArg ((chartLocalizationInverseImageIso B S hS X U).hom.app _ ≫ ·)
      (forgetRing_chartLocalizationHom_fSharpInverseImage' B S hS X U)).trans
      ((Category.comp_id _).trans (forgetRing_fSharpInverseImage_eq_inverseImageIso B S hS
        (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)).symm))

/-- Sheaves on the site of elements of `h_U` are sheaves on the small étale site of the chart `U`:
`CategoryTheory.Equivalence.sheafCongr` at the equivalence of sites of
`AlgebraicGeometry.Space.chartElementEquivalence`. Its functor is restriction along that
equivalence, which is the inverse image of `AlgebraicGeometry.Space.chartLocalizationHom`. -/
noncomputable def chartLocalizationSheafEquiv (U : SmallEtale B S hS X.1) :
    Sheaf (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
        (Type u) ≌
      Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (Type u) :=
  haveI : (chartElementEquivalence B S hS X U).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U)) :=
    isDenseSubsite_chartElementEquivalence B S hS X U
  Equivalence.sheafCongr
    (RingedTopos.elementTopology (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U))
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (chartElementEquivalence B S hS X U).symm (Type u)

/-- The functor of `AlgebraicGeometry.Space.chartLocalizationSheafEquiv` is the inverse image of
the identification of Stacks 04M1. -/
theorem chartLocalizationSheafEquiv_functor (U : SmallEtale B S hS X.1) :
    (chartLocalizationSheafEquiv B S hS X U).functor =
      (chartLocalizationHom B S hS X U).toToposHom.inverseImage :=
  rfl

/-- **The identification of Stacks 04M1 is an equivalence of topoi**: its inverse image is an
equivalence of categories. -/
instance isEquivalence_chartLocalizationHom_inverseImage (U : SmallEtale B S hS X.1) :
    (chartLocalizationHom B S hS X U).toToposHom.inverseImage.IsEquivalence :=
  (chartLocalizationSheafEquiv B S hS X U).isEquivalence_functor

/-- The inverse image of the identification of Stacks 04M1 is fully faithful. -/
noncomputable def chartLocalizationHom_fullyFaithful (U : SmallEtale B S hS X.1) :
    (chartLocalizationHom B S hS X U).toToposHom.inverseImage.FullyFaithful :=
  (chartLocalizationSheafEquiv B S hS X U).fullyFaithfulFunctor

end AlgebraicGeometry.Space

end
