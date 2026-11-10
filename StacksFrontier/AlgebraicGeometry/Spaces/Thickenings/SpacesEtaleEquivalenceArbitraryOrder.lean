module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEquivalence

/-!
# The étale site of a thickening of algebraic spaces, at arbitrary order (Stacks 05ZS)

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, of arbitrary order. Base
change along the inclusion, `V' ↦ G ×_X V'`, is an *equivalence of categories* from the small
étale site of the ambient space `X` to the small étale site of the closed subspace `G` — the
sites of Stacks 03ED, whose objects are the schemes étale over the two spaces. That is
**Stacks 05ZS**, proved here with nothing granted. The first-order forms are in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalence.lean`.

In the notation of the source, `G` is `X` and `X` is `X'`, so the functor is the one the source
writes `V' ↦ V = X ×_{X'} V'` and it runs `X'_étale → X_étale`.

## Main results

* `AlgebraicGeometry.Space.isThickening_range_inclusion`: the range of the inclusion of a
  thickening is a thickening.
* `AlgebraicGeometry.Space.fullyFaithfulThickeningChartBaseChangeOfIsThickening`: base change of
  étale scheme charts along the inclusion is fully faithful, at arbitrary order, proved
  directly on the charts.
* `AlgebraicGeometry.Space.essSurj_thickeningChartBaseChange_of_isThickening`: it is essentially
  surjective, at arbitrary order.
* `AlgebraicGeometry.Space.isEquivalence_thickeningChartBaseChange_of_isThickening`:
  **Stacks 05ZS**, and `AlgebraicGeometry.Space.smallEtaleEquivalenceOfIsThickening`, the same
  packaged as a `CategoryTheory.Equivalence`.

## Implementation notes

The source's proof cites Theorem 05ZH for the equivalence of spaces-étale sites and Lemma 05ZR
for the fact that `V'` is a scheme exactly when `G ×_X V'` is. Here the two halves of the
equivalence on scheme charts are proved separately.

*Full faithfulness* at arbitrary order is proved on the charts themselves: a morphism of charts
`V' ⟶ W'` is a section of the étale projection `V' ×_X W' ⟶ V'`, and a section over the closed
subscheme `G ×_X V'`, which has the same points as `V'`, extends to one over `V'` by
`Stacks.Etale.exists_lift_of_surjective_closedImmersion`. No bound on the order enters. At
first order the same conclusion also follows from the spaces-étale equivalence through the
Stacks 03G1 comparison, `AlgebraicGeometry.Space.smallBaseChange_comparison`.

*Essential surjectivity* follows the source's route. The comparison functor of Stacks 03G1
carries a chart `V` of `G` to an algebraic space étale over `G`; base change on the spaces-étale
sites is essentially surjective at arbitrary order,
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`, so that space is `G ×_X C`
for an object `C` of the spaces-étale site of `X`. The cartesian projection `G ×_X C ⟶ C` is a
closed immersion bijective on points with representable source, so `C` is a scheme by the
closed-immersion form of Stacks 07VV,
`AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`, which is the
content of Stacks 05ZR used by the source; it rests on the thickening case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`. Both are proved
with no hypotheses.

## What is not covered

Nothing of the source's statement is left out: the full statement is
`AlgebraicGeometry.Space.isEquivalence_thickeningChartBaseChange_of_isThickening`. The two
registrations of the tag in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEquivalence` are restricted forms.
The equivalence
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening` is on the
spaces-étale sites of Stacks 03G0 rather than on the small étale sites of Stacks 03ED, and
needs a first-order thickening because the library's Stacks 05ZH full faithfulness,
`AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening`, is stated
only at first order. The full faithfulness
`AlgebraicGeometry.Space.fullyFaithfulThickeningChartBaseChangeOfIsFirstOrderThickening` is
one half of the equivalence and inherits the same first-order restriction.

## References

* [Stacks Project, Tag 025H](https://stacks.math.columbia.edu/tag/025H)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-! ### The inclusion of a thickening -/

/-- The range of the inclusion of a thickening `G ⊂ X` is `G` itself, so `G ⊂ X` being a
thickening is the same as the range of the inclusion being one.

This is the hypothesis shape in which essential surjectivity of base change on the
spaces-étale sites at a thickening of arbitrary order,
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`, is stated. -/
theorem isThickening_range_inclusion (hG : IsThickening B S hS X G) :
    IsThickening B S hS X
      (Subfunctor.range (IsThickening.inclusion B S hS hG).hom) :=
  (Subfunctor.range_ι G).symm ▸ hG

/-! ### Full faithfulness on the small étale sites of scheme charts, at arbitrary order -/

/-- **A morphism of base-changed étale scheme charts descends to a morphism of charts.** This
is the content of fullness, stated for the underlying morphism `cl` of the chosen fibre
products and with the relative representability data of the inclusion of the thickening and of
the target chart taken as parameters, so that the proof reasons about them as opaque fibre
products.

A morphism `V ⟶ W` of charts is the same datum as a section of the projection `V ×_X W ⟶ V`,
which is étale because `W` is an étale chart. The datum `cl` supplies such a section over
`G ×_X V`, a closed subscheme of `V` with the same points, and
`Stacks.Etale.exists_lift_of_surjective_closedImmersion` extends it to a section over `V`. The
extended section is a morphism of schemes; it commutes with the structure morphisms to `S`
because it is a section, so it is a morphism of the site by
`AlgebraicGeometry.BigFppfOver.homOfCompEq`. No hypothesis on the order of the thickening
enters: the extension asks only for a closed immersion which is surjective on points. -/
private theorem exists_chartHom_left_eq (hG : IsThickening B S hS X G)
    (hι : yoneda.relativelyRepresentable (IsThickening.inclusion B S hS hG).hom)
    {V W : SmallEtale B S hS X.1} (hW : yoneda.relativelyRepresentable W.1.hom)
    (hWet : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (hW.snd V.1.hom)))
    (hci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hι.snd V.1.hom)))
    (hsj : Function.Surjective ((BigFppfOver.toScheme B S hS).map (hι.snd V.1.hom)).base)
    (cl : hι.pullback V.1.hom ⟶ hι.pullback W.1.hom)
    (hcw : yoneda.map cl ≫ hι.fst W.1.hom = hι.fst V.1.hom) :
    ∃ k : V ⟶ W, hι.snd V.1.hom ≫ k.hom.left = cl ≫ hι.snd W.1.hom := by
  have := hWet
  have := hci
  have hcond : yoneda.map (cl ≫ hι.snd W.1.hom) ≫ W.1.hom =
      yoneda.map (hι.snd V.1.hom) ≫ V.1.hom := by
    rw [yoneda.map_comp, Category.assoc, ← hι.w W.1.hom, ← Category.assoc, hcw, hι.w V.1.hom]
  obtain ⟨f, hfp, hfj⟩ := Stacks.Etale.exists_lift_of_surjective_closedImmersion
    ((BigFppfOver.toScheme B S hS).map (hW.snd V.1.hom))
    (𝟙 ((BigFppfOver.toScheme B S hS).obj V.1.left))
    ((BigFppfOver.toScheme B S hS).map (hι.snd V.1.hom)) hsj
    ((BigFppfOver.toScheme B S hS).map
      (hW.lift (yoneda.map (cl ≫ hι.snd W.1.hom)) (hι.snd V.1.hom) hcond))
    (by rw [Category.comp_id, ← (BigFppfOver.toScheme B S hS).map_comp, hW.lift_snd])
  have hQ : (BigFppfOver.toScheme B S hS).map (hW.snd V.1.hom) ≫
      B.inclusion.map (V.1.left).hom = B.inclusion.map (hW.pullback V.1.hom).hom := by
    change B.inclusion.map (hW.snd V.1.hom).left ≫ B.inclusion.map (V.1.left).hom = _
    rw [← B.inclusion.map_comp, Over.w]
  have hcomp : f ≫ B.inclusion.map (hW.pullback V.1.hom).hom =
      B.inclusion.map (V.1.left).hom := by
    rw [← hQ, ← Category.assoc, hfp, Category.id_comp]
  have hfbmap : (BigFppfOver.toScheme B S hS).map
      (BigFppfOver.homOfCompEq B S hS f hcomp) = f :=
    BigFppfOver.toScheme_map_homOfCompEq B S hS f hcomp
  have hfbsnd : BigFppfOver.homOfCompEq B S hS f hcomp ≫ hW.snd V.1.hom = 𝟙 V.1.left :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [(BigFppfOver.toScheme B S hS).map_comp, hfbmap, hfp,
        (BigFppfOver.toScheme B S hS).map_id])
  have hfbj : hι.snd V.1.hom ≫ BigFppfOver.homOfCompEq B S hS f hcomp =
      hW.lift (yoneda.map (cl ≫ hι.snd W.1.hom)) (hι.snd V.1.hom) hcond :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [(BigFppfOver.toScheme B S hS).map_comp, hfbmap, hfj])
  have hchart : yoneda.map (BigFppfOver.homOfCompEq B S hS f hcomp ≫
        yoneda.preimage (hW.fst V.1.hom)) ≫ W.1.hom = V.1.hom := by
    rw [yoneda.map_comp, yoneda.map_preimage, Category.assoc, hW.w V.1.hom, ← Category.assoc,
      ← yoneda.map_comp, hfbsnd, yoneda.map_id, Category.id_comp]
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk _ hchart), ?_⟩
  refine yoneda.map_injective ?_
  change yoneda.map (hι.snd V.1.hom ≫ BigFppfOver.homOfCompEq B S hS f hcomp ≫
      yoneda.preimage (hW.fst V.1.hom)) = yoneda.map (cl ≫ hι.snd W.1.hom)
  rw [← Category.assoc, hfbj, yoneda.map_comp, yoneda.map_preimage, hW.lift_fst]

/-- **Base change of étale scheme charts along the inclusion of a thickening is full**, at a
thickening of arbitrary order and with nothing granted.

This is `AlgebraicGeometry.Space.exists_chartHom_left_eq`, whose three geometric inputs at the
chart `V` are the étaleness of the projection of the chosen fibre product `V ×_X W`, and that
the projection of the thickening at `V` is a closed immersion
(`AlgebraicGeometry.Space.isClosedImmersion_inclusion_of_isThickening`) which is surjective
(`AlgebraicGeometry.Space.surjective_projection_of_isThickening`). -/
theorem thickeningChartBaseChange_full (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).Full where
  map_surjective {V W} c := by
    obtain ⟨k, hk⟩ := exists_chartHom_left_eq B S hS hG
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep W.property.rep
      (W.property.property_snd V.1.hom)
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG).property_snd V.1.hom)
      (surjective_projection_of_isThickening B S hS hG V).surj c.hom.left
      (CostructuredArrow.w c.hom)
    refine ⟨k, ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)⟩
    refine (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.hom_ext ?_ ?_
    · exact ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.lift_fst _ _ _).trans
        (CostructuredArrow.w c.hom).symm
    · exact (smallBaseChange_map_snd B S hS (IsThickening.inclusion B S hS hG)
        (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep k).trans hk

/-- **Stacks 05ZS, full faithfulness of the functor `X'_étale → X_étale`, at a thickening of
arbitrary order.** Let `G ⊂ X` be a thickening of algebraic spaces over `S`, of arbitrary
order. Base change of étale *scheme* charts along the inclusion,
`AlgebraicGeometry.Space.thickeningChartBaseChange`, is fully faithful.

This is on the source's own site: the objects are the schemes étale over the two spaces.
Faithfulness is `AlgebraicGeometry.Space.thickeningChartBaseChange_faithful` and fullness is
`AlgebraicGeometry.Space.thickeningChartBaseChange_full`; neither restricts the order of the
thickening and neither grants anything. The other half of the source's assertion is
`AlgebraicGeometry.Space.essSurj_thickeningChartBaseChange_of_isThickening`; the two together
are `AlgebraicGeometry.Space.isEquivalence_thickeningChartBaseChange_of_isThickening`. -/
noncomputable def fullyFaithfulThickeningChartBaseChangeOfIsThickening
    (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).FullyFaithful :=
  letI := thickeningChartBaseChange_full B S hS hG
  letI := thickeningChartBaseChange_faithful B S hS hG
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### Essential surjectivity on the small étale sites of scheme charts -/

/-- **Base change of étale scheme charts along the inclusion of a thickening is essentially
surjective**, at a thickening `G ⊂ X` of arbitrary order: every
scheme étale over `G` is `G ×_X V'` for some scheme `V'` étale over `X`.

The route is the source's own, and the spaces-étale half of it needs nothing. The comparison
functor of Stacks 03G1 carries the given chart `V` to an algebraic space étale over `G`, and
base change on the spaces-étale sites is essentially surjective at a thickening of arbitrary
order with nothing granted, by
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`, so that algebraic space is
`G ×_X C` for an object `C` of the spaces-étale site of `X`. What is left is the source's
appeal to Stacks 05ZR: `C` has to be a *scheme*. Its cartesian projection `G ×_X C ⟶ C` is a
closed immersion surjective on points, and its source is the comparison image of `V`, hence
representable; so `C` is representable by
`AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`, which is proved
with no hypotheses. Representability is exactly membership in the essential image of the comparison
functor, by `AlgebraicGeometry.Space.essImage_comparisonFunctor_iff`, so `C` is the comparison
image of a chart `U`, and the comparison isomorphism
`AlgebraicGeometry.Space.smallBaseChange_comparison` identifies the comparison image of
`G ×_X U` with `G ×_X C`; the comparison functor of `G` is fully faithful, so that isomorphism
descends to `G ×_X U ≅ V`.

Nothing here bounds the order of the thickening, and nothing is granted: the affineness step
inside the proof of Stacks 05ZR is the thickening case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`, which is proved
with no hypotheses. -/
theorem essSurj_thickeningChartBaseChange_of_isThickening (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).EssSurj := by
  let := mono_hom_inclusion B S hS hG
  let := essSurj_spacesBaseChange_of_isThickening B S hS hG
  let := comparisonFunctor_full B S hS (IsThickening.space B S hS hG)
  let := comparisonFunctor_faithful B S hS (IsThickening.space B S hS hG)
  refine ⟨fun V => ?_⟩
  set W := (comparisonFunctor B S hS (IsThickening.space B S hS hG)).obj V with hWdef
  set Cv := (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor with hCvdef
  -- The spaces-étale lift of the comparison image of `V`.
  set C := Cv.objPreimage W with hCdef
  have e : Cv.obj C ≅ W := Cv.objObjPreimageIso W
  -- Its cartesian projection has representable source, being the comparison image of `V`.
  let : W.1.left.1.IsRepresentable :=
    (essImage_comparisonFunctor_iff B S hS (IsThickening.space B S hS hG) W).1
      ⟨V, ⟨Iso.refl _⟩⟩
  have erep : (Cv.obj C).1.left.1 ≅ W.1.left.1 :=
    (SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG) ⋙
      ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)).mapIso e
  -- So the lift is representable, by Stacks 05ZR at that projection.
  have hCrep : C.1.left.1.IsRepresentable :=
    isRepresentable_of_isClosedImmersion_of_bijective B S hS
      (Cv.obj C).1.left.property C.1.left.property
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app C).hom
      (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG C)
      (bijective_pointsMap_spacesBaseChange_projection_of_isThickening B S hS hG C)
      (isRepresentable_of_natIso _ erep.symm)
  obtain ⟨U, ⟨eU⟩⟩ := (essImage_comparisonFunctor_iff B S hS X C).2 hCrep
  refine ⟨U, ⟨(comparisonFunctor B S hS (IsThickening.space B S hS hG)).preimageIso ?_⟩⟩
  exact (smallBaseChange_comparison B S hS (IsThickening.inclusion B S hS hG)
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep).app U ≪≫
    Cv.mapIso eU ≪≫ e

/-! ### The equivalence of the small étale sites of scheme charts -/

/-- The two constructions of base change of étale scheme charts along the inclusion of a
thickening `G ⊂ X` agree.

`AlgebraicGeometry.Space.thickeningChartBaseChange` is the Stacks 03G2 part (4) base change of
charts, built from the relative representability of the inclusion, while
`AlgebraicGeometry.Space.smallEtalePullback` is the restriction of spaces-étale base change to
the charts, built from the Stacks 03G1 comparison. Each is characterised by its comparison
isomorphism with spaces-étale base change —
`AlgebraicGeometry.Space.smallBaseChange_comparison` and
`AlgebraicGeometry.Space.smallEtalePullbackComparisonIso` — so composing one with the inverse
of the other identifies the two functors after the comparison functor of the closed subspace,
and that comparison functor is fully faithful. -/
noncomputable def thickeningChartBaseChangeIsoSmallEtalePullback
    (hG : IsThickening B S hS X G) :
    thickeningChartBaseChange B S hS hG ≅
      smallEtalePullback B S hS (IsThickening.inclusion B S hS hG)
        (isIntegralHom_ι_of_isThickening B S hS hG) :=
  letI := comparisonFunctor_full B S hS (IsThickening.space B S hS hG)
  letI := comparisonFunctor_faithful B S hS (IsThickening.space B S hS hG)
  Functor.fullyFaithfulCancelRight
    (comparisonFunctor B S hS (IsThickening.space B S hS hG))
    (smallBaseChange_comparison B S hS (IsThickening.inclusion B S hS hG)
        (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep ≪≫
      (smallEtalePullbackComparisonIso B S hS (IsThickening.inclusion B S hS hG)
        (isIntegralHom_ι_of_isThickening B S hS hG)).symm)

/-- **Stacks 05ZS.** Let `S` be a scheme and let `G ⊂ X` be a thickening of algebraic spaces
over `S`, of arbitrary order. Base change of étale *scheme* charts along the inclusion,
`V' ↦ G ×_X V'`, is an equivalence of categories from the small étale site of `X` to the small
étale site of `G`.

In the notation of the source, `G` is `X` and `X` is `X'`: the functor is `V' ↦ V = X ×_{X'} V'`
and the equivalence runs `X'_étale → X_étale`, on the sites of Stacks 03ED whose objects are the
schemes étale over the two spaces, which are the sites the source's statement is about. The
cartesian square identifying the value of the functor at a chart with the fibre product is
`AlgebraicGeometry.Space.smallBaseChange_isPullback`.

Full faithfulness is `AlgebraicGeometry.Space.thickeningChartBaseChange_full` and
`AlgebraicGeometry.Space.thickeningChartBaseChange_faithful`; essential surjectivity is
`AlgebraicGeometry.Space.essSurj_thickeningChartBaseChange_of_isThickening`, which uses the
source's Lemma 05ZR in its closed-immersion form. Nothing is granted and neither half bounds the
order of the thickening. -/
@[stacks 05ZS "the functor is `AlgebraicGeometry.Space.thickeningChartBaseChange`, base change \
`V' ↦ X ×_{X'} V'` of schemes étale over `X'` along the inclusion of the thickening, between \
the small étale sites of Stacks 03ED; the packaged `CategoryTheory.Equivalence` is \
`AlgebraicGeometry.Space.smallEtaleEquivalenceOfIsThickening`"]
theorem isEquivalence_thickeningChartBaseChange_of_isThickening
    (hG : IsThickening B S hS X G) :
    (thickeningChartBaseChange B S hS hG).IsEquivalence where
  faithful := thickeningChartBaseChange_faithful B S hS hG
  full := thickeningChartBaseChange_full B S hS hG
  essSurj := essSurj_thickeningChartBaseChange_of_isThickening B S hS hG

/-- **Stacks 05ZS, as an equivalence of categories.** The equivalence of
`AlgebraicGeometry.Space.isEquivalence_thickeningChartBaseChange_of_isThickening`, packaged as
a `CategoryTheory.Equivalence` from the small étale site of `X` to that of `G`.

Its functor is `AlgebraicGeometry.Space.thickeningChartBaseChange`, by
`AlgebraicGeometry.Space.smallEtaleEquivalenceOfIsThickening_functor`.

The registration of Stacks 05ZS is on
`AlgebraicGeometry.Space.isEquivalence_thickeningChartBaseChange_of_isThickening`, of which this
is the packaged form. -/
noncomputable def smallEtaleEquivalenceOfIsThickening (hG : IsThickening B S hS X G) :
    SmallEtale B S hS X.1 ≌ SmallEtale B S hS (IsThickening.space B S hS hG).1 :=
  letI := isEquivalence_thickeningChartBaseChange_of_isThickening B S hS hG
  (thickeningChartBaseChange B S hS hG).asEquivalence

/-- The functor of `AlgebraicGeometry.Space.smallEtaleEquivalenceOfIsThickening` is base change
of étale scheme charts along the inclusion of the thickening. -/
theorem smallEtaleEquivalenceOfIsThickening_functor (hG : IsThickening B S hS X G) :
    (smallEtaleEquivalenceOfIsThickening B S hS hG).functor =
      thickeningChartBaseChange B S hS hG :=
  rfl

end AlgebraicGeometry.Space

end
