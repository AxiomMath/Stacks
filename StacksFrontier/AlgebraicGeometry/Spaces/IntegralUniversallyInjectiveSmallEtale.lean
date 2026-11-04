module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveChartLocalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardFullyFaithful

/-!
# The small étale direct image along an integral universally injective morphism

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. This file proves that the small étale direct image along `f` is fully faithful, on
sheaves of sets and on sheaves of abelian groups, and that the inverse image is a left inverse
of it. These are the full-faithfulness assertions of Stacks 0AEH together with its trailing
clause.

Everything comes from the two site-theoretic properties of chart base change proved in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveChartCoverDensity.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveChartLocalFullness.lean`:
base change along `f` of étale scheme charts of `X` is cover dense and locally full for the
small étale topology of `Y`. Restriction along a cover-dense, locally full, continuous functor
is fully faithful whatever the coefficients are, and the counit of an adjunction is invertible
exactly when the right adjoint is fully faithful.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_of_isIntegralHom`: an integral morphism of
  algebraic spaces is relatively representable, so that chart base change and the direct image
  exist.
* `fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective`, in the namespace
  `AlgebraicGeometry.Space`: restriction along chart base change is fully faithful on sheaves
  with values in *any* category. All the full-faithfulness assertions below are instances of
  it.
* `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleSetPushforwardOfIntegralUniversallyInjective`
  and
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIntegralUniversallyInjective`
  are **Stacks 0AEH, part (1)**: the direct image of sheaves of sets is fully faithful, at an
  arbitrary coefficient universe and for the morphism of small étale topoi of Stacks 03G2,
  part (3) respectively.
* `AlgebraicGeometry.Space.smallEtaleAdjunctionCounitIsIsoOfIntegralUniversallyInjective` and
  `smallEtalePullbackPushforwardCounitIsoOfIntegralUniversallyInjective` are the trailing clause
  of Stacks 0AEH for sheaves of sets: the inverse image is a left inverse of the direct image.
* `fullyFaithfulSmallEtaleAbelianPushforwardOfIntegralUniversallyInjective` and
  `smallEtalePushforwardAbIsRightAdjointOfIntegralUniversallyInjective` are **Stacks 0AEH,
  part (2)**: the direct image of abelian sheaves is fully faithful and has the inverse image as
  a left adjoint.
* `smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective` and
  `smallEtaleAbelianPullbackPushforwardCounitIsoOfIntegralUniversallyInjective` are the trailing
  clause of Stacks 0AEH for abelian sheaves.

## The essential images

The two essential-image descriptions of Stacks 0AEH are not proved here, and are not
consequences of the two site conditions used here: cover density and local fullness give full
faithfulness and say nothing about which sheaves are hit. The one for sheaves of sets is
`AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_of_integral_universallyInjective`,
in `StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveSetEssentialImage.lean`:
a sheaf of sets on `X_étale` is a direct image along `f` exactly when its restriction to the
open complement of `f(|Y|)` is the singleton sheaf. The abelian one is
`AlgebraicGeometry.Space.smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective`,
in `StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveEssentialImage.lean`: an
abelian sheaf on `X_étale` is a direct image along `f` exactly when its support is contained in
`f(|Y|)`. Its two inclusions are
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_essImage_of_isIntegralHom`, which holds for
every integral morphism, and
`AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset_of_isIntegralHom`, which lifts
a geometric point of `X` lying over `f(|Y|)` to a geometric point of `Y` and then compares
stalks. In both cases the full faithfulness proved here is what turns the resulting
invertibility of the unit into membership of the essential image.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **An integral morphism of algebraic spaces is relatively representable.** This is the
implication from condition (1) to condition (2) of Stacks 03ZQ. -/
theorem relativelyRepresentable_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) : yoneda.relativelyRepresentable f.hom :=
  ((isIntegralHom_iff_representable B S hS f.hom Y.property X.property).mp hf).1

/-- **Full faithfulness of restriction along chart base change for an integral universally
injective morphism**, with coefficients in an arbitrary category. For such a morphism
`f : Y ⟶ X` of algebraic spaces over `S`, restriction along the base-change functor on étale
scheme charts is fully faithful on `A`-valued sheaves.

The two inputs are cover density
(`AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isIntegralHom_of_universallyInjective`)
and local fullness
(`smallBaseChange_isLocallyFull_of_isIntegralHom_of_universallyInjective`) of chart base change,
and neither depends on the coefficients. -/
def fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective (A : Type w)
    [Category.{v} A] (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    ((smallBaseChange B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).FullyFaithful :=
  fullyFaithfulSmallEtaleRestriction B S hS A f
    (relativelyRepresentable_of_isIntegralHom B S hS f hf)
    (smallBaseChange_isCoverDense_of_isIntegralHom_of_universallyInjective B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf) hf hui)
    (smallBaseChange_isLocallyFull_of_isIntegralHom_of_universallyInjective B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf) hf hui)

/-! ### Sheaves of sets -/

/-- **Stacks 0AEH, part (1), full faithfulness.** For an integral and universally injective
morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`, the direct image of sheaves of sets
along `f` — restriction along the chart base-change morphism of small étale sites of
Stacks 03G2, part (4) — is fully faithful, at any coefficient universe. -/
@[stacks 0AEH "part (1): full faithfulness of the direct image on sheaves of sets"]
def fullyFaithfulSmallEtaleSetPushforwardOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    ((smallBaseChange B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafPushforwardContinuous
        (Type w) (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).FullyFaithful :=
  fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective B S hS (Type w) f hf hui

/-- **Stacks 0AEH, part (1), full faithfulness, through the morphism of small étale topoi.**
For an integral and universally injective morphism `f : Y ⟶ X` of algebraic spaces over a
scheme `S`, the direct image of sheaves of sets along the morphism of small étale topoi of
Stacks 03G2, part (3) is fully faithful.

By Stacks 03G8 that direct image is restriction along chart base change, so this is the
previous statement read through an identification and not a new proof. -/
@[stacks 0AEH "part (1): the direct image of the morphism of small étale topoi is fully faithful"]
def fullyFaithfulSmallEtalePushforwardOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom) :
    (smallToposMorphismTypeU B S hS f).pushforward.FullyFaithful :=
  fullyFaithfulSmallEtalePushforward B S hS f
    (relativelyRepresentable_of_isIntegralHom B S hS f hf)
    (smallBaseChange_isCoverDense_of_isIntegralHom_of_universallyInjective B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf) hf hui)
    (smallBaseChange_isLocallyFull_of_isIntegralHom_of_universallyInjective B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf) hf hui)

/-- **Stacks 0AEH, the trailing clause, for sheaves of sets.** For an integral and universally
injective morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S` the counit
`f^{-1}f_*\mathcal{G} ⟶ \mathcal{G}` of the inverse-image/direct-image adjunction on sheaves of
sets is an isomorphism: the inverse image is a left inverse of the direct image.

The counit of an adjunction is an isomorphism exactly when the right adjoint is fully
faithful. -/
@[stacks 0AEH "trailing clause for sheaves of sets: the inverse image is a left inverse"]
theorem smallEtaleAdjunctionCounitIsIsoOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (max (u + 1) v))) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    IsIso (((smallBaseChange B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafAdjunctionContinuous
        (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).counit.app G) := by
  have h := fullyFaithfulSmallEtaleSetPushforwardOfIntegralUniversallyInjective.{max (u + 1) v}
    B S hS f hf hui
  exact (smallEtalePushforward_counit_isIso_iff_fullyFaithful.{v} B S hS f
    (relativelyRepresentable_of_isIntegralHom B S hS f hf)).mpr ⟨h.full, h.faithful⟩ G

/-- **Stacks 0AEH, the trailing clause, for sheaves of sets, as a natural isomorphism.** For an
integral and universally injective morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`
the counit of the adjunction of the morphism of small étale topoi of Stacks 03G2, part (3) is a
natural isomorphism `f_* ⋙ f^{-1} ≅ 𝟭`. -/
@[stacks 0AEH "trailing clause for sheaves of sets, as a natural isomorphism f_* f^{-1} ≅ 1"]
def smallEtalePullbackPushforwardCounitIsoOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom) :
    (smallToposMorphismTypeU B S hS f).pushforward ⋙
        (smallToposMorphismTypeU B S hS f).inverseImage ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :=
  have := (fullyFaithfulSmallEtalePushforwardOfIntegralUniversallyInjective
    B S hS f hf hui).full
  have := (fullyFaithfulSmallEtalePushforwardOfIntegralUniversallyInjective
    B S hS f hf hui).faithful
  asIso (smallToposMorphismTypeU B S hS f).adj.counit

/-! ### Abelian sheaves -/

/-- **Stacks 0AEH, part (2), full faithfulness.** For an integral and universally injective
morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`, the direct image of sheaves of
*abelian groups* along `f` is fully faithful.

Full faithfulness of restriction along a cover-dense, locally full, continuous functor does not
depend on the category of coefficients, so this is
`AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective` at
the category of abelian groups. -/
@[stacks 0AEH "part (2): full faithfulness of the direct image on abelian sheaves"]
def fullyFaithfulSmallEtaleAbelianPushforwardOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    ((smallBaseChange B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafPushforwardContinuous
        AddCommGrpCat.{w} (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).FullyFaithful :=
  fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective B S hS
    AddCommGrpCat.{w} f hf hui

/-- **Stacks 0AEH, part (2), existence of the inverse image.** For an integral morphism
`f : Y ⟶ X` of algebraic spaces over a scheme `S`, the direct image of abelian sheaves along
`f` is a right adjoint, so that the inverse image of part (2) exists.

Universal injectivity is not used: representability is all this needs. -/
@[stacks 0AEH "part (2): the direct image of abelian sheaves has the inverse image as left adjoint"]
theorem smallEtalePushforwardAbIsRightAdjointOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    Nonempty (((smallBaseChange B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).IsRightAdjoint) :=
  smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f
    (relativelyRepresentable_of_isIntegralHom B S hS f hf)

/-- **Stacks 0AEH, the trailing clause, for abelian sheaves.** For an integral and universally
injective morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S` the counit of the
inverse-image/direct-image adjunction on abelian sheaves is an isomorphism: the inverse image is
a left inverse of the direct image.

The adjunction is the one whose existence is
`AlgebraicGeometry.Space.smallEtalePushforwardAbIsRightAdjointOfIntegralUniversallyInjective`,
as in the source, where part (2) presupposes it. -/
@[stacks 0AEH "trailing clause for abelian sheaves: the inverse image is a left inverse"]
theorem smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{max (u + 1) v}) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    letI := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf))
    IsIso (((smallBaseChange B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafAdjunctionContinuous
        AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).counit.app G) := by
  have h := fullyFaithfulSmallEtaleAbelianPushforwardOfIntegralUniversallyInjective.{max (u + 1) v}
    B S hS f hf hui
  exact (smallEtalePushforwardAb_counit_isIso_iff_fullyFaithful.{v} B S hS f
    (relativelyRepresentable_of_isIntegralHom B S hS f hf)).mpr ⟨h.full, h.faithful⟩ G

/-- **Stacks 0AEH, the trailing clause, for abelian sheaves, as a natural isomorphism.** For an
integral and universally injective morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`
the counit of the adjunction of `CategoryTheory.Functor.sheafAdjunctionContinuous` for chart
base change is a natural isomorphism `f_* ⋙ f^{-1} ≅ 𝟭`. -/
@[stacks 0AEH "trailing clause for abelian sheaves, as a natural isomorphism f_* f^{-1} ≅ 1"]
def smallEtaleAbelianPullbackPushforwardCounitIsoOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).toIsContinuous
    letI := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf))
    (smallBaseChange B S hS f
        (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1) ⋙
      (smallBaseChange B S hS f
        (relativelyRepresentable_of_isIntegralHom B S hS f hf)).sheafPullback
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1) ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{max (u + 1) v}) := by
  let hr := relativelyRepresentable_of_isIntegralHom B S hS f hf
  letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  letI := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f hr)
  have hiso := smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective.{v}
    B S hS f hf hui
  have : IsIso ((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).counit :=
    NatIso.isIso_of_isIso_app _
  exact asIso ((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
    AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS Y.1)).counit

end AlgebraicGeometry.Space

end
