module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleDivisorDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation

/-!
# The base change of a proper smooth morphism to the spectrum of a field

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`X_T = X ×_Y T` be its base change along a test scheme `T` over `Y`. This file records the
permanence properties of `X_T` that the proof of Stacks 0DNG uses: the base change `X_T ⟶ T` of
a smooth morphism is smooth, the morphism `X_U ⟶ X_T` induced by a flat morphism `U ⟶ T` of test
schemes is flat, and when `f` is proper, smooth and of finite presentation and `T` is the
spectrum of a field, `X_T` is separated, Noetherian and regular — the hypotheses of Stacks 0DMM.

## Main results

* `AlgebraicGeometry.Space.isPullback_baseChange_hom`: the square defining `X_T` is cartesian on
  underlying presheaves.
* `AlgebraicGeometry.Space.isSmooth_baseChangeInclusion`: `X_T ⟶ T` is smooth if `f` is.
* `AlgebraicGeometry.Space.isFlat_baseChangeMap`: `X_U ⟶ X_T` is flat if `U ⟶ T` is.
* `AlgebraicGeometry.Space.baseChangeSpace_separated_noetherian_regular`: over a field, `X_T` is
  separated, Noetherian (Stacks 04ZL) and regular (Stacks 06M1).

## References

* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 0DNG](https://stacks.math.columbia.edu/tag/0DNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The square defining the base change `X_T = X ×_Y T` of `f : X ⟶ Y` along a test scheme `T`
is cartesian as a square of presheaves on the big fppf site of `S`. -/
theorem isPullback_baseChange_hom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : SchemesOver Y) :
    IsPullback (baseChangeProjection f T).hom (baseChangeInclusion f T).hom f.hom T.hom.hom :=
  AlgebraicSpaces.isPullback_hom B S hS (AlgebraicSpaces.isPullback_fiberProduct B S hS f _)

/-- The base change `X_T ⟶ T` of a smooth morphism `X ⟶ Y` along a test scheme is smooth. -/
theorem isSmooth_baseChangeInclusion {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsSmooth B S hS f.hom) (T : SchemesOver Y) :
    IsSmooth B S hS (baseChangeInclusion f T).hom :=
  isSmooth_of_isPullback (isPullback_baseChange_hom f T).flip (baseChangeSpace f T).2 X.2
    ((schemeSpaceFunctor B S hS).obj T.left).2 Y.2 hf

/-- The base change `X_U ⟶ X_T` along a flat morphism `U ⟶ T` of test schemes is flat. -/
theorem isFlat_baseChangeMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U T : SchemesOver Y} (g : U ⟶ T)
    (hg : Flat ((BigFppfOver.toScheme B S hS).map g.left)) :
    IsFlat B S hS (baseChangeMap f g).hom :=
  isFlat_of_isPullback_of_isAlgebraicSpace B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap f g))
    ((schemeSpaceFunctor B S hS).obj U.left).2 ((schemeSpaceFunctor B S hS).obj T.left).2
    (isFlat_yoneda_map B S hS g.left hg)

/-- The base change of a proper, smooth morphism of finite presentation along a test scheme
whose underlying scheme is the spectrum of a field is separated, Noetherian and regular: the
hypotheses of Stacks 0DMM. -/
theorem baseChangeSpace_separated_noetherian_regular {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfp : IsFinitePresentation B S hS f.hom) (hproper : IsProper B S hS f.hom)
    (hsmooth : IsSmooth B S hS f.hom) {K : Type u} [Field K] (T : SchemesOver Y)
    (hT : (BigFppfOver.toScheme B S hS).obj T.left = Spec (.of K)) :
    IsAbsolutelySeparated B S hS B.contains_terminal (baseChangeSpace f T).1 ∧
      IsNoetherian B S hS B.contains_terminal (baseChangeSpace f T).1 ∧
      HasEtaleLocalProperty B S hS (baseChangeSpace f T).1
        (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular V) := by
  have sq := isPullback_baseChange_hom f T
  have hXT := (baseChangeSpace f T).2
  have hTsp := ((schemeSpaceFunctor B S hS).obj T.left).2
  have hpr : IsProper B S hS (baseChangeInclusion f T).hom :=
    isProper_of_isPullback B S hS hXT X.2 hTsp Y.2 sq hproper
  have hfp' : IsFinitePresentation B S hS (baseChangeInclusion f T).hom :=
    isFinitePresentation_of_isPullback B S hS hXT X.2 hTsp Y.2 sq hfp
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) := hT ▸ inferInstance
  have hsep : IsAbsolutelySeparated B S hS B.contains_terminal (baseChangeSpace f T).1 :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal T.left haff
      (baseChangeInclusion f T).hom hpr.1
  refine ⟨hsep, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isQuasiCompactSpace_of_isFinitePresentation B S hS (baseChangeInclusion f T).hom hTsp
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS T.left haff) hfp'
  · exact isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal _ hsep
  · exact hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hXT hTsp
      (baseChangeInclusion f T).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp'.1)
      (hasEtaleLocalProperty_of_representable B S hS _ _ T.left (Iso.refl _) (hT ▸ inferInstance))
  · exact isRegular_of_isSmooth_over_field B S hS K T.left hT hXT (baseChangeInclusion f T).hom
      (isSmooth_baseChangeInclusion f hsmooth T)

end AlgebraicGeometry.Space
