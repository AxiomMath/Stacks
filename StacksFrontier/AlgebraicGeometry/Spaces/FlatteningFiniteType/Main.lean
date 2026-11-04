module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupOfEffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.BlowupOfScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.SchemeBase

/-!
# Flattening a morphism of finite type by a blowup

Let `f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open subspace.
Assume that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is of
finite type and quasi-separated, and that `f⁻¹(U) ⟶ U` is flat and locally of finite
presentation.  Then there is a `U`-admissible blowup `A' ⟶ A` such that the strict transform of
`X` is flat and of finite presentation over `A'`.  This is the statement of Stacks 087E.

The proof here is not the source's, which goes through Stacks 087C, 0873 and 087B: it is an
induction over the elementary distinguished squares of Stacks 08GP
(`AlgebraicGeometry.Space.flattensOverBlowups_of_isQuasiCompactSpace`), whose affine case is
the scheme form of the statement, Stacks 081R.

## Main results

* `exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_flattensOverBlowups`
  (in `AlgebraicGeometry.Space`) is the statement over a base which flattens over its blowups.
* `AlgebraicGeometry.Space.flattensOverBlowups_of_isAffineSpace`: affine spaces flatten over
  their blowups, a blowup of an affine space being a quasi-compact and quasi-separated scheme.
* `exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_isFiniteType`:
  the statement of Stacks 087E.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The flattening over a base which flattens over its blowups**, in the shape of
Stacks 087E: the identity of `A` is the blowup of `A` in its empty closed subspace, so the
flattening over the blowups of `A` applies to `A` itself; the strict transform is
quasi-compact and quasi-separated over the blowup, being a closed subspace of the base change
of `f`, so flat and locally of finite presentation is flat and of finite presentation. -/
theorem exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_flattensOverBlowups
    {A X : AlgebraicSpaces B S hS} (hA : FlattensOverBlowups A) (g : X ⟶ A)
    (U : OpenSubspaces B S hS A.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hft : IsFiniteType B S hS g.hom) (hqs : IsQuasiSeparated B S hS g.hom)
    (hfl : IsFlat B S hS (pullback.snd g.hom U.1.ι))
    (hlfp : IsLocallyOfFinitePresentation B S hS (pullback.snd g.hom U.1.ι)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
        IsBlowupAlong B S hS Z b ∧
        IsFlat B S hS (strictTransformSpaceToBlowUp B S hS g b (Z.1.preimage b.hom)).hom ∧
        IsFinitePresentation B S hS
          (strictTransformSpaceToBlowUp B S hS g b (Z.1.preimage b.hom)).hom := by
  -- the empty closed subspace of `A`, along which the identity is the blowup
  set E : Subfunctor A.1 := (⊥ : Subfunctor A.1).sheafify (BigFppfOver.topology B S hS)
  have hEo : IsOpenSubspace B S hS E := isOpenSubspace_sheafify_bot B S hS A.1 A.2
  have hEc : IsClosedSubspace B S hS E := isClosedSubspace_sheafify_bot B S hS A.2
  have hEfp : IsFinitePresentation B S hS E.ι :=
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hEo.2,
      isQuasiCompact_of_isClosedImmersion' B S hS hEc.2,
      isQuasiSeparated_of_mono B S hS _ inferInstance⟩
  have hid : IsBlowupAlong B S hS ⟨E, hEc⟩ (𝟙 A) :=
    isBlowupAlong_id_of_isEffectiveCartierDivisor B S hS A ⟨E, hEc⟩
      (isEffectiveCartierDivisor_of_isEmpty_points B S hS A ⟨E, hEc⟩
        (isEmpty_points_sheafify_bot B S hS A.1))
  have hfo : FlatOver g U.1 :=
    (flatOver_iff_of_isPullback U.2 (isAlgebraicSpace_pullback B S hS g.hom U.1.ι X.2 U.2.1 A.2)
      (IsPullback.of_hasPullback g.hom U.1.ι)).2 ⟨hfl, hlfp⟩
  obtain ⟨A', b, Z, hZfp, hdisj, hb, hst, hstl⟩ :=
    hA (𝟙 A) ⟨E, hEc⟩ hEfp hid U hUqc g hft hqs hfo
  obtain ⟨hft', hqs'⟩ :=
    isFiniteType_and_isQuasiSeparated_strictTransformSpaceToBlowUp g b (Z.1.preimage b.hom) hft hqs
  exact ⟨A', b, Z, hZfp, hdisj, hb, hst, hstl, hft'.2, hqs'⟩

/-- **Affine algebraic spaces flatten over their blowups**: a blowup of an affine algebraic space
in a finitely presented centre is the algebraic space of a quasi-compact and quasi-separated
scheme, over which the flattening is the scheme form of the statement, Stacks 081R. -/
theorem flattensOverBlowups_of_isAffineSpace {V : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) : FlattensOverBlowups V := by
  intro V₁ c Zc hZcfp hc Ω hΩqc X f hft hqs hfo
  obtain ⟨Q, hQc, hQs, ⟨e⟩⟩ :=
    exists_iso_schemeSpace_of_isBlowupAlong_of_isAffineSpace hV Zc hZcfp hc
  obtain ⟨hfl, hlfp⟩ := (flatOver_iff_of_isPullback Ω.2
    (isAlgebraicSpace_pullback B S hS f.hom Ω.1.ι X.2 Ω.2.1 V₁.2)
    (IsPullback.of_hasPullback f.hom Ω.1.ι)).1 hfo
  exact flattensByBlowup_of_iso_schemeSpace Q e f Ω hΩqc hft hqs hfl hlfp

/-- **Stacks 087E: flattening a morphism of finite type by a blowup.**  Let `g : X ⟶ A` be a
morphism of algebraic spaces over `S` and `U ⊆ A` an open subspace.  Assume (1) `A` is
quasi-compact and quasi-separated, (2) `U` is quasi-compact, (3) `g` is of finite type and
quasi-separated, and (4) `g⁻¹(U) ⟶ U` is flat and locally of finite presentation.  Then there
is a `U`-admissible blowup `b : A' ⟶ A`, in a finitely presented centre `Z` disjoint from `U`,
such that the strict transform of `X` is flat and of finite presentation over `A'`. -/
theorem exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_isFiniteType
    {A X : AlgebraicSpaces B S hS} (g : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor) (hft : IsFiniteType B S hS g.hom)
    (hqs : IsQuasiSeparated B S hS g.hom) (hfl : IsFlat B S hS (pullback.snd g.hom U.1.ι))
    (hlfp : IsLocallyOfFinitePresentation B S hS (pullback.snd g.hom U.1.ι)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
        IsBlowupAlong B S hS Z b ∧
        IsFlat B S hS (strictTransformSpaceToBlowUp B S hS g b (Z.1.preimage b.hom)).hom ∧
        IsFinitePresentation B S hS
          (strictTransformSpaceToBlowUp B S hS g b (Z.1.preimage b.hom)).hom :=
  exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_flattensOverBlowups
    (flattensOverBlowups_of_isQuasiCompactSpace B.contains_terminal
      (fun _ hV => flattensOverBlowups_of_isAffineSpace hV) A hAqc hAqs)
    g U hUqc hft hqs hfl hlfp

end AlgebraicGeometry.Space

end
