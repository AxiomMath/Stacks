module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism

/-!
# The relative spectrum of `f_* 𝒪_X` is the relative normalization

Let `f : X ⟶ S` be a quasi-separated and universally closed morphism of schemes (such an `f` is
automatically quasi-compact). Then `f_* 𝒪_X` is integral over `𝒪_S`, and consequently the
factorization
`X ⟶ Spec_S(f_* 𝒪_X) ⟶ S`
of [Stacks, Tag 01LY] *is* the relative normalization of `S` in `X`: the canonical morphism from
the relative normalization to the relative spectrum is an isomorphism, compatibly with the
structure morphisms to `S` and with the canonical morphisms out of `X`.

## Main definitions

* `Stacks.RelativeSpec.normalizationToRelativeSpec` is the canonical morphism from the relative
  normalization of `S` in `X` to the relative spectrum of `f_* 𝒪_X`.
* `Stacks.RelativeSpec.normalizationIsoRelativeSpec` is that morphism, as an isomorphism.

## Main results

* `Stacks.RelativeSpec.isIntegralHom_toBase`: the structure morphism of the relative spectrum of
  `f_* 𝒪_X` is an integral morphism.
* `Stacks.RelativeSpec.isIso_toRelativeSpec_app`: the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)`
  is an isomorphism on the sections over the preimage of an affine open of `S`.
* `Stacks.RelativeSpec.normalizationIsoRelativeSpec_hom_toBase` and
  `Stacks.RelativeSpec.toNormalization_normalizationIsoRelativeSpec_hom`: the comparison
  isomorphism is compatible with the structure morphisms to `S` and with the canonical morphisms
  out of `X`.

The integrality assertion of [Stacks, Tag 03GQ] itself is
`AlgebraicGeometry.isIntegral_app_of_universallyClosed`, stated for a universally closed
morphism with no further hypotheses.

## Implementation notes

Over an affine open `U` of `S`, the sections of the structure morphism
`π : Spec_S(f_* 𝒪_X) ⟶ S` are the structure map of `f_* 𝒪_X`, which is `f.app U`, followed by
the universal map of Tag 01LV, which is an isomorphism there
(`Stacks.RelativeSpec.toBase_app` and `Stacks.RelativeSpec.isIso_universalAlgebraMap_app`).
Since `RingHom.IsIntegral` respects isomorphisms, `π` is integral; so `f` factors through an
integral morphism and Mathlib's `AlgebraicGeometry.Scheme.Hom.normalizationDesc` produces the
comparison morphism, already compatible with both factorizations.

That the comparison is an isomorphism is checked on the preimages of the affine opens of `S`,
where it is a statement about rings. The canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` is an
isomorphism on sections there because the universal map of Tag 01LV inverts it
(`Stacks.RelativeSpec.pairToHom_appLE` for the pair `(f, 𝟙)`), and the canonical morphism to the
relative normalization is one because `f_* 𝒪_X` is integral
(`AlgebraicGeometry.Scheme.Hom.isIso_toNormalization_app`). The comparison is therefore an
isomorphism on sections as the remaining factor of a composite of isomorphisms.

## References

* [Stacks Project, Tag 03GQ](https://stacks.math.columbia.edu/tag/03GQ)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The relative spectrum of `f_* 𝒪_X` is integral over the base -/

/-- For a quasi-separated and universally closed `f : X ⟶ S`, the structure morphism of the
relative spectrum of `f_* 𝒪_X` is an integral morphism. It is affine by [Stacks, Tag 01LX], and
over an affine open `U` of `S` its sections are `f.app U` followed by an isomorphism, so they are
integral by `AlgebraicGeometry.isIntegral_app_of_universallyClosed`. -/
instance isIntegralHom_toBase [UniversallyClosed f] [QuasiSeparated f] :
    IsIntegralHom (gluedSpectrum (pushforwardSituation f)).toBase := by
  have _ : IsAffineHom (gluedSpectrum (pushforwardSituation f)).toBase :=
    isAffineHom_relativeSpecToBase _
  have _ : (RingHom.toMorphismProperty RingHom.IsIntegral).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  refine ⟨fun U hU => ?_⟩
  have _ := isIso_universalAlgebraMap_app (pushforwardSituation f) ⟨U, hU⟩
  rw [toBase_app]
  exact MorphismProperty.RespectsIso.postcomp
    (RingHom.toMorphismProperty RingHom.IsIntegral) _ _
    (isIntegral_app_of_universallyClosed f hU)

/-! ### The canonical morphism is an isomorphism on sections -/

/-- Over an affine open `U` of the base, the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` of
[Stacks, Tag 01LY] is an isomorphism on the sections over the preimage of `U`: the universal map
of [Stacks, Tag 01LV] is inverse to it there. -/
theorem isIso_toRelativeSpec_app [QuasiCompact f] [QuasiSeparated f] (U : S.affineOpens) :
    IsIso ((toRelativeSpec f).app
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U.1)) := by
  have _ := isIso_universalAlgebraMap_app (pushforwardSituation f) U
  have hpre : toRelativeSpec f ⁻¹ᵁ
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U.1) = f ⁻¹ᵁ U.1 := by
    rw [← Scheme.Hom.comp_preimage, toRelativeSpec_toBase]
  have hkey : (universalAlgebraMap (pushforwardSituation f)).right.app (op U.1) ≫
      (toRelativeSpec f).appLE
        ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) hpre.ge =
      𝟙 Γ(X, f ⁻¹ᵁ U.1) := pairToHom_appLE (pushforwardPair f) U hpre.ge
  have h2 : IsIso ((universalAlgebraMap (pushforwardSituation f)).right.app (op U.1) ≫
      (toRelativeSpec f).appLE
        ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) hpre.ge) := by
    rw [hkey]
    exact IsIso.id _
  have h3 : IsIso ((toRelativeSpec f).appLE
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) hpre.ge) :=
    IsIso.of_isIso_comp_left
      ((universalAlgebraMap (pushforwardSituation f)).right.app (op U.1)) _
  have hh : IsIso (homOfLE hpre.ge : f ⁻¹ᵁ U.1 ⟶ _) :=
    CategoryTheory.homOfLE_isIso_of_eq _ hpre.symm
  change IsIso ((toRelativeSpec f).app _ ≫ X.presheaf.map (homOfLE hpre.ge).op) at h3
  exact (isIso_comp_right_iff _ _).mp h3

/-! ### The comparison with the relative normalization -/

variable [UniversallyClosed f] [QuasiSeparated f]

/-- The canonical morphism from the relative normalization of `S` in `X` to the relative
spectrum of `f_* 𝒪_X`, obtained from the factorization of [Stacks, Tag 01LY] through the
universal property of the relative normalization. -/
noncomputable def normalizationToRelativeSpec :
    f.normalization ⟶ (gluedSpectrum (pushforwardSituation f)).scheme :=
  f.normalizationDesc (toRelativeSpec f) (gluedSpectrum (pushforwardSituation f)).toBase
    (toRelativeSpec_toBase f).symm

/-- The comparison morphism lies over the base: composing with the structure morphism of the
relative spectrum gives the structure morphism of the relative normalization. -/
theorem normalizationToRelativeSpec_toBase :
    normalizationToRelativeSpec f ≫ (gluedSpectrum (pushforwardSituation f)).toBase =
      f.fromNormalization :=
  f.normalizationDesc_comp (toRelativeSpec f) _ (toRelativeSpec_toBase f).symm

/-- The comparison morphism carries the canonical morphism to the relative normalization to the
canonical morphism to the relative spectrum. -/
theorem toNormalization_normalizationToRelativeSpec :
    f.toNormalization ≫ normalizationToRelativeSpec f = toRelativeSpec f :=
  f.toNormalization_normalizationDesc (toRelativeSpec f) _ (toRelativeSpec_toBase f).symm

/-- The comparison morphism from the relative normalization to the relative spectrum of
`f_* 𝒪_X` is an integral morphism. -/
instance isIntegralHom_normalizationToRelativeSpec :
    IsIntegralHom (normalizationToRelativeSpec f) :=
  inferInstanceAs (IsIntegralHom (f.normalizationDesc (toRelativeSpec f)
    (gluedSpectrum (pushforwardSituation f)).toBase (toRelativeSpec_toBase f).symm))

/-- The comparison morphism from the relative normalization to the relative spectrum of
`f_* 𝒪_X` is an isomorphism. -/
instance isIso_normalizationToRelativeSpec : IsIso (normalizationToRelativeSpec f) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme) fun y ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((gluedSpectrum (pushforwardSituation f)).toBase y)) isOpen_univ
  refine ⟨(gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U, hyU,
    (isIso_morphismRestrict_iff_isIso_app (normalizationToRelativeSpec f)
      (hU.preimage _)).2 ?_⟩
  have hV : normalizationToRelativeSpec f ⁻¹ᵁ
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U) =
      f.fromNormalization ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, normalizationToRelativeSpec_toBase]
  have ht : IsIso (f.toNormalization.app (normalizationToRelativeSpec f ⁻¹ᵁ
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U))) := by
    rw [hV]
    exact Scheme.Hom.isIso_toNormalization_app f hU
  have hcan : IsIso ((toRelativeSpec f).app
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U)) :=
    isIso_toRelativeSpec_app f ⟨U, hU⟩
  have h0 : IsIso ((f.toNormalization ≫ normalizationToRelativeSpec f).app
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U)) := by
    rw [Scheme.Hom.congr_app (toNormalization_normalizationToRelativeSpec f)]
    infer_instance
  have hc : IsIso ((normalizationToRelativeSpec f).app
        ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U) ≫
      f.toNormalization.app (normalizationToRelativeSpec f ⁻¹ᵁ
        ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U))) := h0
  exact IsIso.of_isIso_comp_right _ (f.toNormalization.app
    (normalizationToRelativeSpec f ⁻¹ᵁ
      ((gluedSpectrum (pushforwardSituation f)).toBase ⁻¹ᵁ U)))

/-- **Stacks Project, Tag 03GQ.** For a quasi-separated and universally closed morphism
`f : X ⟶ S`, the relative normalization of `S` in `X` is the relative spectrum of `f_* 𝒪_X`. -/
@[stacks 03GQ "comparison with relative normalization"]
noncomputable def normalizationIsoRelativeSpec :
    f.normalization ≅ (gluedSpectrum (pushforwardSituation f)).scheme :=
  asIso (normalizationToRelativeSpec f)

/-- **Stacks Project, Tag 03GQ.** The comparison of the relative normalization with the relative
spectrum of `f_* 𝒪_X` is an isomorphism over the base. -/
@[stacks 03GQ "comparison over the base"]
theorem normalizationIsoRelativeSpec_hom_toBase :
    (normalizationIsoRelativeSpec f).hom ≫
        (gluedSpectrum (pushforwardSituation f)).toBase = f.fromNormalization :=
  normalizationToRelativeSpec_toBase f

/-- **Stacks Project, Tag 03GQ.** The comparison of the relative normalization with the relative
spectrum of `f_* 𝒪_X` carries the canonical morphism to the relative normalization to the
canonical morphism of [Stacks, Tag 01LY]. Together with
`Stacks.RelativeSpec.normalizationIsoRelativeSpec_hom_toBase` this says that the relative
normalization of `S` in `X` *is* the factorization `X ⟶ Spec_S(f_* 𝒪_X) ⟶ S`. -/
@[stacks 03GQ "comparison of canonical source maps"]
theorem toNormalization_normalizationIsoRelativeSpec_hom :
    f.toNormalization ≫ (normalizationIsoRelativeSpec f).hom = toRelativeSpec f :=
  toNormalization_normalizationToRelativeSpec f

end Stacks.RelativeSpec

end
