module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism

/-!
# The pushed-forward structure sheaf of a universally closed morphism is integral

Let `f : X ⟶ S` be a quasi-compact, quasi-separated and universally closed morphism of schemes.
Then `f_* 𝒪_X` is integral over `𝒪_S`, that is, the structure morphism
`π : Spec_S(f_* 𝒪_X) ⟶ S` of the relative spectrum is an integral morphism. Equivalently, the
normalization of `S` in `X` is the factorization
`X ⟶ Spec_S(f_* 𝒪_X) ⟶ S` of the canonical morphism of
`Stacks.RelativeSpec.canonicalMorphism`.

## Main definitions

* `AlgebraicGeometry.toPushforwardSpectrum` is the comparison morphism from the normalization
  of `S` in `X` to `Spec_S(f_* 𝒪_X)` over `S`, and
  `AlgebraicGeometry.normalizationIsoPushforwardSpectrum` is the isomorphism it turns out to
  be.

## Main results

* `AlgebraicGeometry.isIntegralHom_toBase_pushforwardSpectrum`: the structure morphism
  `Spec_S(f_* 𝒪_X) ⟶ S` is integral, i.e. `f_* 𝒪_X` is integral over `𝒪_S`.
* `AlgebraicGeometry.normalizationIsoPushforwardSpectrum`: the normalization of `S` in `X` is
  isomorphic to `Spec_S(f_* 𝒪_X)`.
* `AlgebraicGeometry.toNormalization_normalizationIsoPushforwardSpectrum_hom` and
  `AlgebraicGeometry.normalizationIsoPushforwardSpectrum_hom_comp_toBase`: that isomorphism
  turns the normalization factorization of `f` into the factorization through the relative
  spectrum.

## Implementation notes

An affine morphism is integral as soon as it is universally closed, so integrality of `π` splits
into affineness, which holds for the relative spectrum of any quasi-coherent algebra
(`Stacks.RelativeSpec.isAffineHom_toBase`), and universal closedness, which is local on `S`.
Over an affine open `U` the chart of the relative spectrum is cartesian over `U.ι`, so the
restriction of `π` over `U` is, through the isomorphism
`Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage`, the morphism
`Spec Γ(X, f⁻¹U) ⟶ Spec Γ(S, U) ≅ U`, and that morphism is integral exactly because the ring
map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` is, which is
`Stacks.AlgebraicGeometry.isIntegral_app_of_universallyClosed`, the affine-open form of
Mathlib's `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`.

That last input replaces the route of the Stacks proof. Stacks reads a global section of
`𝒪_X` as a morphism to `𝔸¹_S`, shows its scheme-theoretic image is proper and affine over `S`
hence integral, and extracts a monic polynomial from the ideal of the image; Mathlib instead
cancels, observing that `X ⟶ Spec Γ(X, ⊤)` is universally closed and affine, hence integral and
surjective, so that `Spec Γ(X, ⊤) ⟶ S` is integral too.

Given integrality, the morphism `X ⟶ Spec_S(f_* 𝒪_X)` is a factorization of `f` through an
integral morphism, so the universal property `AlgebraicGeometry.Scheme.Hom.normalizationDesc`
of the relative normalization produces the comparison morphism. That it is an isomorphism is
checked over the affine opens of `S`: both schemes are affine over `S`, and on sections over
`π⁻¹U` the comparison is sandwiched between two isomorphisms, namely
`Stacks.SteinFactorization.isIso_app_toNormalization` (the sections of the normalization over
`π⁻¹U` are `Γ(X, f⁻¹U)`, because the integral closure of `Γ(S, U)` in `Γ(X, f⁻¹U)` is
everything) and `Stacks.RelativeSpec.isIso_canonicalMorphism_app` (the same for the relative
spectrum, by the universal property).

Quasi-compactness of `f` is not assumed: it follows from universal closedness.

## References

* [Stacks Project, Tag 03GQ](https://stacks.math.columbia.edu/tag/03GQ)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RelativeSpec

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] [QuasiSeparated f]

/-! ### Integrality of the pushed-forward structure sheaf -/

/-- For a universally closed morphism `f : X ⟶ S` and an affine open `U ⊆ S`, the chart of the
relative spectrum of `f_* 𝒪_X` at `U` is integral over `U`: it is the spectrum of the integral
ring map `Γ(S, U) ⟶ Γ(X, f⁻¹U)`, followed by the identification of `Spec Γ(S, U)` with `U`. -/
theorem isIntegralHom_specSectionsToOpen (U : S.affineOpens) :
    IsIntegralHom (specSectionsToOpen (pushforwardSituation f) U) :=
  have h : ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.IsIntegral :=
    Stacks.AlgebraicGeometry.isIntegral_app_of_universallyClosed f U.2
  have h₁ : IsIntegralHom (Spec.map ((pushforwardSituation f).algebra.hom.hom.app (op U.1))) :=
    IsIntegralHom.SpecMap_iff.mpr h
  have h₂ : IsIntegralHom U.2.isoSpec.inv := inferInstance
  MorphismProperty.comp_mem @IsIntegralHom _ _ h₁ h₂

/-- The chart of the relative spectrum at an affine open `U` of the base, followed by the
restriction of the structure morphism over `U`, is the structure map of the algebra at `U`
followed by the identification of `Spec Γ(S, U)` with `U`. -/
theorem chartIsoPreimage_hom_comp_morphismRestrict (U : S.affineOpens) :
    ((pushforwardSpectrum f).chartIsoPreimage U).hom ≫ (pushforwardSpectrum f).toBase ∣_ U.1 =
      specSectionsToOpen (pushforwardSituation f) U :=
  (pushforwardSpectrum f).chartIsoPreimage_hom_comp_morphismRestrict U

/-- For a quasi-separated, universally closed morphism `f : X ⟶ S` the sheaf of algebras
`f_* 𝒪_X` is integral over `𝒪_S`: the structure morphism `Spec_S(f_* 𝒪_X) ⟶ S` of its relative
spectrum is an integral morphism.

An affine morphism is integral as soon as it is universally closed, and universal closedness is
checked on the affine opens of `S`, where the structure morphism is the spectrum of the integral
ring map `Γ(S, U) ⟶ Γ(X, f⁻¹U)`. -/
@[stacks 03GQ "integral"]
theorem isIntegralHom_toBase_pushforwardSpectrum :
    IsIntegralHom (pushforwardSpectrum f).toBase := by
  rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom]
  refine ⟨?_, inferInstance⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @UniversallyClosed)
    (fun U : S.affineOpens ↦ U.1) (iSup_affineOpens_eq_top S)]
  intro U
  rw [← (Iso.inv_comp_eq _).mpr (chartIsoPreimage_hom_comp_morphismRestrict f U).symm]
  have := isIntegralHom_specSectionsToOpen f U
  infer_instance

/-! ### The normalization is the relative spectrum of the pushed-forward structure sheaf -/

/-- The comparison morphism from the normalization of `S` in `X` to `Spec_S(f_* 𝒪_X)` over `S`,
given by the universal property of the relative normalization applied to the factorization of `f`
through the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)`, whose second factor is integral. -/
noncomputable def toPushforwardSpectrum :
    f.normalization ⟶ (pushforwardSpectrum f).scheme :=
  have := isIntegralHom_toBase_pushforwardSpectrum f
  f.normalizationDesc (canonicalMorphism f) (pushforwardSpectrum f).toBase
    (canonicalMorphism_comp_toBase f).symm

/-- The canonical morphism `X ⟶ f.normalization` followed by the comparison morphism is the
canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)`. -/
@[reassoc (attr := simp)]
theorem toNormalization_toPushforwardSpectrum :
    f.toNormalization ≫ toPushforwardSpectrum f = canonicalMorphism f :=
  have := isIntegralHom_toBase_pushforwardSpectrum f
  f.toNormalization_normalizationDesc (canonicalMorphism f) (pushforwardSpectrum f).toBase
    (canonicalMorphism_comp_toBase f).symm

/-- The comparison morphism followed by the structure morphism `Spec_S(f_* 𝒪_X) ⟶ S` is the
structure morphism `f.normalization ⟶ S`. -/
@[reassoc (attr := simp)]
theorem toPushforwardSpectrum_comp_toBase :
    toPushforwardSpectrum f ≫ (pushforwardSpectrum f).toBase = f.fromNormalization :=
  have := isIntegralHom_toBase_pushforwardSpectrum f
  f.normalizationDesc_comp (canonicalMorphism f) (pushforwardSpectrum f).toBase
    (canonicalMorphism_comp_toBase f).symm

/-- The comparison morphism from the normalization of `S` in `X` to `Spec_S(f_* 𝒪_X)` is
integral. -/
instance isIntegralHom_toPushforwardSpectrum : IsIntegralHom (toPushforwardSpectrum f) :=
  have := isIntegralHom_toBase_pushforwardSpectrum f
  inferInstanceAs (IsIntegralHom (f.normalizationDesc (canonicalMorphism f)
    (pushforwardSpectrum f).toBase (canonicalMorphism_comp_toBase f).symm))

/-- For an open `U ⊆ S`, the preimage of `π⁻¹(U)` under the comparison morphism is the preimage
of `U` in the normalization of `S` in `X`. -/
theorem toPushforwardSpectrum_preimage (U : S.Opens) :
    toPushforwardSpectrum f ⁻¹ᵁ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U) =
      f.fromNormalization ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, toPushforwardSpectrum_comp_toBase]

/-- The comparison morphism `toPushforwardSpectrum f` is an isomorphism on the sections over
`π⁻¹(U)` for each affine open `U ⊆ S`: composed with the sections of `X ⟶ f.normalization`,
which are an isomorphism because `Γ(X, f⁻¹U)` is integral over `Γ(S, U)`, it gives the sections
of the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)`, which are an isomorphism by the universal
property. -/
instance isIso_toPushforwardSpectrum_app (U : S.affineOpens) :
    IsIso ((toPushforwardSpectrum f).app ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) := by
  have hnorm : IsIso (f.toNormalization.app
      (toPushforwardSpectrum f ⁻¹ᵁ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1))) := by
    rw [toPushforwardSpectrum_preimage]
    exact Stacks.SteinFactorization.isIso_app_toNormalization f U.2
  have e := Scheme.Hom.congr_app (toNormalization_toPushforwardSpectrum f)
    ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)
  have hcomp : IsIso ((toPushforwardSpectrum f).app ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1) ≫
      f.toNormalization.app
        (toPushforwardSpectrum f ⁻¹ᵁ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1))) := by
    have hcan : IsIso ((canonicalMorphism f).app ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) :=
      isIso_canonicalMorphism_app f U
    have hmap : ∀ {V W : X.Opens} (hVW : V = W), IsIso (X.presheaf.map (eqToHom hVW).op) :=
      fun _ ↦ inferInstance
    rw [show (toPushforwardSpectrum f).app ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1) ≫
        f.toNormalization.app
          (toPushforwardSpectrum f ⁻¹ᵁ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) = _ from e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hcan (hmap _)
  exact IsIso.of_isIso_comp_right _ (f.toNormalization.app _)

/-- The comparison morphism from the normalization of `S` in `X` to `Spec_S(f_* 𝒪_X)` is an
isomorphism. -/
instance isIso_toPushforwardSpectrum : IsIso (toPushforwardSpectrum f) := by
  have hcov : ⨆ U : S.affineOpens, (pushforwardSpectrum f).toBase ⁻¹ᵁ U.1 = ⊤ :=
    (pushforwardSpectrum f).toBase.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)
  have h : MorphismProperty.isomorphisms Scheme.{u} (toPushforwardSpectrum f) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme.{u}) _ hcov]
    intro U
    exact (isIso_morphismRestrict_iff_isIso_app (toPushforwardSpectrum f)
      (U.2.preimage (pushforwardSpectrum f).toBase)).mpr (isIso_toPushforwardSpectrum_app f U)
  exact h

/-- For a quasi-separated, universally closed morphism `f : X ⟶ S` the normalization of `S` in
`X` is isomorphic to the relative spectrum `Spec_S(f_* 𝒪_X)`. -/
@[stacks 03GQ "normalization"]
noncomputable def normalizationIsoPushforwardSpectrum :
    f.normalization ≅ (pushforwardSpectrum f).scheme :=
  asIso (toPushforwardSpectrum f)

/-- Under the identification of the normalization of `S` in `X` with `Spec_S(f_* 𝒪_X)`, the
canonical morphism `X ⟶ f.normalization` becomes the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)`. -/
@[stacks 03GQ "normalization: first factor"]
theorem toNormalization_normalizationIsoPushforwardSpectrum_hom :
    f.toNormalization ≫ (normalizationIsoPushforwardSpectrum f).hom = canonicalMorphism f :=
  toNormalization_toPushforwardSpectrum f

/-- Under the identification of the normalization of `S` in `X` with `Spec_S(f_* 𝒪_X)`, the
structure morphism `f.normalization ⟶ S` becomes the structure morphism `Spec_S(f_* 𝒪_X) ⟶ S`. -/
@[stacks 03GQ "normalization: second factor"]
theorem normalizationIsoPushforwardSpectrum_hom_comp_toBase :
    (normalizationIsoPushforwardSpectrum f).hom ≫ (pushforwardSpectrum f).toBase =
      f.fromNormalization :=
  toPushforwardSpectrum_comp_toBase f

end AlgebraicGeometry

end
