module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-affine morphisms are the quasi-compact open subschemes of a relative spectrum

Let `f : X ⟶ S` be a morphism of schemes. Over an arbitrary base `S`, `f` is quasi-affine exactly
when it factors as a quasi-compact open immersion into the relative spectrum of some
quasi-coherent sheaf of `𝒪_S`-algebras, and, for `f` quasi-compact and quasi-separated, exactly
when the canonical morphism `can : X ⟶ Spec_S(f_* 𝒪_X)` is a quasi-compact open immersion.

## Main results

* `AlgebraicGeometry.Scheme.isQuasiAffine_iff_toSpecΓ`: a scheme is quasi-affine exactly when the
  canonical morphism to the spectrum of its global sections is a quasi-compact open immersion.
* `AlgebraicGeometry.isQuasiAffineHom_iff_canonicalMorphism`: a quasi-compact and
  quasi-separated morphism is quasi-affine exactly when its canonical morphism to
  `Spec_S(f_* 𝒪_X)` is a quasi-compact open immersion.
* `AlgebraicGeometry.isOpenImmersion_canonicalMorphism` and
  `AlgebraicGeometry.quasiCompact_canonicalMorphism`: for a quasi-affine morphism the canonical
  morphism is an open immersion and is quasi-compact.
* `AlgebraicGeometry.isQuasiAffineHom_iff_exists_relativeSpec`: a morphism is quasi-affine exactly
  when it factors as a quasi-compact open immersion into the relative spectrum of a
  quasi-coherent sheaf of `𝒪_S`-algebras.

## Implementation notes

`AlgebraicGeometry.chartPreimageIsoSpecΓ` is the chart of the relative spectrum with its source
spelled `Spec Γ(X, f⁻¹(U))`: the sections of `f_* 𝒪_X` over `U` are `Γ(X, f⁻¹(U))`
definitionally but not syntactically, and instance search for `IsIso` on the chart's forward map
does not see through that.

## References

* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

/-- Quasi-compactness of a morphism of schemes respects isomorphisms, being stable under base
change. -/
private instance respectsIso_quasiCompact :
    MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Quasi-compactness is Zariski-local at the target, at the affine-target property "the source
is a compact space". -/
private instance zariskiLocalAtTarget_quasiCompact :
    IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat

variable {X S : Scheme.{u}}

/-- A scheme is quasi-affine if and only if the canonical morphism to the spectrum of its global
sections is a quasi-compact open immersion. -/
theorem Scheme.isQuasiAffine_iff_toSpecΓ (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ IsOpenImmersion X.toSpecΓ ∧ QuasiCompact X.toSpecΓ := by
  refine ⟨fun hX ↦ have := hX; ⟨inferInstance, inferInstance⟩, fun ⟨hi, hc⟩ ↦ ?_⟩
  have := hc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace X.toSpecΓ
  have : IsImmersion X.toSpecΓ := have := hi; inferInstance
  constructor

/-- An open subscheme is quasi-affine if and only if the canonical morphism to the spectrum of
its sections in the ambient scheme is a quasi-compact open immersion. -/
theorem Scheme.Opens.isQuasiAffine_iff_toSpecΓ {X : Scheme.{u}} (U : X.Opens) :
    Scheme.IsQuasiAffine U.toScheme ↔ IsOpenImmersion U.toSpecΓ ∧ QuasiCompact U.toSpecΓ := by
  have h : U.toSpecΓ = U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv := rfl
  rw [h, Scheme.isQuasiAffine_iff_toSpecΓ,
    MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @QuasiCompact)]

section

variable (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]

/-- The chart of `Spec_S(f_* 𝒪_X)` over an affine open `U` of the base, with the spectrum of the
sections of `f_* 𝒪_X` over `U` spelled as the spectrum of the sections of `𝒪_X` over `f⁻¹(U)`:
the identification of `Spec Γ(X, f⁻¹(U))` with the inverse image of `U` in the relative
spectrum. -/
noncomputable def chartPreimageIsoSpecΓ (U : S.affineOpens) :
    Spec Γ(X, f ⁻¹ᵁ U.1) ≅ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1).toScheme :=
  (pushforwardSpectrum f).chartIsoPreimage U

/-- Over an affine open `U` of the base, the restriction of the canonical morphism
`can : X ⟶ Spec_S(f_* 𝒪_X)` to the inverse image of `U` in the relative spectrum is, as an
arrow, the canonical morphism `f⁻¹(U) ⟶ Spec Γ(X, f⁻¹(U))` followed by the chart identifying
that spectrum with the inverse image of `U`. -/
noncomputable def arrowIsoMorphismRestrictCanonicalMorphism (U : S.affineOpens) :
    Arrow.mk (canonicalMorphism f ∣_ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) ≅
      Arrow.mk ((f ⁻¹ᵁ U.1).toSpecΓ ≫ (chartPreimageIsoSpecΓ f U).hom) :=
  Arrow.isoMk (X.isoOfEq (canonicalMorphism_preimage_preimage f U.1)) (Iso.refl _) <| by
    have h₁ : (X.isoOfEq (canonicalMorphism_preimage_preimage f U.1)).hom ≫ (f ⁻¹ᵁ U.1).ι =
        (canonicalMorphism f ⁻¹ᵁ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)).ι :=
      X.isoOfEq_hom_ι _
    have h₂ : ((f ⁻¹ᵁ U.1).toSpecΓ ≫ (chartPreimageIsoSpecΓ f U).hom) ≫
          ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1).ι =
        (f ⁻¹ᵁ U.1).ι ≫ canonicalMorphism f :=
      (Category.assoc _ _ _).trans (ι_toRelativeSpec_eq_chartIsoPreimage f U).symm
    rw [← cancel_mono ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1).ι]
    simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
    rw [Category.assoc, h₂, ← Category.assoc, h₁, morphismRestrict_ι]

/-- Over an affine open `U` of the base, the restriction of the canonical morphism
`can : X ⟶ Spec_S(f_* 𝒪_X)` to the inverse image of `U` is a quasi-compact open immersion
exactly when `f⁻¹(U)` is a quasi-affine scheme. -/
theorem isQuasiAffine_preimage_iff_morphismRestrict_canonicalMorphism (U : S.affineOpens) :
    Scheme.IsQuasiAffine (f ⁻¹ᵁ U.1).toScheme ↔
      IsOpenImmersion (canonicalMorphism f ∣_ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) ∧
        QuasiCompact (canonicalMorphism f ∣_ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) := by
  have e := arrowIsoMorphismRestrictCanonicalMorphism f U
  have key (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
      P (canonicalMorphism f ∣_ ((pushforwardSpectrum f).toBase ⁻¹ᵁ U.1)) ↔
        P (f ⁻¹ᵁ U.1).toSpecΓ :=
    (MorphismProperty.arrow_mk_iso_iff P e).trans
      (MorphismProperty.cancel_right_of_respectsIso P _ _)
  rw [key @IsOpenImmersion, key @QuasiCompact]
  exact Scheme.Opens.isQuasiAffine_iff_toSpecΓ (f ⁻¹ᵁ U.1)

/-- A morphism of schemes which is quasi-compact and quasi-separated — so that `f_* 𝒪_X` is a
quasi-coherent sheaf of `𝒪_S`-algebras and the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` exists —
is quasi-affine if and only if that canonical morphism is a quasi-compact open immersion. -/
@[stacks 01SM "(1) ↔ (4) over a general base, carrying the quasi-compact and quasi-separated \
hypotheses that make `f_* 𝒪_X` quasi-coherent", ega "II 5.1.2" "more general", ega "II 5.1.6"]
theorem isQuasiAffineHom_iff_canonicalMorphism :
    IsQuasiAffineHom f ↔
      IsOpenImmersion (canonicalMorphism f) ∧ QuasiCompact (canonicalMorphism f) := by
  have hcover : ⨆ U : S.affineOpens, (pushforwardSpectrum f).toBase ⁻¹ᵁ U.1 = ⊤ :=
    Scheme.Hom.iSup_preimage_eq_top _ (iSup_affineOpens_eq_top S)
  constructor
  · intro hf
    have h U := (isQuasiAffine_preimage_iff_morphismRestrict_canonicalMorphism f U).mp
      (hf.isQuasiAffine_preimage U.1 U.2)
    exact ⟨IsZariskiLocalAtTarget.of_iSup_eq_top _ hcover fun U ↦ (h U).1,
      IsZariskiLocalAtTarget.of_iSup_eq_top _ hcover fun U ↦ (h U).2⟩
  · rintro ⟨hoi, hqc⟩
    refine ⟨fun U hU ↦ ?_⟩
    exact (isQuasiAffine_preimage_iff_morphismRestrict_canonicalMorphism f ⟨U, hU⟩).mpr
      ⟨IsZariskiLocalAtTarget.restrict hoi _, IsZariskiLocalAtTarget.restrict hqc _⟩

end

/-- The canonical morphism from the source of a quasi-affine morphism to the relative spectrum of
the pushed-forward structure sheaf is an open immersion. -/
@[stacks 01SM "(1) ⇒ (4), the open-immersion half"]
instance isOpenImmersion_canonicalMorphism (f : X ⟶ S) [IsQuasiAffineHom f] :
    IsOpenImmersion (canonicalMorphism f) :=
  ((isQuasiAffineHom_iff_canonicalMorphism f).mp ‹IsQuasiAffineHom f›).1

/-- The canonical morphism from the source of a quasi-affine morphism to the relative spectrum of
the pushed-forward structure sheaf is quasi-compact. -/
@[stacks 01SM "(1) ⇒ (4), the quasi-compactness half"]
instance quasiCompact_canonicalMorphism (f : X ⟶ S) [IsQuasiAffineHom f] :
    QuasiCompact (canonicalMorphism f) :=
  ((isQuasiAffineHom_iff_canonicalMorphism f).mp ‹IsQuasiAffineHom f›).2

/-- A morphism of schemes `f : X ⟶ S` is quasi-affine if and only if there is a quasi-coherent
sheaf `A` of `𝒪_S`-algebras and a quasi-compact open immersion `X ⟶ Spec_S(A)` over `S`. -/
@[stacks 01SM "(1) ↔ (3) over a general base, no hypotheses"]
theorem isQuasiAffineHom_iff_exists_relativeSpec (f : X ⟶ S) :
    IsQuasiAffineHom f ↔
      ∃ (A : AlgebraSheaf S) (hA : AlgebraSheaf.IsQuasicoherent A)
        (g : X ⟶ @relativeSpec S A hA),
        IsOpenImmersion g ∧ QuasiCompact g ∧ g ≫ @relativeSpecToBase S A hA = f := by
  constructor
  · exact fun _ ↦ ⟨pushforwardAlgebra f, AlgebraSheaf.isQuasicoherent_pushforwardAlgebra f,
      canonicalMorphism f, isOpenImmersion_canonicalMorphism f,
      quasiCompact_canonicalMorphism f, canonicalMorphism_comp_toBase f⟩
  · rintro ⟨A, hA, g, hg, hgc, hgf⟩
    have := hA
    refine ⟨fun U hU ↦ ?_⟩
    have hV : IsAffineOpen (relativeSpecToBase A ⁻¹ᵁ U) :=
      isAffineOpen_preimage_relativeSpecToBase A ⟨U, hU⟩
    have hpre : g ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    have hgoi : IsOpenImmersion (g ∣_ (relativeSpecToBase A ⁻¹ᵁ U)) :=
      IsZariskiLocalAtTarget.restrict hg _
    have hgqc : QuasiCompact (g ∣_ (relativeSpecToBase A ⁻¹ᵁ U)) :=
      IsZariskiLocalAtTarget.restrict hgc _
    have : IsAffine (relativeSpecToBase A ⁻¹ᵁ U).toScheme := hV
    have : CompactSpace (g ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ U)).toScheme :=
      QuasiCompact.compactSpace_of_compactSpace (g ∣_ (relativeSpecToBase A ⁻¹ᵁ U))
    have : Scheme.IsQuasiAffine (g ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ U)).toScheme :=
      Scheme.IsQuasiAffine.of_isImmersion (g ∣_ (relativeSpecToBase A ⁻¹ᵁ U))
    rwa [hpre] at this

end AlgebraicGeometry

end
