module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.RelativeSpectrum

/-!
# Finiteness and étaleness of the second factor of the Stein factorization

Let `f : X ⟶ S` be a universally closed, quasi-separated morphism of schemes, so that `f` factors
as `X ⟶ S' ⟶ S` with `S'` the normalization of `S` in `X`. The second factor
`f.fromNormalization` is the structure morphism of the relative spectrum of `f_* 𝒪_X`, so it is
étale as soon as every structure map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` on sections over an affine open of `S`
is; and being already integral, it is then finite étale.

## Main results

* `Stacks.SteinFactorization.etale_toBase_pushforwardSpectrum`: étaleness of the structure
  morphism of `Spec_S(f_* 𝒪_X)`.
* `Stacks.SteinFactorization.etale_fromNormalization_of_forall_etale_app` and
  `Stacks.SteinFactorization.isFinite_fromNormalization_of_forall_etale_app`: the two properties
  of the second factor.
* `Stacks.SteinFactorization.isFinite_and_etale_fromNormalization_of_forall_etale_app`: the
  second factor is finite étale.

## Implementation notes

Étaleness is run the way `AlgebraicGeometry.isIntegralHom_toBase_pushforwardSpectrum` runs
integrality. `AlgebraicGeometry.Etale` is Zariski-local on the target, so it may be checked over
the affine opens of `S`; over such a `U` the chart isomorphism
`Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage` identifies the restriction of the structure
morphism with `Spec Γ(X, f⁻¹U) ⟶ Spec Γ(S, U) ≅ U`, and a property of a morphism of affine schemes
of that shape is the corresponding property of the ring map. The transfer from the relative
spectrum to `f.fromNormalization` is
`AlgebraicGeometry.normalizationIsoPushforwardSpectrum_hom_comp_toBase`, which writes the second
factor as an isomorphism followed by the structure morphism.

**Finiteness costs no hypothesis.** `AlgebraicGeometry.IsFinite` is integrality together with
being locally of finite type
(`AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`). The second factor is
integral for every universally closed quasi-separated `f`, which is
`Stacks.SteinFactorization.isIntegralHom_fromNormalization`, and an étale morphism is locally of
finite type. So the étaleness hypothesis alone gives finite étale.

The locality instance is supplied by hand, as
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`: instance search does not find
it from the goal alone, the ring-homomorphism property it quantifies over being invisible there.

The hypothesis is stated on the structure maps of the algebra on sections over the affine opens
rather than on `f_* 𝒪_X` as a sheaf, because that is the shape in which the chart isomorphism
consumes it, and the shape that
`Stacks.QuasicoherentAlgebraEqualizer.etale_relativeSpecToBase` uses.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] [QuasiSeparated f]

/-! ### The charts over the affine opens of the base -/

/-- For an affine open `U ⊆ S` over which the structure map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` is étale, the
chart of the relative spectrum of `f_* 𝒪_X` at `U` is étale over `U`. -/
public theorem etale_specSectionsToOpen (U : S.affineOpens)
    (h : ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    Etale (specSectionsToOpen (pushforwardSituation f) U) := by
  have h₁ : Etale (Spec.map ((pushforwardSituation f).algebra.hom.hom.app (op U.1))) :=
    HasRingHomProperty.Spec_iff.mpr h
  have h₂ : Etale U.2.isoSpec.inv := inferInstance
  have : MorphismProperty.IsStableUnderComposition (@Etale) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.comp_mem (@Etale) _ _ h₁ h₂

/-- The restriction over an affine open `U ⊆ S` of the structure morphism of the relative
spectrum of `f_* 𝒪_X` is the chart at `U`, up to the chart isomorphism. -/
public theorem chartIsoPreimage_inv_comp_specSectionsToOpen (U : S.affineOpens) :
    ((pushforwardSpectrum f).chartIsoPreimage U).inv ≫
        specSectionsToOpen (pushforwardSituation f) U =
      (pushforwardSpectrum f).toBase ∣_ U.1 := by
  rw [← (pushforwardSpectrum f).chartIsoPreimage_hom_comp_morphismRestrict U,
    Iso.inv_hom_id_assoc]

/-! ### The structure morphism of the relative spectrum -/

/-- The structure morphism `Spec_S(f_* 𝒪_X) ⟶ S` is étale as soon as every structure map
`Γ(S, U) ⟶ Γ(X, f⁻¹U)` on sections over an affine open of `S` is. -/
public theorem etale_toBase_pushforwardSpectrum
    (h : ∀ U : S.affineOpens,
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    Etale (pushforwardSpectrum f).toBase := by
  have : IsZariskiLocalAtTarget @Etale := HasRingHomProperty.instIsZariskiLocalAtTarget @Etale
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale)
    (fun U : S.affineOpens ↦ U.1) (iSup_affineOpens_eq_top S)]
  intro U
  rw [← chartIsoPreimage_inv_comp_specSectionsToOpen f U]
  have := etale_specSectionsToOpen f U (h U)
  infer_instance

/-! ### The second factor of the factorization -/

/-- The second factor of the factorization of `f` through the normalization of `S` in `X` is
étale as soon as every structure map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` on sections over an affine open of
`S` is. -/
public theorem etale_fromNormalization_of_forall_etale_app
    (h : ∀ U : S.affineOpens,
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    Etale f.fromNormalization := by
  rw [← normalizationIsoPushforwardSpectrum_hom_comp_toBase f]
  have := etale_toBase_pushforwardSpectrum f h
  infer_instance

/-- The second factor of the factorization of `f` through the normalization of `S` in `X` is
finite as soon as every structure map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` on sections over an affine open of
`S` is étale: it is integral for every universally closed quasi-separated `f`, and an étale
morphism is locally of finite type. -/
public theorem isFinite_fromNormalization_of_forall_etale_app
    (h : ∀ U : S.affineOpens,
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    IsFinite f.fromNormalization := by
  have := etale_fromNormalization_of_forall_etale_app f h
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f.fromNormalization).mpr
    ⟨isIntegralHom_fromNormalization f, inferInstance⟩

/-- The second factor of the factorization of `f` through the normalization of `S` in `X` is
finite étale as soon as `f_* 𝒪_X` is étale over `𝒪_S` on sections over every affine open of
`S`. -/
public theorem isFinite_and_etale_fromNormalization_of_forall_etale_app
    (h : ∀ U : S.affineOpens,
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization :=
  ⟨isFinite_fromNormalization_of_forall_etale_app f h,
    etale_fromNormalization_of_forall_etale_app f h⟩

end Stacks.SteinFactorization

end
