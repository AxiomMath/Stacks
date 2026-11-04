module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a universally closed morphism, and its relative normalization

Let `f : X ⟶ S` be a universally closed morphism of schemes. Over an affine open `U` of `S` the
ring map on sections `Γ(S, U) ⟶ Γ(X, f⁻¹(U))` is integral: this is Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` applied to the restriction `f ∣_ U`.

Consequently, when `f` is moreover quasi-separated so that the relative normalization `S'` of
`S` in `X` is defined, the canonical map from the sections of `S'` over the preimage of an affine
open `U` to the sections of `X` over `f⁻¹(U)` is an isomorphism: those sections of `S'` are the
integral closure of `Γ(S, U)` in `Γ(X, f⁻¹(U))`, which by the first paragraph is everything.

## Main results

* `AlgebraicGeometry.isIntegral_app_of_universallyClosed`: the ring map on the sections over an
  affine open of the base is integral.
* `AlgebraicGeometry.Scheme.Hom.isIso_toNormalization_app`: the canonical morphism to the
  relative normalization is an isomorphism on the sections over the preimage of an affine open
  of the base.

## Implementation notes

The first result is transported from the global-sections statement along
`AlgebraicGeometry.arrowResLEAppIso`, which identifies the arrow
`(f.resLE U (f⁻¹ U) le_rfl).appTop` with `f.appLE U (f⁻¹ U) le_rfl`, using that
`RingHom.IsIntegral` respects isomorphisms.

The second is `AlgebraicGeometry.Scheme.Hom.normalizationObjIso_hom_val`, which presents the
map in question as the inclusion of the integral closure; that inclusion is bijective because
every element is integral, by the first result. It is the generalisation from a field base to an
arbitrary affine open of the base of `Stacks.SteinFactorization.isIso_appTop_toNormalization`,
which is deduced from it.

## References

* [Stacks Project, Tag 03GQ](https://stacks.math.columbia.edu/tag/03GQ)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 03GQ.** For a universally closed morphism of schemes `f : X ⟶ S` and
an affine open `U` of `S`, the ring map `Γ(S, U) ⟶ Γ(X, f⁻¹(U))` on sections is integral. This
is the assertion that `f_* 𝒪_X` is integral over `𝒪_S`.

Only universal closedness is needed; the quasi-compactness and quasi-separatedness of Tag 03GQ
are what make `f_* 𝒪_X` a quasi-coherent algebra, not what make it integral. -/
@[stacks 03GQ "integrality of the pushed-forward structure sheaf"]
theorem isIntegral_app_of_universallyClosed (f : X ⟶ S) [UniversallyClosed f] {U : S.Opens}
    (hU : IsAffineOpen U) : RingHom.IsIntegral (f.app U).hom := by
  have _ : IsAffine U.toScheme := hU
  have _ : UniversallyClosed (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have _ : (RingHom.toMorphismProperty RingHom.IsIntegral).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  have hLE : RingHom.IsIntegral (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom :=
    (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty RingHom.IsIntegral)
      (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl)).mp
      (isIntegral_appTop_of_universallyClosed _)
  rwa [f.appLE_eq_app] at hLE

namespace Scheme.Hom

/-- For a universally closed and quasi-separated morphism `f : X ⟶ S` and an affine open `U` of
`S`, the canonical morphism to the relative normalization of `S` in `X` is an isomorphism on the
sections over the preimage of `U`. Indeed those sections are the integral closure of `Γ(S, U)`
in `Γ(X, f⁻¹(U))`, and every section of `X` over `f⁻¹(U)` is integral over `Γ(S, U)` by
`AlgebraicGeometry.isIntegral_app_of_universallyClosed`.

This is the local input to [Stacks, Tag 03GQ]. -/
theorem isIso_toNormalization_app (f : X ⟶ S) [UniversallyClosed f] [QuasiSeparated f]
    {U : S.Opens} (hU : IsAffineOpen U) :
    IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
  let _ : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(S, U) Γ(X, f ⁻¹ᵁ U) := by
    rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact isIntegral_app_of_universallyClosed f hU
  have hval : IsIso (CommRingCat.ofHom
      (Subalgebra.val (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))).toRingHom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, Algebra.IsIntegral.isIntegral x⟩, rfl⟩⟩
  have e₂ : f ⁻¹ᵁ U = f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  have key : IsIso (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) e₂.le) := by
    rw [← f.normalizationObjIso_hom_val hU]
    infer_instance
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ _ rfl e₂ (fun g ↦ IsIso g)).mp key

end Scheme.Hom

end AlgebraicGeometry

end
