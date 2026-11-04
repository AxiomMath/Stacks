module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical morphism to the spectrum of the global sections is scheme-theoretically surjective

Let `X` be a scheme and let `f : X ⟶ S = Spec Γ(X, 𝒪_X)` be the canonical morphism, which is
`AlgebraicGeometry.Scheme.toSpecΓ`. The largest quasi-coherent `𝒪_S`-submodule of
`ker (f^♯ : 𝒪_S ⟶ f_* 𝒪_X)` is zero; if `X` is quasi-compact, then `f^♯` is injective and `f` is
dominant.

## Main results

* `AlgebraicGeometry.ker_toSpecΓ_eq_bot`: the largest quasi-coherent ideal sheaf contained in
  `ker f^♯` is zero, with no hypothesis on `X`.
* `AlgebraicGeometry.eq_bot_of_le_ker_toSpecΓ`: the same statement spelled out as a universal
  property: a quasi-coherent ideal sheaf on `S` all of whose sections are killed by `f^♯` is zero.
* `AlgebraicGeometry.toSpecΓ_app_injective`: for quasi-compact `X`, the map `f^♯` is injective on
  sections over every open of `S`.
* `AlgebraicGeometry.isDominant_toSpecΓ`: for quasi-compact `X`, the morphism `f` is dominant.

## References

* [Stacks Project, Tag 0H2R](https://stacks.math.columbia.edu/tag/0H2R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The largest quasi-coherent `𝒪_S`-module contained in the kernel of
`f^♯ : 𝒪_S ⟶ f_* 𝒪_X`, for `f : X ⟶ S = Spec Γ(X, 𝒪_X)` the canonical morphism, is zero. -/
@[stacks 0H2R "the largest quasi-coherent submodule of `ker f^♯` is zero"]
theorem ker_toSpecΓ_eq_bot : X.toSpecΓ.ker = ⊥ := by
  have hker : RingHom.ker (X.toSpecΓ.appTop).hom = ⊥ := by
    rw [Scheme.toSpecΓ_appTop]
    simpa using RingHom.ker_coe_equiv (Scheme.ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv
  rw [Scheme.ker_of_isAffine, hker]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp

/-- A quasi-coherent ideal sheaf on `S = Spec Γ(X, 𝒪_X)` whose sections over every affine open are
killed by `f^♯` is zero. -/
@[stacks 0H2R "the largest quasi-coherent submodule of `ker f^♯` is zero, universal form"]
theorem eq_bot_of_le_ker_toSpecΓ {I : (Spec Γ(X, ⊤)).IdealSheafData}
    (hI : ∀ U, I.ideal U ≤ RingHom.ker (X.toSpecΓ.app U).hom) : I = ⊥ :=
  le_bot_iff.mp (ker_toSpecΓ_eq_bot X ▸ Scheme.IdealSheafData.le_ofIdeals_iff.mpr hI)

/-- The canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)` is scheme-theoretically dominant, equivalently
scheme-theoretically surjective. -/
instance isSchemeTheoreticallyDominant_toSpecΓ :
    IsSchemeTheoreticallyDominant X.toSpecΓ :=
  ⟨ker_toSpecΓ_eq_bot X⟩

/-- If `X` is quasi-compact then `f^♯ : 𝒪_S ⟶ f_* 𝒪_X` is injective, for
`f : X ⟶ S = Spec Γ(X, 𝒪_X)` the canonical morphism: it is injective on the sections over every
open of `S`. -/
@[stacks 0H2R "if `X` is quasi-compact then `f^♯` is injective"]
theorem toSpecΓ_app_injective [CompactSpace X] (U : (Spec Γ(X, ⊤)).Opens) :
    Function.Injective (X.toSpecΓ.app U) :=
  X.toSpecΓ.app_injective U

/-- If `X` is quasi-compact then the canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)` is dominant. -/
@[stacks 0H2R "if `X` is quasi-compact then `f` is dominant"]
theorem isDominant_toSpecΓ [CompactSpace X] : IsDominant X.toSpecΓ := inferInstance

end AlgebraicGeometry

end
