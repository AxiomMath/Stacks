module

public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Transfer

/-!
# The normalization stalk is a localization of the sections over an affine preimage

Let `ν : X^ν → X` be the normalization of a scheme whose quasi-compact opens have finitely many
irreducible components. The stalk of `ν_* 𝒪_{X^ν}` at a point `x` of an affine open `U` is the
localization of `Γ(X^ν, ν⁻¹U)` at the image of the prime of `Γ(X, U)` that `x` determines.

## Main results

* `Stacks.NormalizationStalkAmbient.isLocalization_normalizationPushforwardStalk`: the stalk of
  `ν_* 𝒪_{X^ν}` at `x ∈ U` is a localization of `Γ(X^ν, ν⁻¹U)`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.NormalizationStalkAmbient

/-- The stalk at `x` of the pushforward of the structure sheaf of the normalization is the
localization of the sections of the normalization over the preimage of an affine open `U ∋ x`, at
the image of the prime of `Γ(X, U)` corresponding to `x`. -/
public theorem isLocalization_normalizationPushforwardStalk (X : Scheme.{u})
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI ν := Scheme.normalization X hX
    letI : Algebra Γ(X, U) Γ(Scheme.normalizationScheme X hX, ν ⁻¹ᵁ U) :=
      (ν.app U).hom.toAlgebra
    letI : Algebra Γ(Scheme.normalizationScheme X hX, ν ⁻¹ᵁ U)
        (normalizationPushforwardStalk X hX x) :=
      ((ν.base _* (Scheme.normalizationScheme X hX).presheaf).germ U x hx).hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid
        Γ(Scheme.normalizationScheme X hX, ν ⁻¹ᵁ U)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (normalizationPushforwardStalk X hX x) :=
  hU.isLocalization_pushforwardStalk (Scheme.normalization X hX) hx

end Stacks.NormalizationStalkAmbient

end
