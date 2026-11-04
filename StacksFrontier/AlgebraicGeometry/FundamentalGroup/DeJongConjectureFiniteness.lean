module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DeJongConjecture
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.SpecialFibre

/-!
# Finiteness of the universal deformation ring of a residual representation of `π₁` of a curve

Let `X` be a smooth, geometrically irreducible, projective curve over a finite field `k`, let
`X'` be a base change of `X` to an algebraically closed extension `K` of `k`, and let
`ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` be a continuous representation, `ℓ` a prime not dividing `n`, whose
restriction to `π₁(X')` is absolutely irreducible. Assume de Jong's conjecture for `X`: every
continuous representation `π₁(X) → GL_m(𝐅_ℓ⟦t⟧)`, of any rank `m`, has finite image on `π₁(X')`.
Then the universal deformation ring of `ρ₀` with determinant fixed to a character `δ` lifting
`det ρ₀` is finite over `ℤ_[ℓ]`.

This is the finiteness half of [Stacks, Tag 03W1]. It is the specialization of
`Deformation.IsUniversalFixedDeterminantDeformation.moduleFinite_of_finite_image` to the image
of `π₁(X') → π₁(X)`, whose normality (part of the exactness of Stacks 0BTX) is the hypothesis
`hnormal` of the present statement.

## Main results

* `AlgebraicGeometry.moduleFinite_of_isUniversalFixedDeterminantDeformation_of_normal`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped PowerSeries.WithPiTopology

universe u v

namespace AlgebraicGeometry

/-- **Finiteness half of Stacks 03W1, given the normality of the geometric fundamental group.**
Under de Jong's conjecture for `X` in every rank, the universal deformation ring of `ρ₀` with
determinant fixed to `δ` is finite over `ℤ_[ℓ]`, provided the image of `π₁(X') → π₁(X)` is
normal. -/
theorem moduleFinite_of_isUniversalFixedDeterminantDeformation_of_normal
    (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K] [IsAlgClosed K]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (_hℓp : ℓ ≠ p) (hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    (X' : Scheme.{u}) (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (_hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] (x : GeometricPoint X')
    (ρ₀ : EtaleFundamentalGroup X (x.map q) →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (δ : EtaleFundamentalGroup X (x.map q) →ₜ* ℤ_[ℓ]ˣ)
    (hconj : ∀ (m : ℕ) (ρ : EtaleFundamentalGroup X (x.map q) →ₜ*
        Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (Set.range fun g : EtaleFundamentalGroup X' x => ρ (etaleFundamentalGroupMap q x g)).Finite)
    (hirred : Deformation.IsAbsolutelyIrreducible
      fun g : EtaleFundamentalGroup X' x => ρ₀ (etaleFundamentalGroupMap q x g))
    (hnormal : (etaleFundamentalGroupMap q x).toMonoidHom.range.Normal)
    (R : Type v) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
    (reduce : R →+* ZMod ℓ)
    (ρuniv : EtaleFundamentalGroup X (x.map q) →ₜ* Matrix.GeneralLinearGroup (Fin n) R)
    (hR : Deformation.IsUniversalFixedDeterminantDeformation ℓ n _ ρ₀ δ R reduce ρuniv) :
    Module.Finite ℤ_[ℓ] R := by
  set N := (etaleFundamentalGroupMap q x).toMonoidHom.range
  have hrange : ∀ {β : Type} (φ : EtaleFundamentalGroup X (x.map q) → β),
      Set.range (fun g : N => φ g) =
        Set.range fun g : EtaleFundamentalGroup X' x => φ (etaleFundamentalGroupMap q x g) :=
    fun φ => Set.ext fun _ =>
      ⟨fun ⟨⟨_, g, rfl⟩, h⟩ => ⟨g, h⟩, fun ⟨g, h⟩ => ⟨⟨_, g, rfl⟩, h⟩⟩
  refine hR.moduleFinite_of_finite_image N ?_ hn fun m ρ => ?_
  · unfold Deformation.IsAbsolutelyIrreducible at hirred ⊢
    have := hrange fun g => (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))
    simp only at this ⊢
    rwa [this]
  · rw [Set.image_eq_range]
    exact (hrange ρ).symm ▸ hconj m ρ

end AlgebraicGeometry
