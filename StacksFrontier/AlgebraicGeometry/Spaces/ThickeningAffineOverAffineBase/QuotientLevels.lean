module

public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.PresentationLift

/-!
# The closed subobjects `Spec(A/K)` of an affine object of the site

For an affine object `T` of the big fppf site of `S`, with ring of functions `A`, and an ideal
`K ⊆ A`, the spectrum `Spec(A/K)` is an object of the site over `T`, and its structure morphism
`T_K ⟶ T` is a closed immersion whose kernel on functions is `K`.  A morphism `T₀ ⟶ T` from an
affine object whose kernel on functions contains `K` factors through `T_K`, and for a nilpotent
`K` the closed immersion is a finite-order thickening.

## Main definitions

* `AlgebraicGeometry.Space.quotientLevel`: the object `T_K = Spec(A/K)` of the site.
* `AlgebraicGeometry.Space.quotientLevelι`: its structure morphism `T_K ⟶ T`.

## Main results

* `AlgebraicGeometry.Space.ker_appTop_quotientLevelι`: the kernel on functions is `K`.
* `AlgebraicGeometry.Space.exists_factor_quotientLevelι`: the factorization.
* `AlgebraicGeometry.Space.isFiniteOrderThickening_quotientLevelι`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- For an ideal `K` of the ring of functions `A` of `T`, the site contains `Spec(A/K)`. -/
theorem contains_quotientLevel (K : Ideal (affineBaseRing B S hS T)) :
    B.Contains (Spec (CommRingCat.of (affineBaseRing B S hS T ⧸ K))) :=
  B.contains_specQuotient (contains_spec_affineBaseRing B S hS T) K

/-- The closed subobject `T_K = Spec(A/K)` of an affine object `T` of the site. -/
abbrev quotientLevel (K : Ideal (affineBaseRing B S hS T)) : BigFppfOver B S hS :=
  specOverAffineBase B S hS T (affineBaseRing B S hS T ⧸ K) (contains_quotientLevel B S hS T K)

/-- The structure morphism `T_K ⟶ T`. -/
abbrev quotientLevelι (K : Ideal (affineBaseRing B S hS T)) : quotientLevel B S hS T K ⟶ T :=
  specOverAffineBaseToBase B S hS (affineBaseRing B S hS T ⧸ K) (contains_quotientLevel B S hS T K)

/-- The underlying morphism of schemes of `T_K ⟶ T` is `Spec(A/K) ⟶ Spec A` followed by the
inverse of the isomorphism `T ≅ Spec A`. -/
theorem toScheme_map_quotientLevelι (K : Ideal (affineBaseRing B S hS T)) :
    (BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K) =
      specQuotientMk K ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv :=
  rfl

/-- The underlying morphism of schemes of `T_K ⟶ T` is a closed immersion. -/
instance isClosedImmersion_quotientLevelι (K : Ideal (affineBaseRing B S hS T)) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K)) := by
  rw [toScheme_map_quotientLevelι]
  exact isClosedImmersion_specQuotientToBase _ K

/-- The kernel of the map on global sections induced by `T_K ⟶ T` is `K`. -/
theorem ker_appTop_quotientLevelι (K : Ideal (affineBaseRing B S hS T)) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K)).appTop.hom =
      K := by
  rw [toScheme_map_quotientLevelι]
  exact ker_appTop_specQuotientToBase _ K

/-- **A morphism from an object of the site whose kernel on functions contains `K` factors
through `T_K`.** -/
theorem exists_factor_quotientLevelι (K : Ideal (affineBaseRing B S hS T))
    {T₀ : BigFppfOver B S hS}
    (k : T₀ ⟶ T) (hK : K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom) :
    ∃ j : T₀ ⟶ quotientLevel B S hS T K, j ≫ quotientLevelι B S hS T K = k :=
  exists_comp_eq_of_ker_le B S hS (quotientLevelι B S hS T K) k inferInstance
    ((Scheme.ker_le_ker_iff_of_isAffine _ _).2
      ((ker_appTop_quotientLevelι B S hS T K).le.trans hK))

/-- **For a nilpotent `K` the closed immersion `T_K ⟶ T` is a finite-order thickening.** -/
theorem isFiniteOrderThickening_quotientLevelι (K : Ideal (affineBaseRing B S hS T)) (n : ℕ)
    (hn : K ^ (n + 1) = ⊥) :
    Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K)) := by
  refine ⟨inferInstance, n, ?_⟩
  rw [Scheme.ker_of_isAffine, ker_appTop_quotientLevelι]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ofIdealTop_ideal,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← Ideal.map_pow, hn, Ideal.map_bot]

end AlgebraicGeometry.Space

end
