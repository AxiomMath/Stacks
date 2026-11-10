module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCompactSupportVanishing

/-!
# The Artin–Schreier cover of `t^q - t = σ x` on the affine line is an affine line

Let `k` be a finite field with `q` elements and `F` a field over `k`. For a unit `σ` of `F`, the
Artin–Schreier cover `T^q - T = σ x` of the affine line `𝔸¹_F = Spec F[x]` is again an affine
line: `F[x][T]/(T^q - T - σ x) ≅ F[T]`, by `T ↦ T` and `x ↦ σ⁻¹ (T^q - T)`
(`Stacks.ArtinSchreier.scaledAffineLineRingEquiv`). In particular the cover is irreducible, so
the Artin–Schreier sheaf `L_ψ(σ x)` on any nonempty open of `𝔸¹_F` comes from a connected cover.

## Main definitions

* `Stacks.ArtinSchreier.scaledAffineLineASMap`: `x ↦ σ⁻¹ (x^q - x)` on `F[x]`.
* `Stacks.ArtinSchreier.scaledAffineLineRingEquiv`: `F[x][T]/(T^q - T - σ x) ≅ F[T]`.

## Main results

* `Stacks.ArtinSchreier.isDomain_ring_scaledAffineLine`.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {F : Type v} [Field F] [Algebra k F] (σ : Fˣ)

/-- `x ↦ σ⁻¹ (x^q - x)` on `F[x]`. -/
abbrev scaledAffineLineASMap : F[X] →ₐ[F] F[X] :=
  aeval (C (σ⁻¹ : Fˣ).1 * ((Polynomial.X : F[X]) ^ Fintype.card k - Polynomial.X))

omit [Field k] [Algebra k F] in
/-- Applying `x ↦ σ⁻¹ (x^q - x)` to the coefficients of `T^q - T - σ x` gives a polynomial over
`F[x]` with root `x`. -/
theorem eval₂_poly_scaledAffineLineASMap :
    (poly k (C σ.1 * Polynomial.X : F[X])).eval₂ (scaledAffineLineASMap k σ : F[X] →+* F[X])
      Polynomial.X = 0 := by
  simp only [poly, eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X, eval₂_C]
  change Polynomial.X ^ Fintype.card k - (Polynomial.X +
    aeval (C (σ⁻¹ : Fˣ).1 * ((Polynomial.X : F[X]) ^ Fintype.card k - Polynomial.X))
      (C σ.1 * Polynomial.X)) = 0
  rw [map_mul, aeval_C, aeval_X, algebraMap_eq, ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
  ring

omit [Field k] [Algebra k F] in
/-- `root^q - root = σ x` in `F[x][T]/(T^q - T - σ x)`. -/
theorem root_pow_card_sub_root_scaled :
    AdjoinRoot.root (poly k (C σ.1 * Polynomial.X : F[X])) ^ Fintype.card k -
        AdjoinRoot.root (poly k (C σ.1 * Polynomial.X : F[X])) =
      AdjoinRoot.of (poly k (C σ.1 * Polynomial.X : F[X])) (C σ.1 * Polynomial.X) := by
  have h : AdjoinRoot.mk (poly k (C σ.1 * Polynomial.X : F[X]))
      ((Polynomial.X : (F[X])[X]) ^ Fintype.card k - (Polynomial.X + C (C σ.1 * Polynomial.X))) =
        0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  linear_combination h

/-- **The Artin–Schreier cover `T^q - T = σ x` of the affine line is an affine line**:
`F[x][T]/(T^q - T - σ x) ≅ F[T]`, `T ↦ T`, `x ↦ σ⁻¹ (T^q - T)`. -/
def scaledAffineLineRingEquiv : Ring k (C σ.1 * Polynomial.X : F[X]) ≃ₐ[F] F[X] :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom _ (scaledAffineLineASMap k σ) Polynomial.X
      (eval₂_poly_scaledAffineLineASMap k σ))
    (aeval (AdjoinRoot.root (poly k (C σ.1 * Polynomial.X : F[X]))))
    (by
      apply Polynomial.algHom_ext
      simp)
    (by
      apply AdjoinRoot.algHom_ext'
      · apply Polynomial.algHom_ext
        change (aeval (AdjoinRoot.root (poly k (C σ.1 * Polynomial.X : F[X]))))
            ((AdjoinRoot.liftAlgHom _ (scaledAffineLineASMap k σ) Polynomial.X
              (eval₂_poly_scaledAffineLineASMap k σ)) (AdjoinRoot.of _ Polynomial.X)) =
          AdjoinRoot.of _ Polynomial.X
        rw [AdjoinRoot.liftAlgHom_of, scaledAffineLineASMap, aeval_X, map_mul, aeval_C,
          map_sub, map_pow, aeval_X, root_pow_card_sub_root_scaled,
          IsScalarTower.algebraMap_apply F F[X] (AdjoinRoot _), AdjoinRoot.algebraMap_eq,
          Polynomial.algebraMap_eq, ← map_mul, ← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]
      · simp)

omit [Field k] [Algebra k F] in
/-- **The Artin–Schreier algebra of `σ x` over `F[x]` is a domain**, being a polynomial ring. -/
theorem isDomain_ring_scaledAffineLine : IsDomain (Ring k (C σ.1 * Polynomial.X : F[X])) :=
  (scaledAffineLineRingEquiv k σ).toMulEquiv.isDomain

end Stacks.ArtinSchreier

end
