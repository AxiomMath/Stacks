module

public import StacksFrontier.RingTheory.NoetherNormalization.FiniteOverLine
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.FiniteStability

/-!
# The étale divisor meets every component of every geometric fibre

Let `B` be of finite type over `A`, `t ∈ B` and `a ∈ A` such that every element of `B` times a
power of `a` is integral over `A[X]` through `X ↦ t` (the finiteness half of
`Polynomial.exists_etale_divisor_of_locally_isStandardSmooth`). For a field `L` over `A` in which
`a` is invertible, `L ⊗[A] B` is finite over `L[X]` through `X ↦ 1 ⊗ t`; hence for `h ∈ A[X]`
monic of positive degree, every prime `P` of `L ⊗[A] B` with `dim (L ⊗[A] B) ⧸ P ≥ 1` (every
component of positive dimension of the fibre) lies under a prime containing `1 ⊗ h(t)`
(`Polynomial.exists_isPrime_le_aeval_mem_of_finite`).

This is the property of the divisor `V(h(t))` used for the surjectivity of the Gysin map of
`R² g_!` on the geometric fibres in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the divisor meets every component of
every geometric fibre.

## Main results

* `Polynomial.finite_aeval_one_tmul_of_isIntegralElem`: `L ⊗[A] B` is finite over `L[X]` through
  `X ↦ 1 ⊗ t`.
* `Polynomial.exists_isPrime_le_one_tmul_aeval_mem`: every prime `P` of `L ⊗[A] B` with
  `dim (L ⊗[A] B) ⧸ P ≥ 1` lies under a prime containing `1 ⊗ h(t)`.
-/

public section

open Polynomial TensorProduct

namespace Polynomial

variable {A B L : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field L] [Algebra A L]

/-- Evaluating `q` mapped to `L` at `1 ⊗ t` gives `1 ⊗ q(t)`. -/
private theorem aeval_one_tmul_map (t : B) (q : A[X]) :
    aeval ((1 : L) ⊗ₜ[A] t) (q.map (algebraMap A L)) = (1 : L) ⊗ₜ[A] aeval t q := by
  rw [aeval_map_algebraMap, show (1 : L) ⊗ₜ[A] t =
    (Algebra.TensorProduct.includeRight : B →ₐ[A] L ⊗[A] B) t from rfl, aeval_algHom_apply]
  rfl

/-- **The coordinate `t` is finite on the fibres over the points where `a` is invertible.** If
every element of `B` times a power of `a` is integral over `A[X]` through `X ↦ t`, and `a` is
invertible in the field `L`, then `L ⊗[A] B` is finite over `L[X]` through `X ↦ 1 ⊗ t`. -/
theorem finite_aeval_one_tmul_of_isIntegralElem [Algebra.FiniteType A B] (a : A) (t : B)
    (ha : IsUnit (algebraMap A L a))
    (hint : ∀ x : B, ∃ n : ℕ, (aeval t : A[X] →ₐ[A] B).toRingHom.IsIntegralElem (a ^ n • x)) :
    (aeval ((1 : L) ⊗ₜ[A] t) : L[X] →ₐ[L] L ⊗[A] B).Finite := by
  let : Algebra L[X] (L ⊗[A] B) := (aeval ((1 : L) ⊗ₜ[A] t)).toRingHom.toAlgebra
  have : IsScalarTower L L[X] (L ⊗[A] B) := IsScalarTower.of_algebraMap_eq fun c => by
    show _ = aeval ((1 : L) ⊗ₜ[A] t) (C c)
    rw [aeval_C]
  have hone : ∀ y : B, (aeval t : A[X] →ₐ[A] B).toRingHom.IsIntegralElem y →
      IsIntegral L[X] ((1 : L) ⊗ₜ[A] y) := by
    rintro y ⟨P, hPm, hP⟩
    refine ⟨P.map (mapRingHom (algebraMap A L)), hPm.map _, ?_⟩
    rw [eval₂_map]
    have : (algebraMap L[X] (L ⊗[A] B)).comp (mapRingHom (algebraMap A L)) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] L ⊗[A] B).toRingHom.comp
          (aeval t : A[X] →ₐ[A] B).toRingHom := by
      exact RingHom.ext fun q => aeval_one_tmul_map t q
    rw [this, show (1 : L) ⊗ₜ[A] y =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] L ⊗[A] B).toRingHom y from rfl,
      ← hom_eval₂, hP, map_zero]
  have : Algebra.IsIntegral L[X] (L ⊗[A] B) := ⟨fun z => by
    induction z using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul c x =>
      obtain ⟨n, hn⟩ := hint x
      obtain ⟨u, hu⟩ := ha
      have e : c ⊗ₜ[A] x = algebraMap L (L ⊗[A] B) (c * (u⁻¹ : Lˣ) ^ n) *
          ((1 : L) ⊗ₜ[A] (a ^ n • x)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, ← hu,
          Algebra.algebraMap_self, RingHom.id_apply, mul_left_comm, ← mul_pow, Units.mul_inv,
          one_pow, mul_one]
      rw [e, IsScalarTower.algebraMap_apply L L[X]]
      exact isIntegral_algebraMap.mul (hone _ hn)
    | add x y hx hy => exact hx.add hy⟩
  have : Algebra.FiniteType L[X] (L ⊗[A] B) :=
    Algebra.FiniteType.of_restrictScalars_finiteType L _ _
  exact Algebra.IsIntegral.finite

/-- **The divisor `V(1 ⊗ h(t))` meets every component of positive dimension of the fibre.** Under
the hypotheses of `Polynomial.finite_aeval_one_tmul_of_isIntegralElem`, for `h ∈ A[X]` monic of
positive degree, every prime `P` of `L ⊗[A] B` with `dim (L ⊗[A] B) ⧸ P ≥ 1` lies under a prime
`Q` containing `1 ⊗ h(t)`. -/
theorem exists_isPrime_le_one_tmul_aeval_mem [Algebra.FiniteType A B] (a : A) (t : B)
    (ha : IsUnit (algebraMap A L a))
    (hint : ∀ x : B, ∃ n : ℕ, (aeval t : A[X] →ₐ[A] B).toRingHom.IsIntegralElem (a ^ n • x))
    {h : A[X]} (hh : h.Monic) (hdeg : 0 < h.natDegree) (P : Ideal (L ⊗[A] B)) [P.IsPrime]
    (hdim : 1 ≤ ringKrullDim ((L ⊗[A] B) ⧸ P)) :
    ∃ Q : Ideal (L ⊗[A] B), Q.IsPrime ∧ P ≤ Q ∧ (1 : L) ⊗ₜ[A] aeval t h ∈ Q := by
  obtain ⟨Q, hQ, hPQ, hmem⟩ := exists_isPrime_le_aeval_mem_of_finite
    (finite_aeval_one_tmul_of_isIntegralElem a t ha hint) P hdim (hh.map (algebraMap A L))
    (by rwa [hh.natDegree_map])
  refine ⟨Q, hQ, hPQ, ?_⟩
  rwa [aeval_one_tmul_map] at hmem

end Polynomial
