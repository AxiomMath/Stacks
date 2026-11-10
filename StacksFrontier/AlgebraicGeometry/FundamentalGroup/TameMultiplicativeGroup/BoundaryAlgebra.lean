module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksFrontier.RingTheory.Polynomial.EverywhereUnramifiedDegree

/-!
# Algebra at the boundary of `𝐆_m`

Two elementary facts of commutative algebra about local rings and polynomial rings in one
transcendental element.

* Over a local ring `O`, `(1 + π r)⁻¹` is integral for `π` in the maximal ideal and `r` integral:
  `1 + π r` lies in no maximal ideal of the integral closure, since those contract to the maximal
  ideal of `O`.
* For `s` transcendental over `F`, the ring `F[s]` is a polynomial ring, `s` is irreducible in it,
  and evaluation at `s = 0` is an `F`-algebra map `F[s] → F`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.isIntegral_inv_one_add_mul`: `(1 + π r)⁻¹` is integral
  over a local ring `O` for `π` in the maximal ideal and `r` integral over `O`.
* `AlgebraicGeometry.TameMultiplicativeGroup.irreducible_adjoinGen`: a transcendental `s` is
  irreducible in `F[s]`.
* `AlgebraicGeometry.TameMultiplicativeGroup.evalZero`: evaluation at `s = 0` as an `F`-algebra map
  `F[s] → F`.
-/

@[expose] public noncomputable section

open Polynomial

namespace AlgebraicGeometry.TameMultiplicativeGroup

/-- **Inverting `1 + π r` keeps integrality** over a local ring, for `π` in the maximal ideal. -/
theorem isIntegral_inv_one_add_mul {O L : Type*} [CommRing O] [IsLocalRing O] [Field L]
    [Algebra O L] {π : O} (hπ : π ∈ IsLocalRing.maximalIdeal O) {r : L}
    (hr : _root_.IsIntegral O r) : _root_.IsIntegral O (1 + algebraMap O L π * r)⁻¹ := by
  let y : integralClosure O L := 1 + algebraMap O (integralClosure O L) π * ⟨r, hr⟩
  have hy : IsUnit y := by
    by_contra h
    obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal (Ideal.span {y})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hπM : algebraMap O (integralClosure O L) π ∈ M := by
      rwa [← Ideal.mem_under,
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M)]
    have h1 : (1 : integralClosure O L) ∈ M := by
      have := M.sub_mem (hyM (Ideal.mem_span_singleton_self y))
        (M.mul_mem_right (⟨r, hr⟩ : integralClosure O L) hπM)
      rwa [add_sub_cancel_right] at this
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨z, hz⟩ := hy.exists_right_inv
  have hz' : (1 + algebraMap O L π * r) * (z : L) = 1 := congrArg Subtype.val hz
  rw [← eq_inv_of_mul_eq_one_right hz']
  exact z.2

section Adjoin

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {s : K}

variable (F) in
/-- `s` as an element of `F[s]`. -/
abbrev adjoinGen (s : K) : Algebra.adjoin F {s} := ⟨s, Algebra.self_mem_adjoin_singleton F s⟩

/-- For `s` transcendental over `F`, the isomorphism `F[X] ≃ₐ[F] F[s]` sends `X` to `s`. -/
theorem adjoinSingletonEquiv_X (hs : Transcendental F s) :
    Polynomial.adjoinSingletonEquiv F hs X = adjoinGen F s :=
  Subtype.ext (aeval_X s)

/-- `s` is irreducible in `F[s]`. -/
theorem irreducible_adjoinGen (hs : Transcendental F s) : Irreducible (adjoinGen F s) := by
  rw [← adjoinSingletonEquiv_X hs]
  exact (MulEquiv.irreducible_iff (Polynomial.adjoinSingletonEquiv F hs)).mpr irreducible_X

/-- **Evaluation at `s = 0`**, `F[s] → F`. -/
def evalZero (hs : Transcendental F s) : Algebra.adjoin F {s} →ₐ[F] F :=
  (aeval (0 : F)).comp (Polynomial.adjoinSingletonEquiv F hs).symm.toAlgHom

/-- Evaluation at `s = 0` sends `s` to `0`. -/
theorem evalZero_adjoinGen (hs : Transcendental F s) : evalZero hs (adjoinGen F s) = 0 := by
  rw [evalZero, AlgHom.comp_apply, ← adjoinSingletonEquiv_X hs,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, aeval_X]

end Adjoin

end AlgebraicGeometry.TameMultiplicativeGroup

end
