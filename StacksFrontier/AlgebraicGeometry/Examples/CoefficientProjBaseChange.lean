module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Examples.CoefficientProjFamily
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of the coefficientwise projective family

Extending the coefficients of a coefficientwise ideal along `R → S` gives the coefficientwise
ideal of the extended family, so the base change of the quotient attached to `K` is the quotient
attached to the extended coefficients, as graded rings.

## Main definitions

* `Stacks.CoefficientProj.baseChange`: the coefficientwise family with extended coefficients.
* `Stacks.CoefficientProj.baseChangeAlgEquiv`: the comparison of the base-changed quotient with
  the quotient over the extended base.
* `Stacks.CoefficientProj.baseChangeGradedHom` and `Stacks.CoefficientProj.baseChangeGradedInv`:
  that comparison as mutually inverse homomorphisms of graded rings.

## Main results

* `Stacks.CoefficientProj.coefficientIdeal_map`: the extension of `coefficientIdeal K` along
  `R → S` is `coefficientIdeal (baseChange K S)`.
-/

@[expose] public noncomputable section

namespace Stacks.CoefficientProj

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization TensorProduct
open Stacks.GradedModel CommRingCat

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {m : ℕ} {R : Type u} [CommRing R] (K : (Fin (m + 1) →₀ ℕ) → Ideal R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The coefficientwise family with coefficients extended along `R → S`. -/
def baseChange : (Fin (m + 1) →₀ ℕ) → Ideal S := fun d => (K d).map (algebraMap R S)

/-- The extension of a monotone coefficientwise family is monotone. -/
theorem monotone_baseChange (hK : Monotone K) : Monotone (baseChange K S) :=
  fun _ _ h => Ideal.map_mono (hK h)

/-- If `K 0 = ⊥`, then the extended family also vanishes at `0`. -/
theorem baseChange_zero (hK0 : K 0 = ⊥) : baseChange K S 0 = ⊥ := by
  simp [baseChange, hK0]

/-- The image of `coefficientIdeal K` under `MvPolynomial.map (algebraMap R S)` generates the
coefficientwise ideal of `baseChange K S`. -/
theorem coefficientIdeal_map :
    (coefficientIdeal K).map (MvPolynomial.map (algebraMap R S)) =
      coefficientIdeal (baseChange K S) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr ?_) ?_
  · rw [coefficientIdeal, Ideal.span_le]
    rintro q ⟨d, a, ha, rfl⟩
    refine Ideal.mem_comap.mpr ?_
    rw [MvPolynomial.map_monomial]
    exact monomial_mem_coefficientIdeal _ (Ideal.mem_map_of_mem _ ha)
  · rw [coefficientIdeal, Ideal.span_le]
    rintro q ⟨d, b, hb, rfl⟩
    refine Submodule.span_induction (p := fun b _ => monomial d b ∈
      (coefficientIdeal K).map (MvPolynomial.map (algebraMap R S))) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨a, ha, rfl⟩
      exact MvPolynomial.map_monomial (algebraMap R S) d a ▸
        Ideal.mem_map_of_mem _ (monomial_mem_coefficientIdeal K ha)
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy
    · intro c x _ hx
      rw [smul_eq_mul, ← C_mul_monomial]
      exact Ideal.mul_mem_left _ _ hx

/-- The coefficientwise ideal over the extended base is the image of the one over `R` under the
comparison of the base-changed polynomial ring with the polynomial ring over `S`. -/
theorem coefficientIdeal_baseChange_eq_map :
    coefficientIdeal (baseChange K S) =
      Ideal.map (MvPolynomial.algebraTensorAlgEquiv R S)
        (Ideal.map (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin (m + 1)) R →ₐ[R] S ⊗[R] MvPolynomial (Fin (m + 1)) R)
          (coefficientIdeal K)) := by
  have hgf : (MvPolynomial.algebraTensorAlgEquiv R S).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom =
        MvPolynomial.map (algebraMap R S) :=
    RingHom.ext fun p : MvPolynomial (Fin (m + 1)) R => by
      change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] p) = _
      simp
  rw [← coefficientIdeal_map K S, ← hgf, ← Ideal.map_map]
  rfl

/-- The base change of the quotient is the quotient over the extended base. -/
def baseChangeAlgEquiv :
    S ⊗[R] (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) ≃ₐ[S]
      MvPolynomial (Fin (m + 1)) S ⧸ coefficientIdeal (baseChange K S) :=
  (Algebra.TensorProduct.tensorQuotientEquiv S _ S (coefficientIdeal K)).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
      (coefficientIdeal_baseChange_eq_map K S))

/-- `baseChangeAlgEquiv K S` sends `s ⊗ₜ [p]` to the class of
`C s * MvPolynomial.map (algebraMap R S) p`. -/
@[simp]
theorem baseChangeAlgEquiv_tmul (s : S) (p : MvPolynomial (Fin (m + 1)) R) :
    baseChangeAlgEquiv K S (s ⊗ₜ[R] Ideal.Quotient.mk (coefficientIdeal K) p) =
      Ideal.Quotient.mk _ (C s * MvPolynomial.map (algebraMap R S) p) := by
  show Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
      (coefficientIdeal_baseChange_eq_map K S)
      (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial (Fin (m + 1)) R) S
        (coefficientIdeal K) (s ⊗ₜ[R] Ideal.Quotient.mk (coefficientIdeal K) p)) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  show Ideal.Quotient.mk _ (MvPolynomial.algebraTensorAlgEquiv R S (s ⊗ₜ[R] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, smul_eq_C_mul]

/-- The comparison of the base-changed quotient with the quotient over the extended base,
as a homomorphism of graded rings. -/
def baseChangeGradedHom :
    Stacks.ProjBaseChange.grading (projGrading K) S →+*ᵍ projGrading (baseChange K S) where
  __ := (baseChangeAlgEquiv K S).toRingEquiv.toRingHom
  map_mem := by
    intro i x hx
    have hx' : x ∈ Submodule.span S
        ((projGrading K i).map ((TensorProduct.mk R S _) 1)) := by
      rw [← Submodule.baseChange_eq_span]; exact hx
    refine Submodule.span_induction (p := fun x _ => baseChangeAlgEquiv K S x ∈
      projGrading (baseChange K S) i) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hb
      refine ⟨MvPolynomial.map (algebraMap R S) p, ?_, ?_⟩
      · exact (mem_homogeneousSubmodule i _).2 (((mem_homogeneousSubmodule i p).1 hp).map _)
      · change _ = baseChangeAlgEquiv K S (1 ⊗ₜ[R] Ideal.Quotient.mk (coefficientIdeal K) p)
        rw [baseChangeAlgEquiv_tmul, map_one, one_mul]
        rfl
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx

/-- The inverse comparison, as a homomorphism of graded rings. -/
def baseChangeGradedInv :
    projGrading (baseChange K S) →+*ᵍ Stacks.ProjBaseChange.grading (projGrading K) S where
  __ := (baseChangeAlgEquiv K S).symm.toRingEquiv.toRingHom
  map_mem := by
    classical
    rintro i _ ⟨q, hq, rfl⟩
    have hq' : q.IsHomogeneous i := (mem_homogeneousSubmodule i q).1 hq
    set z : S ⊗[R] (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) :=
      ∑ d ∈ q.support, coeff d q ⊗ₜ[R] Ideal.Quotient.mk (coefficientIdeal K) (monomial d 1)
      with hzdef
    have hz : baseChangeAlgEquiv K S z = Ideal.Quotient.mk _ q := by
      rw [hzdef, map_sum]
      simp only [baseChangeAlgEquiv_tmul, MvPolynomial.map_monomial, map_one, C_mul_monomial,
        mul_one]
      rw [← map_sum, q.support_sum_monomial_coeff]
    have hmem : z ∈ Stacks.ProjBaseChange.grading (projGrading K) S i := by
      refine Submodule.sum_mem _ fun d hd => Submodule.tmul_mem_baseChange_of_mem _ ⟨monomial d 1,
        (mem_homogeneousSubmodule i _).2 (isHomogeneous_monomial 1 ?_), rfl⟩
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (hq'.coeff_eq_zero hne)
    change (baseChangeAlgEquiv K S).symm (Ideal.Quotient.mk _ q) ∈ _
    rw [← hz, AlgEquiv.symm_apply_apply]
    exact hmem

end Stacks.CoefficientProj

end
