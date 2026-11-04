module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.RestrictedPowerSeries.CoefficientIdeal
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# The completed tensor product with a restricted power series ring

Let `A → B` be a homomorphism of commutative rings, let `I` be a finitely generated ideal of
`A` whose extension `I · B` defines the topology of `B`, and let `A{σ}` be the restricted power
series ring over `A` for `I`.  The tensor product `B ⊗[A] A{σ}` carries the tensor product
topology of Tag 0AMU, which here is the adic topology of the extended ideal `I · (B ⊗[A] A{σ})`,
and the level `n` reduction identifies `(B ⊗[A] A{σ}) ⧸ (I · (B ⊗[A] A{σ})) ^ n` with the
polynomial ring `(B ⧸ (I · B) ^ n)[σ]`.  Passing to the limit, the completed tensor product
`B ⊗̂[A] A{σ}` is the restricted power series ring `B{σ}` over `B` for `I · B`.

## Main definitions

* `TopologicalRing.restrictedTensorInclusion`: the canonical map `B[σ] → B ⊗[A] A{σ}`.
* `TopologicalRing.restrictedTensorProjection`: the level `n` reduction
  `B ⊗[A] A{σ} → (B ⧸ (I · B) ^ n)[σ]`.
* `TopologicalRing.restrictedTensorIdeal`: the extended ideal `I · (B ⊗[A] A{σ})`.
* `TopologicalRing.completedTensorProductRestrictedEquiv`: the ring isomorphism
  `B ⊗̂[A] A{σ} ≃+* B{σ}`.

## Main results

* `TopologicalRing.ker_restrictedTensorProjection`: the kernel of the level `n` reduction is the
  `n`-th power of the extended ideal.
* `TopologicalRing.isAdic_restrictedTensorIdeal`: the tensor product topology on `B ⊗[A] A{σ}`
  is the adic topology of the extended ideal.

## Implementation notes

The tensor product topology is not a global instance, so it and its uniformity are supplied by
hand at every statement that needs them, as elsewhere in this directory.  The identification of
the completed tensor product with the restricted power series ring factors through
`AdicCompletionBridge.adicCompletionRingEquiv`, which compares the uniform completion of an
adic ring with its algebraic adic completion.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

namespace TopologicalRing

section

universe u v

open scoped TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The reduction of the coefficient map `A → B` modulo the `n`-th powers of `I` and of its
extension to `B`. -/
public noncomputable def coefficientQuotientMap (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ n →+* B ⧸ (I.map (algebraMap A B)) ^ n :=
  Ideal.quotientMap _ (algebraMap A B) (by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

@[simp]
private theorem coefficientQuotientMap_mk (I : Ideal A) (n : ℕ) (a : A) :
    coefficientQuotientMap (B := B) I n (Ideal.Quotient.mk (I ^ n) a) =
      Ideal.Quotient.mk _ (algebraMap A B a) := rfl

/-- The reductions of the coefficient map are compatible with the transition maps. -/
private theorem factor_comp_coefficientQuotientMap (I : Ideal A) {m n : ℕ}
    (h1 : (I.map (algebraMap A B)) ^ n ≤ (I.map (algebraMap A B)) ^ m) (h2 : I ^ n ≤ I ^ m) :
    (Ideal.Quotient.factor h1).comp (coefficientQuotientMap (B := B) I n) =
      (coefficientQuotientMap (B := B) I m).comp (Ideal.Quotient.factor h2) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/-- The structure map of the polynomial ring over a coefficient quotient of `B`. -/
private theorem algebraMap_mvPolynomial_quotient (I : Ideal A) (σ : Type v) (n : ℕ) (b : B) :
    algebraMap B (MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n)) b =
      MvPolynomial.C (Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n) b) := rfl

section Right

/-- Level `n` reduction of a restricted power series over `A` to a polynomial over the
corresponding coefficient quotient of `B`. -/
public noncomputable def restrictedLevelRight (I : Ideal A) (σ : Type v) (n : ℕ) :
    RestrictedPowerSeries I σ →ₐ[A] MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n) where
  toRingHom := (MvPolynomial.map (coefficientQuotientMap (B := B) I n)).comp
    (RestrictedPowerSeries.coefficientProjection I σ n)
  commutes' a := by
    change MvPolynomial.map (coefficientQuotientMap (B := B) I n)
      (RestrictedPowerSeries.coefficientProjection I σ n
        (algebraMap A (RestrictedPowerSeries I σ) a)) = _
    rw [RestrictedPowerSeries.coefficientProjection_algebraMap, MvPolynomial.map_C]
    rfl

@[simp]
private theorem restrictedLevelRight_apply (I : Ideal A) (σ : Type v) (n : ℕ)
    (f : RestrictedPowerSeries I σ) :
    restrictedLevelRight (B := B) I σ n f =
      MvPolynomial.map (coefficientQuotientMap (B := B) I n)
        (RestrictedPowerSeries.coefficientProjection I σ n f) := rfl

/-- The level `n` reduction `B ⊗[A] A{σ} → (B ⧸ (I · B) ^ n)[σ]`, multiplying the reduction of
the left factor by the coefficientwise reduction of the right factor. -/
public noncomputable def restrictedTensorProjection (I : Ideal A) (σ : Type v) (n : ℕ) :
    (B ⊗[A] RestrictedPowerSeries I σ) →ₐ[A]
      MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n) :=
  Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom A B (MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n)))
    (restrictedLevelRight I σ n)

/-- The level `n` reduction sends `b ⊗ f` to the image of `b` times the coefficientwise
reduction of `f`. -/
@[simp]
public theorem restrictedTensorProjection_tmul (I : Ideal A) (σ : Type v) (n : ℕ) (b : B)
    (f : RestrictedPowerSeries I σ) :
    restrictedTensorProjection I σ n (b ⊗ₜ[A] f) =
      algebraMap B (MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n)) b *
        MvPolynomial.map (coefficientQuotientMap (B := B) I n)
          (RestrictedPowerSeries.coefficientProjection I σ n f) :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

/-- The canonical map from the polynomial ring over `B` into `B ⊗[A] A{σ}`, sending each
variable to the corresponding variable of the right factor. -/
public noncomputable def restrictedTensorInclusion (I : Ideal A) (σ : Type v) :
    MvPolynomial σ B →ₐ[B] B ⊗[A] RestrictedPowerSeries I σ :=
  MvPolynomial.aeval fun i =>
    (1 : B) ⊗ₜ[A] RestrictedPowerSeries.polynomialRingHom I σ (MvPolynomial.X i)

@[simp]
private theorem restrictedTensorInclusion_X (I : Ideal A) (σ : Type v) (i : σ) :
    restrictedTensorInclusion I σ (MvPolynomial.X i) =
      (1 : B) ⊗ₜ[A] RestrictedPowerSeries.polynomialRingHom I σ (MvPolynomial.X i) := by
  simp [restrictedTensorInclusion]

@[simp]
private theorem restrictedTensorInclusion_C (I : Ideal A) (σ : Type v) (b : B) :
    restrictedTensorInclusion I σ (MvPolynomial.C b) =
      b ⊗ₜ[A] (1 : RestrictedPowerSeries I σ) := by
  show restrictedTensorInclusion I σ
    (algebraMap B (MvPolynomial σ B) b) = _
  rw [AlgHom.commutes]
  rfl

/-- On polynomials with coefficients from `A` the canonical inclusion is the inclusion of the
right factor. -/
private theorem restrictedTensorInclusion_map (I : Ideal A) (σ : Type v)
    (p : MvPolynomial σ A) :
    restrictedTensorInclusion I σ (MvPolynomial.map (algebraMap A B) p) =
      (1 : B) ⊗ₜ[A] RestrictedPowerSeries.polynomialRingHom I σ p := by
  have h : ((restrictedTensorInclusion I σ).toRingHom.comp
        (MvPolynomial.map (algebraMap A B))) =
      ((Algebra.TensorProduct.includeRight :
          RestrictedPowerSeries I σ →ₐ[A] B ⊗[A] RestrictedPowerSeries I σ).toRingHom.comp
        (RestrictedPowerSeries.polynomialRingHom I σ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · show restrictedTensorInclusion I σ
        (MvPolynomial.map (algebraMap A B) (MvPolynomial.C a)) = _
      rw [MvPolynomial.map_C, restrictedTensorInclusion_C]
      show algebraMap A B a ⊗ₜ[A] (1 : RestrictedPowerSeries I σ) =
        (1 : B) ⊗ₜ[A] RestrictedPowerSeries.polynomialRingHom I σ (MvPolynomial.C a)
      rw [show RestrictedPowerSeries.polynomialRingHom I σ (MvPolynomial.C a) =
        algebraMap A (RestrictedPowerSeries I σ) a from rfl]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    · show restrictedTensorInclusion I σ
        (MvPolynomial.map (algebraMap A B) (MvPolynomial.X i)) = _
      rw [MvPolynomial.map_X, restrictedTensorInclusion_X]
      rfl
  exact DFunLike.congr_fun h p

/-- The level `n` reduction pulls back along the canonical inclusion to coefficientwise
reduction of polynomials. -/
public theorem restrictedTensorProjection_comp_inclusion (I : Ideal A) (σ : Type v) (n : ℕ) :
    (restrictedTensorProjection I σ n).toRingHom.comp
        (restrictedTensorInclusion I σ).toRingHom =
      MvPolynomial.map (Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n)) := by
  refine MvPolynomial.ringHom_ext (fun b => ?_) (fun i => ?_)
  · show restrictedTensorProjection I σ n
      (restrictedTensorInclusion I σ (MvPolynomial.C b)) = _
    rw [restrictedTensorInclusion_C, restrictedTensorProjection_tmul, MvPolynomial.map_C,
      map_one, map_one, mul_one, algebraMap_mvPolynomial_quotient]
  · show restrictedTensorProjection I σ n
      (restrictedTensorInclusion I σ (MvPolynomial.X i)) = _
    rw [restrictedTensorInclusion_X, restrictedTensorProjection_tmul, MvPolynomial.map_X]
    rw [RestrictedPowerSeries.coefficientProjection_polynomialRingHom]
    simp

/-- The level `n` reduction is surjective. -/
public theorem restrictedTensorProjection_surjective (I : Ideal A) (σ : Type v) (n : ℕ) :
    Function.Surjective (restrictedTensorProjection (B := B) I σ n) := by
  intro q
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n)) Ideal.Quotient.mk_surjective q
  refine ⟨restrictedTensorInclusion I σ p, ?_⟩
  rw [← hp]
  exact DFunLike.congr_fun (restrictedTensorProjection_comp_inclusion I σ n) p

/-- The extended ideal `I · (B ⊗[A] A{σ})`, whose powers are the basic open ideals of the
tensor product topology. -/
public noncomputable abbrev restrictedTensorIdeal (I : Ideal A) (σ : Type v) :
    Ideal (B ⊗[A] RestrictedPowerSeries I σ) :=
  I.map (algebraMap A (B ⊗[A] RestrictedPowerSeries I σ))

private theorem restrictedTensorIdeal_pow (I : Ideal A) (σ : Type v) (n : ℕ) :
    (restrictedTensorIdeal (B := B) I σ) ^ n =
      (I ^ n).map (algebraMap A (B ⊗[A] RestrictedPowerSeries I σ)) :=
  (Ideal.map_pow _ _ _).symm

/-- The `n`-th power of the extended ideal is the extension of the `n`-th power of `I · B`
from the left factor. -/
private theorem map_left_eq_restrictedTensorIdeal_pow (I : Ideal A) (σ : Type v) (n : ℕ) :
    ((I.map (algebraMap A B)) ^ n).map
        (algebraMap B (B ⊗[A] RestrictedPowerSeries I σ)) =
      (restrictedTensorIdeal (B := B) I σ) ^ n := by
  rw [restrictedTensorIdeal_pow, ← Ideal.map_pow, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A B (B ⊗[A] RestrictedPowerSeries I σ)]

/-- The `n`-th power of the extended ideal is also the extension of the `n`-th power of the
coefficient ideal from the right factor. -/
private theorem map_right_eq_restrictedTensorIdeal_pow (I : Ideal A) (σ : Type v) (n : ℕ) :
    ((RestrictedPowerSeries.coefficientIdeal I σ) ^ n).map
        (Algebra.TensorProduct.includeRight :
          RestrictedPowerSeries I σ →ₐ[A] B ⊗[A] RestrictedPowerSeries I σ).toRingHom =
      (restrictedTensorIdeal (B := B) I σ) ^ n := by
  rw [restrictedTensorIdeal_pow, ← Ideal.map_pow, Ideal.map_map]
  congr 1
  refine RingHom.ext fun a => ?_
  exact (Algebra.TensorProduct.includeRight (R := A) (A := B)
    (B := RestrictedPowerSeries I σ)).commutes a

/-- The `n`-th power of the extended ideal is contained in the kernel of the level `n`
reduction. -/
private theorem restrictedTensorIdeal_pow_le_ker (I : Ideal A) (σ : Type v) (n : ℕ) :
    (restrictedTensorIdeal (B := B) I σ) ^ n ≤
      RingHom.ker (restrictedTensorProjection I σ n).toRingHom := by
  rw [← map_left_eq_restrictedTensorIdeal_pow I σ n, Ideal.map_le_iff_le_comap]
  intro b hb
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  show restrictedTensorProjection I σ n
    (algebraMap B (B ⊗[A] RestrictedPowerSeries I σ) b) = 0
  have hb0 : Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n) b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hb
  show restrictedTensorProjection I σ n (b ⊗ₜ[A] (1 : RestrictedPowerSeries I σ)) = 0
  rw [restrictedTensorProjection_tmul, map_one, map_one, mul_one,
    algebraMap_mvPolynomial_quotient, hb0, map_zero]

/-- Every element of `B ⊗[A] A{σ}` agrees, modulo the `n`-th power of the extended ideal, with
the image of a polynomial over `B`. -/
private theorem exists_inclusion_sub_mem (I : Ideal A) (hI : I.FG) (σ : Type v) (n : ℕ)
    (t : B ⊗[A] RestrictedPowerSeries I σ) :
    ∃ q : MvPolynomial σ B,
      t - restrictedTensorInclusion I σ q ∈ (restrictedTensorIdeal (B := B) I σ) ^ n := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul b f =>
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk (I ^ n))
      Ideal.Quotient.mk_surjective (RestrictedPowerSeries.coefficientProjection I σ n f)
    refine ⟨MvPolynomial.C b * MvPolynomial.map (algebraMap A B) p, ?_⟩
    have hmem : f - RestrictedPowerSeries.polynomialRingHom I σ p ∈
        (RestrictedPowerSeries.coefficientIdeal I σ) ^ n := by
      rw [RestrictedPowerSeries.mem_coefficientIdeal_pow_iff I hI σ n, map_sub,
        RestrictedPowerSeries.coefficientProjection_polynomialRingHom, hp, sub_self]
    have hright : (1 : B) ⊗ₜ[A] (f - RestrictedPowerSeries.polynomialRingHom I σ p) ∈
        (restrictedTensorIdeal (B := B) I σ) ^ n := by
      rw [← map_right_eq_restrictedTensorIdeal_pow I σ n]
      exact Ideal.mem_map_of_mem
        (Algebra.TensorProduct.includeRight :
          RestrictedPowerSeries I σ →ₐ[A] B ⊗[A] RestrictedPowerSeries I σ).toRingHom hmem
    have hb : b ⊗ₜ[A] f - restrictedTensorInclusion I σ
        (MvPolynomial.C b * MvPolynomial.map (algebraMap A B) p) =
        (b ⊗ₜ[A] (1 : RestrictedPowerSeries I σ)) *
          ((1 : B) ⊗ₜ[A] (f - RestrictedPowerSeries.polynomialRingHom I σ p)) := by
      rw [map_mul, restrictedTensorInclusion_C, restrictedTensorInclusion_map,
        TensorProduct.tmul_sub, mul_sub]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hb]
    exact Ideal.mul_mem_left _ _ hright
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    refine ⟨q₁ + q₂, ?_⟩
    have hsplit : t₁ + t₂ - restrictedTensorInclusion I σ (q₁ + q₂) =
        (t₁ - restrictedTensorInclusion I σ q₁) +
          (t₂ - restrictedTensorInclusion I σ q₂) := by
      rw [map_add]; ring
    rw [hsplit]
    exact Ideal.add_mem _ hq₁ hq₂

/-- The kernel of the level `n` reduction is the `n`-th power of the extended ideal. -/
public theorem ker_restrictedTensorProjection (I : Ideal A) (hI : I.FG) (σ : Type v) (n : ℕ) :
    RingHom.ker (restrictedTensorProjection (B := B) I σ n).toRingHom =
      (restrictedTensorIdeal (B := B) I σ) ^ n := by
  refine le_antisymm (fun t ht => ?_) (restrictedTensorIdeal_pow_le_ker I σ n)
  obtain ⟨q, hq⟩ := exists_inclusion_sub_mem I hI σ n t
  have hvq : restrictedTensorProjection I σ n (restrictedTensorInclusion I σ q) = 0 := by
    have h1 : restrictedTensorProjection I σ n t = 0 := ht
    have h2 : restrictedTensorProjection I σ n
        (t - restrictedTensorInclusion I σ q) = 0 :=
      restrictedTensorIdeal_pow_le_ker I σ n hq
    rw [map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact h2
  have hmapq : MvPolynomial.map (Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n)) q = 0 := by
    rw [← DFunLike.congr_fun (restrictedTensorProjection_comp_inclusion I σ n) q]
    exact hvq
  have hqmem : q ∈ ((I.map (algebraMap A B)) ^ n).map
      (MvPolynomial.C : B →+* MvPolynomial σ B) := by
    have h := RestrictedPowerSeries.polynomialQuotientEquiv_map_mk
      (I.map (algebraMap A B)) σ n q
    rw [hmapq, map_zero] at h
    have : q ∈ ((I.map (algebraMap A B)).map
        (MvPolynomial.C : B →+* MvPolynomial σ B)) ^ n :=
      Ideal.Quotient.eq_zero_iff_mem.mp h.symm
    rwa [← Ideal.map_pow] at this
  have hvmem : restrictedTensorInclusion I σ q ∈
      (restrictedTensorIdeal (B := B) I σ) ^ n := by
    rw [← map_left_eq_restrictedTensorIdeal_pow I σ n]
    have hcomp : (restrictedTensorInclusion I σ).toRingHom.comp
        (MvPolynomial.C : B →+* MvPolynomial σ B) =
        algebraMap B (B ⊗[A] RestrictedPowerSeries I σ) := by
      refine RingHom.ext fun b => ?_
      show restrictedTensorInclusion I σ (MvPolynomial.C b) = _
      rw [restrictedTensorInclusion_C]
      rfl
    have := Ideal.mem_map_of_mem (restrictedTensorInclusion I σ).toRingHom hqmem
    rwa [Ideal.map_map, hcomp] at this
  simpa using Ideal.add_mem _ hq hvmem

/-- The level `n` reduction identifies `(B ⊗[A] A{σ}) ⧸ (I · (B ⊗[A] A{σ})) ^ n` with the
polynomial ring `(B ⧸ (I · B) ^ n)[σ]`. -/
public noncomputable def restrictedTensorQuotientEquiv (I : Ideal A) (hI : I.FG) (σ : Type v)
    (n : ℕ) :
    (B ⊗[A] RestrictedPowerSeries I σ) ⧸ (restrictedTensorIdeal (B := B) I σ) ^ n ≃+*
      MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n) :=
  (Ideal.quotEquivOfEq (ker_restrictedTensorProjection I hI σ n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (restrictedTensorProjection_surjective I σ n))

@[simp]
private theorem restrictedTensorQuotientEquiv_mk (I : Ideal A) (hI : I.FG) (σ : Type v) (n : ℕ)
    (t : B ⊗[A] RestrictedPowerSeries I σ) :
    restrictedTensorQuotientEquiv I hI σ n (Ideal.Quotient.mk _ t) =
      restrictedTensorProjection I σ n t := rfl

/-- The identifications of the finite quotients are compatible with the transition maps. -/
private theorem restrictedTensorQuotientEquiv_transition (I : Ideal A) (hI : I.FG)
    (σ : Type v) {m n : ℕ} (hmn : m ≤ n)
    (x : (B ⊗[A] RestrictedPowerSeries I σ) ⧸ (restrictedTensorIdeal (B := B) I σ) ^ n) :
    RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
        (restrictedTensorQuotientEquiv I hI σ n x) =
      restrictedTensorQuotientEquiv I hI σ m
        (Ideal.Quotient.factorPow (restrictedTensorIdeal (B := B) I σ) hmn x) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hgen : ∀ t : B ⊗[A] RestrictedPowerSeries I σ,
      RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
          (restrictedTensorProjection I σ n t) =
        restrictedTensorProjection I σ m t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [restrictedTensorProjection_tmul, restrictedTensorProjection_tmul]
      have hcoeff : RestrictedPowerSeries.coefficientProjection I σ m f =
          RestrictedPowerSeries.coefficientTransition I σ hmn
            (RestrictedPowerSeries.coefficientProjection I σ n f) :=
        (f.property hmn).symm
      rw [hcoeff, map_mul, algebraMap_mvPolynomial_quotient,
        algebraMap_mvPolynomial_quotient]
      congr 1
      · rw [show RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
            (MvPolynomial.C (Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n) b)) =
            MvPolynomial.map (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (R := B) hmn))
              (MvPolynomial.C (Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ n) b)) from rfl,
          MvPolynomial.map_C]
        rfl
      · rw [show RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
              (MvPolynomial.map (coefficientQuotientMap (B := B) I n)
                (RestrictedPowerSeries.coefficientProjection I σ n f)) =
            MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (R := B) hmn))
              (MvPolynomial.map (coefficientQuotientMap (B := B) I n)
                (RestrictedPowerSeries.coefficientProjection I σ n f)) from rfl,
          show RestrictedPowerSeries.coefficientTransition I σ hmn
              (RestrictedPowerSeries.coefficientProjection I σ n f) =
            MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (R := A) hmn))
              (RestrictedPowerSeries.coefficientProjection I σ n f) from rfl,
          MvPolynomial.map_map, MvPolynomial.map_map,
          factor_comp_coefficientQuotientMap I (Ideal.pow_le_pow_right hmn)
            (Ideal.pow_le_pow_right hmn)]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  show RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
      (restrictedTensorProjection I σ n t) = _
  rw [hgen t]
  rfl

/-- The basic open submodule of the tensor product topology attached to a pair of ideals is the
restriction of scalars of the sum of their extensions. -/
private theorem tensorProductSubmodule_restrictScalars_eq
    {C : Type*} [CommRing C] [Algebra A C] (P : Ideal B) (Q : Ideal C) :
    tensorProductSubmodule (P.restrictScalars A) (Q.restrictScalars A) =
      ((Ideal.map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom P +
        Ideal.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom Q)
        ).restrictScalars A := by
  rw [tensorProductSubmodule, ← LinearMap.rTensor_def, ← LinearMap.lTensor_def]
  rw [show (LinearMap.rTensor C (Submodule.restrictScalars A P).subtype).range =
      (Ideal.map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom
        P).restrictScalars A
      from (Ideal.map_includeLeft_eq (R := A) P).symm]
  rw [show (LinearMap.lTensor B (Submodule.restrictScalars A Q).subtype).range =
      (Ideal.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
        Q).restrictScalars A
      from (Ideal.map_includeRight_eq (R := A) Q).symm]
  simp

/-- The basic open submodule attached to the `n`-th powers of the two coefficient ideals is the
`n`-th power of the extended ideal. -/
private theorem tensorProductSubmodule_pow_eq (I : Ideal A) (σ : Type v) (n : ℕ) :
    tensorProductSubmodule (((I.map (algebraMap A B)) ^ n).restrictScalars A)
        (((RestrictedPowerSeries.coefficientIdeal I σ) ^ n).restrictScalars A) =
      ((restrictedTensorIdeal (B := B) I σ) ^ n).restrictScalars A := by
  rw [tensorProductSubmodule_restrictScalars_eq]
  congr 1
  rw [show Ideal.map (Algebra.TensorProduct.includeLeft :
      B →ₐ[A] B ⊗[A] RestrictedPowerSeries I σ).toRingHom ((I.map (algebraMap A B)) ^ n) = _ from
    map_left_eq_restrictedTensorIdeal_pow I σ n, map_right_eq_restrictedTensorIdeal_pow I σ n,
    Ideal.add_eq_sup, sup_idem]

/-- The inverses of the identifications of the finite quotients are compatible with the
transition maps. -/
public theorem factorPow_comp_restrictedTensorQuotientEquiv_symm (I : Ideal A) (hI : I.FG)
    (σ : Type v) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (restrictedTensorIdeal (B := B) I σ) hmn).comp
        ((restrictedTensorQuotientEquiv I hI σ n).symm.toRingHom.comp
          (RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n)) =
      (restrictedTensorQuotientEquiv I hI σ m).symm.toRingHom.comp
        (RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ m) := by
  refine RingHom.ext fun f => ?_
  show Ideal.Quotient.factorPow (restrictedTensorIdeal (B := B) I σ) hmn
      ((restrictedTensorQuotientEquiv I hI σ n).symm
        (RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n f)) =
    (restrictedTensorQuotientEquiv I hI σ m).symm
      (RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ m f)
  refine (RingEquiv.eq_symm_apply _).mpr ?_
  rw [← restrictedTensorQuotientEquiv_transition I hI σ hmn, RingEquiv.apply_symm_apply]
  exact f.property hmn

/-- The comparison from the restricted power series ring over `B` into the algebraic adic
completion of `B ⊗[A] A{σ}` along the extended ideal, assembled from the identifications of the
finite quotients. -/
public noncomputable def restrictedToAdicCompletion (I : Ideal A) (hI : I.FG) (σ : Type v) :
    RestrictedPowerSeries (I.map (algebraMap A B)) σ →+*
      AdicCompletion (restrictedTensorIdeal (B := B) I σ)
        (B ⊗[A] RestrictedPowerSeries I σ) :=
  AdicCompletion.liftRingHom _
    (fun n => ((restrictedTensorQuotientEquiv I hI σ n).symm.toRingHom.comp
      (RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n)))
    (fun hmn => factorPow_comp_restrictedTensorQuotientEquiv_symm I hI σ hmn)

/-- The comparison into the adic completion is compatible with the finite evaluations. -/
@[simp]
public theorem evalₐ_restrictedToAdicCompletion (I : Ideal A) (hI : I.FG) (σ : Type v)
    (n : ℕ) (f : RestrictedPowerSeries (I.map (algebraMap A B)) σ) :
    AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n
        (restrictedToAdicCompletion I hI σ f) =
      (restrictedTensorQuotientEquiv I hI σ n).symm
        (RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n f) :=
  AdicCompletion.evalₐ_liftRingHom _ _
    (fun hmn => factorPow_comp_restrictedTensorQuotientEquiv_symm I hI σ hmn) n f

/-- The algebraic adic completion of `B ⊗[A] A{σ}` along the extended ideal is the restricted
power series ring over `B`. -/
public noncomputable def adicCompletionRestrictedTensorEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) :
    AdicCompletion (restrictedTensorIdeal (B := B) I σ)
        (B ⊗[A] RestrictedPowerSeries I σ) ≃+*
      RestrictedPowerSeries (I.map (algebraMap A B)) σ where
  toFun x := ⟨fun n => restrictedTensorQuotientEquiv I hI σ n
      (AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n x), by
    intro m n hmn
    change RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
      (restrictedTensorQuotientEquiv I hI σ n _) = _
    rw [restrictedTensorQuotientEquiv_transition I hI σ hmn, AdicCompletion.factorPow_evalₐ]⟩
  invFun := restrictedToAdicCompletion I hI σ
  left_inv x := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_restrictedToAdicCompletion]
    change (restrictedTensorQuotientEquiv I hI σ n).symm
      (restrictedTensorQuotientEquiv I hI σ n
        (AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n x)) = _
    rw [RingEquiv.symm_apply_apply]
  right_inv f := by
    refine Subtype.ext (funext fun n => ?_)
    change restrictedTensorQuotientEquiv I hI σ n
      (AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n
        (restrictedToAdicCompletion I hI σ f)) = _
    rw [evalₐ_restrictedToAdicCompletion, RingEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    refine Subtype.ext (funext fun n => ?_)
    exact ((restrictedTensorQuotientEquiv I hI σ n).toRingHom.comp
      (AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n).toRingHom).map_mul x y
  map_add' x y := by
    refine Subtype.ext (funext fun n => ?_)
    exact ((restrictedTensorQuotientEquiv I hI σ n).toRingHom.comp
      (AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n).toRingHom).map_add x y

/-- The identification of the adic completion with the restricted power series ring reduces,
at every level, to the level `n` reduction of the tensor product. -/
@[simp]
public theorem coefficientProjection_adicCompletionRestrictedTensorEquiv (I : Ideal A)
    (hI : I.FG) (σ : Type v) (n : ℕ) (t : B ⊗[A] RestrictedPowerSeries I σ) :
    RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n
        (adicCompletionRestrictedTensorEquiv I hI σ
          (AdicCompletion.of (restrictedTensorIdeal (B := B) I σ)
            (B ⊗[A] RestrictedPowerSeries I σ) t)) =
      restrictedTensorProjection I σ n t := by
  show restrictedTensorQuotientEquiv I hI σ n
    (AdicCompletion.evalₐ (restrictedTensorIdeal (B := B) I σ) n
      (AdicCompletion.of (restrictedTensorIdeal (B := B) I σ)
        (B ⊗[A] RestrictedPowerSeries I σ) t)) = _
  rw [AdicCompletion.evalₐ_of]
  rfl

end Right

section Topology

variable [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- If the powers of an ideal form a neighbourhood basis of zero, each power is open. -/
private theorem isOpen_restrictScalars_pow {R : Type*} [CommRing R] [Algebra A R]
    [TopologicalSpace R] [IsTopologicalRing R] (J : Ideal R)
    (h : (nhds (0 : R)).HasBasis (fun _ : ℕ => True) fun n => ((J ^ n : Ideal R) : Set R))
    (n : ℕ) : IsOpen (((J ^ n).restrictScalars A : Submodule A R) : Set R) :=
  (J ^ n).toAddSubgroup.isOpen_of_mem_nhds (by simpa using h.mem_of_mem (i := n) trivial)

/-- A higher power of an ideal restricts to a submodule containing a lower power. -/
private theorem restrictScalars_pow_le {R : Type*} [CommRing R] [Algebra A R] (J : Ideal R)
    (U : Submodule A R) {m k : ℕ} (h : ((J ^ m : Ideal R) : Set R) ⊆ U) (hmk : m ≤ k) :
    (J ^ k).restrictScalars A ≤ U :=
  (Submodule.restrictScalars_mono A (Ideal.pow_le_pow_right hmk)).trans h

/-- The tensor product topology on `B ⊗[A] A{σ}` is the adic topology of the extended ideal
`I · (B ⊗[A] A{σ})`. -/
public theorem isAdic_restrictedTensorIdeal (I : Ideal A) (hI : I.FG) (σ : Type v)
    (hJ : _root_.IsAdic (I.map (algebraMap A B))) :
    letI : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    _root_.IsAdic (restrictedTensorIdeal (B := B) I σ) := by
  let _ : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let _ : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I hI σ
  have hJb := hJ.hasBasis_nhds_zero
  have hKb := RestrictedPowerSeries.hasBasis_nhds_zero_coefficientIdeal I hI σ
  have hbasis := hasBasis_tensorProductTopology (R := A) (M := B)
    (N := RestrictedPowerSeries I σ)
  -- the basic open submodules at matching levels are exactly the powers of the extended ideal
  have hopenJ := isOpen_restrictScalars_pow (A := A) _ hJb
  have hopenK := isOpen_restrictScalars_pow (A := A) _ hKb
  rw [_root_.isAdic_iff]
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · have hmem : (((restrictedTensorIdeal (B := B) I σ) ^ n :
        Ideal (B ⊗[A] RestrictedPowerSeries I σ)) :
        Set (B ⊗[A] RestrictedPowerSeries I σ)) ∈ nhds 0 := by
      refine Filter.mem_of_superset
        (hbasis.mem_of_mem (i := (⟨_, hopenJ n⟩, ⟨_, hopenK n⟩)) trivial) (fun x hx => ?_)
      have hx' : x ∈ tensorProductSubmodule (((I.map (algebraMap A B)) ^ n).restrictScalars A)
          (((RestrictedPowerSeries.coefficientIdeal I σ) ^ n).restrictScalars A) := hx
      rw [tensorProductSubmodule_pow_eq] at hx'
      exact hx'
    exact ((restrictedTensorIdeal (B := B) I σ) ^ n).toAddSubgroup.isOpen_of_mem_nhds hmem
  · obtain ⟨i, -, hi⟩ := hbasis.mem_iff.mp hU
    obtain ⟨m, -, hm⟩ := hJb.mem_iff.mp (i.1.2.mem_nhds (zero_mem i.1.1))
    obtain ⟨k, -, hk⟩ := hKb.mem_iff.mp (i.2.2.mem_nhds (zero_mem i.2.1))
    refine ⟨max m k, fun x hx => hi ?_⟩
    have hmono : tensorProductSubmodule
        (((I.map (algebraMap A B)) ^ (max m k)).restrictScalars A)
        (((RestrictedPowerSeries.coefficientIdeal I σ) ^ (max m k)).restrictScalars A) ≤
        tensorProductSubmodule i.1.1 i.2.1 := by
      refine tensorProductSubmodule_mono ?_ ?_
      · exact restrictScalars_pow_le _ _ hm (le_max_left m k)
      · exact restrictScalars_pow_le _ _ hk (le_max_right m k)
    refine hmono ?_
    rw [tensorProductSubmodule_pow_eq (B := B) I σ (max m k)]
    exact hx

/-- **The completed tensor product with a restricted power series ring.**  For a finitely
generated ideal `I` of `A` whose extension defines the topology of `B`, the completed tensor
product `B ⊗̂[A] A{σ}` is canonically the restricted power series ring `B{σ}` over `B` for the
extended ideal. -/
public noncomputable def completedTensorProductRestrictedEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (hJ : _root_.IsAdic (I.map (algebraMap A B))) :
    CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ) ≃+*
      RestrictedPowerSeries (I.map (algebraMap A B)) σ :=
  letI : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I hI σ
  letI : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  letI : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  letI : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
  letI : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  (AdicCompletionBridge.adicCompletionRingEquiv (restrictedTensorIdeal (B := B) I σ)
    (isAdic_restrictedTensorIdeal I hI σ hJ)).trans
      (adicCompletionRestrictedTensorEquiv I hI σ)

/-- The identification `B ⊗̂[A] A{σ} ≃+* B{σ}` reduces, at every level, to the level `n`
reduction of the tensor product: it sends the image of `t : B ⊗[A] A{σ}` to the restricted
power series whose level `n` coefficient polynomial is the reduction of `t`. -/
public theorem coefficientProjection_completedTensorProductRestrictedEquiv (I : Ideal A)
    (hI : I.FG) (σ : Type v) (hJ : _root_.IsAdic (I.map (algebraMap A B))) (n : ℕ)
    (t : B ⊗[A] RestrictedPowerSeries I σ) :
    letI : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
      RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I hI σ
    letI : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
    letI : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n
        (completedTensorProductRestrictedEquiv I hI σ hJ
          (UniformSpace.Completion.coeRingHom t)) =
      restrictedTensorProjection I σ n t := by
  let _ : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    RestrictedPowerSeries.isLinearTopology_restrictedPowerSeries I hI σ
  let _ : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let _ : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let _ : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
  let _ : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  show RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n
    (adicCompletionRestrictedTensorEquiv I hI σ
      (AdicCompletionBridge.adicCompletionRingEquiv (restrictedTensorIdeal (B := B) I σ)
        (isAdic_restrictedTensorIdeal I hI σ hJ) (t : CompletedTensorProduct
          (R := A) (M := B) (N := RestrictedPowerSeries I σ)))) = _
  rw [AdicCompletionBridge.adicCompletionRingEquiv_coe,
    coefficientProjection_adicCompletionRestrictedTensorEquiv]

end Topology


end

end TopologicalRing

end
