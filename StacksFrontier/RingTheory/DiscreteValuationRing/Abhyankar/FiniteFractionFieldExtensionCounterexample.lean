module

public import StacksFrontier.RingTheory.AdicCompletion.NonreducedLocalizedCompletion
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionInput

/-!
# The printed equalities of Tag 09EQ fail

Tag 09EQ asserts that for an extension `A → B` of discrete valuation rings, formally smooth for
the `𝔪_B`-adic topology, and any finite extension `K₁ / K` of the fraction field of `A`, one has
`L₁ = L ⊗_K K₁` and `B₁ = B ⊗_A A₁`, where `L₁ = (L ⊗_K K₁)_red`, `A₁` is the integral closure of
`A` in `K₁` and `B₁` the integral closure of `B` in `L₁` (Remark 09EM). Both rings `L₁` and `B₁`
are reduced, so the two equalities say that `L ⊗_K K₁` and `B ⊗_A A₁` are reduced. This file shows
that neither need be.

Take the characteristic-two discrete valuation ring `A` of Tag 00PB with fraction field `K`, in
which some `a ∈ A` is not a square in `K` but has a square root `α` in the completion `B = A^`.
Then `A → A^` is formally smooth in the adic topology (Tag 09E7: a uniformizer stays one and the
residue fields agree). Let `K₁ = K[T]/(T² - a)`, a field of degree two over `K`. In `L ⊗_K K₁` the
element `1 ⊗ T - α ⊗ 1` is nonzero, as `1, T` is a basis of `K₁` over `K`, and its square is
`1 ⊗ a - a ⊗ 1 = 0` in characteristic two. The element `α ⊗ 1 - 1 ⊗ T` of `B ⊗_A A₁` maps to its
negative, so it is a nonzero nilpotent too.

## Main results

* `IsDiscreteValuationRing.exists_formallySmoothNAdic_not_isReduced_tensorProduct`: the
  counterexample.

## References

* [The Stacks Project, Tag 09EQ](https://stacks.math.columbia.edu/tag/09EQ)
* [The Stacks Project, Tag 00PB](https://stacks.math.columbia.edu/tag/00PB), the source of the
  discrete valuation ring
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing Polynomial
open scoped TensorProduct

universe u

/-- A ring with a nonzero element of square zero is not reduced. -/
private theorem not_isReduced_of_sq_eq_zero {R : Type*} [CommRing R] {z : R} (hz : z ≠ 0)
    (hz2 : z ^ 2 = 0) : ¬ IsReduced R :=
  fun _ => hz (IsNilpotent.eq_zero ⟨2, hz2⟩)

/-- In a tensor product of algebras, a scalar may be moved across the tensor sign. -/
private theorem one_tmul_algebraMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (c : R) :
    (1 : S) ⊗ₜ[R] algebraMap R T c = algebraMap R S c ⊗ₜ[R] (1 : T) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- **The equalities of Tag 09EQ fail as printed.** There are an extension `A → B` of discrete
valuation rings, formally smooth for the `𝔪_B`-adic topology, and a finite extension `K₁ / K` of
the fraction field of `A`, such that neither `L ⊗_K K₁` nor `B ⊗_A A₁` is reduced, where `L` is
the fraction field of `B` and `A₁` the integral closure of `A` in `K₁`. Since `L₁ = (L ⊗_K K₁)_red`
and its subring `B₁` are reduced, neither `L₁ = L ⊗_K K₁` nor `B₁ = B ⊗_A A₁` holds.

The witness is `A → A^` for the characteristic-two discrete valuation ring of Tag 00PB, with
`K₁ = K(√a)` for an `a ∈ A` that is a square in `A^` but not in `K`. -/
@[stacks 09EQ "The printed equalities `L₁ = L ⊗_K K₁` and `B₁ = B ⊗_A A₁` are false in general:
this is the counterexample, `A → A^` for a non-excellent discrete valuation ring of characteristic
two and a purely inseparable `K₁ / K` of degree two. The corrected statement, with the
equalities under the hypothesis that `L ⊗_K K₁` is reduced, is
`formallySmooth_localizations_after_finite_fraction_field_extension`."]
theorem exists_formallySmoothNAdic_not_isReduced_tensorProduct :
    ∃ (A B K L K₁ : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B)
      (_ : IsExtension A B) (_ : Field K) (_ : Field L) (_ : Field K₁)
      (_ : Algebra A K) (_ : Algebra A L) (_ : Algebra B L) (_ : Algebra K L)
      (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A B L) (_ : IsScalarTower A K L) (_ : IsScalarTower A K K₁)
      (_ : IsFractionRing A K) (_ : IsFractionRing B L) (_ : Module.Finite K K₁),
      RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B) ∧
        ¬ IsReduced (L ⊗[K] K₁) ∧ ¬ IsReduced (B ⊗[A] integralClosure A K₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, K, _, _, _, _, _, _, _, _, _, a, α, hα, hK⟩ :=
    exists_charTwo_isDiscreteValuationRing_sq_in_adicCompletion_not_in_fractionField
      (ULift.{u} (ZMod 2))
  let : Algebra K (AdicCompletionFractionField A) := algebraAdicCompletionFractionField A K
  have : IsScalarTower A K (AdicCompletionFractionField A) :=
    isScalarTower_adicCompletionFractionField A K
  have hirr : Irreducible (X ^ 2 - C (algebraMap A K a)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hK
  have : Fact (Irreducible (X ^ 2 - C (algebraMap A K a))) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : Module.Finite K (AdjoinRoot (X ^ 2 - C (algebraMap A K a))) := pb.finite
  refine ⟨A, AdicCompletion (maximalIdeal A) A, K, AdicCompletionFractionField A,
    AdjoinRoot (X ^ 2 - C (algebraMap A K a)), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, formallySmoothNAdic_algebraMap_adicCompletion A, ?_⟩
  set K₁ := AdjoinRoot (X ^ 2 - C (algebraMap A K a))
  set L := AdicCompletionFractionField A
  have h2A : (2 : A) = 0 := by exact_mod_cast CharP.cast_eq_zero A 2
  have h2K : (2 : K) = 0 := by rw [← map_ofNat (algebraMap A K) 2, h2A, map_zero]
  let r : K₁ := AdjoinRoot.root _
  have hr : r ^ 2 = algebraMap K K₁ (algebraMap A K a) := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C (algebraMap A K a))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact sub_eq_zero.mp h
  let αL : L := algebraMap (AdicCompletion (maximalIdeal A) A) L α
  have hαL : αL ^ 2 = algebraMap K L (algebraMap A K a) := by
    rw [← map_pow, hα, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hdim : pb.dim = 2 := by
    simp [pb, AdjoinRoot.powerBasis_dim]
  let i0 : Fin pb.dim := ⟨0, by omega⟩
  let i1 : Fin pb.dim := ⟨1, by omega⟩
  have hb0 : pb.basis i0 = 1 := by simp [i0, PowerBasis.coe_basis]
  have hb1 : pb.basis i1 = r := by simp [i1, PowerBasis.coe_basis, pb, AdjoinRoot.powerBasis_gen, r]
  let z : L ⊗[K] K₁ := (1 : L) ⊗ₜ r - αL ⊗ₜ 1
  have hz : z ≠ 0 := by
    intro h
    let bL := Algebra.TensorProduct.basis L pb.basis
    have hzb : z = bL i1 - αL • bL i0 := by
      simp only [z, bL, Algebra.TensorProduct.basis_apply, hb0, hb1, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have := congrArg (fun x => bL.repr x i1) (hzb.symm.trans h)
    simp [hne] at this
  have hz2 : z ^ 2 = 0 := by
    have h2 : (2 : L ⊗[K] K₁) = 0 := by
      rw [← map_ofNat (algebraMap K (L ⊗[K] K₁)) 2, h2K, map_zero]
    apply sq_sub_eq_zero_of_two_eq_zero h2
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow, hr, hαL]
    exact one_tmul_algebraMap _
  refine ⟨not_isReduced_of_sq_eq_zero hz hz2, ?_⟩
  have hint : IsIntegral A r := by
    refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr, ← IsScalarTower.algebraMap_apply, sub_self]
  let r₁ : integralClosure A K₁ := ⟨r, hint⟩
  have hr₁ : r₁ ^ 2 = algebraMap A (integralClosure A K₁) a := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, r₁, hr]
    rfl
  let w : AdicCompletion (maximalIdeal A) A ⊗[A] integralClosure A K₁ := α ⊗ₜ 1 - 1 ⊗ₜ r₁
  have hw2 : w ^ 2 = 0 := by
    have h2 : (2 : AdicCompletion (maximalIdeal A) A ⊗[A] integralClosure A K₁) = 0 := by
      rw [← map_ofNat (algebraMap A (AdicCompletion (maximalIdeal A) A ⊗[A] integralClosure A K₁))
        2, h2A, map_zero]
    apply sq_sub_eq_zero_of_two_eq_zero h2
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow, hr₁, hα]
    exact (one_tmul_algebraMap _).symm
  let f₁ : AdicCompletion (maximalIdeal A) A →ₐ[A] L ⊗[K] K₁ :=
    (Algebra.TensorProduct.includeLeft (R := K) (S := A) (A := L) (B := K₁)).comp
      (IsScalarTower.toAlgHom A (AdicCompletion (maximalIdeal A) A) L)
  let g₁ : integralClosure A K₁ →ₐ[A] L ⊗[K] K₁ :=
    ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := K₁)).restrictScalars A).comp
      (integralClosure A K₁).val
  let Φ := Algebra.TensorProduct.productMap f₁ g₁
  have hΦ : Φ w = -z := by
    simp [Φ, w, z, f₁, g₁, r₁, αL, Algebra.TensorProduct.productMap_apply_tmul]
  have hw : w ≠ 0 := by
    intro h
    apply hz
    rw [← neg_eq_zero, ← hΦ, h, map_zero]
  exact not_isReduced_of_sq_eq_zero hw hw2

end IsDiscreteValuationRing
