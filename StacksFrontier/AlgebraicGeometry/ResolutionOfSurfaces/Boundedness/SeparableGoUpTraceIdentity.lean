module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.Trace.Discriminant

/-!
# A trace identity for a finite separable extension of fraction fields

Let `A → B` be a finite map of domains with `A` normal, and let `K ⊆ L` be fraction fields of
`A` and `B` with `L / K` finite separable. Choose `b₁, …, bₙ ∈ B` forming a `K`-basis of `L`.
The trace matrix `M = (Trace(bᵢ bⱼ))` has entries in `A` and nonzero determinant `d`, and with
`eⱼ = ∑ᵢ adj(M)ᵢⱼ bᵢ ∈ B` one has, for every `σ ∈ L`,

  `d σ = ∑ⱼ Trace(bⱼ σ) eⱼ`.

## Main results

* `Stacks.Trace.exists_traceIdentity`: elements `b, e` of `B` and a nonzero `d ∈ A` such that
  the identity holds in *every* pair of fraction fields `K ⊆ L` of `A ⊆ B`.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
-/

@[expose] public section

namespace Stacks.Trace

universe u

open Matrix

section Model

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
  [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [Module.Finite A B] [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [IsDomain A] in
/-- The trace identity in one pair of fraction fields. -/
theorem exists_traceIdentity_of_model :
    ∃ (n : ℕ) (b e : Fin n → B) (d : A), d ≠ 0 ∧ ∀ σ : L,
      algebraMap A L d * σ =
        ∑ j, algebraMap K L (Algebra.trace K L (algebraMap B L (b j) * σ)) *
          algebraMap B L (e j) := by
  classical
  obtain ⟨n, bb, hbb⟩ := exists_basis_mem_range_algebraMap B K L
  choose b hb using hbb
  have hint : ∀ i j, IsIntegral A (Algebra.trace K L (bb i * bb j)) := fun i j => by
    refine Algebra.isIntegral_trace ?_
    rw [← hb i, ← hb j, ← map_mul]
    exact (Algebra.IsIntegral.isIntegral (R := A) (b i * b j)).map
      (IsScalarTower.toAlgHom A B L)
  have hmem : ∀ i j, ∃ a : A, algebraMap A K a = Algebra.trace K L (bb i * bb j) :=
    fun i j => IsIntegrallyClosed.isIntegral_iff.mp (hint i j)
  choose MA hMA using hmem
  let MA' : Matrix (Fin n) (Fin n) A := MA
  have hmap : MA'.map (algebraMap A K) = Algebra.traceMatrix K bb := by
    ext i j
    rw [Matrix.map_apply, hMA, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  let d : A := MA'.det
  have hd : algebraMap A K d = Algebra.discr K bb := by
    rw [Algebra.discr_def, ← hmap, RingHom.map_det]
    rfl
  have hd0 : d ≠ 0 := fun h0 ↦ Algebra.discr_not_zero_of_basis K bb (by rw [← hd, h0, map_zero])
  let adj := MA'.adjugate
  let e : Fin n → B := fun j => ∑ i, adj i j • b i
  refine ⟨n, b, e, d, hd0, fun σ => ?_⟩
  let lhs : L →ₗ[K] L := algebraMap A L d • LinearMap.id
  let rhs : L →ₗ[K] L := ∑ j, (LinearMap.toSpanSingleton K L (algebraMap B L (e j))).comp
    ((Algebra.trace K L).comp (LinearMap.mulLeft K (algebraMap B L (b j))))
  have hA : ∀ a : A, algebraMap K L (algebraMap A K a) = algebraMap A L a := fun a =>
    (IsScalarTower.algebraMap_apply A K L a).symm
  have he : ∀ j, algebraMap B L (e j) = ∑ i, algebraMap A L (adj i j) * bb i := fun j => by
    simp only [e, map_sum, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, hb]
  have hext : lhs = rhs := by
    refine bb.ext fun k => ?_
    simp only [lhs, rhs, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.toSpanSingleton_apply]
    have htr : ∀ j, Algebra.trace K L (algebraMap B L (b j) * bb k) = algebraMap A K (MA j k) :=
      fun j => by rw [hMA, hb j]
    simp only [htr, he, Algebra.smul_def, hA]
    symm
    calc ∑ j, algebraMap A L (MA j k) * ∑ i, algebraMap A L (adj i j) * bb i
        = ∑ i, algebraMap A L ((adj * MA') i k) * bb i := by
          simp only [Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]
          simp only [MA']
          ring
      _ = algebraMap A L d * bb k := by
          simp only [adj, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
            mul_ite, mul_one, mul_zero]
          rw [Finset.sum_eq_single k (fun j _ hj => by rw [ite_eq_right hj, map_zero, zero_mul])
            (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]
  simpa [lhs, rhs, Algebra.smul_def] using LinearMap.congr_fun hext σ

end Model

section Transfer

/-- **The trace identity transfers between pairs of fraction fields.** If it holds in one pair
`K₀ ⊆ L₀` of fraction fields of `A ⊆ B`, it holds in every other pair `K ⊆ L`. -/
theorem traceIdentity_transfer (A B K₀ L₀ K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra A B] [Field K₀] [Field L₀] [Algebra A K₀] [IsFractionRing A K₀]
    [Algebra B L₀] [IsFractionRing B L₀] [Algebra K₀ L₀] [Algebra A L₀] [IsScalarTower A K₀ L₀]
    [IsScalarTower A B L₀] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] {n : ℕ} (b e : Fin n → B) (d : A)
    (h : ∀ σ : L₀, algebraMap A L₀ d * σ =
        ∑ j, algebraMap K₀ L₀ (Algebra.trace K₀ L₀ (algebraMap B L₀ (b j) * σ)) *
          algebraMap B L₀ (e j)) (σ : L) :
    algebraMap A L d * σ =
      ∑ j, algebraMap K L (Algebra.trace K L (algebraMap B L (b j) * σ)) *
        algebraMap B L (e j) := by
  let e₁ : K₀ ≃+* K := (IsLocalization.algEquiv (nonZeroDivisors A) K₀ K).toRingEquiv
  let e₂ : L₀ ≃+* L := (IsLocalization.algEquiv (nonZeroDivisors B) L₀ L).toRingEquiv
  have he₁ : ∀ a : A, e₁ (algebraMap A K₀ a) = algebraMap A K a := fun a =>
    (IsLocalization.algEquiv (nonZeroDivisors A) K₀ K).commutes a
  have he₂ : ∀ c : B, e₂ (algebraMap B L₀ c) = algebraMap B L c := fun c =>
    (IsLocalization.algEquiv (nonZeroDivisors B) L₀ L).commutes c
  have hsq : (algebraMap K L).comp (e₁ : K₀ →+* K) = (e₂ : L₀ →+* L).comp (algebraMap K₀ L₀) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) ?_
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, he₁]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L₀, he₂]
  have htr : ∀ x : L₀, e₁ (Algebra.trace K₀ L₀ x) = Algebra.trace K L (e₂ x) := fun x => by
    rw [Algebra.trace_eq_of_equiv_equiv e₁ e₂ hsq x, RingEquiv.apply_symm_apply]
  have hA : ∀ a : A, e₂ (algebraMap A L₀ a) = algebraMap A L a := fun a => by
    rw [IsScalarTower.algebraMap_apply A B L₀, he₂, ← IsScalarTower.algebraMap_apply]
  have hK : ∀ x : K₀, e₂ (algebraMap K₀ L₀ x) = algebraMap K L (e₁ x) := fun x =>
    (congrArg (fun f : K₀ →+* L => f x) hsq).symm
  have := congrArg e₂ (h (e₂.symm σ))
  simpa only [map_mul, map_sum, hA, RingEquiv.apply_symm_apply, hK, htr, he₂] using this

/-- **The trace identity.** Let `A → B` be a finite map of domains
with `A` normal, and suppose that for some pair of fraction fields `K₀ ⊆ L₀` the extension
`L₀ / K₀` is finite separable. Then there are `b₁, …, bₙ, e₁, …, eₙ ∈ B` and a nonzero `d ∈ A`
such that `d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` for every `σ` in every pair of fraction fields `K ⊆ L` of
`A ⊆ B`. -/
theorem exists_traceIdentity (A B K₀ L₀ : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Field K₀] [Field L₀] [Algebra A B]
    [Algebra A K₀] [IsFractionRing A K₀] [Algebra B L₀] [IsFractionRing B L₀] [Algebra K₀ L₀]
    [Algebra A L₀] [IsScalarTower A K₀ L₀] [IsScalarTower A B L₀] [Module.Finite A B]
    [FiniteDimensional K₀ L₀] [Algebra.IsSeparable K₀ L₀] :
    ∃ (n : ℕ) (b e : Fin n → B) (d : A), d ≠ 0 ∧
      ∀ (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
        [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
        [IsScalarTower A B L] (σ : L),
        algebraMap A L d * σ =
          ∑ j, algebraMap K L (Algebra.trace K L (algebraMap B L (b j) * σ)) *
            algebraMap B L (e j) := by
  obtain ⟨n, b, e, d, hd, h⟩ := exists_traceIdentity_of_model A B K₀ L₀
  exact ⟨n, b, e, d, hd, fun K L _ _ _ _ _ _ _ _ _ _ σ =>
    traceIdentity_transfer A B K₀ L₀ K L b e d h σ⟩

end Transfer

end Stacks.Trace

end
