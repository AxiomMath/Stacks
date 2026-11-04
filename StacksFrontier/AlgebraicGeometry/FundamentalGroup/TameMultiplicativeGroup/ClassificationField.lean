module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.ConstantField
public import StacksFrontier.RingTheory.Polynomial.EverywhereUnramifiedDegree

/-!
# Function fields of covers of `𝐏¹` unramified everywhere

* `F⟮t⟯` is a fraction field of `F[t]`, and a fraction field of `F[s]` is one of `F[s⁻¹]`.
* Let `s` be transcendental over `F`, `K` a fraction field of `F[s]`, and `N / K` finite separable
  such that the integral closures of `F[s]` and `F[s⁻¹]` in `N` are unramified at every prime.
  Then `N` is spanned over `K` by its constants, the elements of `N` integral over `F`
  (`Polynomial.finrank_le_of_forall_isUnramifiedAt` bounds `[N : K]` by the degree of the
  constants, and `span_integralClosure_eq_top` concludes).

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.isFractionRing_adjoin_gen`.
* `AlgebraicGeometry.TameMultiplicativeGroup.isFractionRing_adjoin_inv`.
* `AlgebraicGeometry.TameMultiplicativeGroup.span_integralClosure_eq_top_of_forall_isUnramifiedAt`.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

namespace AlgebraicGeometry.TameMultiplicativeGroup

section FractionRing

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Every element of `F[s]` is `y s^n` with `y ∈ F[s⁻¹]`. -/
theorem exists_mem_adjoin_inv_mul_pow {s : K} (hs : s ≠ 0) {x : K}
    (hx : x ∈ Algebra.adjoin F {s}) : ∃ n : ℕ, ∃ y ∈ Algebra.adjoin F {s⁻¹}, x = y * s ^ n := by
  have hinv : s⁻¹ ∈ Algebra.adjoin F {s⁻¹} := Algebra.self_mem_adjoin_singleton F _
  refine Algebra.adjoin_induction
    (p := fun x _ ↦ ∃ n : ℕ, ∃ y ∈ Algebra.adjoin F {s⁻¹}, x = y * s ^ n)
    (fun y hy ↦ ?_) (fun r ↦ ?_) (fun _ _ _ _ ha hb ↦ ?_) (fun _ _ _ _ ha hb ↦ ?_) hx
  · rw [Set.mem_singleton_iff.mp hy]
    exact ⟨1, 1, one_mem _, by rw [one_mul, pow_one]⟩
  · exact ⟨0, algebraMap F K r, Subalgebra.algebraMap_mem _ r, by rw [pow_zero, mul_one]⟩
  · obtain ⟨n, a, ha, rfl⟩ := ha
    obtain ⟨m, b, hb, rfl⟩ := hb
    refine ⟨n + m, a * s⁻¹ ^ m + b * s⁻¹ ^ n,
      add_mem (mul_mem ha (pow_mem hinv m)) (mul_mem hb (pow_mem hinv n)), ?_⟩
    rw [add_mul, pow_add, inv_pow, inv_pow]
    field_simp
  · obtain ⟨n, a, ha, rfl⟩ := ha
    obtain ⟨m, b, hb, rfl⟩ := hb
    exact ⟨n + m, a * b, mul_mem ha hb, by ring⟩

/-- **A fraction field of `F[s]` is a fraction field of `F[s⁻¹]`.** -/
theorem isFractionRing_adjoin_inv {s : K} (hs : s ≠ 0) [IsFractionRing (Algebra.adjoin F {s}) K] :
    IsFractionRing (Algebra.adjoin F {s⁻¹}) K := by
  have hinv : s⁻¹ ∈ Algebra.adjoin F {s⁻¹} := Algebra.self_mem_adjoin_singleton F _
  have : FaithfulSMul (Algebra.adjoin F {s⁻¹}) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Algebra.adjoin F {s}) z
  obtain ⟨n, a', ha', ha⟩ := exists_mem_adjoin_inv_mul_pow hs a.2
  obtain ⟨m, b', hb', hbeq⟩ := exists_mem_adjoin_inv_mul_pow hs b.2
  refine ⟨⟨a' * s⁻¹ ^ m, mul_mem ha' (pow_mem hinv m)⟩,
    ⟨b' * s⁻¹ ^ n, mul_mem hb' (pow_mem hinv n)⟩, ?_⟩
  have hb0 : (b : K) ≠ 0 := fun h0 ↦ nonZeroDivisors.ne_zero hb (Subtype.ext h0)
  change (a : K) / (b : K) = (a' * s⁻¹ ^ m) / (b' * s⁻¹ ^ n)
  rw [ha, hbeq] at *
  have hb'0 : b' ≠ 0 := fun h0 ↦ hb0 (by rw [h0, zero_mul])
  rw [inv_pow, inv_pow]
  field_simp

/-- **`F⟮t⟯` is a fraction field of `F[t]`.** -/
theorem isFractionRing_adjoin_gen {Ω : Type*} [Field Ω] [Algebra F Ω] (t : Ω) :
    IsFractionRing (Algebra.adjoin F {IntermediateField.AdjoinSimple.gen F t}) F⟮t⟯ := by
  have : FaithfulSMul (Algebra.adjoin F {IntermediateField.AdjoinSimple.gen F t}) F⟮t⟯ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨r, r', h⟩ := (IntermediateField.mem_adjoin_simple_iff F (z : Ω)).mp z.2
  refine ⟨⟨aeval (IntermediateField.AdjoinSimple.gen F t) r, aeval_mem_adjoin_singleton F _⟩,
    ⟨aeval (IntermediateField.AdjoinSimple.gen F t) r', aeval_mem_adjoin_singleton F _⟩,
    Subtype.ext ?_⟩
  change (z : Ω) = ((aeval (IntermediateField.AdjoinSimple.gen F t) r : F⟮t⟯) : Ω) /
    ((aeval (IntermediateField.AdjoinSimple.gen F t) r' : F⟮t⟯) : Ω)
  rw [IntermediateField.AdjoinSimple.coe_aeval_gen_apply,
    IntermediateField.AdjoinSimple.coe_aeval_gen_apply, h]

end FractionRing

/-- **A cover of `𝐏¹` unramified everywhere is spanned by its constants.** If the integral
closures of `F[s]` and `F[s⁻¹]` in a finite separable extension `N` of `K = F(s)` are unramified
at every prime, then `N` is spanned over `K` by the elements integral over `F`. -/
theorem span_integralClosure_eq_top_of_forall_isUnramifiedAt {F K N : Type*} [Field F] [Field K]
    [Field N] [Algebra F K] [Algebra K N] [Algebra F N] [IsScalarTower F K N] {s : K}
    (hs : Transcendental F s) [IsFractionRing (Algebra.adjoin F {s}) K]
    [IsFractionRing (Algebra.adjoin F {s⁻¹}) K] [FiniteDimensional K N] [Algebra.IsSeparable K N]
    (h₀ : ∀ (P : Ideal (integralClosure (Algebra.adjoin F {s}) N)) [P.IsPrime],
      Algebra.IsUnramifiedAt (Algebra.adjoin F {s}) P)
    (h₁ : ∀ (P : Ideal (integralClosure (Algebra.adjoin F {s⁻¹}) N)) [P.IsPrime],
      Algebra.IsUnramifiedAt (Algebra.adjoin F {s⁻¹}) P) :
    Submodule.span K (integralClosure F N : Set N) = ⊤ := by
  have : FiniteDimensional F (integralClosure F N) := (finite_integralClosure hs (N := N)).1
  have : FiniteDimensional F (integralClosure F N).toSubmodule :=
    inferInstanceAs (FiniteDimensional F (integralClosure F N))
  refine span_integralClosure_eq_top hs ?_
  exact Polynomial.finrank_le_of_forall_isUnramifiedAt hs h₀ h₁ (integralClosure F N).toSubmodule
    fun x hx₁ hx₂ ↦ (isAlgebraic_of_isIntegral_adjoin hs hx₁ hx₂).isIntegral

end AlgebraicGeometry.TameMultiplicativeGroup

end
