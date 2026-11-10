module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.Dimension.Free
public import StacksFrontier.RingTheory.Polynomial.EverywhereUnramifiedDegree

/-!
# Constants of finite extensions of a rational function field

Let `K` be a fraction field of `F[s]` with `s` transcendental over `F`, and `N / K` a finite
extension. The elements of `N` algebraic over `F` (the *constants* of `N`) form a finite extension
of `F`: an `F`-linearly independent family of constants stays linearly independent over `K`,
because `s` stays transcendental over the constants. An element of `N` integral both over `F[s]`
and over `F[s⁻¹]` is a constant, since the coefficients of its minimal polynomial lie in
`F[s] ∩ F[s⁻¹] = F`. Finally, if `[N : K]` is at most the degree of the constants over `F`, then
`N` is spanned over `K` by its constants.

These facts turn the degree bound `Polynomial.finrank_le_of_forall_isUnramifiedAt` for
everywhere unramified extensions of `F(s)` into the statement that such an extension is a
constant field extension.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.linearIndependent_of_isAlgebraic`.
* `AlgebraicGeometry.TameMultiplicativeGroup.mem_bot_of_mem_adjoin_of_mem_adjoin_inv`.
* `AlgebraicGeometry.TameMultiplicativeGroup.isAlgebraic_of_isIntegral_adjoin`.
* `AlgebraicGeometry.TameMultiplicativeGroup.finite_integralClosure`.
* `AlgebraicGeometry.TameMultiplicativeGroup.span_integralClosure_eq_top`.
-/

@[expose] public noncomputable section

open Polynomial Module

namespace AlgebraicGeometry.TameMultiplicativeGroup

section Laurent

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- **`F[s] ∩ F[s⁻¹] = F`** for `s` transcendental over `F`. -/
theorem mem_bot_of_mem_adjoin_of_mem_adjoin_inv {s x : Ω} (hs : Transcendental F s)
    (h₁ : x ∈ Algebra.adjoin F {s}) (h₂ : x ∈ Algebra.adjoin F {s⁻¹}) :
    x ∈ (⊥ : Subalgebra F Ω) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁ h₂
  obtain ⟨p, rfl⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  change aeval s⁻¹ q = aeval s p at hq
  change aeval s p ∈ _
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs isAlgebraic_zero
  let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs0)
  have hrefl := eval₂_reflect_mul_pow (algebraMap F Ω) s⁻¹ q.natDegree q le_rfl
  rw [invOf_eq_inv, inv_inv] at hrefl
  have heq : aeval s (reflect q.natDegree q) = aeval s (p * X ^ q.natDegree) := by
    rw [map_mul, map_pow, aeval_X, aeval_def, ← hq, aeval_def]
    rw [← hrefl, mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, mul_one]
  have hpq := (transcendental_iff_injective.mp hs) heq
  by_cases hp : p = 0
  · rw [hp, map_zero]
    exact Subalgebra.zero_mem _
  have hdeg := natDegree_reflect_le (N := q.natDegree) (p := q)
  rw [hpq, natDegree_mul_X_pow _ hp, max_self] at hdeg
  have hp0 : p.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hp0, aeval_C]
  exact Subalgebra.algebraMap_mem _ _

end Laurent

variable {F K N : Type*} [Field F] [Field K] [Field N] [Algebra F K] [Algebra K N] [Algebra F N]
  [IsScalarTower F K N] {s : K}

/-- **Constants stay linearly independent over `F(s)`.** An `F`-linearly independent family of
elements algebraic over `F` is linearly independent over a fraction field `K` of `F[s]`, `s`
transcendental. -/
theorem linearIndependent_of_isAlgebraic (hs : Transcendental F s)
    [IsFractionRing (Algebra.adjoin F {s}) K] {ι : Type*} {v : ι → N}
    (hv : LinearIndependent F v) (halg : ∀ i, IsAlgebraic F (v i)) : LinearIndependent K v := by
  classical
  set A := Algebra.adjoin F {s}
  rw [linearIndependent_iff']
  intro t g hg i hi
  choose a b hb hab using fun j ↦ IsFractionRing.div_surjective (A := A) (g j)
  have hb0 : ∀ j, algebraMap A K (b j) ≠ 0 := fun j ↦
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hb j)
  set c : ι → A := fun j ↦ a j * ∏ l ∈ t.erase j, b l
  have hc : ∀ j ∈ t, algebraMap A K (c j) = (∏ l ∈ t, algebraMap A K (b l)) * g j := by
    intro j hj
    rw [← Finset.mul_prod_erase t (fun l ↦ algebraMap A K (b l)) hj, ← hab j, map_mul, map_prod]
    have hbj := hb0 j
    rw [mul_comm (algebraMap A K (b j)), mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hbj,
      mul_comm]
  have hsum : ∑ j ∈ t, algebraMap A K (c j) • v j = 0 := by
    calc ∑ j ∈ t, algebraMap A K (c j) • v j
        = ∑ j ∈ t, (∏ l ∈ t, algebraMap A K (b l)) • (g j • v j) :=
          Finset.sum_congr rfl fun j hj ↦ by rw [hc j hj, mul_smul]
      _ = (∏ l ∈ t, algebraMap A K (b l)) • ∑ j ∈ t, g j • v j := Finset.smul_sum.symm
      _ = 0 := by rw [hg, smul_zero]
  -- the numerators as polynomials in `s`
  have hrange : ∀ j, ∃ P : F[X], aeval s P = (c j : K) := fun j ↦ by
    have := (c j).2
    change (c j : K) ∈ Algebra.adjoin F {s} at this
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  choose P hP using hrange
  set σ : N := algebraMap K N s
  have hσ : Transcendental F σ :=
    (transcendental_algebraMap_iff (algebraMap K N).injective).mpr hs
  let E := integralClosure F N
  have hσE : Transcendental E σ := hσ.integralClosure
  have hvE : ∀ j, v j ∈ E := fun j ↦ (halg j).isIntegral
  let Q : E[X] := ∑ j ∈ t, C (⟨v j, hvE j⟩ : E) * (P j).map (algebraMap F E)
  have hQ : aeval σ Q = 0 := by
    simp only [Q, map_sum, map_mul, aeval_C, aeval_map_algebraMap]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, show algebraMap A K (c j) = (c j : K) from rfl, ← hP j,
      ← aeval_algebraMap_apply, mul_comm]
    rfl
  have hQ0 : Q = 0 := (transcendental_iff_injective.mp hσE) (hQ.trans (map_zero _).symm)
  have hcoeff : ∀ n, ∀ j ∈ t, (P j).coeff n = 0 := by
    intro n
    have h := congrArg (fun R : E[X] ↦ ((R.coeff n : E) : N)) hQ0
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero, ZeroMemClass.coe_zero,
      AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] at h
    have h' : ∑ j ∈ t, (P j).coeff n • v j = 0 := by
      rw [← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Algebra.smul_def, mul_comm]
      rfl
    exact (linearIndependent_iff'.mp hv) t _ h'
  have hPi : P i = 0 := Polynomial.ext fun n ↦ by rw [hcoeff n i hi, coeff_zero]
  have hci : algebraMap A K (c i) = 0 := by
    change (c i : K) = 0
    rw [← hP i, hPi, map_zero]
  rw [hc i hi] at hci
  exact (mul_eq_zero.mp hci).resolve_left (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hb0 j)

/-- **Elements integral over `F[s]` and over `F[s⁻¹]` are constants.** -/
theorem isAlgebraic_of_isIntegral_adjoin (hs : Transcendental F s)
    [IsFractionRing (Algebra.adjoin F {s}) K] [IsFractionRing (Algebra.adjoin F {s⁻¹}) K]
    {x : N} (h₁ : IsIntegral (Algebra.adjoin F {s}) x)
    (h₂ : IsIntegral (Algebra.adjoin F {s⁻¹}) x) : IsAlgebraic F x := by
  have hsi : Transcendental F s⁻¹ := fun h ↦ hs (IsAlgebraic.inv_iff.mp h)
  have coeff_mem : ∀ {u : K} [IsFractionRing (Algebra.adjoin F {u}) K], Transcendental F u →
      IsIntegral (Algebra.adjoin F {u}) x → ∀ n, (minpoly K x).coeff n ∈ Algebra.adjoin F {u} := by
    intro u _ hu h n
    have := Polynomial.isPrincipalIdealRing_adjoin F hu
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h, coeff_map]
    exact ((minpoly (Algebra.adjoin F {u}) x).coeff n).2
  have hlift : minpoly K x ∈ lifts (algebraMap F K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact Algebra.mem_bot.mp
      (mem_bot_of_mem_adjoin_of_mem_adjoin_inv hs (coeff_mem hs h₁ n) (coeff_mem hsi h₂ n))
  obtain ⟨p, hp⟩ := hlift
  replace hp : p.map (algebraMap F K) = minpoly K x := hp
  have hint : IsIntegral K x := h₁.tower_top
  refine ⟨p, ?_, ?_⟩
  · rintro rfl
    rw [Polynomial.map_zero] at hp
    exact minpoly.ne_zero hint hp.symm
  · rw [← aeval_map_algebraMap K, hp, minpoly.aeval]

/-- An `F`-linearly independent family of constants of `N` is linearly independent over `K`. -/
private theorem linearIndependent_integralClosure (hs : Transcendental F s)
    [IsFractionRing (Algebra.adjoin F {s}) K] {ι : Type*} {v : ι → integralClosure F N}
    (hv : LinearIndependent F v) : LinearIndependent K fun i ↦ (v i : N) :=
  linearIndependent_of_isAlgebraic hs
    (hv.map' (integralClosure F N).val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
    fun i ↦ (v i).2.isAlgebraic

/-- **The constants of a finite extension of `F(s)` are a finite extension of `F`**, of degree at
most `[N : K]`. -/
theorem finite_integralClosure (hs : Transcendental F s)
    [IsFractionRing (Algebra.adjoin F {s}) K] [FiniteDimensional K N] :
    FiniteDimensional F (integralClosure F N) ∧
      finrank F (integralClosure F N) ≤ finrank K N := by
  have hle : Module.rank F (integralClosure F N) ≤ finrank K N := by
    refine rank_le fun t ht ↦ ?_
    simpa using (linearIndependent_integralClosure (N := N) hs ht).fintype_card_le_finrank
  have hfin : FiniteDimensional F (integralClosure F N) :=
    rank_lt_aleph0_iff.mp (hle.trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨hfin, ?_⟩
  rw [← Module.finrank_eq_rank] at hle
  exact_mod_cast hle

/-- **An extension of `F(s)` of degree at most that of its constants is spanned by them.** -/
theorem span_integralClosure_eq_top (hs : Transcendental F s)
    [IsFractionRing (Algebra.adjoin F {s}) K] [FiniteDimensional K N]
    (h : finrank K N ≤ finrank F (integralClosure F N)) :
    Submodule.span K (integralClosure F N : Set N) = ⊤ := by
  have := (finite_integralClosure hs (N := N)).1
  set E := integralClosure F N
  let b := Module.finBasis F E
  let v : Fin (finrank F E) → N := fun i ↦ (b i : N)
  have hli : LinearIndependent K v := linearIndependent_integralClosure hs b.linearIndependent
  have hrank : finrank K (Submodule.span K (Set.range v)) = finrank F E := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h.trans hrank.symm.le))
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (Set.range_subset_iff.mpr fun i ↦ (b i).2)

end AlgebraicGeometry.TameMultiplicativeGroup

end
