module

public import StacksFrontier.AlgebraicGeometry.Curves.WeilBound.FrobeniusTwistPoints
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.CurveZetaRoots
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.EigenvalueSqrtBound
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Weil bound for curves over a finite field

Let `X` be a smooth, proper, geometrically irreducible curve of genus `g` over a finite field `k`
and `K` a finite extension of `k`. Then

`|#X(K) - #K - 1| ≤ 2 g √#K`.

This is the Riemann hypothesis for curves over a finite field in the form in which Stacks uses it
in the proof of Tag 03W5 ("By R.H. for X ..."). It combines

* the rationality of the zeta function of `X_Ω = X ×_k Ω`, `Ω` an algebraic closure of `k`, with
  respect to the Frobenius twist `Ψ`: there are `r ≤ 2 g(X_Ω)` algebraic integers `α_i` with
  `#Fix(Ψ^m) = 1 + q^m - ∑ α_i^m` (`Stacks.Zeta.exists_zeta_roots_of_isCurve`);
* the count `#Fix(Ψ^m) = #X(k_m)` (`AlgebraicGeometry.WeilBound.natCard_fixed_frobeniusTwist`);
* the eigenvalue bound `|α_i| ≤ √q` of Bombieri–Stepanov
  (`Stacks.BombieriStepanov.norm_le_sqrt_of_smooth`);
* the invariance of the genus under extension of the ground field
  (`AlgebraicGeometry.genus_baseChange`, Stacks 0BY9).

## Main results

* `AlgebraicGeometry.WeilBound.abs_natCard_fieldValuedPoints_sub_le`: the Weil bound.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.WeilBound

open Stacks.EtaleCohomology IntermediateField

/-- An algebraic closure of a finite field of characteristic `p` is algebraic over `𝔽_p`. -/
theorem isAlgebraic_zmod_algebraicClosure (k : Type u) [Field k] [Finite k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [CharP (AlgebraicClosure k) p] :
    letI := ZMod.algebra (AlgebraicClosure k) p
    Algebra.IsAlgebraic (ZMod p) (AlgebraicClosure k) := by
  let := ZMod.algebra (AlgebraicClosure k) p
  refine ⟨fun z => ?_⟩
  have : FiniteDimensional k k⟮z⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have : Finite k⟮z⟯ := Module.finite_of_finite k
  let := Fintype.ofFinite k⟮z⟯
  have hpow : z ^ Fintype.card k⟮z⟯ = z := by
    simpa using congrArg Subtype.val
      (FiniteField.pow_card (⟨z, IntermediateField.mem_adjoin_simple_self k z⟩ : k⟮z⟯))
  refine ⟨Polynomial.X ^ Fintype.card k⟮z⟯ - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero _ Fintype.one_lt_card, ?_⟩
  simp [hpow]

/-- If `N = 1 - ∑ zᵢ ^ m + q ^ m` for `r` complex numbers `zᵢ` of norm at most `c`, then
`|N - q ^ m - 1| ≤ r c ^ m`. -/
private theorem abs_natCast_sub_pow_sub_one_le {r m N q : ℕ} {c : ℝ} (z : Fin r → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ c) (hN : (N : ℂ) = 1 - (∑ i, z i ^ m) + (q : ℂ) ^ m) :
    |(N : ℝ) - (q : ℝ) ^ m - 1| ≤ r * c ^ m := by
  have hS : ∑ i, z i ^ m = ((1 + (q : ℝ) ^ m - N : ℝ) : ℂ) := by
    push_cast
    linear_combination hN
  rw [show (N : ℝ) - (q : ℝ) ^ m - 1 = -(1 + (q : ℝ) ^ m - N) by ring, abs_neg,
    ← Real.norm_eq_abs, ← Complex.norm_real, ← hS]
  calc ‖∑ i, z i ^ m‖ ≤ ∑ i, ‖z i‖ ^ m := by
        refine (norm_sum_le _ _).trans ?_
        simp only [norm_pow, le_refl]
    _ ≤ ∑ _i : Fin r, c ^ m :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz i) m
    _ = r * c ^ m := by simp

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Weil bound** (the Riemann hypothesis for curves over a finite field). For a smooth,
proper, geometrically irreducible curve `X` of genus `g` over a finite field `k` and a finite
extension `K` of `k`, `|#X(K) - #K - 1| ≤ 2 g √#K`. -/
theorem abs_natCard_fieldValuedPoints_sub_le [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [IsCurve k f] (K : Type u) [Field K] [Fintype K] [Algebra k K] :
    |(Nat.card (fieldValuedPoints f K) : ℝ) - Fintype.card K - 1| ≤
      2 * genus f * Real.sqrt (Fintype.card K) := by
  have := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨e, -, he⟩ := FiniteField.card k p
  set Ω := AlgebraicClosure k
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap k Ω).injective p
  have : GeometricallyIntegral f := Stacks.AbelMap.geometricallyIntegral_of_smooth f
  have hpb := IsPullback.of_hasPullback f (baseMap k Ω)
  set g := pullback.snd f (baseMap k Ω)
  have : IsProper g := Stacks.AbelMap.isProper_of_isPullback f _ _ hpb
  have : IsCurve Ω g :=
    { toIsIntegral := Stacks.AbelMap.isIntegral_of_isPullback f _ _ hpb
      topologicalKrullDim_eq_one :=
        Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback f _ _ hpb }
  set Ψ := frobeniusTwist Ω p e he f
  obtain ⟨-, -, r, α, hr, -, hN⟩ := Stacks.Zeta.exists_zeta_roots_of_isCurve p g e e.pos Ψ
    (frobeniusTwist_hom_comp_snd Ω p e he f) (isAlgebraic_zmod_algebraicClosure k p)
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  set N : ℕ → ℕ := fun m => Nat.card {x : geometricBaseChange Ω f |
    IsClosed ({x} : Set (geometricBaseChange Ω f)) ∧ Ψ.hom.base^[m] x = x}
  have hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (L : Type u) [Field L] [Algebra k L] [Finite L],
      Module.finrank k L = m → Nat.card (fieldValuedPoints f L) = N m := by
    intro m _ L _ _ _ hL
    have := Fintype.ofFinite L
    exact (natCard_fixed_frobeniusTwist Ω p e he f L m hL).symm
  have hNα : ∀ m : ℕ, m ≠ 0 →
      (N m : ℂ) = 1 - (∑ i, (ι (α i)) ^ m) + (Fintype.card k : ℂ) ^ m := by
    intro m hm
    have h := congrArg ι (hN m (Nat.pos_of_ne_zero hm)).1
    rw [map_natCast] at h
    rw [h, he]
    simp only [map_add, map_sub, map_one, map_sum, map_pow, map_natCast]
    push_cast
    ring
  have hle : ∀ i, ‖ι (α i)‖ ≤ Real.sqrt (Fintype.card k) := fun i =>
    Stacks.BombieriStepanov.norm_le_sqrt_of_smooth p f N hNcard (fun i => ι (α i)) hNα i
  set m := Module.finrank k K
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hcardK : Fintype.card K = Fintype.card k ^ m := Module.card_eq_pow_finrank
  have hsqrt : Real.sqrt (Fintype.card K) = Real.sqrt (Fintype.card k) ^ m := by
    rw [hcardK, Nat.cast_pow, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
      ← mul_pow, Real.mul_self_sqrt (by positivity)]
  have hr' : (r : ℝ) ≤ 2 * genus f := by
    rw [← genus_baseChange k Ω _ g f hpb]
    exact_mod_cast hr
  rw [hNcard m hm K rfl, hsqrt, hcardK, Nat.cast_pow]
  exact (abs_natCast_sub_pow_sub_one_le (fun i => ι (α i)) hle (hNα m hm)).trans
    (mul_le_mul_of_nonneg_right hr' (by positivity))

end AlgebraicGeometry.WeilBound

end
