module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormula
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A component of positive intersection with a partial special fibre

Let `X ⟶ Spec(R)` be a regular proper model and let `C₁, …, Cₙ` be the irreducible components
of its special fibre, with multiplicities `mᵢ`, so that `X_k = Σ mᵢ Cᵢ`. Suppose some component
`C₀` has multiplicity one. For a divisor `D = Σ aᵢ Cᵢ` with `0 ≤ aᵢ ≤ mᵢ`, `a₀ = 1` and `a ≠ m`,
there is a component `Cᵢ` with `aᵢ < mᵢ` on which `𝒪_X(-D)` has negative degree.

Indeed `a` is not a rational multiple of `m`: such a multiple `q·m` has `q = a₀ / m₀ = 1`. So
`(D · D) < 0` by the negative semidefiniteness of the intersection form, part (4) of
[Stacks, Tag 0C66], while `(X_k · D) = 0` by part (2).
Hence `Σᵢ (mᵢ - aᵢ)(Cᵢ · D) = -(D · D) > 0`, and some `i` has `aᵢ < mᵢ` and `(Cᵢ · D) > 0`;
the degree of `𝒪_X(-D)` on `Cᵢ` is `-(Cᵢ · D)`.

This is the step that lets a field of global functions on `C₀` propagate, one component at a
time, to the whole special fibre.

## Main results

* `Stacks.Models.RegularProperModelSituation.specialFiberComponentDegree_negativeTwist_prod` —
  `deg(𝒪_X(-Σⱼ cⱼCⱼ)|_{Cᵢ}) = -Σⱼ cⱼ(Cᵢ · Cⱼ)`.
* `Stacks.Models.RegularProperModelSituation.exists_specialFiberComponentDegree_negativeTwist_neg`
  — the component of positive intersection above.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]

/-- `deg(𝒪_X(-Σⱼ cⱼCⱼ)|_{Cᵢ}) = -Σⱼ cⱼ(Cᵢ · Cⱼ)` at the components of the special fibre. -/
theorem specialFiberComponentDegree_negativeTwist_prod
    (c : irreducibleComponents S.specialFiber → ℕ) (W : irreducibleComponents S.specialFiber) :
    S.specialFiberComponentDegree W
        (Stacks.Divisors.negativeTwist (∏ V, S.specialFiberComponentIdeal V ^ c V))
        (@Stacks.Divisors.stacksIsInvertible_negativeTwist _ _
          (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ c
            fun V _ => S.isEffectiveCartierDivisor_specialFiberComponent V)) =
      -∑ V, (c V : ℤ) * S.specialFiberIntersectionMatrix W V := by
  rw [← S.specialFiberDivisorDegree_eq_sum W c]
  exact componentDegree_negativeTwist_eq_neg S (fun V => S.specialFiberComponentIdeal V)
    (fun V => S.specialFiberComponentToSpec V) (fun V => S.isProper_specialFiberComponentToSpec V)
    (fun V => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent V) W _
    (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ c
      fun V _ => S.isEffectiveCartierDivisor_specialFiberComponent V)

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **A component of positive intersection with a partial special fibre.** If the component
`C₀` has multiplicity one and `D = Σ aᵢCᵢ` has `aᵢ ≤ mᵢ`, `a₀ = 1` and `a ≠ m`, then some
component `Cᵢ` with `aᵢ < mᵢ` has `deg(𝒪_X(-D)|_{Cᵢ}) < 0`. -/
@[sga "7 X 1.13" "special case"]
theorem exists_specialFiberComponentDegree_negativeTwist_neg
    (Z0 : irreducibleComponents S.specialFiber) (hZ0 : S.specialFiberMultiplicity Z0 = 1)
    (a : irreducibleComponents S.specialFiber → ℕ) (ha : ∀ W, a W ≤ S.specialFiberMultiplicity W)
    (ha0 : a Z0 = 1) (hne : a ≠ S.specialFiberMultiplicity) :
    ∃ W, a W < S.specialFiberMultiplicity W ∧
      S.specialFiberComponentDegree W
        (Stacks.Divisors.negativeTwist (∏ V, S.specialFiberComponentIdeal V ^ a V))
        (@Stacks.Divisors.stacksIsInvertible_negativeTwist _ _
          (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ a
            fun V _ => S.isEffectiveCartierDivisor_specialFiberComponent V)) < 0 := by
  classical
  set f : irreducibleComponents S.specialFiber → ℤ :=
    fun Z => ∑ W, (a W : ℤ) * S.specialFiberIntersectionMatrix Z W with hf
  set Q : ℤ := ∑ Z, ∑ W, (a Z : ℤ) * (a W : ℤ) * S.specialFiberIntersectionMatrix Z W with hQ
  -- `(D · D) < 0`, since `a` is not a rational multiple of `m`
  obtain ⟨hle, hiff⟩ := S.specialFiberIntersectionForm_nonpos_and_eq_zero_iff fun Z => (a Z : ℚ)
  have hcast : ((Q : ℤ) : ℚ) = ∑ Z, ∑ W, (a Z : ℚ) * (a W : ℚ) *
      (S.specialFiberIntersectionMatrix Z W : ℚ) := by
    simp only [hQ]
    push_cast
    rfl
  rw [← hcast] at hle hiff
  have hlt : Q < 0 := by
    refine lt_of_le_of_ne (by exact_mod_cast hle) fun h0 => hne ?_
    obtain ⟨q, hq⟩ := hiff.mp (by exact_mod_cast h0)
    have hq1 : q = 1 := by
      have := hq Z0
      rw [ha0, hZ0] at this
      simpa using this.symm
    funext Z
    have := hq Z
    rw [hq1, one_mul] at this
    exact_mod_cast this
  -- `Σ aᵢ (Cᵢ · D) = (D · D)` and `Σ mᵢ (Cᵢ · D) = 0`
  have hA : ∑ Z, (a Z : ℤ) * f Z = Q := by
    simp only [hf, hQ, Finset.mul_sum, mul_assoc]
  have hM : ∑ Z, (S.specialFiberMultiplicity Z : ℤ) * f Z = 0 := by
    simp only [hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun W _ => ?_
    have := sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion S
      (fun V => S.specialFiberComponentIdeal V) (fun V => S.specialFiberComponentToSpec V)
      (fun V => S.isProper_specialFiberComponentToSpec V)
      (fun V => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent V)
      S.specialFiberIntersectionMatrix S.specialFiberMultiplicity
      (fun V => S.isEffectiveCartierDivisor_specialFiberComponent V)
      (fun c V => S.specialFiberDivisorDegree_eq_sum V c) S.specialFiberIdeal_eq_prod W
    calc ∑ Z, (S.specialFiberMultiplicity Z : ℤ) *
          ((a W : ℤ) * S.specialFiberIntersectionMatrix Z W)
        = (a W : ℤ) * ∑ Z, (S.specialFiberMultiplicity Z : ℤ) *
            S.specialFiberIntersectionMatrix W Z := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun Z _ => by
            rw [S.specialFiberIntersectionMatrix_comm Z W]; ring
      _ = 0 := by rw [this, mul_zero]
  have hpos : ∑ _Z : irreducibleComponents S.specialFiber, (0 : ℤ) <
      ∑ Z, ((S.specialFiberMultiplicity Z : ℤ) - a Z) * f Z := by
    simp only [sub_mul, Finset.sum_sub_distrib, hA, hM, Finset.sum_const_zero]
    linarith
  obtain ⟨W, -, hW⟩ := Finset.exists_lt_of_sum_lt hpos
  have hmW : (0 : ℤ) ≤ (S.specialFiberMultiplicity W : ℤ) - a W :=
    sub_nonneg.mpr (by exact_mod_cast ha W)
  obtain ⟨h1, h2⟩ : 0 < (S.specialFiberMultiplicity W : ℤ) - a W ∧ 0 < f W := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hW with h | h
    · exact h
    · exact absurd h.1 (not_lt.mpr hmW)
  refine ⟨W, by exact_mod_cast sub_pos.mp h1, ?_⟩
  rw [S.specialFiberComponentDegree_negativeTwist_prod a W]
  exact neg_neg_of_pos h2

end Stacks.Models.RegularProperModelSituation

end
