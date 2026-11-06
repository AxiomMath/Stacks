module

public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.AlgebraicGeometry.Curves.JacobianMinorIdeal
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.CompleteLocalRing.QuotientNodal
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Jacobian criterion in two variables

For a field `k` and `A = k[[x_0, x_1]]`, let `f ∈ 𝔪_A ^ 2` and `I = (f)`. The Jacobian matrix of
the one-element generating family `f` of `I` is the column `(∂f/∂x_0, ∂f/∂x_1)`, and its ideal of
`1 × 1` minors is `(∂f/∂x_0, ∂f/∂x_1)`. This file proves that this ideal generates the maximal
ideal of `A/I` exactly when the quadratic term of `f` is nondegenerate, that is, when
`4ac - b² ≠ 0` for `f = a x_0² + b x_0 x_1 + c x_1² + (higher order)`.

This is the computation that both directions of the Jacobian criterion for a node pass through.
In the source's proof the forward direction reads "then we can explicitly compute to show that
both (2) and (3) are true", after a change of coordinates putting the quotient in the form
`k[[x_{n-1}, x_n]]/(q)`; the converse ends "the condition on the minors exactly says that the
quadratic term in `f` is nondegenerate".

## Main results

* `Stacks.Curves.span_pair_eq_maximalIdeal_iff` — two elements of `𝔪_A` generate `𝔪_A` if and
  only if the determinant of their matrix of linear coefficients is nonzero. This is the
  two-variable case and carries the content; it is stated for an arbitrary pair rather than for
  a pair of partial derivatives.
* `Stacks.Curves.span_pderiv_eq_maximalIdeal_iff` — the partial derivatives of `f ∈ 𝔪_A ^ 2`
  generate `𝔪_A` if and only if the quadratic term of `f` is nondegenerate.
* `Stacks.Curves.jacobianMinorIdealModulo_eq_maximalIdeal_iff` — the Jacobian-minor ideal of
  Tag 0C4B equals the maximal ideal of the quotient if and only if the ideal of minors together
  with the defining ideal generates the maximal ideal upstairs. This is the bridge between the
  intrinsic formulation of Tag 0C4C and a computation in the power-series ring.
* `Stacks.Curves.jacobianMinorIdealModulo_eq_maximalIdeal_iff_nondegenerate` — the two combined:
  for a plane hypersurface the Jacobian condition of Tag 0C4C is nondegeneracy of the quadratic
  term.
* `Stacks.Curves.isRegularLocalRing_mvPowerSeries_two`,
  `Stacks.Curves.ringKrullDim_mvPowerSeries_two` and the two specializations
  `Stacks.Curves.exists_eq_span_singleton_of_quotient_depth_eq_one`,
  `Stacks.Curves.eq_bot_or_eq_maximalIdeal_or_exists_eq_span_singleton_of_quotient_isReduced`
  of Tag 0C48 to `k[[x_0, x_1]]`. These are what the source's appeal to Tag 0C48 needs once the
  coordinate change has reduced to two variables: the ideal is principal.

## Implementation notes

The linear coefficient of a power series at `x_i` is `MvPowerSeries.coeff (Finsupp.single i 1)`,
which is `MvPowerSeries.constantCoeff ∘ MvPowerSeries.pderiv i`; the second description is the
one used in the proofs, because the Leibniz rule for `pderiv` then gives the behaviour of linear
coefficients on products for free, and that is the only property of them the argument needs. No
model of `𝔪/𝔪²` is chosen: the statements are equalities of ideals of `A`, and the passage
modulo `𝔪²` happens through `Submodule.le_of_le_smul_of_le_jacobson_bot`, Nakayama's lemma, and
`Stacks.MvPowerSeries.RegularParameters.mem_sq_maximalIdeal_of_linear_coeff_zero`.

The nondegeneracy condition is written out in coefficients rather than through
`Stacks.Curves.quadDisc`, whose argument is a coefficient triple, so that the statement mentions
only `f`.

## References

* [Stacks Project, Tag 0C4C](https://stacks.math.columbia.edu/tag/0C4C)
* [Stacks Project, Tag 0C4B](https://stacks.math.columbia.edu/tag/0C4B)
-/

@[expose] public section

open IsLocalRing MvPowerSeries

namespace Stacks.Curves

universe u

variable {k : Type u} [Field k]

/-! ### Linear coefficients -/

/-- The coefficient of `x_i` in a power series, computed as the constant coefficient of its
`i`-th formal partial derivative. -/
private noncomputable def linCoeff {n : ℕ} (i : Fin n) (g : MvPowerSeries (Fin n) k) : k :=
  MvPowerSeries.constantCoeff (pderiv (R := k) i g)

private theorem linCoeff_eq_coeff {n : ℕ} (i : Fin n) (g : MvPowerSeries (Fin n) k) :
    linCoeff i g = MvPowerSeries.coeff (Finsupp.single i 1) g := by
  rw [linCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

private theorem linCoeff_add {n : ℕ} (i : Fin n) (g h : MvPowerSeries (Fin n) k) :
    linCoeff i (g + h) = linCoeff i g + linCoeff i h := by simp [linCoeff]

private theorem linCoeff_smul {n : ℕ} (i : Fin n) (a : k) (g : MvPowerSeries (Fin n) k) :
    linCoeff i (a • g) = a * linCoeff i g := by simp [linCoeff]

private theorem linCoeff_sum {n : ℕ} {ι : Type*} (i : Fin n) (s : Finset ι)
    (g : ι → MvPowerSeries (Fin n) k) :
    linCoeff i (∑ j ∈ s, g j) = ∑ j ∈ s, linCoeff i (g j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [linCoeff]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, linCoeff_add, ih]

/-- The Leibniz rule for linear coefficients. -/
private theorem linCoeff_mul {n : ℕ} (i : Fin n) (u v : MvPowerSeries (Fin n) k) :
    linCoeff i (u * v) = MvPowerSeries.constantCoeff u * linCoeff i v +
      linCoeff i u * MvPowerSeries.constantCoeff v := by
  rw [linCoeff, linCoeff, linCoeff, (pderiv (R := k) i).leibniz]
  simp [mul_comm]

private theorem linCoeff_X {n : ℕ} (i j : Fin n) :
    linCoeff i (MvPowerSeries.X j : MvPowerSeries (Fin n) k) = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [linCoeff]
  · simp [linCoeff, MvPowerSeries.pderiv_X_of_ne h, h]

private theorem constantCoeff_eq_zero_of_mem {n : ℕ} {g : MvPowerSeries (Fin n) k}
    (hg : g ∈ maximalIdeal (MvPowerSeries (Fin n) k)) :
    MvPowerSeries.constantCoeff g = (0 : k) :=
  (Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_eq_zero_field g).1 hg

private theorem mem_maximalIdeal_of_constantCoeff_eq_zero {n : ℕ}
    {g : MvPowerSeries (Fin n) k} (hg : MvPowerSeries.constantCoeff g = (0 : k)) :
    g ∈ maximalIdeal (MvPowerSeries (Fin n) k) :=
  (Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_eq_zero_field g).2 hg

/-- A power series in `𝔪 ^ 2` has vanishing linear coefficients. -/
private theorem linCoeff_eq_zero_of_mem_sq {n : ℕ} (i : Fin n) {g : MvPowerSeries (Fin n) k}
    (hg : g ∈ (maximalIdeal (MvPowerSeries (Fin n) k)) ^ 2) : linCoeff i g = 0 := by
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg ?_ ?_
  · intro u hu v hv
    rw [linCoeff_mul, constantCoeff_eq_zero_of_mem hu, constantCoeff_eq_zero_of_mem hv]
    ring
  · intro x y hx hy
    rw [linCoeff_add, hx, hy]
    ring

/-- A power series in `𝔪` agrees with its linear part modulo `𝔪 ^ 2`. -/
private theorem sub_linearPart_mem_sq {n : ℕ} {g : MvPowerSeries (Fin n) k}
    (hg : MvPowerSeries.constantCoeff g = (0 : k)) :
    g - ∑ j : Fin n, linCoeff j g • (MvPowerSeries.X j : MvPowerSeries (Fin n) k) ∈
      (maximalIdeal (MvPowerSeries (Fin n) k)) ^ 2 := by
  classical
  have hlin (i : Fin n) :
      linCoeff i (∑ j : Fin n, linCoeff j g • (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) =
        linCoeff i g := by
    rw [linCoeff_sum, Finset.sum_congr rfl (fun j _ => by
      rw [linCoeff_smul, linCoeff_X]), Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  refine Stacks.MvPowerSeries.RegularParameters.mem_sq_maximalIdeal_of_linear_coeff_zero _ ?_ ?_
  · have : MvPowerSeries.constantCoeff
        (∑ j : Fin n, linCoeff j g • (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) = (0 : k) := by
      simp
    rw [map_sub, hg, this, sub_zero]
  · intro i
    rw [← linCoeff_eq_coeff]
    rw [show linCoeff i (g - ∑ j : Fin n,
        linCoeff j g • (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) =
          linCoeff i g - linCoeff i (∑ j : Fin n,
            linCoeff j g • (MvPowerSeries.X j : MvPowerSeries (Fin n) k)) from by
      simp [linCoeff, map_sub], hlin i, sub_self]

/-! ### Nakayama -/

/-- An ideal of `k[[x_1, …, x_n]]` contained in the maximal ideal and generating it modulo
`𝔪 ^ 2` is the maximal ideal. -/
theorem eq_maximalIdeal_of_le_sup_sq {n : ℕ} {J : Ideal (MvPowerSeries (Fin n) k)}
    (hJ : J ≤ maximalIdeal (MvPowerSeries (Fin n) k))
    (h : maximalIdeal (MvPowerSeries (Fin n) k) ≤
      J ⊔ (maximalIdeal (MvPowerSeries (Fin n) k)) ^ 2) :
    J = maximalIdeal (MvPowerSeries (Fin n) k) := by
  refine le_antisymm hJ ?_
  have hfg : (maximalIdeal (MvPowerSeries (Fin n) k)).FG := by
    rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
    exact Submodule.fg_span (Set.finite_range _)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) ?_
  rwa [Ideal.smul_eq_mul, ← pow_two]

/-! ### Two elements generating the maximal ideal of `k[[x_0, x_1]]` -/

/-- Solving a `2 × 2` linear system inside a module: the combination of two vectors whose
coordinates in `x`, `y` are the rows of a matrix. -/
private theorem smul_pair_combination {V : Type*} [AddCommGroup V] [Module k V]
    (x y : V) (m₀₀ m₀₁ m₁₀ m₁₁ a₀ a₁ c₀ c₁ : k)
    (h₀ : a₀ * m₀₀ + a₁ * m₁₀ = c₀) (h₁ : a₀ * m₀₁ + a₁ * m₁₁ = c₁) :
    a₀ • (m₀₀ • x + m₀₁ • y) + a₁ • (m₁₀ • x + m₁₁ • y) = c₀ • x + c₁ • y := by
  match_scalars
  · linear_combination h₀
  · linear_combination h₁

/-- A `2 × 2` matrix over a field with vanishing determinant kills a nonzero vector. -/
private theorem exists_ne_zero_of_det_eq_zero (m₀₀ m₀₁ m₁₀ m₁₁ : k)
    (hD : m₀₀ * m₁₁ - m₀₁ * m₁₀ = 0) :
    ∃ v₀ v₁ : k, (v₀ ≠ 0 ∨ v₁ ≠ 0) ∧ m₀₀ * v₀ + m₀₁ * v₁ = 0 ∧
      m₁₀ * v₀ + m₁₁ * v₁ = 0 := by
  have key : ∀ a b : k, ¬(a = 0 ∧ b = 0) → b ≠ 0 ∨ -a ≠ 0 := fun a b h => by
    rw [neg_ne_zero]; tauto
  by_cases h₀ : m₀₀ = 0 ∧ m₀₁ = 0
  · obtain ⟨h₀₀, h₀₁⟩ := h₀
    by_cases h₁ : m₁₀ = 0 ∧ m₁₁ = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h₀₀, h₀₁], by simp [h₁.1, h₁.2]⟩
    · exact ⟨m₁₁, -m₁₀, key _ _ h₁, by simp [h₀₀, h₀₁], by ring⟩
  · exact ⟨m₀₁, -m₀₀, key _ _ h₀, by ring, by linear_combination -hD⟩

/-- **Two elements of `𝔪` generate the maximal ideal of `k[[x_0, x_1]]` exactly when the
determinant of their linear coefficients is nonzero.** -/
theorem span_pair_eq_maximalIdeal_iff (g : Fin 2 → MvPowerSeries (Fin 2) k)
    (hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin 2) k)) :
    Ideal.span (Set.range g) = maximalIdeal (MvPowerSeries (Fin 2) k) ↔
      MvPowerSeries.coeff (Finsupp.single 0 1) (g 0) *
            MvPowerSeries.coeff (Finsupp.single 1 1) (g 1) -
          MvPowerSeries.coeff (Finsupp.single 1 1) (g 0) *
            MvPowerSeries.coeff (Finsupp.single 0 1) (g 1) ≠ 0 := by
  classical
  set m₀₀ := linCoeff 0 (g 0) with hm₀₀
  set m₀₁ := linCoeff 1 (g 0) with hm₀₁
  set m₁₀ := linCoeff 0 (g 1) with hm₁₀
  set m₁₁ := linCoeff 1 (g 1) with hm₁₁
  have hcoeff : ∀ i j : Fin 2,
      MvPowerSeries.coeff (Finsupp.single j 1) (g i) = linCoeff j (g i) :=
    fun i j => (linCoeff_eq_coeff j (g i)).symm
  rw [hcoeff 0 0, hcoeff 1 1, hcoeff 0 1, hcoeff 1 0]
  have hspan_le : Ideal.span (Set.range g) ≤ maximalIdeal (MvPowerSeries (Fin 2) k) :=
    Ideal.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hg i)
  constructor
  · -- If the two elements generate `𝔪`, the determinant is nonzero.
    intro hspan hD
    obtain ⟨v₀, v₁, hv, he₀, he₁⟩ := exists_ne_zero_of_det_eq_zero m₀₀ m₀₁ m₁₀ m₁₁ hD
    -- the functional `h ↦ v₀ * linCoeff 0 h + v₁ * linCoeff 1 h` kills `g 0` and `g 1`
    set φ : MvPowerSeries (Fin 2) k → k :=
      fun h => v₀ * linCoeff 0 h + v₁ * linCoeff 1 h with hφ
    have hφg : ∀ i, φ (g i) = 0 := by
      intro i
      fin_cases i
      · simpa [hφ, hm₀₀, hm₀₁, mul_comm] using he₀
      · simpa [hφ, hm₁₀, hm₁₁, mul_comm] using he₁
    have hφmul : ∀ (u h : MvPowerSeries (Fin 2) k),
        MvPowerSeries.constantCoeff h = (0 : k) →
        φ (u * h) = MvPowerSeries.constantCoeff u * φ h := by
      intro u h hh
      simp only [hφ, linCoeff_mul, hh, mul_zero, add_zero]
      ring
    have hφX : ∀ j : Fin 2,
        φ (MvPowerSeries.X j : MvPowerSeries (Fin 2) k) = if j = 0 then v₀ else v₁ := by
      intro j
      fin_cases j <;> simp [hφ, linCoeff_X]
    have hvanish : ∀ j : Fin 2, φ (MvPowerSeries.X j : MvPowerSeries (Fin 2) k) = 0 := by
      intro j
      have hmem : (MvPowerSeries.X j : MvPowerSeries (Fin 2) k) ∈
          Ideal.span (Set.range g) := by
        rw [hspan, MvPowerSeries.maximalIdeal_eq_span_range_X]
        exact Ideal.subset_span ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
      rw [← hc]
      have : φ (∑ i : Fin 2, c i * g i) = ∑ i : Fin 2, φ (c i * g i) := by
        simp only [hφ, linCoeff_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
      rw [this]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hφmul _ _ (constantCoeff_eq_zero_of_mem (hg i)), hφg i, mul_zero]
    rcases hv with h | h
    · exact h (by simpa [hφX 0] using hvanish 0)
    · exact h (by simpa [hφX 1] using hvanish 1)
  · -- If the determinant is nonzero, the two elements generate `𝔪`.
    intro hD
    refine eq_maximalIdeal_of_le_sup_sq hspan_le ?_
    conv_lhs => rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
    rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    -- coefficients of `X j` as a combination of `g 0` and `g 1`
    obtain ⟨a₀, a₁, hcomb⟩ : ∃ a₀ a₁ : k,
        a₀ • (∑ l : Fin 2, linCoeff l (g 0) • (MvPowerSeries.X l : MvPowerSeries (Fin 2) k)) +
          a₁ • (∑ l : Fin 2,
            linCoeff l (g 1) • (MvPowerSeries.X l : MvPowerSeries (Fin 2) k)) =
          (MvPowerSeries.X j : MvPowerSeries (Fin 2) k) := by
      have hDne : m₀₀ * m₁₁ - m₀₁ * m₁₀ ≠ 0 := hD
      set D := m₀₀ * m₁₁ - m₀₁ * m₁₀ with hDdef
      fin_cases j
      · refine ⟨D⁻¹ * m₁₁, -(D⁻¹ * m₀₁), ?_⟩
        have h₀ : (D⁻¹ * m₁₁) * m₀₀ + (-(D⁻¹ * m₀₁)) * m₁₀ = 1 := by
          field_simp [hDdef]
          ring
        have h₁ : (D⁻¹ * m₁₁) * m₀₁ + (-(D⁻¹ * m₀₁)) * m₁₁ = 0 := by ring
        simp only [Fin.sum_univ_two, ← hm₀₀, ← hm₀₁, ← hm₁₀, ← hm₁₁]
        rw [smul_pair_combination _ _ m₀₀ m₀₁ m₁₀ m₁₁ _ _ 1 0 h₀ h₁]
        simp
      · refine ⟨-(D⁻¹ * m₁₀), D⁻¹ * m₀₀, ?_⟩
        have h₀ : (-(D⁻¹ * m₁₀)) * m₀₀ + (D⁻¹ * m₀₀) * m₁₀ = 0 := by ring
        have h₁ : (-(D⁻¹ * m₁₀)) * m₀₁ + (D⁻¹ * m₀₀) * m₁₁ = 1 := by
          field_simp [hDdef]
          ring
        simp only [Fin.sum_univ_two, ← hm₀₀, ← hm₀₁, ← hm₁₀, ← hm₁₁]
        rw [smul_pair_combination _ _ m₀₀ m₀₁ m₁₀ m₁₁ _ _ 0 1 h₀ h₁]
        simp
    have hsq : ∀ i : Fin 2,
        g i - ∑ l : Fin 2,
            linCoeff l (g i) • (MvPowerSeries.X l : MvPowerSeries (Fin 2) k) ∈
          (maximalIdeal (MvPowerSeries (Fin 2) k)) ^ 2 :=
      fun i => sub_linearPart_mem_sq (constantCoeff_eq_zero_of_mem (hg i))
    have hrewrite : (MvPowerSeries.X j : MvPowerSeries (Fin 2) k) =
        (a₀ • g 0 + a₁ • g 1) -
          (a₀ • (g 0 - ∑ l : Fin 2,
              linCoeff l (g 0) • (MvPowerSeries.X l : MvPowerSeries (Fin 2) k)) +
            a₁ • (g 1 - ∑ l : Fin 2,
              linCoeff l (g 1) • (MvPowerSeries.X l : MvPowerSeries (Fin 2) k))) := by
      rw [← hcomb]
      simp only [smul_sub]
      abel
    rw [hrewrite]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · refine Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ ?_)
        (Submodule.smul_of_tower_mem _ _ ?_)
      · exact Ideal.subset_span (Set.mem_range_self 0)
      · exact Ideal.subset_span (Set.mem_range_self 1)
    · exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ (hsq 0))
        (Submodule.smul_of_tower_mem _ _ (hsq 1))

/-! ### The partial derivatives of a plane curve singularity -/

/-- A partial derivative of a power series in `𝔪 ^ 2` lies in the maximal ideal. -/
private theorem pderiv_mem_maximalIdeal_of_mem_sq {n : ℕ} (i : Fin n)
    {f : MvPowerSeries (Fin n) k} (hf : f ∈ (maximalIdeal (MvPowerSeries (Fin n) k)) ^ 2) :
    pderiv (R := k) i f ∈ maximalIdeal (MvPowerSeries (Fin n) k) :=
  mem_maximalIdeal_of_constantCoeff_eq_zero (linCoeff_eq_zero_of_mem_sq i hf)

/-- The partial derivatives of a power series in two variables, as a range and as a pair. -/
private theorem range_pderiv_eq_pair (f : MvPowerSeries (Fin 2) k) :
    Set.range (fun i : Fin 2 => pderiv (R := k) i f) =
      {pderiv (R := k) 0 f, pderiv (R := k) 1 f} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨by rintro ⟨i, rfl⟩; fin_cases i <;> simp, by
    rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩⟩

/-- **The partial derivatives of `f ∈ 𝔪 ^ 2` generate the maximal ideal of `k[[x_0, x_1]]`
exactly when the quadratic term of `f` is nondegenerate.** -/
@[sga "7 XV 1.2.7" "partial, special case"]
theorem span_pderiv_eq_maximalIdeal_iff {f : MvPowerSeries (Fin 2) k}
    (hf : f ∈ (maximalIdeal (MvPowerSeries (Fin 2) k)) ^ 2) :
    Ideal.span {pderiv (R := k) 0 f, pderiv (R := k) 1 f} = maximalIdeal (MvPowerSeries (Fin 2) k) ↔
      4 * MvPowerSeries.coeff (Finsupp.single 0 2) f *
            MvPowerSeries.coeff (Finsupp.single 1 2) f -
          MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) f ^ 2 ≠ 0 := by
  classical
  set g : Fin 2 → MvPowerSeries (Fin 2) k := fun i => pderiv (R := k) i f with hgdef
  have hg : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin 2) k) :=
    fun i => pderiv_mem_maximalIdeal_of_mem_sq i hf
  -- the four linear coefficients of the two partial derivatives
  have hlc : ∀ i j : Fin 2, MvPowerSeries.coeff (Finsupp.single j 1) (g i) =
      MvPowerSeries.coeff (Finsupp.single j 1 + Finsupp.single i 1) f *
        ((Finsupp.single j 1 : Fin 2 →₀ ℕ) i + 1) := by
    intro i j
    simpa [hgdef] using MvPowerSeries.coeff_pderiv (R := k) (i := i) f (Finsupp.single j 1)
  have h00 : MvPowerSeries.coeff (Finsupp.single 0 1) (g 0) =
      2 * MvPowerSeries.coeff (Finsupp.single 0 2) f := by
    rw [hlc 0 0, ← Finsupp.single_add]
    norm_num [mul_comm]
  have h11 : MvPowerSeries.coeff (Finsupp.single 1 1) (g 1) =
      2 * MvPowerSeries.coeff (Finsupp.single 1 2) f := by
    rw [hlc 1 1, ← Finsupp.single_add]
    norm_num [mul_comm]
  have h01 : MvPowerSeries.coeff (Finsupp.single 1 1) (g 0) =
      MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) f := by
    rw [hlc 0 1, add_comm (Finsupp.single (1 : Fin 2) 1)]
    norm_num
  have h10 : MvPowerSeries.coeff (Finsupp.single 0 1) (g 1) =
      MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) f := by
    rw [hlc 1 0]
    norm_num
  rw [← range_pderiv_eq_pair, span_pair_eq_maximalIdeal_iff g hg, h00, h11, h01, h10]
  exact ⟨fun h hz => h (by linear_combination hz), fun h hz => h (by linear_combination hz)⟩

/-! ### The Jacobian-minor ideal of the quotient -/

/-- The ideal of `1 × 1` minors of a matrix is generated by its entries. -/
theorem minorIdeal_one {R : Type*} [CommRing R] {l o : Type*} (A : Matrix l o R) :
    minorIdeal A 1 = Ideal.span {x : R | ∃ i j, x = A i j} := by
  rw [minorIdeal]
  congr 1
  ext x
  constructor
  · rintro ⟨f, g, rfl⟩
    exact ⟨f 0, g 0, by rw [Matrix.det_fin_one]; rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨fun _ => i, fun _ => j, by rw [Matrix.det_fin_one]; rfl⟩

/-- For an ideal `I` of a local ring contained in the maximal ideal, an ideal maps onto the
maximal ideal of `R ⧸ I` exactly when it generates the maximal ideal of `R` together with `I`. -/
theorem map_eq_maximalIdeal_quotient_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (I J : Ideal R) (hI : I ≤ maximalIdeal R) [IsLocalRing (R ⧸ I)] :
    J.map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) ↔ J ⊔ I = maximalIdeal R := by
  have hmax : maximalIdeal (R ⧸ I) = (maximalIdeal R).map (Ideal.Quotient.mk I) :=
    (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).symm
  have hker : Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (R ⧸ I)) = I := Ideal.mk_ker
  have hmapI : Ideal.map (Ideal.Quotient.mk I) I = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  rw [hmax]
  constructor
  · intro h
    have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, hker] at hcomap
    rw [hcomap, sup_eq_left.mpr hI]
  · intro h
    rw [← h, Ideal.map_sup, hmapI, sup_bot_eq]

/-- **The Jacobian condition of Tag 0C4C, moved upstairs.** The Jacobian-minor ideal of
Tag 0C4B equals the maximal ideal of the quotient exactly when the ideal of minors together with
the defining ideal generates the maximal ideal of the power-series ring. -/
theorem jacobianMinorIdealModulo_eq_maximalIdeal_iff {n m : ℕ}
    (I : Ideal (MvPowerSeries (Fin n) k)) (hI : I ≤ maximalIdeal (MvPowerSeries (Fin n) k))
    (f : Fin m → MvPowerSeries (Fin n) k) (r : ℕ)
    [IsLocalRing (MvPowerSeries (Fin n) k ⧸ I)] :
    jacobianMinorIdealModulo I f r = maximalIdeal (MvPowerSeries (Fin n) k ⧸ I) ↔
      minorIdeal (fun i j => pderiv (R := k) i (f j)) r ⊔ I =
        maximalIdeal (MvPowerSeries (Fin n) k) :=
  map_eq_maximalIdeal_quotient_iff I _ hI

/-- **The Jacobian criterion for a plane hypersurface.** For `f ∈ 𝔪 ^ 2` in `k[[x_0, x_1]]` the
Jacobian-minor ideal of the one-element generating family `f` of `I = (f)` at `r = 1` equals the
maximal ideal of `k[[x_0, x_1]]/(f)` exactly when the quadratic term of `f` is nondegenerate.

This is the case `n = 2`, `t = n - 2 = 0` of the computation both directions of Tag 0C4C pass
through. -/
theorem jacobianMinorIdealModulo_eq_maximalIdeal_iff_nondegenerate
    {f : MvPowerSeries (Fin 2) k}
    (hf : f ∈ (maximalIdeal (MvPowerSeries (Fin 2) k)) ^ 2)
    [IsLocalRing (MvPowerSeries (Fin 2) k ⧸ Ideal.span {f})] :
    jacobianMinorIdealModulo (Ideal.span {f}) (fun _ : Fin 1 => f) 1 =
        maximalIdeal (MvPowerSeries (Fin 2) k ⧸ Ideal.span {f}) ↔
      4 * MvPowerSeries.coeff (Finsupp.single 0 2) f *
            MvPowerSeries.coeff (Finsupp.single 1 2) f -
          MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) f ^ 2 ≠ 0 := by
  classical
  have hfm : f ∈ maximalIdeal (MvPowerSeries (Fin 2) k) :=
    (Ideal.pow_le_self (n := 2) (by norm_num)) hf
  have hIle : Ideal.span {f} ≤ maximalIdeal (MvPowerSeries (Fin 2) k) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm)
  have hIsq : Ideal.span {f} ≤ (maximalIdeal (MvPowerSeries (Fin 2) k)) ^ 2 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf)
  have hminor :
      minorIdeal (fun (i : Fin 2) (j : Fin 1) => pderiv (R := k) i ((fun _ : Fin 1 => f) j)) 1 =
        Ideal.span {pderiv (R := k) 0 f, pderiv (R := k) 1 f} :=
    (minorIdeal_one _).trans (by
      rw [← range_pderiv_eq_pair]
      congr 1
      ext x
      simp [eq_comm])
  have hJle : Ideal.span {pderiv (R := k) 0 f, pderiv (R := k) 1 f} ≤
      maximalIdeal (MvPowerSeries (Fin 2) k) := by
    rw [← range_pderiv_eq_pair, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact pderiv_mem_maximalIdeal_of_mem_sq i hf
  rw [jacobianMinorIdealModulo_eq_maximalIdeal_iff _ hIle, hminor,
    ← span_pderiv_eq_maximalIdeal_iff hf]
  exact ⟨fun h => eq_maximalIdeal_of_le_sup_sq hJle (h.ge.trans (sup_le_sup_left hIsq _)),
    fun h => by rw [h, sup_eq_left.mpr hIle]⟩

/-! ### Tag 0C48 for `k[[x_0, x_1]]`

The source's proof reduces to a quotient of `k[[x_{n-1}, x_n]]` and then applies Tag 0C48 to
conclude that the defining ideal is principal. Both hypotheses of Tag 0C48 hold for the
two-variable power-series ring over a field.
-/

/-- `k[[x_0, x_1]]` is a regular local ring. -/
theorem isRegularLocalRing_mvPowerSeries_two :
    IsRegularLocalRing (MvPowerSeries (Fin 2) k) :=
  MvPowerSeries.isRegularLocalRing k 2

/-- `k[[x_0, x_1]]` has Krull dimension `2`. -/
theorem ringKrullDim_mvPowerSeries_two :
    ringKrullDim (MvPowerSeries (Fin 2) k) = 2 := by
  rw [MvPowerSeries.ringKrullDim_eq]
  norm_num

/-- **Tag 0C48 (2) for `k[[x_0, x_1]]`.** An ideal contained in the maximal ideal whose quotient
has depth one is generated by a single nonzero element of the maximal ideal. -/
theorem exists_eq_span_singleton_of_quotient_depth_eq_one
    (I : Ideal (MvPowerSeries (Fin 2) k)) (hI : I ≤ maximalIdeal (MvPowerSeries (Fin 2) k))
    (hdepth : Module.depth (MvPowerSeries (Fin 2) k)
      (maximalIdeal (MvPowerSeries (Fin 2) k)) (MvPowerSeries (Fin 2) k ⧸ I) = 1) :
    ∃ f : MvPowerSeries (Fin 2) k, f ≠ 0 ∧ f ∈ maximalIdeal (MvPowerSeries (Fin 2) k) ∧
      I = Ideal.span {f} :=
  let := isRegularLocalRing_mvPowerSeries_two (k := k)
  IsRegularLocalRing.exists_ne_zero_mem_maximalIdeal_and_eq_span_singleton_of_quotient_depth_eq_one
    ringKrullDim_mvPowerSeries_two I hI hdepth

/-- **Tag 0C48 (1) for `k[[x_0, x_1]]`.** An ideal contained in the maximal ideal with reduced
quotient is zero, maximal, or generated by a single nonzero element of the maximal ideal. -/
theorem eq_bot_or_eq_maximalIdeal_or_exists_eq_span_singleton_of_quotient_isReduced
    (I : Ideal (MvPowerSeries (Fin 2) k)) (hI : I ≤ maximalIdeal (MvPowerSeries (Fin 2) k))
    [IsReduced (MvPowerSeries (Fin 2) k ⧸ I)] :
    I = ⊥ ∨ I = maximalIdeal (MvPowerSeries (Fin 2) k) ∨
      ∃ f : MvPowerSeries (Fin 2) k, f ≠ 0 ∧ f ∈ maximalIdeal (MvPowerSeries (Fin 2) k) ∧
        I = Ideal.span {f} :=
  let := isRegularLocalRing_mvPowerSeries_two (k := k)
  IsRegularLocalRing.eq_bot_or_eq_maximalIdeal_or_eq_span_singleton_of_quotient_isReduced
    ringKrullDim_mvPowerSeries_two I hI

end Stacks.Curves

end
