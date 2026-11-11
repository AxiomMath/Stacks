module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharSeriesTrace

/-!
# Cohomological interpretation of the L-function

Let `X` be a scheme of finite type over a finite field `k` and let `ℱ` be a sheaf on
`X_étale` whose geometric Frobenius acts on the stalk at a closed point `x` by a matrix
`π_x^*`, and on the compactly supported cohomology `H_c^i(X_k̄, ℱ)` by a matrix `π_X^*`.
Grothendieck's cohomological interpretation of the L-function is the identity

`L(X, ℱ) = ∏_i det(1 - π_X^* T |_{H_c^i(X_k̄, ℱ)}) ^ ((-1) ^ (i + 1))`

in `Λ⟦T⟧`.  Both sides have constant coefficient `1`, so over a coefficient ring with
torsion-free additive group they agree as soon as their logarithmic derivatives do.  The
logarithmic derivative of the left-hand side is read off the local factors, that of the
right-hand side off the cohomological ones, and the resulting identity of coefficients is the
trace formula

`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n / d})^* |_{ℱ_x̄}) = ∑_i (-1) ^ i tr((π_X^n)^* |_{H_c^i})`

for every `n ≥ 1`.  That is exactly the displayed identity in the Stacks proof of Theorem
64.20.2, equivalent by Möbius inversion to Theorem 64.20.5 applied to every finite extension
of `k`.  This file proves the reduction from that identity, stated as `TraceFormula`; the
identity itself is proved for `ℚ_ℓ`-sheaves from the trace formula of Tag 03V2, and Tag 03V0 is
`LAdicSheaf.nonempty_compactificationOf_and_rationalLFunction_eq_gradedCharSeries`.

## Main definitions

* `Stacks.EtaleCohomology.alternatingCharSeries`: the alternating product
  `∏_i det(1 - π_X^* T |_{H_c^i}) ^ ((-1) ^ (i + 1))`.
* `Stacks.EtaleCohomology.TraceFormula`: the trace formula displayed above.

## Main results

* `Stacks.EtaleCohomology.coeff_logDerivative_lFunction`: the logarithmic derivative of the
  L-function, coefficient by coefficient, as a sum of traces of powers of the local Frobenius
  matrices.
* `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction_eq_alternatingCharSeries`: the
  determinant identity, from the trace identity.

## Implementation notes

The cohomology is presented as a finite family of square matrices together with a degree, the
matrix at an index being the action of geometric Frobenius on the cohomology in that degree.
A degree in which the cohomology vanishes contributes the factor `1` to the product and the
summand `0` to the trace formula, so it may be omitted from the family; conversely a degree may
be split across several indices without changing either side.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0), Theorem 64.20.2.
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2), Theorem 64.20.5, the
  trace formula from which the trace identity is deduced.
* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV), the L-function.
* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ), the finite
  coefficient statement, which the source does not prove.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset Matrix PowerSeries

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The cohomological side -/

section Cohomology

variable {Λ : Type v} [CommRing Λ] {ι : Type w} [Fintype ι] (deg : ι → ℤ) (rk : ι → ℕ)
  (B : ∀ a : ι, Matrix (Fin (rk a)) (Fin (rk a)) Λ)

/-- The alternating product `∏_i det(1 - π_X^* T |_{H_c^i}) ^ ((-1) ^ (i + 1))` of the
characteristic series of a finite family of Frobenius matrices graded by cohomological degree:
an even degree contributes the inverse determinant, an odd degree the determinant. -/
public def alternatingCharSeries : Λ⟦X⟧ :=
  ∏ a : ι, if Even (deg a) then localEulerFactor (B a) 1 else localCharSeries (B a) 1

omit [Fintype ι] in
/-- Each factor of the alternating product has constant coefficient `1`. -/
private lemma constantCoeff_factor (a : ι) :
    constantCoeff (if Even (deg a) then localEulerFactor (B a) 1 else localCharSeries (B a) 1)
      = 1 := by
  split_ifs
  · exact constantCoeff_localEulerFactor (B a) 1
  · exact constantCoeff_localCharSeries (B a) one_ne_zero

/-- The alternating product has constant coefficient `1`, hence is a unit of `Λ⟦T⟧`. -/
public theorem constantCoeff_alternatingCharSeries :
    constantCoeff (alternatingCharSeries deg rk B) = 1 := by
  rw [alternatingCharSeries, map_prod]
  exact Finset.prod_eq_one fun a _ => constantCoeff_factor deg rk B a

/-- The logarithmic derivative of the alternating product is the alternating sum of the trace
series of the cohomological Frobenius matrices. -/
public theorem logDerivative_alternatingCharSeries :
    logDerivative (alternatingCharSeries deg rk B)
      = ∑ a : ι, (if Even (deg a) then (1 : Λ⟦X⟧) else -1) * traceSeries (B a) 1 := by
  rw [alternatingCharSeries,
    PowerSeries.logDerivative_finsetProd _ _ fun a _ => constantCoeff_factor deg rk B a]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : Even (deg a)
  · simp only [ha, ite_true]
    rw [logDerivative_localEulerFactor (B a) one_ne_zero]
    simp
  · simp only [ha, ite_false]
    rw [logDerivative_localCharSeries (B a) one_ne_zero]
    simp

/-- The coefficient of `T ^ m`, for `m ≥ 1`, of the logarithmic derivative of the alternating
product is `∑_i (-1) ^ i tr((π_X^m)^* |_{H_c^i})`. -/
public theorem coeff_logDerivative_alternatingCharSeries {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (alternatingCharSeries deg rk B))
      = ∑ a : ι, (if Even (deg a) then (1 : Λ) else -1) * ((B a) ^ m).trace := by
  rw [logDerivative_alternatingCharSeries, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : Even (deg a) <;>
    simp [ha, coeff_traceSeries, hm]

end Cohomology

/-! ### The local side -/

namespace FrobeniusMatrices

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] {Λ : Type v} [CommRing Λ] (D : FrobeniusMatrices f Λ)

omit [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Each local Euler factor has constant coefficient `1`. -/
private lemma constantCoeff_localFactor (x : closedPoints X) :
    constantCoeff (D.localFactor x) = 1 :=
  constantCoeff_localEulerFactor _ _

/-- The L-function agrees modulo `T ^ (m + 1)` with the product of the local Euler factors over
the closed points of degree at most `m`. -/
@[sga "7 XXII 3.0" "special case"]
public theorem X_pow_dvd_lFunction_sub_partialProduct (m : ℕ) :
    (PowerSeries.X : Λ⟦X⟧) ^ (m + 1) ∣
      D.lFunction - ∏ x ∈ D.eulerSystem.support m, D.localFactor x := by
  refine PowerSeries.X_pow_dvd_iff.2 fun j hj => ?_
  rw [map_sub, sub_eq_zero]
  exact D.coeff_lFunction_eq (D.eulerSystem.support_subset (by omega))

/-- The coefficient of `T ^ m`, for `m ≥ 1`, of the logarithmic derivative of the L-function is
`∑_{d ∣ m} d ∑_{deg x = d} tr((π_x^{m / d})^*)`. -/
public theorem coeff_logDerivative_lFunction {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative D.lFunction)
      = ∑ x ∈ (D.eulerSystem.support m).filter fun x => residueDegree f x.1 ∣ m,
          (residueDegree f x.1 : Λ) * ((D.matrix x) ^ (m / residueDegree f x.1)).trace := by
  have hc (x : closedPoints X) (_ : x ∈ D.eulerSystem.support m) :
      constantCoeff (D.localFactor x) = 1 := constantCoeff_localFactor D x
  rw [PowerSeries.coeff_logDerivative_congr D.constantCoeff_lFunction
      (by rw [map_prod]; exact Finset.prod_eq_one hc)
      (D.X_pow_dvd_lFunction_sub_partialProduct m),
    PowerSeries.logDerivative_finsetProd _ _ hc, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [localFactor, logDerivative_localEulerFactor _ (residueDegree_pos f x.1 x.2).ne',
    ← map_natCast C,
    PowerSeries.coeff_C_mul, coeff_traceSeries]
  by_cases hx : residueDegree f x.1 ∣ m
  · simp [hx, hm]
  · simp [hx]

/-- The trace formula relating the local Frobenius matrices of `D` to a finite family of
cohomological Frobenius matrices: for every `n ≥ 1`,
`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n / d})^* |_{ℱ_x̄}) = ∑_i (-1) ^ i tr((π_X^n)^* |_{H_c^i})`.
This is the displayed identity in the proof of Theorem 64.20.2, which the source deduces by
Möbius inversion from Theorem 64.20.5 applied to every finite extension of `k`. -/
public def TraceFormula {ι : Type w} [Fintype ι] (deg : ι → ℤ) (rk : ι → ℕ)
    (B : ∀ a : ι, Matrix (Fin (rk a)) (Fin (rk a)) Λ) : Prop :=
  ∀ m : ℕ, m ≠ 0 →
    ∑ x ∈ (D.eulerSystem.support m).filter fun x => residueDegree f x.1 ∣ m,
        (residueDegree f x.1 : Λ) * ((D.matrix x) ^ (m / residueDegree f x.1)).trace
      = ∑ a : ι, (if Even (deg a) then (1 : Λ) else -1) * ((B a) ^ m).trace

/-- **The reduction to the trace identity**, the first step of the proof of Theorem 64.20.2
(Stacks, Tag 03V0): for matrices satisfying the trace identity `TraceFormula`, the L-function is
the alternating product of their characteristic series,
`L(X, ℱ) = ∏_i det(1 - π_X^* T |_{H_c^i(X_k̄, ℱ)}) ^ ((-1) ^ (i + 1))`.
The coefficient ring is only required to have torsion-free additive group, which holds for
`ℚ_ℓ`; this is the hypothesis behind the source's "since `ℚ_ℓ` has characteristic `0`, it
suffices to prove the equality after taking logarithmic derivatives". Tag 03V0 itself, for a
`ℚ_ℓ`-sheaf with the trace identity proved from Tag 03V2, is
`LAdicSheaf.nonempty_compactificationOf_and_rationalLFunction_eq_gradedCharSeries`. -/
public theorem lFunction_eq_alternatingCharSeries [IsAddTorsionFree Λ] {ι : Type w} [Fintype ι]
    (deg : ι → ℤ) (rk : ι → ℕ) (B : ∀ a : ι, Matrix (Fin (rk a)) (Fin (rk a)) Λ)
    (htrace : D.TraceFormula deg rk B) :
    D.lFunction = alternatingCharSeries deg rk B := by
  refine PowerSeries.eq_of_logDerivative_eq D.constantCoeff_lFunction
    (constantCoeff_alternatingCharSeries deg rk B) (PowerSeries.ext fun m => ?_)
  rcases eq_or_ne m 0 with rfl | hm
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [D.coeff_logDerivative_lFunction hm,
      coeff_logDerivative_alternatingCharSeries deg rk B hm]
    exact htrace m hm

end FrobeniusMatrices

end Stacks.EtaleCohomology

end
