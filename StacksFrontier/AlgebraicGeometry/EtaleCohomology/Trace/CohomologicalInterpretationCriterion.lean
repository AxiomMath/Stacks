module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalInterpretation

/-!
# The cohomological interpretation of the L-function as a criterion

Grothendieck's cohomological interpretation of the L-function of a scheme `X` of finite type
over a finite field `k` is the identity

`L(X, ℱ) = ∏_i det(1 - π_X^* T |_{H_c^i(X_k̄, ℱ)}) ^ ((-1) ^ (i + 1))`

in `Λ⟦T⟧`.  The source reduces it, over a coefficient ring of characteristic zero, to the trace
identity

`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n / d})^* |_{ℱ_x̄}) = ∑_i (-1) ^ i tr((π_X^n)^* |_{H_c^i})`

for every `n ≥ 1`, by taking logarithmic derivatives and comparing coefficients.  The reduction
runs in both directions: over a coefficient ring with torsion-free additive group the
determinant identity and the trace identity are *equivalent*.  That equivalence is the main
result here, and it needs no further input.

The remaining results describe the alternating product on the right-hand side.  It is unchanged
by a change of basis in each cohomology group, so the identity speaks about the Frobenius action
and not about a presentation of it by matrices; it is unchanged by reindexing; and the indices
whose cohomology vanishes may be dropped.  Together these say that the right-hand side depends
only on the graded Frobenius action up to isomorphism.  Finally the alternating product is the
ratio of the product of the characteristic series in odd degrees by the product of those in even
degrees, which is the shape in which the identity exhibits the L-function as a rational
function.

## Main definitions

* `Stacks.EtaleCohomology.charSeriesEven` and `Stacks.EtaleCohomology.charSeriesOdd`: the
  products `∏_{i even} det(1 - π_X^* T |_{H_c^i})` and `∏_{i odd} det(1 - π_X^* T |_{H_c^i})`.

## Main results

* `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction_eq_alternatingCharSeries_iff`: the
  determinant identity holds exactly when the trace identity does.
* `Stacks.EtaleCohomology.FrobeniusMatrices.traceFormula_of_lFunction_eq`: the determinant
  identity implies the trace identity.
* `Stacks.EtaleCohomology.alternatingCharSeries_conj`,
  `Stacks.EtaleCohomology.alternatingCharSeries_equiv` and
  `Stacks.EtaleCohomology.alternatingCharSeries_subtype`: the alternating product is unchanged
  by a change of basis, by reindexing, and by dropping the indices of rank zero.
* `Stacks.EtaleCohomology.alternatingCharSeries_mul_charSeriesEven` and
  `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction_mul_charSeriesEven`: the alternating
  product, and under the identity the L-function itself, times the even characteristic series
  equals the odd one.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0), Theorem 64.20.2, whose
  proof reduces the determinant identity to the trace identity.
* [Stacks Project, Tag 03UY](https://stacks.math.columbia.edu/tag/03UY), Section 64.20.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset Matrix PowerSeries

universe u v w

namespace Stacks.EtaleCohomology

/-! ### Characteristic series of an empty family of matrices -/

section Empty

variable {Λ : Type v} [CommRing Λ] {n : Type w} [Fintype n] [DecidableEq n] [IsEmpty n]

/-- The characteristic series of a matrix indexed by an empty type is `1`. -/
public theorem localCharSeries_eq_one (A : Matrix n n Λ) (d : ℕ) : localCharSeries A d = 1 :=
  Matrix.det_isEmpty

/-- The Euler factor of a matrix indexed by an empty type is `1`. -/
public theorem localEulerFactor_eq_one (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    localEulerFactor A d = 1 := by
  have h := localCharSeries_mul_localEulerFactor A hd
  rwa [localCharSeries_eq_one, one_mul] at h

end Empty

/-! ### The alternating product depends only on the graded Frobenius action -/

section Cohomology

variable {Λ : Type v} [CommRing Λ] {ι : Type w} [Fintype ι] (deg : ι → ℤ) (rk : ι → ℕ)
  (B : ∀ a : ι, Matrix (Fin (rk a)) (Fin (rk a)) Λ)

omit [Fintype ι] in
/-- The factor of the alternating product at an index of rank zero is `1`, so such an index
contributes nothing. -/
public theorem alternatingCharSeries_factor_eq_one {a : ι} (ha : rk a = 0) :
    (if Even (deg a) then localEulerFactor (B a) 1 else localCharSeries (B a) 1) = 1 := by
  have : IsEmpty (Fin (rk a)) := by rw [ha]; infer_instance
  split_ifs
  · exact localEulerFactor_eq_one (B a) one_ne_zero
  · exact localCharSeries_eq_one (B a) 1

/-- The alternating product is unchanged on replacing each matrix `B a` by `P a * B a * Q a`
with `P a * Q a = 1`.  So the right-hand side of the cohomological interpretation depends on the
Frobenius action on each cohomology group and not on the basis in which it is written. -/
public theorem alternatingCharSeries_conj
    (P Q : ∀ a : ι, Matrix (Fin (rk a)) (Fin (rk a)) Λ) (hPQ : ∀ a, P a * Q a = 1) :
    alternatingCharSeries deg rk (fun a => P a * B a * Q a) = alternatingCharSeries deg rk B := by
  simp only [alternatingCharSeries]
  refine Finset.prod_congr rfl fun a _ => ?_
  split_ifs
  · exact localEulerFactor_conj (B a) 1 (hPQ a)
  · exact localCharSeries_conj (B a) 1 (hPQ a)

/-- The alternating product is unchanged by reindexing the family along an equivalence. -/
public theorem alternatingCharSeries_equiv {ι' : Type w} [Fintype ι'] (e : ι' ≃ ι) :
    alternatingCharSeries (fun a => deg (e a)) (fun a => rk (e a)) (fun a => B (e a))
      = alternatingCharSeries deg rk B := by
  simp only [alternatingCharSeries]
  exact Fintype.prod_equiv e _ _ fun _ => rfl

/-- The indices of rank zero may be dropped from the alternating product: a cohomological degree
in which the cohomology vanishes contributes the factor `1`. -/
public theorem alternatingCharSeries_subtype :
    alternatingCharSeries (fun a : {a : ι // rk a ≠ 0} => deg a.1) (fun a => rk a.1)
        (fun a => B a.1) = alternatingCharSeries deg rk B := by
  simp only [alternatingCharSeries]
  refine Eq.trans ?_ (Finset.prod_filter_of_ne (p := fun a : ι => rk a ≠ 0)
    fun a _ hne hrk => hne (alternatingCharSeries_factor_eq_one deg rk B hrk))
  exact (Finset.prod_subtype (p := fun a : ι => rk a ≠ 0)
    (Finset.univ.filter fun a : ι => rk a ≠ 0) (by simp)
    (fun a : ι => if Even (deg a) then localEulerFactor (B a) 1
      else localCharSeries (B a) 1)).symm

/-! ### The alternating product as a ratio -/

/-- The product `∏_{i even} det(1 - π_X^* T |_{H_c^i})` of the characteristic series in even
cohomological degrees, the denominator of the alternating product. -/
public def charSeriesEven : Λ⟦X⟧ :=
  ∏ a ∈ Finset.univ.filter fun a : ι => Even (deg a), localCharSeries (B a) 1

/-- The product `∏_{i odd} det(1 - π_X^* T |_{H_c^i})` of the characteristic series in odd
cohomological degrees, the numerator of the alternating product. -/
public def charSeriesOdd : Λ⟦X⟧ :=
  ∏ a ∈ Finset.univ.filter fun a : ι => ¬ Even (deg a), localCharSeries (B a) 1

/-- The alternating product is the odd characteristic series divided by the even one: multiplied
by the even product it gives the odd product.  This exhibits the right-hand side of the
cohomological interpretation as a ratio of two characteristic series. -/
public theorem alternatingCharSeries_mul_charSeriesEven :
    alternatingCharSeries deg rk B * charSeriesEven deg rk B = charSeriesOdd deg rk B := by
  have hcancel : (∏ a ∈ Finset.univ.filter fun a : ι => Even (deg a),
      localEulerFactor (B a) 1) * ∏ a ∈ Finset.univ.filter fun a : ι => Even (deg a),
        localCharSeries (B a) 1 = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => by
      rw [mul_comm]; exact localCharSeries_mul_localEulerFactor (B a) one_ne_zero
  rw [alternatingCharSeries, Finset.prod_ite, charSeriesEven, charSeriesOdd, mul_right_comm,
    hcancel, one_mul]

end Cohomology

/-! ### The criterion -/

namespace FrobeniusMatrices

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {Λ : Type v}
  [CommRing Λ] [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] (D : FrobeniusMatrices f Λ)
  {ι : Type w} [Fintype ι] (deg : ι → ℤ) (rk : ι → ℕ)
  (B : ∀ a : ι, Matrix (Fin (rk a)) (Fin (rk a)) Λ)

/-- If the L-function is the alternating product of the characteristic series of the
cohomological Frobenius matrices then the trace identity holds. -/
public theorem traceFormula_of_lFunction_eq
    (h : D.lFunction = alternatingCharSeries deg rk B) : D.TraceFormula deg rk B := by
  intro m hm
  rw [← D.coeff_logDerivative_lFunction hm,
    ← coeff_logDerivative_alternatingCharSeries deg rk B hm, h]

/-- **The cohomological interpretation of the L-function, as a criterion.**
Over a coefficient ring with torsion-free additive group the determinant identity
`L(X, ℱ) = ∏_i det(1 - π_X^* T |_{H_c^i(X_k̄, ℱ)}) ^ ((-1) ^ (i + 1))`
holds if and only if the trace identity
`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n / d})^* |_{ℱ_x̄}) = ∑_i (-1) ^ i tr((π_X^n)^* |_{H_c^i})`
holds for every `n ≥ 1`. -/
@[stacks 03V0 "the determinant identity, equivalent to the trace identity in the proof"]
public theorem lFunction_eq_alternatingCharSeries_iff [IsAddTorsionFree Λ] :
    D.lFunction = alternatingCharSeries deg rk B ↔ D.TraceFormula deg rk B :=
  ⟨D.traceFormula_of_lFunction_eq deg rk B, D.lFunction_eq_alternatingCharSeries deg rk B⟩

/-- Under the determinant identity the L-function is the ratio of the odd characteristic series
by the even one. -/
public theorem lFunction_mul_charSeriesEven
    (h : D.lFunction = alternatingCharSeries deg rk B) :
    D.lFunction * charSeriesEven deg rk B = charSeriesOdd deg rk B := by
  rw [h, alternatingCharSeries_mul_charSeriesEven]

end FrobeniusMatrices

end Stacks.EtaleCohomology

end
