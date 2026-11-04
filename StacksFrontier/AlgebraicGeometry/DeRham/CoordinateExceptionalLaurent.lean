module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupLaurentForms
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupTwistCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalBundle

/-!
# The functions on the exceptional divisor over an intersection of charts, as Laurent polynomials

Fix a ring `R`, `n ≥ 1`, the coordinate blowup `b : L ⟶ 𝐀^{m+n}_R` with exceptional divisor
`j : E ⟶ L`, and an intersection `V = L_{x₀} ∩ ⋯ ∩ L_{x_p}` of standard charts. A function `z` on
`V` is a Laurent polynomial all of whose exponents have nonnegative degree in the `y`'s, and the
exceptional divisor is cut out on `V` by `y_{x₀}`, of degree one. So the part of degree zero in
the `y`'s is a ring homomorphism on the functions on `V` that kills the ideal of `E`, and it
descends to the functions on `E ∩ V`.

## Main definitions

* `Stacks.DeRham.CoordinateCech.chartLaurentWt0`: the degree-zero part of the Laurent polynomial
  of a function on an intersection of charts, as a ring homomorphism.
* `Stacks.DeRham.CoordinateCech.exceptionalChartLaurent`: its descent to the functions on the
  exceptional divisor over the intersection of charts.

## Main results

* `Stacks.DeRham.CoordinateCech.exceptionalChartLaurent_app`: the descent, on the restriction of
  a function on the intersection of charts, is the degree-zero part of its Laurent polynomial.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite AddMonoidAlgebra

universe u

namespace Stacks.DeRham.CoordinateCech

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The Laurent polynomial of a function on an intersection of charts has only exponents of
nonnegative degree in the `y`'s. -/
theorem nonnegW_laurent_toFracOf_tupleOpen (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n)
    (z : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1)) :
    NonnegW (laurent R m n (toFracOf R m n hn (punctured_le_tupleOpen R m n hn x) z)) := by
  have hf := ((toFracOf_basicOpen_tupleRatio R m n hn x).2 _).1 ⟨z, rfl⟩
  have h := coeff_laurent_mem_supported R m n 0 x (h := toFracOf R m n hn
    (punctured_le_basicOpen_tupleRatio R m n hn x) z) (by rw [pow_zero, mul_one]; exact hf)
  intro v hv
  obtain ⟨⟨-, h2⟩, -⟩ := (Stacks.CechFinsupp.mem_supported.1 h) v hv
  simpa using h2

/-- **The degree-zero part of the Laurent polynomial of a function on an intersection of
charts**, as a ring homomorphism: it is multiplicative because all the exponents that occur have
nonnegative degree in the `y`'s. -/
def chartLaurentWt0 (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n) :
    Γ(coordinateBlowup R m n, (tupleOpen R m n x).1) →+* Lau R m n where
  toFun z := wt0 R m n (laurent R m n (toFracOf R m n hn (punctured_le_tupleOpen R m n hn x) z))
  map_one' := by rw [map_one, map_one, wt0_one]
  map_mul' z z' := by
    rw [map_mul, map_mul]
    exact wt0_mul (nonnegW_laurent_toFracOf_tupleOpen R m n hn x z)
      (nonnegW_laurent_toFracOf_tupleOpen R m n hn x z')
  map_zero' := by rw [map_zero, map_zero, map_zero]
  map_add' z z' := by rw [map_add, map_add, map_add]

/-- `chartLaurentWt0` sends a function to the degree-zero part of its Laurent polynomial. -/
theorem chartLaurentWt0_apply (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n)
    (z : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1)) :
    chartLaurentWt0 R m n hn x z =
      wt0 R m n (laurent R m n (toFracOf R m n hn (punctured_le_tupleOpen R m n hn x) z)) :=
  rfl

/-- The local equation `y_{x₀}` of the exceptional divisor has degree one, so its degree-zero
part vanishes. -/
theorem chartLaurentWt0_tupleGen (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n) :
    chartLaurentWt0 R m n hn x (tupleGen R m n x) = 0 := by
  rw [chartLaurentWt0_apply, tupleGen, toFracOf_res, toFracOf_chartMap, laurent_toFrac_coord,
    wt0_single, ite_eq_right (by rw [yDegree_yExp]; exact one_ne_zero)]

/-- The degree-zero part kills the ideal of the exceptional divisor. -/
theorem ker_subschemeι_app_le_ker_chartLaurentWt0 (hn : 0 < n) {p : ℕ}
    (x : Fin (p + 1) → Fin n) :
    RingHom.ker ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom ≤
      RingHom.ker (chartLaurentWt0 R m n hn x) := by
  intro z hz
  rw [Scheme.IdealSheafData.ker_subschemeι_app (coordinateExceptional R m n) (tupleOpen R m n x),
    ideal_tupleOpen, Ideal.mem_span_singleton'] at hz
  obtain ⟨c, rfl⟩ := hz
  rw [RingHom.mem_ker, map_mul, chartLaurentWt0_tupleGen, mul_zero]

/-- **The functions on the exceptional divisor over an intersection of charts, as Laurent
polynomials**: the descent of `chartLaurentWt0` along the surjection from the functions on the
intersection of charts. -/
def exceptionalChartLaurent (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n) :
    Γ(coordinateExceptionalScheme R m n,
        (coordinateExceptionalι R m n) ⁻¹ᵁ (tupleOpen R m n x).1) →+* Lau R m n :=
  RingHom.liftOfSurjective ((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom
    ((coordinateExceptional R m n).subschemeι_app_surjective (tupleOpen R m n x))
    ⟨chartLaurentWt0 R m n hn x, ker_subschemeι_app_le_ker_chartLaurentWt0 R m n hn x⟩

/-- **The descent on the restriction of a function**: the degree-zero part of the Laurent
polynomial of the function. -/
theorem exceptionalChartLaurent_app (hn : 0 < n) {p : ℕ} (x : Fin (p + 1) → Fin n)
    (z : Γ(coordinateBlowup R m n, (tupleOpen R m n x).1)) :
    exceptionalChartLaurent R m n hn x
        (((coordinateExceptionalι R m n).app (tupleOpen R m n x).1).hom z) =
      wt0 R m n (laurent R m n (toFracOf R m n hn (punctured_le_tupleOpen R m n hn x) z)) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ z

end Stacks.DeRham.CoordinateCech
