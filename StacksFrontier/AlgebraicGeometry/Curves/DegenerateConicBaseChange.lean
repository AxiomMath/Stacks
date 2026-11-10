module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIrreducibleEquation
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceFinitePresentation
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs

/-!
# A plane conic that is integral but not geometrically integral

Let `k` be a field in which `-1` is not a square and let `K/k` be an extension in which it is.
The quadratic form

```
F = T₀² + T₁²
```

is irreducible over `k` and reducible over `K`, being `(T₀ + iT₁)(T₀ - iT₁)` there. So the plane
curve `Z ⊆ 𝐏²_k` it cuts out is **integral** — a curve over `k` in the sense of [Stacks, Tag
0A23], by [Stacks, Tag 0BYC] — with `H⁰(Z, 𝒪_Z) = k` and **genus zero**, by [Stacks, Tag 0BYD],
while its base change to `K` is not integral: `Z_K` is the union of two distinct lines meeting at
one point.

## Main results

* `Stacks.Curves.DegenerateConic.conicForm_irreducible` and
  `Stacks.Curves.DegenerateConic.conicForm_not_irreducible`: `F` is irreducible over `k` and
  reducible over `K`.
* `Stacks.Curves.DegenerateConic.isCurve_conic`, `.genus_conic_eq_zero` and
  `.conicGlobalSectionsEquiv`: the plane curve `Z` cut out by `F` is a curve over `k`, of genus
  zero, with `H⁰(Z, 𝒪_Z) = k`; and `.not_isCurve_conic`: the same equation over `K` cuts out
  something that is not a curve.
* `Stacks.Curves.DegenerateConic.geometricallyIntegral_opens_ι`: geometric integrality over a
  field passes to a nonempty open of the source. This is the general lemma that carries a
  statement about an affine chart to the whole curve.
* `Stacks.Curves.DegenerateConic.not_geometricallyIntegral_conic`: **`Z` is not geometrically
  integral over `k`**, in Mathlib's `AlgebraicGeometry.GeometricallyIntegral` — the predicate
  [Stacks, Tag 0E65] asks of a rational bridge. Each standard chart of `Z` is
  `k[Y₀, Y₁]/(Y₀² + c²)`, whose base change to `K` has the zero divisors `Y₀ ⊗ 1 ± c ⊗ i`.
* `Stacks.Curves.DegenerateConic.isCurve_genus_zero_and_not_isCurve_baseChange`: the five
  together.

## References

* [Stacks Project, Tag 0BYC](https://stacks.math.columbia.edu/tag/0BYC)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme (idealOfClosedSubscheme)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (PlaneCurveData genus_planeCurve
  planeCurveGlobalSectionsEquiv)

universe u

namespace Stacks.Curves.DegenerateConic

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The quadratic form and its irreducibility -/

/-- **The degenerate conic `T₀² + T₁²`.** Over a field in which `-1` is not a square it is
irreducible; over one in which `-1` is a square it factors as `(T₀ + iT₁)(T₀ - iT₁)`. -/
def conicForm (k : Type u) [CommRing k] : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2

/-- The form `T₀² + T₁²` is homogeneous of degree `2`. -/
theorem conicForm_isHomogeneous (k : Type u) [CommRing k] :
    (conicForm k).IsHomogeneous 2 := by
  refine MvPolynomial.IsHomogeneous.add ?_ ?_
  · simpa using (MvPolynomial.isHomogeneous_X k (0 : Fin 3)).pow 2
  · simpa using (MvPolynomial.isHomogeneous_X k (1 : Fin 3)).pow 2

/-- Over a nontrivial ring the form `T₀² + T₁²` is nonzero. -/
theorem conicForm_ne_zero (k : Type u) [CommRing k] [Nontrivial k] :
    conicForm k ≠ 0 := by
  intro h
  have := congrArg (fun p : MvPolynomial (Fin 3) k => p.coeff (Finsupp.single (0 : Fin 3) 2)) h
  rw [conicForm] at this
  simp [MvPolynomial.coeff_X_pow, Finsupp.single_eq_single_iff] at this

/-- The form read as a monic quadratic in `T₀` with coefficients in `k[T₁, T₂]`. -/
theorem finSuccEquiv_conicForm (k : Type u) [Field k] :
    MvPolynomial.finSuccEquiv k 2 (conicForm k) =
      Polynomial.X ^ 2 + Polynomial.C ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2) := by
  have h1 : (1 : Fin 3) = Fin.succ (0 : Fin 2) := rfl
  rw [conicForm]
  simp only [map_add, map_pow, MvPolynomial.finSuccEquiv_X_zero, h1,
    MvPolynomial.finSuccEquiv_X_succ]

/-- **`-1` is not a square in the field of rational functions in two variables** over a field in
which it is not a square. A square root of `-1` is integral over `k[Y₀, Y₁]`, which is a unique
factorization domain and hence integrally closed, so it is a polynomial; evaluating at the origin
puts a square root of `-1` in `k`. -/
theorem not_isSquare_neg_one_fractionRing {k : Type u} [Field k] (hk : ∀ c : k, c ^ 2 ≠ -1)
    (b : FractionRing (MvPolynomial (Fin 2) k)) : b ^ 2 ≠ -1 := by
  intro hb
  have hint : IsIntegral (MvPolynomial (Fin 2) k) b := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).add_of_left (by simp)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one]
      rw [hb]
      ring
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hs2 : (s : MvPolynomial (Fin 2) k) ^ 2 = -1 := by
    have heq : algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
          (s ^ 2) =
        algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k)) (-1) := by
      rw [map_pow, hs, hb, map_neg, map_one]
    exact IsFractionRing.injective (MvPolynomial (Fin 2) k)
      (FractionRing (MvPolynomial (Fin 2) k)) heq
  have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : k))) hs2
  simp only [map_pow, map_neg, map_one] at this
  exact hk _ this

/-- **The degenerate conic is irreducible over a field in which `-1` is not a square.** Read as
the monic quadratic `T₀² + T₁²` over `k[T₁, T₂]`, which is integrally closed, it is irreducible
exactly when it is over the field of rational functions (Gauss's lemma), where it is
`X² - C(-T₁²)` and the Kummer criterion applies: a square root of `-T₁²` would give one of `-1`.

With [Stacks, Tag 0BYC] this is what makes the zero scheme a curve over `k`. -/
theorem conicForm_irreducible {k : Type u} [Field k] (hk : ∀ c : k, c ^ 2 ≠ -1) :
    Irreducible (conicForm k) := by
  set A := MvPolynomial (Fin 2) k with hA
  set F := FractionRing A with hF
  refine (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv k 2).toMulEquiv).mp ?_
  change Irreducible (MvPolynomial.finSuccEquiv k 2 (conicForm k))
  rw [finSuccEquiv_conicForm k]
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C ((MvPolynomial.X 0 : A) ^ 2)).Monic := by
    refine (Polynomial.monic_X_pow 2).add_of_left ?_
    exact lt_of_le_of_lt (Polynomial.degree_C_le) (by
      rw [Polynomial.degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by norm_num))
  rw [hmonic.irreducible_iff_irreducible_map_fraction_map (K := F)]
  have hmap : Polynomial.map (algebraMap A F)
      (Polynomial.X ^ 2 + Polynomial.C ((MvPolynomial.X 0 : A) ^ 2)) =
      Polynomial.X ^ 2 - Polynomial.C (-(algebraMap A F (MvPolynomial.X 0)) ^ 2) := by
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      map_pow, Polynomial.C_neg]
    ring
  rw [hmap]
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two ?_
  intro b hb
  have hx : algebraMap A F (MvPolynomial.X 0) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact MvPolynomial.X_ne_zero 0
  have hone : (b / algebraMap A F (MvPolynomial.X 0)) ^ 2 = -1 := by
    rw [div_pow, hb, neg_div, div_self (pow_ne_zero 2 hx)]
  exact not_isSquare_neg_one_fractionRing hk _ hone

/-- **Over a field in which `-1` is a square the degenerate conic is reducible.** -/
theorem conicForm_not_irreducible {K : Type u} [Field K] (i : K) (hi : i ^ 2 = -1) :
    ¬ Irreducible (conicForm K) := by
  intro h
  set A := MvPolynomial (Fin 2) K with hA
  have h' : Irreducible (MvPolynomial.finSuccEquiv K 2 (conicForm K)) :=
    (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 2).toMulEquiv).mpr h
  rw [finSuccEquiv_conicForm K] at h'
  set y : A := MvPolynomial.C i * MvPolynomial.X 0 with hy
  have hfac : (Polynomial.X ^ 2 + Polynomial.C ((MvPolynomial.X 0 : A) ^ 2) :
      Polynomial A) = (Polynomial.X + Polynomial.C y) * (Polynomial.X - Polynomial.C y) := by
    have hy2 : y ^ 2 = -(MvPolynomial.X (0 : Fin 2) : A) ^ 2 := by
      rw [hy, mul_pow, ← map_pow, hi]
      simp only [map_neg, map_one]
      ring
    rw [show (Polynomial.X + Polynomial.C y) * (Polynomial.X - Polynomial.C y) =
      Polynomial.X ^ 2 - Polynomial.C (y ^ 2) from by rw [Polynomial.C_pow]; ring, hy2]
    simp only [map_neg]
    ring
  have hdeg : ∀ c : A, ¬ IsUnit (Polynomial.X + Polynomial.C c) := by
    intro c hu
    have := Polynomial.degree_eq_zero_of_isUnit hu
    rw [Polynomial.degree_X_add_C] at this
    exact one_ne_zero this
  rcases h'.isUnit_or_isUnit hfac with hu | hu
  · exact hdeg y hu
  · refine hdeg (-y) ?_
    rwa [map_neg, ← sub_eq_add_neg]

/-! ### The affine charts of the conic and their base change -/

/-- The constant of the chart equation: dehomogenizing `T₀² + T₁²` at `Tⱼ` gives
`Y₀² + (cⱼ)²`, with `c₂ = Y₁` and `c₀ = c₁ = 1`. -/
def conicChartC (k : Type u) [CommRing k] (j : Fin 3) : MvPolynomial (Fin 2) k :=
  if j = 2 then MvPolynomial.X 1 else 1

/-- The equation of the chart `Z ∩ D₊(Tⱼ)` of the degenerate conic. -/
abbrev conicChartIdeal (k : Type u) [CommRing k] (c : MvPolynomial (Fin 2) k) :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 + c ^ 2}

/-- The coordinate ring of the chart `Z ∩ D₊(Tⱼ)` of the degenerate conic:
`k[Y₀, Y₁]/(Y₀² + c²)`. -/
abbrev conicChartRing (k : Type u) [CommRing k] (c : MvPolynomial (Fin 2) k) : Type u :=
  MvPolynomial (Fin 2) k ⧸ conicChartIdeal k c

/-- The dehomogenization of `T₀² + T₁²` at `Tⱼ`, in terms of the images of `0, 1` under
`finSuccEquiv' j`. -/
private theorem dehomCoeff_conicForm_eq (k : Type u) [CommRing k] (j : Fin 3) :
    Stacks.ProjectiveChart.dehomCoeff k j (conicForm k) =
      (Option.elim (finSuccEquiv' j 0) 1 MvPolynomial.X : MvPolynomial (Fin 2) k) ^ 2 +
        (Option.elim (finSuccEquiv' j 1) 1 MvPolynomial.X : MvPolynomial (Fin 2) k) ^ 2 := by
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, conicForm, map_add, map_pow, map_pow,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X]

/-- The dehomogenization of the degenerate conic at `T₀` is `1 + Y₀²`. -/
theorem dehomCoeff_conicForm_zero (k : Type u) [CommRing k] :
    Stacks.ProjectiveChart.dehomCoeff k 0 (conicForm k) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 + 1 := by
  rw [dehomCoeff_conicForm_eq, show finSuccEquiv' (0 : Fin 3) 0 = none by decide,
    show finSuccEquiv' (0 : Fin 3) 1 = some 0 by decide]
  simp [add_comm]

/-- The dehomogenization of the degenerate conic at `T₁` is `Y₀² + 1`. -/
theorem dehomCoeff_conicForm_one (k : Type u) [CommRing k] :
    Stacks.ProjectiveChart.dehomCoeff k 1 (conicForm k) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 + 1 := by
  rw [dehomCoeff_conicForm_eq, show finSuccEquiv' (1 : Fin 3) 0 = some 0 by decide,
    show finSuccEquiv' (1 : Fin 3) 1 = none by decide]
  simp

/-- The dehomogenization of the degenerate conic at `T₂` is `Y₀² + Y₁²`. -/
theorem dehomCoeff_conicForm_two (k : Type u) [CommRing k] :
    Stacks.ProjectiveChart.dehomCoeff k 2 (conicForm k) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 +
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2 := by
  rw [dehomCoeff_conicForm_eq, show finSuccEquiv' (2 : Fin 3) 0 = some 0 by decide,
    show finSuccEquiv' (2 : Fin 3) 1 = some 1 by decide]
  simp

/-- **The dehomogenizations of the degenerate conic.** At `T₂` the chart equation is
`Y₀² + Y₁²`; at `T₀` and at `T₁` it is `Y₀² + 1`. -/
theorem dehomCoeff_conicForm (k : Type u) [CommRing k] (j : Fin 3) :
    Stacks.ProjectiveChart.dehomCoeff k j (conicForm k) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 + (conicChartC k j) ^ 2 := by
  fin_cases j
  · exact (dehomCoeff_conicForm_zero k).trans (by simp [conicChartC])
  · exact (dehomCoeff_conicForm_one k).trans (by simp [conicChartC])
  · exact (dehomCoeff_conicForm_two k).trans (by simp [conicChartC])

/-- Evaluation of a chart coordinate ring at `Y₀ ↦ t`, `Y₁ ↦ 1`: the generic point of one of the
two lines into which the conic splits over a field holding a square root of `-1`. -/
def conicEval {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] (t : K) :
    MvPolynomial (Fin 2) k →ₐ[k] K :=
  MvPolynomial.aeval (fun l : Fin 2 => if l = 0 then t else 1)

/-- `conicEval t` sends `Y₀` to `t`. -/
@[simp] theorem conicEval_X_zero {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    (t : K) : conicEval (k := k) t (MvPolynomial.X (0 : Fin 2)) = t := by
  simp [conicEval]

/-- `conicEval t` sends each chart coefficient `conicChartC k j` to `1`. -/
@[simp] theorem conicEval_conicChartC {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    (t : K) (j : Fin 3) : conicEval (k := k) t (conicChartC k j) = 1 := by
  fin_cases j <;> simp [conicChartC, conicEval]

/-- The `k`-algebra map `k[Y₀, Y₁]/(Y₀² + c²) ⟶ K` at `Y₀ ↦ t`, `Y₁ ↦ 1`, for `t² = -1` and `c`
evaluating to `1`. -/
def conicChartEval {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    (c : MvPolynomial (Fin 2) k) (t : K) (ht : t ^ 2 = -1) (hc : conicEval (k := k) t c = 1) :
    conicChartRing k c →ₐ[k] K :=
  Ideal.Quotient.liftₐ _ (conicEval t) (by
    intro a ha
    have hgen : conicEval (k := k) t
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 + c ^ 2) = 0 := by
      rw [map_add, map_pow, map_pow, conicEval_X_zero, hc, ht]
      ring
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨d, rfl⟩ := ha
    rw [map_mul, hgen, zero_mul])

/-- `conicChartEval c t ht hc` sends the class of `y` to `conicEval t y`. -/
@[simp] theorem conicChartEval_mk {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    (c : MvPolynomial (Fin 2) k) (t : K) (ht : t ^ 2 = -1) (hc : conicEval (k := k) t c = 1)
    (y : MvPolynomial (Fin 2) k) :
    conicChartEval c t ht hc (Ideal.Quotient.mk (conicChartIdeal k c) y) = conicEval t y := rfl

/-- **A chart of the degenerate conic is not geometrically integral over `k`.** Write `x` and `y`
for the classes of `Y₀` and `c`, so that `x² + y² = 0`. The base change to a field `K` holding a
square root `i` of `-1` contains `x ⊗ 1 ± y ⊗ i`, whose product is `(x² + y²) ⊗ 1 = 0`. Each is
nonzero because one of the two `K`-algebra maps determined by `Y₀ ↦ ±i`, `Y₁ ↦ 1` sends it to
`±2i ≠ 0`; the characteristic is not two because `-1` is not a square in `k`. -/
theorem not_isDomain_tensor_conicChartRing {k : Type u} [Field k] (hk : ∀ a : k, a ^ 2 ≠ -1)
    (K : Type u) [Field K] [Algebra k K] (i : K) (hi : i ^ 2 = -1)
    (c : MvPolynomial (Fin 2) k) (hci : conicEval (k := k) i c = 1)
    (hcn : conicEval (k := k) (-i) c = 1) :
    ¬ IsDomain (conicChartRing k c ⊗[k] K) := by
  intro hdom
  have h2k : (2 : k) ≠ 0 := by
    intro h
    refine hk 1 ?_
    rw [one_pow]
    linear_combination h
  have h2 : (2 : K) ≠ 0 := by
    intro h
    refine h2k ?_
    have halg : algebraMap k K (2 : k) = 0 := by rw [map_ofNat]; exact h
    exact (map_eq_zero_iff (algebraMap k K) (algebraMap k K).injective).mp halg
  have hneg : (-i) ^ 2 = -1 := by rw [neg_pow]; simpa using hi
  set x : conicChartRing k c :=
    Ideal.Quotient.mk (conicChartIdeal k c) (MvPolynomial.X 0) with hx
  set y : conicChartRing k c := Ideal.Quotient.mk (conicChartIdeal k c) c with hy
  have hsum : x ^ 2 + y ^ 2 = 0 := by
    have hmem : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ^ 2 + c ^ 2 ∈
        conicChartIdeal k c := Ideal.mem_span_singleton_self _
    have h0 : Ideal.Quotient.mk (conicChartIdeal k c)
        ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ^ 2 + c ^ 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_add, map_pow, map_pow, ← hx, ← hy] at h0
    exact h0
  -- `x ⊗ 1 + y ⊗ t` is nonzero for `t = ± i`, as an algebra map sends it to `2t`
  have hne : ∀ t : K, t ^ 2 = -1 → ∀ hct : conicEval (k := k) t c = 1,
      x ⊗ₜ[k] (1 : K) + y ⊗ₜ t ≠ 0 := by
    intro t ht hct h
    have hval : Algebra.TensorProduct.productMap (conicChartEval c t ht hct) (AlgHom.id k K)
        (x ⊗ₜ[k] (1 : K) + y ⊗ₜ t) = t + t := by
      rw [map_add]
      simp only [Algebra.TensorProduct.productMap_apply_tmul, hx, hy, conicChartEval_mk,
        conicEval_X_zero, hct, AlgHom.coe_id, id_eq, mul_one, one_mul]
    rw [h, map_zero] at hval
    have htwo : (2 : K) * t = 0 := by linear_combination -hval
    rcases mul_eq_zero.mp htwo with h' | h'
    · exact h2 h'
    · rw [h'] at ht
      simp at ht
  have hprod : (x ⊗ₜ[k] (1 : K) + y ⊗ₜ i) * (x ⊗ₜ[k] (1 : K) + y ⊗ₜ (-i)) = 0 := by
    calc (x ⊗ₜ[k] (1 : K) + y ⊗ₜ i) * (x ⊗ₜ[k] (1 : K) + y ⊗ₜ (-i))
        = (x ⊗ₜ[k] (1 : K)) ^ 2 - (y ⊗ₜ[k] i) ^ 2 := by rw [TensorProduct.tmul_neg]; ring
      _ = (x ^ 2) ⊗ₜ[k] (1 : K) - (y ^ 2) ⊗ₜ[k] (i ^ 2) := by
            rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow]
      _ = (x ^ 2) ⊗ₜ[k] (1 : K) + (y ^ 2) ⊗ₜ[k] (1 : K) := by
            rw [hi, TensorProduct.tmul_neg]
            ring
      _ = (x ^ 2 + y ^ 2) ⊗ₜ[k] (1 : K) := (TensorProduct.add_tmul _ _ _).symm
      _ = 0 := by rw [hsum, TensorProduct.zero_tmul]
  rcases mul_eq_zero.mp hprod with h | h
  · exact hne i hi hci h
  · exact hne (-i) hneg hcn h

/-- **A chart of the degenerate conic is not geometrically integral**, in the morphism-property
sense of [Stacks, Tag 05DX] — the predicate that [Stacks, Tag 0E65] asks of a rational bridge. -/
theorem not_isGeometricallyIntegral_conicChartRing {k : Type u} [Field k]
    (hk : ∀ a : k, a ^ 2 ≠ -1) (K : Type u) [Field K] [Algebra k K] (i : K) (hi : i ^ 2 = -1)
    (c : MvPolynomial (Fin 2) k) (hci : conicEval (k := k) i c = 1)
    (hcn : conicEval (k := k) (-i) c = 1) :
    ¬ Algebra.IsGeometricallyIntegral k (conicChartRing k c) := by
  intro h
  exact not_isDomain_tensor_conicChartRing hk K i hi c hci hcn
    ((Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k (conicChartRing k c)).mp h K)

/-! ### Geometric integrality passes to a nonempty open of the source -/

/-- **A field-valued base change of a scheme over a field is surjective.** Both spectra have a
single point. -/
theorem surjective_of_spec_field {k K : Type u} [Field k] [Field K]
    (y : Spec (.of K) ⟶ Spec (.of k)) : Surjective y :=
  ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- **Geometric integrality passes to a nonempty open of the source.** Let `f : X ⟶ Spec k` with
`k` a field and let `U ⊆ X` be a nonempty open. Every field-valued base change `q : P ⟶ X` of `f`
is surjective, so `q ⁻¹ᵁ U` is a nonempty open of the integral scheme `P` and hence integral; and
`q ⁻¹ᵁ U` is the base change of `U.ι ≫ f` along the same field-valued point, by pasting the
cartesian square of an open immersion onto the cartesian square of the base change.

This is what makes a statement about an affine chart of a curve a statement about the curve: if
some chart of `X` fails to be geometrically integral over `k`, then so does `X`. -/
theorem geometricallyIntegral_opens_ι {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] (U : X.Opens) [Nonempty U] :
    GeometricallyIntegral (U.ι ≫ f) := by
  refine ⟨fun K _ y Z' fst snd hsq => ?_⟩
  have hP : IsIntegral (Limits.pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral y _ _ (IsPullback.of_hasPullback f y)
  have hqsurj : Surjective (Limits.pullback.fst f y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback f y).flip
      (surjective_of_spec_field y)
  have hne : Nonempty (Limits.pullback.fst f y ⁻¹ᵁ U) := by
    obtain ⟨u⟩ := ‹Nonempty U›
    obtain ⟨p, hp⟩ := hqsurj.surj (U.ι.base u)
    refine ⟨⟨p, ?_⟩⟩
    change (Limits.pullback.fst f y).base p ∈ U
    rw [hp]
    exact u.2
  have hpaste : IsPullback (Limits.pullback.fst f y ∣_ U)
      ((Limits.pullback.fst f y ⁻¹ᵁ U).ι ≫ Limits.pullback.snd f y) (U.ι ≫ f) y :=
    (isPullback_morphismRestrict (Limits.pullback.fst f y) U).paste_vert
      (IsPullback.of_hasPullback f y)
  exact ObjectProperty.prop_of_iso (AlgebraicGeometry.IsIntegral (X := ·))
    (hpaste.isoIsPullback _ _ hsq) inferInstance

/-! ### The conic as a plane curve: integral, of genus zero, with constant functions -/

/-- **The plane-curve data of the degenerate conic**, with the degree recorded as the literal
`2`, so that the genus formula of [Stacks, Tag 0BYD] returns `(2 - 1)(2 - 2)/2` with no
rewriting. -/
def conicData {k : Type u} [Field k] {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion iZ]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    PlaneCurveData k where
  Z := Z
  i := iZ
  isClosedImmersion := ‹IsClosedImmersion iZ›
  nonempty := ‹Nonempty Z›
  hasNoEmbeddedPoints := hno
  equidimensional := hdim
  deg := 2
  F := conicForm k
  isHomogeneous := (MvPolynomial.mem_homogeneousSubmodule 2 _).2 (conicForm_isHomogeneous k)
  span_eq := hI

/-- The plane-curve data `conicData` has degree `2`. -/
@[simp] theorem conicData_deg {k : Type u} [Field k] {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion iZ]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    (conicData iZ hno hdim hI).deg = 2 := rfl

/-- **The genus of the degenerate conic is zero**, by the degree formula of [Stacks, Tag 0BYD]
at `deg F = 2`: `(2 - 1)(2 - 2)/2 = 0`. No genus value is assumed. -/
theorem genus_conic_eq_zero {k : Type u} [Field k] {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion iZ]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    genus (iZ ≫ projToSpecCoeff k 2) = 0 :=
  (genus_planeCurve (conicData iZ hno hdim hI)).trans (by rw [conicData_deg])

/-- **The global functions on the degenerate conic are the constants**, by [Stacks, Tag 0BYD].
So the field `k'` of [Stacks, Tag 0E3M] attached to this curve is `k` itself. -/
def conicGlobalSectionsEquiv {k : Type u} [Field k] {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion iZ]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    structureSheafCohomology (iZ ≫ projToSpecCoeff k 2) 0 ≃ₗ[k] k :=
  planeCurveGlobalSectionsEquiv (conicData iZ hno hdim hI)

/-- **The degenerate conic is a curve over `k`** — integral, by [Stacks, Tag 0BYC], because its
equation is irreducible over `k`. -/
theorem isCurve_conic {k : Type u} [Field k] (hk : ∀ c : k, c ^ 2 ≠ -1) {Z : Scheme.{u}}
    [Nonempty Z] (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    [IsClosedImmersion iZ]
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    IsCurve k (iZ ≫ projToSpecCoeff k 2) :=
  (ProjectiveSpectrum.Proj.projectivePlane_isCurve_iff_irreducible_of_equidimensional
    k iZ hdim hI).mpr (conicForm_irreducible hk)

/-- **The same equation over `K` does not cut out a curve.** Over a field containing a square
root of `-1` the form `T₀² + T₁²` is reducible, so by [Stacks, Tag 0BYC] the closed subscheme of
`𝐏²_K` it cuts out is not integral: it is the union of two distinct lines. -/
theorem not_isCurve_conic {K : Type u} [Field K] (i : K) (hi : i ^ 2 = -1) {W : Scheme.{u}}
    [Nonempty W] (iW : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    [IsClosedImmersion iW]
    (hdim : ∀ V ∈ irreducibleComponents W, topologicalKrullDim V = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) K) iW =
      Ideal.span {conicForm K}) :
    ¬ IsCurve K (iW ≫ projToSpecCoeff K 2) := fun h =>
  conicForm_not_irreducible i hi
    ((ProjectiveSpectrum.Proj.projectivePlane_isCurve_iff_irreducible_of_equidimensional
      K iW hdim hI).mp h)

/-- A nonempty affine open of a geometrically integral `k`-scheme has geometrically integral
ring of sections, in the form of the induced map of spectra. -/
private theorem geometricallyIntegral_specMap_appLE {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] {V : X.Opens} (hV : IsAffineOpen V)
    [Nonempty V] : GeometricallyIntegral (Spec.map (f.appLE ⊤ V le_top)) := by
  have : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hgiV : GeometricallyIntegral (V.ι ≫ f) := geometricallyIntegral_opens_ι f V
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of k))) hV
    (le_top : V ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, ← IsAffineOpen.isoSpec_inv_ι] at hsq
  have hfactor : V.ι ≫ f =
      hV.isoSpec.hom ≫ Spec.map (f.appLE ⊤ V le_top) ≫ (Spec (.of k)).isoSpec.inv := by
    rw [hsq]
    simp
  rw [hfactor] at hgiV
  exact (MorphismProperty.cancel_right_of_respectsIso (@GeometricallyIntegral) _
    (Spec (.of k)).isoSpec.inv).mp
    ((MorphismProperty.cancel_left_of_respectsIso (@GeometricallyIntegral) hV.isoSpec.hom _).mp
      hgiV)

/-- **The degenerate plane conic is not geometrically integral over `k`.**

The chart `Z ∩ D₊(T₁)` is the affine hypersurface `k[Y₀, Y₁]/(Y₀² + 1)`, by
[Stacks, Tag 0BYB]'s chart presentation at the dehomogenization of `T₀² + T₁²` at `T₁`, and the
`k`-algebra structure that presentation carries is the one the structure morphism induces. That
chart is not geometrically integral, and `geometricallyIntegral_opens_ι` carries the failure
from the chart to the curve. -/
theorem not_geometricallyIntegral_conic {k : Type u} [Field k] (hk : ∀ c : k, c ^ 2 ≠ -1)
    (K : Type u) [Field K] [Algebra k K] (i : K) (hi : i ^ 2 = -1)
    {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    [IsClosedImmersion iZ]
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k}) :
    ¬ GeometricallyIntegral (iZ ≫ projToSpecCoeff k 2) := by
  intro hgi
  have : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  set f : Z ⟶ Spec (.of k) := iZ ≫ projToSpecCoeff k 2
  -- the standard charts cover `Z`, so one of them is nonempty
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hz : z ∈ (⨆ l : Fin 3, Stacks.ProjectiveChart.subschemeChart iZ l) := by
    rw [Stacks.ProjectiveChart.iSup_subschemeChart_eq_top]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  set V : Z.Opens := Stacks.ProjectiveChart.subschemeChart iZ j
  have hVaff : IsAffineOpen V := Stacks.ProjectiveChart.isAffineOpen_subschemeChart iZ j
  have : Nonempty V := ⟨⟨z, hj⟩⟩
  set φ : Γ(Spec (.of k), ⊤) ⟶ Γ(Z, V) := f.appLE ⊤ V le_top
  have hgiV : GeometricallyIntegral (Spec.map φ) := geometricallyIntegral_specMap_appLE f hVaff
  -- transport to the `k`-algebra structure of the chart
  let : Algebra k Γ(Z, V) := ((Scheme.ΓSpecIso (.of k)).inv ≫ φ).hom.toAlgebra
  have halg : Algebra.IsGeometricallyIntegral k Γ(Z, V) := by
    change GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, V))))
    have hcomp : Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, V))) =
        Spec.map φ ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
      rw [← Spec.map_comp]
      rfl
    rw [hcomp]
    exact (MorphismProperty.cancel_right_of_respectsIso (@GeometricallyIntegral) (Spec.map φ)
      (Spec.map (Scheme.ΓSpecIso (.of k)).inv)).mpr hgiV
  -- the chart is `k[Y₀, Y₁]/(Y₀² + 1)` as a `k`-algebra
  have hFhom : conicForm k ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k (2 • 1) := by
    simpa using (MvPolynomial.mem_homogeneousSubmodule 2 _).2 (conicForm_isHomogeneous k)
  have hid : conicChartIdeal k (conicChartC k j) =
      Ideal.span {Stacks.ProjectiveChart.dehomCoeff k j (conicForm k)} := by
    rw [dehomCoeff_conicForm]
  let e : conicChartRing k (conicChartC k j) ≃+* Γ(Z, V) :=
    (Ideal.quotEquivOfEq hid).trans
      (Stacks.ProjectiveChart.chartQuotientEquiv iZ j (conicForm k) hFhom hI)
  have hek : ∀ r : k,
      e (algebraMap k (conicChartRing k (conicChartC k j)) r) = algebraMap k Γ(Z, V) r := by
    intro r
    change (Stacks.ProjectiveChart.chartQuotientEquiv iZ j (conicForm k) hFhom hI)
      (Ideal.quotEquivOfEq hid (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
    rw [Ideal.quotEquivOfEq_mk,
      Stacks.ProjectiveChart.chartQuotientEquiv_mk iZ j (conicForm k) hFhom hI]
    exact Stacks.ProjectiveChart.chartPresentation_C iZ j r
  let eA : conicChartRing k (conicChartC k j) ≃ₐ[k] Γ(Z, V) := { e with commutes' := hek }
  refine not_isDomain_tensor_conicChartRing hk K i hi (conicChartC k j)
    (conicEval_conicChartC i j) (conicEval_conicChartC (-i) j) ?_
  have hdom : IsDomain (Γ(Z, V) ⊗[k] K) :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k Γ(Z, V)).mp halg K
  exact MulEquiv.isDomain (Γ(Z, V) ⊗[k] K)
    (Algebra.TensorProduct.congr eA (AlgEquiv.refl (R := k) (A₁ := K))).toRingEquiv.toMulEquiv

/-- **The degenerate conic settles the inference "genus-zero curve over its field of global
functions, hence a conic, hence geometrically integral".**

Let `k` be a field in which `-1` is not a square and `K/k` an extension in which it is — for
instance `ℝ ⊆ ℂ`. Let `Z ⊆ 𝐏²_k` and `W ⊆ 𝐏²_K` be the closed subschemes cut out by
`T₀² + T₁²` over `k` and over `K`, each equidimensional of dimension one without embedded
points. Then

* `Z` is a curve over `k`, that is an **integral** closed subscheme,
* its **genus is zero** and its **global functions are exactly `k`**, so `k' = H⁰(Z, 𝒪_Z) = k`
  and `Z` has genus zero over `k'`, which are clauses (2) and (3) of [Stacks, Tag 0E3M], and
* `W` — the same equation over `K` — is **not** a curve over `K`, and
* `Z` is **not geometrically integral** over `k`, in Mathlib's
  `AlgebraicGeometry.GeometricallyIntegral` — the predicate [Stacks, Tag 0E65] asks of a
  rational bridge.

The last two clauses are the same failure read twice: the equation becomes reducible over `K`,
and each affine chart `k[Y₀, Y₁]/(Y₀² + c²)` of `Z` acquires the zero divisors
`Y₀ ⊗ 1 ± c ⊗ i` after base change.

So an integral plane conic of genus zero over its own field of global functions need not be
geometrically integral: a degenerate conic, the norm form of a separable quadratic extension, is
irreducible over `k` and splits into two conjugate lines over `K`. -/
theorem isCurve_genus_zero_and_not_isCurve_baseChange {k : Type u} [Field k]
    (hk : ∀ c : k, c ^ 2 ≠ -1) {K : Type u} [Field K] [Algebra k K] (i : K) (hi : i ^ 2 = -1)
    {Z : Scheme.{u}} [Nonempty Z]
    (iZ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion iZ]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ V ∈ irreducibleComponents Z, topologicalKrullDim V = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) iZ =
      Ideal.span {conicForm k})
    {W : Scheme.{u}} [Nonempty W]
    (iW : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) K)) [IsClosedImmersion iW]
    (hdimW : ∀ V ∈ irreducibleComponents W, topologicalKrullDim V = 1)
    (hIW : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) K) iW =
      Ideal.span {conicForm K}) :
    IsCurve k (iZ ≫ projToSpecCoeff k 2) ∧
      genus (iZ ≫ projToSpecCoeff k 2) = 0 ∧
      Nonempty (structureSheafCohomology (iZ ≫ projToSpecCoeff k 2) 0 ≃ₗ[k] k) ∧
      ¬ IsCurve K (iW ≫ projToSpecCoeff K 2) ∧
      ¬ GeometricallyIntegral (iZ ≫ projToSpecCoeff k 2) :=
  ⟨isCurve_conic hk iZ hdim hI, genus_conic_eq_zero iZ hno hdim hI,
    ⟨conicGlobalSectionsEquiv iZ hno hdim hI⟩, not_isCurve_conic i hi iW hdimW hIW,
    not_geometricallyIntegral_conic hk K i hi iZ hI⟩

end Stacks.Curves.DegenerateConic

end
