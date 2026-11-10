module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Freeness of the divided power algebra of a free module over a torsion-free base

Let `R` be a commutative ring and `M` a free `R`-module with basis `b`. The divided power
monomials `∏ i, bᵢ^[k i]`, indexed by the exponent vectors `k : ι →₀ ℕ`, span
`DividedPowerAlgebra R M`; this is `DividedPowerAlgebra.submodule_span_prod_dp_eq_top`. This
file proves that they are moreover linearly independent, hence a basis, under the hypothesis
that `R` admits an injective algebra map into a `ℚ`-algebra — equivalently, that `R` is
torsion-free as an additive group.

The argument is a comparison with an ordinary polynomial algebra. Over a `ℚ`-algebra `K` every
ideal carries a divided power structure, namely `x^[n] = xⁿ / n!`, by
`DividedPowers.RatAlgebra.dividedPowers`. Applying the universal property of the divided power
algebra to the unit ideal of `MvPolynomial ι K` and to the linear map sending `bᵢ` to the
variable `Xᵢ` produces an `R`-algebra map `DividedPowerAlgebra R M → MvPolynomial ι K` carrying
the divided power monomial indexed by `k` to the ordinary monomial `X^k` scaled by the unit
`∏ i, ((k i)!)⁻¹`. Distinct monomials of a polynomial algebra are linearly independent and
rescaling by units preserves that, so the divided power monomials are independent over `K`, and
hence over `R` because `R → K` is injective.

The torsion-free hypothesis cannot be dropped from this argument, and the comparison map is the
only input it needs: no divided power structure on the augmentation ideal of
`DividedPowerAlgebra R M` is used or produced here.

## Main definitions

* `DividedPowerAlgebra.dpMonomial` — the divided power monomial `∏ i, bᵢ^[k i]`.
* `DividedPowerAlgebra.toRatMvPolynomial` — the comparison map to a polynomial algebra over a
  `ℚ`-algebra.
* `DividedPowerAlgebra.basisDPMonomial` — the resulting basis of divided power monomials.
* `DividedPowerAlgebra.basisDPMonomialFinsupp` — the same basis for the free module `ι →₀ R`.

## Main results

* `DividedPowerAlgebra.toRatMvPolynomial_dpMonomial` — the comparison map sends a divided power
  monomial to a unit multiple of the corresponding ordinary monomial.
* `DividedPowerAlgebra.linearIndependent_dpMonomial` — the divided power monomials are linearly
  independent.

## References

* [Stacks Project, Tag 07H5](https://stacks.math.columbia.edu/tag/07H5)
-/

@[expose] public section

namespace DividedPowerAlgebra

open MvPolynomial

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {ι : Type w}
  {K : Type*} [CommRing K] [Algebra ℚ K] [Algebra R K]

/-- The divided power monomial `∏ i, (v i)^[k i]` attached to a family `v` of elements of `M`
and an exponent vector `k`. -/
public noncomputable def dpMonomial (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] {ι : Type w} (v : ι → M) (k : ι →₀ ℕ) : DividedPowerAlgebra R M :=
  k.prod fun i m ↦ dp R m (v i)

/-- The divided power monomials attached to a spanning family span the divided power algebra.
This is `DividedPowerAlgebra.submodule_span_prod_dp_eq_top` restated for `dpMonomial`. -/
public theorem span_range_dpMonomial_eq_top {v : ι → M}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (dpMonomial R v)) = ⊤ :=
  submodule_span_prod_dp_eq_top hv

open Classical in
/-- The comparison map from the divided power algebra of a free module to an ordinary polynomial
algebra over a `ℚ`-algebra `K`, sending the basis vector `b i` to the variable `X i`. It is
obtained from the universal property of the divided power algebra applied to the unit ideal of
`MvPolynomial ι K`, which carries the divided power structure `x^[n] = xⁿ / n!`. -/
public noncomputable def toRatMvPolynomial (b : Module.Basis ι R M) (K : Type*) [CommRing K]
    [Algebra ℚ K] [Algebra R K] : DividedPowerAlgebra R M →ₐ[R] MvPolynomial ι K :=
  lift (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (MvPolynomial ι K)))
    (b.constr R fun i ↦ (MvPolynomial.X i : MvPolynomial ι K)) fun _ ↦ Submodule.mem_top

/-- The comparison map sends the `n`th divided power of a basis vector to `Xᵢⁿ / n!`. -/
public theorem toRatMvPolynomial_dp_basis (b : Module.Basis ι R M) (n : ℕ) (i : ι) :
    toRatMvPolynomial b K (dp R n (b i))
      = MvPolynomial.C (Ring.inverse (n.factorial : K))
        * (MvPolynomial.X i : MvPolynomial ι K) ^ n := by
  classical
  have hC : ((n.factorial : ℕ) : MvPolynomial ι K)
      = MvPolynomial.C (n.factorial : K) := by simp
  rw [toRatMvPolynomial, lift_apply_dp, Module.Basis.constr_basis,
    DividedPowers.RatAlgebra.dpow_apply, ite_eq_left Submodule.mem_top,
    Ring.inverse_mul_eq_iff_eq_mul _ _ _
      (IsUnit.natCast_factorial_of_algebra (A := MvPolynomial ι K) ℚ n),
    ← mul_assoc, hC, ← map_mul,
    Ring.mul_inverse_cancel _ (IsUnit.natCast_factorial_of_algebra (A := K) ℚ n),
    map_one, one_mul]

/-- The unit `∏ i, ((k i)!)⁻¹` of a `ℚ`-algebra by which the comparison map rescales the
ordinary monomial indexed by `k`. -/
public noncomputable def dpMonomialCoeff (K : Type*) [CommRing K] [Algebra ℚ K] {ι : Type w}
    (k : ι →₀ ℕ) : K :=
  ∏ i ∈ k.support, Ring.inverse ((k i).factorial : K)

/-- The rescaling coefficient of a divided power monomial is a unit. -/
public theorem isUnit_dpMonomialCoeff (K : Type*) [CommRing K] [Algebra ℚ K] {ι : Type w}
    (k : ι →₀ ℕ) : IsUnit (dpMonomialCoeff K k) :=
  Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun i _ ↦ by
    rw [Ring.inverse_of_isUnit (IsUnit.natCast_factorial_of_algebra (A := K) ℚ (k i))]
    exact Units.isUnit _

/-- The comparison map sends the divided power monomial indexed by `k` to the ordinary monomial
indexed by `k` with the unit coefficient `∏ i, ((k i)!)⁻¹`. -/
public theorem toRatMvPolynomial_dpMonomial (b : Module.Basis ι R M) (k : ι →₀ ℕ) :
    toRatMvPolynomial b K (dpMonomial R b k)
      = MvPolynomial.monomial k (dpMonomialCoeff K k) := by
  classical
  rw [dpMonomial, Finsupp.prod, map_prod]
  calc ∏ i ∈ k.support, toRatMvPolynomial b K (dp R (k i) (b i))
      = ∏ i ∈ k.support, (MvPolynomial.C (Ring.inverse ((k i).factorial : K))
          * (MvPolynomial.X i : MvPolynomial ι K) ^ (k i)) :=
        Finset.prod_congr rfl fun i _ ↦ toRatMvPolynomial_dp_basis b _ _
    _ = (∏ i ∈ k.support, MvPolynomial.C (Ring.inverse ((k i).factorial : K)))
          * ∏ i ∈ k.support, (MvPolynomial.X i : MvPolynomial ι K) ^ (k i) :=
        Finset.prod_mul_distrib
    _ = MvPolynomial.C (dpMonomialCoeff K k) * MvPolynomial.monomial k (1 : K) := by
        rw [← map_prod, MvPolynomial.prod_X_pow_eq_monomial, dpMonomialCoeff]
    _ = MvPolynomial.monomial k (dpMonomialCoeff K k) := by
        rw [MvPolynomial.C_mul_monomial, mul_one]

/-- The divided power monomials of a basis are linearly independent, provided the base ring
admits an injective algebra map to a `ℚ`-algebra. -/
public theorem linearIndependent_dpMonomial (b : Module.Basis ι R M) (K : Type*) [CommRing K]
    [Algebra ℚ K] [Algebra R K] (hinj : Function.Injective (algebraMap R K)) :
    LinearIndependent R (dpMonomial R b) := by
  classical
  have hfun : ((fun k : ι →₀ ℕ ↦ (isUnit_dpMonomialCoeff K k).unit) •
        (MvPolynomial.basisMonomials ι K : (ι →₀ ℕ) → MvPolynomial ι K))
      = fun k : ι →₀ ℕ ↦ (MvPolynomial.monomial k (dpMonomialCoeff K k) : MvPolynomial ι K) := by
    funext k
    change ((isUnit_dpMonomialCoeff K k).unit : K) • (MvPolynomial.basisMonomials ι K k) = _
    rw [IsUnit.unit_spec,
      show (MvPolynomial.basisMonomials ι K) k = MvPolynomial.monomial k (1 : K) from rfl,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hb : LinearIndependent K
      (fun k : ι →₀ ℕ ↦ (MvPolynomial.monomial k (dpMonomialCoeff K k) : MvPolynomial ι K)) :=
    hfun ▸ (MvPolynomial.basisMonomials ι K).linearIndependent.units_smul
      fun k : ι →₀ ℕ ↦ (isUnit_dpMonomialCoeff K k).unit
  have hinj' : Function.Injective fun r : R ↦ r • (1 : K) := by
    intro a c hac
    exact hinj (by simpa only [Algebra.smul_def, mul_one] using hac)
  have hR : LinearIndependent R
      (fun k : ι →₀ ℕ ↦ (MvPolynomial.monomial k (dpMonomialCoeff K k) : MvPolynomial ι K)) :=
    hb.restrict_scalars hinj'
  refine LinearIndependent.of_comp (toRatMvPolynomial b K).toLinearMap ?_
  have hcomp : ((toRatMvPolynomial b K).toLinearMap ∘ dpMonomial R b)
      = fun k : ι →₀ ℕ ↦ (MvPolynomial.monomial k (dpMonomialCoeff K k) : MvPolynomial ι K) :=
    funext fun k ↦ toRatMvPolynomial_dpMonomial b k
  exact hcomp ▸ hR

/-- The divided power monomials of a basis form a basis of the divided power algebra, provided
the base ring admits an injective algebra map to a `ℚ`-algebra. -/
public noncomputable def basisDPMonomial (b : Module.Basis ι R M) (K : Type*) [CommRing K]
    [Algebra ℚ K] [Algebra R K] (hinj : Function.Injective (algebraMap R K)) :
    Module.Basis (ι →₀ ℕ) R (DividedPowerAlgebra R M) :=
  Module.Basis.mk (linearIndependent_dpMonomial b K hinj)
    (le_of_eq (span_range_dpMonomial_eq_top b.span_eq).symm)

/-- The basis vector indexed by an exponent vector is the corresponding divided power
monomial. -/
@[simp]
public theorem basisDPMonomial_apply (b : Module.Basis ι R M) (K : Type*) [CommRing K]
    [Algebra ℚ K] [Algebra R K] (hinj : Function.Injective (algebraMap R K)) (k : ι →₀ ℕ) :
    basisDPMonomial b K hinj k = dpMonomial R b k :=
  Module.Basis.mk_apply _ _ _

/-- For the free module `ι →₀ R`, the divided power monomials `∏ i, xᵢ^[k i]` form a basis of
the divided power algebra, provided the base ring admits an injective algebra map to a
`ℚ`-algebra. -/
public noncomputable def basisDPMonomialFinsupp (R : Type u) [CommRing R] {ι : Type w}
    (K : Type*) [CommRing K] [Algebra ℚ K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) :
    Module.Basis (ι →₀ ℕ) R (DividedPowerAlgebra R (ι →₀ R)) :=
  basisDPMonomial Finsupp.basisSingleOne K hinj

/-- The basis vector indexed by an exponent vector `k` is `∏ i, xᵢ^[k i]`. -/
public theorem basisDPMonomialFinsupp_apply (R : Type u) [CommRing R] {ι : Type w}
    (K : Type*) [CommRing K] [Algebra ℚ K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (k : ι →₀ ℕ) :
    basisDPMonomialFinsupp R K hinj k = k.prod fun i m ↦ dp R m (Finsupp.single i (1 : R)) := by
  rw [basisDPMonomialFinsupp, basisDPMonomial_apply, dpMonomial, Finsupp.coe_basisSingleOne]

end DividedPowerAlgebra
