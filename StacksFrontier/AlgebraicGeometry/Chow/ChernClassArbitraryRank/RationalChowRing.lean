module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation

/-!
# The ring `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`

Let `X` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`A^i(X)` be its Chow cohomology groups (Stacks 0B7E, at the Gysin system of the first Chern class
of an invertible module). The product `∏_{i ≥ 0} (A^i(X) ⊗ 𝐐)` is
`Stacks.Chow.fullRationalChowCohomology`. This file makes it a ring under the Cauchy product

  `(a b)_n = ∑_{i + j = n} a_i b_j`

of the products `A^i(X) × A^j(X) ⟶ A^{i+j}(X)` of Stacks 0B75, extended to rational
coefficients, with unit `1 ∈ A^0(X)`. It is the ring in which the Chern character of
Stacks 0ESX lives and which receives the ring map of Stacks 0FEM.

## How the ring structure is obtained

`A^*(X) = ∏_{q ≥ 0} A^q(X)` is already a ring, `Stacks.Chow.TotalChowClass`, and so is
`A^*(X) ⊗ 𝐐`, `Stacks.Chow.rationalTotalChowClass`. A family `a = (a_i)` with `a_i ∈ A^i(X) ⊗ 𝐐`
is sent to the formal power series over `A^*(X) ⊗ 𝐐` whose coefficient of index `i` is `a_i`,
placed in degree `i` (`Stacks.Chow.toRationalPowerSeries`). The power series reached this way are
those whose coefficient of index `i` is concentrated in degree `i`; a product of a class
concentrated in degree `i` and one concentrated in degree `j` is concentrated in degree `i + j`
(`Stacks.Chow.TotalChowClass.IsHomogeneous.mul`), so these power series form a subring, and the
Cauchy product of power series restricts to the Cauchy product above. The product of `a` and `b`
is read back from the product of their power series by taking the degree-`i` component of the
coefficient of index `i` (`Stacks.Chow.ofRationalPowerSeries`). The ring axioms are those of
power series, and `Stacks.Chow.toRationalPowerSeriesRingHom` is an injective ring homomorphism.

## Main definitions

* `Stacks.Chow.TotalChowClass.single` — the total class concentrated in one degree.
* `Stacks.Chow.instRingFullRationalChowCohomology` — the ring `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`.
* `Stacks.Chow.toRationalPowerSeriesRingHom` — its embedding into power series over
  `A^*(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.TotalChowClass.IsHomogeneous.mul` — degrees add under the product.
* `Stacks.Chow.fullRationalChowCohomology_mul_apply` — the Cauchy product formula.
* `Stacks.Chow.toRationalPowerSeries_injective`.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Stacks.Chow

/-! ### Total classes concentrated in one degree -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The total class concentrated in degree `p`, with component `a ∈ A^p(X)` there. -/
def single (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) →+ TotalChowClass C sX :=
  AddMonoidHom.single (fun q : ℕ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) p

/-- The degree-`p` component of the class concentrated in degree `p` with component `a`. -/
@[simp]
theorem single_apply_same (p : ℕ)
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ)) :
    single p a p = a :=
  Pi.single_eq_same (M := fun q : ℕ ↦
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) p a

/-- The components of a class concentrated in degree `p` vanish away from `p`. -/
theorem single_apply_of_ne {p q : ℕ} (h : q ≠ p)
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ)) :
    single p a q = 0 :=
  Pi.single_eq_of_ne (M := fun q : ℕ ↦
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) h a

/-- A class concentrated in degree `p` is homogeneous of degree `p`. -/
theorem isHomogeneous_single (p : ℕ)
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ)) :
    (single p a).IsHomogeneous p :=
  fun _ hq ↦ single_apply_of_ne hq a

/-- A class homogeneous of degree `p` is the class concentrated in degree `p` with its own
degree-`p` component. -/
theorem IsHomogeneous.single_apply_eq {p : ℕ} {c : TotalChowClass C sX} (hc : c.IsHomogeneous p) :
    single p (c p) = c := by
  refine ext fun q ↦ ?_
  rcases eq_or_ne q p with rfl | hq
  · exact single_apply_same q (c q)
  · rw [single_apply_of_ne hq, hc q hq]

/-- The homogeneous components of a homogeneous class vanish away from its degree. -/
theorem IsHomogeneous.homComponent_of_ne {p q : ℕ} {c : TotalChowClass C sX}
    (hc : c.IsHomogeneous p) (h : q ≠ p) : homComponent q c = 0 := by
  refine ext fun m ↦ ?_
  rw [homComponent_apply, zero_apply]
  split_ifs with hm
  · subst hm
    exact hc m h
  · rfl

/-- **Degrees add under the product**: a class homogeneous of degree `i` times a class
homogeneous of degree `j` is homogeneous of degree `i + j`. -/
theorem IsHomogeneous.mul {i j : ℕ} {c d : TotalChowClass C sX} (hc : c.IsHomogeneous i)
    (hd : d.IsHomogeneous j) : (c * d).IsHomogeneous (i + j) := by
  intro m hm
  have h : homComponent m (c * d) m =
      (∑ k ∈ Finset.range (m + 1), homComponent (m - k) c * homComponent k d) m := by
    rw [homComponent_mul]
  rw [homComponent_apply, if_pos rfl] at h
  rw [h, sum_apply]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rcases eq_or_ne k j with rfl | hkj
  · rw [hc.homComponent_of_ne (show m - k ≠ i by omega), zero_mul, zero_apply]
  · rw [hd.homComponent_of_ne hkj, mul_zero, zero_apply]

/-- The unit total class is homogeneous of degree `0`. -/
theorem isHomogeneous_one : (1 : TotalChowClass C sX).IsHomogeneous 0 :=
  fun _ hp ↦ one_apply_of_ne hp

end TotalChowClass

/-! ### Rational coefficients -/

section Rational

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The rational class concentrated in degree `p`: `TotalChowClass.single` with rational
coefficients. -/
def rationalSingle (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) →ₗ[ℤ]
      rationalTotalChowClass C sX :=
  LinearMap.lTensor ℚ (TotalChowClass.single (sX := sX) p).toIntLinearMap

/-- The degree-`p` component of a rational total class. -/
def rationalComponent (p : ℕ) :
    rationalTotalChowClass C sX →ₗ[ℤ]
      rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  LinearMap.lTensor ℚ
    (Pi.evalAddMonoidHom (fun q : ℕ ↦
      chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) p).toIntLinearMap

variable {C sX}

/-- The rational class concentrated in degree `p` of `q ⊗ a` is `q` tensored with the integral
class concentrated in degree `p` of `a`. -/
@[simp]
theorem rationalSingle_tmul (p : ℕ) (q : ℚ)
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ)) :
    rationalSingle C sX p (q ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] TotalChowClass.single p a :=
  rfl

/-- The degree-`p` component of `q ⊗ c` is `q` tensored with the degree-`p` component of `c`. -/
@[simp]
theorem rationalComponent_tmul (p : ℕ) (q : ℚ) (c : TotalChowClass C sX) :
    rationalComponent C sX p (q ⊗ₜ[ℤ] c) = q ⊗ₜ[ℤ] c p :=
  rfl

/-- The degree-`p` component of the rational class concentrated in degree `p`. -/
@[simp]
theorem rationalComponent_rationalSingle (p : ℕ)
    (x : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ)) :
    rationalComponent C sX p (rationalSingle C sX p x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q a => simp
  | add x y hx hy => simp [hx, hy]

/-- A rational total class is *concentrated in degree `n`* if it is the class concentrated in
degree `n` with its own degree-`n` component. -/
def IsRationalHomogeneous (n : ℕ) (z : rationalTotalChowClass C sX) : Prop :=
  rationalSingle C sX n (rationalComponent C sX n z) = z

/-- The zero class is concentrated in every degree. -/
theorem isRationalHomogeneous_zero (n : ℕ) :
    IsRationalHomogeneous n (0 : rationalTotalChowClass C sX) := by
  simp [IsRationalHomogeneous]

/-- A sum of two classes concentrated in degree `n` is concentrated in degree `n`. -/
theorem IsRationalHomogeneous.add {n : ℕ} {z w : rationalTotalChowClass C sX}
    (hz : IsRationalHomogeneous n z) (hw : IsRationalHomogeneous n w) :
    IsRationalHomogeneous n (z + w) := by
  rw [IsRationalHomogeneous, map_add, map_add, hz, hw]

/-- A finite sum of classes concentrated in degree `n` is concentrated in degree `n`. -/
theorem isRationalHomogeneous_sum {ι : Type*} (s : Finset ι) {n : ℕ}
    (z : ι → rationalTotalChowClass C sX) (h : ∀ i ∈ s, IsRationalHomogeneous n (z i)) :
    IsRationalHomogeneous n (∑ i ∈ s, z i) := by
  rw [IsRationalHomogeneous, map_sum, map_sum]
  exact Finset.sum_congr rfl h

/-- A rational multiple of a homogeneous integral class is concentrated in its degree. -/
theorem isRationalHomogeneous_tmul {n : ℕ} (q : ℚ) {c : TotalChowClass C sX}
    (hc : c.IsHomogeneous n) : IsRationalHomogeneous n (q ⊗ₜ[ℤ] c) := by
  rw [IsRationalHomogeneous, rationalComponent_tmul, rationalSingle_tmul, hc.single_apply_eq]

/-- The rational class concentrated in degree `n` is concentrated in degree `n`. -/
theorem isRationalHomogeneous_rationalSingle (n : ℕ)
    (x : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (n : ℤ)) :
    IsRationalHomogeneous n (rationalSingle C sX n x) := by
  rw [IsRationalHomogeneous, rationalComponent_rationalSingle]

/-- **Degrees add under the product, with rational coefficients.** -/
theorem isRationalHomogeneous_rationalSingle_mul {i j n : ℕ} (h : i + j = n)
    (x : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (i : ℤ))
    (y : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (j : ℤ)) :
    IsRationalHomogeneous n (rationalSingle C sX i x * rationalSingle C sX j y) := by
  subst h
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_mul]; exact isRationalHomogeneous_zero _
  | add x x' hx hx' => rw [map_add, add_mul]; exact hx.add hx'
  | tmul q a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero]; exact isRationalHomogeneous_zero _
    | add y y' hy hy' => rw [map_add, mul_add]; exact hy.add hy'
    | tmul q' b =>
      rw [rationalSingle_tmul, rationalSingle_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      exact isRationalHomogeneous_tmul _
        ((TotalChowClass.isHomogeneous_single i a).mul (TotalChowClass.isHomogeneous_single j b))

/-! ### The embedding into power series -/

variable (C sX)

/-- A family `(a_i)` of rational classes `a_i ∈ A^i(X) ⊗ 𝐐`, as the power series over
`A^*(X) ⊗ 𝐐` whose coefficient of index `i` is `a_i` placed in degree `i`. -/
def toRationalPowerSeries :
    fullRationalChowCohomology C (gysinSystemOfInvertible C) sX →+
      PowerSeries (rationalTotalChowClass C sX) where
  toFun a := PowerSeries.mk fun i ↦ rationalSingle C sX i (a i)
  map_zero' := by
    ext i
    simp
  map_add' a b := by
    ext i
    simp

/-- A power series over `A^*(X) ⊗ 𝐐`, read back as the family of the degree-`i` components of its
coefficients of index `i`. -/
def ofRationalPowerSeries :
    PowerSeries (rationalTotalChowClass C sX) →+
      fullRationalChowCohomology C (gysinSystemOfInvertible C) sX where
  toFun f i := rationalComponent C sX i (PowerSeries.coeff i f)
  map_zero' := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp

variable {C sX}

/-- The coefficient of index `i` of the power series of a family `(a_i)` is `a_i` placed in degree
`i`. -/
@[simp]
theorem coeff_toRationalPowerSeries
    (a : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX)
    (i : ℕ) :
    PowerSeries.coeff i (toRationalPowerSeries C sX a) = rationalSingle C sX i (a i) := by
  show PowerSeries.coeff i (PowerSeries.mk fun i ↦ rationalSingle C sX i (a i)) = _
  exact PowerSeries.coeff_mk i _

/-- The `i`-th entry of the family read back from `f` is the degree-`i` component of the
coefficient of index `i` of `f`. -/
@[simp]
theorem ofRationalPowerSeries_apply (f : PowerSeries (rationalTotalChowClass C sX)) (i : ℕ) :
    ofRationalPowerSeries C sX f i = rationalComponent C sX i (PowerSeries.coeff i f) :=
  rfl

/-- Reading back the power series of a family gives the family. -/
@[simp]
theorem ofRationalPowerSeries_toRationalPowerSeries
    (a : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX) :
    ofRationalPowerSeries C sX (toRationalPowerSeries C sX a) = a := by
  funext i
  simp

/-- The embedding into power series is injective. -/
theorem toRationalPowerSeries_injective :
    Function.Injective (toRationalPowerSeries C sX) := fun a b h ↦ by
  rw [← ofRationalPowerSeries_toRationalPowerSeries a, h,
    ofRationalPowerSeries_toRationalPowerSeries]

/-- A power series whose coefficient of index `i` is concentrated in degree `i` is the power series
of the family it reads back as. -/
theorem toRationalPowerSeries_ofRationalPowerSeries {f : PowerSeries (rationalTotalChowClass C sX)}
    (hf : ∀ i, IsRationalHomogeneous i (PowerSeries.coeff i f)) :
    toRationalPowerSeries C sX (ofRationalPowerSeries C sX f) = f := by
  ext i
  rw [coeff_toRationalPowerSeries, ofRationalPowerSeries_apply]
  exact hf i

/-- The coefficients of a product of power series of families are concentrated in the right
degrees. -/
theorem isRationalHomogeneous_coeff_mul
    (a b : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX) (n : ℕ) :
    IsRationalHomogeneous n
      (PowerSeries.coeff n (toRationalPowerSeries C sX a * toRationalPowerSeries C sX b)) := by
  rw [PowerSeries.coeff_mul]
  refine isRationalHomogeneous_sum _ _ fun q hq ↦ ?_
  rw [coeff_toRationalPowerSeries, coeff_toRationalPowerSeries]
  exact isRationalHomogeneous_rationalSingle_mul (Finset.HasAntidiagonal.mem_antidiagonal.mp hq) _ _

/-- The coefficients of the unit power series are concentrated in the right degrees. -/
theorem isRationalHomogeneous_coeff_one (n : ℕ) :
    IsRationalHomogeneous n
      (PowerSeries.coeff n (1 : PowerSeries (rationalTotalChowClass C sX))) := by
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h
    exact isRationalHomogeneous_tmul 1 TotalChowClass.isHomogeneous_one
  · exact isRationalHomogeneous_zero n

/-! ### The ring -/

/-- **The ring `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`**, under the Cauchy product
`(a b)_n = ∑_{i + j = n} a_i b_j` of the products `A^i(X) × A^j(X) ⟶ A^{i+j}(X)` of Stacks 0B75
with rational coefficients, and with unit `1 ∈ A^0(X)`. The ring axioms are those of the power
series over `A^*(X) ⊗ 𝐐` that the families embed into. -/
instance instRingFullRationalChowCohomology :
    Ring (fullRationalChowCohomology C (gysinSystemOfInvertible C) sX) where
  __ := (inferInstance : AddCommGroup (fullRationalChowCohomology C (gysinSystemOfInvertible C) sX))
  mul a b :=
    ofRationalPowerSeries C sX (toRationalPowerSeries C sX a * toRationalPowerSeries C sX b)
  one := ofRationalPowerSeries C sX 1
  mul_assoc a b c := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX
        (ofRationalPowerSeries C sX (toRationalPowerSeries C sX a * toRationalPowerSeries C sX b)) *
        toRationalPowerSeries C sX c) =
      ofRationalPowerSeries C sX (toRationalPowerSeries C sX a * toRationalPowerSeries C sX
        (ofRationalPowerSeries C sX (toRationalPowerSeries C sX b * toRationalPowerSeries C sX c)))
    rw [toRationalPowerSeries_ofRationalPowerSeries (isRationalHomogeneous_coeff_mul a b),
      toRationalPowerSeries_ofRationalPowerSeries (isRationalHomogeneous_coeff_mul b c), mul_assoc]
  one_mul a := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX (ofRationalPowerSeries C sX 1) *
      toRationalPowerSeries C sX a) = a
    rw [toRationalPowerSeries_ofRationalPowerSeries isRationalHomogeneous_coeff_one, one_mul,
      ofRationalPowerSeries_toRationalPowerSeries]
  mul_one a := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX a *
      toRationalPowerSeries C sX (ofRationalPowerSeries C sX 1)) = a
    rw [toRationalPowerSeries_ofRationalPowerSeries isRationalHomogeneous_coeff_one, mul_one,
      ofRationalPowerSeries_toRationalPowerSeries]
  zero_mul a := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX 0 *
      toRationalPowerSeries C sX a) = 0
    rw [map_zero, zero_mul, map_zero]
  mul_zero a := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX a *
      toRationalPowerSeries C sX 0) = 0
    rw [map_zero, mul_zero, map_zero]
  left_distrib a b c := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX a *
      toRationalPowerSeries C sX (b + c)) = ofRationalPowerSeries C sX
        (toRationalPowerSeries C sX a * toRationalPowerSeries C sX b) +
      ofRationalPowerSeries C sX (toRationalPowerSeries C sX a * toRationalPowerSeries C sX c)
    rw [map_add, mul_add, map_add]
  right_distrib a b c := by
    change ofRationalPowerSeries C sX (toRationalPowerSeries C sX (a + b) *
      toRationalPowerSeries C sX c) = ofRationalPowerSeries C sX
        (toRationalPowerSeries C sX a * toRationalPowerSeries C sX c) +
      ofRationalPowerSeries C sX (toRationalPowerSeries C sX b * toRationalPowerSeries C sX c)
    rw [map_add, add_mul, map_add]

/-- The product of `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` read through power series. -/
theorem toRationalPowerSeries_mul
    (a b : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX) :
    toRationalPowerSeries C sX (a * b) =
      toRationalPowerSeries C sX a * toRationalPowerSeries C sX b :=
  toRationalPowerSeries_ofRationalPowerSeries (isRationalHomogeneous_coeff_mul a b)

/-- The unit of `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` read through power series. -/
theorem toRationalPowerSeries_one :
    toRationalPowerSeries C sX (1 : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX) =
      1 :=
  toRationalPowerSeries_ofRationalPowerSeries isRationalHomogeneous_coeff_one

variable (C sX)

/-- **The embedding of `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` into power series over `A^*(X) ⊗ 𝐐`**, as an
injective ring homomorphism. -/
def toRationalPowerSeriesRingHom :
    fullRationalChowCohomology C (gysinSystemOfInvertible C) sX →+*
      PowerSeries (rationalTotalChowClass C sX) where
  toFun := toRationalPowerSeries C sX
  map_one' := toRationalPowerSeries_one
  map_mul' := toRationalPowerSeries_mul
  map_zero' := map_zero _
  map_add' := map_add _

variable {C sX}

/-- **The Cauchy product formula**: the degree-`n` component of a product is
`∑_{i + j = n} a_i b_j`, each product formed in `A^*(X) ⊗ 𝐐` and read in degree `n`. -/
theorem fullRationalChowCohomology_mul_apply
    (a b : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX) (n : ℕ) :
    (a * b) n = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      rationalComponent C sX n
        (rationalSingle C sX q.1 (a q.1) * rationalSingle C sX q.2 (b q.2)) := by
  show rationalComponent C sX n (PowerSeries.coeff n
    (toRationalPowerSeries C sX a * toRationalPowerSeries C sX b)) = _
  rw [PowerSeries.coeff_mul, map_sum]
  simp only [coeff_toRationalPowerSeries]

end Rational

end Stacks.Chow

end
