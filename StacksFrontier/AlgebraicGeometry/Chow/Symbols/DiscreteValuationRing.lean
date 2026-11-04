module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Self
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.TameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
public import StacksCore.Tactic.StacksAttribute

/-!
# The symbol of a discrete valuation ring is the usual tame symbol

Let `A` be a discrete valuation ring with fraction field `K`. For nonzero `x, y ∈ K` the symbol
of `A` is

`d_A(x, y) = (-1) ^ (ord_A x * ord_A y) * x ^ (ord_A y) / y ^ (ord_A x)   mod 𝔪_A`,

the classical tame symbol. The two exponents are integers, possibly negative, so the quotient
on the right is a power product in `K`; part of the assertion is that this power product is the
image of a unit of `A`, and the equality then takes place in the residue field.

## Main results

* `AlgebraicGeometry.exists_unit_algebraMap_eq_zpow_div_zpow` says that the power product
  `x ^ (ord_A y) / y ^ (ord_A x)` is the image of a unit of `A`.
* `AlgebraicGeometry.tameSymbol_eq_negOnePow_mul_residue` computes the symbol as the residue of
  any such unit, corrected by the sign `(-1) ^ (ord_A x * ord_A y)`.

## References

* [Stacks Project, Tag 02Q6](https://stacks.math.columbia.edu/tag/02Q6)
-/

@[expose] public section

noncomputable section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-! ### The order of vanishing of a unit times a power of a uniformizer -/

/-- The integer order of vanishing of `x` is the exponent appearing in the value of
`Ring.ordFrac` at `x`. -/
private theorem ordInt_eq_of_ordFrac_eq_exp
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Nontrivial A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (x : K) (hx : x ≠ 0) (n : ℤ)
    (h : Ring.ordFrac A (K := K) x = WithZero.exp n) :
    ordInt A x hx = n := by
  have hu : WithZero.unzero ((hx.isUnit.map (Ring.ordFrac A)).ne_zero) =
      Multiplicative.ofAdd n := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, h, WithZero.exp_eq_coe_ofAdd]
  simp [ordInt, hu]

/-- A nonzero fraction written as a unit of `A` times an integral power of a uniformizer has
order of vanishing equal to that power. -/
private theorem ordInt_eq_of_eq_unit_smul_zpow
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {π : A} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) {n : ℤ} {u : Aˣ}
    (h : x = u • (algebraMap A K π) ^ n) :
    ordInt A x hx = n := by
  refine ordInt_eq_of_ordFrac_eq_exp (A := A) x hx n ?_
  subst h
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
    Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible (K := K) hπ, one_mul,
    ← WithZero.exp_zsmul]
  simp

/-- With `x = u π ^ m` and `y = v π ^ n`, the power product `x ^ n / y ^ m` is the image of the
unit `u ^ n / v ^ m` of `A`. -/
private theorem algebraMap_unit_zpow_div_zpow
    {A : Type u} [CommRing A] [IsDomain A] {K : Type v} [Field K] [Algebra A K]
    [IsFractionRing A K] {π : A} (hπ : π ≠ 0) (u v : Aˣ) (m n : ℤ) {x y : K}
    (hx : x = u • (algebraMap A K π) ^ m) (hy : y = v • (algebraMap A K π) ^ n) :
    algebraMap A K ((u ^ n / v ^ m : Aˣ) : A) = x ^ n / y ^ m := by
  have hπK : algebraMap A K π ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ)
  subst hx hy
  simp only [Units.smul_def, Algebra.smul_def]
  let f : Aˣ →* Kˣ := Units.map (algebraMap A K).toMonoidHom
  have hf (a : Aˣ) : (f a : K) = algebraMap A K (a : A) := by simp [f, Units.coe_map]
  calc
    algebraMap A K ((u ^ n / v ^ m : Aˣ) : A) = (f (u ^ n / v ^ m) : K) := (hf _).symm
    _ = (f u : K) ^ n / (f v : K) ^ m := by
      simp only [map_div, map_zpow, Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val]
    _ = (algebraMap A K (u : A)) ^ n / (algebraMap A K (v : A)) ^ m := by rw [hf, hf]
    _ = _ := by
      rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm m n]
      field_simp [hπK]

/-! ### The values of the symbol on units and on a uniformizer -/

/-- A nonzerodivisor of `A`, viewed as a unit of the fraction field `K`. -/
private def fractionOfRegular
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (a : A) (ha : IsRegular a) : Kˣ :=
  (IsLocalization.map_units K ⟨a, isRegular_iff_mem_nonZeroDivisors.mp ha⟩).unit

/-- The unit `fractionOfRegular a ha` of `K` is the image of `a` in `K`. -/
private theorem fractionOfRegular_val
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (a : A) (ha : IsRegular a) :
    (fractionOfRegular (K := K) a ha : K) = algebraMap A K a :=
  IsUnit.unit_spec _

/-- A unit of `A`, viewed as a unit of the residue field. -/
private def residueUnit {A : Type u} [CommRing A] [IsLocalRing A] (u : Aˣ) :
    (IsLocalRing.ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom u

/-- The length of `A / bA` is the order of vanishing of `b`. -/
private theorem moduleLength_quotient_range_lsmul
    {A : Type u} [CommRing A] [IsLocalRing A] (b : A) :
    moduleLength A (A ⧸ (LinearMap.lsmul A A b).range) = (Ring.ord A b).toNat := by
  have hrange : (LinearMap.lsmul A A b).range = Ideal.span {b} := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, smul_eq_mul,
      Ideal.mem_span_singleton', mul_comm b]
  rw [hrange]
  rfl

/-- The symbol of a unit `u` of `A` against a nonzerodivisor `b` is the residue of `u` raised to
the order of vanishing of `b`. -/
private theorem moduleSymbol_unit_left_residueUnit
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (u : Aˣ) (b : A) (hb : IsSMulRegular A b) :
    moduleSymbol (M := A) (u : A) b (Units.isSMulRegular A u) hb
        (by simpa only [Module.supportDim_self_eq_ringKrullDim] using hdim) =
      residueUnit u ^ (Ring.ord A b).toNat := by
  apply Units.ext
  simpa [residueUnit, Units.coe_map] using moduleSymbol_unit_left_ring u b hb hdim

/-- The order of vanishing of a uniformizer is `1`. -/
private theorem ord_eq_one_of_irreducible
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π) : Ring.ord A π = 1 := by
  simp [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_uniformizer hπ]

/-- A uniformizer is a nonzerodivisor. -/
private theorem isSMulRegular_of_irreducible
    {A : Type u} [CommRing A] [IsDomain A] {π : A} (hπ : Irreducible π) :
    IsSMulRegular A π :=
  (IsRegular.of_ne_zero hπ.ne_zero).isSMulRegular

/-- The symbol of a uniformizer against a unit of `A` is the inverse of the residue of the
unit. -/
private theorem moduleSymbol_irreducible_unit
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A]
    (hdim : ringKrullDim A = 1) {π : A} (hπ : Irreducible π) (u : Aˣ) :
    moduleSymbol (M := A) π (u : A) (isSMulRegular_of_irreducible hπ)
        (Units.isSMulRegular A u)
        (by simpa only [Module.supportDim_self_eq_ringKrullDim] using hdim) =
      (residueUnit u)⁻¹ := by
  have hswap := moduleSymbol_mul_swap (A := A) (M := A) π (u : A)
    (isSMulRegular_of_irreducible hπ) (Units.isSMulRegular A u)
    (by simpa only [Module.supportDim_self_eq_ringKrullDim] using hdim)
  have hunit := moduleSymbol_unit_left_residueUnit hdim u π (isSMulRegular_of_irreducible hπ)
  refine (mul_eq_one_iff_eq_inv.mp hswap).trans ?_
  rw [hunit, ord_eq_one_of_irreducible hπ]
  simp

/-- The symbol of a uniformizer with itself is `-1`. -/
private theorem moduleSymbol_irreducible_self
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A]
    (hdim : ringKrullDim A = 1) {π : A} (hπ : Irreducible π) :
    moduleSymbol (M := A) π π (isSMulRegular_of_irreducible hπ)
        (isSMulRegular_of_irreducible hπ)
        (by simpa only [Module.supportDim_self_eq_ringKrullDim] using hdim) = -1 := by
  rw [moduleSymbol_self_eq_negOne_pow_length (M := A) π (isSMulRegular_of_irreducible hπ),
    moduleLength_quotient_range_lsmul π, ord_eq_one_of_irreducible hπ]
  simp

/-! ### Powers in the two arguments of the tame symbol -/

/-- The tame symbol in its first argument, as a homomorphism of groups. -/
private def tameSymbolLeftHom
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {hdim : ringKrullDim A = 1} (T : TameSymbol (K := K) hdim) (y : Kˣ) :
    Kˣ →* (IsLocalRing.ResidueField A)ˣ where
  toFun x := T x y
  map_one' := by
    apply mul_left_cancel (a := T 1 y)
    simpa using (T.map_mul_left 1 1 y).symm
  map_mul' x x' := T.map_mul_left x x' y

/-- The tame symbol in its second argument, as a homomorphism of groups. -/
private def tameSymbolRightHom
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {hdim : ringKrullDim A = 1} (T : TameSymbol (K := K) hdim) (x : Kˣ) :
    Kˣ →* (IsLocalRing.ResidueField A)ˣ where
  toFun y := T x y
  map_one' := by
    apply mul_left_cancel (a := T x 1)
    simpa using (T.map_mul_right x 1 1).symm
  map_mul' y y' := T.map_mul_right x y y'

/-- The tame symbol takes an integral power in its first argument to that power of itself. -/
private theorem tameSymbol_zpow_left
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {hdim : ringKrullDim A = 1} (T : TameSymbol (K := K) hdim) (x y : Kˣ) (n : ℤ) :
    T (x ^ n) y = T x y ^ n :=
  map_zpow (tameSymbolLeftHom T y) x n

/-- The tame symbol takes an integral power in its second argument to that power of itself. -/
private theorem tameSymbol_zpow_right
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {hdim : ringKrullDim A = 1} (T : TameSymbol (K := K) hdim) (x y : Kˣ) (n : ℤ) :
    T x (y ^ n) = T x y ^ n :=
  map_zpow (tameSymbolRightHom T x) y n

/-- A unit of the fraction field written as a unit of `A` times an integral power of a
uniformizer, as a product of units coming from `A`. -/
private theorem eq_fractionOfRegular_mul_zpow
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {π : A} (hπ : π ≠ 0) (m : ℤ) (u : Aˣ) (x : Kˣ)
    (hx : (x : K) = u • (algebraMap A K π) ^ m) :
    x = fractionOfRegular (K := K) (u : A) u.isUnit.isRegular *
      fractionOfRegular (K := K) π (IsRegular.of_ne_zero hπ) ^ m := by
  apply Units.ext
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, fractionOfRegular_val,
    Units.smul_def, Algebra.smul_def] using hx

/-! ### The tame symbol formula -/

/-- For a discrete valuation ring `A` with fraction field `K` and nonzero `x, y ∈ K`, the power
product `x ^ (ord_A y) / y ^ (ord_A x)` is the image of a unit of `A`. -/
@[stacks 02Q6 "the power product is a unit of the valuation ring"]
theorem exists_unit_algebraMap_eq_zpow_div_zpow
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] (x y : Kˣ) :
    ∃ w : Aˣ, algebraMap A K (w : A) =
      (x : K) ^ (ordInt A (y : K) y.ne_zero) / (y : K) ^ (ordInt A (x : K) x.ne_zero) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨m, u, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (x := (x : K)) x.ne_zero
  obtain ⟨n, v, hy⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (x := (y : K)) y.ne_zero
  refine ⟨u ^ n / v ^ m, ?_⟩
  rw [ordInt_eq_of_eq_unit_smul_zpow hπ x.ne_zero hx,
    ordInt_eq_of_eq_unit_smul_zpow hπ y.ne_zero hy]
  exact algebraMap_unit_zpow_div_zpow hπ.ne_zero u v m n hx hy

/-- For a discrete valuation ring `A` with fraction field `K` and nonzero `x, y ∈ K`, the symbol
`d_A(x, y)` is the usual tame symbol: if `w` is a unit of `A` representing
`x ^ (ord_A y) / y ^ (ord_A x)`, then `d_A(x, y)` is the residue of `w` times
`(-1) ^ (ord_A x * ord_A y)`. -/
@[stacks 02Q6 "the tame symbol formula"]
theorem tameSymbol_eq_negOnePow_mul_residue
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] (x y : Kˣ) (w : Aˣ)
    (hw : algebraMap A K (w : A) =
      (x : K) ^ (ordInt A (y : K) y.ne_zero) / (y : K) ^ (ordInt A (x : K) x.ne_zero)) :
    ((tameSymbol (K := K) (IsDiscreteValuationRing.ringKrullDim_eq_one A) x y :
          (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
      (((-1 : (IsLocalRing.ResidueField A)ˣ) ^
            (ordInt A (x : K) x.ne_zero * ordInt A (y : K) y.ne_zero) :
          (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) *
        IsLocalRing.residue A (w : A) := by
  set hdim := IsDiscreteValuationRing.ringKrullDim_eq_one A
  set T := tameSymbol (K := K) hdim with hTdef
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨m, u, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (x := (x : K)) x.ne_zero
  obtain ⟨n, v, hy⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (x := (y : K)) y.ne_zero
  have hxord : ordInt A (x : K) x.ne_zero = m := ordInt_eq_of_eq_unit_smul_zpow hπ x.ne_zero hx
  have hyord : ordInt A (y : K) y.ne_zero = n := ordInt_eq_of_eq_unit_smul_zpow hπ y.ne_zero hy
  have hπreg : IsRegular π := IsRegular.of_ne_zero hπ.ne_zero
  set uf := fractionOfRegular (A := A) (K := K) (u : A) u.isUnit.isRegular with hufdef
  set vf := fractionOfRegular (A := A) (K := K) (v : A) v.isUnit.isRegular with hvfdef
  set pf := fractionOfRegular (A := A) (K := K) π hπreg with hpfdef
  have hxunit : x = uf * pf ^ m := eq_fractionOfRegular_mul_zpow hπ.ne_zero m u x hx
  have hyunit : y = vf * pf ^ n := eq_fractionOfRegular_mul_zpow hπ.ne_zero n v y hy
  have hunitUnit : T uf vf = 1 := by
    rw [hTdef, hufdef, hvfdef, fractionOfRegular, fractionOfRegular,
      (tameSymbol (K := K) hdim).eq_moduleSymbol (u : A) (v : A) u.isUnit.isRegular
        v.isUnit.isRegular,
      show v.isUnit.isRegular.isSMulRegular = Units.isSMulRegular A v from rfl,
      moduleSymbol_unit_left_residueUnit hdim u (v : A) (Units.isSMulRegular A v),
      Ring.ord_of_isUnit v.isUnit]
    simp
  have hunitPi : T uf pf = residueUnit u := by
    rw [hTdef, hufdef, hpfdef, fractionOfRegular, fractionOfRegular,
      (tameSymbol (K := K) hdim).eq_moduleSymbol (u : A) π u.isUnit.isRegular hπreg,
      show hπreg.isSMulRegular = isSMulRegular_of_irreducible hπ from rfl,
      moduleSymbol_unit_left_residueUnit hdim u π (isSMulRegular_of_irreducible hπ),
      ord_eq_one_of_irreducible hπ]
    simp
  have hpiUnit : T pf vf = (residueUnit v)⁻¹ := by
    rw [hTdef, hpfdef, hvfdef, fractionOfRegular, fractionOfRegular,
      (tameSymbol (K := K) hdim).eq_moduleSymbol π (v : A) hπreg v.isUnit.isRegular,
      show hπreg.isSMulRegular = isSMulRegular_of_irreducible hπ from rfl,
      show v.isUnit.isRegular.isSMulRegular = Units.isSMulRegular A v from rfl]
    exact moduleSymbol_irreducible_unit hdim hπ v
  have hpiPi : T pf pf = -1 := by
    rw [hTdef, hpfdef, fractionOfRegular,
      (tameSymbol (K := K) hdim).eq_moduleSymbol π π hπreg hπreg,
      show hπreg.isSMulRegular = isSMulRegular_of_irreducible hπ from rfl]
    exact moduleSymbol_irreducible_self hdim hπ
  have hcalc : T x y =
      (T uf vf * (T uf pf) ^ n) * ((T pf vf) ^ m * (T pf pf) ^ (m * n)) := by
    rw [hxunit, hyunit]
    calc
      T (uf * pf ^ m) (vf * pf ^ n) =
          T uf (vf * pf ^ n) * T (pf ^ m) (vf * pf ^ n) :=
        T.map_mul_left uf (pf ^ m) (vf * pf ^ n)
      _ = (T uf vf * T uf (pf ^ n)) * (T (pf ^ m) vf * T (pf ^ m) (pf ^ n)) := by
        rw [T.map_mul_right, T.map_mul_right]
      _ = (T uf vf * (T uf pf) ^ n) * ((T pf vf) ^ m * (T pf pf) ^ (m * n)) := by
        rw [tameSymbol_zpow_right, tameSymbol_zpow_left, tameSymbol_zpow_right,
          tameSymbol_zpow_left, ← zpow_mul]
  have hquot := algebraMap_unit_zpow_div_zpow hπ.ne_zero u v m n hx hy
  have hweq : w = u ^ n / v ^ m := by
    apply Units.ext
    refine IsFractionRing.injective A K ?_
    rw [hw, hxord, hyord, hquot]
  rw [hxord, hyord, hcalc, hunitUnit, hunitPi, hpiUnit, hpiPi, hweq]
  have hres : residueUnit (u ^ n / v ^ m) = residueUnit u ^ n / residueUnit v ^ m := by
    simp [residueUnit]
  have hgroup :
      (1 * residueUnit u ^ n *
          ((residueUnit v)⁻¹ ^ m * (-1 : (IsLocalRing.ResidueField A)ˣ) ^ (m * n))) =
        (-1 : (IsLocalRing.ResidueField A)ˣ) ^ (m * n) * residueUnit (u ^ n / v ^ m) := by
    rw [hres, inv_zpow', div_eq_mul_inv, ← zpow_neg]
    ac_rfl
  rw [show IsLocalRing.residue A ((u ^ n / v ^ m : Aˣ) : A) = residueUnit (u ^ n / v ^ m) from rfl]
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using congrArg Units.val hgroup

end AlgebraicGeometry
