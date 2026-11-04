module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import StacksFrontier.Examples.Flatness.OrdinaryCone.EllipticCocycle

/-!
# The function field of the ordinary elliptic curve and an Artin–Schreier obstruction

Let `k` be a field and `E` the plane cubic `z³ + (y² + xy) z + x³ = 0`, whose homogeneous
coordinate ring is the cone `G = Stacks.Examples.OrdinaryCone.Cone k`. Its function field `k(E)` is
the field of degree-zero fractions `α / β` of `G`, with `α` and `β` homogeneous of the same degree.
In the affine coordinates `w = y / x` and `v = z / x` it is the cubic extension
`k(w)[v] / (v³ + (w² + w) v + 1)` of the rational function field `k(w)`.

In characteristic two, `(z / x)² = v²` is not of the form `h² + h` with `h ∈ k(E)`. Writing
`h = a + b v + c v²` over `k(w)` and comparing coefficients gives `b = c²` and
`c⁴ + (w² + w) c² + c + 1 = 0`; by the rational root theorem `c` is a polynomial in `w`, a divisor
of `1`, hence a constant, and the coefficient of `w²` then forces `c = 0`, which is absurd.

## Main definitions

* `Stacks.Examples.OrdinaryCone.affineCubic`: the cubic `v³ + (w² + w) v + 1` over `k(w)`.
* `Stacks.Examples.OrdinaryCone.CurveField`: the field `k(w)[v] / (v³ + (w² + w) v + 1)`.
* `Stacks.Examples.OrdinaryCone.Cone.functionField`: the subfield of degree-zero fractions of the
  fraction field of the cone.

## Main results

* `Stacks.Examples.OrdinaryCone.irreducible_affineCubic`: the cubic is irreducible over `k(w)`.
* `Stacks.Examples.OrdinaryCone.CurveField.sq_add_self_ne_v_sq`: in characteristic two,
  `h² + h ≠ v²` for every `h ∈ k(w)[v] / (v³ + (w² + w) v + 1)`.
* `Stacks.Examples.OrdinaryCone.Cone.sq_add_self_ne_sq_z_div_x`: in characteristic two,
  `h² + h ≠ (z / x)²` for every degree-zero fraction `h` of the cone.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open Polynomial

variable (k : Type*) [Field k]

/-- The cubic `v³ + (w² + w) v + 1` over the rational function field `k(w)`: the equation of the
elliptic curve in the affine chart `x ≠ 0`, with `w = y / x` and `v = z / x`. -/
noncomputable def affineCubic : (RatFunc k)[X] :=
  X ^ 3 + C (RatFunc.X ^ 2 + RatFunc.X) * X + 1

/-- The cubic `v³ + (w² + w) v + 1` has natural degree `3`. -/
theorem natDegree_affineCubic : (affineCubic k).natDegree = 3 := by
  unfold affineCubic
  compute_degree!

/-- The cubic `v³ + (w² + w) v + 1` has degree `3`. -/
theorem degree_affineCubic : (affineCubic k).degree = 3 := by
  unfold affineCubic
  compute_degree!

/-- A polynomial over a field dividing `±1` is a nonzero constant. -/
private theorem exists_eq_C_of_mul_eq {P Q : k[X]} {c : k} (hc : c ≠ 0) (h : P * Q = C c) :
    ∃ u : k, u ≠ 0 ∧ P = C u := by
  have hunit : IsUnit P := isUnit_of_dvd_unit ⟨Q, h.symm⟩ (isUnit_C.2 hc.isUnit)
  obtain ⟨u, hu, rfl⟩ := Polynomial.isUnit_iff.1 hunit
  exact ⟨u, hu.ne_zero, rfl⟩

/-- A root in `k(w)` of a monic polynomial over `k[w]` is the image of a root in `k[w]`. -/
private theorem exists_eq_algebraMap_of_aeval {p : k[X][X]} (hp : p.Monic) {r : RatFunc k}
    (hr : aeval r p = 0) : ∃ P : k[X], algebraMap k[X] (RatFunc k) P = r ∧ p.eval P = 0 := by
  obtain ⟨P, rfl⟩ := isInteger_of_is_root_of_monic hp hr
  refine ⟨P, rfl, RatFunc.algebraMap_injective k ?_⟩
  rw [map_zero, ← hr, aeval_algebraMap_apply, coe_aeval_eq_eval]

/-- If `C b + C a * (X² + X) = 0` over `k`, then `a = 0`. -/
private theorem eq_zero_of_C_add_C_mul_X_sq_add_X {a b : k} (h : C b + C a * (X ^ 2 + X) = 0) :
    a = 0 := by
  simpa [mul_add, coeff_C] using congrArg (coeff · 2) h

/-- The cubic `v³ + (w² + w) v + 1` has no root in `k(w)`. -/
theorem affineCubic_eval_ne_zero (r : RatFunc k) :
    r ^ 3 + (RatFunc.X ^ 2 + RatFunc.X) * r + 1 ≠ 0 := by
  intro hr
  have hmonic : (X ^ 3 + C (X ^ 2 + X) * X + 1 : k[X][X]).Monic := by monicity!
  obtain ⟨P, rfl, hP⟩ := exists_eq_algebraMap_of_aeval k hmonic (r := r) (by
    simpa [RatFunc.algebraMap_X] using hr)
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one] at hP
  obtain ⟨u, hu, rfl⟩ := exists_eq_C_of_mul_eq k (neg_ne_zero.2 one_ne_zero)
    (P := P) (Q := P ^ 2 + X ^ 2 + X) (by rw [C_neg, C_1]; linear_combination hP)
  refine hu (eq_zero_of_C_add_C_mul_X_sq_add_X k (b := u ^ 3 + 1) ?_)
  rw [← hP, map_add, map_pow, map_one]
  ring

/-- The cubic `v³ + (w² + w) v + 1` is irreducible over `k(w)`. -/
theorem irreducible_affineCubic : Irreducible (affineCubic k) := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [natDegree_affineCubic]; norm_num) (by rw [natDegree_affineCubic])]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  have hne : affineCubic k ≠ 0 := by
    intro h
    simpa [h] using natDegree_affineCubic k
  have := (mem_roots hne).1 hr
  simp only [affineCubic, IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one] at this
  exact affineCubic_eval_ne_zero k r this

/-- The irreducibility of `v³ + (w² + w) v + 1` over `k(w)`, as a `Fact`. -/
instance fact_irreducible_affineCubic : Fact (Irreducible (affineCubic k)) :=
  ⟨irreducible_affineCubic k⟩

/-- The function field `k(w)[v] / (v³ + (w² + w) v + 1)` of the elliptic curve, in the affine
coordinates `w = y / x` and `v = z / x`. -/
abbrev CurveField : Type _ := AdjoinRoot (affineCubic k)

namespace CurveField

/-- The coordinate `w = y / x` of the function field. -/
noncomputable def w : CurveField k := algebraMap (RatFunc k) (CurveField k) RatFunc.X

/-- The coordinate `v = z / x` of the function field. -/
noncomputable def v : CurveField k := AdjoinRoot.root (affineCubic k)

/-- The coordinates of the function field satisfy `v³ + (w² + w) v + 1 = 0`. -/
theorem v_cube : v k ^ 3 + (w k ^ 2 + w k) * v k + 1 = 0 := by
  have h : AdjoinRoot.mk (affineCubic k) (affineCubic k) = 0 := AdjoinRoot.mk_self
  calc _ = AdjoinRoot.mk (affineCubic k)
        (X ^ 3 + C (RatFunc.X ^ 2 + RatFunc.X) * X + 1) := by
        simp [v, w, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    _ = 0 := h

/-- **`v²` is not an Artin–Schreier value.** In characteristic two, `h² + h ≠ v²` for every
element `h` of the function field `k(w)[v] / (v³ + (w² + w) v + 1)`. -/
theorem sq_add_self_ne_v_sq [CharP k 2] (h : CurveField k) : h ^ 2 + h ≠ v k ^ 2 := by
  intro hh
  have h2 : (2 : CurveField k) = 0 := by
    have : CharP (CurveField k) 2 :=
      charP_of_injective_algebraMap (algebraMap k (CurveField k)).injective 2
    exact CharTwo.two_eq_zero
  -- Write `h = a + b v + c v²` with `a, b, c ∈ k(w)`.
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective h
  set r := q %ₘ affineCubic k with hr
  have hmonic : (affineCubic k).Monic := by unfold affineCubic; monicity!
  have hqr : AdjoinRoot.mk (affineCubic k) q = AdjoinRoot.mk (affineCubic k) r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨q /ₘ affineCubic k, by linear_combination -(modByMonic_add_div q (affineCubic k))⟩
  have hrdeg : r.degree < 3 := by
    rw [← degree_affineCubic k]
    exact degree_modByMonic_lt q hmonic
  have hr3 : r = C (r.coeff 2) * X ^ 2 + C (r.coeff 1) * X + C (r.coeff 0) := by
    ext n
    rcases n with _ | _ | _ | n
    · simp
    · simp
    · simp
    · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hrdeg (by exact_mod_cast (by omega)))]
      simp
  set a := r.coeff 0
  set b := r.coeff 1
  set c := r.coeff 2
  rw [hqr, hr3] at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X] at hh
  -- Comparing coefficients in the basis `1, v, v²`.
  set W : RatFunc k := RatFunc.X
  set V := AdjoinRoot.root (affineCubic k)
  have hv : V ^ 3 + (AdjoinRoot.of (affineCubic k) W ^ 2 + AdjoinRoot.of (affineCubic k) W) * V +
      1 = 0 := v_cube k
  rw [show v k = V from rfl] at hh
  set A₂ := b ^ 2 - c ^ 2 * (W ^ 2 + W) + c - 1 with hA₂def
  set A₁ := b - c ^ 2 with hA₁def
  set A₀ := a ^ 2 + a with hA₀def
  have hzero : AdjoinRoot.mk (affineCubic k) (C A₂ * X ^ 2 + C A₁ * X + C A₀) = 0 := by
    simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, hA₂def, hA₁def,
      hA₀def, map_sub, map_one]
    linear_combination hh - (AdjoinRoot.of _ c ^ 2 * V) * hv -
      (AdjoinRoot.of _ b * AdjoinRoot.of _ c * V ^ 3 + AdjoinRoot.of _ a * AdjoinRoot.of _ b *
        V + AdjoinRoot.of _ a * AdjoinRoot.of _ c * V ^ 2) * h2
  rw [AdjoinRoot.mk_eq_zero] at hzero
  have hpoly := eq_zero_of_dvd_of_degree_lt hzero
    (lt_of_le_of_lt degree_quadratic_le (by rw [degree_affineCubic]; norm_num))
  have hA₂ := congrArg (coeff · 2) hpoly
  have hA₁ := congrArg (coeff · 1) hpoly
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at hA₂ hA₁
  norm_num at hA₂ hA₁
  -- Hence `c⁴ - (w² + w) c² + c - 1 = 0`, and `c` is a polynomial in `w`.
  have hc : c ^ 4 - (W ^ 2 + W) * c ^ 2 + c - 1 = 0 := by
    rw [hA₁def, sub_eq_zero] at hA₁
    rw [← hA₂, hA₂def, hA₁]
    ring
  have hmonic4 : (X ^ 4 - C (X ^ 2 + X) * X ^ 2 + X - 1 : k[X][X]).Monic := by monicity!
  obtain ⟨P, -, hP'⟩ := exists_eq_algebraMap_of_aeval k hmonic4 (r := c) (by
    simpa [RatFunc.algebraMap_X, W] using hc)
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one] at hP'
  obtain ⟨u, hu, rfl⟩ := exists_eq_C_of_mul_eq k one_ne_zero
    (P := P) (Q := P ^ 3 - (X ^ 2 + X) * P + 1) (by rw [C_1]; linear_combination hP')
  refine hu (pow_eq_zero_iff two_ne_zero |>.1 (neg_eq_zero.1
    (eq_zero_of_C_add_C_mul_X_sq_add_X k (b := u ^ 4 + u - 1) ?_)))
  rw [← hP']
  simp only [map_add, map_sub, map_neg, map_pow, map_one]
  ring

end CurveField

namespace Cone

local notation "Ω" => FractionRing (Cone k)

local notation "⟪" g "⟫" => algebraMap (Cone k) (FractionRing (Cone k)) g

/-- The dehomogenization of the cone at `x`: the `k`-algebra map to the function field sending
`x`, `y` and `z` to `1`, `w` and `v`. -/
noncomputable def dehomogenize : Cone k →ₐ[k] CurveField k :=
  lift k 1 (CurveField.w k) (CurveField.v k) (by linear_combination CurveField.v_cube k)

/-- The dehomogenization sends `x` to `1`. -/
@[simp]
theorem dehomogenize_x : dehomogenize k (x k) = 1 := lift_x _ _ _ _

/-- The dehomogenization sends `y` to `w`. -/
@[simp]
theorem dehomogenize_y : dehomogenize k (y k) = CurveField.w k := lift_y _ _ _ _

/-- The dehomogenization sends `z` to `v`. -/
@[simp]
theorem dehomogenize_z : dehomogenize k (z k) = CurveField.v k := lift_z _ _ _ _

/-- The polynomial map `k[w] → Ω` sending `w` to `y / x`. -/
noncomputable def evalYDivX : k[X] →+* Ω :=
  eval₂RingHom (algebraMap k Ω) (⟪y k⟫ / ⟪x k⟫)

/-- `y / x` is transcendental over `k`: a nonzero polynomial does not vanish at it. -/
theorem evalYDivX_ne_zero {p : k[X]} (hp : p ≠ 0) : evalYDivX k p ≠ 0 := by
  intro h0
  have hx := algebraMap_x_ne_zero k
  set n := p.natDegree
  set H : Cone k := ∑ i ∈ Finset.range (n + 1),
    algebraMap k (Cone k) (p.coeff i) * y k ^ i * x k ^ (n - i) with hH
  have hHΩ : ⟪H⟫ = ⟪x k⟫ ^ n * evalYDivX k p := by
    rw [evalYDivX, coe_eval₂RingHom, eval₂_eq_sum_range, Finset.mul_sum, hH, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_mul, map_mul, map_pow, map_pow, ← IsScalarTower.algebraMap_apply, div_pow,
      show ⟪x k⟫ ^ n = ⟪x k⟫ ^ (n - i) * ⟪x k⟫ ^ i by rw [← pow_add, Nat.sub_add_cancel hin]]
    field_simp
  have hH0 : H = 0 := IsFractionRing.injective (Cone k) Ω (by rw [hHΩ, h0, mul_zero, map_zero])
  have hΨ : dehomogenize k H = algebraMap (RatFunc k) (CurveField k)
      (algebraMap k[X] (RatFunc k) p) := by
    conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
    simp only [hH, map_sum, map_mul, map_pow, AlgHom.commutes, dehomogenize_x, dehomogenize_y,
      one_pow, mul_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X, CurveField.w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IsScalarTower.algebraMap_apply k (RatFunc k) (CurveField k), RatFunc.algebraMap_eq_C]
  rw [hH0, map_zero] at hΨ
  exact hp (RatFunc.algebraMap_injective k
    ((algebraMap (RatFunc k) (CurveField k)).injective (by rw [← hΨ, map_zero, map_zero])))

/-- The embedding of the rational functions in `w` into the fraction field of the cone, sending
`w` to `y / x`. -/
noncomputable def ratFuncToFractionRing : RatFunc k →+* Ω :=
  RatFunc.liftRingHom (evalYDivX k) fun _p hp =>
    mem_nonZeroDivisors_of_ne_zero (evalYDivX_ne_zero k (nonZeroDivisors.ne_zero hp))

/-- On a polynomial `p` in `w`, the embedding `ratFuncToFractionRing` is the evaluation
`p(y / x)`. -/
theorem ratFuncToFractionRing_algebraMap (p : k[X]) :
    ratFuncToFractionRing k (algebraMap k[X] (RatFunc k) p) = evalYDivX k p := by
  have h := RatFunc.liftRingHom_apply_div (evalYDivX k) (fun p hp =>
    mem_nonZeroDivisors_of_ne_zero (evalYDivX_ne_zero k (nonZeroDivisors.ne_zero hp))) p 1
  rw [map_one, div_one, map_one, div_one] at h
  exact h

/-- The embedding of the function field `k(w)[v] / (v³ + (w² + w) v + 1)` into the fraction field
of the cone, sending `w` to `y / x` and `v` to `z / x`. -/
noncomputable def CurveField.toFractionRing : CurveField k →+* Ω :=
  AdjoinRoot.lift (ratFuncToFractionRing k) (⟪z k⟫ / ⟪x k⟫) <| by
    have hx := algebraMap_x_ne_zero k
    have h := congrArg (algebraMap (Cone k) Ω) (equation_eq_zero k)
    simp only [map_add, map_mul, map_pow, map_zero] at h
    have hW : ratFuncToFractionRing k RatFunc.X = ⟪y k⟫ / ⟪x k⟫ := by
      rw [← RatFunc.algebraMap_X, ratFuncToFractionRing_algebraMap]
      simp [evalYDivX]
    simp only [affineCubic, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, eval₂_one,
      map_add, map_pow, hW]
    field_simp
    linear_combination h

/-- The embedding of the function field sends `w` to `y / x`. -/
theorem CurveField.toFractionRing_w : CurveField.toFractionRing k (CurveField.w k) =
    ⟪y k⟫ / ⟪x k⟫ := by
  rw [CurveField.toFractionRing, CurveField.w, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
    ← RatFunc.algebraMap_X, ratFuncToFractionRing_algebraMap]
  simp [evalYDivX]

/-- The embedding of the function field sends `v` to `z / x`. -/
theorem CurveField.toFractionRing_v : CurveField.toFractionRing k (CurveField.v k) =
    ⟪z k⟫ / ⟪x k⟫ :=
  AdjoinRoot.lift_root _

/-- The embedding of the function field is the identity on the constants `k`. -/
theorem CurveField.toFractionRing_algebraMap (c : k) :
    CurveField.toFractionRing k (algebraMap k (CurveField k) c) = algebraMap k Ω c := by
  rw [IsScalarTower.algebraMap_apply k (RatFunc k) (CurveField k), CurveField.toFractionRing,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
    IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
    ratFuncToFractionRing_algebraMap]
  simp [evalYDivX]

/-- On the degree `d` part of the cone, the dehomogenization followed by the embedding of the
function field is `g ↦ g / xᵈ`. -/
theorem toFractionRing_dehomogenize {d : ℕ} {g : Cone k} (hg : g ∈ component k d) :
    CurveField.toFractionRing k (dehomogenize k g) = ⟪g⟫ / ⟪x k⟫ ^ d := by
  have hx := algebraMap_x_ne_zero k
  refine component_induction (P := fun g =>
      CurveField.toFractionRing k (dehomogenize k g) = ⟪g⟫ / ⟪x k⟫ ^ d)
    (by simp) (fun g h hg hh => by simp only [map_add, hg, hh, add_div]) (fun r g hg => ?_)
    (fun a b c habc => ?_) hg
  · rw [Algebra.smul_def, map_mul, map_mul, AlgHom.commutes, hg, map_mul,
      CurveField.toFractionRing_algebraMap, ← IsScalarTower.algebraMap_apply, mul_div_assoc]
  · simp only [map_mul, map_pow, dehomogenize_x, dehomogenize_y, dehomogenize_z, one_pow,
      one_mul, CurveField.toFractionRing_w, CurveField.toFractionRing_v]
    rw [eq_div_iff (pow_ne_zero _ hx), ← habc, div_pow, div_pow, pow_add, pow_add]
    field_simp

/-- The function field of the elliptic curve: the degree-zero fractions `α / β` of the cone, with
`α` and `β` homogeneous of the same degree, as a subfield of the fraction field of the cone. -/
noncomputable def functionField : Subfield Ω where
  carrier := {h | ∃ d, ∃ α ∈ component k d, ∃ β ∈ component k d, h = ⟪α⟫ / ⟪β⟫}
  zero_mem' := ⟨0, 0, zero_mem (component k 0), 1, one_mem_component_zero (k := k), by simp⟩
  one_mem' := ⟨0, 1, one_mem_component_zero (k := k), 1, one_mem_component_zero (k := k),
    by simp⟩
  add_mem' := by
    rintro _ _ ⟨d, α, hα, β, hβ, rfl⟩ ⟨d', α', hα', β', hβ', rfl⟩
    by_cases hb : β = 0
    · exact ⟨d', α', hα', β', hβ', by simp [hb]⟩
    by_cases hb' : β' = 0
    · exact ⟨d, α, hα, β, hβ, by simp [hb']⟩
    have h0 := (map_ne_zero_iff _ (IsFractionRing.injective (Cone k) Ω)).2 hb
    have h0' := (map_ne_zero_iff _ (IsFractionRing.injective (Cone k) Ω)).2 hb'
    refine ⟨d + d', α * β' + β * α', add_mem (mul_mem_component hα hβ')
      (mul_mem_component hβ hα'), β * β', mul_mem_component hβ hβ', ?_⟩
    rw [div_add_div _ _ h0 h0', map_add, map_mul, map_mul, map_mul]
  neg_mem' := by
    rintro _ ⟨d, α, hα, β, hβ, rfl⟩
    exact ⟨d, -α, neg_mem hα, β, hβ, by rw [map_neg, neg_div]⟩
  mul_mem' := by
    rintro _ _ ⟨d, α, hα, β, hβ, rfl⟩ ⟨d', α', hα', β', hβ', rfl⟩
    exact ⟨d + d', α * α', mul_mem_component hα hα', β * β', mul_mem_component hβ hβ', by
      rw [map_mul, map_mul, div_mul_div_comm]⟩
  inv_mem' := by
    rintro _ ⟨d, α, hα, β, hβ, rfl⟩
    exact ⟨d, β, hβ, α, hα, by rw [inv_div]⟩

/-- A quotient of two homogeneous elements of the same degree is a function on the curve. -/
theorem div_mem_functionField {d : ℕ} {α β : Cone k} (hα : α ∈ component k d)
    (hβ : β ∈ component k d) : ⟪α⟫ / ⟪β⟫ ∈ functionField k :=
  ⟨d, α, hα, β, hβ, rfl⟩

/-- Every function on the curve comes from the function field
`k(w)[v] / (v³ + (w² + w) v + 1)`. -/
theorem exists_toFractionRing_eq {h : Ω} (hh : h ∈ functionField k) :
    ∃ h' : CurveField k, CurveField.toFractionRing k h' = h := by
  obtain ⟨d, α, hα, β, hβ, rfl⟩ := hh
  have hxd := pow_ne_zero d (algebraMap_x_ne_zero k)
  refine ⟨dehomogenize k α / dehomogenize k β, ?_⟩
  rw [map_div₀, toFractionRing_dehomogenize k hα, toFractionRing_dehomogenize k hβ,
    div_div_div_cancel_right₀ hxd]

/-- **`(z / x)²` is not an Artin–Schreier value on the curve.** In characteristic two,
`h² + h ≠ (z / x)²` for every function `h` on the elliptic curve, that is, for every quotient
`h = α / β` of homogeneous elements of the same degree of the cone. -/
theorem sq_add_self_ne_sq_z_div_x [CharP k 2] {h : Ω} (hh : h ∈ functionField k) :
    h ^ 2 + h ≠ (⟪z k⟫ / ⟪x k⟫) ^ 2 := by
  obtain ⟨h', rfl⟩ := exists_toFractionRing_eq k hh
  rw [← CurveField.toFractionRing_v, ← map_pow, ← map_pow, ← map_add]
  exact fun e => CurveField.sq_add_self_ne_v_sq k h' ((CurveField.toFractionRing k).injective e)

end Cone

end Stacks.Examples.OrdinaryCone
