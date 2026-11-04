module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.UnitPart
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction

/-!
# The tame symbol of a discrete valuation ring

For a discrete valuation ring `A` with a uniformizer `ϖ`, every nonzerodivisor is `u ϖ ^ m` with
`u` a unit, and

`∂_A(u ϖ ^ m, v ϖ ^ n) = (-1) ^ (m n) ū ^ n v̄ ^ (-m)`

is a tame symbol `Stacks.Chow.RegularTameSymbol` on pairs of nonzerodivisors of `A`, which does
not depend on the choice of uniformizer. Its extension to the total ring of fractions is a tame
symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`.

## Main definitions

* `Stacks.Chow.dvrTameSymbolFormula`: `(-1) ^ (m n) U ^ n (V ^ m)⁻¹`, the formula above as a
  function of the two orders of vanishing and the two residues.
* `Stacks.Chow.dvrRegularTameSymbol`: the tame symbol of a discrete valuation ring on pairs of
  nonzerodivisors.
* `Stacks.Chow.dvrTameSymbol`: its extension to the units of the total ring of fractions.

## Main results

* `Stacks.Chow.dvrRegularTameSymbol_apply`: the defining formula.
* `Stacks.Chow.dvrRegularTameSymbol_irreducible_congr`: independence of the uniformizer.
* `Stacks.Chow.dvrTameSymbol_regularFractionUnit`: the extension restricts to the formula.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u v

namespace Stacks.Chow

/-! ### Signs -/

section Sign

variable {k : Type v} [CommRing k]

/-- The inverse of a power of `-1` is that power again. -/
theorem inv_neg_one_pow (m : ℕ) : ((-1 : kˣ) ^ m)⁻¹ = (-1) ^ m := by
  rw [← inv_pow]
  norm_num

/-- Two powers of `-1` agree when the sum of their exponents is even. -/
theorem neg_one_pow_eq_of_even_add {α β : ℕ} (h : Even (α + β)) :
    (-1 : kˣ) ^ α = (-1) ^ β :=
  inv_inv ((-1 : kˣ) ^ β) ▸ eq_inv_of_mul_eq_one_left
    (by rw [inv_neg_one_pow, ← pow_add, h.neg_one_pow])

end Sign

/-! ### The formula -/

section Formula

variable {k : Type v} [CommRing k]

/-- The tame-symbol formula of a discrete valuation ring, as a function of the orders of vanishing
`m`, `n` of two nonzerodivisors and the residues `U`, `V` of their unit parts:
`∂(u ϖ ^ m, v ϖ ^ n) = (-1) ^ (m n) ū ^ n v̄ ^ (-m)`. -/
def dvrTameSymbolFormula (m n : ℕ) (U V : kˣ) : kˣ := (-1) ^ (m * n) * U ^ n * (V ^ m)⁻¹

/-- The formula, regrouped so that the sign is a single factor. -/
theorem dvrTameSymbolFormula_eq (m n : ℕ) (U V : kˣ) :
    dvrTameSymbolFormula m n U V = (-1) ^ (m * n) * (U ^ n * (V ^ m)⁻¹) :=
  (mul_assoc _ _ _)

/-- The formula with its second residue negated. -/
theorem dvrTameSymbolFormula_neg_right (m n : ℕ) (U V : kˣ) :
    dvrTameSymbolFormula m n U (-V) = (-1) ^ (m * n + m) * (U ^ n * (V ^ m)⁻¹) := by
  rw [dvrTameSymbolFormula, neg_pow V m, mul_inv, inv_neg_one_pow, pow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

/-- A product of two sign-times-rest expressions, with the signs collected. -/
theorem neg_one_pow_mul_mul (α β : ℕ) (X Y : kˣ) :
    ((-1 : kˣ) ^ α * X) * ((-1) ^ β * Y) = (-1) ^ (α + β) * (X * Y) := by
  rw [pow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

/-- The formula is multiplicative in the first argument. -/
theorem dvrTameSymbolFormula_mul_left (m m' n : ℕ) (U U' V : kˣ) :
    dvrTameSymbolFormula (m + m') n (U * U') V =
      dvrTameSymbolFormula m n U V * dvrTameSymbolFormula m' n U' V := by
  simp only [dvrTameSymbolFormula, add_mul, pow_add, mul_pow, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- The formula is multiplicative in the second argument. -/
theorem dvrTameSymbolFormula_mul_right (m n n' : ℕ) (U V V' : kˣ) :
    dvrTameSymbolFormula m (n + n') U (V * V') =
      dvrTameSymbolFormula m n U V * dvrTameSymbolFormula m n' U V' := by
  simp only [dvrTameSymbolFormula, mul_add, pow_add, mul_pow, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- The formula on two equal arguments of order `n` is `(-1) ^ n`. -/
theorem dvrTameSymbolFormula_self (n : ℕ) (V : kˣ) :
    dvrTameSymbolFormula n n V V = (-1) ^ n := by
  rw [dvrTameSymbolFormula, mul_inv_cancel_right]
  refine neg_one_pow_eq_of_even_add ?_
  have h : n * n + n = n * (n + 1) := by ring
  rw [h]
  exact Nat.even_mul_succ_self n

/-- The formula with first order of vanishing zero is `U ^ n`. -/
theorem dvrTameSymbolFormula_zero_left (n : ℕ) (U V : kˣ) :
    dvrTameSymbolFormula 0 n U V = U ^ n := by
  simp [dvrTameSymbolFormula]

/-- The Steinberg identity for the formula when the difference `c = b - a` has order `m` and
residue `-U`. -/
theorem dvrTameSymbolFormula_steinberg_neg (m n : ℕ) (U V : kˣ) :
    dvrTameSymbolFormula m m U (-U) * dvrTameSymbolFormula n n V V =
      dvrTameSymbolFormula n m V (-U) * dvrTameSymbolFormula m n U V := by
  rw [dvrTameSymbolFormula_neg_right, dvrTameSymbolFormula_neg_right, dvrTameSymbolFormula_eq,
    dvrTameSymbolFormula_eq, neg_one_pow_mul_mul, neg_one_pow_mul_mul]
  have hX : (U ^ m * (U ^ m)⁻¹) * (V ^ n * (V ^ n)⁻¹) =
      (V ^ m * (U ^ n)⁻¹) * (U ^ n * (V ^ m)⁻¹) := by
    simp
  rw [hX]
  refine congrArg (· * _) (neg_one_pow_eq_of_even_add ?_)
  have h : m * m + m + n * n + (n * m + n + m * n) =
      m * (m + 1) + n * (n + 1) + 2 * (m * n) := by ring
  rw [h]
  exact ((Nat.even_mul_succ_self m).add (Nat.even_mul_succ_self n)).add (even_two_mul _)

/-- The Steinberg identity for the formula when the two arguments have the same order of
vanishing `m` and either the difference has order `p = m` or the residues agree. -/
theorem dvrTameSymbolFormula_steinberg_eq (m p : ℕ) (U V W : kˣ) (h : p = m ∨ U = V) :
    dvrTameSymbolFormula m p U W * dvrTameSymbolFormula m m V V =
      dvrTameSymbolFormula m p V W * dvrTameSymbolFormula m m U V := by
  rw [dvrTameSymbolFormula_eq, dvrTameSymbolFormula_eq, dvrTameSymbolFormula_eq,
    dvrTameSymbolFormula_eq, neg_one_pow_mul_mul, neg_one_pow_mul_mul]
  refine congrArg (_ * ·) ?_
  have key : Additive.ofMul (U ^ p) + Additive.ofMul (V ^ m) =
      Additive.ofMul (V ^ p) + Additive.ofMul (U ^ m) := by
    refine (ofMul_mul _ _).symm.trans (congrArg Additive.ofMul ?_) |>.trans (ofMul_mul _ _)
    rcases h with h | h
    · rw [h, mul_comm]
    · rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  linear_combination (norm := abel) key

/-- The formula is unchanged when the residues of orders `m` and `n` are multiplied by
`C ^ (-m)` and `C ^ (-n)` respectively. -/
theorem dvrTameSymbolFormula_mul_inv_pow (m n : ℕ) (U V C : kˣ) :
    dvrTameSymbolFormula m n (U * (C ^ m)⁻¹) (V * (C ^ n)⁻¹) = dvrTameSymbolFormula m n U V := by
  have h : ((C ^ n)⁻¹) ^ m = ((C ^ m)⁻¹) ^ n := by
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [dvrTameSymbolFormula, mul_pow, h, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Formula

/-! ### The tame symbol -/

section Dvr

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The residue of a unit is nonzero. -/
theorem residue_unit_ne_zero (u : Aˣ) : residue A (u : A) ≠ 0 :=
  (u.isUnit.map (residue A)).ne_zero

/-- If `c = t ϖ ^ n` with the residue of `t` that of a unit `x`, then `ord c = n` and the residue
of the unit part of `c` is `x`. -/
private theorem dvrOrd_and_residue_dvrUnitPart_of_eq_mul_pow {ϖ : A} (hϖ : Irreducible ϖ)
    {c : nonZeroDivisors A} {n : ℕ} {t : A} {x : (ResidueField A)ˣ}
    (hct : (c : A) = t * ϖ ^ n) (htres : residue A t = x) :
    dvrOrd c = n ∧ Units.map (residue A).toMonoidHom (dvrUnitPart hϖ c) = x := by
  have htunit : IsUnit t := isUnit_of_residue_ne_zero (by rw [htres]; exact x.ne_zero)
  have hct' : (c : A) = (htunit.unit : A) * ϖ ^ n := by rw [htunit.unit_spec]; exact hct
  refine ⟨dvrOrd_eq_of_eq_unit_mul_pow hϖ hct', ?_⟩
  rw [dvrUnitPart_eq_of_eq_unit_mul_pow hϖ hct']
  exact Units.ext (by simpa [htunit.unit_spec] using htres)

/-- If `ord a < ord b` and `c = b - a` then `ord c = ord a` and the residue of the unit part of
`c` is minus that of `a`. -/
theorem dvrOrd_and_residue_dvrUnitPart_sub_of_lt {ϖ : A} (hϖ : Irreducible ϖ)
    {a b c : nonZeroDivisors A} (hc : (c : A) = (b : A) - (a : A))
    (h : dvrOrd a < dvrOrd b) :
    dvrOrd c = dvrOrd a ∧
      Units.map (residue A).toMonoidHom (dvrUnitPart hϖ c) =
        -Units.map (residue A).toMonoidHom (dvrUnitPart hϖ a) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt h
  refine dvrOrd_and_residue_dvrUnitPart_of_eq_mul_pow hϖ
    (t := (dvrUnitPart hϖ b : A) * ϖ ^ (j + 1) - (dvrUnitPart hϖ a : A)) ?_ ?_
  · rw [hc, dvrUnitPart_spec hϖ a, dvrUnitPart_spec hϖ b, hj]
    ring
  · rw [map_sub, map_mul, map_pow, residue_eq_zero_of_irreducible hϖ]
    simp

/-- If `ord b < ord a` and `c = b - a` then `ord c = ord b` and the residue of the unit part of
`c` is that of `b`. -/
theorem dvrOrd_and_residue_dvrUnitPart_sub_of_gt {ϖ : A} (hϖ : Irreducible ϖ)
    {a b c : nonZeroDivisors A} (hc : (c : A) = (b : A) - (a : A))
    (h : dvrOrd b < dvrOrd a) :
    dvrOrd c = dvrOrd b ∧
      Units.map (residue A).toMonoidHom (dvrUnitPart hϖ c) =
        Units.map (residue A).toMonoidHom (dvrUnitPart hϖ b) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt h
  refine dvrOrd_and_residue_dvrUnitPart_of_eq_mul_pow hϖ
    (t := (dvrUnitPart hϖ b : A) - (dvrUnitPart hϖ a : A) * ϖ ^ (j + 1)) ?_ ?_
  · rw [hc, dvrUnitPart_spec hϖ a, dvrUnitPart_spec hϖ b, hj]
    ring
  · rw [map_sub, map_mul, map_pow, residue_eq_zero_of_irreducible hϖ]
    simp

/-- If `ord a = ord b` and `c = b - a` then either `ord c = ord a` or the residues of the unit
parts of `a` and `b` agree. -/
theorem dvrOrd_sub_or_residue_dvrUnitPart_eq {ϖ : A} (hϖ : Irreducible ϖ)
    {a b c : nonZeroDivisors A} (hc : (c : A) = (b : A) - (a : A))
    (h : dvrOrd a = dvrOrd b) :
    dvrOrd c = dvrOrd a ∨
      Units.map (residue A).toMonoidHom (dvrUnitPart hϖ a) =
        Units.map (residue A).toMonoidHom (dvrUnitPart hϖ b) := by
  set u := dvrUnitPart hϖ a with hu
  set v := dvrUnitPart hϖ b with hv
  set s : A := (v : A) - (u : A) with hs
  have hcs : (c : A) = s * ϖ ^ dvrOrd a := by
    rw [hs, hc, dvrUnitPart_spec hϖ a, dvrUnitPart_spec hϖ b, ← h, ← hu, ← hv]
    ring
  by_cases hsu : IsUnit s
  · exact Or.inl (dvrOrd_eq_of_eq_unit_mul_pow hϖ (by rw [hsu.unit_spec]; exact hcs))
  · refine Or.inr (Units.ext ?_)
    have hmem : s ∈ maximalIdeal A := by
      by_contra hmem
      exact hsu (notMem_maximalIdeal.mp hmem)
    have hzero : residue A s = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hs, map_sub, sub_eq_zero] at hzero
    simpa using hzero.symm

/-- The tame symbol of a discrete valuation ring on pairs of nonzerodivisors: fixing a
uniformizer `ϖ`, it is `∂_A(u ϖ ^ m, v ϖ ^ n) = (-1) ^ (m n) ū ^ n v̄ ^ (-m)`. -/
def dvrRegularTameSymbol {ϖ : A} (hϖ : Irreducible ϖ) : RegularTameSymbol A where
  toFun a b :=
    dvrTameSymbolFormula (dvrOrd a) (dvrOrd b)
      (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ a))
      (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ b))
  map_mul_left a a' b := by
    rw [dvrOrd_mul, dvrUnitPart_mul, map_mul, dvrTameSymbolFormula_mul_left]
  map_mul_right a b b' := by
    rw [dvrOrd_mul, dvrUnitPart_mul, map_mul, dvrTameSymbolFormula_mul_right]
  self b := dvrTameSymbolFormula_self _ _
  unit_left a b u hu := by
    rw [dvrOrd_eq_zero_of_coe_eq_unit hϖ hu, dvrUnitPart_of_coe_eq_unit hϖ hu,
      dvrTameSymbolFormula_zero_left]
    rfl
  steinberg a b c hc := by
    rcases lt_trichotomy (dvrOrd a) (dvrOrd b) with h | h | h
    · obtain ⟨hp, hw⟩ := dvrOrd_and_residue_dvrUnitPart_sub_of_lt hϖ hc h
      rw [hp, hw]
      exact dvrTameSymbolFormula_steinberg_neg _ _ _ _
    · obtain hp | hw := dvrOrd_sub_or_residue_dvrUnitPart_eq hϖ hc h
      · rw [← h, hp]
        exact dvrTameSymbolFormula_steinberg_eq _ _ _ _ _ (Or.inl rfl)
      · rw [← h]
        exact dvrTameSymbolFormula_steinberg_eq _ _ _ _ _ (Or.inr hw)
    · obtain ⟨hp, hw⟩ := dvrOrd_and_residue_dvrUnitPart_sub_of_gt hϖ hc h
      rw [hp, hw]
      exact mul_comm _ _

/-- `Stacks.Chow.dvrRegularTameSymbol` is given by `Stacks.Chow.dvrTameSymbolFormula` applied to
the orders of vanishing and the residues of the unit parts. -/
theorem dvrRegularTameSymbol_apply {ϖ : A} (hϖ : Irreducible ϖ) (a b : nonZeroDivisors A) :
    dvrRegularTameSymbol hϖ a b =
      dvrTameSymbolFormula (dvrOrd a) (dvrOrd b)
        (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ a))
        (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ b)) :=
  rfl

/-- The tame symbol of a discrete valuation ring does not depend on the uniformizer. -/
theorem dvrRegularTameSymbol_irreducible_congr {ϖ ϖ' : A} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (a b : nonZeroDivisors A) :
    dvrRegularTameSymbol hϖ a b = dvrRegularTameSymbol hϖ' a b := by
  obtain ⟨c, hc⟩ := associated_of_irreducible A hϖ hϖ'
  have hpow (m : ℕ) : ϖ' ^ m = ϖ ^ m * ((c ^ m : Aˣ) : A) := by
    rw [← hc, mul_pow, Units.val_pow_eq_pow_val]
  have hup (x : nonZeroDivisors A) :
      dvrUnitPart hϖ' x = dvrUnitPart hϖ x * (c ^ dvrOrd x)⁻¹ := by
    refine dvrUnitPart_eq_of_eq_unit_mul_pow hϖ' (n := dvrOrd x) ?_
    rw [hpow (dvrOrd x), Units.val_mul]
    calc (x : A) = (dvrUnitPart hϖ x : A) * ϖ ^ dvrOrd x := dvrUnitPart_spec hϖ x
      _ = (dvrUnitPart hϖ x : A) * ϖ ^ dvrOrd x *
            ((((c ^ dvrOrd x : Aˣ)⁻¹ : Aˣ) : A) * ((c ^ dvrOrd x : Aˣ) : A)) := by
          rw [Units.inv_mul, mul_one]
      _ = (dvrUnitPart hϖ x : A) * (((c ^ dvrOrd x : Aˣ)⁻¹ : Aˣ) : A) *
            (ϖ ^ dvrOrd x * ((c ^ dvrOrd x : Aˣ) : A)) := by ring
  rw [dvrRegularTameSymbol_apply, dvrRegularTameSymbol_apply, hup a, hup b, map_mul, map_mul,
    map_inv, map_inv, map_pow, map_pow]
  exact (dvrTameSymbolFormula_mul_inv_pow _ _ _ _ _).symm

/-- The tame symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of a discrete valuation ring, the
extension of `Stacks.Chow.dvrRegularTameSymbol` to the total ring of fractions. -/
def dvrTameSymbol {ϖ : A} (hϖ : Irreducible ϖ) (Q : Type v) [CommRing Q] [Algebra A Q]
    [IsFractionRing A Q] : TameSymbol A Q :=
  (dvrRegularTameSymbol hϖ).extend Q

/-- On the images of two nonzerodivisors, `Stacks.Chow.dvrTameSymbol` is given by
`Stacks.Chow.dvrTameSymbolFormula`. -/
@[simp]
theorem dvrTameSymbol_regularFractionUnit {ϖ : A} (hϖ : Irreducible ϖ) (Q : Type v) [CommRing Q]
    [Algebra A Q] [IsFractionRing A Q] (a b : nonZeroDivisors A) :
    dvrTameSymbol hϖ Q (regularFractionUnit a) (regularFractionUnit b) =
      dvrTameSymbolFormula (dvrOrd a) (dvrOrd b)
        (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ a))
        (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ b)) :=
  (dvrRegularTameSymbol hϖ).extend_regularFractionUnit Q a b

end Dvr

end Stacks.Chow

end
