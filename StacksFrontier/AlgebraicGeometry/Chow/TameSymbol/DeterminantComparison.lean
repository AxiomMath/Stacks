module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocityNonzero
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.DiscreteValuationRing

/-!
# The determinant symbol of a discrete valuation ring is its tame symbol

A one-dimensional Noetherian local ring carries two symbols on pairs of units of its total ring
of fractions. One, `AlgebraicGeometry.tameSymbol`, is built from the determinants of two-periodic
complexes; the other is the extension `Stacks.Chow.RegularTameSymbol.extend` of a datum
satisfying the four conditions Stacks 0EAL, 0EAM, 0EAN and 0EAP, which for a discrete valuation
ring is `Stacks.Chow.dvrRegularTameSymbol`.

At a discrete valuation ring the two agree. Both are computed by the classical formula

`∂_A(u ϖ ^ m, v ϖ ^ n) = (-1) ^ (m n) ū ^ n v̄ ^ (-m)`,

the first by `AlgebraicGeometry.tameSymbol_eq_negOnePow_mul_residue` and the second by
`Stacks.Chow.dvrRegularTameSymbol_apply`, so the comparison is an identification of two
power products in the residue field. On pairs of units of the fraction field the two agree as
well, because each is bimultiplicative in both arguments and every unit of the fraction field is
a quotient of two nonzerodivisors of `A`.

## Main results

* `Stacks.Chow.ordInt_regularFractionUnit` — the order of vanishing of a nonzerodivisor of a
  discrete valuation ring, read in the fraction field, is the exponent of a uniformizer in it.
* `Stacks.Chow.dvrRegularTameSymbol_eq_tameSymbol` — the two symbols agree on pairs of
  nonzerodivisors of `A`.
* `Stacks.Chow.dvrTameSymbol_eq_tameSymbol` — the two symbols agree on pairs of units of the
  fraction field.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 02Q6](https://stacks.math.columbia.edu/tag/02Q6)
-/

@[expose] public section

open IsLocalRing IsDiscreteValuationRing

universe u v

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The order of vanishing of a nonzerodivisor of a discrete valuation ring.** Read in the
fraction field it is `length_A(A / aA)`, which is the exponent of a uniformizer in `a`. -/
theorem ordInt_regularFractionUnit (a : nonZeroDivisors A) :
    ordInt A ((regularFractionUnit (Q := K) a : Kˣ) : K)
        (regularFractionUnit (Q := K) a).ne_zero = (dvrOrd a : ℤ) :=
  ordInt_algebraMap_eq_ord A (a : A) (mem_nonZeroDivisors_iff_ne_zero.mp a.2) _

/-- The image of a uniformizer in the fraction field is nonzero. -/
theorem algebraMap_ne_zero_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ) :
    algebraMap A K ϖ ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)

/-- The unit of the residue field appearing in the classical tame-symbol formula, as the residue
of a unit of `A`: for `a = u ϖ ^ m` and `b = v ϖ ^ n` the power product `a ^ n / b ^ m` of the
fraction field is the image of `u ^ n (v ^ m)⁻¹`. -/
theorem algebraMap_dvrUnitPart_zpow_div_zpow {ϖ : A} (hϖ : Irreducible ϖ)
    (a b : nonZeroDivisors A) :
    algebraMap A K
        (((dvrUnitPart hϖ a ^ dvrOrd b * (dvrUnitPart hϖ b ^ dvrOrd a)⁻¹ : Aˣ) : A)) =
      ((regularFractionUnit (Q := K) a : Kˣ) : K) ^
          ordInt A ((regularFractionUnit (Q := K) b : Kˣ) : K)
            (regularFractionUnit (Q := K) b).ne_zero /
        ((regularFractionUnit (Q := K) b : Kˣ) : K) ^
          ordInt A ((regularFractionUnit (Q := K) a : Kˣ) : K)
            (regularFractionUnit (Q := K) a).ne_zero := by
  have hϖ' : algebraMap A K ϖ ≠ 0 := algebraMap_ne_zero_of_irreducible (K := K) hϖ
  have hfac (x : nonZeroDivisors A) : ((regularFractionUnit (Q := K) x : Kˣ) : K) =
      algebraMap A K ((dvrUnitPart hϖ x : A)) * algebraMap A K ϖ ^ dvrOrd x := by
    rw [regularFractionUnit_val, dvrUnitPart_spec hϖ x, map_mul, map_pow]
  rw [Units.val_mul, map_mul, map_units_inv (algebraMap A K) (dvrUnitPart hϖ b ^ dvrOrd a),
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow,
    ordInt_regularFractionUnit (K := K) a, ordInt_regularFractionUnit (K := K) b,
    zpow_natCast, zpow_natCast, hfac a, hfac b, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm (dvrOrd a) (dvrOrd b)]
  have hu := ((dvrUnitPart hϖ a).isUnit.map (algebraMap A K)).ne_zero
  have hv := ((dvrUnitPart hϖ b).isUnit.map (algebraMap A K)).ne_zero
  field_simp

/-- **The two symbols of a discrete valuation ring agree on pairs of nonzerodivisors.** Both are
the classical formula `(-1) ^ (m n) ū ^ n v̄ ^ (-m)` on a simultaneous factorization
`a = u ϖ ^ m`, `b = v ϖ ^ n` by a uniformizer. -/
theorem dvrRegularTameSymbol_eq_tameSymbol (hdim : ringKrullDim A = 1) {ϖ : A}
    (hϖ : Irreducible ϖ) (a b : nonZeroDivisors A) :
    dvrRegularTameSymbol hϖ a b =
      AlgebraicGeometry.tameSymbol (K := K) hdim
        (regularFractionUnit a) (regularFractionUnit b) := by
  have hw := algebraMap_dvrUnitPart_zpow_div_zpow (K := K) hϖ a b
  set w : Aˣ := dvrUnitPart hϖ a ^ dvrOrd b * (dvrUnitPart hϖ b ^ dvrOrd a)⁻¹ with hwdef
  have hres : Units.map (residue A).toMonoidHom w =
      Units.map (residue A).toMonoidHom (dvrUnitPart hϖ a) ^ dvrOrd b *
        (Units.map (residue A).toMonoidHom (dvrUnitPart hϖ b) ^ dvrOrd a)⁻¹ := by
    rw [hwdef, map_mul, map_inv, map_pow, map_pow]
  have key : dvrRegularTameSymbol hϖ a b =
      (-1 : (ResidueField A)ˣ) ^ (dvrOrd a * dvrOrd b) *
        Units.map (residue A).toMonoidHom w := by
    rw [dvrRegularTameSymbol_apply, hres, dvrTameSymbolFormula, mul_assoc]
  refine Units.ext ?_
  rw [AlgebraicGeometry.tameSymbol_eq_negOnePow_mul_residue
      (regularFractionUnit (Q := K) a) (regularFractionUnit (Q := K) b) w hw,
    ordInt_regularFractionUnit (K := K) a, ordInt_regularFractionUnit (K := K) b,
    ← Int.natCast_mul, zpow_natCast, key, Units.val_mul]
  simp

/-- **The two symbols of a discrete valuation ring agree on pairs of units of the fraction
field.** Each is bimultiplicative, and every unit of the fraction field is a quotient of two
nonzerodivisors of `A`, so agreement on those determines both. -/
theorem dvrTameSymbol_eq_tameSymbol (hdim : ringKrullDim A = 1) {ϖ : A}
    (hϖ : Irreducible ϖ) (f g : Kˣ) :
    dvrTameSymbol hϖ K f g = AlgebraicGeometry.tameSymbol (K := K) hdim f g := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := K) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) (Q := K) g
  set T := AlgebraicGeometry.tameSymbol (K := K) hdim with hT
  have honel (y : Kˣ) : T.toFun 1 y = 1 :=
    right_eq_mul.mp (by simpa only [one_mul] using T.map_mul_left 1 1 y)
  have honer (x : Kˣ) : T.toFun x 1 = 1 :=
    right_eq_mul.mp (by simpa only [one_mul] using T.map_mul_right x 1 1)
  have hinvl (x y : Kˣ) : T.toFun x⁻¹ y = (T.toFun x y)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← T.map_mul_left, inv_mul_cancel, honel])
  have hinvr (x y : Kˣ) : T.toFun x y⁻¹ = (T.toFun x y)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by
      rw [mul_comm, ← T.map_mul_right, mul_inv_cancel, honer])
  have hval (x y : nonZeroDivisors A) :
      T.toFun (regularFractionUnit (Q := K) x) (regularFractionUnit (Q := K) y) =
        dvrRegularTameSymbol hϖ x y :=
    (dvrRegularTameSymbol_eq_tameSymbol (K := K) hdim hϖ x y).symm
  have expand : T.toFun f g =
      T.toFun (regularFractionUnit (Q := K) a) (regularFractionUnit (Q := K) c) *
          (T.toFun (regularFractionUnit (Q := K) a) (regularFractionUnit (Q := K) d))⁻¹ *
          (T.toFun (regularFractionUnit (Q := K) b) (regularFractionUnit (Q := K) c))⁻¹ *
        T.toFun (regularFractionUnit (Q := K) b) (regularFractionUnit (Q := K) d) := by
    rw [hf, hg, T.map_mul_left, hinvl, T.map_mul_right, T.map_mul_right, hinvr, hinvr]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  change _ = T.toFun f g
  rw [expand, hval a c, hval a d, hval b c, hval b d, dvrTameSymbol,
    (dvrRegularTameSymbol hϖ).extend_eq K a b c d hf hg]

end Stacks.Chow

end
