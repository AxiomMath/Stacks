module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol

/-!
# Units of the fraction field of a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `F`, and fix a uniformizer `ϖ`. Then
every unit of `F` is uniquely `u ϖ ^ n` for a unit `u` of `A` and an integer `n`: the group
`Fˣ` is `Aˣ × ℤ`. This file proves that (`dvrFracUnitsEquiv`) and reads off the two coordinates:

* `dvrFracOrd hϖ f = n`, the valuation of `f`;
* `dvrFracUnitPart hϖ f`, the residue of `f ϖ ^ -n`, a unit of the residue field.

Both are multiplicative, and the pair is pinned down by any presentation `f = u ϖ ^ n` at all.
This is the fraction-field counterpart of `Stacks.Chow.dvrOrd` and `Stacks.Chow.dvrUnitPart`,
which do the same for nonzerodivisors of `A`.

Given units `f, g` of `F` with `f + g = 1`,

* if `v(f) > 0` then `v(g) = 0` and the unit part of `g` is `1`;
* if `v(f) < 0` then `v(g) = v(f)` and the unit part of `g` is minus that of `f`;
* if `v(f) = 0` and `v(g) > 0` then the unit part of `f` is `1`;
* if `v(f) = v(g) = 0` then the two unit parts add to `1` in the residue field.

## Main definitions

* `Stacks.Chow.dvrFracUniformizer` — a uniformizer, as a unit of the fraction field.
* `Stacks.Chow.dvrFracUnitsEquiv` — the isomorphism `Aˣ × ℤ ≃ Fˣ`.
* `Stacks.Chow.dvrFracOrd`, `Stacks.Chow.dvrFracUnitPart` — the two coordinates.

## Main results

* `Stacks.Chow.dvrFracOrd_eq_of_eq`, `Stacks.Chow.dvrFracUnitPart_eq_of_eq` — the coordinates are
  determined by any presentation `f = u ϖ ^ n`.
* `Stacks.Chow.dvrFracOrd_mul`, `Stacks.Chow.dvrFracUnitPart_mul` — both are multiplicative.
* `Stacks.Chow.dvrFracOrd_eq_zero_and_dvrFracUnitPart_eq_one_of_pos`,
  `Stacks.Chow.dvrFracOrd_eq_and_dvrFracUnitPart_eq_neg_of_neg`,
  `Stacks.Chow.dvrFracUnitPart_eq_one_of_pos`, `Stacks.Chow.dvrFracUnitPart_add_eq_one` — the
  four cases above.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u v

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {F : Type v} [Field F] [Algebra A F] [IsFractionRing A F]
variable {ϖ : A}

/-! ### `Fˣ` is `Aˣ × ℤ` -/

/-- A uniformizer of a discrete valuation ring, as a unit of the fraction field. -/
def dvrFracUniformizer (F : Type v) [Field F] [Algebra A F] [IsFractionRing A F]
    (hϖ : Irreducible ϖ) : Fˣ :=
  Units.mk0 (algebraMap A F ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hϖ.ne_zero)

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The underlying element of `dvrFracUniformizer F hϖ` is the image of `ϖ` in `F`. -/
@[simp]
theorem dvrFracUniformizer_val (hϖ : Irreducible ϖ) :
    (dvrFracUniformizer F hϖ : F) = algebraMap A F ϖ := rfl

/-- `(u, n) ↦ u ϖ ^ n`, as a homomorphism from `Aˣ × ℤ` to the units of the fraction field. -/
def dvrFracUnitsHom (F : Type v) [Field F] [Algebra A F] [IsFractionRing A F]
    (hϖ : Irreducible ϖ) : Aˣ × Multiplicative ℤ →* Fˣ where
  toFun p := Units.map (algebraMap A F : A →* F) p.1 *
    dvrFracUniformizer F hϖ ^ Multiplicative.toAdd p.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, toAdd_mul, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- `dvrFracUnitsHom F hϖ` sends `(u, n)` to `u ϖ ^ n` in `F`. -/
@[simp]
theorem dvrFracUnitsHom_apply (hϖ : Irreducible ϖ) (p : Aˣ × Multiplicative ℤ) :
    (dvrFracUnitsHom F hϖ p : F) =
      algebraMap A F (p.1 : A) * (algebraMap A F ϖ) ^ Multiplicative.toAdd p.2 := by
  simp [dvrFracUnitsHom]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- A unit of `A` times a nonnegative power of a uniformizer is `1` only trivially: a positive
power of a uniformizer is not a unit. -/
private theorem dvrFrac_eq_one_aux (hϖ : Irreducible ϖ) (u : Aˣ) (m : ℕ)
    (h : algebraMap A F (u : A) * (algebraMap A F ϖ) ^ (m : ℤ) = 1) : m = 0 ∧ u = 1 := by
  have hA : algebraMap A F ((u : A) * ϖ ^ m) = algebraMap A F 1 := by
    rw [map_mul, map_pow, map_one, ← zpow_natCast (algebraMap A F ϖ) m]
    exact h
  have hring : (u : A) * ϖ ^ m = 1 := (IsFractionRing.injective A F) hA
  have hunit : IsUnit (ϖ ^ m) := ⟨⟨ϖ ^ m, u, by rw [mul_comm, hring], hring⟩, rfl⟩
  have hm : m = 0 := by
    by_contra hm
    exact hϖ.not_isUnit ((isUnit_pow_iff hm).mp hunit)
  refine ⟨hm, Units.ext ?_⟩
  rw [hm, pow_zero, mul_one] at hring
  simpa using hring

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The homomorphism `(u, n) ↦ u ϖ ^ n` from `Aˣ × ℤ` to `Fˣ` is injective. -/
theorem dvrFracUnitsHom_injective (hϖ : Irreducible ϖ) :
    Function.Injective (dvrFracUnitsHom F hϖ) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  rintro ⟨u, n⟩ hp
  have hval : algebraMap A F (u : A) * (algebraMap A F ϖ) ^ Multiplicative.toAdd n = 1 := by
    simpa using congrArg (Units.val) hp
  set m : ℤ := Multiplicative.toAdd n with hm
  rcases le_or_gt 0 m with hm0 | hm0
  · obtain ⟨p, hp'⟩ := Int.eq_ofNat_of_zero_le hm0
    rw [hp'] at hval
    obtain ⟨hp0, hu⟩ := dvrFrac_eq_one_aux (F := F) hϖ u p hval
    refine Prod.ext hu ?_
    have : m = 0 := by rw [hp', hp0]; rfl
    exact Multiplicative.toAdd.injective (by simpa [hm] using this)
  · exfalso
    have hinv : algebraMap A F ((u⁻¹ : Aˣ) : A) * (algebraMap A F ϖ) ^ (-m) = 1 := by
      rw [map_units_inv, zpow_neg, ← mul_inv, hval, inv_one]
    obtain ⟨p, hp'⟩ := Int.eq_ofNat_of_zero_le (le_of_lt (neg_pos.mpr hm0))
    rw [hp'] at hinv
    obtain ⟨hp0, -⟩ := dvrFrac_eq_one_aux (F := F) hϖ u⁻¹ p hinv
    rw [hp0] at hp'
    omega

/-- The homomorphism `(u, n) ↦ u ϖ ^ n` from `Aˣ × ℤ` to `Fˣ` is surjective. -/
theorem dvrFracUnitsHom_surjective (hϖ : Irreducible ϖ) :
    Function.Surjective (dvrFracUnitsHom F hϖ) := by
  intro x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := A) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨b, hb⟩
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, zero_div] at hab
    exact x.ne_zero hab.symm
  obtain ⟨p, u, hu⟩ := eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨q, w, hw⟩ := eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(u * w⁻¹, Multiplicative.ofAdd ((p : ℤ) - (q : ℤ))), Units.ext ?_⟩
  have hπ : algebraMap A F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hϖ.ne_zero
  have hwF : algebraMap A F (w : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr w.ne_zero
  have hwinv : algebraMap A F ((w⁻¹ : Aˣ) : A) = (algebraMap A F (w : A))⁻¹ := map_units_inv _ w
  rw [dvrFracUnitsHom_apply, ← hab, hu, hw]
  simp only [Units.val_mul, map_mul, map_pow, toAdd_ofAdd]
  rw [zpow_sub₀ hπ, zpow_natCast, zpow_natCast, hwinv]
  field_simp

/-- **`Fˣ ≅ Aˣ × ℤ`.** For a discrete valuation ring `A` with fraction field `F` and uniformizer
`ϖ`, every unit of `F` is uniquely a unit of `A` times an integral power of `ϖ`. -/
def dvrFracUnitsEquiv (F : Type v) [Field F] [Algebra A F] [IsFractionRing A F]
    (hϖ : Irreducible ϖ) : Aˣ × Multiplicative ℤ ≃* Fˣ :=
  MulEquiv.ofBijective (dvrFracUnitsHom F hϖ)
    ⟨dvrFracUnitsHom_injective hϖ, dvrFracUnitsHom_surjective hϖ⟩

/-- `dvrFracUnitsEquiv F hϖ` agrees with `dvrFracUnitsHom F hϖ`. -/
@[simp]
theorem dvrFracUnitsEquiv_apply (hϖ : Irreducible ϖ) (p : Aˣ × Multiplicative ℤ) :
    dvrFracUnitsEquiv F hϖ p = dvrFracUnitsHom F hϖ p := rfl

/-! ### The two coordinates -/

/-- The valuation of a unit of the fraction field of a discrete valuation ring: the exponent of
the uniformizer in it. -/
def dvrFracOrd (hϖ : Irreducible ϖ) (x : Fˣ) : ℤ :=
  Multiplicative.toAdd ((dvrFracUnitsEquiv F hϖ).symm x).2

/-- The unit part of a unit `f` of the fraction field, relative to a uniformizer `ϖ`: the residue
of `f ϖ ^ -v(f)`, a unit of the residue field. -/
def dvrFracUnitPart (hϖ : Irreducible ϖ) (x : Fˣ) : (ResidueField A)ˣ :=
  Units.map (residue A).toMonoidHom ((dvrFracUnitsEquiv F hϖ).symm x).1

/-- If `x = u ϖ ^ n` in `F` then the inverse of `dvrFracUnitsEquiv F hϖ` sends `x` to `(u, n)`. -/
theorem dvrFracUnitsEquiv_symm_eq {x : Fˣ} {u : Aˣ} {n : ℤ} (hϖ : Irreducible ϖ)
    (hx : (x : F) = algebraMap A F (u : A) * (algebraMap A F ϖ) ^ n) :
    (dvrFracUnitsEquiv F hϖ).symm x = (u, Multiplicative.ofAdd n) := by
  have hmap : dvrFracUnitsEquiv F hϖ (u, Multiplicative.ofAdd n) = x := by
    refine Units.ext ?_
    rw [dvrFracUnitsEquiv_apply, dvrFracUnitsHom_apply, hx]
    simp
  rw [← hmap, MulEquiv.symm_apply_apply]

/-- If `x = u ϖ ^ n` in `F` with `u` a unit of `A`, then the valuation of `x` is `n`. -/
theorem dvrFracOrd_eq_of_eq {x : Fˣ} {u : Aˣ} {n : ℤ} (hϖ : Irreducible ϖ)
    (hx : (x : F) = algebraMap A F (u : A) * (algebraMap A F ϖ) ^ n) :
    dvrFracOrd hϖ x = n := by
  rw [dvrFracOrd, dvrFracUnitsEquiv_symm_eq hϖ hx]
  simp

/-- If `x = u ϖ ^ n` in `F` with `u` a unit of `A`, then the unit part of `x` is the residue
of `u`. -/
theorem dvrFracUnitPart_eq_of_eq {x : Fˣ} {u : Aˣ} {n : ℤ} (hϖ : Irreducible ϖ)
    (hx : (x : F) = algebraMap A F (u : A) * (algebraMap A F ϖ) ^ n) :
    dvrFracUnitPart hϖ x = Units.map (residue A).toMonoidHom u := by
  rw [dvrFracUnitPart, dvrFracUnitsEquiv_symm_eq hϖ hx]

/-- Every unit of the fraction field is a unit of `A` times a power of the uniformizer, with the
exponent its valuation and the unit its unit part. -/
theorem exists_eq_unit_mul_zpow (hϖ : Irreducible ϖ) (x : Fˣ) :
    ∃ u : Aˣ, (x : F) = algebraMap A F (u : A) * (algebraMap A F ϖ) ^ dvrFracOrd hϖ x ∧
      dvrFracUnitPart hϖ x = Units.map (residue A).toMonoidHom u := by
  refine ⟨((dvrFracUnitsEquiv F hϖ).symm x).1, ?_, rfl⟩
  have hx : dvrFracUnitsEquiv F hϖ ((dvrFracUnitsEquiv F hϖ).symm x) = x :=
    (dvrFracUnitsEquiv F hϖ).apply_symm_apply x
  rw [dvrFracUnitsEquiv_apply] at hx
  have := congrArg (Units.val) hx
  rw [dvrFracUnitsHom_apply] at this
  rw [← this, dvrFracOrd]

/-- The valuation of `1` is `0`. -/
@[simp]
theorem dvrFracOrd_one (hϖ : Irreducible ϖ) : dvrFracOrd (F := F) hϖ 1 = 0 :=
  dvrFracOrd_eq_of_eq (u := 1) (n := 0) hϖ (by simp)

/-- The unit part of `1` is `1`. -/
@[simp]
theorem dvrFracUnitPart_one (hϖ : Irreducible ϖ) :
    dvrFracUnitPart (F := F) hϖ 1 = 1 := by
  rw [dvrFracUnitPart_eq_of_eq (u := 1) (n := 0) hϖ (by simp)]
  exact Units.ext (by simp)

/-- The valuation of a product of units of `F` is the sum of their valuations. -/
theorem dvrFracOrd_mul (hϖ : Irreducible ϖ) (x y : Fˣ) :
    dvrFracOrd hϖ (x * y) = dvrFracOrd hϖ x + dvrFracOrd hϖ y := by
  rw [dvrFracOrd, dvrFracOrd, dvrFracOrd, map_mul, Prod.snd_mul, toAdd_mul]

/-- The unit part of a product of units of `F` is the product of their unit parts. -/
theorem dvrFracUnitPart_mul (hϖ : Irreducible ϖ) (x y : Fˣ) :
    dvrFracUnitPart hϖ (x * y) = dvrFracUnitPart hϖ x * dvrFracUnitPart hϖ y := by
  rw [dvrFracUnitPart, dvrFracUnitPart, dvrFracUnitPart, map_mul, Prod.fst_mul, map_mul]

/-- A unit of `F` of valuation zero comes from a unit of `A`. -/
theorem exists_val_eq_algebraMap_of_dvrFracOrd_eq_zero (hϖ : Irreducible ϖ) {x : Fˣ}
    (hx : dvrFracOrd hϖ x = 0) :
    ∃ u : Aˣ, (x : F) = algebraMap A F (u : A) ∧
      dvrFracUnitPart hϖ x = Units.map (residue A).toMonoidHom u := by
  obtain ⟨u, hu, hpart⟩ := exists_eq_unit_mul_zpow hϖ x
  exact ⟨u, by rw [hu, hx, zpow_zero, mul_one], hpart⟩

/-! ### Units of `F` adding up to `1` -/

/-- If `g = a ϖ ^ n` with `a` of nonzero residue, then `g` has valuation `n` and unit part the
residue of `a`. -/
private theorem dvrFracOrd_and_unitPart_of_residue_ne_zero (hϖ : Irreducible ϖ) {g : Fˣ} {a : A}
    {n : ℤ} (ha : residue A a ≠ 0) (hg : (g : F) = algebraMap A F a * (algebraMap A F ϖ) ^ n) :
    dvrFracOrd hϖ g = n ∧ (dvrFracUnitPart hϖ g : ResidueField A) = residue A a := by
  obtain ⟨w, rfl⟩ : IsUnit a := isUnit_of_residue_ne_zero ha
  exact ⟨dvrFracOrd_eq_of_eq hϖ hg, by rw [dvrFracUnitPart_eq_of_eq hϖ hg]; rfl⟩

/-- If `f + g = 1` and `f` has positive valuation then `g` is a unit of `A` congruent to `1`:
its valuation is zero and its unit part is `1`. -/
theorem dvrFracOrd_eq_zero_and_dvrFracUnitPart_eq_one_of_pos (hϖ : Irreducible ϖ) {f g : Fˣ}
    (hfg : (f : F) + (g : F) = 1) (hf : 0 < dvrFracOrd hϖ f) :
    dvrFracOrd hϖ g = 0 ∧ dvrFracUnitPart hϖ g = 1 := by
  obtain ⟨u, hu, -⟩ := exists_eq_unit_mul_zpow hϖ f
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le hf.le
  have hp0 : p ≠ 0 := by omega
  have hres : residue A (1 - (u : A) * ϖ ^ p) = 1 := by
    rw [map_sub, map_one, map_mul, map_pow, residue_eq_zero_of_irreducible hϖ,
      zero_pow hp0, mul_zero, sub_zero]
  obtain ⟨h0, h1⟩ := dvrFracOrd_and_unitPart_of_residue_ne_zero hϖ (g := g)
    (a := 1 - (u : A) * ϖ ^ p) (n := 0) (by rw [hres]; exact one_ne_zero)
    (by rw [zpow_zero, mul_one, map_sub, map_one, map_mul, map_pow, ← zpow_natCast, ← hp, ← hu,
      ← hfg, add_sub_cancel_left])
  exact ⟨h0, Units.ext (h1.trans hres)⟩

/-- If `f + g = 1` and `f` has valuation zero while `g` has positive valuation, then the unit
part of `f` is `1`. -/
theorem dvrFracUnitPart_eq_one_of_pos (hϖ : Irreducible ϖ) {f g : Fˣ}
    (hfg : (f : F) + (g : F) = 1) (hg : 0 < dvrFracOrd hϖ g) :
    dvrFracUnitPart hϖ f = 1 :=
  (dvrFracOrd_eq_zero_and_dvrFracUnitPart_eq_one_of_pos hϖ (by rw [← hfg]; ring) hg).2

/-- If `f + g = 1` and `f` has negative valuation then `g` has the same valuation as `f`, and
the unit part of `g` is minus that of `f`. -/
theorem dvrFracOrd_eq_and_dvrFracUnitPart_eq_neg_of_neg (hϖ : Irreducible ϖ) {f g : Fˣ}
    (hfg : (f : F) + (g : F) = 1) (hf : dvrFracOrd hϖ f < 0) :
    dvrFracOrd hϖ g = dvrFracOrd hϖ f ∧
      dvrFracUnitPart hϖ g = -dvrFracUnitPart hϖ f := by
  obtain ⟨u, hu, hpart⟩ := exists_eq_unit_mul_zpow hϖ f
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hf.le)
  have hp0 : p ≠ 0 := by omega
  have hπ : algebraMap A F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hϖ.ne_zero
  have hres : residue A (ϖ ^ p - (u : A)) = -residue A (u : A) := by
    rw [map_sub, map_pow, residue_eq_zero_of_irreducible hϖ, zero_pow hp0, zero_sub]
  obtain ⟨h0, h1⟩ := dvrFracOrd_and_unitPart_of_residue_ne_zero hϖ (g := g)
    (a := ϖ ^ p - (u : A)) (n := dvrFracOrd hϖ f)
    (by rw [hres, neg_ne_zero]; exact residue_unit_ne_zero u)
    (by rw [show (g : F) = 1 - f by rw [← hfg]; ring, hu, map_sub, map_pow, sub_mul,
      ← zpow_natCast (algebraMap A F ϖ) p, ← zpow_add₀ hπ,
      show (p : ℤ) + dvrFracOrd hϖ f = 0 by omega, zpow_zero])
  refine ⟨h0, Units.ext ?_⟩
  rw [h1, hres, hpart]
  simp

/-- If `f + g = 1` and both have valuation zero then their unit parts add to `1` in the residue
field. -/
theorem dvrFracUnitPart_add_eq_one (hϖ : Irreducible ϖ) {f g : Fˣ}
    (hfg : (f : F) + (g : F) = 1) (hf : dvrFracOrd hϖ f = 0) (hg : dvrFracOrd hϖ g = 0) :
    (dvrFracUnitPart hϖ f : ResidueField A) + (dvrFracUnitPart hϖ g : ResidueField A) = 1 := by
  obtain ⟨u, hu, hpu⟩ := exists_val_eq_algebraMap_of_dvrFracOrd_eq_zero hϖ hf
  obtain ⟨v, hv, hpv⟩ := exists_val_eq_algebraMap_of_dvrFracOrd_eq_zero hϖ hg
  have hA : algebraMap A F ((u : A) + (v : A)) = algebraMap A F 1 := by
    rw [map_add, map_one, ← hu, ← hv, hfg]
  have hring : (u : A) + (v : A) = 1 := IsFractionRing.injective A F hA
  rw [hpu, hpv]
  show residue A (u : A) + residue A (v : A) = 1
  rw [← map_add, hring, map_one]

end Stacks.Chow
