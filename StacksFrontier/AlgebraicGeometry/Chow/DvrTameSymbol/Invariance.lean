module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueConstants

/-!
# The tame symbol of a discrete valuation ring: independence of the uniformizer, and base change

The tame symbol `∂_A : K^M_{i+1}(F) → K^M_i(κ)` of a discrete valuation ring `A` is built in
`StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol` from a chosen uniformizer `ϖ`:
it is the `ξ`-coefficient of the ring homomorphism

`θ_ϖ : K^M_*(F) → K^M_*(κ) ⊕ K^M_*(κ) ξ`, `f ↦ {f ϖ ^ -v(f)} + v(f) ξ`.

This file proves the two invariance properties of that construction.

* **Independence of the uniformizer.** If `ϖ' = w ϖ` with `w` a unit, then `θ_{ϖ'} = Φ ∘ θ_ϖ` for
  the ring automorphism `Φ(a + b ξ) = (a - b {w̄}) + b ξ` of `K^M_*(κ) ⊕ K^M_*(κ) ξ`
  (`Stacks.Chow.MilnorKShift.twist`), which does not change the `ξ`-coefficient. So `∂_A` does
  not depend on `ϖ` (`Stacks.Chow.dvrMilnorTameSymbol_irreducible_congr`).
* **Unramified base change.** If `A → B` is a local homomorphism of discrete valuation rings with
  the same fraction field `F`, carrying a uniformizer of `A` to a uniformizer of `B`, then
  `θ_B = (κ_A → κ_B)_* ∘ θ_A`, so `∂_B = (κ_A → κ_B)_* ∘ ∂_A`
  (`Stacks.Chow.dvrMilnorTameSymbol'_algebraMap`).

## Main definitions

* `Stacks.Chow.MilnorKShift.twist` — the automorphism `ξ ↦ ξ - c` attached to a degree-one symbol.
* `Stacks.Chow.MilnorKShift.map` — the ring homomorphism induced by a field homomorphism.

## Main results

* `Stacks.Chow.milnorKSymbol_mul_eq_milnorKInvolution_mul` — `{w} x = σ(x) {w}`.
* `Stacks.Chow.dvrMilnorShiftMap_shift_irreducible_congr`,
  `Stacks.Chow.dvrMilnorTameSymbol_irreducible_congr` — independence of the uniformizer.
* `Stacks.Chow.dvrMilnorShiftMap_shift_algebraMap`,
  `Stacks.Chow.dvrMilnorTameSymbol'_algebraMap` — unramified base change.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u v

section Ring

variable {k : Type u} [Field k]

/-- **A degree-one symbol commutes with everything up to the grading involution:**
`{w} x = σ(x) {w}`. -/
theorem milnorKSymbol_mul_eq_milnorKInvolution_mul (w : kˣ) (x : MilnorKRing k) :
    milnorKSymbol k w * x = milnorKInvolution k x * milnorKSymbol k w := by
  obtain ⟨t, rfl⟩ := milnorKRing_mk'_surjective k x
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
      rw [eq_intCast (algebraMap ℤ (MilnorKTensorAlgebra k)) r, map_intCast, map_intCast,
        Int.cast_comm]
  | ι a =>
      have hval : (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ a) =
          milnorKSymbol k (Additive.toMul a) := rfl
      rw [hval, milnorKInvolution_milnorKSymbol, neg_mul, eq_neg_iff_add_eq_zero]
      exact milnorKSymbol_mul_add_mul_comm w (Additive.toMul a)
  | mul a b ha hb =>
      rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [map_add, map_add, mul_add, add_mul, ha, hb]

/-- The square of a degree-one symbol: `{w} {w} = -{-1} {w}`. -/
theorem milnorKSymbol_mul_self_eq (w : kˣ) :
    milnorKSymbol k w * milnorKSymbol k w = -(milnorKNegOne k * milnorKSymbol k w) := by
  have h := milnorKSymbol_mul_self_add_mul_negOne (k := k) w
  rw [milnorKSymbol_mul_eq_milnorKInvolution_mul w (milnorKNegOne k),
    milnorKInvolution_milnorKNegOne] at h
  exact eq_neg_of_add_eq_zero_left h

namespace MilnorKShift

/-- **The twist of `K^M_*(k) ⊕ K^M_*(k) ξ` by a unit `w`**: `a + b ξ ↦ (a - b {w}) + b ξ`, that is
`ξ ↦ ξ - {w}`. It is a ring homomorphism and does not change the `ξ`-coefficient. -/
def twist (w : kˣ) : MilnorKShift k →+* MilnorKShift k where
  toFun x := mk (main x - shift x * milnorKSymbol k w) (shift x)
  map_one' := ext (by simp) (by simp)
  map_zero' := ext (by simp) (by simp)
  map_add' x y := ext (by simp only [main_mk, main_add, shift_add]; noncomm_ring)
    (by simp)
  map_mul' x y := by
    refine ext ?_ ?_
    · simp only [main_mk, main_mul, shift_mul]
      have h1 : shift x * milnorKSymbol k w * main y =
          shift x * milnorKInvolution k (main y) * milnorKSymbol k w := by
        rw [mul_assoc, milnorKSymbol_mul_eq_milnorKInvolution_mul, ← mul_assoc]
      have h2 : shift x * milnorKSymbol k w * (shift y * milnorKSymbol k w) =
          -(shift x * shift y * milnorKNegOne k * milnorKSymbol k w) := by
        have e1 : shift x * milnorKSymbol k w * (shift y * milnorKSymbol k w) =
            shift x * milnorKInvolution k (shift y) *
              (milnorKSymbol k w * milnorKSymbol k w) := by
          rw [mul_assoc (shift x), ← mul_assoc (milnorKSymbol k w) (shift y),
            milnorKSymbol_mul_eq_milnorKInvolution_mul w (shift y)]
          noncomm_ring
        rw [e1, milnorKSymbol_mul_self_eq, mul_neg, ← mul_assoc,
          mul_assoc (shift x) (milnorKInvolution k (shift y)),
          milnorKInvolution_mul_milnorKNegOne]
        noncomm_ring
      calc main x * main y - (main x * shift y + shift x * milnorKInvolution k (main y) +
              shift x * shift y * milnorKNegOne k) * milnorKSymbol k w
          = main x * main y - main x * shift y * milnorKSymbol k w -
              shift x * milnorKSymbol k w * main y +
              shift x * milnorKSymbol k w * (shift y * milnorKSymbol k w) := by
            rw [h1, h2]; noncomm_ring
        _ = (main x - shift x * milnorKSymbol k w) *
              (main y - shift y * milnorKSymbol k w) := by noncomm_ring
    · simp only [main_mk, shift_mk, shift_mul, map_sub, map_mul,
        milnorKInvolution_milnorKSymbol]
      have h3 : shift x * milnorKSymbol k w * shift y =
          shift x * milnorKInvolution k (shift y) * milnorKSymbol k w := by
        rw [mul_assoc, milnorKSymbol_mul_eq_milnorKInvolution_mul, ← mul_assoc]
      rw [sub_mul, h3]
      noncomm_ring

/-- The `K^M_*(k)`-part of `twist w x` is `main x - shift x · {w}`. -/
@[simp] theorem main_twist (w : kˣ) (x : MilnorKShift k) :
    main (twist w x) = main x - shift x * milnorKSymbol k w := rfl

/-- The `ξ`-part of `twist w x` is the `ξ`-part of `x`. -/
@[simp] theorem shift_twist (w : kˣ) (x : MilnorKShift k) : shift (twist w x) = shift x := rfl

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂]

/-- The symbol `{-1}` is preserved by the maps induced by field homomorphisms. -/
theorem milnorKRingMap_milnorKNegOne (φ : k₁ →+* k₂) :
    milnorKRingMap φ (milnorKNegOne k₁) = milnorKNegOne k₂ := by
  rw [milnorKNegOne_eq, milnorKRingMap_milnorKSymbol, milnorKNegOne_eq]
  congr 1
  ext
  simp

/-- **The ring homomorphism `K^M_*(k₁) ⊕ K^M_*(k₁) ξ → K^M_*(k₂) ⊕ K^M_*(k₂) ξ` induced by a field
homomorphism**, `a + b ξ ↦ φ_* a + φ_* b ξ`. -/
def map (φ : k₁ →+* k₂) : MilnorKShift k₁ →+* MilnorKShift k₂ where
  toFun x := mk (milnorKRingMap φ (main x)) (milnorKRingMap φ (shift x))
  map_one' := ext (by simp) (by simp)
  map_zero' := ext (by simp) (by simp)
  map_add' x y := ext (by simp) (by simp)
  map_mul' x y := ext (by simp) (by
    simp only [shift_mk, main_mk, shift_mul, main_mul, map_add, map_mul,
      Stacks.Chow.milnorKInvolution_milnorKRingMap, milnorKRingMap_milnorKNegOne])

/-- The `K^M_*(k₂)`-part of `map φ x` is the image under `φ_*` of the `K^M_*(k₁)`-part of `x`. -/
@[simp] theorem main_map (φ : k₁ →+* k₂) (x : MilnorKShift k₁) :
    main (map φ x) = milnorKRingMap φ (main x) := rfl

/-- The `ξ`-part of `map φ x` is the image under `φ_*` of the `ξ`-part of `x`. -/
@[simp] theorem shift_map (φ : k₁ →+* k₂) (x : MilnorKShift k₁) :
    shift (map φ x) = milnorKRingMap φ (shift x) := rfl

end MilnorKShift

end Ring

namespace Stacks.Chow

/-! ### Independence of the uniformizer -/

section Uniformizer

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {F : Type v} [Field F] [Algebra A F] [IsFractionRing A F]

/-- Two uniformizers differ by a unit. -/
theorem exists_unit_eq_mul_of_irreducible {ϖ ϖ' : A} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') : ∃ w : Aˣ, ϖ' = (w : A) * ϖ := by
  obtain ⟨w, hw⟩ := (associated_of_irreducible A hϖ hϖ')
  exact ⟨w, by rw [← hw, mul_comm]⟩

/-- **Changing the uniformizer twists `θ`**: `θ_{w ϖ} = Φ_{w̄} ∘ θ_ϖ`. -/
theorem dvrMilnorShiftMap_eq_twist_comp {ϖ : A} (hϖ : Irreducible ϖ) (w : Aˣ)
    (hwϖ : Irreducible ((w : A) * ϖ)) :
    dvrMilnorShiftMap (F := F) hwϖ =
      (MilnorKShift.twist (Units.map (residue A).toMonoidHom w)).comp
        (dvrMilnorShiftMap (F := F) hϖ) := by
  refine Stacks.Chow.milnorKRing_ringHom_ext fun f ↦ ?_
  obtain ⟨u, hu, hpart⟩ := exists_eq_unit_mul_zpow (F := F) hϖ f
  obtain ⟨n, hn⟩ : ∃ n, dvrFracOrd (F := F) hϖ f = n := ⟨_, rfl⟩
  rw [hn] at hu
  have hc : algebraMap A F (w : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr w.ne_zero
  have hval : algebraMap A F ((u * w ^ (-n) : Aˣ) : A) =
      algebraMap A F (u : A) * (algebraMap A F (w : A)) ^ (-n) := by
    have h := congrArg Units.val (map_mul (Units.map (algebraMap A F : A →* F)) u (w ^ (-n)))
    rw [map_zpow] at h
    simpa only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val]
      using h
  have hf' : (f : F) = algebraMap A F ((u * w ^ (-n) : Aˣ) : A) *
      (algebraMap A F ((w : A) * ϖ)) ^ n := by
    rw [hu, hval, map_mul, mul_zpow, zpow_neg, mul_assoc (algebraMap A F (u : A)),
      ← mul_assoc _ (_ ^ n), inv_mul_cancel₀ (zpow_ne_zero n hc), one_mul]
  have hord : dvrFracOrd (F := F) hwϖ f = n := dvrFracOrd_eq_of_eq hwϖ hf'
  have hpart' : dvrFracUnitPart (F := F) hwϖ f =
      Units.map (residue A).toMonoidHom (u * w ^ (-n)) := dvrFracUnitPart_eq_of_eq hwϖ hf'
  refine MilnorKShift.ext ?_ ?_
  · rw [RingHom.comp_apply, MilnorKShift.main_twist, dvrMilnorShiftMap_milnorKSymbol,
      dvrMilnorShiftMap_milnorKSymbol, main_dvrMilnorThetaHom, main_dvrMilnorThetaHom,
      shift_dvrMilnorThetaHom, hpart', hpart, hn, map_mul, map_zpow, milnorKSymbol_mul,
      milnorKSymbol_zpow, smul_mul_assoc, one_mul, neg_smul, sub_eq_add_neg]
  · rw [RingHom.comp_apply, MilnorKShift.shift_twist, dvrMilnorShiftMap_milnorKSymbol,
      dvrMilnorShiftMap_milnorKSymbol, shift_dvrMilnorThetaHom, shift_dvrMilnorThetaHom, hord, hn]

/-- **The `ξ`-coefficient of `θ_ϖ` does not depend on the uniformizer `ϖ`.** -/
theorem dvrMilnorShiftMap_shift_irreducible_congr {ϖ ϖ' : A} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (x : MilnorKRing F) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ' x) =
      MilnorKShift.shift (dvrMilnorShiftMap (F := F) hϖ x) := by
  obtain ⟨w, rfl⟩ := exists_unit_eq_mul_of_irreducible hϖ hϖ'
  rw [dvrMilnorShiftMap_eq_twist_comp hϖ w hϖ', RingHom.comp_apply, MilnorKShift.shift_twist]

/-- **The tame symbol `∂_A` does not depend on the uniformizer.** -/
theorem dvrMilnorTameSymbol_irreducible_congr {ϖ ϖ' : A} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (i : ℕ) :
    dvrMilnorTameSymbol (F := F) hϖ' i = dvrMilnorTameSymbol (F := F) hϖ i :=
  AddMonoidHom.ext fun y ↦ Subtype.ext (by
    rw [dvrMilnorTameSymbol_coe, dvrMilnorTameSymbol_coe,
      dvrMilnorShiftMap_shift_irreducible_congr hϖ hϖ'])

/-- The tame symbol with no choice in its statement is the tame symbol of any uniformizer. -/
theorem dvrMilnorTameSymbol'_eq {ϖ : A} (hϖ : Irreducible ϖ) (i : ℕ) :
    dvrMilnorTameSymbol' A F i = dvrMilnorTameSymbol (F := F) hϖ i :=
  dvrMilnorTameSymbol_irreducible_congr (F := F) hϖ (exists_irreducible A).choose_spec i

end Uniformizer

/-! ### Unramified base change -/

section BaseChange

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {F : Type v} [Field F] [Algebra A F] [IsFractionRing A F] [Algebra B F]
  [IsFractionRing B F] [Algebra A B] [IsScalarTower A B F] [IsLocalHom (algebraMap A B)]

/-- **`θ` under an unramified local homomorphism of discrete valuation rings with the same
fraction field**: if `ϖ` is a uniformizer of `A` whose image is a uniformizer of `B`, then
`θ_B = (κ_A → κ_B)_* ∘ θ_A`. -/
theorem dvrMilnorShiftMap_algebraMap {ϖ : A} (hϖ : Irreducible ϖ)
    (hϖB : Irreducible (algebraMap A B ϖ)) :
    dvrMilnorShiftMap (A := B) (F := F) hϖB =
      (MilnorKShift.map (algebraMap (ResidueField A) (ResidueField B))).comp
        (dvrMilnorShiftMap (A := A) (F := F) hϖ) := by
  refine Stacks.Chow.milnorKRing_ringHom_ext fun f ↦ ?_
  obtain ⟨u, hu, hpart⟩ := exists_eq_unit_mul_zpow (F := F) hϖ f
  have hf' : (f : F) = algebraMap B F ((Units.map (algebraMap A B : A →* B) u : Bˣ) : B) *
      (algebraMap B F (algebraMap A B ϖ)) ^ dvrFracOrd (F := F) hϖ f := by
    rw [hu, Units.coe_map, MonoidHom.coe_coe, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hord : dvrFracOrd (F := F) hϖB f = dvrFracOrd (F := F) hϖ f := dvrFracOrd_eq_of_eq hϖB hf'
  have hpart' : dvrFracUnitPart (F := F) hϖB f =
      Units.map (residue B).toMonoidHom (Units.map (algebraMap A B : A →* B) u) :=
    dvrFracUnitPart_eq_of_eq hϖB hf'
  refine MilnorKShift.ext ?_ ?_
  · rw [RingHom.comp_apply, MilnorKShift.main_map, dvrMilnorShiftMap_milnorKSymbol,
      dvrMilnorShiftMap_milnorKSymbol, main_dvrMilnorThetaHom, main_dvrMilnorThetaHom,
      milnorKRingMap_milnorKSymbol, hpart', hpart]
    congr 1
  · rw [RingHom.comp_apply, MilnorKShift.shift_map, dvrMilnorShiftMap_milnorKSymbol,
      dvrMilnorShiftMap_milnorKSymbol, shift_dvrMilnorThetaHom, shift_dvrMilnorThetaHom, hord,
      map_zsmul, map_one]

/-- **The `ξ`-coefficient of `θ` under an unramified local homomorphism of discrete valuation
rings with the same fraction field.** -/
theorem dvrMilnorShiftMap_shift_algebraMap {ϖA : A} (hϖA : Irreducible ϖA) {ϖB : B}
    (hϖB : Irreducible ϖB) (hunr : Irreducible (algebraMap A B ϖA)) (x : MilnorKRing F) :
    MilnorKShift.shift (dvrMilnorShiftMap (A := B) (F := F) hϖB x) =
      milnorKRingMap (algebraMap (ResidueField A) (ResidueField B))
        (MilnorKShift.shift (dvrMilnorShiftMap (A := A) (F := F) hϖA x)) := by
  rw [dvrMilnorShiftMap_shift_irreducible_congr hunr hϖB, dvrMilnorShiftMap_algebraMap hϖA hunr,
    RingHom.comp_apply, MilnorKShift.shift_map]

/-- **The tame symbol under an unramified local homomorphism of discrete valuation rings with the
same fraction field**: `∂_B = (κ_A → κ_B)_* ∘ ∂_A`. -/
theorem dvrMilnorTameSymbol'_algebraMap {ϖ : A} (hϖ : Irreducible ϖ)
    (hunr : Irreducible (algebraMap A B ϖ)) (i : ℕ) (y : MilnorKTheory F (i + 1)) :
    dvrMilnorTameSymbol' B F i y =
      milnorKTransport (algebraMap (ResidueField A) (ResidueField B)) i
        (dvrMilnorTameSymbol' A F i y) := by
  have hch : Irreducible (algebraMap A B (exists_irreducible A).choose) := by
    obtain ⟨w, hw⟩ := exists_unit_eq_mul_of_irreducible hϖ (exists_irreducible A).choose_spec
    rw [hw, map_mul]
    exact (associated_unit_mul_left _ _ (w.isUnit.map (algebraMap A B))).symm.irreducible hunr
  refine Subtype.ext ?_
  rw [dvrMilnorTameSymbol'_coe, milnorKTransport_coe, dvrMilnorTameSymbol'_coe,
    dvrMilnorShiftMap_shift_algebraMap (exists_irreducible A).choose_spec
      (exists_irreducible B).choose_spec hch]

end BaseChange

end Stacks.Chow

end
