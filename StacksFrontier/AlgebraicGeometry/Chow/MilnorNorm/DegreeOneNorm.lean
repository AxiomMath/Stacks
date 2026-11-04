module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.NormResultant

/-!
# In degree one, the norm of a simple extension is the field norm

Let `k` be a field and `φ ∈ k[X]` monic irreducible, `κ = k[X] ⧸ φ`. This file proves that the
norm map `N_φ` of `Stacks.Chow.simpleMilnorNorm` is the field norm in degree one:

`N_φ {u} = {N_{κ/k}(u)}` for every `u ∈ κˣ`  (`Stacks.Chow.simpleMilnorNorm_milnorKSymbol`).

## The argument (Bass–Tate)

By strong induction on `deg φ`. Write `u` as the class of a polynomial `g` of degree below
`deg φ` and factor `g` into a constant and monic irreducibles of degree below `deg φ`; both sides
are multiplicative in `u`, so it suffices to treat the factors.

* For a constant `c`, `N_φ {c} = {c} · N_φ(1) = deg φ · {c} = {c ^ deg φ}`, by the projection
  formula and the degree-zero value.
* For a monic irreducible `χ ≠ φ`, the class `{χ, φ}` has residue `{χ̄}` at `φ`, residue `-{φ̄}`
  at `χ` and no other; adding a lift of `{φ̄}` with its only residue at `χ` gives a lift of
  `{χ̄}` with its only residue at `φ`. Hence
  `N_φ {χ̄} = -∂_∞ {χ, φ} + N_χ {φ̄} = deg χ · deg φ · {-1} + {N(φ mod χ)}`
  (`Stacks.Chow.simpleMilnorNorm_quotUnit`), using `∂_∞ {χ, φ} = deg χ · deg φ · {-1}`
  (`Stacks.Chow.infinityResidueRing_milnorKSymbol_mul_monic`) and the induction hypothesis for
  `χ`, of smaller degree. The reciprocity of norms
  `N(χ mod φ) = (-1)^{deg φ deg χ} N(φ mod χ)` (`Stacks.Chow.norm_mk_eq_neg_one_pow_mul_norm_mk`)
  finishes.

## Main results

* `Stacks.Chow.infinityResidueRing_milnorKSymbol_mul_monic` — `∂_∞ {χ, φ} = deg χ deg φ {-1}`.
* `Stacks.Chow.simpleMilnorNorm_quotUnit` — the reciprocity step.
* `Stacks.Chow.simpleMilnorNorm_milnorKSymbol` — **`N_φ {u} = {N_{κ/k}(u)}`.**

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* H. Bass, J. Tate, *The Milnor ring of a global field*, LNM 342 (1973), §I.5.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

attribute [local instance] Ideal.Quotient.field
attribute [local instance] isDiscreteValuationRing_localizationAtPrime_polynomial

/-! ### Classes of polynomials as units -/

/-- The class of a polynomial not divisible by `φ`, as a unit of `k[X] ⧸ φ`. -/
def quotUnit {d : ℕ} (φ : MonicIrreducibleOfDegree k d) (g : Polynomial k)
    (hg : ¬poly φ ∣ g) : (Polynomial k ⧸ Ideal.span {poly φ})ˣ :=
  Units.mk0 (Ideal.Quotient.mk _ g) fun h ↦
    hg (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h))

/-- The unit `quotUnit φ g hg` is the class of `g` in `k[X] ⧸ φ`. -/
@[simp]
theorem coe_quotUnit {d : ℕ} (φ : MonicIrreducibleOfDegree k d) (g : Polynomial k)
    (hg : ¬poly φ ∣ g) :
    (quotUnit φ g hg : Polynomial k ⧸ Ideal.span {poly φ}) = Ideal.Quotient.mk _ g :=
  rfl

/-- Two distinct monic irreducibles do not divide each other. -/
theorem not_dvd_of_poly_ne {d d' : ℕ} {ψ : MonicIrreducibleOfDegree k d}
    {χ : MonicIrreducibleOfDegree k d'} (h : poly ψ ≠ poly χ) : ¬poly ψ ∣ poly χ := fun hdvd ↦
  h (Polynomial.eq_of_monic_of_associated (monic ψ) (monic χ)
    ((irreducible ψ).associated_of_dvd (irreducible χ) hdvd))

/-- A polynomial not divisible by `φ` is a unit of the local ring at `φ` with residue its
class. -/
theorem exists_unit_residue_eq_quotUnit {d : ℕ} (φ : MonicIrreducibleOfDegree k d)
    {g : Polynomial k} (hg0 : g ≠ 0) (hg : ¬poly φ ∣ g) :
    ∃ w : (Localization.AtPrime (Ideal.span {poly φ}))ˣ,
      Units.map (algebraMap (Localization.AtPrime (Ideal.span {poly φ})) (RatFunc k) :
          Localization.AtPrime (Ideal.span {poly φ}) →* RatFunc k) w = polyUnit hg0 ∧
      Units.map ((quotientRingEquivResidueField (Ideal.span {poly φ})).symm :
          (Ideal.span {poly φ}).ResidueField →* (Polynomial k ⧸ Ideal.span {poly φ}))
        (Units.map (residue (Localization.AtPrime (Ideal.span {poly φ}))).toMonoidHom w) =
        quotUnit φ g hg := by
  obtain ⟨w, hw⟩ := exists_unit_localization_of_mem_polyUnitsNotDvd
    (p := poly φ) (u := polyUnit hg0) ⟨g, hg0, hg, rfl⟩
  have hwval : (w : Localization.AtPrime (Ideal.span {poly φ})) =
      algebraMap (Polynomial k) (Localization.AtPrime (Ideal.span {poly φ})) g := by
    refine IsFractionRing.injective (Localization.AtPrime (Ideal.span {poly φ})) (RatFunc k) ?_
    have h := congrArg (fun v : (RatFunc k)ˣ ↦ (v : RatFunc k)) hw
    simp only [Units.coe_map, MonoidHom.coe_coe, coe_polyUnit] at h
    rw [h, ← IsScalarTower.algebraMap_apply]
  refine ⟨w, hw, Units.ext ?_⟩
  change (quotientRingEquivResidueField (Ideal.span {poly φ})).symm
    (residue (Localization.AtPrime (Ideal.span {poly φ}))
      (w : Localization.AtPrime (Ideal.span {poly φ}))) = _
  rw [hwval, residue_algebraMap_eq_quotientRingEquivResidueField, RingEquiv.symm_apply_apply]
  rfl

/-! ### The residues of `{g, φ}` -/

/-- **`∂_φ {g, φ} = {ḡ}`** for `g` not divisible by `φ`. -/
theorem monicIrreducibleResidue_milnorKSymbol_mul_self {d : ℕ} (φ : MonicIrreducibleOfDegree k d)
    {g : Polynomial k} (hg0 : g ≠ 0) (hg : ¬poly φ ∣ g) :
    monicIrreducibleResidue φ (milnorKSymbol (RatFunc k) (polyUnit hg0) *
        milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ))) =
      milnorKSymbol _ (quotUnit φ g hg) := by
  obtain ⟨w, hw1, hw2⟩ := exists_unit_residue_eq_quotUnit φ hg0 hg
  have h := monicIrreducibleResidue_unitSymbolProd_mul_uniformizer φ [w]
  rw [dvrFracUniformizer_irreducible_algebraMap_self (ne_zero φ)] at h
  simpa only [unitSymbolProd, List.map_cons, List.map_nil, milnorKSymbolProd_singleton, hw1,
    hw2] using h

/-- **`∂_ψ {g, h} = 0`** when `ψ` divides neither `g` nor `h`. -/
theorem monicIrreducibleResidue_milnorKSymbol_mul_eq_zero {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d) {g h : Polynomial k} (hg0 : g ≠ 0) (hh0 : h ≠ 0)
    (hg : ¬poly ψ ∣ g) (hh : ¬poly ψ ∣ h) :
    monicIrreducibleResidue ψ (milnorKSymbol (RatFunc k) (polyUnit hg0) *
      milnorKSymbol (RatFunc k) (polyUnit hh0)) = 0 := by
  refine monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration ψ ?_
  rw [show milnorKSymbol (RatFunc k) (polyUnit hg0) * milnorKSymbol (RatFunc k) (polyUnit hh0) =
      milnorKSymbolProd (RatFunc k) [polyUnit hg0, polyUnit hh0] by
    rw [milnorKSymbolProd_cons, milnorKSymbolProd_singleton]]
  refine milnorKSymbolProd_mem_milnorKNotDvdFiltration fun v hv ↦ ?_
  rcases List.mem_cons.mp hv with rfl | hv'
  · exact ⟨g, hg0, hg, rfl⟩
  · rw [List.mem_singleton.mp hv']
    exact ⟨h, hh0, hh, rfl⟩

/-- **`∂_∞ {χ, φ} = deg χ · deg φ · {-1}`** for monic `χ` and `φ`. -/
theorem infinityResidueRing_milnorKSymbol_mul_monic {χ φ : Polynomial k} (hχ : χ.Monic)
    (hφ : φ.Monic) :
    infinityResidueRing k (milnorKSymbol (RatFunc k) (polyUnit hχ.ne_zero) *
        milnorKSymbol (RatFunc k) (polyUnit hφ.ne_zero)) =
      ((χ.natDegree * φ.natDegree : ℕ) : ℤ) • milnorKNegOne k := by
  rw [infinityResidueRing_apply, map_mul, map_mul, dvrMilnorShiftMap_inversion_monic hχ,
    dvrMilnorShiftMap_inversion_monic hφ, MilnorKShift.shift_mul]
  simp only [MilnorKShift.main_mk, MilnorKShift.shift_mk, zero_mul, map_zero, mul_zero,
    zero_add, smul_mul_assoc, one_mul, map_zsmul, milnorKNegOne_eq, milnorKRingMap_milnorKSymbol,
    smul_smul]
  congr 1
  · push_cast; ring
  · congr 1
    exact Units.ext (by simp)

/-! ### The reciprocity step -/

/-- **`N_φ {χ̄} = N_χ {φ̄} - deg χ · deg φ · {-1}`** for distinct monic irreducibles. -/
theorem simpleMilnorNorm_quotUnit {d d' : ℕ} (φ : MonicIrreducibleOfDegree k d)
    (χ : MonicIrreducibleOfDegree k d') (hne : poly χ ≠ poly φ) :
    simpleMilnorNorm φ (milnorKSymbol _ (quotUnit φ (poly χ) (not_dvd_of_poly_ne hne.symm))) =
      simpleMilnorNorm χ (milnorKSymbol _ (quotUnit χ (poly φ) (not_dvd_of_poly_ne hne))) -
        ((d' * d : ℕ) : ℤ) • milnorKNegOne k := by
  obtain ⟨z, hz⟩ := exists_isSingleResidueLift_ring' χ
    (milnorKSymbol _ (quotUnit χ (poly φ) (not_dvd_of_poly_ne hne)))
  set x := milnorKSymbol (RatFunc k) (polyUnit (ne_zero χ)) *
    milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ)) with hx
  have hxφ : monicIrreducibleResidue φ x =
      milnorKSymbol _ (quotUnit φ (poly χ) (not_dvd_of_poly_ne hne.symm)) :=
    monicIrreducibleResidue_milnorKSymbol_mul_self φ (ne_zero χ) _
  have hxχ : monicIrreducibleResidue χ x =
      -milnorKSymbol _ (quotUnit χ (poly φ) (not_dvd_of_poly_ne hne)) := by
    rw [hx, eq_neg_of_add_eq_zero_left (milnorKSymbol_mul_add_mul_comm _ _), map_neg,
      monicIrreducibleResidue_milnorKSymbol_mul_self χ (ne_zero φ) _]
  have hy : IsSingleResidueLift φ
      (milnorKSymbol _ (quotUnit φ (poly χ) (not_dvd_of_poly_ne hne.symm))) (x + z) := by
    refine ⟨by rw [map_add, hxφ, hz.2 d φ hne.symm, add_zero], fun d'' ψ hψ ↦ ?_⟩
    by_cases h : poly ψ = poly χ
    · obtain rfl : d'' = d' := by rw [← natDegree_eq ψ, h, natDegree_eq χ]
      obtain rfl := poly_injective h
      rw [map_add, hxχ, hz.1, neg_add_cancel]
    · rw [map_add, hx, monicIrreducibleResidue_milnorKSymbol_mul_eq_zero ψ _ _
        (not_dvd_of_poly_ne h) (not_dvd_of_poly_ne hψ), hz.2 _ ψ h, add_zero]
  rw [simpleMilnorNorm_eq hy, simpleMilnorNorm_eq hz, map_add, hx,
    infinityResidueRing_milnorKSymbol_mul_monic (monic χ) (monic φ), natDegree_eq,
    natDegree_eq]
  abel

/-! ### Constants -/

/-- **`N_φ {c} = {c ^ deg φ}`** for a constant `c`. -/
theorem simpleMilnorNorm_milnorKSymbol_algebraMap {d : ℕ} (φ : MonicIrreducibleOfDegree k d)
    (c : kˣ) :
    simpleMilnorNorm φ (milnorKSymbol _
        (Units.map ((algebraMap k (Polynomial k ⧸ Ideal.span {poly φ}) :
          k →+* Polynomial k ⧸ Ideal.span {poly φ}) : k →* Polynomial k ⧸ Ideal.span {poly φ})
          c)) =
      milnorKSymbol k (c ^ d) := by
  rw [← milnorKRingMap_milnorKSymbol, ← mul_one (milnorKRingMap _ _), simpleMilnorNorm_map_mul,
    simpleMilnorNorm_one, mul_smul_comm, mul_one, ← zpow_natCast, milnorKSymbol_zpow]

/-! ### The degree-one value -/

/-- `2 {-1} = 0`, in the form `-(n {-1}) = n {-1}`. -/
theorem neg_zsmul_milnorKNegOne (n : ℤ) : -(n • milnorKNegOne k) = n • milnorKNegOne k :=
  neg_eq_of_add_eq_zero_left (by rw [← smul_add, milnorKNegOne_add_self, smul_zero])

/-- **In degree one the norm of a simple extension is the field norm:
`N_φ {u} = {N_{κ/k}(u)}`.** -/
theorem simpleMilnorNorm_milnorKSymbol : ∀ (d : ℕ) (φ : MonicIrreducibleOfDegree k d)
    (u : (Polynomial k ⧸ Ideal.span {poly φ})ˣ),
    simpleMilnorNorm φ (milnorKSymbol _ u) =
      milnorKSymbol k (Units.map (Algebra.norm k :
        (Polynomial k ⧸ Ideal.span {poly φ}) →* k) u) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro φ
  let P : (Polynomial k ⧸ Ideal.span {poly φ})ˣ → Prop := fun v ↦
    simpleMilnorNorm φ (milnorKSymbol _ v) =
      milnorKSymbol k (Units.map (Algebra.norm k :
        (Polynomial k ⧸ Ideal.span {poly φ}) →* k) v)
  have hmul : ∀ v w, P v → P w → P (v * w) := fun v w hv hw ↦ by
    change simpleMilnorNorm φ _ = _
    rw [milnorKSymbol_mul, map_add, hv, hw, map_mul, milnorKSymbol_mul]
  have hconst : ∀ (v : (Polynomial k ⧸ Ideal.span {poly φ})ˣ) (c : kˣ),
      (v : Polynomial k ⧸ Ideal.span {poly φ}) = algebraMap k _ c → P v := by
    intro v c hv
    obtain rfl : v = Units.map ((algebraMap k (Polynomial k ⧸ Ideal.span {poly φ}) :
      k →+* Polynomial k ⧸ Ideal.span {poly φ}) : k →* Polynomial k ⧸ Ideal.span {poly φ}) c :=
      Units.ext hv
    change simpleMilnorNorm φ _ = _
    rw [simpleMilnorNorm_milnorKSymbol_algebraMap]
    congr 1
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_algebraMap,
      finrank_quotient_span_eq_natDegree, natDegree_eq]
  have hirr : ∀ χ : Polynomial k, ∀ hm : χ.Monic, ∀ hi : Irreducible χ, χ.natDegree < d →
      ∀ v : (Polynomial k ⧸ Ideal.span {poly φ})ˣ,
        (v : Polynomial k ⧸ Ideal.span {poly φ}) = Ideal.Quotient.mk _ χ → P v := by
    intro χ hm hi hlt v hv
    let χ' : MonicIrreducibleOfDegree k χ.natDegree := ⟨χ, hm, hi, rfl⟩
    have hne : poly χ' ≠ poly φ := fun h ↦ by
      have h1 := natDegree_eq φ
      rw [← h] at h1
      exact absurd h1 (Nat.ne_of_lt hlt)
    obtain rfl : v = quotUnit φ (poly χ') (not_dvd_of_poly_ne hne.symm) := Units.ext hv
    change simpleMilnorNorm φ _ = _
    rw [simpleMilnorNorm_quotUnit φ χ' hne, ih _ hlt χ']
    have hnorm : Units.map (Algebra.norm k : (Polynomial k ⧸ Ideal.span {poly φ}) →* k)
          (quotUnit φ (poly χ') (not_dvd_of_poly_ne hne.symm)) =
        (-1) ^ (d * χ.natDegree) * Units.map (Algebra.norm k :
          (Polynomial k ⧸ Ideal.span {poly χ'}) →* k)
          (quotUnit χ' (poly φ) (not_dvd_of_poly_ne hne)) := by
      refine Units.ext ?_
      have h := norm_mk_eq_neg_one_pow_mul_norm_mk (K := k) (monic φ) hm
      rw [natDegree_eq φ] at h
      simp only [Units.coe_map, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
        Units.val_one, coe_quotUnit]
      exact h
    rw [hnorm, milnorKSymbol_mul, ← zpow_natCast, milnorKSymbol_zpow, ← milnorKNegOne_eq,
      sub_eq_add_neg, neg_zsmul_milnorKNegOne, add_comm, mul_comm χ.natDegree d]
  have hpoly : ∀ g : Polynomial k, g ≠ 0 → g.natDegree < d →
      ∀ v : (Polynomial k ⧸ Ideal.span {poly φ})ˣ,
        (v : Polynomial k ⧸ Ideal.span {poly φ}) = Ideal.Quotient.mk _ g → P v := by
    intro g
    induction g using WfDvdMonoid.induction_on_irreducible with
    | zero => exact fun h ↦ absurd rfl h
    | unit p hp =>
        intro _ _ v hv
        obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hp
        exact hconst v hc.unit hv
    | mul a i ha0 hi iha =>
        intro hia hdeg v hv
        have hi0 : i ≠ 0 := hi.ne_zero
        have hdeg' : (i * a).natDegree = i.natDegree + a.natDegree := natDegree_mul hi0 ha0
        have hc0 : i.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hi0
        set i' := i * C i.leadingCoeff⁻¹ with hi'
        have hi'm : i'.Monic := monic_mul_leadingCoeff_inv hi0
        have hi'i : Irreducible i' := irreducible_mul_leadingCoeff_inv.mpr hi
        have hi'd : i'.natDegree = i.natDegree := natDegree_mul_C (inv_ne_zero hc0)
        have hfac : i * a = C i.leadingCoeff * i' * a := by
          rw [hi', mul_comm i (C _), ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
        have hv0 : (Ideal.Quotient.mk (Ideal.span {poly φ}) (i * a)) ≠ 0 := by
          rw [← hv]; exact Units.ne_zero v
        rw [hfac, map_mul, map_mul] at hv0
        have h1 := right_ne_zero_of_mul (left_ne_zero_of_mul hv0)
        have h2 := right_ne_zero_of_mul hv0
        have hv' : v = Units.mk0 _ (left_ne_zero_of_mul (left_ne_zero_of_mul hv0)) *
            Units.mk0 _ h1 * Units.mk0 _ h2 := by
          refine Units.ext ?_
          rw [hv, hfac, map_mul, map_mul]
          rfl
        rw [hv']
        exact hmul _ _ (hmul _ _ (hconst _ (Units.mk0 _ hc0) rfl)
          (hirr i' hi'm hi'i (by omega) _ rfl)) (iha ha0 (by omega) _ rfl)
  rcases d with _ | e
  · exact fun u ↦ (MonicIrreducibleOfDegree.isEmpty_zero.false φ).elim
  intro u
  exact hpoly (polyRep (monic φ) (ne_one φ) u) (polyRep_ne_zero (monic φ) (ne_one φ) u)
    (by have := natDegree_polyRep_lt (monic φ) (ne_one φ) u; rwa [natDegree_eq φ] at this) u
    (mk_polyRep (monic φ) (ne_one φ) u).symm

end Stacks.Chow

end
