module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.KummerCover

/-!
# Automorphisms of `F[X]_X`

For a field `F`, the ring `F[X]_X` of Laurent polynomials has the automorphisms `X ↦ c X`
(`c ∈ Fˣ`) and the automorphisms induced by ring automorphisms of the coefficients. They form
group homomorphisms `Fˣ →* RingAut F[X]_X` and `RingAut F →* RingAut F[X]_X`, and conjugating
`X ↦ c X` by the coefficient automorphism `σ` gives `X ↦ σ(c) X`.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.scaleAut F`: `c ↦ (X ↦ c X)`.
* `AlgebraicGeometry.TameMultiplicativeGroup.coeffAut F`: `σ ↦ (∑ a_i X^i ↦ ∑ σ(a_i) X^i)`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.coeffAut_mul_scaleAut_mul_inv`: the conjugation
  formula.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (F : Type*) [Field F]

/-- Two ring maps out of `F[X]_X` agreeing on constants and on `X` are equal. -/
theorem ringHom_ext_ring {S : Type*} [CommRing S] {f g : Ring F →+* S}
    (hC : ∀ a : F, f (algebraMap F[X] (Ring F) (C a)) = g (algebraMap F[X] (Ring F) (C a)))
    (hX : f (coord F) = g (coord F)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (X : F[X]))
    (Polynomial.ringHom_ext (fun a ↦ hC a) hX)

/-- The map `X ↦ c X` of `F[X]_X`, for `c ≠ 0`. -/
def scaleHom (c : Fˣ) : Ring F →+* Ring F :=
  IsLocalization.Away.lift (X : F[X])
    (g := (algebraMap F[X] (Ring F)).comp (eval₂RingHom C (C (c : F) * X)))
    (by
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, map_mul]
      exact ((IsUnit.map C c.isUnit).map _).mul (isUnit_coord F))

/-- On polynomials, `scaleHom F c` sends `p(X)` to `p(c X)`. -/
theorem scaleHom_algebraMap (c : Fˣ) (p : F[X]) :
    scaleHom F c (algebraMap F[X] (Ring F) p) =
      algebraMap F[X] (Ring F) (eval₂ C (C (c : F) * X) p) :=
  IsLocalization.Away.lift_eq _ _ p

/-- The map `X ↦ c X` fixes constants. -/
theorem scaleHom_C (c : Fˣ) (a : F) :
    scaleHom F c (algebraMap F[X] (Ring F) (C a)) = algebraMap F[X] (Ring F) (C a) := by
  rw [scaleHom_algebraMap, eval₂_C]

/-- The map `X ↦ c X` sends the coordinate `X` to `c X`. -/
theorem scaleHom_coord (c : Fˣ) :
    scaleHom F c (coord F) = algebraMap F[X] (Ring F) (C (c : F)) * coord F := by
  rw [coord, scaleHom_algebraMap, eval₂_X, map_mul]

/-- Composing `X ↦ d X` with `X ↦ c X` gives `X ↦ (c d) X`. -/
theorem scaleHom_mul (c d : Fˣ) : (scaleHom F c).comp (scaleHom F d) = scaleHom F (c * d) := by
  refine ringHom_ext_ring F (fun a ↦ ?_) ?_
  · simp only [RingHom.comp_apply, scaleHom_C]
  · simp only [RingHom.comp_apply, scaleHom_coord, map_mul, scaleHom_C, Units.val_mul, C_mul]
    ring

/-- The map `X ↦ 1 X` is the identity. -/
theorem scaleHom_one : scaleHom F 1 = RingHom.id _ := by
  refine ringHom_ext_ring F (fun a ↦ ?_) ?_
  · simp only [scaleHom_C, RingHom.id_apply]
  · simp only [scaleHom_coord, Units.val_one, C_1, map_one, one_mul, RingHom.id_apply]

/-- The group homomorphism `Fˣ →* RingAut F[X]_X` sending `c` to the automorphism `X ↦ c X`. -/
def scaleAut : Fˣ →* RingAut (Ring F) where
  toFun c := RingEquiv.ofRingHom (scaleHom F c) (scaleHom F c⁻¹)
    (by rw [scaleHom_mul, mul_inv_cancel, scaleHom_one])
    (by rw [scaleHom_mul, inv_mul_cancel, scaleHom_one])
  map_one' := RingEquiv.ext fun z ↦ by
    change scaleHom F 1 z = z
    rw [scaleHom_one, RingHom.id_apply]
  map_mul' c d := RingEquiv.ext fun z ↦ by
    change scaleHom F (c * d) z = scaleHom F c (scaleHom F d z)
    rw [← scaleHom_mul, RingHom.comp_apply]

/-- The automorphism `scaleAut F c` acts as `scaleHom F c`. -/
theorem scaleAut_apply (c : Fˣ) (z : Ring F) : scaleAut F c z = scaleHom F c z := rfl

/-- The map of `F[X]_X` induced by a ring map of the coefficients. -/
def coeffHom (σ : F →+* F) : Ring F →+* Ring F :=
  IsLocalization.Away.lift (X : F[X]) (g := (algebraMap F[X] (Ring F)).comp (mapRingHom σ))
    (by
      rw [RingHom.comp_apply, coe_mapRingHom, map_X]
      exact isUnit_coord F)

/-- On polynomials, `coeffHom F σ` applies `σ` to the coefficients. -/
theorem coeffHom_algebraMap (σ : F →+* F) (p : F[X]) :
    coeffHom F σ (algebraMap F[X] (Ring F) p) = algebraMap F[X] (Ring F) (p.map σ) :=
  IsLocalization.Away.lift_eq _ _ p

/-- The map `coeffHom F σ` sends the constant `a` to `σ a`. -/
theorem coeffHom_C (σ : F →+* F) (a : F) :
    coeffHom F σ (algebraMap F[X] (Ring F) (C a)) = algebraMap F[X] (Ring F) (C (σ a)) := by
  rw [coeffHom_algebraMap, map_C]

/-- The map `coeffHom F σ` fixes the coordinate `X`. -/
theorem coeffHom_coord (σ : F →+* F) : coeffHom F σ (coord F) = coord F := by
  rw [coord, coeffHom_algebraMap, map_X]

/-- The map induced by `σ ∘ τ` is the composite of the maps induced by `σ` and `τ`. -/
theorem coeffHom_comp (σ τ : F →+* F) :
    (coeffHom F σ).comp (coeffHom F τ) = coeffHom F (σ.comp τ) := by
  refine ringHom_ext_ring F (fun a ↦ ?_) ?_
  · simp only [RingHom.comp_apply, coeffHom_C]
  · simp only [RingHom.comp_apply, coeffHom_coord]

/-- The identity of `F` induces the identity of `F[X]_X`. -/
theorem coeffHom_id : coeffHom F (RingHom.id F) = RingHom.id _ := by
  refine ringHom_ext_ring F (fun a ↦ ?_) ?_
  · simp only [coeffHom_C, RingHom.id_apply]
  · simp only [coeffHom_coord, RingHom.id_apply]

/-- The group homomorphism `RingAut F →* RingAut F[X]_X` sending `σ` to the automorphism
`∑ a_i X^i ↦ ∑ σ(a_i) X^i`. -/
def coeffAut : RingAut F →* RingAut (Ring F) where
  toFun σ := RingEquiv.ofRingHom (coeffHom F σ.toRingHom) (coeffHom F σ.symm.toRingHom)
    (by
      rw [coeffHom_comp, ← coeffHom_id]
      congr 1
      ext a
      simp)
    (by
      rw [coeffHom_comp, ← coeffHom_id]
      congr 1
      ext a
      simp)
  map_one' := RingEquiv.ext fun z ↦ by
    change coeffHom F (RingHom.id F) z = z
    rw [coeffHom_id, RingHom.id_apply]
  map_mul' σ τ := RingEquiv.ext fun z ↦ by
    change coeffHom F (σ.toRingHom.comp τ.toRingHom) z =
      coeffHom F σ.toRingHom (coeffHom F τ.toRingHom z)
    rw [← coeffHom_comp, RingHom.comp_apply]

/-- The automorphism `coeffAut F σ` acts as `coeffHom F σ`. -/
theorem coeffAut_apply (σ : RingAut F) (z : Ring F) : coeffAut F σ z = coeffHom F σ.toRingHom z :=
  rfl

/-- **The conjugation formula.** Conjugating `X ↦ c X` by the coefficient automorphism `σ` gives
`X ↦ σ(c) X`. -/
theorem coeffAut_mul_scaleAut_mul_inv (σ : RingAut F) (c : Fˣ) :
    coeffAut F σ * scaleAut F c * (coeffAut F σ)⁻¹ =
      scaleAut F (Units.map σ.toRingHom.toMonoidHom c) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine RingEquiv.ext fun z ↦ ?_
  show coeffHom F σ.toRingHom (scaleHom F c z) =
    scaleHom F (Units.map σ.toRingHom.toMonoidHom c) (coeffHom F σ.toRingHom z)
  have h : (coeffHom F σ.toRingHom).comp (scaleHom F c) =
      (scaleHom F (Units.map σ.toRingHom.toMonoidHom c)).comp (coeffHom F σ.toRingHom) := by
    refine ringHom_ext_ring F (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, scaleHom_C, coeffHom_C]
    · simp only [RingHom.comp_apply, scaleHom_coord, map_mul, coeffHom_C, coeffHom_coord,
        Units.coe_map, MonoidHom.coe_coe]
      rfl
  exact RingHom.congr_fun h z

end AlgebraicGeometry.TameMultiplicativeGroup

end
