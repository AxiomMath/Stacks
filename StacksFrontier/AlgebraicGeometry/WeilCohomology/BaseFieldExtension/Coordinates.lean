module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Pullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup

/-!
# The comparison of first twists in coordinates

In the canonical coordinates `κ` on the twists of `H^*` and `(H')^*`, the comparison
`H^*(X)(1) → (H')^*(X_{k'})(1)` is the comparison `H^*(X) → (H')^*(X_{k'})` times a fixed nonzero
scalar `u ∈ F'`, which records the two coordinates on `F(1)` and `F'(1)`.

## Main definitions

* `FieldExtensionComparison.tateUnit`: The scalar `u ∈ F'` comparing the coordinates of `F(1)`
  and `F'(1)`.

## Main results

* `FieldExtensionComparison.tateUnit_ne_zero`: The scalar `u` is nonzero.
* `FieldExtensionComparison.κ_twistOne`: In coordinates, the comparison of first twists is `u`
  times the comparison of the untwisted cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

section Line

variable {F : Type*} [Field F] {L : Type*} [AddCommGroup L] [Module F L]

/-- The coordinate of the first tensor power is the coordinate of the line. -/
theorem tateLineCoordinates_one (c : L ≃ₗ[F] F) (t : tateLine F L 1) :
    tateLineCoordinates c 1 t =
      c (PiTensorProduct.subsingletonEquiv (R := F) (s := fun _ : Fin 1 => L) 0 t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a f =>
    show tensorPowerCoordinates c 1 _ = _
    simp [tensorPowerCoordinates, PiTensorProduct.constantBaseRingEquiv_tprod,
      PiTensorProduct.subsingletonEquiv_apply_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

end Line

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- The scalar comparing the coordinates of `F(1)` and `F'(1)` through `F(1) ⊗_F F' ≅ F'(1)`. -/
def tateUnit : F' := 𝔇'.coord (Φ.tateEquiv (1 ⊗ₜ 𝔇.coord.symm 1))

/-- The scalar comparing the coordinates of `F(1)` and `F'(1)` is nonzero. -/
theorem tateUnit_ne_zero : Φ.tateUnit ≠ 0 := by
  intro h
  have h1 : Φ.tateEquiv (1 ⊗ₜ 𝔇.coord.symm 1) = 0 :=
    𝔇'.coord.injective (by rw [map_zero]; exact h)
  have h2 : (1 : F') ⊗ₜ[F] 𝔇.coord.symm 1 = 0 :=
    Φ.tateEquiv.injective (by rw [map_zero]; exact h1)
  have h3 := injective_one_tmul (F := F) (V := 𝔇.tate) F' (h2.trans (tmul_zero _ _).symm)
  exact one_ne_zero (𝔇.coord.symm.injective (h3.trans (map_zero _).symm))

/-- The comparison `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` sends `1 ⊗ (c • v)` to the image of `c`
in `F'` times the image of `1 ⊗ v`. -/
theorem iso_one_tmul_smul (X : (SmoothProjectiveScheme k).FullSubcategory) (c : F)
    (v : 𝔇.H X) : Φ.iso X (1 ⊗ₜ (c • v)) = algebraMap F F' c • Φ.iso X (1 ⊗ₜ v) := by
  rw [TensorProduct.tmul_smul, ← map_smul, algebraMap_smul]

/-- **The comparison of first twists in coordinates**: `κ'(θ(x)) = u • ψ(κ(x))`. -/
theorem κ_twistOne (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    𝔇'.κ _ 1 (Φ.twistOne X x) = Φ.tateUnit • Φ.iso X (1 ⊗ₜ 𝔇.κ X 1 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [twistOne]
  | tmul v t =>
    simp only [twistOne]
    rw [twistOneBaseChange_tmul]
    simp only [FirstChernClassData.κ]
    rw [tateTwistCoordinates_tmul 𝔇'.coord 1 _
        (tensorPowerOneBaseChange Φ.tateEquiv (1 ⊗ₜ[F] (t : TensorPower F 1 𝔇.tate))),
      tateTwistCoordinates_tmul 𝔇.coord 1 v t, tateLineCoordinates_one, tateLineCoordinates_one]
    set l := PiTensorProduct.subsingletonEquiv (R := F) (s := fun _ : Fin 1 => 𝔇.tate) 0 t
    have hl : l = 𝔇.coord l • 𝔇.coord.symm 1 := by
      apply 𝔇.coord.injective; simp
    have hT : PiTensorProduct.subsingletonEquiv (R := F') (s := fun _ : Fin 1 => 𝔇'.tate) 0
        (tensorPowerOneBaseChange Φ.tateEquiv (1 ⊗ₜ[F] (t : TensorPower F 1 𝔇.tate))) =
        Φ.tateEquiv (1 ⊗ₜ l) := by
      simp [tensorPowerOneBaseChange, l]
    have hτ : Φ.tateEquiv (1 ⊗ₜ l) =
        algebraMap F F' (𝔇.coord l) • Φ.tateEquiv (1 ⊗ₜ 𝔇.coord.symm 1) := by
      conv_lhs => rw [hl]
      rw [TensorProduct.tmul_smul, ← algebraMap_smul F' (𝔇.coord l), map_smul]
    rw [hT, hτ, map_smul, smul_eq_mul, iso_one_tmul_smul, ← mul_smul, mul_comm]
    rfl
  | add x y hx hy =>
    simp only [twistOne, map_add, TensorProduct.tmul_add] at hx hy ⊢
    rw [hx, hy, smul_add]

end FieldExtensionComparison

end Stacks.WeilCohomology
