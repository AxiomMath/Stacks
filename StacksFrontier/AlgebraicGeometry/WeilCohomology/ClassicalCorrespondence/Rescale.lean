module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheoryPairing

/-!
# Rescaling a classical Weil cohomology theory

Let `c ∈ Fˣ`. Replacing the cycle class maps `γ : CHʳ(X) → H^{2r}(X)` by `c⁻ʳ γ` and the trace
maps `∫_X : H^{2d}(X) → F` by `c^d ∫_X` turns data `(D1)`, `(D2)`, `(D3)` satisfying all of `(A)`,
`(B)`, `(C)` except possibly `(A)(c)`, `(A)(d)` into data of the same kind: the trace pairings are
scaled by the unit `c^d`, so stay perfect, the pushforward of the pairings is scaled by
`c^{dim X - dim Y}`, and every axiom is homogeneous in these scalings.

This is the change of coordinate of the Tate line `F(1)` in the proof of Stacks 0FH3: a realization
`G` of Chow motives with a basis `e₁` of `G^{-2}(𝟏(1))` gives `γ(α) = G(a_α)(e_{-r})` and
`∫_X x = G([X])(x ⊗ e_d)`, and replacing `e₁` by `c e₁` rescales `γ` and `∫` as above.

## Main definitions

* `Stacks.WeilCohomology.PoincarePairingSetup.rescale`: the trace maps scaled by `c^d`.
* `Stacks.WeilCohomology.PreClassicalWeilCohomologyTheory.rescale`: also the cycle class maps
  scaled by `c⁻ʳ`.

## Main results

* `Stacks.WeilCohomology.PoincarePairingSetup.pushforward_rescale`: the pushforward of the
  rescaled pairings is `c^{dim X - dim Y} f_*`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w t

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

namespace PoincarePairingSetup

variable (S : PoincarePairingSetup.{u, v, w} k F) (c : Fˣ)

/-- The trace pairing of a scaled trace map is the scaled trace pairing. -/
theorem tracePairing_smul (A : ExternallyGradedAlgebra.{v, w} F) (d : ℕ)
    (integration : A.piece (2 * (d : ℤ)) →ₗ[F] F) (a : F) (i : ℤ) :
    A.tracePairing d (a • integration) i = a • A.tracePairing d integration i := by
  ext x y
  simp [ExternallyGradedAlgebra.tracePairing]

/-- **The pairing setup with trace maps scaled by `c^d`**: `∫'_X = c^{dim X} ∫_X`. -/
def rescale : PoincarePairingSetup.{u, v, w} k F where
  H := S.H
  gradedComm := S.gradedComm
  dimension := S.dimension
  dimension_eq := S.dimension_eq
  pullback := S.pullback
  pullback_id := S.pullback_id
  pullback_comp := S.pullback_comp
  pullback_one := S.pullback_one
  pullback_mul := S.pullback_mul
  integration X := ((c ^ (S.dimension X : ℤ) : Fˣ) : F) • S.integration X
  finite := S.finite
  perfect X i := by
    rw [tracePairing_smul]
    have := S.perfect X i
    have h : ((c ^ (S.dimension X : ℤ) : Fˣ) : F) • (S.H X).tracePairing (S.dimension X)
        (S.integration X) i = ((S.H X).tracePairing (S.dimension X) (S.integration X) i).compl₁₂
          (LinearEquiv.smulOfUnit (c ^ (S.dimension X : ℤ))).toLinearMap
          (LinearEquiv.refl F _).toLinearMap := by
      ext x y
      simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.refl_apply]
      change _ = ((S.H X).tracePairing (S.dimension X) (S.integration X) i)
        ((c ^ (S.dimension X : ℤ)) • x) y
      rw [Units.smul_def, map_smul, LinearMap.smul_apply]
    rw [h]
    exact LinearMap.IsPerfPair.compl₁₂ _ _ _

@[simp]
theorem rescale_H : (S.rescale c).H = S.H :=
  rfl

@[simp]
theorem rescale_dimension : (S.rescale c).dimension = S.dimension :=
  rfl

@[simp]
theorem rescale_pullback {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (i : ℤ) :
    (S.rescale c).pullback f i = S.pullback f i :=
  rfl

theorem rescale_integration (X : (SmoothProjective k).FullSubcategory) :
    (S.rescale c).integration X = ((c ^ (S.dimension X : ℤ) : Fˣ) : F) • S.integration X :=
  rfl

/-- **The pushforward of the rescaled pairings** is `c^{dim X - dim Y} f_*`. -/
theorem pushforward_rescale {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (i : ℤ) :
    (S.rescale c).pushforward f i =
      ((c ^ ((S.dimension X : ℤ) - S.dimension Y) : Fˣ) : F) • S.pushforward f i := by
  have key : ∀ (b : (S.H Y).piece i) (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)),
      ((S.H X).tracePairing (S.dimension X)
        (((c ^ (S.dimension X : ℤ) : Fˣ) : F) • S.integration X) i) (S.pullback f i b) a =
      ((S.H Y).tracePairing (S.dimension Y)
        (((c ^ (S.dimension Y : ℤ) : Fˣ) : F) • S.integration Y) i) b
        (((c ^ ((S.dimension X : ℤ) - S.dimension Y) : Fˣ) : F) • S.pushforward f i a) := by
    intro b a
    rw [tracePairing_smul, tracePairing_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      S.integration_pullback_mul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      smul_smul, ← Units.val_mul, ← zpow_add]
    congr 3
    ring
  exact (((S.rescale c).eq_pushforward_iff f i
    (((c ^ ((S.dimension X : ℤ) - S.dimension Y) : Fˣ) : F) • S.pushforward f i)).2 key).symm

theorem pushforward_rescale_apply {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)
    (i : ℤ) (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)) :
    (S.rescale c).pushforward f i a =
      ((c ^ ((S.dimension X : ℤ) - S.dimension Y) : Fˣ) : F) • S.pushforward f i a := by
  rw [pushforward_rescale]
  rfl

end PoincarePairingSetup

namespace PreClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, t} k}
  (T : PreClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch) (c : Fˣ)

/-- Compatibility of the rescaled cycle class maps with the pushforward of the rescaled
pairings. -/
theorem rescale_cycleClass_pushforward {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)
    (r : ℤ) (α : Ch.group X r) :
    (T.toPoincarePairingSetup.rescale c).pushforward f (2 * (T.dimension X : ℤ) - 2 * r)
        (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
          (show 2 * r = 2 * (T.dimension X : ℤ) - (2 * (T.dimension X : ℤ) - 2 * r) by ring)
          (((c ^ (-r) : Fˣ) : F) • T.cycleClass X r α)) =
      ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
        (show 2 * (r + (T.dimension Y : ℤ) - (T.dimension X : ℤ)) =
            2 * (T.dimension Y : ℤ) - (2 * (T.dimension X : ℤ) - 2 * r) by ring)
        (((c ^ (-(r + (T.dimension Y : ℤ) - T.dimension X)) : Fˣ) : F) •
          T.cycleClass Y (r + (T.dimension Y : ℤ) - (T.dimension X : ℤ))
            (Ch.pushforward f (T.dimension X) (T.dimension Y) (T.dimension_eq X)
              (T.dimension_eq Y) r α)) := by
  rw [PoincarePairingSetup.pushforward_rescale_apply, map_smul, map_smul,
    T.cycleClass_pushforward f r α, map_smul, smul_smul, ← Units.val_mul, ← zpow_add]
  congr 3
  ring

/-- Compatibility of the rescaled cycle class maps with the intersection product. -/
theorem rescale_cycleClass_mul (X : (SmoothProjective k).FullSubcategory) (r s : ℤ)
    (α : Ch.group X r) (β : Ch.group X s) :
    ((c ^ (-(r + s)) : Fˣ) : F) • T.cycleClass X (r + s) (Ch.mul r s α β) =
      (T.H X).evenCup r s (((c ^ (-r) : Fˣ) : F) • T.cycleClass X r α)
        (((c ^ (-s) : Fˣ) : F) • T.cycleClass X s β) := by
  rw [T.cycleClass_mul, LinearMap.map_smul₂, map_smul, smul_smul, ← Units.val_mul, ← zpow_add,
    neg_add]

/-- The rescaled trace of the rescaled class of a point is `1`. -/
theorem rescale_integration_cycleClass_fundamental (X : (SmoothProjective k).FullSubcategory)
    (hX : IsIso X.obj.hom) (h0 : T.dimension X = 0) :
    (((c ^ (T.dimension X : ℤ) : Fˣ) : F) • T.integration X)
      (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
        (show 2 * (0 : ℤ) = 2 * (T.dimension X : ℤ) by omega)
        (((c ^ (-(0 : ℤ)) : Fˣ) : F) • T.cycleClass X 0 (Ch.fundamental X))) = 1 := by
  rw [LinearMap.smul_apply, map_smul, map_smul, T.integration_cycleClass_fundamental X hX h0, h0]
  simp

/-- The rescaled cycle class maps are compatible with the Gysin pullback. -/
theorem rescale_cycleClass_gysin {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y)
    (r : ℤ) (β : Ch.group Y r) :
    ((c ^ (-r) : Fˣ) : F) • T.cycleClass X r (Ch.gysin f r β) =
      T.pullback f (2 * r) (((c ^ (-r) : Fˣ) : F) • T.cycleClass Y r β) := by
  rw [T.cycleClass_gysin, map_smul]

/-- **The rescaled theory**: cycle class maps `c⁻ʳ γ` and trace maps `c^d ∫_X`. -/
def rescale : PreClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch where
  toPoincarePairingSetup := T.toPoincarePairingSetup.rescale c
  cycleClass X r := ((c ^ (-r) : Fˣ) : F) • T.cycleClass X r
  kunneth := T.kunneth
  cycleClass_gysin f r β := T.rescale_cycleClass_gysin c f r β
  cycleClass_pushforward f r α := T.rescale_cycleClass_pushforward c f r α
  cycleClass_mul X r s α β := T.rescale_cycleClass_mul c X r s α β
  integration_cycleClass_fundamental X hX h0 :=
    T.rescale_integration_cycleClass_fundamental c X hX h0

@[simp]
theorem rescale_toPoincarePairingSetup :
    (T.rescale c).toPoincarePairingSetup = T.toPoincarePairingSetup.rescale c :=
  rfl

theorem rescale_cycleClass (X : (SmoothProjective k).FullSubcategory) (r : ℤ) :
    (T.rescale c).cycleClass X r = ((c ^ (-r) : Fˣ) : F) • T.cycleClass X r :=
  rfl

end PreClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
