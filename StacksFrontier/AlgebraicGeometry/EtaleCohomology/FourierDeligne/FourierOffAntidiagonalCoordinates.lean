module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTripleCoordinates
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The complement of the antidiagonal is an affine line over `{x + u ≠ 0}`

On `Q = 𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u` let `Q_U = {x + u ≠ 0}`, `W = Spec k[x, u]_{x+u}` and
`s = t(x + u) : Q ⟶ 𝔸¹`. The change of coordinates `t' = t(x + u)` is an isomorphism
`k[x, u]_{x+u}[t'] ≅ k[x, t, u]_{x+u}` (with inverse `t ↦ t'/(x + u)`), so the square

`Q_U --s--> 𝔸¹_k`
` |a         |`
` W  -----> Spec k`

is cartesian, `a = (x, u)`: `Q_U` is the affine line over `W` with coordinate `s`. Moreover the
coordinates `x` and `u` of `Q_U` factor through `a`.

## Main definitions

* `Stacks.EtaleCohomology.fourierOffAntidiagonalBase`: `W = Spec k[x, u]_{x+u}`.
* `Stacks.EtaleCohomology.fourierOffAntidiagonalProj`: `a : Q_U ⟶ W`.
* `Stacks.EtaleCohomology.fourierOffAntidiagonalBaseX`, `fourierOffAntidiagonalBaseU`:
  `x, u : W ⟶ 𝔸¹`.

## Main results

* `Stacks.EtaleCohomology.isPullback_fourierOffAntidiagonal`: the square above is cartesian.
* `Stacks.EtaleCohomology.fourierOffAntidiagonalι_comp_x`, `fourierOffAntidiagonalι_comp_u`: the
  coordinates `x` and `u` of `Q_U` factor through `a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open Stacks.Blowup Stacks.ArtinSchreier

variable (k : Type u) [Field k]

local notation "𝔸f" => affineLineStructureMap k

/-- `k[x, u]_{x + u}`. -/
local notation "AW" =>
  Localization.Away (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k)

/-- `k[x, t, u]_{x + u}`. -/
local notation "B3" =>
  Localization.Away (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) k)

/-- **The base `W = Spec k[x, u]_{x + u}`** of `Q_U`. -/
abbrev fourierOffAntidiagonalBase : Scheme.{u} := Spec (CommRingCat.of AW)

/-- The structure morphism `W ⟶ Spec k`. -/
abbrev fourierOffAntidiagonalBaseStructure :
    fourierOffAntidiagonalBase k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k AW))

/-- The coordinate `x : W ⟶ 𝔸¹`. -/
abbrev fourierOffAntidiagonalBaseX :
    fourierOffAntidiagonalBase k ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (algebraMap (MvPolynomial (Fin 2) k) AW
    (MvPolynomial.X 0))).toRingHom)

/-- The coordinate `u : W ⟶ 𝔸¹`. -/
abbrev fourierOffAntidiagonalBaseU :
    fourierOffAntidiagonalBase k ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (algebraMap (MvPolynomial (Fin 2) k) AW
    (MvPolynomial.X 1))).toRingHom)

/-- The image of `x + u` under `k[x, u] → k[x, t, u] → k[x, t, u]_{x+u}`, `x ↦ x`, `u ↦ u`, is a
unit. -/
theorem isUnit_algebraMap_rename_fourierBaseSum :
    IsUnit ((algebraMap (MvPolynomial (Fin 3) k) B3).comp
      (MvPolynomial.rename ![(0 : Fin 3), 2]).toRingHom (MvPolynomial.X 0 + MvPolynomial.X 1)) := by
  have h : (MvPolynomial.rename ![(0 : Fin 3), 2]).toRingHom
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 + MvPolynomial.X 2 := by
    simp [MvPolynomial.rename_X]
  rw [RingHom.comp_apply, h]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- **The ring map `k[x, u]_{x+u} → k[x, t, u]_{x+u}`**, `x ↦ x`, `u ↦ u`. -/
def fourierOffAntidiagonalBaseRingHom : AW →+* B3 :=
  IsLocalization.Away.lift (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
    (isUnit_algebraMap_rename_fourierBaseSum k)

/-- On polynomials, `fourierOffAntidiagonalBaseRingHom` is the renaming `x ↦ x`, `u ↦ u`. -/
theorem fourierOffAntidiagonalBaseRingHom_algebraMap (a : MvPolynomial (Fin 2) k) :
    fourierOffAntidiagonalBaseRingHom k (algebraMap _ AW a) =
      algebraMap _ B3 (MvPolynomial.rename ![(0 : Fin 3), 2] a) :=
  IsLocalization.Away.lift_eq _ _ a

/-- `fourierOffAntidiagonalBaseRingHom` is `k`-linear: it fixes the constants `c ∈ k`. -/
theorem fourierOffAntidiagonalBaseRingHom_algebraMap_k (c : k) :
    fourierOffAntidiagonalBaseRingHom k (algebraMap k AW c) = algebraMap k B3 c := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) AW,
    fourierOffAntidiagonalBaseRingHom_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.rename_C,
    ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- `x + u` is a unit of `k[x, u]_{x+u}`. -/
theorem isUnit_fourierBaseSum :
    IsUnit (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 0 + MvPolynomial.X 1)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- **The coordinate change `t' = t(x + u)`**: `k[x, u]_{x+u}[t'] → k[x, t, u]_{x+u}`. -/
def fourierCoordinateChange : Polynomial AW →+* B3 :=
  Polynomial.eval₂RingHom (fourierOffAntidiagonalBaseRingHom k)
    (algebraMap (MvPolynomial (Fin 3) k) B3
      (MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 2)))

/-- The inverse coordinate change on polynomials: `x ↦ x`, `t ↦ t'/(x + u)`, `u ↦ u`. -/
def fourierCoordinateChangeInvPoly : MvPolynomial (Fin 3) k →ₐ[k] Polynomial AW :=
  MvPolynomial.aeval ![Polynomial.C (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 0)),
    Polynomial.X * Polynomial.C (((isUnit_fourierBaseSum k).unit⁻¹ : AWˣ) : AW),
    Polynomial.C (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 1))]

/-- The image of `x + u` under `fourierCoordinateChangeInvPoly` is a unit of `k[x, u]_{x+u}[t']`.
-/
theorem isUnit_fourierCoordinateChangeInvPoly :
    IsUnit ((fourierCoordinateChangeInvPoly k).toRingHom
      (MvPolynomial.X 0 + MvPolynomial.X 2)) := by
  have h : (fourierCoordinateChangeInvPoly k).toRingHom (MvPolynomial.X 0 + MvPolynomial.X 2) =
      Polynomial.C (algebraMap (MvPolynomial (Fin 2) k) AW
        (MvPolynomial.X 0 + MvPolynomial.X 1)) := by
    simp [fourierCoordinateChangeInvPoly, map_add]
  rw [h]
  exact (isUnit_fourierBaseSum k).map _

/-- **The inverse coordinate change** `k[x, t, u]_{x+u} → k[x, u]_{x+u}[t']`. -/
def fourierCoordinateChangeInv : B3 →+* Polynomial AW :=
  IsLocalization.Away.lift (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) k)
    (isUnit_fourierCoordinateChangeInvPoly k)

/-- On polynomials, `fourierCoordinateChangeInv` agrees with `fourierCoordinateChangeInvPoly`. -/
theorem fourierCoordinateChangeInv_algebraMap (a : MvPolynomial (Fin 3) k) :
    fourierCoordinateChangeInv k (algebraMap _ B3 a) = fourierCoordinateChangeInvPoly k a :=
  IsLocalization.Away.lift_eq _ _ a

/-- On constants, `fourierCoordinateChange` is `fourierOffAntidiagonalBaseRingHom`. -/
theorem fourierCoordinateChange_C (a : AW) :
    fourierCoordinateChange k (Polynomial.C a) = fourierOffAntidiagonalBaseRingHom k a :=
  Polynomial.eval₂_C _ _

/-- `fourierCoordinateChange` sends the variable `t'` to `t(x + u)`. -/
theorem fourierCoordinateChange_X :
    fourierCoordinateChange k Polynomial.X =
      algebraMap (MvPolynomial (Fin 3) k) B3
        (MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 2)) :=
  Polynomial.eval₂_X _ _

/-- `fourierOffAntidiagonalBaseRingHom` sends `(x + u)⁻¹` to the inverse of `x + u` in
`k[x, t, u]_{x+u}`. -/
theorem fourierOffAntidiagonalBaseRingHom_inv :
    fourierOffAntidiagonalBaseRingHom k (((isUnit_fourierBaseSum k).unit⁻¹ : AWˣ) : AW) *
      algebraMap (MvPolynomial (Fin 3) k) B3 (MvPolynomial.X 0 + MvPolynomial.X 2) = 1 := by
  have h : algebraMap (MvPolynomial (Fin 3) k) B3 (MvPolynomial.X 0 + MvPolynomial.X 2) =
      fourierOffAntidiagonalBaseRingHom k
        (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 0 + MvPolynomial.X 1)) := by
    rw [fourierOffAntidiagonalBaseRingHom_algebraMap]
    simp [MvPolynomial.rename_X]
  rw [h, ← map_mul]
  show fourierOffAntidiagonalBaseRingHom k
    (((isUnit_fourierBaseSum k).unit⁻¹ * (isUnit_fourierBaseSum k).unit : AWˣ) : AW) = 1
  rw [inv_mul_cancel, Units.val_one, map_one]

/-- `fourierCoordinateChangeInvPoly` sends a constant `c ∈ k` to the constant polynomial `c`. -/
theorem fourierCoordinateChangeInvPoly_C (c : k) :
    fourierCoordinateChangeInvPoly k (MvPolynomial.C c) = Polynomial.C (algebraMap k AW c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply]

/-- The image in `k[x, u]_{x+u}` of the constant polynomial `c` is the scalar `c`. -/
theorem algebraMap_fourierBase_C (c : k) :
    algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.C c) = algebraMap k AW c := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- The image in `k[x, t, u]_{x+u}` of the constant polynomial `c` is the scalar `c`. -/
theorem algebraMap_fourierTriple_C (c : k) :
    algebraMap (MvPolynomial (Fin 3) k) B3 (MvPolynomial.C c) = algebraMap k B3 c := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- `fourierCoordinateChange ∘ fourierCoordinateChangeInv` is the identity of `k[x, t, u]_{x+u}`.
-/
theorem fourierCoordinateChange_comp_inv :
    (fourierCoordinateChange k).comp (fourierCoordinateChangeInv k) = RingHom.id B3 := by
  refine IsLocalization.ringHom_ext (Submonoid.powers
    (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) k)) ?_
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply,
      fourierCoordinateChangeInv_algebraMap, fourierCoordinateChangeInvPoly_C,
      fourierCoordinateChange_C, fourierOffAntidiagonalBaseRingHom_algebraMap_k,
      algebraMap_fourierTriple_C]
  · simp only [RingHom.comp_apply, RingHom.id_apply, fourierCoordinateChangeInv_algebraMap,
      fourierCoordinateChangeInvPoly, MvPolynomial.aeval_X]
    fin_cases i
    · simp [fourierCoordinateChange_C, fourierOffAntidiagonalBaseRingHom_algebraMap,
        MvPolynomial.rename_X]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul,
        fourierCoordinateChange_X, fourierCoordinateChange_C]
      rw [mul_assoc, mul_comm (algebraMap (MvPolynomial (Fin 3) k) B3
        (MvPolynomial.X 0 + MvPolynomial.X 2)), fourierOffAntidiagonalBaseRingHom_inv, mul_one]
    · simp [fourierCoordinateChange_C, fourierOffAntidiagonalBaseRingHom_algebraMap,
        MvPolynomial.rename_X]

/-- `fourierCoordinateChangeInv ∘ fourierOffAntidiagonalBaseRingHom` is the inclusion of constants
`Polynomial.C : k[x, u]_{x+u} → k[x, u]_{x+u}[t']`. -/
theorem fourierCoordinateChangeInv_comp_baseRingHom :
    (fourierCoordinateChangeInv k).comp (fourierOffAntidiagonalBaseRingHom k) = Polynomial.C := by
  refine IsLocalization.ringHom_ext (Submonoid.powers
    (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) k)) ?_
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      fourierOffAntidiagonalBaseRingHom_algebraMap, MvPolynomial.rename_C,
      fourierCoordinateChangeInv_algebraMap, fourierCoordinateChangeInvPoly_C,
      algebraMap_fourierBase_C]
  · simp only [RingHom.comp_apply, fourierOffAntidiagonalBaseRingHom_algebraMap,
      fourierCoordinateChangeInv_algebraMap, MvPolynomial.rename_X, fourierCoordinateChangeInvPoly,
      MvPolynomial.aeval_X]
    fin_cases i <;> rfl

/-- `fourierCoordinateChangeInv ∘ fourierCoordinateChange` is the identity of `k[x, u]_{x+u}[t']`.
-/
theorem fourierCoordinateChangeInv_comp :
    (fourierCoordinateChangeInv k).comp (fourierCoordinateChange k) = RingHom.id _ := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, fourierCoordinateChange_C, ← RingHom.comp_apply,
      fourierCoordinateChangeInv_comp_baseRingHom, RingHom.id_apply]
  · rw [RingHom.comp_apply, fourierCoordinateChange_X, fourierCoordinateChangeInv_algebraMap,
      RingHom.id_apply]
    simp only [fourierCoordinateChangeInvPoly, map_mul, map_add, MvPolynomial.aeval_X]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    have hsum : Polynomial.C (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 0)) +
        Polynomial.C (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 1)) =
        Polynomial.C (algebraMap (MvPolynomial (Fin 2) k) AW
          (MvPolynomial.X 0 + MvPolynomial.X 1)) := by
      simp only [map_add]
    have h1 : (((isUnit_fourierBaseSum k).unit⁻¹ : AWˣ) : AW) *
        algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X 0 + MvPolynomial.X 1) = 1 :=
      (isUnit_fourierBaseSum k).val_inv_mul
    rw [hsum, mul_assoc, ← Polynomial.C_mul]
    simp

/-- **The coordinate change as a ring isomorphism** `k[x, u]_{x+u}[t'] ≃ k[x, t, u]_{x+u}`. -/
def fourierCoordinateChangeEquiv : Polynomial AW ≃+* B3 :=
  RingEquiv.ofRingHom (fourierCoordinateChange k) (fourierCoordinateChangeInv k)
    (fourierCoordinateChange_comp_inv k) (fourierCoordinateChangeInv_comp k)

/-- The kernel ring map `k[X] → k[x, t, u]_{x+u}`, `X ↦ t(x + u)`. -/
abbrev fourierOffAntidiagonalKernelRingHom : Polynomial k →+* B3 :=
  (algebraMap (MvPolynomial (Fin 3) k) B3).comp (fourierTripleSum k).toRingHom

/-- Restricted to `k[X] ⊆ k[x, u]_{x+u}[X]`, `fourierCoordinateChange` is
`fourierOffAntidiagonalKernelRingHom`, `X ↦ t(x + u)`. -/
theorem fourierCoordinateChange_comp_algebraMap_polynomial :
    (fourierCoordinateChange k).comp (algebraMap (Polynomial k) (Polynomial AW)) =
      fourierOffAntidiagonalKernelRingHom k := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.algebraMap_def,
      Polynomial.coe_mapRingHom, Polynomial.map_C, fourierCoordinateChange_C,
      fourierOffAntidiagonalBaseRingHom_algebraMap_k]
    show _ = algebraMap (MvPolynomial (Fin 3) k) B3 (Polynomial.aeval _ (Polynomial.C c))
    rw [Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
  · simp only [RingHom.comp_apply, Polynomial.algebraMap_def, Polynomial.coe_mapRingHom,
      Polynomial.map_X, fourierCoordinateChange_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X]

/-- **The Artin–Schreier kernel square over `W` is a pushout of rings**: `k[x, t, u]_{x+u}` is
`k[x, u]_{x+u} ⊗_k k[X]` with `X ↦ t(x + u)`. -/
theorem isPushout_fourierOffAntidiagonal :
    IsPushout (CommRingCat.ofHom (algebraMap k AW))
      (CommRingCat.ofHom (algebraMap k (Polynomial k)))
      (CommRingCat.ofHom (fourierOffAntidiagonalBaseRingHom k))
      (CommRingCat.ofHom (fourierOffAntidiagonalKernelRingHom k)) := by
  have h₀ := CommRingCat.isPushout_of_isPushout k AW (Polynomial k) (Polynomial AW)
  refine h₀.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fourierCoordinateChangeEquiv k).toCommRingCatIso (by simp) (by simp) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact fourierCoordinateChange_C k a
  · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    exact RingHom.congr_fun (fourierCoordinateChange_comp_algebraMap_polynomial k) c

/-- **The projection `a = (x, u) : Q_U ⟶ W`.** -/
def fourierOffAntidiagonalProj : fourierOffAntidiagonal k ⟶ fourierOffAntidiagonalBase k :=
  pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (fourierOffAntidiagonalBaseRingHom k))

/-- The morphism `s = t(x + u) : Q_U ⟶ 𝔸¹` is induced by `fourierOffAntidiagonalKernelRingHom`. -/
theorem fourierOffAntidiagonalι_comp_fourierTripleKernelMap :
    fourierOffAntidiagonalι k ≫ fourierTripleKernelMap k =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (fourierOffAntidiagonalKernelRingHom k)) := by
  rw [fourierTripleKernelMap, ← Category.assoc, pullback.condition, Category.assoc,
    ← Spec.map_comp]
  rfl

/-- **`Q_U` is the affine line over `W` with coordinate `s = t(x + u)`**: the square
`Q_U --s--> 𝔸¹`, `Q_U --a--> W`, `W ⟶ Spec k`, `𝔸¹ ⟶ Spec k` is cartesian. -/
theorem isPullback_fourierOffAntidiagonal :
    IsPullback (fourierOffAntidiagonalι k ≫ fourierTripleKernelMap k)
      (fourierOffAntidiagonalProj k) 𝔸f (fourierOffAntidiagonalBaseStructure k) := by
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_fourierOffAntidiagonal k)).flip
  rw [fourierOffAntidiagonalι_comp_fourierTripleKernelMap]
  exact h.of_iso (asIso (pullback.snd (fourierTripleCoords k) _)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp [fourierOffAntidiagonalProj]) (by simp) (by simp)

/-- For `i = ![0, 2] i'`, the `i`-th coordinate of `Q_U` is the composite of
`fourierOffAntidiagonalProj` with the `i'`-th coordinate of `W`. -/
theorem fourierOffAntidiagonal_coordinate_eq (i : Fin 3) (i' : Fin 2) (hi : ![0, 2] i' = i) :
    fourierOffAntidiagonalι k ≫ fourierTripleCoords k ≫ affineSpaceCoordinate k i =
      fourierOffAntidiagonalProj k ≫ Spec.map (CommRingCat.ofHom (Polynomial.aeval
        (algebraMap (MvPolynomial (Fin 2) k) AW (MvPolynomial.X i'))).toRingHom) := by
  rw [← Category.assoc, pullback.condition, Category.assoc, fourierOffAntidiagonalProj,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_)
  · show algebraMap (MvPolynomial (Fin 3) k) B3
        (Polynomial.aeval (MvPolynomial.X i) (Polynomial.C c)) =
      fourierOffAntidiagonalBaseRingHom k (Polynomial.aeval (algebraMap (MvPolynomial (Fin 2) k) AW
        (MvPolynomial.X i')) (Polynomial.C c))
    rw [Polynomial.aeval_C, Polynomial.aeval_C, fourierOffAntidiagonalBaseRingHom_algebraMap_k,
      ← IsScalarTower.algebraMap_apply]
  · show algebraMap (MvPolynomial (Fin 3) k) B3
        (Polynomial.aeval (MvPolynomial.X i) Polynomial.X) =
      fourierOffAntidiagonalBaseRingHom k (Polynomial.aeval (algebraMap (MvPolynomial (Fin 2) k) AW
        (MvPolynomial.X i')) Polynomial.X)
    rw [Polynomial.aeval_X, Polynomial.aeval_X, fourierOffAntidiagonalBaseRingHom_algebraMap,
      MvPolynomial.rename_X, hi]

/-- **The coordinate `x` of `Q_U` factors through `a`.** -/
theorem fourierOffAntidiagonalι_comp_x :
    fourierOffAntidiagonalι k ≫ (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) =
      fourierOffAntidiagonalProj k ≫ fourierOffAntidiagonalBaseX k := by
  have h := fourierTripleCoords_comp_affineSpaceCoordinate k 0
  simp only [Matrix.cons_val_zero] at h
  rw [← h]
  exact fourierOffAntidiagonal_coordinate_eq k 0 0 rfl

/-- **The coordinate `u` of `Q_U` factors through `a`.** -/
theorem fourierOffAntidiagonalι_comp_u :
    fourierOffAntidiagonalι k ≫ (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _) =
      fourierOffAntidiagonalProj k ≫ fourierOffAntidiagonalBaseU k := by
  have h := fourierTripleCoords_comp_affineSpaceCoordinate k 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  rw [← h]
  exact fourierOffAntidiagonal_coordinate_eq k 2 1 rfl

end Stacks.EtaleCohomology

end
