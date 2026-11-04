module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
public import StacksCore.Tactic.StacksAttribute

/-!
# The split equalizer of a descent datum for modules

Let `R → S` be a ring map, write `S₂ = S ⊗_R S`, `S₃ = S ⊗_R S ⊗_R S`, and let `(M, θ)` be a
descent datum, with `θ : M ⊗_{S, δ₀¹} S₂ → M ⊗_{S, δ₁¹} S₂`. The diagram
```
      θ ∘ (1 ⊗ δ₀¹)                    (θ ⊗ δ₂²) ∘ (1 ⊗ δ₀²)
  M ---------------> M ⊗_{S, δ₁¹} S₂ ========================> M ⊗_{S, δ₁₂¹} S₃
                                            1 ⊗ δ₁²
```
is a split equalizer, the auxiliary maps being `1 ⊗ σ₀⁰` and `1 ⊗ σ₀¹`. The first of the
identities of a split equalizer is the cocycle condition tensored with `σ₁¹`, the others are
immediate.

## Main definitions

* `ModuleCat.DescentData.inverseTransition` is the descent datum `θ` of the source.
* `ModuleCat.DescentData.inverseTransitionUnit` is the arrow `θ ∘ (1 ⊗ δ₀¹)`.
* `ModuleCat.DescentData.inverseTransition01AfterUnit` and
  `ModuleCat.DescentData.middleUnitInsertion` are the parallel arrows
  `(θ ⊗ δ₂²) ∘ (1 ⊗ δ₀²)` and `1 ⊗ δ₁²`.
* `ModuleCat.DescentData.actionRetraction` and `ModuleCat.DescentData.multiplyLastSection` are
  the auxiliary maps `1 ⊗ σ₀⁰` and `1 ⊗ σ₀¹`.
* `ModuleCat.DescentData.lastFactorObj` is `X ⊗[R] A` as an `A`-module through the last factor;
  `ModuleCat.DescentData.inverseTransitionUnitHom` and its siblings are the five arrows above
  as morphisms of `A`-modules.
* `ModuleCat.DescentData.inverseTransitionUnitSplitEqualizer` is the split equalizer structure.

## Main results

* `ModuleCat.DescentData.isSplitEqualizer_inverseTransitionUnitHom`: the diagram is a split
  equalizer of `S`-modules.

## Implementation notes

A descent datum is a `ModuleCat.DescentData`, whose transition is
`φ : N ⊗[R] A ≃ A ⊗[R] N`, the isomorphism of Definition 023G. We use the identifications
recorded in that file: `M ⊗_{S, δ₁¹} S₂ = N ⊗[R] A`, where `M` is merged into the first tensor
factor, `M ⊗_{S, δ₀¹} S₂ = A ⊗[R] N`, and `M ⊗_{S, δ₁₂¹} S₃ = (N ⊗[R] A) ⊗[R] A`. The source's
`θ` is the inverse of `φ` (footnote in Subsection 08WW); it is `inverseTransition`.
Under these identifications

* `1 ⊗ δ₀¹ : M → M ⊗_{S, δ₀¹} S₂` is `n ↦ 1 ⊗ n`;
* `1 ⊗ δ₀² : M ⊗_{S, δ₁¹} S₂ → M ⊗_{S, δ₀₂¹} S₃ = (A ⊗[R] N) ⊗[R] A` is `n ⊗ b ↦ (1 ⊗ n) ⊗ b`;
* `θ ⊗ δ₂²` is `θ ⊗ id_A`, the inverse of the map `transition01` of the cocycle condition;
* `1 ⊗ δ₁²` is `n ⊗ b ↦ (n ⊗ 1) ⊗ b`;
* `1 ⊗ σ₀⁰` is `n ⊗ b ↦ b • n` and `1 ⊗ σ₀¹` is `(n ⊗ a) ⊗ b ↦ n ⊗ ab`.

All five arrows are linear for the action of `S` on `M ⊗_{S, δ₁¹} S₂` through
`δ₀¹ : S → S₂` and on `M ⊗_{S, δ₁₂¹} S₃` through `δ₀₁¹ = δ₀² ∘ δ₀¹ = δ₁² ∘ δ₀¹ : S → S₃`, that is
through the last tensor factor, so the diagram is a split equalizer of `S`-modules (and hence,
applying the forgetful functor, of `R`-modules). Its first object is universe-lifted so that it
lives in the same universe as the tensor products.

The cocycle condition is used in the form `φ₁₂ ∘ φ₀₁ = φ₀₂` of the structure: the equalizing
identity is the cocycle condition at `θ(1 ⊗ n)` with a unit inserted, and the retraction
identity `(1 ⊗ σ₀⁰) ∘ θ ∘ (1 ⊗ δ₀¹) = 1` is the cocycle condition multiplied out in the last two
factors (the source's "tensoring with `σ₁¹`"), which says that the endomorphism
`n ↦ (1 ⊗ σ₀⁰)(φ(n ⊗ 1))` of `M` becomes the identity after the faithful base change along the
surjection `φ`.

## References

* [Stacks Project, Tag 08WZ](https://stacks.math.columbia.edu/tag/08WZ)
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat.DescentData

open CategoryTheory TensorProduct

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The descent datum `θ : M ⊗_{S, δ₀¹} S₂ → M ⊗_{S, δ₁¹} S₂` of Subsection 08WW, the inverse
of the transition isomorphism, as an `R`-linear isomorphism. -/
abbrev inverseTransition (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) ≃ₗ[R] (restrictModule R A D.module ⊗[R] A) :=
  (D.transitionRestrictScalars R A).symm

/-- The arrow `θ ∘ (1_M ⊗ δ₀¹) : M → M ⊗_{S, δ₁¹} S₂`, that is `n ↦ θ (1 ⊗ n)`. -/
def inverseTransitionUnit (D : DescentData.{u, v, w} R A) :
    restrictModule R A D.module →ₗ[R] restrictModule R A D.module ⊗[R] A :=
  (inverseTransition R A D).toLinearMap ∘ₗ TensorProduct.mk R A (restrictModule R A D.module) 1

/-- The arrow `(θ ⊗ δ₂²) ∘ (1_M ⊗ δ₀²) : M ⊗_{S, δ₁¹} S₂ → M ⊗_{S, δ₁₂¹} S₃`, that is
`n ⊗ b ↦ θ (1 ⊗ n) ⊗ b`. -/
def inverseTransition01AfterUnit (D : DescentData.{u, v, w} R A) :
    restrictModule R A D.module ⊗[R] A →ₗ[R] (restrictModule R A D.module ⊗[R] A) ⊗[R] A :=
  (inverseTransition R A D).toLinearMap.rTensor A ∘ₗ
    (TensorProduct.assoc R A (restrictModule R A D.module) A).symm.toLinearMap ∘ₗ
      TensorProduct.mk R A (restrictModule R A D.module ⊗[R] A) 1

/-- The arrow `1_{M ⊗ S₂} ⊗ δ₁² : M ⊗_{S, δ₁¹} S₂ → M ⊗_{S, δ₁₂¹} S₃`, that is
`n ⊗ b ↦ (n ⊗ 1) ⊗ b`. -/
def middleUnitInsertion (D : DescentData.{u, v, w} R A) :
    restrictModule R A D.module ⊗[R] A →ₗ[R] (restrictModule R A D.module ⊗[R] A) ⊗[R] A :=
  ((TensorProduct.mk R (restrictModule R A D.module) A).flip 1).rTensor A

/-- The auxiliary map `1_M ⊗ σ₀⁰ : M ⊗_{S, δ₁¹} S₂ → M`, that is `n ⊗ b ↦ b • n`. -/
def actionRetraction (D : DescentData.{u, v, w} R A) :
    restrictModule R A D.module ⊗[R] A →ₗ[R] restrictModule R A D.module :=
  TensorProduct.lift (restrictedScalarAction R A D.module).toLinearMap.flip

/-- The auxiliary map `1_M ⊗ σ₀¹ : M ⊗_{S, δ₁₂¹} S₃ → M ⊗_{S, δ₁¹} S₂`, that is
`(n ⊗ a) ⊗ b ↦ n ⊗ ab`. -/
def multiplyLastSection (D : DescentData.{u, v, w} R A) :
    (restrictModule R A D.module ⊗[R] A) ⊗[R] A →ₗ[R] restrictModule R A D.module ⊗[R] A :=
  (LinearMap.mul' R A).lTensor _ ∘ₗ
    (TensorProduct.assoc R (restrictModule R A D.module) A A).toLinearMap

variable {R A}

section Lemmas

variable (D : DescentData.{u, v, w} R A)

/-- The multiplication map `A ⊗[R] N → N`, `c ⊗ m ↦ c • m`. -/
private def targetAction : A ⊗[R] restrictModule R A D.module →ₗ[R] restrictModule R A D.module :=
  TensorProduct.lift (restrictedScalarAction R A D.module).toLinearMap

private theorem targetAction_tmul (c : A) (m : restrictModule R A D.module) :
    targetAction D (c ⊗ₜ[R] m) = restrictedScalarAction R A D.module c m := rfl

private theorem restrictedScalarAction_one (m : restrictModule R A D.module) :
    restrictedScalarAction R A D.module 1 m = m := by
  rw [map_one]; rfl

private theorem restrictedScalarAction_mul (a b : A) (m : restrictModule R A D.module) :
    restrictedScalarAction R A D.module (a * b) m =
      restrictedScalarAction R A D.module a (restrictedScalarAction R A D.module b m) := by
  rw [map_mul]; rfl

private theorem targetAction_one_tmul (m : restrictModule R A D.module) :
    targetAction D ((1 : A) ⊗ₜ[R] m) = m :=
  restrictedScalarAction_one D m

/-- The multiplication map is linear for the action of `A ⊗[R] A` through multiplication. -/
private theorem targetAction_smul (a b : A) (y : A ⊗[R] restrictModule R A D.module) :
    targetAction D ((a ⊗ₜ[R] b) • y) =
      restrictedScalarAction R A D.module (a * b) (targetAction D y) := by
  induction y with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul c m =>
    rw [targetTensor_smul_tmul, targetAction_tmul, targetAction_tmul,
      restrictedScalarAction_mul D a c, restrictedScalarAction_mul D a b,
      ← restrictedScalarAction_mul D c b, mul_comm c b, restrictedScalarAction_mul D b c]

private theorem transition_restrictScalars_apply (x : restrictModule R A D.module ⊗[R] A) :
    (D.transition.toLinearMap.restrictScalars R) x = D.transition x := rfl

private theorem inverseTransition_apply (y : A ⊗[R] restrictModule R A D.module) :
    inverseTransition R A D y = D.transition.symm y := rfl

private theorem inverseTransition_transition (x : restrictModule R A D.module ⊗[R] A) :
    inverseTransition R A D (D.transition x) = x := by
  rw [inverseTransition_apply, LinearEquiv.symm_apply_apply]

private theorem transition_inverseTransition (y : A ⊗[R] restrictModule R A D.module) :
    D.transition (inverseTransition R A D y) = y := by
  rw [inverseTransition_apply, LinearEquiv.apply_symm_apply]

/-- `θ (1 ⊗ a • n) = (1 ⊗ a) • θ (1 ⊗ n)`. -/
private theorem inverseTransition_one_tmul_restrictedScalarAction
    (a : A) (n : restrictModule R A D.module) :
    inverseTransition R A D ((1 : A) ⊗ₜ[R] restrictedScalarAction R A D.module a n) =
      ((1 : A) ⊗ₜ[R] a) • inverseTransition R A D ((1 : A) ⊗ₜ[R] n) := by
  rw [inverseTransition_apply, inverseTransition_apply, ← LinearEquiv.map_smul,
    targetTensor_smul_tmul, mul_one]

/-- `n ⊗ b = (1 ⊗ b) • (n ⊗ 1)` in `N ⊗[R] A`. -/
private theorem tmul_eq_smul_tmul_one (n : restrictModule R A D.module) (b : A) :
    n ⊗ₜ[R] b = ((1 : A) ⊗ₜ[R] b) • (n ⊗ₜ[R] (1 : A)) := by
  rw [sourceTensor_smul_tmul, restrictedScalarAction_one, mul_one]

/-- The map `v ↦ (c ⊗ 1) ⊗ m`, inserting a unit in the middle of `A ⊗[R] N`. -/
private def middleUnitTarget :
    A ⊗[R] restrictModule R A D.module →ₗ[R] (A ⊗[R] A) ⊗[R] restrictModule R A D.module :=
  ((TensorProduct.mk R A A).flip 1).rTensor _

private theorem rightComm_tmul_one (v : A ⊗[R] restrictModule R A D.module) :
    TensorProduct.rightComm R A (restrictModule R A D.module) A (v ⊗ₜ[R] (1 : A)) =
      middleUnitTarget D v := by
  induction v with
  | zero => simp only [zero_tmul, map_zero]
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | tmul c m => rfl

/-- The pullback `φ₀₂` of the transition sends a unit inserted in the middle to a unit
inserted in the middle. -/
private theorem transition02_middleUnitInsertion (x : restrictModule R A D.module ⊗[R] A) :
    transition02 R A D.module D.transition (middleUnitInsertion R A D x) =
      middleUnitTarget D (D.transition x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    change TensorProduct.rightComm R A (restrictModule R A D.module) A
        (((D.transition.toLinearMap.restrictScalars R).rTensor A)
          (TensorProduct.rightComm R (restrictModule R A D.module) A A
            ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] b))) = _
    rw [TensorProduct.rightComm_tmul, LinearMap.rTensor_tmul, transition_restrictScalars_apply,
      rightComm_tmul_one]

/-- The pullback `φ₁₂` of the transition on an element with a unit in the first factor. -/
private theorem transition12_assoc_symm_one_tmul (x : restrictModule R A D.module ⊗[R] A) :
    transition12 R A D.module D.transition
        ((TensorProduct.assoc R A (restrictModule R A D.module) A).symm ((1 : A) ⊗ₜ[R] x)) =
      (TensorProduct.assoc R A A (restrictModule R A D.module)).symm
        ((1 : A) ⊗ₜ[R] D.transition x) := by
  change (TensorProduct.assoc R A A (restrictModule R A D.module)).symm
      (((D.transition.toLinearMap.restrictScalars R).lTensor A)
        ((TensorProduct.assoc R A (restrictModule R A D.module) A)
          ((TensorProduct.assoc R A (restrictModule R A D.module) A).symm
            ((1 : A) ⊗ₜ[R] x)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.lTensor_tmul, transition_restrictScalars_apply]

private theorem transition12_injective :
    Function.Injective (transition12 R A D.module D.transition) := by
  have h : transition12 R A D.module D.transition =
      ((TensorProduct.assoc R A (restrictModule R A D.module) A).trans
        (((D.transitionRestrictScalars R A).lTensor A).trans
          (TensorProduct.assoc R A A (restrictModule R A D.module)).symm)).toLinearMap := rfl
  rw [h]
  exact LinearEquiv.injective _

private theorem inverseTransition_rTensor_transition01
    (y : (restrictModule R A D.module ⊗[R] A) ⊗[R] A) :
    (inverseTransition R A D).toLinearMap.rTensor A
        (transition01 R A D.module D.transition y) = y := by
  induction y with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x b =>
    change (inverseTransition R A D).toLinearMap.rTensor A
        (((D.transition.toLinearMap.restrictScalars R).rTensor A) (x ⊗ₜ[R] b)) = _
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, transition_restrictScalars_apply,
      LinearEquiv.coe_coe, inverseTransition_transition]

/-- The two parallel arrows agree after `θ ∘ (1 ⊗ δ₀¹)`; this is the cocycle condition. -/
theorem inverseTransition01AfterUnit_inverseTransitionUnit
    (n : restrictModule R A D.module) :
    inverseTransition01AfterUnit R A D (inverseTransitionUnit R A D n) =
      middleUnitInsertion R A D (inverseTransitionUnit R A D n) := by
  set x := inverseTransitionUnit R A D n with hxdef
  have hx : D.transition x = (1 : A) ⊗ₜ[R] n := transition_inverseTransition D _
  have key : transition01 R A D.module D.transition (middleUnitInsertion R A D x) =
      (TensorProduct.assoc R A (restrictModule R A D.module) A).symm ((1 : A) ⊗ₜ[R] x) := by
    apply transition12_injective D
    rw [← LinearMap.comp_apply, D.cocycle, transition02_middleUnitInsertion,
      transition12_assoc_symm_one_tmul, hx]
    rfl
  change (inverseTransition R A D).toLinearMap.rTensor A
      ((TensorProduct.assoc R A (restrictModule R A D.module) A).symm ((1 : A) ⊗ₜ[R] x)) = _
  rw [← key, inverseTransition_rTensor_transition01]

/-- The endomorphism `n ↦ (1 ⊗ σ₀⁰)(φ(n ⊗ 1))`; the cocycle condition forces it to be the
identity. -/
private def diagonalEndo : restrictModule R A D.module →ₗ[R] restrictModule R A D.module :=
  targetAction D ∘ₗ (D.transitionRestrictScalars R A).toLinearMap ∘ₗ
    (TensorProduct.mk R (restrictModule R A D.module) A).flip 1

private theorem diagonalEndo_apply (n : restrictModule R A D.module) :
    diagonalEndo D n = targetAction D (D.transition (n ⊗ₜ[R] (1 : A))) := rfl

private theorem diagonalEndo_smul (a : A) (m : restrictModule R A D.module) :
    diagonalEndo D (restrictedScalarAction R A D.module a m) =
      restrictedScalarAction R A D.module a (diagonalEndo D m) := by
  have h : restrictedScalarAction R A D.module a m ⊗ₜ[R] (1 : A) =
      (a ⊗ₜ[R] (1 : A)) • (m ⊗ₜ[R] (1 : A)) := by
    rw [sourceTensor_smul_tmul, mul_one]
  rw [diagonalEndo_apply, h, LinearEquiv.map_smul, targetAction_smul, mul_one,
    diagonalEndo_apply]

/-- The second factor of a pullback of `φ₁₂`, multiplied out. -/
private theorem lTensor_targetAction_transition12_tmul_one
    (v : A ⊗[R] restrictModule R A D.module) :
    (targetAction D).lTensor A
        (TensorProduct.assoc R A A (restrictModule R A D.module)
          (transition12 R A D.module D.transition (v ⊗ₜ[R] (1 : A)))) =
      (diagonalEndo D).lTensor A v := by
  induction v with
  | zero => simp only [zero_tmul, map_zero]
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | tmul c m =>
    change (targetAction D).lTensor A
        (TensorProduct.assoc R A A (restrictModule R A D.module)
          ((TensorProduct.assoc R A A (restrictModule R A D.module)).symm
            (((D.transition.toLinearMap.restrictScalars R).lTensor A)
              ((TensorProduct.assoc R A (restrictModule R A D.module) A)
                ((c ⊗ₜ[R] m) ⊗ₜ[R] (1 : A)))))) = _
    rw [LinearEquiv.apply_symm_apply, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, transition_restrictScalars_apply,
      diagonalEndo_apply]

private theorem lTensor_targetAction_middleUnitTarget (v : A ⊗[R] restrictModule R A D.module) :
    (targetAction D).lTensor A
        (TensorProduct.assoc R A A (restrictModule R A D.module) (middleUnitTarget D v)) = v := by
  induction v with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c m =>
    change (targetAction D).lTensor A
        (TensorProduct.assoc R A A (restrictModule R A D.module) ((c ⊗ₜ[R] 1) ⊗ₜ[R] m)) = _
    rw [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, targetAction_one_tmul]

/-- The cocycle condition at `(n ⊗ 1) ⊗ 1`, multiplied out in the last two factors. -/
private theorem lTensor_diagonalEndo_transition_tmul_one (n : restrictModule R A D.module) :
    (diagonalEndo D).lTensor A (D.transition (n ⊗ₜ[R] (1 : A))) =
      D.transition (n ⊗ₜ[R] (1 : A)) := by
  have hc := congrArg (fun z => (targetAction D).lTensor A
      (TensorProduct.assoc R A A (restrictModule R A D.module) z))
    (LinearMap.congr_fun D.cocycle ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)))
  simp only [LinearMap.comp_apply] at hc
  have h01 : transition01 R A D.module D.transition ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)) =
      D.transition (n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A) := rfl
  have h02 : (n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A) = middleUnitInsertion R A D (n ⊗ₜ[R] (1 : A)) :=
    rfl
  rw [h01, lTensor_targetAction_transition12_tmul_one, h02,
    transition02_middleUnitInsertion, lTensor_targetAction_middleUnitTarget] at hc
  exact hc

private theorem lTensor_diagonalEndo_smul (a b : A) (y : A ⊗[R] restrictModule R A D.module) :
    (diagonalEndo D).lTensor A ((a ⊗ₜ[R] b) • y) =
      (a ⊗ₜ[R] b) • (diagonalEndo D).lTensor A y := by
  induction y with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul c m =>
    rw [targetTensor_smul_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      targetTensor_smul_tmul, diagonalEndo_smul]

private theorem lTensor_diagonalEndo_transition (x : restrictModule R A D.module ⊗[R] A) :
    (diagonalEndo D).lTensor A (D.transition x) = D.transition x := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    rw [tmul_eq_smul_tmul_one, LinearEquiv.map_smul, lTensor_diagonalEndo_smul,
      lTensor_diagonalEndo_transition_tmul_one]

/-- The cocycle condition tensored with `σ₁¹`: the endomorphism is the identity. -/
private theorem diagonalEndo_eq (m : restrictModule R A D.module) : diagonalEndo D m = m := by
  have h := congrArg (targetAction D)
    (lTensor_diagonalEndo_transition D (inverseTransition R A D ((1 : A) ⊗ₜ[R] m)))
  rwa [transition_inverseTransition, LinearMap.lTensor_tmul, targetAction_one_tmul,
    targetAction_one_tmul] at h

private theorem targetAction_transition (x : restrictModule R A D.module ⊗[R] A) :
    targetAction D (D.transition x) = actionRetraction R A D x := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    rw [tmul_eq_smul_tmul_one, LinearEquiv.map_smul, targetAction_smul, one_mul,
      ← diagonalEndo_apply, diagonalEndo_eq, ← tmul_eq_smul_tmul_one]
    rfl

/-- `(1 ⊗ σ₀⁰) ∘ θ ∘ (1 ⊗ δ₀¹) = 1`. -/
theorem actionRetraction_inverseTransitionUnit (n : restrictModule R A D.module) :
    actionRetraction R A D (inverseTransitionUnit R A D n) = n := by
  rw [← targetAction_transition]
  exact (congrArg (targetAction D) (transition_inverseTransition D _)).trans
    (targetAction_one_tmul D n)

/-- `(1 ⊗ σ₀¹) ∘ (1 ⊗ δ₁²) = 1`. -/
theorem multiplyLastSection_middleUnitInsertion (x : restrictModule R A D.module ⊗[R] A) :
    multiplyLastSection R A D (middleUnitInsertion R A D x) = x := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    change (LinearMap.mul' R A).lTensor _
        (TensorProduct.assoc R (restrictModule R A D.module) A A
          ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] b)) = _
    rw [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply, one_mul]

private theorem multiplyLastSection_tmul (v : restrictModule R A D.module ⊗[R] A) (b : A) :
    multiplyLastSection R A D (v ⊗ₜ[R] b) = ((1 : A) ⊗ₜ[R] b) • v := by
  induction v with
  | zero => simp only [zero_tmul, map_zero, smul_zero]
  | add x y hx hy => simp only [add_tmul, map_add, smul_add, hx, hy]
  | tmul n a =>
    change (LinearMap.mul' R A).lTensor _
        (TensorProduct.assoc R (restrictModule R A D.module) A A ((n ⊗ₜ[R] a) ⊗ₜ[R] b)) = _
    rw [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
      sourceTensor_smul_tmul, restrictedScalarAction_one, mul_comm]

/-- `(1 ⊗ σ₀¹) ∘ (θ ⊗ δ₂²) ∘ (1 ⊗ δ₀²) = θ ∘ (1 ⊗ δ₀¹) ∘ (1 ⊗ σ₀⁰)`. -/
theorem multiplyLastSection_inverseTransition01AfterUnit
    (x : restrictModule R A D.module ⊗[R] A) :
    multiplyLastSection R A D (inverseTransition01AfterUnit R A D x) =
      inverseTransitionUnit R A D (actionRetraction R A D x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    change multiplyLastSection R A D ((inverseTransition R A D).toLinearMap.rTensor A
        ((TensorProduct.assoc R A (restrictModule R A D.module) A).symm
          ((1 : A) ⊗ₜ[R] (n ⊗ₜ[R] b)))) =
      inverseTransition R A D ((1 : A) ⊗ₜ[R] restrictedScalarAction R A D.module b n)
    rw [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      multiplyLastSection_tmul, inverseTransition_one_tmul_restrictedScalarAction]

/-- **The transition of a descent datum restricts to the identity on the diagonal**: multiplying
out `φ(n ⊗ 1) ∈ A ⊗_R N` gives back `n`.  This is the unit condition `φ|_Δ = id`, a consequence
of the cocycle condition because `φ` is invertible. -/
theorem lift_restrictedScalarAction_transition_tmul_one (n : restrictModule R A D.module) :
    TensorProduct.lift (restrictedScalarAction R A D.module).toLinearMap
      (D.transition (n ⊗ₜ[R] (1 : A))) = n :=
  diagonalEndo_eq D n

end Lemmas

section LastFactor

variable (R A)

/-- The action of `A` on `X ⊗[R] A` through the last tensor factor. -/
def lastFactorAction (X : Type*) [AddCommGroup X] [Module R X] :
    A →ₐ[R] Module.End R (X ⊗[R] A) :=
  (Module.End.lTensorAlgHom R A X).comp (Algebra.lsmul R R A)

/-- `X ⊗[R] A` as an `A`-module through the last tensor factor. -/
abbrev lastFactorModule (X : Type*) [AddCommGroup X] [Module R X] : Module A (X ⊗[R] A) :=
  Module.compHom (X ⊗[R] A) (lastFactorAction R A X).toRingHom

/-- `X ⊗[R] A` as an object of `A`-modules, through the last tensor factor. For `X = N` and
`X = N ⊗[R] A` these are `M ⊗_{S, δ₁¹} S₂` and `M ⊗_{S, δ₁₂¹} S₃`, with `S` acting through
`δ₀¹ : S → S₂` and `δ₀₁¹ : S → S₃` respectively. -/
def lastFactorObj (X : Type*) [AddCommGroup X] [Module R X] : ModuleCat A :=
  letI := lastFactorModule R A X
  ModuleCat.of A (X ⊗[R] A)

variable {R A}

/-- An `R`-linear map commuting with the actions through the last tensor factor, as an
`A`-linear map. -/
def lastFactorLinearMap {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X ⊗[R] A →ₗ[R] Y ⊗[R] A)
    (hf : ∀ (a : A) (x : X ⊗[R] A),
      f (lastFactorAction R A X a x) = lastFactorAction R A Y a (f x)) :
    letI := lastFactorModule R A X
    letI := lastFactorModule R A Y
    X ⊗[R] A →ₗ[A] Y ⊗[R] A :=
  letI := lastFactorModule R A X
  letI := lastFactorModule R A Y
  { toFun := f
    map_add' := f.map_add
    map_smul' := hf }

/-- The action through the last factor on a pure tensor. -/
@[simp]
theorem lastFactorAction_tmul {X : Type*} [AddCommGroup X] [Module R X] (a b : A) (x : X) :
    lastFactorAction R A X a (x ⊗ₜ[R] b) = x ⊗ₜ[R] (a * b) := rfl

/-- A map of the form `g ⊗ id_A` commutes with the actions through the last factor. -/
theorem rTensor_lastFactorAction {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (g : X →ₗ[R] Y) (a : A) (x : X ⊗[R] A) :
    g.rTensor A (lastFactorAction R A X a x) = lastFactorAction R A Y a (g.rTensor A x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x b => rfl

/-- For `X = N`, the action through the last factor is the second-factor action
`ModuleCat.sourceRightAction` on the source of the transition. -/
theorem lastFactorAction_eq_sourceRightAction (N : ModuleCat.{w} A) :
    lastFactorAction R A (restrictModule R A N) = sourceRightAction R A N := rfl

end LastFactor

section Linearity

variable (D : DescentData.{u, v, w} R A)

/-- On `N ⊗[R] A = M ⊗_{S, δ₁¹} S₂`, the action through the last factor is the action of
`S₂` restricted along `δ₀¹ : a ↦ 1 ⊗ a`. -/
theorem one_tmul_smul (a : A) (y : restrictModule R A D.module ⊗[R] A) :
    ((1 : A) ⊗ₜ[R] a) • y = lastFactorAction R A _ a y := by
  induction y with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul n b =>
    rw [sourceTensor_smul_tmul, restrictedScalarAction_one, lastFactorAction_tmul]

/-- `θ ∘ (1 ⊗ δ₀¹)` is linear for the action through the last factor. -/
theorem inverseTransitionUnit_smul (a : A) (n : restrictModule R A D.module) :
    inverseTransitionUnit R A D (restrictedScalarAction R A D.module a n) =
      lastFactorAction R A _ a (inverseTransitionUnit R A D n) := by
  change inverseTransition R A D ((1 : A) ⊗ₜ[R] restrictedScalarAction R A D.module a n) = _
  rw [inverseTransition_one_tmul_restrictedScalarAction, one_tmul_smul]
  rfl

/-- `(θ ⊗ δ₂²) ∘ (1 ⊗ δ₀²) = (θ ∘ (1 ⊗ δ₀¹)) ⊗ id_A`. -/
theorem inverseTransition01AfterUnit_eq :
    inverseTransition01AfterUnit R A D = (inverseTransitionUnit R A D).rTensor A := by
  ext n b
  rfl

/-- `1 ⊗ σ₀⁰` is linear for the action through the last factor. -/
theorem actionRetraction_lastFactorAction (a : A)
    (x : restrictModule R A D.module ⊗[R] A) :
    actionRetraction R A D (lastFactorAction R A _ a x) =
      restrictedScalarAction R A D.module a (actionRetraction R A D x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    rw [lastFactorAction_tmul]
    exact restrictedScalarAction_mul D a b n

/-- `1 ⊗ σ₀¹` is linear for the actions through the last factor. -/
theorem multiplyLastSection_lastFactorAction (a : A)
    (x : (restrictModule R A D.module ⊗[R] A) ⊗[R] A) :
    multiplyLastSection R A D (lastFactorAction R A _ a x) =
      lastFactorAction R A _ a (multiplyLastSection R A D x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    rw [lastFactorAction_tmul, multiplyLastSection_tmul, multiplyLastSection_tmul,
      ← one_tmul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Linearity

/-- The first object `M` of the diagram, as an `A`-module (universe-lifted to the universe of the
tensor products). -/
abbrev descentModuleLift (D : DescentData.{u, v, w} R A) : ModuleCat.{max w v} A :=
  ModuleCat.of A (ULift.{v} D.module)

/-- The arrow `θ ∘ (1 ⊗ δ₀¹) : M → M ⊗_{S, δ₁¹} S₂` as a morphism of `A`-modules. -/
def inverseTransitionUnitHom (D : DescentData.{u, v, w} R A) :
    descentModuleLift D ⟶ lastFactorObj R A (restrictModule R A D.module) :=
  letI := lastFactorModule R A (restrictModule R A D.module)
  ModuleCat.ofHom
    { toFun := fun z => inverseTransitionUnit R A D z.down
      map_add' := fun z z' => map_add (inverseTransitionUnit R A D) z.down z'.down
      map_smul' := fun a z => inverseTransitionUnit_smul D a z.down }

/-- The arrow `(θ ⊗ δ₂²) ∘ (1 ⊗ δ₀²)` as a morphism of `A`-modules. -/
def inverseTransition01AfterUnitHom (D : DescentData.{u, v, w} R A) :
    lastFactorObj R A (restrictModule R A D.module) ⟶
      lastFactorObj R A (restrictModule R A D.module ⊗[R] A) :=
  letI := lastFactorModule R A (restrictModule R A D.module)
  letI := lastFactorModule R A (restrictModule R A D.module ⊗[R] A)
  ModuleCat.ofHom <| lastFactorLinearMap (inverseTransition01AfterUnit R A D) fun a x => by
    rw [inverseTransition01AfterUnit_eq]
    exact rTensor_lastFactorAction _ a x

/-- The arrow `1 ⊗ δ₁²` as a morphism of `A`-modules. -/
def middleUnitInsertionHom (D : DescentData.{u, v, w} R A) :
    lastFactorObj R A (restrictModule R A D.module) ⟶
      lastFactorObj R A (restrictModule R A D.module ⊗[R] A) :=
  letI := lastFactorModule R A (restrictModule R A D.module)
  letI := lastFactorModule R A (restrictModule R A D.module ⊗[R] A)
  ModuleCat.ofHom <| lastFactorLinearMap (middleUnitInsertion R A D) fun a x =>
    rTensor_lastFactorAction _ a x

/-- The auxiliary map `1 ⊗ σ₀⁰` as a morphism of `A`-modules. -/
def actionRetractionHom (D : DescentData.{u, v, w} R A) :
    lastFactorObj R A (restrictModule R A D.module) ⟶ descentModuleLift D :=
  letI := lastFactorModule R A (restrictModule R A D.module)
  ModuleCat.ofHom
    { toFun := fun x => ULift.up (actionRetraction R A D x)
      map_add' := fun x y => congrArg ULift.up (map_add (actionRetraction R A D) x y)
      map_smul' := fun a x => congrArg ULift.up (actionRetraction_lastFactorAction D a x) }

/-- The auxiliary map `1 ⊗ σ₀¹` as a morphism of `A`-modules. -/
def multiplyLastSectionHom (D : DescentData.{u, v, w} R A) :
    lastFactorObj R A (restrictModule R A D.module ⊗[R] A) ⟶
      lastFactorObj R A (restrictModule R A D.module) :=
  letI := lastFactorModule R A (restrictModule R A D.module)
  letI := lastFactorModule R A (restrictModule R A D.module ⊗[R] A)
  ModuleCat.ofHom <| lastFactorLinearMap (multiplyLastSection R A D)
    (multiplyLastSection_lastFactorAction D)

/-- The split equalizer structure on the diagram of Tag 08WZ, with the auxiliary maps
`1 ⊗ σ₀⁰` and `1 ⊗ σ₀¹`. -/
def inverseTransitionUnitSplitEqualizer (D : DescentData.{u, v, w} R A) :
    IsSplitEqualizer (inverseTransition01AfterUnitHom D) (middleUnitInsertionHom D)
      (inverseTransitionUnitHom D) where
  leftRetraction := actionRetractionHom D
  rightRetraction := multiplyLastSectionHom D
  condition := ModuleCat.hom_ext <| LinearMap.ext fun z =>
    inverseTransition01AfterUnit_inverseTransitionUnit D z.down
  ι_leftRetraction := ModuleCat.hom_ext <| LinearMap.ext fun z =>
    congrArg ULift.up (actionRetraction_inverseTransitionUnit D z.down)
  bottom_rightRetraction := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    multiplyLastSection_middleUnitInsertion D x
  top_rightRetraction := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    multiplyLastSection_inverseTransition01AfterUnit D x

/-- **Stacks Project, Tag 08WZ.** For a descent datum `(M, θ)` relative to `R → S`, the diagram
```
      θ ∘ (1 ⊗ δ₀¹)                    (θ ⊗ δ₂²) ∘ (1 ⊗ δ₀²)
  M ---------------> M ⊗_{S, δ₁¹} S₂ ========================> M ⊗_{S, δ₁₂¹} S₃
                                            1 ⊗ δ₁²
```
is a split equalizer of `S`-modules. Here `M ⊗_{S, δ₁¹} S₂ = N ⊗[R] A` and
`M ⊗_{S, δ₁₂¹} S₃ = (N ⊗[R] A) ⊗[R] A`, on which `S` acts through the last tensor factor, and
`θ` is `inverseTransition`, the inverse of the transition isomorphism; see the module docstring
for the identifications. The auxiliary maps are `1 ⊗ σ₀⁰` and `1 ⊗ σ₀¹`, see
`inverseTransitionUnitSplitEqualizer`. -/
@[stacks 08WZ]
theorem isSplitEqualizer_inverseTransitionUnitHom (D : DescentData.{u, v, w} R A) :
    Nonempty (IsSplitEqualizer (inverseTransition01AfterUnitHom D) (middleUnitInsertionHom D)
      (inverseTransitionUnitHom D)) :=
  ⟨inverseTransitionUnitSplitEqualizer D⟩

end ModuleCat.DescentData

end
