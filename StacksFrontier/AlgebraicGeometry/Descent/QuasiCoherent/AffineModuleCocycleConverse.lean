module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineModuleBridge

/-!
# From the `ModuleCat.extendScalars` cocycle condition back to `ModuleCat.DescentData`

A `B`-module `N` together with an isomorphism of its two extensions of scalars to `B ⊗[R] B`
satisfying the `ModuleCat.extendScalars`-level cocycle identity is a `ModuleCat.DescentData`
(`Stacks.Descent.moduleDescentDataOfCocycle`).  This is the converse of
`Stacks.Descent.extendScalarsTripleTransition_comp`, which translates the cocycle condition of a
`ModuleCat.DescentData` for `R → B` into the identity between the three base changes of its
transition along the three ring maps `B ⊗[R] B → B ⊗[R] (B ⊗[R] B)`.

## Main definitions

* `Stacks.Descent.extendScalarsTmul`: the element `s ⊗ x` of an extension of scalars.
* `Stacks.Descent.cocycleActHom`: the `R`-linear operator `(x ⊗ y) ⊗ n ↦ (x ⊗ c * y) ⊗ b • n`
  on `(B ⊗[R] B) ⊗[R] N`.
* `Stacks.Descent.transitionOfExtendScalars`: the `B ⊗[R] B`-linear isomorphism
  `N ⊗[R] B ≃ B ⊗[R] N` attached to an isomorphism of the two extensions of scalars of `N`,
  inverse to `Stacks.Descent.extendScalarsTransitionOfEquiv`.
* `Stacks.Descent.extendScalarsTransitionOfEquiv` and
  `Stacks.Descent.extendScalarsTripleTransitionOf`:
  `Stacks.Descent.extendScalarsTransitionOfDescentData` and
  `Stacks.Descent.extendScalarsTripleTransition` for a transition that is not given by a
  `ModuleCat.DescentData`.
* `Stacks.Descent.ExtendScalarsCocycle`: the cocycle condition at the level of
  `ModuleCat.extendScalars`.
* `Stacks.Descent.moduleDescentDataOfCocycle`: **the module descent datum attached to a
  `B`-module and such an isomorphism.**

## Main results

* `Stacks.Descent.tripleCocycleMap_injective`: **`Stacks.Descent.tripleCocycleMap` is
  injective**, with an explicit retraction
  `Stacks.Descent.invTripleCocycleMap`.
* `Stacks.Descent.cocycle_of_oneTmul`: **the cocycle identity of a module descent datum follows
  from its values at `(n ⊗ 1) ⊗ 1`.**
* `Stacks.Descent.extendScalarsCocycle_iff`: **the two cocycle conditions are equivalent.**  Its
  two directions are `Stacks.Descent.extendScalarsCocycle_of_descentData` and
  `Stacks.Descent.cocycle_of_extendScalarsCocycle`.
* `Stacks.Descent.moduleDescentDataOfCocycle_transition` and
  `Stacks.Descent.extendScalarsTransitionOfDescentData_moduleDescentDataOfCocycle`: the
  transition of `Stacks.Descent.moduleDescentDataOfCocycle` is the given one, read in either
  model.

## References

* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

open scoped ChangeOfRings

universe u

namespace Stacks.Descent

/-! ### Elements of an extension of scalars -/

section ExtendScalarsTmul

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {X : ModuleCat.{u} R}

/-- The element `s ⊗ x` of `(ModuleCat.extendScalars f).obj X`. -/
def extendScalarsTmul (s : S) (x : X) : ((ModuleCat.extendScalars f).obj X : Type u) :=
  s ⊗ₜ[R,f] x

/-- Scalars act on `Stacks.Descent.extendScalarsTmul` through the first factor. -/
theorem smul_extendScalarsTmul (t s : S) (x : X) :
    t • extendScalarsTmul f s x = extendScalarsTmul f (t * s) x :=
  rfl

/-- `ModuleCat.ExtendScalars.oneTmul` scaled by `t` is `Stacks.Descent.extendScalarsTmul` at
`t`. -/
theorem smul_oneTmul (t : S) (x : X) :
    t • ModuleCat.ExtendScalars.oneTmul f x = extendScalarsTmul f t x :=
  (smul_extendScalarsTmul f t 1 x).trans
    (congrArg (fun y ↦ extendScalarsTmul f y x) (mul_one t))

end ExtendScalarsTmul

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (N : ModuleCat.{u} B)

/-! ### The cocycle identity from its values at `(n ⊗ 1) ⊗ 1` -/

section Generators

/-- The `R`-linear operator `(x ⊗ y) ⊗ n ↦ (x ⊗ c * y) ⊗ b • n` on the target of the cocycle
identity. -/
def cocycleActHom (c b : B) :
    (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N →ₗ[R]
      (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N :=
  TensorProduct.map (TensorProduct.map LinearMap.id (LinearMap.mulLeft R c))
    (ModuleCat.restrictedScalarAction R B N b)

/-- `Stacks.Descent.cocycleActHom` on a pure tensor. -/
@[simp]
theorem cocycleActHom_tmul (c b x y : B) (n : ModuleCat.restrictModule R B N) :
    cocycleActHom R B N c b ((x ⊗ₜ[R] y) ⊗ₜ[R] n) =
      (x ⊗ₜ[R] (c * y)) ⊗ₜ[R] ModuleCat.restrictedScalarAction R B N b n := by
  rw [cocycleActHom, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

variable (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
  (B ⊗[R] ModuleCat.restrictModule R B N))

/-- `ModuleCat.transition01` on a pure tensor. -/
theorem transition01_tmul (n : ModuleCat.restrictModule R B N) (c b : B) :
    ModuleCat.transition01 R B N e ((n ⊗ₜ[R] c) ⊗ₜ[R] b) = e (n ⊗ₜ[R] c) ⊗ₜ[R] b := by
  rw [ModuleCat.transition01]; simp

/-- `ModuleCat.transition02` on a pure tensor. -/
theorem transition02_tmul (n : ModuleCat.restrictModule R B N) (c b : B) :
    ModuleCat.transition02 R B N e ((n ⊗ₜ[R] c) ⊗ₜ[R] b) =
      (TensorProduct.rightComm R B (ModuleCat.restrictModule R B N) B)
        (e (n ⊗ₜ[R] b) ⊗ₜ[R] c) := by
  rw [ModuleCat.transition02]; simp

/-- `ModuleCat.transition12` on a pure tensor. -/
theorem transition12_tmul (x : B) (m : ModuleCat.restrictModule R B N) (b : B) :
    ModuleCat.transition12 R B N e ((x ⊗ₜ[R] m) ⊗ₜ[R] b) =
      (TensorProduct.assoc R B B (ModuleCat.restrictModule R B N)).symm
        (x ⊗ₜ[R] e (m ⊗ₜ[R] b)) := by
  rw [ModuleCat.transition12]; simp

/-- The value of the transition at `n ⊗ c`, in terms of its value at `n ⊗ 1`. -/
theorem apply_tmul_eq_smul (n : ModuleCat.restrictModule R B N) (c : B) :
    e (n ⊗ₜ[R] c) = ((1 : B) ⊗ₜ[R] c) • e (n ⊗ₜ[R] (1 : B)) := by
  rw [← map_smul]
  congr 1
  rw [ModuleCat.sourceTensor_smul_tmul]
  simp

/-- The value of the transition at `(c • n) ⊗ b`, in terms of its value at `n ⊗ 1`. -/
theorem apply_smul_tmul (n : ModuleCat.restrictModule R B N) (c b : B) :
    e (ModuleCat.restrictedScalarAction R B N c n ⊗ₜ[R] b) =
      (c ⊗ₜ[R] b) • e (n ⊗ₜ[R] (1 : B)) := by
  rw [← map_smul]
  congr 1
  rw [ModuleCat.sourceTensor_smul_tmul, mul_one]

/-- The last step of `ModuleCat.transition12` intertwines the action of `c ⊗ b` with
`Stacks.Descent.cocycleActHom`. -/
theorem assoc_symm_smul (x c b : B) (u : B ⊗[R] ModuleCat.restrictModule R B N) :
    (TensorProduct.assoc R B B (ModuleCat.restrictModule R B N)).symm
        (x ⊗ₜ[R] ((c ⊗ₜ[R] b) • u)) =
      cocycleActHom R B N c b
        ((TensorProduct.assoc R B B (ModuleCat.restrictModule R B N)).symm (x ⊗ₜ[R] u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul y n =>
    rw [ModuleCat.targetTensor_smul_tmul, TensorProduct.assoc_symm_tmul,
      TensorProduct.assoc_symm_tmul, cocycleActHom_tmul]
  | add u u' hu hu' =>
    rw [smul_add, TensorProduct.tmul_add, map_add, hu, hu', TensorProduct.tmul_add,
      map_add, map_add]

/-- A linear map out of `(B ⊗ N) ⊗ B` transforms by `Stacks.Descent.cocycleActHom` as soon as it
does on pure tensors. -/
private theorem transport_of_tmul
    (Φ : ((B ⊗[R] ModuleCat.restrictModule R B N) ⊗[R] B) →ₗ[R]
      ((B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N)) (c b s t : B)
    (h : ∀ (x : B) (n : ModuleCat.restrictModule R B N),
      Φ ((((1 : B) ⊗ₜ[R] s) • (x ⊗ₜ[R] n)) ⊗ₜ[R] t) =
        cocycleActHom R B N c b (Φ ((x ⊗ₜ[R] n) ⊗ₜ[R] (1 : B))))
    (w : B ⊗[R] ModuleCat.restrictModule R B N) :
    Φ ((((1 : B) ⊗ₜ[R] s) • w) ⊗ₜ[R] t) = cocycleActHom R B N c b (Φ (w ⊗ₜ[R] (1 : B))) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => exact h x n
  | add w w' hw hw' =>
    rw [smul_add, TensorProduct.add_tmul, map_add, hw, hw', TensorProduct.add_tmul,
      map_add, map_add]

/-- **`ModuleCat.transition12` transforms by `Stacks.Descent.cocycleActHom`.** -/
theorem transition12_transport (c b : B) (w : B ⊗[R] ModuleCat.restrictModule R B N) :
    ModuleCat.transition12 R B N e ((((1 : B) ⊗ₜ[R] c) • w) ⊗ₜ[R] b) =
      cocycleActHom R B N c b (ModuleCat.transition12 R B N e (w ⊗ₜ[R] (1 : B))) :=
  transport_of_tmul R B N _ c b c b (fun x n ↦ by
    rw [ModuleCat.targetTensor_smul_tmul, one_mul, transition12_tmul, transition12_tmul,
      apply_smul_tmul, assoc_symm_smul]) w

/-- **The last step of `ModuleCat.transition02` transforms by
`Stacks.Descent.cocycleActHom`.** -/
theorem rightComm_transport (c b : B) (w : B ⊗[R] ModuleCat.restrictModule R B N) :
    (TensorProduct.rightComm R B (ModuleCat.restrictModule R B N) B)
        ((((1 : B) ⊗ₜ[R] b) • w) ⊗ₜ[R] c) =
      cocycleActHom R B N c b
        ((TensorProduct.rightComm R B (ModuleCat.restrictModule R B N) B) (w ⊗ₜ[R] (1 : B))) :=
  transport_of_tmul R B N (TensorProduct.rightComm R B _ B).toLinearMap c b b c (fun x n ↦ by
    rw [ModuleCat.targetTensor_smul_tmul, one_mul, LinearEquiv.coe_coe,
      TensorProduct.rightComm_tmul, TensorProduct.rightComm_tmul, cocycleActHom_tmul, mul_one]) w

/-- **The cocycle condition of `ModuleCat.DescentData` follows from its values at the elements
`(n ⊗ 1) ⊗ 1`.** -/
theorem cocycle_of_oneTmul
    (hgen : ∀ n : ModuleCat.restrictModule R B N,
      ModuleCat.transition12 R B N e (e (n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) =
        ModuleCat.transition02 R B N e ((n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B))) :
    (ModuleCat.transition12 R B N e).comp (ModuleCat.transition01 R B N e) =
      ModuleCat.transition02 R B N e := by
  refine TensorProduct.ext' fun y b ↦ ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul n c =>
    have hL : ModuleCat.transition12 R B N e
        (ModuleCat.transition01 R B N e ((n ⊗ₜ[R] c) ⊗ₜ[R] b)) =
        cocycleActHom R B N c b
          (ModuleCat.transition12 R B N e (e (n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B))) := by
      rw [transition01_tmul, apply_tmul_eq_smul R B N e n c, transition12_transport]
    have hR : ModuleCat.transition02 R B N e ((n ⊗ₜ[R] c) ⊗ₜ[R] b) =
        cocycleActHom R B N c b
          (ModuleCat.transition02 R B N e ((n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B))) := by
      rw [transition02_tmul, apply_tmul_eq_smul R B N e n b, rightComm_transport,
        transition02_tmul R B N e n 1 1]
    rw [LinearMap.comp_apply, hL, hR, hgen]
  | add y y' hy hy' =>
    rw [TensorProduct.add_tmul, map_add, map_add, hy, hy']

end Generators

/-! ### `Stacks.Descent.tripleCocycleMap` is injective

`Stacks.Descent.tripleCocycleMap` sends `(b₀ ⊗ b₁) ⊗ n` to `b₀ ⊗ (b₁ ⊗ 1) ⊗ n` in the extension
of scalars of `N` along `b ↦ 1 ⊗ (1 ⊗ b)`.  The retraction sends `b₀ ⊗ (b₁ ⊗ b₂) ⊗ n` to
`(b₀ ⊗ b₁) ⊗ b₂ • n`. -/

section Injectivity

/-- The bilinear map `(x ⊗ y, b) ↦ (n ↦ (x ⊗ y) ⊗ b • n)`. -/
def invTripleBil : (B ⊗[R] B) →ₗ[R] B →ₗ[R]
    (ModuleCat.restrictModule R B N →ₗ[R]
      (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N) :=
  ((LinearMap.llcomp R (ModuleCat.restrictModule R B N) (ModuleCat.restrictModule R B N)
        ((B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N)).comp
      (TensorProduct.mk R (B ⊗[R] B) (ModuleCat.restrictModule R B N))).compl₂
    (ModuleCat.restrictedScalarAction R B N).toLinearMap

/-- The `R`-linear map `b₀ ⊗ (b₁ ⊗ b₂) ↦ (n ↦ (b₀ ⊗ b₁) ⊗ b₂ • n)`. -/
def invTripleLin : (B ⊗[R] (B ⊗[R] B)) →ₗ[R]
    (ModuleCat.restrictModule R B N →ₗ[R]
      (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N) :=
  (TensorProduct.lift (invTripleBil R B N)).comp (TensorProduct.assoc R B B B).symm.toLinearMap

/-- `Stacks.Descent.invTripleLin` on a pure tensor. -/
theorem invTripleLin_apply (b₀ b₁ b₂ : B) (n : ModuleCat.restrictModule R B N) :
    invTripleLin R B N (b₀ ⊗ₜ[R] (b₁ ⊗ₜ[R] b₂)) n =
      (b₀ ⊗ₜ[R] b₁) ⊗ₜ[R] ModuleCat.restrictedScalarAction R B N b₂ n := by
  rw [invTripleLin, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
    TensorProduct.lift.tmul]
  rfl

/-- `Stacks.Descent.invTripleLin` as a biadditive map. -/
def invTripleAddHom : (B ⊗[R] (B ⊗[R] B)) →+
    ((N : Type u) →+ (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N) where
  toFun t := (invTripleLin R B N t).toAddMonoidHom
  map_zero' := by
    ext n
    exact (AddMonoidHom.zero_apply n).symm
  map_add' t t' := by
    ext n
    rw [map_add]
    exact (AddMonoidHom.add_apply (invTripleLin R B N t).toAddMonoidHom
      (invTripleLin R B N t').toAddMonoidHom n).symm

/-- `Stacks.Descent.invTripleAddHom` on a pure tensor. -/
theorem invTripleAddHom_apply (b₀ b₁ b₂ : B) (n : N) :
    invTripleAddHom R B N (b₀ ⊗ₜ[R] (b₁ ⊗ₜ[R] b₂)) n =
      (b₀ ⊗ₜ[R] b₁) ⊗ₜ[R] (show ModuleCat.restrictModule R B N from b₂ • n) :=
  invTripleLin_apply R B N b₀ b₁ b₂ n

/-- `Stacks.Descent.invTripleAddHom` is balanced over `B` acting through `b ↦ 1 ⊗ (1 ⊗ b)`. -/
theorem invTripleAddHom_balanced (b : B) (t : B ⊗[R] (B ⊗[R] B)) (n : N) :
    invTripleAddHom R B N ((tensorIncl₂ R B).hom b * t) n =
      invTripleAddHom R B N t (b • n) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b₀ y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b₁ b₂ =>
      rw [show ((tensorIncl₂ R B).hom b : B ⊗[R] (B ⊗[R] B)) =
            (1 : B) ⊗ₜ[R] ((1 : B) ⊗ₜ[R] b) from rfl,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, one_mul, invTripleAddHom_apply, invTripleAddHom_apply, mul_comm b b₂, mul_smul]
    | add y y' hy hy' =>
      rw [TensorProduct.tmul_add, mul_add, map_add, map_add, AddMonoidHom.add_apply,
        AddMonoidHom.add_apply, hy, hy']
  | add t t' ht ht' =>
    rw [mul_add, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, ht, ht']

/-- **The retraction of `Stacks.Descent.tripleCocycleMap`**, sending
`b₀ ⊗ (b₁ ⊗ b₂) ⊗ n` to `(b₀ ⊗ b₁) ⊗ b₂ • n`. -/
def invTripleCocycleMap :
    ((ModuleCat.extendScalars (tensorIncl₂ R B).hom).obj N : Type u) →+
      (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N :=
  TensorProduct.liftAddHom (R := B) (invTripleAddHom R B N)
    fun b t n ↦ invTripleAddHom_balanced R B N b t n

/-- `Stacks.Descent.invTripleCocycleMap` sends `t ⊗ n` to `Stacks.Descent.invTripleAddHom` at
`t` and `n`. -/
theorem invTripleCocycleMap_extendScalarsTmul (t : B ⊗[R] (B ⊗[R] B)) (n : N) :
    invTripleCocycleMap R B N (extendScalarsTmul (tensorIncl₂ R B).hom t n) =
      invTripleAddHom R B N t n :=
  rfl

/-- `Stacks.Descent.tensorMap₀₁` on a pure tensor, as a pure tensor. -/
theorem tensorMap₀₁_tmul' (b₀ b₁ : B) :
    (tensorMap₀₁ R B).hom (b₀ ⊗ₜ[R] b₁) = b₀ ⊗ₜ[R] (b₁ ⊗ₜ[R] (1 : B)) := by
  show Algebra.TensorProduct.map _ _ (b₀ ⊗ₜ[R] b₁) = _
  simp

/-- `Stacks.Descent.invTripleCocycleMap` is a left inverse of
`Stacks.Descent.tripleCocycleMap`. -/
theorem invTripleCocycleMap_tripleCocycleMap
    (z : (B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N) :
    invTripleCocycleMap R B N (tripleCocycleMap R B N z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x n =>
    induction x using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | tmul b₀ b₁ =>
      rw [smulOneTmulMap_tmul, smulOneTmul, smul_oneTmul,
        invTripleCocycleMap_extendScalarsTmul, tensorMap₀₁_tmul', invTripleAddHom_apply,
        one_smul]
    | add x x' hx hx' =>
      rw [TensorProduct.add_tmul, map_add, map_add, hx, hx']
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- **`Stacks.Descent.tripleCocycleMap` is injective.** -/
theorem tripleCocycleMap_injective : Function.Injective (tripleCocycleMap R B N) :=
  Function.LeftInverse.injective (invTripleCocycleMap_tripleCocycleMap R B N)

end Injectivity

/-! ### The dictionary, read backwards -/

section Dictionary

/-- `Stacks.Descent.extendScalarsTransitionOfDescentData` for a transition isomorphism that is
not given by a module descent datum. -/
def extendScalarsTransitionOfEquiv
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N)) :
    (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N :=
  extendScalarsInlSourceIso R B N ≪≫ e.toModuleIso ≪≫ (extendScalarsInrTargetIso R B N).symm

/-- `Stacks.Descent.extendScalarsTransitionOfDescentData` is
`Stacks.Descent.extendScalarsTransitionOfEquiv` at the transition of the datum. -/
theorem extendScalarsTransitionOfDescentData_eq (D : ModuleCat.DescentData.{u, u, u} R B) :
    extendScalarsTransitionOfDescentData R B D =
      extendScalarsTransitionOfEquiv R B D.module D.transition :=
  rfl

/-- **The transition isomorphism of the two models attached to an isomorphism of the two
extensions of scalars.**  This is the inverse of
`Stacks.Descent.extendScalarsTransitionOfEquiv`. -/
def transitionOfExtendScalars
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N) :
    (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N) :=
  ((extendScalarsInlSourceIso R B N).symm ≪≫ α ≪≫
    extendScalarsInrTargetIso R B N).toLinearEquiv

/-- `Stacks.Descent.extendScalarsTransitionOfEquiv` is a left inverse of
`Stacks.Descent.transitionOfExtendScalars`. -/
@[simp]
theorem extendScalarsTransitionOfEquiv_transitionOfExtendScalars
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N) :
    extendScalarsTransitionOfEquiv R B N (transitionOfExtendScalars R B N α) = α := by
  rw [extendScalarsTransitionOfEquiv, transitionOfExtendScalars,
    show (((extendScalarsInlSourceIso R B N).symm ≪≫ α ≪≫
            extendScalarsInrTargetIso R B N).toLinearEquiv).toModuleIso =
        (extendScalarsInlSourceIso R B N).symm ≪≫ α ≪≫ extendScalarsInrTargetIso R B N from rfl]
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

/-- `Stacks.Descent.extendScalarsTransitionOfDescentData_hom_oneTmul` for a transition that is
not given by a module descent datum. -/
theorem extendScalarsTransitionOfEquiv_hom_oneTmul
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N))
    (n : ModuleCat.restrictModule R B N) :
    (extendScalarsTransitionOfEquiv R B N e).hom
        (ModuleCat.ExtendScalars.oneTmul (tensorInl R B).hom (show (N : Type u) from n)) =
      targetModelInvAdd R B N (e (n ⊗ₜ[R] (1 : B))) := by
  have h : sourceModelHom R B N
      (ModuleCat.ExtendScalars.oneTmul (tensorInl R B).hom (show (N : Type u) from n)) =
      n ⊗ₜ[R] (1 : B) :=
    (sourceModelHom_tensorInlElt R B N 1 n).trans (one_smul _ _)
  show targetModelInvAdd R B N (e (sourceModelHom R B N
    (ModuleCat.ExtendScalars.oneTmul (tensorInl R B).hom (show (N : Type u) from n)))) = _
  rw [h]

variable {T : Type u} [CommRing T]

/-- `Stacks.Descent.extendScalarsTripleTransition` for a transition that is not given by a
module descent datum. -/
def extendScalarsTripleTransitionOf
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ⟶
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N)
    (ψ : (B ⊗[R] B) →+* T) {j₁ j₂ : B →+* T}
    (h₁ : ψ.comp (tensorInl R B).hom = j₁) (h₂ : ψ.comp (tensorInr R B).hom = j₂) :
    (ModuleCat.extendScalars j₁).obj N ⟶ (ModuleCat.extendScalars j₂).obj N :=
  (ModuleCat.cancelExtendScalars (tensorInl R B).hom ψ h₁ N).inv ≫
    (ModuleCat.extendScalars ψ).map α ≫
    (ModuleCat.cancelExtendScalars (tensorInr R B).hom ψ h₂ N).hom

/-- `Stacks.Descent.extendScalarsTripleTransition` is
`Stacks.Descent.extendScalarsTripleTransitionOf` at the transition of the datum. -/
theorem extendScalarsTripleTransition_eq (D : ModuleCat.DescentData.{u, u, u} R B)
    (ψ : (B ⊗[R] B) →+* T) {j₁ j₂ : B →+* T}
    (h₁ : ψ.comp (tensorInl R B).hom = j₁) (h₂ : ψ.comp (tensorInr R B).hom = j₂) :
    extendScalarsTripleTransition R B D ψ h₁ h₂ =
      extendScalarsTripleTransitionOf R B D.module
        (extendScalarsTransitionOfDescentData R B D).hom ψ h₁ h₂ :=
  rfl

/-- `Stacks.Descent.extendScalarsTripleTransition_oneTmul` for a transition that is not given by
a module descent datum. -/
theorem extendScalarsTripleTransitionOf_oneTmul
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N))
    (ψ : (B ⊗[R] B) →+* T) {j₁ j₂ : B →+* T}
    (h₁ : ψ.comp (tensorInl R B).hom = j₁) (h₂ : ψ.comp (tensorInr R B).hom = j₂)
    [Algebra R T]
    (hj₁ : ∀ r : R, j₁ (algebraMap R B r) = algebraMap R T r)
    (hj₂ : ∀ r : R, j₂ (algebraMap R B r) = algebraMap R T r)
    (n : ModuleCat.restrictModule R B N) :
    extendScalarsTripleTransitionOf R B N (extendScalarsTransitionOfEquiv R B N e).hom ψ h₁ h₂
        (ModuleCat.ExtendScalars.oneTmul j₁ (show (N : Type u) from n)) =
      smulOneTmulMap R B N j₁ j₂ hj₁ hj₂ (e (n ⊗ₜ[R] (1 : B))) := by
  rw [extendScalarsTripleTransitionOf, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.cancelExtendScalars_inv_oneTmul, ModuleCat.ExtendScalars.map_oneTmul,
    extendScalarsTransitionOfEquiv_hom_oneTmul,
    cancelExtendScalars_hom_oneTmul_targetModelInvAdd R B N ψ h₁ h₂ hj₁ hj₂]

/-- `Stacks.Descent.extendScalarsTripleTransition₁₂_tripleMap₀₁` for a transition that is not
given by a module descent datum. -/
theorem extendScalarsTripleTransitionOf₁₂_tripleMap₀₁
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N))
    (y : B ⊗[R] ModuleCat.restrictModule R B N) :
    extendScalarsTripleTransitionOf R B N (extendScalarsTransitionOfEquiv R B N e).hom
        (tensorMap₁₂ R B).hom (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B)
        (tripleMap₀₁ R B N y) =
      tripleCocycleMap R B N (ModuleCat.transition12 R B N e (y ⊗ₜ[R] (1 : B))) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | tmul c n =>
    rw [transition12_tmul, tripleCocycleMap_assoc_symm, smulOneTmulMap_tmul, smulOneTmul, map_smul,
      extendScalarsTripleTransitionOf_oneTmul R B N e (tensorMap₁₂ R B).hom
        (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B)
        (tensorIncl₁_algebraMap R B) (tensorIncl₂_algebraMap R B) n]
  | add y y' hy hy' =>
    rw [TensorProduct.add_tmul, map_add, map_add, map_add, hy, hy', map_add]

end Dictionary

/-! ### The converse -/

section Converse

/-- **An identity of composites of morphisms of modules, read at a point.**  If `u ≫ v = w`,
`u x = y` and `w x = z`, then `v y = z`. -/
theorem comp_apply_eq {T : Type u} [CommRing T] {X₀ X₁ X₂ : ModuleCat.{u} T}
    {u : X₀ ⟶ X₁} {v : X₁ ⟶ X₂} {w : X₀ ⟶ X₂} (h : u ≫ v = w) (x : X₀)
    {y : X₁} (hy : u x = y) {z : X₂} (hz : w x = z) : v y = z := by
  subst hy
  subst hz
  rw [← h, ModuleCat.comp_apply]


/-- **The cocycle condition at the level of `ModuleCat.extendScalars`**: the three base changes
of a morphism between the two extensions of scalars of `N` to `B ⊗[R] B`, along the three ring
maps into `B ⊗[R] (B ⊗[R] B)`, compose correctly.  For the transition of a module descent datum
this is `Stacks.Descent.extendScalarsTripleTransition_comp`. -/
abbrev ExtendScalarsCocycle
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ⟶
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N) : Prop :=
  extendScalarsTripleTransitionOf R B N α (tensorMap₀₁ R B).hom
        (tensorMap₀₁_comp_tensorInl R B) (tensorMap₀₁_comp_tensorInr R B) ≫
      extendScalarsTripleTransitionOf R B N α (tensorMap₁₂ R B).hom
        (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B) =
    extendScalarsTripleTransitionOf R B N α (tensorMap₀₂ R B).hom
      (tensorMap₀₂_comp_tensorInl R B) (tensorMap₀₂_comp_tensorInr R B)

/-- The transition of a module descent datum satisfies
`Stacks.Descent.ExtendScalarsCocycle`. -/
theorem extendScalarsCocycle_of_descentData (D : ModuleCat.DescentData.{u, u, u} R B) :
    ExtendScalarsCocycle R B D.module (extendScalarsTransitionOfDescentData R B D).hom :=
  extendScalarsTripleTransition_comp R B D

/-- **The cocycle condition of `ModuleCat.DescentData` from the cocycle condition at the level of
`ModuleCat.extendScalars`.**  This is the converse of
`Stacks.Descent.extendScalarsTripleTransition_comp`. -/
theorem cocycle_of_extendScalarsCocycle
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N))
    (h : ExtendScalarsCocycle R B N (extendScalarsTransitionOfEquiv R B N e).hom) :
    (ModuleCat.transition12 R B N e).comp (ModuleCat.transition01 R B N e) =
      ModuleCat.transition02 R B N e :=
  cocycle_of_oneTmul R B N e fun n ↦ tripleCocycleMap_injective R B N <|
    have key := comp_apply_eq h
      (ModuleCat.ExtendScalars.oneTmul (tensorIncl₀ R B).hom (show (N : Type u) from n))
      (extendScalarsTripleTransitionOf_oneTmul R B N e (tensorMap₀₁ R B).hom
        (tensorMap₀₁_comp_tensorInl R B) (tensorMap₀₁_comp_tensorInr R B)
        (tensorIncl₀_algebraMap R B) (tensorIncl₁_algebraMap R B) n)
      (extendScalarsTripleTransitionOf_oneTmul R B N e (tensorMap₀₂ R B).hom
        (tensorMap₀₂_comp_tensorInl R B) (tensorMap₀₂_comp_tensorInr R B)
        (tensorIncl₀_algebraMap R B) (tensorIncl₂_algebraMap R B) n)
    (extendScalarsTripleTransitionOf₁₂_tripleMap₀₁ R B N e (e (n ⊗ₜ[R] (1 : B)))).symm.trans
      (key.trans ((tripleCocycleMap_rightComm R B N (e (n ⊗ₜ[R] (1 : B)))).symm.trans
        (congrArg (fun z ↦ tripleCocycleMap R B N z)
          (transition02_tmul R B N e n 1 1)).symm))

/-- The converse of `Stacks.Descent.cocycle_of_oneTmul`: the cocycle condition of a module
descent datum holds in particular at the elements `(n ⊗ 1) ⊗ 1`. -/
theorem oneTmul_of_cocycle
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N))
    (h : (ModuleCat.transition12 R B N e).comp (ModuleCat.transition01 R B N e) =
      ModuleCat.transition02 R B N e) (n : ModuleCat.restrictModule R B N) :
    ModuleCat.transition12 R B N e (e (n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) =
      ModuleCat.transition02 R B N e ((n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) :=
  (congrArg (fun z ↦ ModuleCat.transition12 R B N e z)
      (transition01_tmul R B N e n 1 1).symm).trans
    (LinearMap.congr_fun h ((n ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)))

/-- **The cocycle condition of `ModuleCat.DescentData` and the cocycle condition at the level of
`ModuleCat.extendScalars` are equivalent.** -/
theorem extendScalarsCocycle_iff
    (e : (ModuleCat.restrictModule R B N ⊗[R] B) ≃ₗ[B ⊗[R] B]
      (B ⊗[R] ModuleCat.restrictModule R B N)) :
    ExtendScalarsCocycle R B N (extendScalarsTransitionOfEquiv R B N e).hom ↔
      (ModuleCat.transition12 R B N e).comp (ModuleCat.transition01 R B N e) =
        ModuleCat.transition02 R B N e :=
  ⟨cocycle_of_extendScalarsCocycle R B N e,
    fun h ↦ extendScalarsCocycle_of_descentData R B
      { module := N, transition := e, cocycle := h }⟩

/-- **A `B`-module together with an isomorphism of its two extensions of scalars to `B ⊗[R] B`
satisfying the cocycle condition is a module descent datum.** -/
def moduleDescentDataOfCocycle
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N)
    (h : ExtendScalarsCocycle R B N α.hom) : ModuleCat.DescentData.{u, u, u} R B where
  module := N
  transition := transitionOfExtendScalars R B N α
  cocycle := cocycle_of_extendScalarsCocycle R B N (transitionOfExtendScalars R B N α)
    (by rw [extendScalarsTransitionOfEquiv_transitionOfExtendScalars]; exact h)

/-- The module of `Stacks.Descent.moduleDescentDataOfCocycle` is `N`. -/
@[simp]
theorem moduleDescentDataOfCocycle_module
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N)
    (h : ExtendScalarsCocycle R B N α.hom) :
    (moduleDescentDataOfCocycle R B N α h).module = N :=
  rfl

/-- The transition of `Stacks.Descent.moduleDescentDataOfCocycle` is
`Stacks.Descent.transitionOfExtendScalars` of the given isomorphism. -/
@[simp]
theorem moduleDescentDataOfCocycle_transition
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N)
    (h : ExtendScalarsCocycle R B N α.hom) :
    (moduleDescentDataOfCocycle R B N α h).transition = transitionOfExtendScalars R B N α :=
  rfl

/-- **The geometric transition of `Stacks.Descent.moduleDescentDataOfCocycle` is the isomorphism
it was built from.** -/
theorem extendScalarsTransitionOfDescentData_moduleDescentDataOfCocycle
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N)
    (h : ExtendScalarsCocycle R B N α.hom) :
    extendScalarsTransitionOfDescentData R B (moduleDescentDataOfCocycle R B N α h) = α :=
  extendScalarsTransitionOfEquiv_transitionOfExtendScalars R B N α

end Converse

end Stacks.Descent

end

end
