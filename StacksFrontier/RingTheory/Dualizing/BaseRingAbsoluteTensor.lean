module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModule
public import StacksFrontier.RingTheory.Dualizing.BaseBimodule

/-!
# Tensoring over the base ring in degree zero is tensoring over the base ring

Let `R` be a commutative ring, `(B, d)` a differential graded `R`-algebra, `K` a right
differential graded module over `Dualizing.baseAlgebra R` — the base ring placed in degree zero —
and `M` a differential graded `(R, B)`-bimodule. Then the relative tensor product `K ⊗_R M` of
Tag 09LM is the absolute tensor product `K ⊗_R M` of the two underlying complexes:

`DifferentialGraded.Bimodule.tensorObj M K ≅ DifferentialGradedModule.absoluteTensorModule K
M.rightModule`.

The reason is that over the base ring placed in degree zero *both* actions are the scalar action.
On the right of `K` this is the `IsScalarTower` field of a differential graded module
(`DifferentialGradedModule.op_algebraMap_smul`); on the left of `M` it is forced, because by
`Dualizing.baseLeftAction_unique` the scalar action is the only left action of
`Dualizing.baseAlgebra R` there — no hypothesis on `M` is needed. So the balancing relation that
the relative tensor product imposes is `(r • x) ⊗ y = x ⊗ (r • y)`, which already holds in the
tensor product over `R`, and the two tensor products agree.

This generalises `DifferentialGraded.absBaseBalanceIso`, which is the case in which `K` is the
regular module of a differential graded `R`-algebra read over `R` in degree zero. Here the left
factor is an arbitrary differential graded module.

## Main definitions

* `Dualizing.baseAbsBalanced`: the pure tensor `(x, y) ↦ x ⊗ y` as a balanced bilinear map, and
  `Dualizing.baseAbsForward`, `Dualizing.baseAbsInverse`: the two homomorphisms of differential
  graded `B`-modules it produces.

## Main results

* `Dualizing.leftAction_v_coe_eq_smul`: **the left action of the base ring in degree zero on an
  arbitrary bimodule over it is scalar multiplication**, in the shape the balancing relation of
  Tag 09LM is phrased in.
* `Dualizing.baseAbsBalanceIso`: **the relative tensor product over the base ring in degree zero
  is the absolute tensor product of the underlying complexes.**

## Implementation notes

*Why the right action is reached through `algebraMap`.* Instance synthesis for a right action by
`(Dualizing.baseAlgebra R).A` does not succeed at that concrete term — the field projection
carrying the module structure is not found — which is the obstruction recorded in
`StacksFrontier/RingTheory/Koszul/BaseCellFiltration.lean`. So the formula
`DifferentialGradedModule.op_algebraMap_smul` is stated with the algebra still a variable and used
here inside a goal that already carries the instance, through `congrArg` rather than `rw`: the
scalar in the goal is the coercion of a homogeneous element, which is only definitionally the
image of `algebraMap`.

*Why no bimodule map is needed.* `Dualizing.bimodule_eq_baseBimodule` makes every bimodule over
the base ring equal to the one attached to its right module, so the left action never has to be
fixed up; `Dualizing.leftAction_v_coe_eq_smul` reads the formula off that uniqueness directly.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product with a differential graded bimodule, and
  [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) the notion of a differential graded
  bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGradedModule
open scoped TensorProduct DirectSum

universe u

namespace Dualizing

attribute [local instance] DifferentialGradedModule.absModRightModule
  DifferentialGradedModule.absModRightScalarTower
  DifferentialGradedModule.absModDecomposition

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, u} R)

/-! ### The left action of the base ring in degree zero -/

/-- **The left action of the base ring in degree zero is scalar multiplication**, on every
differential graded `(R, B)`-bimodule. The scalar action is the only left action there, by
`Dualizing.baseLeftAction_unique`, so this needs no hypothesis on the bimodule; it is stated at an
arbitrary target index, which is the shape the balancing relation of Tag 09LM uses. -/
theorem leftAction_v_coe_eq_smul (M : Bimodule (baseAlgebra R) B) {n : ℤ}
    (a : (baseAlgebra R).grading n) (p q : ℤ) (h : p + n = q) (x : M.rightModule.grading p) :
    ((show M.rightModule.grading q from
        ((M.leftAction.1.action n a).v p q h) x) : M.rightModule.M) =
      (a : R) • (x : M.rightModule.M) := by
  rw [baseLeftAction_unique M.rightModule.toCochainComplex M.leftAction.1]
  exact baseLeftAction_v_coe B M.rightModule a p q h x

/-! ### The relative tensor product over the base ring in degree zero -/

/-- The pure tensor `(x, y) ↦ x ⊗ y`, as a balanced bilinear map over the base ring in degree
zero. Both actions being the scalar action, the balancing relation is `R`-bilinearity. -/
def baseAbsBalanced (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) :
    Bimodule.BalancedBilinearMap K M (absoluteTensorModule K M.rightModule) where
  toLinearMap := TensorProduct.mk R K.M M.rightModule.M
  map_grading p q x y := absModTmul_mem K M.rightModule p q _ _ x.property y.property
  map_d p x y := absModDifferential_tmul K M.rightModule p x y
  balance p q n x y a := by
    rw [leftAction_v_coe_eq_smul B M a q (q + n) (by omega) y]
    exact (congrArg
      (fun z : K.M => (TensorProduct.mk R K.M M.rightModule.M z) (y : M.rightModule.M))
      (op_algebraMap_smul K (a : R) (x : K.M))).trans
      (TensorProduct.smul_tmul _ _ _)
  map_right x y b := (absMod_smul_tmul K M.rightModule x y b).symm

/-- The relative tensor product of `K` with `M` over the base ring placed in degree zero. -/
abbrev baseAbsRelative (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) : DifferentialGradedModule.{u, u, u} B :=
  Bimodule.tensorObj M K

/-- The universal pure tensors into the relative tensor product over the base ring in degree
zero. -/
abbrev baseAbsPure (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) :
    Bimodule.BalancedBilinearMap K M (baseAbsRelative B K M) :=
  Bimodule.tensorPure M K

/-- The universal pure tensors, as a bilinear map. -/
def baseAbsPureBilinear (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) :
    K.M →ₗ[R] M.rightModule.M →ₗ[R] (baseAbsRelative B K M).M :=
  (baseAbsPure B K M).toLinearMap

/-- The identification, as a homomorphism out of the relative tensor product: the unique
homomorphism of differential graded `B`-modules sending `x ⊗ y` to `x ⊗ y`. -/
def baseAbsForward (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) :
    baseAbsRelative B K M ⟶ absoluteTensorModule K M.rightModule :=
  ((Bimodule.tensorDGFunctor M).universal K
    (absoluteTensorModule K M.rightModule) (baseAbsBalanced B K M)).choose

/-- The map `baseAbsForward` sends the pure tensor `x ⊗ y` of the relative tensor product to the
pure tensor `x ⊗ y` of the absolute tensor product. -/
theorem baseAbsForward_pure (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) (x : K.M) (y : M.rightModule.M) :
    (baseAbsForward B K M).toFun (baseAbsPureBilinear B K M x y) =
      (x ⊗ₜ[R] y : K.M ⊗[R] M.rightModule.M) :=
  ((Bimodule.tensorDGFunctor M).universal K
    (absoluteTensorModule K M.rightModule) (baseAbsBalanced B K M)).choose_spec.1 x y

/-- The inverse of the identification, as a homomorphism of differential graded `B`-modules. -/
def baseAbsInverse (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) :
    absoluteTensorModule K M.rightModule ⟶ baseAbsRelative B K M where
  toFun := TensorProduct.lift (baseAbsPureBilinear B K M)
  map_smul z b := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul x y =>
      rw [absMod_smul_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      exact (baseAbsPure B K M).map_right x y b
  map_grading n z hz := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, x, y, hx, hy, rfl, rfl⟩ := hz
      rw [TensorProduct.lift.tmul]
      exact (baseAbsPure B K M).map_grading p q ⟨x, hx⟩ ⟨y, hy⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  map_d := by
    refine LinearMap.ext fun z => ?_
    change TensorProduct.lift (baseAbsPureBilinear B K M)
        (absModDifferential K M.rightModule z) =
      (baseAbsRelative B K M).d (TensorProduct.lift (baseAbsPureBilinear B K M) z)
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      induction x using DirectSum.Decomposition.inductionOn K.grading with
      | zero => simp
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
      | @homogeneous p x =>
        rw [absModDifferential_tmul, map_add, map_zsmul, TensorProduct.lift.tmul,
          TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        exact ((baseAbsPure B K M).map_d p x y).symm

/-- **The relative tensor product over the base ring in degree zero is the absolute tensor
product.** For an arbitrary right differential graded module `K` over the base ring placed in
degree zero and an arbitrary differential graded `(R, B)`-bimodule `M`, the relative tensor
product `K ⊗_R M` of Tag 09LM is the tensor product over `R` of the two underlying complexes. -/
def baseAbsBalanceIso (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R))
    (M : Bimodule (baseAlgebra R) B) :
    baseAbsRelative B K M ≅ absoluteTensorModule K M.rightModule where
  hom := baseAbsForward B K M
  inv := baseAbsInverse B K M
  hom_inv_id := Bimodule.tensorObj_hom_ext M K _ _ fun x y =>
    (congrArg (baseAbsInverse B K M).toFun (baseAbsForward_pure B K M x y)).trans
      (TensorProduct.lift.tmul (f' := baseAbsPureBilinear B K M) x y)
  inv_hom_id := by
    refine DifferentialGradedModule.Hom.ext (TensorProduct.ext' fun x y => ?_)
    change (baseAbsForward B K M).toFun
      (TensorProduct.lift (baseAbsPureBilinear B K M) (x ⊗ₜ[R] y)) = x ⊗ₜ[R] y
    rw [TensorProduct.lift.tmul]
    exact baseAbsForward_pure B K M x y

end Dualizing

end
