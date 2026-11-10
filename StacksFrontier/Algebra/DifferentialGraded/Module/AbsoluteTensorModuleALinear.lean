module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra

/-!
# The bigraded decomposition of `L ⊗_R N` is `A`-linear

Let `R` and `A` be commutative rings with `A` an `R`-algebra, let `(A₁, d)` be a differential
graded `R`-algebra, let `L` be a right differential graded `A₁`-module and let `N` be a right
differential graded module over `A` placed in degree zero. Then
`DifferentialGradedModule.absoluteTensorModule L N` is again a differential graded module over `A`
in degree zero, so each of its homogeneous components is an `A`-module
(`DifferentialGradedModule.degreeZeroComponentModule`), and this file upgrades the bigraded
decomposition of that component from `R`-linear to `A`-linear:

`⨁_{p + q = n} L^p ⊗_R N^q ≃ₗ[A] (L ⊗_R N)^n`.

The `A`-action on the summand `L^p ⊗_R N^q` is the one on the second factor, matching the action
on the target, where `a` acts as the right action of `a` on the `N`-factor of a pure tensor.

The same `A`-action makes each summand the base change of nothing: `L^p ⊗_R N^q` is `A`-linearly
`(A ⊗_R L^p) ⊗_A N^q`, which is Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange` read with the base-changed factor on the
left. That is the degreewise shape taken by `CochainComplex.extendScalarsLarge` followed by
`CochainComplex.tensorRightLarge`, which is the form the derived change-of-rings API of Tag 06Y6
consumes.

## Main definitions

* `DifferentialGradedModule.absModSummandModule`: the `A`-module structure on a bigraded summand
  `L^p ⊗_R N^q`, acting on the second factor.
* `DifferentialGradedModule.absModComponentAEquiv`: **the bigraded decomposition of the degree-`n`
  part of `L ⊗_R N`, as an `A`-linear equivalence.**
* `DifferentialGradedModule.absModSummandBaseChange`: **the bigraded summand as a base change**,
  `(A ⊗_R L^p) ⊗_A N^q ≃ₗ[A] L^p ⊗_R N^q`.

## Main results

* `DifferentialGradedModule.absModSummand_smul_tmul`: the `A`-action on a pure tensor of a
  summand.
* `DifferentialGradedModule.absModComponentAEquiv_lof_tmul`: the decomposition on a pure tensor.
* `DifferentialGradedModule.absModSummandBaseChange_tmul`: `(a ⊗ x) ⊗ y ↦ x ⊗ a y`.

## Implementation notes

*Why a parallel layer and not a reuse.* Everything in
`StacksFrontier/Algebra/DifferentialGraded/Module/AbsoluteTensorModule.lean` is stated over the base
ring `R`, because the left factor there is a module over an arbitrary differential graded algebra
and carries no `A`-action at all. The `A`-linearity below is therefore a second layer over the
same maps rather than a generalisation of them: `absModComponentAEquiv` has the same underlying
function as `DifferentialGradedModule.absModComponentEquiv`, with the `A`-linearity proved by
induction over the direct sum and the spanning pure tensors.

*The two scalar-tower side conditions.* The `A`-module structure
`DifferentialGradedModule.degreeZeroComponentModule` on a homogeneous component is the right
action of `A` read through commutativity, so the compatibilities `IsScalarTower R A N^q` and
`SMulCommClass R A N^q` that the tensor product needs are not automatic; they are
`DifferentialGradedModule.degreeZeroComponent_isScalarTower` and
`DifferentialGradedModule.degreeZeroComponent_smulCommClass`, both read off the corresponding
properties of the right action on the whole module.

*Universes.* The differential graded algebras and their modules live in a single universe `u`,
following the encoding of Tag 09JJ used throughout this chapter.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) is the notion of a
  differential graded module, and [Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) the
  derived change-of-rings tensor product whose degreewise shape the base change below matches.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] DifferentialGradedModule.degreeZeroOppositeModule
  DifferentialGradedModule.degreeZeroOppositeModule_isScalarTower
  DifferentialGradedModule.degreeZeroComponentModule

/-! ### The two scalar-tower side conditions -/

/-- The `R`-action and the `A`-action on a homogeneous component of a differential graded module
over `A` in degree zero commute: on the whole module they are the scalar action and the right
action, which commute. -/
theorem degreeZeroComponent_smulCommClass
    (N : DifferentialGradedModule.{u, u, u} (degreeZero R A)) (q : ℤ) :
    SMulCommClass R A (N.grading q) :=
  ⟨fun r a x => Subtype.ext (smul_comm (MulOpposite.op a) r (x : N.M)).symm⟩

/-- The `A`-action on a homogeneous component of a differential graded module over `A` in degree
zero is compatible with the `R`-action on `A`. -/
theorem degreeZeroComponent_isScalarTower
    (N : DifferentialGradedModule.{u, u, u} (degreeZero R A)) (q : ℤ) :
    IsScalarTower R A (N.grading q) := by
  refine ⟨fun r a x => Subtype.ext ?_⟩
  change MulOpposite.op (r • a) • (x : N.M) = r • (MulOpposite.op a • (x : N.M))
  rw [MulOpposite.op_smul]
  exact smul_assoc r (MulOpposite.op a) (x : N.M)

attribute [local instance] degreeZeroComponent_smulCommClass degreeZeroComponent_isScalarTower

/-- The `A`-action on a homogeneous component of a differential graded module over `A` in degree
zero, on an element: it is the right action of `A`. The module is kept a variable, because the
field projection carrying the opposite action is not found by instance synthesis at a concrete
differential graded module over `DifferentialGradedAlgebra.degreeZero R A`; this is the
obstruction recorded in `StacksFrontier/RingTheory/Koszul/BaseCellFiltration.lean`. -/
theorem degreeZeroComponent_smul_coe
    (M : DifferentialGradedModule.{u, u, u} (degreeZero R A)) (n : ℤ) (a : A)
    (x : M.grading n) :
    ((a • x : M.grading n) : M.M) = MulOpposite.op a • (x : M.M) := rfl

attribute [local instance] absModRightModule absModRightScalarTower absModDecomposition

variable {A₁ : DifferentialGradedAlgebra.{u, u} R}
  (L : DifferentialGradedModule.{u, u, u} A₁)
  (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))

/-! ### The two module structures, named -/

/-- The right `A`-action on `L ⊗_R N`, named at the ring `A` itself rather than at
`(DifferentialGradedAlgebra.degreeZero R A).A`, so that instance synthesis finds it at the
concrete module `DifferentialGradedModule.absoluteTensorModule L N`. -/
@[instance_reducible]
def absModOppositeModule : Module Aᵐᵒᵖ (L.M ⊗[R] N.M) := absModRightModule L N

attribute [local instance] absModOppositeModule

/-- The `A`-module structure on the degree-`n` part of `L ⊗_R N`, named so that instance
synthesis finds it: `DifferentialGradedModule.degreeZeroComponentModule` would have to be
matched against a projection of a structure literal. -/
@[instance_reducible]
def absModGradingModule (n : ℤ) : Module A ((absoluteTensorModule L N).grading n) :=
  degreeZeroComponentModule (R := R) (A := A) (absoluteTensorModule L N) n

attribute [local instance] absModGradingModule

/-! ### The `A`-module structure on a bigraded summand -/

/-- The `A`-action on the bigraded summand `L^p ⊗_R N^q`, on the second factor. -/
@[instance_reducible]
def absModSummandModule (p q : ℤ) : Module A (L.grading p ⊗[R] N.grading q) :=
  (TensorProduct.comm R (L.grading p) (N.grading q)).toAddEquiv.module A

attribute [local instance] absModSummandModule

/-- The `R`- and `A`-actions on the bigraded summand `L^p ⊗_R N^q` form a scalar tower. -/
theorem absModSummand_isScalarTower (p q : ℤ) :
    IsScalarTower R A (L.grading p ⊗[R] N.grading q) :=
  (TensorProduct.comm R (L.grading p) (N.grading q)).isScalarTower A

attribute [local instance] absModSummand_isScalarTower

/-- The `A`-action on the bigraded summand `L^p ⊗_R N^q` acts on the second factor of a pure
tensor: `a • (x ⊗ y) = x ⊗ (a • y)`. -/
theorem absModSummand_smul_tmul (p q : ℤ) (a : A) (x : L.grading p) (y : N.grading q) :
    a • (x ⊗ₜ[R] y : L.grading p ⊗[R] N.grading q) = x ⊗ₜ[R] (a • y) := by
  change (TensorProduct.comm R (N.grading q) (L.grading p))
    (a • (TensorProduct.comm R (L.grading p) (N.grading q)) (x ⊗ₜ[R] y)) = _
  simp [TensorProduct.smul_tmul']

/-! ### The bigraded decomposition is `A`-linear -/

/-- The inclusion of a single bigraded summand into the direct sum is `A`-linear, on a pure
tensor. -/
theorem absModComponents_smul_of (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) (a : A)
    (z : L.grading pq.val.1 ⊗[R] N.grading pq.val.2) :
    a • (DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦
          L.grading pq.val.1 ⊗[R] N.grading pq.val.2) pq z) =
      DirectSum.of (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦
        L.grading pq.val.1 ⊗[R] N.grading pq.val.2) pq (a • z) := by
  simpa only [DirectSum.lof_eq_of] using ((DirectSum.lof A {pq : ℤ × ℤ // pq.1 + pq.2 = n}
    (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦
      L.grading pq.val.1 ⊗[R] N.grading pq.val.2) pq).map_smul a z).symm

/-- The `A`-action on the degree-`n` part of `L ⊗_R N`: it is the right action of `A`. -/
theorem absModGrading_smul_coe (n : ℤ) (a : A)
    (z : (absoluteTensorModule L N).grading n) :
    ((a • z : (absoluteTensorModule L N).grading n) : L.M ⊗[R] N.M) =
      MulOpposite.op a • (z : L.M ⊗[R] N.M) :=
  degreeZeroComponent_smul_coe (absoluteTensorModule L N) n a z

/-- The `A`-action on the degree-`n` part of `L ⊗_R N`, on a pure tensor of homogeneous
elements: it moves onto the second factor. -/
theorem absModGrading_smul_tmul (p q : ℤ) (a : A) (x : L.grading p) (y : N.grading q) :
    MulOpposite.op a • ((x : L.M) ⊗ₜ[R] (y : N.M)) =
      (x : L.M) ⊗ₜ[R] ((a • y : N.grading q) : N.M) :=
  (absMod_smul_tmul L N (x : L.M) (y : N.M) a).trans
    (congrArg (fun w : N.M => ((x : L.M) ⊗ₜ[R] w))
      (degreeZeroComponent_smul_coe N q a y).symm)

/-- **The bigraded decomposition of the degree-`n` part of `L ⊗_R N` is `A`-linear.** The
underlying function is the `R`-linear `DifferentialGradedModule.absModComponentEquiv`; what is
proved here is that it carries the `A`-action on the second factor of each summand to the right
action of `A` on `L ⊗_R N`. -/
def absModComponentAEquiv (n : ℤ) :
    absModComponents L N n ≃ₗ[A] (absoluteTensorModule L N).grading n where
  toFun := absModComponentEquiv L N n
  map_add' := map_add _
  map_smul' a z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
    | of pq z =>
      rw [absModComponents_smul_of L N n pq a z]
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [smul_add, map_add, hz, hw]
      | tmul x y =>
        apply Subtype.ext
        simp only [RingHom.id_apply]
        rw [absModGrading_smul_coe L N n a]
        simp only [← DirectSum.lof_eq_of (R := R)]
        rw [absModSummand_smul_tmul L N pq.val.1 pq.val.2 a x y,
          show ((absModComponentEquiv L N n
              (DirectSum.lof R _ _ pq ((x : L.grading pq.val.1) ⊗ₜ[R] (a • y))) :
              absModGrading L N n) : L.M ⊗[R] N.M) =
            ((x : L.M) ⊗ₜ[R] ((a • y : N.grading pq.val.2) : N.M)) from
          (absModComponentEquiv_coe L N n _).trans
            (absModFiberMap_lof_tmul L N n pq x (a • y)),
          show ((absModComponentEquiv L N n
              (DirectSum.lof R _ _ pq ((x : L.grading pq.val.1) ⊗ₜ[R] y)) :
              absModGrading L N n) : L.M ⊗[R] N.M) =
            ((x : L.M) ⊗ₜ[R] (y : N.M)) from
          (absModComponentEquiv_coe L N n _).trans
            (absModFiberMap_lof_tmul L N n pq x y)]
        exact (absModGrading_smul_tmul L N pq.val.1 pq.val.2 a x y).symm
  invFun := (absModComponentEquiv L N n).symm
  left_inv := (absModComponentEquiv L N n).left_inv
  right_inv := (absModComponentEquiv L N n).right_inv

/-- The underlying element of `L ⊗_R N` of the image of `z` under `absModComponentAEquiv` is
`absModFiberMap L N n z`. -/
@[simp] theorem absModComponentAEquiv_coe_apply (n : ℤ) (z : absModComponents L N n) :
    ((absModComponentAEquiv L N n z : (absoluteTensorModule L N).grading n) :
      L.M ⊗[R] N.M) = absModFiberMap L N n z := rfl

/-- `absModComponentAEquiv` sends the pure tensor `x ⊗ y` in the summand indexed by `pq` to
`x ⊗ y` in `L ⊗_R N`. -/
theorem absModComponentAEquiv_lof_tmul (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (x : L.grading pq.val.1) (y : N.grading pq.val.2) :
    ((absModComponentAEquiv L N n (DirectSum.lof R _ _ pq (x ⊗ₜ[R] y)) :
        (absoluteTensorModule L N).grading n) : L.M ⊗[R] N.M) =
      ((x : L.M) ⊗ₜ[R] (y : N.M)) := by
  rw [absModComponentAEquiv_coe_apply, absModFiberMap_lof_tmul]

/-! ### The bigraded summand as a base change -/

/-- The interchange of the two factors of a bigraded summand, as an `A`-linear equivalence: the
`A`-action is on the `N`-factor on both sides. -/
def absModSummandComm (p q : ℤ) :
    N.grading q ⊗[R] L.grading p ≃ₗ[A] L.grading p ⊗[R] N.grading q where
  toFun := TensorProduct.comm R (N.grading q) (L.grading p)
  map_add' := map_add _
  map_smul' a z := by
    simp only [RingHom.id_apply]
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
    | tmul y x =>
      rw [TensorProduct.smul_tmul' a y (x : L.grading p), TensorProduct.comm_tmul,
        TensorProduct.comm_tmul, absModSummand_smul_tmul L N p q a x y]
  invFun := (TensorProduct.comm R (N.grading q) (L.grading p)).symm
  left_inv := (TensorProduct.comm R (N.grading q) (L.grading p)).left_inv
  right_inv := (TensorProduct.comm R (N.grading q) (L.grading p)).right_inv

/-- `absModSummandComm` sends `y ⊗ x` to `x ⊗ y`. -/
@[simp] theorem absModSummandComm_tmul (p q : ℤ) (y : N.grading q) (x : L.grading p) :
    absModSummandComm L N p q (y ⊗ₜ[R] x) = x ⊗ₜ[R] y := rfl

/-- **The bigraded summand `L^p ⊗_R N^q` is the base change `(A ⊗_R L^p) ⊗_A N^q`.** This is
Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange` read with the base-changed factor
on the left, which is the degreewise shape of `CochainComplex.extendScalarsLarge` followed by
`CochainComplex.tensorRightLarge`. -/
def absModSummandBaseChange (p q : ℤ) :
    (A ⊗[R] L.grading p) ⊗[A] N.grading q ≃ₗ[A] L.grading p ⊗[R] N.grading q :=
  ((TensorProduct.comm A (A ⊗[R] L.grading p) (N.grading q)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A
      (N.grading q) (L.grading p))).trans
    (absModSummandComm L N p q)

/-- `absModSummandBaseChange` sends `(a ⊗ x) ⊗ y` to `x ⊗ (a • y)`. -/
theorem absModSummandBaseChange_tmul (p q : ℤ) (a : A) (x : L.grading p) (y : N.grading q) :
    absModSummandBaseChange L N p q ((a ⊗ₜ[R] x) ⊗ₜ[A] y) = x ⊗ₜ[R] (a • y) := by
  simp only [absModSummandBaseChange, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, absModSummandComm_tmul]

/-- **Naturality of the base-change comparison in the base-changed variable.** This is the
first-variable analogue of `TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange`,
which Mathlib has only in the second variable: the comparison carries `(A ⊗ g) ⊗ 1` to `g ⊗ 1`.
It is what the `d₁` leg of the total-complex differential square needs: on the
`CochainComplex.extendScalarsLarge` side that leg is `A ⊗ d_L` tensored with the identity, and
the comparison lets it pass to `d_L ⊗ 1`.

It is stated on pure tensors rather than as an equality of linear maps because the two composites
have different scalar rings in their types — `LinearMap.rTensor` over `A` on the left and
`TensorProduct.map` over `R` on the right — so an equation between them does not typecheck
without a further transport. -/
theorem absModSummandBaseChange_baseChange_tmul (p p' q : ℤ)
    (g : L.grading p →ₗ[R] L.grading p') (a : A) (x : L.grading p) (y : N.grading q) :
    absModSummandBaseChange L N p' q
        ((LinearMap.baseChange A g) (a ⊗ₜ[R] x) ⊗ₜ[A] y) = (g x) ⊗ₜ[R] (a • y) := by
  rw [LinearMap.baseChange_tmul, absModSummandBaseChange_tmul]

/-- **Naturality of the base-change comparison in the other variable.** For an `A`-linear map
`h : N^q → N^{q'}`, the comparison carries `1 ⊗ h` to `1 ⊗ h`, the scalar `a` crossing `h` by
`A`-linearity. This is the `d₂` leg of the total-complex differential square: on the
`CochainComplex.tensorRightLarge` side that leg is the identity tensored with the differential of
`N`, and the comparison lets it pass to `1 ⊗ d_N`, since the differential of a differential graded
module over `A` in degree zero is `A`-linear on each component
(`DifferentialGradedModule.degreeZeroDifferential`). -/
theorem absModSummandBaseChange_lTensor_tmul (p q q' : ℤ)
    (h : N.grading q →ₗ[A] N.grading q') (a : A) (x : L.grading p) (y : N.grading q) :
    absModSummandBaseChange L N p q' ((a ⊗ₜ[R] x) ⊗ₜ[A] (h y)) = x ⊗ₜ[R] (h (a • y)) := by
  rw [absModSummandBaseChange_tmul, map_smul]

/-- The base-change comparison on a pure tensor, read in `L ⊗_R N` through the bigraded
decomposition: `(a ⊗ x) ⊗ y` goes to the pure tensor `x ⊗ a y`. -/
theorem absModSummandBaseChange_tmul_coe (p q : ℤ) (a : A) (x : L.grading p)
    (y : N.grading q) :
    ((TensorProduct.map (L.grading p).subtype (N.grading q).subtype)
        (absModSummandBaseChange L N p q ((a ⊗ₜ[R] x) ⊗ₜ[A] y)) : L.M ⊗[R] N.M) =
      MulOpposite.op a • ((x : L.M) ⊗ₜ[R] (y : N.M)) := by
  rw [absModSummandBaseChange_tmul, TensorProduct.map_tmul]
  exact (absModGrading_smul_tmul L N p q a x y).symm

/-! ### The algebra instance used by extension of scalars -/

/-- **The algebra structure `CochainComplex.extendScalarsLarge` builds from a ring homomorphism is
the ambient one**, when that homomorphism is the structure map. `ModuleCat.extendScalars` is
defined for a bare ring homomorphism `f` and uses `f.toAlgebra`, which is *not* definitionally the
ambient `Algebra R A` instance even at `f = algebraMap R A`; the two are nevertheless equal, so
`DifferentialGradedAlgebra.degreeZero R A` — and hence the type of differential graded modules
over it — is literally the same under both.

This is recorded because every statement in this file is generic in the `Algebra R A` instance
and may therefore be instantiated at `f.toAlgebra` directly, with no transport; the equality below
is only needed to connect such an instantiation back to a statement about the ambient instance. -/
theorem degreeZero_algebraMap_toAlgebra (R A : Type u) [CommRing R] [CommRing A]
    [alg : Algebra R A] :
    @degreeZero R _ A _ (algebraMap R A).toAlgebra = @degreeZero R _ A _ alg :=
  congrArg _ (Algebra.algebra_ext _ _ fun _ => rfl)

/-! ### The forward summand map of the total-complex comparison -/

/-- The inclusion of a bigraded summand into the direct sum, as an `A`-linear map. -/
def absModSummandLof (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) :
    (L.grading pq.val.1 ⊗[R] N.grading pq.val.2) →ₗ[A] absModComponents L N n :=
  DirectSum.lof A {pq : ℤ × ℤ // pq.1 + pq.2 = n}
    (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦
      L.grading pq.val.1 ⊗[R] N.grading pq.val.2) pq

/-- The `A`-linear inclusion of a bigraded summand is the `R`-linear one: both are
`DirectSum.of`. -/
theorem absModSummandLof_eq_lof (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (z : L.grading pq.val.1 ⊗[R] N.grading pq.val.2) :
    absModSummandLof L N n pq z = DirectSum.lof R _ _ pq z := by
  rw [absModSummandLof, DirectSum.lof_eq_of, DirectSum.lof_eq_of]

/-- **The forward summand map of the total-complex comparison.** On the bigraded summand
`(A ⊗_R L^p) ⊗_A N^q` of `CochainComplex.extendScalarsLarge` followed by
`CochainComplex.tensorRightLarge` it is the base-change comparison, followed by the inclusion into
the bigraded direct sum, followed by the `A`-linear bigraded decomposition — all three `A`-linear,
so this is the map that a `HomologicalComplex.mapBifunctorDesc` over `ModuleCat A` consumes. -/
def absModSummandToGrading (p q n : ℤ) (h : p + q = n) :
    ((A ⊗[R] L.grading p) ⊗[A] N.grading q) →ₗ[A] (absoluteTensorModule L N).grading n :=
  (absModComponentAEquiv L N n).toLinearMap ∘ₗ
    absModSummandLof L N n ⟨(p, q), h⟩ ∘ₗ (absModSummandBaseChange L N p q).toLinearMap

/-- The forward summand map on a pure tensor: `(a ⊗ x) ⊗ y` goes to the pure tensor `x ⊗ a y`. -/
theorem absModSummandToGrading_tmul (p q n : ℤ) (h : p + q = n) (a : A) (x : L.grading p)
    (y : N.grading q) :
    ((absModSummandToGrading L N p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] y) :
        (absoluteTensorModule L N).grading n) : L.M ⊗[R] N.M) =
      (x : L.M) ⊗ₜ[R] ((a • y : N.grading q) : N.M) := by
  simp only [absModSummandToGrading, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    absModSummandBaseChange_tmul]
  exact absModComponentAEquiv_lof_tmul L N n ⟨(p, q), h⟩ x (a • y)

/-! ### The differential square, on a bigraded summand -/

/-- The `d₁` leg of the differential square: the differential of the left factor, base changed to
`A`, followed by the forward summand map, is the forward summand map followed by the first half of
the differential of `L ⊗_R N`. -/
theorem absModSummandToGrading_d_one (p q n : ℤ) (h : p + q = n) (a : A) (x : L.grading p)
    (y : N.grading q) :
    ((absModSummandToGrading L N (p + 1) q (n + 1) (by omega)
        ((LinearMap.baseChange A (L.gradedDifferential p)) (a ⊗ₜ[R] x) ⊗ₜ[A] y) :
        (absoluteTensorModule L N).grading (n + 1)) : L.M ⊗[R] N.M) =
      (L.d (x : L.M)) ⊗ₜ[R] ((a • y : N.grading q) : N.M) := by
  rw [LinearMap.baseChange_tmul,
    absModSummandToGrading_tmul L N (p + 1) q (n + 1) (by omega) a _ y]
  rfl

/-- The `d₂` leg of the differential square: the differential of the right factor, followed by the
forward summand map, is the forward summand map followed by the second half of the differential of
`L ⊗_R N`. The scalar crosses the differential because the differential of a differential graded
module over `A` in degree zero is `A`-linear on each component. -/
theorem absModSummandToGrading_d_two (p q n : ℤ) (h : p + q = n) (a : A) (x : L.grading p)
    (y : N.grading q) :
    ((absModSummandToGrading L N p (q + 1) (n + 1) (by omega)
        ((a ⊗ₜ[R] x) ⊗ₜ[A] (degreeZeroDifferential (A := A) N q y)) :
        (absoluteTensorModule L N).grading (n + 1)) : L.M ⊗[R] N.M) =
      (x : L.M) ⊗ₜ[R] N.d (((a • y : N.grading q) : N.M)) := by
  rw [absModSummandToGrading_tmul L N p (q + 1) (n + 1) (by omega) a x _,
    ← map_smul (degreeZeroDifferential (A := A) N q) a y]
  rfl

/-- **The differential square of the total-complex comparison, on a bigraded summand.** The
differential of `L ⊗_R N` applied to the image of a pure tensor is the sum of the two legs, the
second carrying the Koszul sign `(-1)^p`. This is the whole content of the square; what a
`HomologicalComplex.mapBifunctor` computation adds to it is only the bookkeeping of the
bigraded summands, and the signs it produces are `ComplexShape.ε₁ = 1` and
`ComplexShape.ε₂ = (-1)^p`, matching the two terms below. -/
theorem absModSummandToGrading_differential (p q n : ℤ) (h : p + q = n) (a : A)
    (x : L.grading p) (y : N.grading q) :
    absModDifferential L N
        ((absModSummandToGrading L N p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] y) :
          (absoluteTensorModule L N).grading n) : L.M ⊗[R] N.M) =
      ((absModSummandToGrading L N (p + 1) q (n + 1) (by omega)
          ((LinearMap.baseChange A (L.gradedDifferential p)) (a ⊗ₜ[R] x) ⊗ₜ[A] y) :
          (absoluteTensorModule L N).grading (n + 1)) : L.M ⊗[R] N.M) +
        (p.negOnePow : ℤ) •
          ((absModSummandToGrading L N p (q + 1) (n + 1) (by omega)
            ((a ⊗ₜ[R] x) ⊗ₜ[A] (degreeZeroDifferential (A := A) N q y)) :
            (absoluteTensorModule L N).grading (n + 1)) : L.M ⊗[R] N.M) := by
  rw [absModSummandToGrading_tmul L N p q n h a x y,
    absModSummandToGrading_d_one L N p q n h a x y,
    absModSummandToGrading_d_two L N p q n h a x y]
  exact absModDifferential_tmul L N p x _

/-- **The differential square of the total-complex comparison, as an identity of linear maps.**
This is `DifferentialGradedModule.absModSummandToGrading_differential` repackaged: the
differential of `L ⊗_R N` precomposed with the forward summand map is the sum of the two legs,
the second carrying the Koszul sign `(-1)^p`. The two legs are `LinearMap.rTensor` of the base
changed differential of `L` and `LinearMap.lTensor` of the differential of `N`, which is exactly
what the lifted monoidal structure on `ModuleCat A` produces for
`HomologicalComplex.mapBifunctor.d₁` and `d₂`.

It is stated here, away from `ModuleCat`, because the coercions there prevent the two-step tensor
extensionality from descending into the base-changed factor. -/
theorem absModSummandToGrading_differential_linear (p q n : ℤ) (h : p + q = n) :
    (degreeZeroDifferential (A := A) (absoluteTensorModule L N) n) ∘ₗ
        (absModSummandToGrading L N p q n h) =
      (absModSummandToGrading L N (p + 1) q (n + 1) (by omega)) ∘ₗ
          LinearMap.rTensor (N.grading q)
            (LinearMap.baseChange A (L.gradedDifferential p)) +
        (p.negOnePow : ℤ) • ((absModSummandToGrading L N p (q + 1) (n + 1) (by omega)) ∘ₗ
          LinearMap.lTensor (A ⊗[R] L.grading p) (degreeZeroDifferential (A := A) N q)) := by
  refine TensorProduct.ext' fun w y => ?_
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, LinearMap.smul_apply,
      hu, hv]
  | tmul a x =>
    exact Subtype.ext (absModSummandToGrading_differential L N p q n h a x y)

end DifferentialGradedModule

end
