module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictRight

/-! # Base change of a differential graded module over the base-changed algebra

Let `R → R'` be a map of commutative rings, let `(A, d)` be a differential graded `R`-algebra and
let `A' = A ⊗_R R'` be its base change. For a differential graded `A`-module `M` the base change
`M ⊗_R R'` is a differential graded `A'`-module: the element `a ⊗ s` of `A'` acts by `a` on the
first factor and by `s` on the second,

`(m ⊗ t) · (a ⊗ s) = (m · a) ⊗ (t s)`,

and the canonical map `c_M : M ⊗_R R' → M ⊗_A A'` of the proof of Stacks 0BYZ is an isomorphism
of differential graded `A'`-modules. That `A'`-linearity is what this file adds: the same
identification was available over `R'` alone, as
`DifferentialGraded.Bimodule.baseChangeTensorIso`, because the tree had no differential graded
module over a graded tensor product of two algebras.

## Main definitions

* `DifferentialGradedModule.baseChangeAct`: the right action of `A' = A ⊗_R R'` on `M ⊗_R R'`,
  and `DifferentialGradedModule.baseChangeActRingHom`: that action as a homomorphism out of the
  opposite algebra, which is what makes it an action.
* `DifferentialGradedModule.baseChangeAbsoluteTensor`: **`M ⊗_R R'` as a differential graded
  `A ⊗_R R'`-module.**
* `DifferentialGraded.Bimodule.baseChangeTensorForward`: the canonical map `c_M`, over `A'`, as a
  homomorphism of differential graded `A'`-modules.

## Main results

* `DifferentialGradedAlgebra.baseChange_tmul_mul_tmul`: multiplication in `A ⊗_R R'` carries no
  Koszul sign.
* `DifferentialGradedModule.baseChange_smul_tmul`: the right `A'`-action on a pure tensor is
  `(m ⊗ t) · (a ⊗ s) = (m · a) ⊗ (t s)`.
* `DifferentialGraded.Bimodule.baseChangeTensorAlgebraIso`: **the `A'`-linearity of `c_M`** —
  `M ⊗_A A' ≅ M ⊗_R R'` as differential graded `A'`-modules, the map sending `x ⊗ (a ⊗ s)` to
  `(x · a) ⊗ s`.
* `DifferentialGraded.Bimodule.restrictBaseChangeAbsoluteTensorIso`: restricting that right
  action along `r' ↦ 1 ⊗ r'` gives back the differential graded `R'`-module `M ⊗_R R'` of
  `DifferentialGraded.Bimodule.baseChangeTensorIso`.

## Implementation notes

*What of Tag 0BYZ this completes.* With the `A'`-linearity of `c_M` formalized, nothing of
Tag 0BYZ is left unformalized. Part (1) is
`DifferentialGraded.Bimodule.derivedBaseChangeFunctor_isLeftDerivedFunctor` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChange.lean`, part (2) is
`DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRestrictionSquare.lean`, and part (3) is
`DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRepresents.lean`. The canonical map
`c_M` of the proof is this file over `A'` and
`DifferentialGraded.Bimodule.baseChangeTensorIso` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorRestrictRight.lean` over `R'` alone,
by a different route; that the `A'`-module structure built here restricts along `r' ↦ 1 ⊗ r'` to
the `R'`-module structure there is
`DifferentialGraded.Bimodule.restrictBaseChangeAbsoluteTensorIso`.

*Why the action can be written down without the general theory.* A module over a graded tensor
product of two algebras does not exist in this tree —
`DifferentialGradedModule.absoluteTensor` gives `M ⊗_R C` only as a module over `C` — and the
Koszul signs of Tag 065W are what makes the general construction work. Here the second factor
`degreeZero R R'` is concentrated in degree zero, so every sign in sight is `+1`: multiplication
in `A'` is that of the ordinary tensor product of algebras
(`DifferentialGradedAlgebra.baseChange_tmul_mul_tmul`), and the prescription
`(m ⊗ t) · (a ⊗ s) = (m · a) ⊗ (t s)` is therefore already a ring homomorphism from the opposite
algebra of `A'` into the endomorphisms of `M ⊗_R R'`, with no sign to track. The general
graded-tensor-product module theory is not needed and is not built.

*What is reused.* The grading, the differential, the direct-sum decomposition and the two
differential conditions are those of
`DifferentialGradedModule.absoluteTensor M (degreeZero R R')`, unchanged: only the right action is
new, so only the graded compatibility of the action and its Leibniz rule are proved here. The
degree-zero concentration enters twice more. The differential of `M ⊗_R R'` is `d_M ⊗ 1`
(`DifferentialGradedModule.absTensorDifferential_tmul_degreeZero`). And the Leibniz rule for the
action is stated with its sign at the total degree of the element of `M ⊗_R R'`, whereas the
Leibniz rule of `M` over `A` gives it at the degree of the factor in `M`; the two agree because a
homogeneous element of `R'` of nonzero degree is zero, which is the one case distinction in
`DifferentialGradedModule.baseChangeAct_leibniz`.

*Two spellings of one algebra.* The type `(A.baseChange R').A`, reached through the differential
graded algebra structure, and `A.grading ᵍ⊗[R] (degreeZero R R').grading`, the graded tensor
product itself, are the same type, and instance resolution does not see through the first. The
right-action instance is declared at the first spelling, which is the one the differential graded
module structure and the universal property of the relative tensor product ask for, and a
statement that needs an element of it as a pure tensor passes the element at the second spelling
through a `show`, as in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorAlgebraComparison.lean`.

*Why the right action of `M ⊗_R R'` over `R'` is spelled through a bilinear map.* The right
action of `DifferentialGradedModule.absoluteTensor M C` is found by instance resolution only
while `C` is a variable: at the concrete algebra `degreeZero R R'` the goal is reduced past the
projection `(degreeZero R R').A` that the instance is keyed on, and nothing matches. The one
statement here that mentions that action,
`DifferentialGradedModule.baseChangeAct_one_tmul`, therefore writes it as
`DifferentialGradedModule.rightActionBilinear`, which takes the module as an explicit argument.

*Universes.* The differential graded algebras and their modules live in a single universe `u`,
following the encoding of Tag 09JJ used throughout this chapter.

## References

* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ), whose proof begins with
  the canonical map `c_M : M ⊗_R R' → M ⊗_A A'`; the tensor product of differential graded
  algebras is [Tag 065W](https://stacks.math.columbia.edu/tag/065W), the relative tensor product
  with a bimodule and its universal property is
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), and the regular bimodule of a
  homomorphism is [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX).
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- Every element of `R'` is homogeneous of degree zero in `degreeZero R R'`. -/
private theorem mem_degreeZeroGrading_zero (s : R') : s ∈ (degreeZero R R').grading 0 :=
  (degreeZeroGrading_zero R R').ge Submodule.mem_top

/-- Multiplication in the base change `A' = A ⊗_R R'` carries no Koszul sign. -/
theorem baseChange_tmul_mul_tmul (a a' : A.A) (s s' : R') :
    ((a ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading) *
        (a' ᵍ⊗ₜ[R] s' : A.grading ᵍ⊗[R] (degreeZero R R').grading)) =
      ((a * a') ᵍ⊗ₜ[R] (s * s') : A.grading ᵍ⊗[R] (degreeZero R R').grading) := by
  induction a' using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [GradedTensorProduct.tmul]
  | add x y hx hy =>
    rw [tmul_add_left, mul_add, hx, hy, mul_add, tmul_add_left]
  | @homogeneous p a' =>
    simpa using GradedTensorProduct.tmul_coe_mul_coe_tmul A.grading (degreeZero R R').grading a
      ⟨s, mem_degreeZeroGrading_zero R' s⟩ a' s'

/-- The unit of the base change `A ⊗_R R'` is the pure tensor `1 ⊗ 1`. -/
theorem baseChange_one_eq_tmul :
    (1 : (A.baseChange R').A) =
      ((1 : A.A) ᵍ⊗ₜ[R] (1 : R') : A.grading ᵍ⊗[R] (degreeZero R R').grading) := by
  simp only [GradedTensorProduct.tmul, ← Algebra.TensorProduct.one_def,
    GradedTensorProduct.of_one]

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}
  (M : DifferentialGradedModule.{u, u, u} A) (R' : Type u) [CommRing R'] [Algebra R R']

/-- `(m ⊗ t) ⊗ (a ⊗ s) ↦ (m · a) ⊗ (t s)`, the right action of `A ⊗_R R'` on `M ⊗_R R'` read on
the plain tensor product of the two factors. -/
def baseChangeSmulₗ :
    ((M.M ⊗[R] R') ⊗[R] (A.A ⊗[R] R')) →ₗ[R] (M.M ⊗[R] R') :=
  TensorProduct.map (TensorProduct.lift (rightActionBilinear M))
      (TensorProduct.lift (LinearMap.mul R R')) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R M.M R' A.A R').toLinearMap

/-- The right action of `A' = A ⊗_R R'` on `M ⊗_R R'`: the element `a ⊗ s` acts by `a` on the
first factor and by `s` on the second. -/
def baseChangeAct : (A.baseChange R').A →ₗ[R] Module.End R (M.M ⊗[R] R') :=
  (TensorProduct.curry (baseChangeSmulₗ M R')).flip ∘ₗ
    (GradedTensorProduct.of R A.grading (degreeZero R R').grading).symm.toLinearMap

/-- The element `a ⊗ s` of `A'` sends the pure tensor `m ⊗ t` to `(m · a) ⊗ (t s)`. -/
theorem baseChangeAct_tmul (a : A.A) (s : R') (m : M.M) (t : R') :
    baseChangeAct M R' (a ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading) (m ⊗ₜ[R] t) =
      (MulOpposite.op a • m) ⊗ₜ[R] (t * s) := by
  simp [baseChangeAct, baseChangeSmulₗ, GradedTensorProduct.tmul]

/-- The action of a product is the composite of the actions, in the opposite order: the right
action of `A'` on `M ⊗_R R'` is an action. -/
theorem baseChangeAct_mul (z w : (A.baseChange R').A) :
    baseChangeAct M R' (z * w) = baseChangeAct M R' w * baseChangeAct M R' z := by
  induction z using DifferentialGraded.gradedTensor_induction with
  | add z z' hz hz' => rw [add_mul, map_add, hz, hz', map_add, mul_add]
  | tmul a s =>
    induction w using DifferentialGraded.gradedTensor_induction with
    | add w w' hw hw' => rw [mul_add, map_add, hw, hw', map_add, add_mul]
    | tmul a' s' =>
      refine TensorProduct.ext' fun m t => ?_
      rw [baseChange_tmul_mul_tmul]
      rw [Module.End.mul_apply, baseChangeAct_tmul, baseChangeAct_tmul, baseChangeAct_tmul,
        MulOpposite.op_mul, mul_smul, mul_assoc]

/-- The right action of `A' = A ⊗_R R'` on `M ⊗_R R'`, as a ring homomorphism from the opposite
algebra: a right `A'`-module structure on `M ⊗_R R'`. -/
def baseChangeActRingHom :
    (A.baseChange R').Aᵐᵒᵖ →+* Module.End R (M.M ⊗[R] R') where
  toFun z := baseChangeAct M R' z.unop
  map_one' := by
    refine TensorProduct.ext' fun m t => ?_
    rw [MulOpposite.unop_one, baseChange_one_eq_tmul, baseChangeAct_tmul]
    simp
  map_mul' z w := baseChangeAct_mul M R' w.unop z.unop
  map_zero' := by rw [MulOpposite.unop_zero, map_zero]
  map_add' z w := by rw [MulOpposite.unop_add, map_add]

/-- The right `A'`-action on `M ⊗_R R'`, where `A' = A ⊗_R R'`: the element `a ⊗ s` acts by `a`
on the first factor and by `s` on the second. -/
@[instance_reducible]
def baseChangeRightModule : Module (A.baseChange R').Aᵐᵒᵖ (M.M ⊗[R] R') :=
  Module.compHom _ (baseChangeActRingHom M R')

attribute [local instance] baseChangeRightModule

/-- The scalar action of `A'ᵐᵒᵖ` on `M ⊗_R R'` is `baseChangeAct` applied to the underlying
element of `A'`. -/
theorem baseChange_smul_def (z : (A.baseChange R').Aᵐᵒᵖ) (x : M.M ⊗[R] R') :
    z • x = baseChangeAct M R' z.unop x := rfl

/-- **The right action of `A' = A ⊗_R R'` on `M ⊗_R R'` on pure tensors**:
`(m ⊗ t) · (a ⊗ s) = (m · a) ⊗ (t s)`. -/
theorem baseChange_smul_tmul (a : A.A) (s : R') (m : M.M) (t : R') :
    MulOpposite.op (show (A.baseChange R').A from
          (a ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading)) • (m ⊗ₜ[R] t) =
      (MulOpposite.op a • m) ⊗ₜ[R] (t * s) :=
  baseChangeAct_tmul M R' a s m t

/-- The right `A'`-action on `M ⊗_R R'` is `R`-linear: the scalars `R`, `A'ᵐᵒᵖ` and `M ⊗_R R'`
form a scalar tower. -/
theorem baseChangeRightScalarTower :
    IsScalarTower R (A.baseChange R').Aᵐᵒᵖ (M.M ⊗[R] R') where
  smul_assoc r z x := by
    rw [baseChange_smul_def, baseChange_smul_def, MulOpposite.unop_smul, map_smul]
    rfl

attribute [local instance] baseChangeRightScalarTower


private theorem degreeZero_d_eq_zero (s : R') : (degreeZero R R').d s = 0 := rfl

/-- The differential of `M ⊗_R R'` is `d_M ⊗ 1`: the second factor sits in degree zero and
carries the zero differential, so neither the sign nor the second term of the signed tensor
differential survives. -/
theorem absTensorDifferential_tmul_degreeZero (p : ℤ) (y : M.M) (hy : y ∈ M.grading p) (t : R') :
    absTensorDifferential M (degreeZero R R') (y ⊗ₜ[R] t) = (M.d y) ⊗ₜ[R] t := by
  have h := absTensorDifferential_tmul M (degreeZero R R') p ⟨y, hy⟩ t
  rw [degreeZero_d_eq_zero, TensorProduct.tmul_zero, smul_zero, add_zero] at h
  exact h

/-- The differential of `A' = A ⊗_R R'` on a pure tensor with homogeneous left factor is
`d_A ⊗ 1`, stated with the homogeneity as a hypothesis. -/
private theorem baseChange_d_tmul_of_mem (i : ℤ) (a : A.A) (ha : a ∈ A.grading i) (s : R') :
    (A.baseChange R').d (a ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading) =
      ((A.d a) ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading) :=
  baseChange_d_tmul A R' i ⟨a, ha⟩ s

/-- **The right `A'`-action adds degrees.** -/
theorem baseChangeAct_mem (n m : ℤ) (x : M.M ⊗[R] R') (z : (A.baseChange R').A)
    (hx : x ∈ absTensorGrading M (degreeZero R R') n)
    (hz : z ∈ (A.baseChange R').grading m) :
    baseChangeAct M R' z x ∈ absTensorGrading M (degreeZero R R') (n + m) := by
  refine tensorProductGrading_induction A (degreeZero R R') m
    (motive := fun z => baseChangeAct M R' z x ∈ absTensorGrading M (degreeZero R R') (n + m))
    (by rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _)
    (fun z w hz hw => by rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hz hw)
    (fun r z hz => by rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ r hz)
    ?_ z hz
  intro i j a s ha hs hij
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, y, t, hy, ht, hpq, rfl⟩ := hx
    rw [show y = ((⟨y, hy⟩ : M.grading p) : M.M) from rfl, baseChangeAct_tmul]
    have h := absTmul_mem M (degreeZero R R') (p + i) (q + j)
      (MulOpposite.op a • y) (t * s) (M.smul_mem p i y a hy ha)
      (SetLike.mul_mem_graded ht hs)
    rwa [show p + i + (q + j) = n + m by omega] at h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

/-- **The right `A'`-action satisfies the graded Leibniz rule.** The second factor of
`A' = A ⊗_R R'` is concentrated in degree zero with zero differential, so the whole rule is the
Leibniz rule of `M` over `A`; the degree that the sign is read at is that of the first factor,
which is the total degree because a homogeneous element of nonzero degree of `R'` vanishes. -/
theorem baseChangeAct_leibniz (n m : ℤ) (x : M.M ⊗[R] R') (z : (A.baseChange R').A)
    (hx : x ∈ absTensorGrading M (degreeZero R R') n)
    (hz : z ∈ (A.baseChange R').grading m) :
    absTensorDifferential M (degreeZero R R') (baseChangeAct M R' z x) =
      baseChangeAct M R' z (absTensorDifferential M (degreeZero R R') x) +
        (n.negOnePow : ℤ) • baseChangeAct M R' ((A.baseChange R').d z) x := by
  refine tensorProductGrading_induction A (degreeZero R R') m
    (motive := fun z => absTensorDifferential M (degreeZero R R') (baseChangeAct M R' z x) =
      baseChangeAct M R' z (absTensorDifferential M (degreeZero R R') x) +
        (n.negOnePow : ℤ) • baseChangeAct M R' ((A.baseChange R').d z) x)
    (by simp) (fun z w hz hw => by
      simp only [map_add, LinearMap.add_apply, hz, hw, smul_add]
      abel)
    (fun r z hz => by
      simp only [map_smul, LinearMap.smul_apply, hz, smul_add, smul_comm (n.negOnePow : ℤ) r])
    ?_ z hz
  intro i j a s ha hs hij
  rw [baseChange_d_tmul_of_mem R' i a ha s]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, y, t, hy, ht, hpq, rfl⟩ := hx
    by_cases hq : q = 0
    · subst hq
      have hn : n = p := by omega
      subst hn
      have hL : absTensorDifferential M (degreeZero R R')
            (baseChangeAct M R' (a ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading)
              (y ⊗ₜ[R] t)) =
          (MulOpposite.op a • M.d y) ⊗ₜ[R] (t * s) +
            (n.negOnePow : ℤ) • ((MulOpposite.op (A.d a) • y) ⊗ₜ[R] (t * s)) := by
        rw [baseChangeAct_tmul, absTensorDifferential_tmul_degreeZero M R' (n + i) _
          (M.smul_mem n i y a hy ha), M.leibniz n i y a hy ha, TensorProduct.add_tmul,
          ← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul', Int.cast_smul_eq_zsmul]
      have hR : baseChangeAct M R' (a ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading)
            (absTensorDifferential M (degreeZero R R') (y ⊗ₜ[R] t)) =
          (MulOpposite.op a • M.d y) ⊗ₜ[R] (t * s) := by
        rw [absTensorDifferential_tmul_degreeZero M R' n y hy, baseChangeAct_tmul]
      rw [hL, hR, baseChangeAct_tmul]
    · have ht0 : t = 0 := by
        have hb : t ∈ degreeZeroGrading R R' q := ht
        rw [degreeZeroGrading_eq_bot R R' hq] at hb
        simpa using hb
      subst ht0
      simp
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [map_add, ihx, ihy, smul_add]
    abel
  | smul r x hx ih =>
    simp only [map_smul, ih, smul_add, smul_comm (n.negOnePow : ℤ) r]

/-- **The right `A'`-action restricted along `r' ↦ 1 ⊗ r'` is the right `R'`-action**: the
element `1 ⊗ c` of `A'` acts on `M ⊗_R R'` as `c` does on the second factor. The right action of
`DifferentialGradedModule.absoluteTensor` is spelled through
`DifferentialGradedModule.rightActionBilinear` because the module `M ⊗_R R'` is reached here at
the concrete algebra `degreeZero R R'`, where instance resolution no longer recovers it. -/
theorem baseChangeAct_one_tmul (c : (degreeZero R R').A)
    (x : M.M ⊗[R] (degreeZero R R').A) :
    baseChangeAct M R' (((1 : A.A) ᵍ⊗ₜ[R] c) : A.grading ᵍ⊗[R] (degreeZero R R').grading) x =
      rightActionBilinear (M.absoluteTensor (degreeZero R R')) x c := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy, map_add, LinearMap.add_apply]
  | tmul m t =>
    rw [baseChangeAct_tmul, rightActionBilinear_apply, absTensor_smul_tmul,
      MulOpposite.op_one, one_smul]

/-- **`M ⊗_R R'` as a differential graded `A' = A ⊗_R R'`-module.** -/
@[reducible]
def baseChangeAbsoluteTensor : DifferentialGradedModule.{u, u, u} (A.baseChange R') where
  M := M.M ⊗[R] R'
  rmodule := baseChangeRightModule M R'
  isScalarTower := baseChangeRightScalarTower M R'
  grading := absTensorGrading M (degreeZero R R')
  decomposition := absTotalDecomposition M (degreeZero R R')
  smul_mem := baseChangeAct_mem M R'
  d := absTensorDifferential M (degreeZero R R')
  d_comp_d := absTensorDifferential_sq M (degreeZero R R')
  d_mem := absTensorDifferential_mem M (degreeZero R R')
  leibniz := baseChangeAct_leibniz M R'

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)
  (R' : Type u) [CommRing R'] [Algebra R R']

attribute [local instance] DifferentialGradedModule.baseChangeRightModule
  DifferentialGradedModule.baseChangeRightScalarTower
  DifferentialGradedModule.absTotalDecomposition

/-! ### The two actions on the base-change bimodule -/

/-- The left `A`-action on the base-change bimodule `{}_A(A ⊗_R R')_{A'}` is left multiplication
by `a ⊗ 1`. -/
theorem baseChange_leftAction (n q : ℤ) (a : A.grading n)
    (y : (baseChange A R').rightModule.grading q) :
    ((show (baseChange A R').rightModule.grading (q + n) from
      ((baseChange A R').leftAction.1.action n a).v q (q + n) (by omega) y) :
        (baseChange A R').rightModule.M) =
      (((a : A.A) ᵍ⊗ₜ[R] (1 : R')) : A.grading ᵍ⊗[R] (degreeZero R R').grading) *
        (show A.grading ᵍ⊗[R] (degreeZero R R').grading from
          (y : (baseChange A R').rightModule.M)) :=
  (regularBimoduleStructure_action (A.toBaseChange R') n q a y).trans
    (by rw [toBaseChange_apply])

/-- The right `A'`-action on the base-change bimodule is multiplication in `A'`. -/
theorem baseChange_op_smul (y : (baseChange A R').rightModule.M) (b : (A.baseChange R').A) :
    MulOpposite.op b • y = (show (A.baseChange R').A from y) * b := rfl

variable (M : DifferentialGradedModule.{u, u, u} A)

/-! ### The canonical map as a map of differential graded `A'`-modules -/

/-- The relative tensor product `M ⊗_A A'`, as a right differential graded `A'`-module. -/
abbrev baseChangeRelativeTensor : DifferentialGradedModule.{u, u, u} (A.baseChange R') :=
  Bimodule.tensorObj (baseChange A R') M

/-- The universal pure tensors `x ⊗ y` into `M ⊗_A A'`, with the second argument read in the
graded tensor product `A ⊗_R R'` itself rather than through the bimodule structure. -/
def baseChangePureBilinear :
    M.M →ₗ[R] (A.grading ᵍ⊗[R] (degreeZero R R').grading) →ₗ[R]
      (baseChangeRelativeTensor A R' M).M :=
  (Bimodule.tensorPure (baseChange A R') M).toLinearMap

/-- The pure tensors are balanced over `A`, for homogeneous arguments. -/
theorem baseChangePureBilinear_balance_of_mem (p q n : ℤ) (x : M.M) (hx : x ∈ M.grading p)
    (y : A.grading ᵍ⊗[R] (degreeZero R R').grading)
    (hy : y ∈ tensorProductGrading A (degreeZero R R') q) (a : A.grading n) :
    baseChangePureBilinear A R' M (MulOpposite.op (a : A.A) • x) y =
      baseChangePureBilinear A R' M x
        ((((a : A.A) ᵍ⊗ₜ[R] (1 : R')) : A.grading ᵍ⊗[R] (degreeZero R R').grading) * y) := by
  have h := (Bimodule.tensorPure (baseChange A R') M).balance p q n ⟨x, hx⟩ ⟨y, hy⟩ a
  rw [baseChange_leftAction] at h
  exact h

/-- **The pure tensors are balanced over `A`**: moving `a` from the right action on `M` to the
left action on `A ⊗_R R'` does not change them. -/
theorem baseChangePureBilinear_balance (a : A.A) (x : M.M)
    (y : A.grading ᵍ⊗[R] (degreeZero R R').grading) :
    baseChangePureBilinear A R' M (MulOpposite.op a • x) y =
      baseChangePureBilinear A R' M x
        (((a ᵍ⊗ₜ[R] (1 : R')) : A.grading ᵍ⊗[R] (degreeZero R R').grading) * y) := by
  have := totalDecomposition A (degreeZero R R')
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [GradedTensorProduct.tmul]
  | add a a' ha ha' =>
    rw [MulOpposite.op_add, add_smul, map_add, LinearMap.add_apply, ha, ha', tmul_add_left,
      add_mul, map_add]
  | @homogeneous n a =>
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x x' hx hx' => simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
    | @homogeneous p x =>
      induction y using DirectSum.Decomposition.inductionOn
          (tensorProductGrading A (degreeZero R R')) with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
      | @homogeneous q y =>
        exact baseChangePureBilinear_balance_of_mem A R' M p q n x.1 x.2 y.1 y.2 a

/-- **The right `A'`-action on `M ⊗_R R'` is the one the canonical map transports**: unbalancing
a pure tensor and then acting by `b` is unbalancing the pure tensor multiplied by `b`. -/
theorem absUnbalance_mul (x : M.M) (y b : A.grading ᵍ⊗[R] (degreeZero R R').grading) :
    absUnbalance A (degreeZero R R') M x (y * b) =
      baseChangeAct M R' b (absUnbalance A (degreeZero R R') M x y) := by
  induction y using gradedTensor_induction with
  | add y y' hy hy' => simp only [add_mul, map_add, hy, hy']
  | tmul c t =>
    induction b using gradedTensor_induction with
    | add b b' hb hb' => simp only [mul_add, map_add, LinearMap.add_apply, hb, hb']
    | tmul a s =>
      rw [baseChange_tmul_mul_tmul, absUnbalance_tmul, absUnbalance_tmul, baseChangeAct_tmul,
        MulOpposite.op_mul, mul_smul]

/-- **The canonical map `c_M` of the proof of Stacks 0BYZ, as a balanced bilinear map over
`A'`**: `(x, a ⊗ s) ↦ (x · a) ⊗ s`, with values in `M ⊗_R R'` carrying its right
`A'`-action. -/
def baseChangeUnbalanceBalanced :
    Bimodule.BalancedBilinearMap M (baseChange A R') (baseChangeAbsoluteTensor M R') where
  toLinearMap := absUnbalance A (degreeZero R R') M
  map_grading p q x y := absUnbalance_mem A (degreeZero R R') M p q x ⟨y.1, y.2⟩
  map_d p x y := absUnbalance_d A (degreeZero R R') M p x y
  balance p q n x y a := by
    rw [baseChange_leftAction]
    exact absUnbalance_balance A (degreeZero R R') M x.1 a.1 y.1
  map_right x y b := by
    rw [baseChange_op_smul]
    exact absUnbalance_mul A R' M x y b

/-- **The canonical map `c_M` of the proof of Stacks 0BYZ, over `A'`**, as a homomorphism of
differential graded `A'`-modules: the unique one sending `x ⊗ (a ⊗ s)` to `(x · a) ⊗ s`. -/
def baseChangeTensorForward :
    baseChangeRelativeTensor A R' M ⟶ baseChangeAbsoluteTensor M R' :=
  ((Bimodule.tensorDGFunctor (baseChange A R')).universal M (baseChangeAbsoluteTensor M R')
    (baseChangeUnbalanceBalanced A R' M)).choose

/-- The canonical map sends the pure tensor `x ⊗ y` of `M ⊗_A A'` to the unbalanced tensor of
`x` and `y` in `M ⊗_R R'`. -/
theorem baseChangeTensorForward_pure (x : M.M)
    (y : A.grading ᵍ⊗[R] (degreeZero R R').grading) :
    (baseChangeTensorForward A R' M).toFun (baseChangePureBilinear A R' M x y) =
      absUnbalance A (degreeZero R R') M x y :=
  ((Bimodule.tensorDGFunctor (baseChange A R')).universal M (baseChangeAbsoluteTensor M R')
    (baseChangeUnbalanceBalanced A R' M)).choose_spec.1 x y

/-- `x ⊗ s ↦ x ⊗ (1 ⊗ s)`, the inverse of the canonical map, as a linear map. -/
def baseChangeTensorInverseLinear :
    (M.M ⊗[R] R') →ₗ[R] (baseChangeRelativeTensor A R' M).M :=
  TensorProduct.lift ((baseChangePureBilinear A R' M).compl₂
    (GradedTensorProduct.includeRight A.grading (degreeZero R R').grading).toLinearMap)

/-- The inverse of the canonical map sends `x ⊗ s` to the pure tensor `x ⊗ (1 ⊗ s)`. -/
theorem baseChangeTensorInverseLinear_tmul (x : M.M) (s : R') :
    baseChangeTensorInverseLinear A R' M (x ⊗ₜ[R] s) =
      baseChangePureBilinear A R' M x
        (((1 : A.A) ᵍ⊗ₜ[R] s : A.grading ᵍ⊗[R] (degreeZero R R').grading)) := rfl

/-- The inverse of the canonical map sends the unbalanced tensor of `x` and `y` to the pure
tensor `x ⊗ y` of `M ⊗_A A'`. -/
theorem baseChangeTensorInverseLinear_absUnbalance (x : M.M)
    (y : A.grading ᵍ⊗[R] (degreeZero R R').grading) :
    baseChangeTensorInverseLinear A R' M (absUnbalance A (degreeZero R R') M x y) =
      baseChangePureBilinear A R' M x y := by
  induction y using gradedTensor_induction with
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  | tmul a s =>
    rw [absUnbalance_tmul, baseChangeTensorInverseLinear_tmul, baseChangePureBilinear_balance,
      tmul_one_mul_tmul A (degreeZero R R') a 1 s, mul_one]

/-- `baseChangeTensorInverseLinear` is a right inverse of the canonical map. -/
theorem baseChangeTensorForward_inverseLinear (z : M.M ⊗[R] R') :
    (baseChangeTensorForward A R' M).toFun (baseChangeTensorInverseLinear A R' M z) = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x s =>
    rw [baseChangeTensorInverseLinear_tmul, baseChangeTensorForward_pure, absUnbalance_tmul]
    simp

/-- `baseChangeTensorInverseLinear` is a left inverse of the canonical map. -/
theorem baseChangeTensorInverseLinear_forward (w : (baseChangeRelativeTensor A R' M).M) :
    baseChangeTensorInverseLinear A R' M ((baseChangeTensorForward A R' M).toFun w) = w := by
  refine LinearMap.congr_fun (Bimodule.tensorObj_linearMap_ext (baseChange A R') M
    (baseChangeTensorInverseLinear A R' M ∘ₗ (baseChangeTensorForward A R' M).toFun)
    LinearMap.id fun x y => ?_) w
  exact (congrArg (baseChangeTensorInverseLinear A R' M)
      (baseChangeTensorForward_pure A R' M x y)).trans
    (baseChangeTensorInverseLinear_absUnbalance A R' M x y)

/-- **The `A'`-linearity of the canonical map `c_M` in the proof of Stacks 0BYZ.** Let `R → R'`
be a map of commutative rings, let `(A, d)` be a differential graded `R`-algebra and let
`A' = A ⊗_R R'` be its base change. For a differential graded `A`-module `M` the base change
`M ⊗_A A'` is `M ⊗_R R'` **as a differential graded `A'`-module**, the right action of `a ⊗ s`
on `M ⊗_R R'` being `(m ⊗ t) · (a ⊗ s) = (m · a) ⊗ (t s)`
(`DifferentialGradedModule.baseChange_smul_tmul`).

The isomorphism is the source's `c_M`, read in the direction out of the relative tensor product:
it sends the pure tensor `x ⊗ (a ⊗ s)` to `(x · a) ⊗ s`
(`DifferentialGraded.Bimodule.baseChangeTensorForward_pure`), and its inverse — the source's
`c_M` itself — sends `x ⊗ s` to `x ⊗ (1 ⊗ s)`. -/
@[stacks 0BYZ "the A'-linearity of the canonical map c_M of the PROOF, NOT any of parts (1), \
(2), (3): M (x)_A A' is M (x)_R R' as differential graded A'-modules, the right action on \
M (x)_R R' being (m (x) t)(a (x) s) = (m a) (x) (t s). With this nothing of Tag 0BYZ is left \
unformalized; the module docstring says where the three parts and the R'-only form \
baseChangeTensorIso are, and how this A'-module restricts to that R'-module"]
def baseChangeTensorAlgebraIso :
    baseChangeRelativeTensor A R' M ≅ baseChangeAbsoluteTensor M R' :=
  (baseChangeTensorForward A R' M).isoOfBijective
    (Function.bijective_iff_has_inverse.2
      ⟨baseChangeTensorInverseLinear A R' M, baseChangeTensorInverseLinear_forward A R' M,
        baseChangeTensorForward_inverseLinear A R' M⟩)

/-- **The `A'`-module `M ⊗_R R'` restricts to the `R'`-module `M ⊗_R R'`.** Restricting the right
action along `r' ↦ 1 ⊗ r'` turns the differential graded `A'`-module
`DifferentialGradedModule.baseChangeAbsoluteTensor` into the differential graded `R'`-module
`DifferentialGradedModule.absoluteTensor` of
`DifferentialGraded.Bimodule.baseChangeTensorIso`: the underlying complexes are equal and the
two actions of `r' : R'` agree, both sending `m ⊗ t` to `m ⊗ (t r')`. -/
def restrictBaseChangeAbsoluteTensorIso :
    (restrictScalarsFunctor (tensorIncludeRightHom A (degreeZero R R'))).obj
        (baseChangeAbsoluteTensor M R') ≅
      M.absoluteTensor (degreeZero R R') :=
  DifferentialGradedModule.Hom.isoOfBijective
    { toFun := LinearMap.id
      map_smul := fun x c => Eq.trans rfl (baseChangeAct_one_tmul M R' c x)
      map_grading := fun _ _ hx => hx
      map_d := rfl }
    Function.bijective_id

end DifferentialGraded.Bimodule

end
