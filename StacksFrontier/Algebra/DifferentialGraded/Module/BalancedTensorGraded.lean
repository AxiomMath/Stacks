module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import StacksFrontier.Algebra.DifferentialGraded.Module.BalancedTensor
public import StacksFrontier.Algebra.Module.BalancedTensorProduct

/-!
# The grading on the balanced tensor product of graded modules

Let `R` be a commutative ring, `A` a graded `R`-algebra, `M'` a graded right `A`-module and `M`
a graded left `A`-module. The balanced tensor product `M' ⊗_A M` of
`StacksDraft.BalancedTensorProduct` is a graded `R`-module whose degree-`n` piece is

`Coker(⨁_{r + t + s = n} (M')^r ⊗_R A^t ⊗_R M^s → ⨁_{p + q = n} (M')^p ⊗_R M^q)`,

the map sending `x ⊗ a ⊗ y` to `x ⊗ a y - x a ⊗ y`. The map `M' × M → M' ⊗_A M` is `A`-balanced,
compatible with the gradings, and universal for graded balanced bilinear maps into graded
`R`-modules.

## Main definitions

* `DifferentialGraded.gradedAlgebraOfGraded`, `DifferentialGraded.gradedRightModuleOfGraded`,
  `DifferentialGraded.gradedLeftModuleOfGraded`: a graded algebra and graded modules over it,
  with zero differentials.
* `DifferentialGraded.tensorRelMap`: the map `⨁ (M')^r ⊗ A^t ⊗ M^s → ⨁ (M')^p ⊗ M^q`,
  `x ⊗ a ⊗ y ↦ x ⊗ a y - x a ⊗ y`, in total degree `n`.
* `DifferentialGraded.GradedBalancedBilinear`: graded `A`-balanced bilinear maps `M' × M → Q` into
  a graded `R`-module `Q`, given by its pieces.
* `DifferentialGraded.balancedTensorGradedEquiv` ([stacks 09LL]): the identification of the
  balanced tensor product `M' ⊗_A M` with the direct sum of the pieces `tensorDeg M' M n`.

## Main results

* `DifferentialGraded.range_tensorRelMap`: the image of `tensorRelMap` is the submodule of
  balancing relations, so that `tensorDeg M' M n` is the cokernel of `tensorRelMap`.
* `DifferentialGraded.tensorDegEquivCoker` ([stacks 09LL]): the degree-`n` piece of `M' ⊗_A M`
  is that cokernel.
* `DifferentialGraded.balancedTensorGradedEquiv_lof_tmul` ([stacks 09LL]): under that
  identification the class of a homogeneous `x ⊗ y` of degree `p + q` is the symbol `x ⊗ y`.
* `DifferentialGraded.gradedTensorHomEquiv` ([stacks 09LL]): the universal property
  `GradedBilinear_A(M' × M, Q) = Hom_{graded R-modules}(M' ⊗_A M, Q)`.

## Implementation notes

The graded algebra and the graded modules are taken in the form of
`DifferentialGradedAlgebra`, `DifferentialGradedModule` and `LeftModule`. None of the statements
below mentions a differential, so they hold for every choice of differentials. A graded algebra
and graded modules in the source's sense are the case where every differential is zero:
`gradedAlgebraOfGraded`, `gradedRightModuleOfGraded` and `gradedLeftModuleOfGraded` make them
into such structures. A graded
`R`-module is given by its family of pieces `Q n`, and a map of graded `R`-modules out of
`M' ⊗_A M` by its family of components on the pieces `tensorDeg M' M n`, which
`balancedTensorGradedEquiv` identifies with the graded pieces of `M' ⊗_A M`.

## References

* [Stacks Project, Tag 09LL](https://stacks.math.columbia.edu/tag/09LL)
-/

@[expose] public section

open scoped TensorProduct DirectSum

universe u v

namespace DifferentialGraded

variable {R : Type u} [CommRing R]

/-! ## Graded algebras and graded modules -/

/-- A `ℤ`-graded `R`-algebra, as a differential graded algebra with zero differential. -/
def gradedAlgebraOfGraded (B : Type v) [Ring B] [Algebra R B] (𝒜 : ℤ → Submodule R B)
    [GradedAlgebra 𝒜] : DifferentialGradedAlgebra.{u, v} R where
  A := B
  grading := 𝒜
  d := 0
  d_comp_d := LinearMap.zero_comp 0
  d_mem _ _ _ := zero_mem _
  leibniz _ _ _ _ _ _ := by simp

/-- A graded right module over a differential graded algebra with zero differential, as a
differential graded module with zero differential. -/
def gradedRightModuleOfGraded (A : DifferentialGradedAlgebra.{u, v} R) (hA : A.d = 0)
    (X : Type u) [AddCommGroup X] [Module R X] [Module (MulOpposite A.A) X]
    [IsScalarTower R (MulOpposite A.A) X] (𝒳 : ℤ → Submodule R X) [DirectSum.Decomposition 𝒳]
    (smul_mem : ∀ (n m : ℤ) (x : X) (a : A.A), x ∈ 𝒳 n → a ∈ A.grading m →
      MulOpposite.op a • x ∈ 𝒳 (n + m)) :
    DifferentialGradedModule.{u, v, u} A where
  M := X
  grading := 𝒳
  smul_mem := smul_mem
  d := 0
  d_comp_d := LinearMap.zero_comp 0
  d_mem _ _ _ := zero_mem _
  leibniz _ _ _ _ _ _ := by simp [hA]

/-- A graded left module over a differential graded algebra with zero differential, as a
differential graded module with zero differential. -/
def gradedLeftModuleOfGraded (A : DifferentialGradedAlgebra.{u, v} R) (hA : A.d = 0)
    (X : Type u) [AddCommGroup X] [Module R X] [Module A.A X] [IsScalarTower R A.A X]
    (𝒳 : ℤ → Submodule R X) [DirectSum.Decomposition 𝒳]
    (smul_mem : ∀ (m n : ℤ) (a : A.A) (x : X), a ∈ A.grading m → x ∈ 𝒳 n → a • x ∈ 𝒳 (m + n)) :
    LeftModule A where
  M := X
  grading := 𝒳
  smul_mem := smul_mem
  d := 0
  d_comp_d := LinearMap.zero_comp 0
  d_mem _ _ _ := zero_mem _
  leibniz _ _ _ _ _ _ := by simp [hA]

variable {A : DifferentialGradedAlgebra.{u, v} R}
variable (M' : DifferentialGradedModule.{u, v, u} A) (M : LeftModule A)

attribute [local instance] tensorRawAddCommGroup

attribute [local instance 2000] tensorRawAddCommMonoid

/-! ## The cokernel description of the graded pieces -/

/-- Left multiplication by homogeneous elements, as a bilinear map `A^i × M^q → M^{i+q}`. -/
noncomputable def gradedLeftSmulₗ (i q : ℤ) :
    A.grading i →ₗ[R] M.grading q →ₗ[R] M.grading (i + q) :=
  LinearMap.mk₂ R (gradedLeftSmul M i q)
    (fun a a' y => Subtype.ext (by
      simp only [gradedLeftSmul_coe, Submodule.coe_add, add_smul]))
    (fun r a y => Subtype.ext (by
      simp only [gradedLeftSmul_coe, SetLike.val_smul]
      exact smul_assoc _ _ _))
    (fun a y y' => Subtype.ext (by
      simp only [gradedLeftSmul_coe, Submodule.coe_add, smul_add]))
    (fun r a y => Subtype.ext (by
      simp only [gradedLeftSmul_coe, SetLike.val_smul]
      exact smul_comm _ _ _))

/-- Right multiplication by homogeneous elements, as a bilinear map `(M')^p × A^i → (M')^{p+i}`. -/
noncomputable def gradedRightSmulₗ (p i : ℤ) :
    M'.grading p →ₗ[R] A.grading i →ₗ[R] M'.grading (p + i) :=
  LinearMap.mk₂ R (gradedRightSmul M' p i)
    (fun x x' a => Subtype.ext (by
      simp only [gradedRightSmul_coe, Submodule.coe_add, smul_add]))
    (fun r x a => Subtype.ext (by
      simp only [gradedRightSmul_coe, SetLike.val_smul]
      exact smul_comm _ _ _))
    (fun x a a' => Subtype.ext (by
      simp only [gradedRightSmul_coe, Submodule.coe_add, MulOpposite.op_add, add_smul]))
    (fun r x a => Subtype.ext (by
      simp only [gradedRightSmul_coe, SetLike.val_smul, MulOpposite.op_smul]
      exact smul_assoc _ _ _))

/-- The component `x ⊗ a ⊗ y ↦ x ⊗ a y - x a ⊗ y` of `tensorRelMap` in degrees `r`, `t` and
`n - r - t`. -/
noncomputable def tensorRelComp (n r t : ℤ) :
    (M'.grading r ⊗[R] A.grading t) ⊗[R] M.grading (n - r - t) →ₗ[R] tensorRaw M' M n :=
  TensorProduct.lift ((tensorMk M' M n r (t + (n - r - t)) (by omega)).compl₂
      (TensorProduct.lift (gradedLeftSmulₗ M t (n - r - t)))) ∘ₗ
      (TensorProduct.assoc R (M'.grading r) (A.grading t) (M.grading (n - r - t))).toLinearMap -
    TensorProduct.lift ((tensorMk M' M n (r + t) (n - r - t) (by omega)).comp
      (TensorProduct.lift (gradedRightSmulₗ M' r t)))

/-- The map `⨁_{r + t + s = n} (M')^r ⊗_R A^t ⊗_R M^s → ⨁_{p + q = n} (M')^p ⊗_R M^q` sending
`x ⊗ a ⊗ y` to `x ⊗ a y - x a ⊗ y`; the summand of `(r, t)` has `s = n - r - t`. -/
noncomputable def tensorRelMap (n : ℤ) :
    (⨁ rt : ℤ × ℤ, (M'.grading rt.1 ⊗[R] A.grading rt.2) ⊗[R] M.grading (n - rt.1 - rt.2)) →ₗ[R]
      tensorRaw M' M n :=
  DirectSum.toModule R (ℤ × ℤ) _ fun rt => tensorRelComp M' M n rt.1 rt.2

/-- `tensorRelMap` sends `x ⊗ a ⊗ y` to minus the balancing relation `x a ⊗ y - x ⊗ a y`. -/
theorem tensorRelMap_lof (n r t : ℤ) (x : M'.grading r) (a : A.grading t)
    (y : M.grading (n - r - t)) :
    tensorRelMap M' M n (DirectSum.lof R (ℤ × ℤ)
        (fun rt : ℤ × ℤ => (M'.grading rt.1 ⊗[R] A.grading rt.2) ⊗[R] M.grading (n - rt.1 - rt.2))
        (r, t) ((x ⊗ₜ[R] a) ⊗ₜ[R] y)) =
      -tensorRelator M' M r t (n - r - t) n (by omega) x a y := by
  rw [tensorRelMap, DirectSum.toModule_lof, tensorRelator, neg_sub]
  simp only [tensorRelComp, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.assoc_tmul, TensorProduct.lift.tmul,
    LinearMap.compl₂_apply]
  rfl

/-- The image of `tensorRelMap` is the submodule of balancing relations. -/
theorem range_tensorRelMap (n : ℤ) : LinearMap.range (tensorRelMap M' M n) = tensorRel M' M n := by
  apply le_antisymm
  · rw [← Submodule.ker_mkQ (tensorRel M' M n), LinearMap.range_le_ker_iff]
    refine DirectSum.linearMap_ext R fun ⟨r, t⟩ => TensorProduct.ext_threefold fun x a y => ?_
    change (tensorRel M' M n).mkQ (tensorRelMap M' M n (DirectSum.lof R (ℤ × ℤ) _ (r, t)
      ((x ⊗ₜ[R] a) ⊗ₜ[R] y))) = 0
    rw [tensorRelMap_lof, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact neg_mem (tensorRelator_mem M' M _ _ _ _ _ _ _ _)
  · rw [tensorRel, Submodule.span_le]
    rintro z ⟨p, i, q, h, x, a, y, rfl⟩
    obtain rfl : q = n - p - i := by omega
    refine ⟨-DirectSum.lof R (ℤ × ℤ) _ (p, i) ((x ⊗ₜ[R] a) ⊗ₜ[R] y), ?_⟩
    rw [map_neg, tensorRelMap_lof, neg_neg]

/-- The degree-`n` piece of `M' ⊗_A M` is the cokernel of `tensorRelMap`, the map
`⨁_{r + t + s = n} (M')^r ⊗_R A^t ⊗_R M^s → ⨁_{p + q = n} (M')^p ⊗_R M^q` sending
`x ⊗ a ⊗ y` to `x ⊗ a y - x a ⊗ y`. -/
@[stacks 09LL "the n-th graded piece of M ⊗_A N is the cokernel"]
noncomputable def tensorDegEquivCoker (n : ℤ) :
    tensorDeg M' M n ≃ₗ[R] tensorRaw M' M n ⧸ LinearMap.range (tensorRelMap M' M n) :=
  Submodule.quotEquivOfEq _ _ (range_tensorRelMap M' M n).symm

/-! ## The grading of the balanced tensor product -/

/-- The map from `tensorRaw M' M n` to the balanced tensor product, `x ⊗ y ↦ x ⊗ y`. -/
noncomputable def tensorRawToBalanced (n : ℤ) :
    tensorRaw M' M n →ₗ[R] StacksDraft.BalancedTensorProduct R A.A M'.M M.M :=
  DirectSum.toModule R ℤ _ fun i => StacksDraft.BalancedTensorProduct.mk R A.A M'.M M.M ∘ₗ
    TensorProduct.map (M'.grading i).subtype (M.grading (n - i)).subtype

/-- `tensorRawToBalanced` sends a homogeneous `x ⊗ y` to the symbol `x ⊗ y`. -/
theorem tensorRawToBalanced_mk (n p q : ℤ) (h : p + q = n) (x : M'.grading p)
    (y : M.grading q) :
    tensorRawToBalanced M' M n (tensorMk M' M n p q h x y) =
      StacksDraft.BalancedTensorProduct.tmul R A.A M'.M M.M x y := by
  change tensorRawToBalanced M' M n (DirectSum.lof R ℤ
    (fun i => M'.grading i ⊗[R] M.grading (n - i)) p
    (x ⊗ₜ[R] gradingCast M.grading (show q = n - p by omega) y)) = _
  rw [tensorRawToBalanced, DirectSum.toModule_lof]
  rfl

/-- `tensorRawToBalanced` kills the balancing relations. -/
theorem tensorRel_le_ker_tensorRawToBalanced (n : ℤ) :
    tensorRel M' M n ≤ LinearMap.ker (tensorRawToBalanced M' M n) := by
  rw [tensorRel, Submodule.span_le]
  rintro z ⟨p, i, q, h, x, a, y, rfl⟩
  change tensorRawToBalanced M' M n (tensorRelator M' M p i q n h x a y) = 0
  rw [tensorRelator, map_sub, tensorRawToBalanced_mk, tensorRawToBalanced_mk, sub_eq_zero]
  exact StacksDraft.BalancedTensorProduct.tmul_balanced R A.A M'.M M.M (x : M'.M) a (y : M.M)

/-- The map from the direct sum of the pieces `tensorDeg M' M n` to `M' ⊗_A M`. -/
noncomputable def tensorDegToBalanced :
    (⨁ n : ℤ, tensorDeg M' M n) →ₗ[R] StacksDraft.BalancedTensorProduct R A.A M'.M M.M :=
  DirectSum.toModule R ℤ _ fun n =>
    Submodule.liftQ _ (tensorRawToBalanced M' M n) (tensorRel_le_ker_tensorRawToBalanced M' M n)

/-- The map from `M' ⊗_R M` to the direct sum of the pieces, sending `x ⊗ y` to the sum of the
classes of `x_p ⊗ y_q` in degree `p + q`. -/
noncomputable def tensorToDeg : M'.M ⊗[R] M.M →ₗ[R] ⨁ n : ℤ, tensorDeg M' M n :=
  DirectSum.toModule R (ℤ × ℤ) _ (fun pq =>
      DirectSum.lof R ℤ (fun n => tensorDeg M' M n) (pq.1 + pq.2) ∘ₗ
        (tensorRel M' M (pq.1 + pq.2)).mkQ ∘ₗ
          TensorProduct.lift (tensorMk M' M (pq.1 + pq.2) pq.1 pq.2 rfl)) ∘ₗ
    (TensorProduct.directSum R R (fun p => M'.grading p) (fun q => M.grading q)).toLinearMap ∘ₗ
      TensorProduct.map (DirectSum.decomposeLinearEquiv M'.grading).toLinearMap
        (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- `tensorToDeg` sends `x ⊗ y`, with `x` and `y` homogeneous of degrees `p` and `q`, to the class
of `x ⊗ y` in degree `p + q`. -/
theorem tensorToDeg_tmul_of_mem (p q : ℤ) (x : M'.grading p) (y : M.grading q) :
    tensorToDeg M' M ((x : M'.M) ⊗ₜ[R] (y : M.M)) =
      DirectSum.lof R ℤ (fun n => tensorDeg M' M n) (p + q)
        ((tensorRel M' M (p + q)).mkQ (tensorMk M' M (p + q) p q rfl x y)) := by
  simp only [tensorToDeg, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_coe]
  rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, TensorProduct.directSum_lof_tmul_lof,
    DirectSum.toModule_lof]
  rfl

/-- The class of `x ⊗ y` in the direct sum of the pieces does not depend on how its total degree
is written. -/
theorem lof_tensorMk_congr {N N' : ℤ} (e : N = N') {p q : ℤ} (h : p + q = N) (h' : p + q = N')
    (x : M'.grading p) (y : M.grading q) :
    DirectSum.lof R ℤ (fun n => tensorDeg M' M n) N
        ((tensorRel M' M N).mkQ (tensorMk M' M N p q h x y)) =
      DirectSum.lof R ℤ (fun n => tensorDeg M' M n) N'
        ((tensorRel M' M N').mkQ (tensorMk M' M N' p q h' x y)) := by
  subst e
  rfl

/-- `tensorToDeg` is `A`-balanced. -/
theorem tensorToDeg_balanced :
    StacksDraft.IsBalancedBilinear A.A (TensorProduct.curry (tensorToDeg M' M)) := by
  intro x a y
  simp only [TensorProduct.curry_apply]
  induction x using DirectSum.Decomposition.inductionOn M'.grading with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, TensorProduct.add_tmul, map_add, hx, hx']
  | homogeneous x =>
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add a a' ha ha' =>
      simp only [MulOpposite.op_add, add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
        map_add, ha, ha']
    | homogeneous a =>
      induction y using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | add y y' hy hy' => simp only [smul_add, TensorProduct.tmul_add, map_add, hy, hy']
      | @homogeneous q y =>
        rename_i p i
        have h1 := tensorToDeg_tmul_of_mem M' M (p + i) q (gradedRightSmul M' p i x a) y
        have h2 := tensorToDeg_tmul_of_mem M' M p (i + q) x (gradedLeftSmul M i q a y)
        rw [gradedRightSmul_coe] at h1
        rw [gradedLeftSmul_coe] at h2
        rw [h1, h2]
        have hn : p + i + q = p + (i + q) := by omega
        have key : (tensorRel M' M (p + i + q)).mkQ
            (tensorMk M' M (p + i + q) (p + i) q rfl (gradedRightSmul M' p i x a) y) =
            (tensorRel M' M (p + i + q)).mkQ
              (tensorMk M' M (p + i + q) p (i + q) (by omega) x (gradedLeftSmul M i q a y)) :=
          (Submodule.Quotient.eq _).2 (tensorRelator_mem M' M p i q (p + i + q) rfl x a y)
        rw [key]
        exact lof_tensorMk_congr M' M hn _ _ x _

/-- The map from `M' ⊗_A M` to the direct sum of the pieces `tensorDeg M' M n`. -/
noncomputable def balancedToTensorDeg :
    StacksDraft.BalancedTensorProduct R A.A M'.M M.M →ₗ[R] ⨁ n : ℤ, tensorDeg M' M n :=
  StacksDraft.BalancedTensorProduct.lift (TensorProduct.curry (tensorToDeg M' M))
    (tensorToDeg_balanced M' M)

/-- **`M' ⊗_A M` is a graded `R`-module.** The balanced tensor product `M' ⊗_A M` of the
underlying modules is the direct sum of the pieces `tensorDeg M' M n`, the degree-`n` piece
being the cokernel of `tensorRelMap` (`tensorDegEquivCoker`). -/
@[stacks 09LL "M ⊗_A N is a graded R-module"]
noncomputable def balancedTensorGradedEquiv :
    (⨁ n : ℤ, tensorDeg M' M n) ≃ₗ[R] StacksDraft.BalancedTensorProduct R A.A M'.M M.M :=
  LinearEquiv.ofLinearMap (tensorDegToBalanced M' M) (balancedToTensorDeg M' M)
    (by
      refine StacksDraft.BalancedTensorProduct.hom_ext R A.A M'.M M.M _ _ fun x y => ?_
      change tensorDegToBalanced M' M (tensorToDeg M' M (x ⊗ₜ[R] y)) = _
      induction x using DirectSum.Decomposition.inductionOn M'.grading with
      | zero => simp
      | add x x' hx hx' =>
        simp only [TensorProduct.add_tmul, map_add, hx, hx', LinearMap.id_apply,
          LinearMap.add_apply]
      | homogeneous x =>
        induction y using DirectSum.Decomposition.inductionOn M.grading with
        | zero => simp
        | add y y' hy hy' =>
          simp only [TensorProduct.tmul_add, map_add, hy, hy', LinearMap.id_apply]
        | @homogeneous q y =>
          rename_i p
          rw [tensorToDeg_tmul_of_mem, tensorDegToBalanced, DirectSum.toModule_lof,
            Submodule.mkQ_apply, Submodule.liftQ_apply, tensorRawToBalanced_mk]
          rfl)
    (by
      refine DirectSum.linearMap_ext R fun n => tensorDeg_linearMap_ext M' M
        fun p q h x y => ?_
      subst h
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
      rw [tensorDegToBalanced, DirectSum.toModule_lof, Submodule.mkQ_apply,
        Submodule.liftQ_apply, tensorRawToBalanced_mk]
      exact tensorToDeg_tmul_of_mem M' M p q x y)

/-- Under `balancedTensorGradedEquiv`, the class of a homogeneous `x ⊗ y` in degree `p + q` is
the symbol `x ⊗ y` of `M' ⊗_A M`: the universal map `M' × M → M' ⊗_A M` is compatible with the
gradings. -/
@[stacks 09LL "the map M × N → M ⊗_A N is compatible with gradings"]
theorem balancedTensorGradedEquiv_lof_tmul (p q n : ℤ) (h : p + q = n) (x : M'.grading p)
    (y : M.grading q) :
    balancedTensorGradedEquiv M' M (DirectSum.lof R ℤ (fun n => tensorDeg M' M n) n
        ((tensorRel M' M n).mkQ (tensorMk M' M n p q h x y))) =
      StacksDraft.BalancedTensorProduct.tmul R A.A M'.M M.M x y := by
  change tensorDegToBalanced M' M _ = _
  rw [tensorDegToBalanced, DirectSum.toModule_lof, Submodule.mkQ_apply, Submodule.liftQ_apply,
    tensorRawToBalanced_mk]

/-! ## The universal property for graded bilinear maps -/

/-- A graded `A`-balanced bilinear map from `M' × M` to the graded `R`-module with pieces `Q n`:
`R`-bilinear maps `(M')^p × M^q → Q^{p + q}` with `f (x a) y = f x (a y)`. -/
structure GradedBalancedBilinear (Q : ℤ → Type u) [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] where
  /-- The component in degrees `p` and `q`. -/
  map : ∀ p q n : ℤ, p + q = n → M'.grading p →ₗ[R] M.grading q →ₗ[R] Q n
  /-- `A`-balancedness on homogeneous elements. -/
  balance : ∀ (p i q n : ℤ) (h₁ : p + i + q = n) (h₂ : p + (i + q) = n)
      (x : M'.grading p) (a : A.grading i) (y : M.grading q),
    map (p + i) q n h₁ (gradedRightSmul M' p i x a) y =
      map p (i + q) n h₂ x (gradedLeftSmul M i q a y)

variable {M' M} in
/-- Two graded balanced bilinear maps with the same components agree. -/
theorem GradedBalancedBilinear.ext {Q : ℤ → Type u} [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] {b c : GradedBalancedBilinear M' M Q}
    (h : ∀ (p q n : ℤ) (hpq : p + q = n) (x : M'.grading p) (y : M.grading q),
      b.map p q n hpq x y = c.map p q n hpq x y) : b = c := by
  have hm : b.map = c.map := by
    funext p q n hpq
    exact LinearMap.ext fun x => LinearMap.ext fun y => h p q n hpq x y
  cases b; cases c; cases hm; rfl

variable {M' M} in
/-- The components of a graded balanced bilinear map depend on the degrees only through the
underlying elements. -/
theorem GradedBalancedBilinear.map_congr {Q : ℤ → Type u} [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] (b : GradedBalancedBilinear M' M Q) (p q q' n : ℤ) (h : p + q = n)
    (h' : p + q' = n) (x : M'.grading p) (y : M.grading q) (y' : M.grading q')
    (hy : (y : M.M) = (y' : M.M)) : b.map p q n h x y = b.map p q' n h' x y' := by
  have hq : q = q' := by omega
  subst hq
  obtain rfl : y = y' := Subtype.ext hy
  rfl

/-- The map out of the degree-`n` piece determined by a graded balanced bilinear map. -/
noncomputable def gradedTensorDegDesc {Q : ℤ → Type u} [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] (b : GradedBalancedBilinear M' M Q) (n : ℤ) :
    tensorDeg M' M n →ₗ[R] Q n :=
  Submodule.liftQ _
    (DirectSum.toModule R ℤ _ fun i => TensorProduct.lift (b.map i (n - i) n (by omega))) <| by
      rw [tensorRel, Submodule.span_le]
      rintro z ⟨p, i, q, h, x, a, y, rfl⟩
      have hmk : ∀ (p q : ℤ) (h : p + q = n) (x : M'.grading p) (y : M.grading q),
          (DirectSum.toModule R ℤ _ fun i => TensorProduct.lift (b.map i (n - i) n (by omega)))
            (tensorMk M' M n p q h x y) = b.map p q n h x y := by
        intro p q h x y
        change (DirectSum.toModule R ℤ _ fun i => TensorProduct.lift (b.map i (n - i) n (by omega)))
          (DirectSum.lof R ℤ (fun i => M'.grading i ⊗[R] M.grading (n - i)) p
            (x ⊗ₜ[R] gradingCast M.grading (show q = n - p by omega) y)) = _
        rw [DirectSum.toModule_lof, TensorProduct.lift.tmul]
        exact b.map_congr p (n - p) q n (by omega) h x _ y rfl
      change _ = (0 : Q n)
      rw [tensorRelator, map_sub, hmk, hmk, sub_eq_zero]
      exact b.balance p i q n (by omega) (by omega) x a y

/-- `gradedTensorDegDesc` sends the class of `x ⊗ y` to `b.map p q n h x y`. -/
theorem gradedTensorDegDesc_mk {Q : ℤ → Type u} [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] (b : GradedBalancedBilinear M' M Q) (p q n : ℤ) (h : p + q = n)
    (x : M'.grading p) (y : M.grading q) :
    gradedTensorDegDesc M' M b n ((tensorRel M' M n).mkQ (tensorMk M' M n p q h x y)) =
      b.map p q n h x y := by
  change (DirectSum.toModule R ℤ _ fun i => TensorProduct.lift (b.map i (n - i) n (by omega)))
    (DirectSum.lof R ℤ (fun i => M'.grading i ⊗[R] M.grading (n - i)) p
      (x ⊗ₜ[R] gradingCast M.grading (show q = n - p by omega) y)) = _
  rw [DirectSum.toModule_lof, TensorProduct.lift.tmul]
  exact b.map_congr p (n - p) q n (by omega) h x _ y rfl

/-- The universal graded balanced bilinear map `(x, y) ↦ x ⊗ y` into the pieces of `M' ⊗_A M`. -/
noncomputable def gradedTensorTmul : GradedBalancedBilinear M' M (tensorDeg M' M) where
  map p q n h := (tensorMk M' M n p q h).compr₂ (tensorRel M' M n).mkQ
  balance p i q n h₁ h₂ x a y :=
    (Submodule.Quotient.eq (tensorRel M' M n)).2 (tensorRelator_mem M' M p i q n (by omega) x a y)

/-- **The universal property of the graded tensor product.** Maps of graded `R`-modules from
`M' ⊗_A M` (with the pieces `tensorDeg M' M n` of `balancedTensorGradedEquiv`) to a graded
`R`-module with pieces `Q n` are the graded `A`-balanced bilinear maps `M' × M → Q`:
`GradedBilinear_A(M' × M, Q) = Hom_{graded R-modules}(M' ⊗_A M, Q)`. -/
@[stacks 09LL "GradedBilinear_A(M × N, Q) = Hom_{graded R-modules}(M ⊗_A N, Q)"]
noncomputable def gradedTensorHomEquiv (Q : ℤ → Type u) [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] :
    (∀ n : ℤ, tensorDeg M' M n →ₗ[R] Q n) ≃ GradedBalancedBilinear M' M Q where
  toFun g :=
    { map := fun p q n h => ((gradedTensorTmul M' M).map p q n h).compr₂ (g n)
      balance := fun p i q n h₁ h₂ x a y =>
        congrArg (g n) ((gradedTensorTmul M' M).balance p i q n h₁ h₂ x a y) }
  invFun b := gradedTensorDegDesc M' M b
  left_inv _ := funext fun n => tensorDeg_linearMap_ext M' M fun p q h x y =>
    gradedTensorDegDesc_mk M' M _ p q n h x y
  right_inv b := GradedBalancedBilinear.ext fun p q n h x y =>
    gradedTensorDegDesc_mk M' M b p q n h x y

end DifferentialGraded
