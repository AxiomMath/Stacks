module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorAssoc
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorHom

/-! # The inverse of the associativity comparison

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule, let `N'` be a differential graded
`(B, C)`-bimodule and let `M` be a right differential graded `A`-module. This file builds the
comparison `(M ⊗_A N) ⊗_B N' ⟶ M ⊗_A (N ⊗_B N')` inverse to
`DifferentialGraded.Bimodule.assocForward`.

The relative tensor product has only the universal property of Tag 09LM as a handle, and that
property produces homomorphisms out of `X ⊗_B N'` into a right differential graded `C`-module
from balanced bilinear maps on `X` and `N'`; writing one down with `X = M ⊗_A N` therefore needs a
map out of `M ⊗_A N` for each element of `N'`, which the universal property of `M ⊗_A N` cannot
give, its targets being right differential graded `B`-modules. The internal hom supplies the
missing room: `Hom^•_C(N', M ⊗_A (N ⊗_B N'))` *is* a right differential graded `B`-module, the
pairing `(x, y) ↦ (y' ↦ x ⊗ (y ⊗ y'))` is a balanced bilinear map into it, and the tensor–Hom
bijection of Tag 09LN turns the resulting homomorphism
`M ⊗_A N ⟶ Hom^•_C(N', M ⊗_A (N ⊗_B N'))` into the comparison sought.

## Main definitions

* `DifferentialGraded.Bimodule.assocPairHom`: the homogeneous map `y' ↦ x ⊗ (y ⊗ y')` attached to
  homogeneous elements `x` of `M` and `y` of `N`.
* `DifferentialGraded.Bimodule.assocEval`: evaluation of the presented internal hom.
* `DifferentialGraded.Bimodule.assocInvTotal`: the pairing `(x, y) ↦ (y' ↦ x ⊗ (y ⊗ y'))`, as a
  balanced bilinear map into the internal hom.
* `DifferentialGraded.Bimodule.assocPsi`: the homomorphism
  `M ⊗_A N ⟶ Hom^•_C(N', M ⊗_A (N ⊗_B N'))` it factors through.
* `DifferentialGraded.Bimodule.assocInverse`: the comparison
  `(M ⊗_A N) ⊗_B N' ⟶ M ⊗_A (N ⊗_B N')`.

## Main results

* `DifferentialGraded.Bimodule.assocInverse_pure`: the comparison carries `(x ⊗ y) ⊗ y'` to
  `x ⊗ (y ⊗ y')`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product; [Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR) and
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ) are the internal hom and its functor, and
  [Tag 09LN](https://stacks.math.columbia.edu/tag/09LN) is the tensor–Hom bijection.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-! ### The pure tensors of the composite bimodule -/

/-- The pure tensor `y ⊗ y'` of `y ∈ N^q` and `y' ∈ N'^s` lies in degree `q + s` of `N ⊗_B N'`.
-/
theorem compPure_mem (N : Bimodule A B) (N' : Bimodule B C) {q s : ℤ}
    (y : N.rightModule.grading q) (y' : N'.rightModule.grading s) :
    compPure N N' (y : N.rightModule.M) (y' : N'.rightModule.M) ∈
      (compTensor N N').rightModule.grading (q + s) :=
  (tensorPure N' N.rightModule).map_grading q s y y'

/-- The pure tensors of `N ⊗_B N'` are right `C`-linear in the second factor:
`y ⊗ (y' c) = (y ⊗ y') c`. -/
theorem compPure_op_smul (N : Bimodule A B) (N' : Bimodule B C) (y : N.rightModule.M)
    (y' : N'.rightModule.M) (c : C.A) :
    compPure N N' y (MulOpposite.op c • y') = MulOpposite.op c • compPure N N' y y' :=
  (tensorPure N' N.rightModule).map_right y y' c

/-- The graded Leibniz rule for the pure tensors of `N ⊗_B N'`: for `y ∈ N^q`,
`d(y ⊗ y') = d y ⊗ y' + (-1)^q y ⊗ d y'`. -/
theorem compPure_d (N : Bimodule A B) (N' : Bimodule B C) {q : ℤ}
    (y : N.rightModule.grading q) (y' : N'.rightModule.M) :
    (compTensor N N').rightModule.d (compPure N N' (y : N.rightModule.M) y') =
      compPure N N' (N.rightModule.d (y : N.rightModule.M)) y' +
        ((q.negOnePow : ℤ)) • compPure N N' (y : N.rightModule.M) (N'.rightModule.d y') :=
  (tensorPure N' N.rightModule).map_d q y y'

/-- The total left action of a homogeneous `a ∈ A` on `N ⊗_B N'` acts on the first factor of a
pure tensor: `a (y ⊗ y') = (a y) ⊗ y'`. -/
theorem compPure_leftActionTotal (N : Bimodule A B) (N' : Bimodule B C) {n : ℤ}
    (a : A.grading n) (y : N.rightModule.M) (y' : N'.rightModule.M) :
    leftActionTotal A C (compTensor N N').rightModule (compTensor N N').leftAction.1 (a : A.A)
        (compPure N N' y y') =
      compPure N N' (leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) y) y' :=
  compTensor_leftActionTotal_tensorPure N N' a y y'

/-! ### The pure tensors of a relative tensor product, balanced through the total action -/

/-- The pure tensors are balanced over `A`, for an arbitrary homogeneous element of `A` acting
through the total left action rather than through a graded component. -/
theorem tensorPure_balance_total (T : Bimodule A C) (M : DifferentialGradedModule.{u, u, u} A)
    {n : ℤ} (a : A.grading n) (x : M.M) (z : T.rightModule.M) :
    (tensorPure T M).toLinearMap (MulOpposite.op (a : A.A) • x) z =
      (tensorPure T M).toLinearMap x
        (leftActionTotal A C T.rightModule T.leftAction.1 (a : A.A) z) := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x x' hx hx' =>
    simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
  | @homogeneous p x =>
    induction z using DirectSum.Decomposition.inductionOn T.rightModule.grading with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | @homogeneous q z =>
      rw [(tensorPure T M).balance p q n x z a,
        leftActionTotal_apply A C T.rightModule T.leftAction.1 n a]
      exact congrArg (fun w => (tensorPure T M).toLinearMap (x : M.M) w)
        (totalizeCochain_apply_of_eq C T.rightModule n q (q + n) rfl
          (T.leftAction.1.action n a) z).symm

/-- The pure tensors of `N ⊗_B N'` are balanced over `B` for a homogeneous `b ∈ B` acting
through the total left action on `N'`: `(y b) ⊗ y' = y ⊗ (b y')`. -/
theorem compPure_balance_total (N : Bimodule A B) (N' : Bimodule B C) {m' : ℤ}
    (b : B.grading m') (y : N.rightModule.M) (y' : N'.rightModule.M) :
    compPure N N' (MulOpposite.op (b : B.A) • y) y' =
      compPure N N' y
        (leftActionTotal B C N'.rightModule N'.leftAction.1 (b : B.A) y') :=
  tensorPure_balance_total N' N.rightModule b y y'

/-! ### The pairing `(x, y) ↦ (y' ↦ x ⊗ (y ⊗ y'))` -/

/-- The chosen presentation of the internal hom `Hom^•_C(N', M ⊗_A (N ⊗_B N'))`, a right
differential graded `B`-module. -/
abbrev assocHomPresentation (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    HomModuleData B C N'.rightModule (tensorObj (compTensor N N') M) N'.leftAction :=
  homPresentation N' (tensorObj (compTensor N N') M)

/-- The map `y' ↦ x ⊗ (y ⊗ y')`, `R`-linear in `y'`. -/
def assocPairMap (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M) :
    N'.rightModule.M →ₗ[R] (tensorObj (compTensor N N') M).M :=
  (assocPure N N' M x).comp (compPure N N' y)

/-- The map `assocPairMap N N' M x y` sends `y'` to `x ⊗ (y ⊗ y')`. -/
theorem assocPairMap_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M)
    (y' : N'.rightModule.M) :
    assocPairMap N N' M x y y' = assocPure N N' M x (compPure N N' y y') := rfl

/-- For homogeneous `x ∈ M^p` and `y ∈ N^q` the map `y' ↦ x ⊗ (y ⊗ y')` is a homogeneous right
`C`-linear map `N' ⟶ M ⊗_A (N ⊗_B N')` of degree `p + q`. -/
def assocPairHom (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.grading p)
    (y : N.rightModule.grading q) :
    HomogeneousMap C N'.rightModule (tensorObj (compTensor N N') M) (p + q) :=
  ⟨assocPairMap N N' M (x : M.M) (y : N.rightModule.M), by
    rw [mem_homogeneousMapSubmodule]
    refine ⟨fun s y' hy' => ?_, fun c y' => ?_⟩
    · have h2 := (tensorPure (compTensor N N') M).map_grading p (q + s) x
        (⟨compPure N N' (y : N.rightModule.M) y', compPure_mem N N' y ⟨y', hy'⟩⟩ :
          (compTensor N N').rightModule.grading (q + s))
      rw [show p + (q + s) = s + (p + q) from by ring] at h2
      exact h2
    · rw [assocPairMap_apply, assocPairMap_apply, compPure_op_smul]
      exact (tensorPure (compTensor N N') M).map_right (x : M.M)
        (compPure N N' (y : N.rightModule.M) y') c⟩

/-- The homogeneous map `y' ↦ x ⊗ (y ⊗ y')` is additive in `x`. -/
theorem assocPairHom_add_left (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x x' : M.grading p)
    (y : N.rightModule.grading q) :
    assocPairHom N N' M (x + x') y = assocPairHom N N' M x y + assocPairHom N N' M x' y :=
  Subtype.ext (LinearMap.ext fun z => by
    change assocPure N N' M ((x : M.M) + (x' : M.M)) (compPure N N' (y : N.rightModule.M) z) =
      assocPure N N' M (x : M.M) (compPure N N' (y : N.rightModule.M) z) +
        assocPure N N' M (x' : M.M) (compPure N N' (y : N.rightModule.M) z)
    rw [map_add (assocPure N N' M), LinearMap.add_apply])

/-- The homogeneous map `y' ↦ x ⊗ (y ⊗ y')` commutes with scalars of `R` in `x`. -/
theorem assocPairHom_smul_left (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (r : R) (x : M.grading p)
    (y : N.rightModule.grading q) :
    assocPairHom N N' M (r • x) y = r • assocPairHom N N' M x y :=
  Subtype.ext (LinearMap.ext fun z => by
    change assocPure N N' M (r • (x : M.M)) (compPure N N' (y : N.rightModule.M) z) =
      r • assocPure N N' M (x : M.M) (compPure N N' (y : N.rightModule.M) z)
    rw [map_smul (assocPure N N' M), LinearMap.smul_apply])

/-- The homogeneous map `y' ↦ x ⊗ (y ⊗ y')` is additive in `y`. -/
theorem assocPairHom_add_right (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.grading p)
    (y y' : N.rightModule.grading q) :
    assocPairHom N N' M x (y + y') = assocPairHom N N' M x y + assocPairHom N N' M x y' :=
  Subtype.ext (LinearMap.ext fun z => by
    change assocPure N N' M (x : M.M)
        (compPure N N' ((y : N.rightModule.M) + (y' : N.rightModule.M)) z) =
      assocPure N N' M (x : M.M) (compPure N N' (y : N.rightModule.M) z) +
        assocPure N N' M (x : M.M) (compPure N N' (y' : N.rightModule.M) z)
    rw [map_add (compPure N N'), LinearMap.add_apply, map_add])

/-- The homogeneous map `y' ↦ x ⊗ (y ⊗ y')` commutes with scalars of `R` in `y`. -/
theorem assocPairHom_smul_right (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (r : R) (x : M.grading p)
    (y : N.rightModule.grading q) :
    assocPairHom N N' M x (r • y) = r • assocPairHom N N' M x y :=
  Subtype.ext (LinearMap.ext fun z => by
    change assocPure N N' M (x : M.M) (compPure N N' (r • (y : N.rightModule.M)) z) =
      r • assocPure N N' M (x : M.M) (compPure N N' (y : N.rightModule.M) z)
    rw [map_smul (compPure N N'), LinearMap.smul_apply, map_smul])

/-! ### Evaluation of the presented internal hom -/

/-- Evaluation on a homogeneous piece of the presented internal hom. -/
def assocEvalComponent (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (m : ℤ) :
    (assocHomPresentation N N' M).module.grading m →ₗ[R]
      N'.rightModule.M →ₗ[R] (tensorObj (compTensor N N') M).M :=
  (homogeneousMapSubmodule C N'.rightModule (tensorObj (compTensor N N') M) m).subtype.comp
    ((assocHomPresentation N N' M).homogeneousEquiv m).toLinearMap

/-- **Evaluation of the presented internal hom**: an element is read as the right `C`-linear map
`N' → M ⊗_A (N ⊗_B N')` that its homogeneous pieces present. -/
def assocEval (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    (assocHomPresentation N N' M).module.M →ₗ[R]
      N'.rightModule.M →ₗ[R] (tensorObj (compTensor N N') M).M :=
  (DirectSum.toModule R ℤ _ (assocEvalComponent N N' M)).comp
    (DirectSum.decomposeLinearEquiv (assocHomPresentation N N' M).module.grading).toLinearMap

/-- The evaluation of a homogeneous element of degree `m` of the presented internal hom is the
homogeneous map of degree `m` it presents. -/
theorem assocEval_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (m : ℤ)
    (z : (assocHomPresentation N N' M).module.M)
    (hz : z ∈ (assocHomPresentation N N' M).module.grading m) :
    assocEval N N' M z = ((assocHomPresentation N N' M).homogeneousEquiv m ⟨z, hz⟩).1 := by
  change (DirectSum.toModule R ℤ _ (assocEvalComponent N N' M))
    ((DirectSum.decomposeLinearEquiv (assocHomPresentation N N' M).module.grading)
      ((⟨z, hz⟩ : (assocHomPresentation N N' M).module.grading m) :
        (assocHomPresentation N N' M).module.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rfl

/-- Two homogeneous elements of the presented internal hom of the same degree with the same
evaluation are equal. -/
theorem assocEval_injOn (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (m : ℤ)
    {z w : (assocHomPresentation N N' M).module.M}
    (hz : z ∈ (assocHomPresentation N N' M).module.grading m)
    (hw : w ∈ (assocHomPresentation N N' M).module.grading m)
    (h : ∀ y' : N'.rightModule.M, assocEval N N' M z y' = assocEval N N' M w y') : z = w := by
  have key : (assocHomPresentation N N' M).homogeneousEquiv m ⟨z, hz⟩ =
      (assocHomPresentation N N' M).homogeneousEquiv m ⟨w, hw⟩ :=
    Subtype.ext (LinearMap.ext fun y' => by
      rw [← assocEval_apply N N' M m z hz, ← assocEval_apply N N' M m w hw]
      exact h y')
  exact congrArg Subtype.val
    (((assocHomPresentation N N' M).homogeneousEquiv m).injective key)

/-- Evaluation of the differential of a homogeneous element: the differential of the presented
internal hom is the differential of the differential graded category. -/
theorem assocEval_d (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (m : ℤ)
    (z : (assocHomPresentation N N' M).module.M)
    (hz : z ∈ (assocHomPresentation N N' M).module.grading m) (y' : N'.rightModule.M) :
    assocEval N N' M ((assocHomPresentation N N' M).module.d z) y' =
      (tensorObj (compTensor N N') M).d (assocEval N N' M z y') -
        DifferentialGraded.gradedSign R m • assocEval N N' M z (N'.rightModule.d y') := by
  have hd : (assocHomPresentation N N' M).module.d z ∈
      (assocHomPresentation N N' M).module.grading (m + 1) :=
    (assocHomPresentation N N' M).module.d_mem m z hz
  rw [assocEval_apply N N' M (m + 1) _ hd, assocEval_apply N N' M m z hz]
  have hge : (⟨(assocHomPresentation N N' M).module.d z, hd⟩ :
        (assocHomPresentation N N' M).module.grading (m + 1)) =
      (assocHomPresentation N N' M).module.gradedDifferential m ⟨z, hz⟩ := rfl
  rw [hge, (assocHomPresentation N N' M).map_d m ⟨z, hz⟩]
  rfl

/-- Evaluation of the right action of a homogeneous element of `B`: the action is precomposition
with the left action on `N'`. -/
theorem assocEval_op_smul (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {m m' : ℤ}
    (z : (assocHomPresentation N N' M).module.M)
    (hz : z ∈ (assocHomPresentation N N' M).module.grading m) (b : B.grading m')
    (y' : N'.rightModule.M) :
    assocEval N N' M (MulOpposite.op (b : B.A) • z) y' =
      assocEval N N' M z
        (leftActionTotal B C N'.rightModule N'.leftAction.1 (b : B.A) y') := by
  have hzb : MulOpposite.op (b : B.A) • z ∈
      (assocHomPresentation N N' M).module.grading (m + m') :=
    (assocHomPresentation N N' M).module.smul_mem m m' z (b : B.A) hz b.property
  rw [assocEval_apply N N' M (m + m') _ hzb, assocEval_apply N N' M m z hz]
  induction y' using DirectSum.Decomposition.inductionOn N'.rightModule.grading with
  | zero => simp
  | add y' y'' hy' hy'' => simp only [map_add, hy', hy'']
  | @homogeneous s y' =>
    rw [leftActionTotal_apply B C N'.rightModule N'.leftAction.1 m' b]
    refine ((assocHomPresentation N N' M).map_smul m m' s ⟨z, hz⟩ b y').trans
      (congrArg (fun w => ((assocHomPresentation N N' M).homogeneousEquiv m ⟨z, hz⟩).1 w) ?_)
    exact (totalizeCochain_apply_of_eq C N'.rightModule m' s (s + m') rfl
      (N'.leftAction.1.action m' b) y').symm

/-! ### The pairing as a balanced bilinear map into the internal hom -/

/-- The pairing on a pair of homogeneous pieces, read into the presented internal hom. -/
def assocInvPiece (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (p q : ℤ) :
    M.grading p →ₗ[R] N.rightModule.grading q →ₗ[R]
      (assocHomPresentation N N' M).module.M where
  toFun x :=
    { toFun := fun y =>
        ((((assocHomPresentation N N' M).homogeneousEquiv (p + q)).symm
          (assocPairHom N N' M x y)) : (assocHomPresentation N N' M).module.M)
      map_add' := fun y y' => by
        rw [assocPairHom_add_right, map_add]
        rfl
      map_smul' := fun r y => by
        rw [RingHom.id_apply, assocPairHom_smul_right, map_smul]
        rfl }
  map_add' x x' := by
    refine LinearMap.ext fun y => ?_
    change ((((assocHomPresentation N N' M).homogeneousEquiv (p + q)).symm
      (assocPairHom N N' M (x + x') y)) : (assocHomPresentation N N' M).module.M) = _
    rw [assocPairHom_add_left, map_add]
    rfl
  map_smul' r x := by
    refine LinearMap.ext fun y => ?_
    change ((((assocHomPresentation N N' M).homogeneousEquiv (p + q)).symm
      (assocPairHom N N' M (r • x) y)) : (assocHomPresentation N N' M).module.M) = _
    rw [assocPairHom_smul_left, map_smul]
    rfl

/-- The pairing out of the whole of `N`, for a homogeneous element of `M`. -/
def assocInvRowFun (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ} (x : M.grading p) :
    N.rightModule.M →ₗ[R] (assocHomPresentation N N' M).module.M :=
  (DirectSum.toModule R ℤ (assocHomPresentation N N' M).module.M
    fun q => assocInvPiece N N' M p q x).comp
    (DirectSum.decomposeLinearEquiv N.rightModule.grading).toLinearMap

/-- On a homogeneous `y ∈ N^q`, `assocInvRowFun` is the pairing on the pieces `M^p` and `N^q`. -/
theorem assocInvRowFun_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.grading p)
    (y : N.rightModule.grading q) :
    assocInvRowFun N N' M x (y : N.rightModule.M) = assocInvPiece N N' M p q x y := by
  change (DirectSum.toModule R ℤ (assocHomPresentation N N' M).module.M
      fun i => assocInvPiece N N' M p i x)
      ((DirectSum.decomposeLinearEquiv N.rightModule.grading)
        (y : N.rightModule.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]

/-- The pairing, as an `R`-linear map in the homogeneous element of `M`. -/
def assocInvRow (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (p : ℤ) :
    M.grading p →ₗ[R] (N.rightModule.M →ₗ[R] (assocHomPresentation N N' M).module.M) where
  toFun x := assocInvRowFun N N' M x
  map_add' x x' := by
    refine LinearMap.ext fun y => ?_
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | @homogeneous q y =>
      rw [LinearMap.add_apply, assocInvRowFun_apply, assocInvRowFun_apply,
        assocInvRowFun_apply, (assocInvPiece N N' M p q).map_add x x', LinearMap.add_apply]
    | add y y' hy hy' =>
      rw [map_add, hy, hy']
      simp only [LinearMap.add_apply, map_add]
  map_smul' r x := by
    refine LinearMap.ext fun y => ?_
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | @homogeneous q y =>
      rw [LinearMap.smul_apply, RingHom.id_apply, assocInvRowFun_apply,
        assocInvRowFun_apply, (assocInvPiece N N' M p q).map_smul r x, LinearMap.smul_apply]
    | add y y' hy hy' =>
      rw [map_add, hy, hy']
      simp only [LinearMap.smul_apply, RingHom.id_apply, map_add]

/-- **The pairing `(x, y) ↦ (y' ↦ x ⊗ (y ⊗ y'))`**, as an `R`-bilinear map on the whole of `M`
and of `N` into the presented internal hom. -/
def assocInvTotal (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    M.M →ₗ[R] (N.rightModule.M →ₗ[R] (assocHomPresentation N N' M).module.M) :=
  (DirectSum.toModule R ℤ (N.rightModule.M →ₗ[R] (assocHomPresentation N N' M).module.M)
    fun p => assocInvRow N N' M p).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- The pairing of homogeneous `x ∈ M^p` and `y ∈ N^q` is the element of degree `p + q` of the
presented internal hom presenting the map `y' ↦ x ⊗ (y ⊗ y')`. -/
theorem assocInvTotal_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.grading p)
    (y : N.rightModule.grading q) :
    assocInvTotal N N' M (x : M.M) (y : N.rightModule.M) =
      ((((assocHomPresentation N N' M).homogeneousEquiv (p + q)).symm
        (assocPairHom N N' M x y)) : (assocHomPresentation N N' M).module.M) := by
  have h : assocInvTotal N N' M (x : M.M) = assocInvRowFun N N' M x := by
    change (DirectSum.toModule R ℤ _ fun i => assocInvRow N N' M i)
      ((DirectSum.decomposeLinearEquiv M.grading) (x : M.M)) = _
    rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
    rfl
  rw [h, assocInvRowFun_apply]
  rfl

/-- The pairing of homogeneous elements lies in the degree-`p + q` piece. -/
theorem assocInvTotal_mem (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.grading p)
    (y : N.rightModule.grading q) :
    assocInvTotal N N' M (x : M.M) (y : N.rightModule.M) ∈
      (assocHomPresentation N N' M).module.grading (p + q) := by
  rw [assocInvTotal_apply]
  exact (((assocHomPresentation N N' M).homogeneousEquiv (p + q)).symm
    (assocPairHom N N' M x y)).property

/-- Evaluating the pairing of homogeneous elements returns the map `y' ↦ x ⊗ (y ⊗ y')`. -/
theorem assocEval_assocInvTotal (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.grading p)
    (y : N.rightModule.grading q) (y' : N'.rightModule.M) :
    assocEval N N' M (assocInvTotal N N' M (x : M.M) (y : N.rightModule.M)) y' =
      assocPure N N' M (x : M.M) (compPure N N' (y : N.rightModule.M) y') := by
  rw [assocEval_apply N N' M (p + q) _ (assocInvTotal_mem N N' M x y)]
  have h : (⟨assocInvTotal N N' M (x : M.M) (y : N.rightModule.M),
        assocInvTotal_mem N N' M x y⟩ :
      (assocHomPresentation N N' M).module.grading (p + q)) =
      ((assocHomPresentation N N' M).homogeneousEquiv (p + q)).symm
        (assocPairHom N N' M x y) :=
    Subtype.ext (assocInvTotal_apply N N' M x y)
  rw [h, LinearEquiv.apply_symm_apply]
  rfl

/-- `DifferentialGraded.Bimodule.assocEval_assocInvTotal` with the homogeneous elements and their
memberships given separately. -/
theorem assocEval_assocInvTotal' (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.M) (hx : x ∈ M.grading p)
    (y : N.rightModule.M) (hy : y ∈ N.rightModule.grading q) (y' : N'.rightModule.M) :
    assocEval N N' M (assocInvTotal N N' M x y) y' =
      assocPure N N' M x (compPure N N' y y') :=
  assocEval_assocInvTotal N N' M ⟨x, hx⟩ ⟨y, hy⟩ y'

/-- `DifferentialGraded.Bimodule.assocInvTotal_mem` with the memberships given separately. -/
theorem assocInvTotal_mem' (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p q : ℤ} (x : M.M) (hx : x ∈ M.grading p)
    (y : N.rightModule.M) (hy : y ∈ N.rightModule.grading q) :
    assocInvTotal N N' M x y ∈ (assocHomPresentation N N' M).module.grading (p + q) :=
  assocInvTotal_mem N N' M ⟨x, hx⟩ ⟨y, hy⟩

/-- The sign `(-1)^n`, acting as an integer, is the scalar `gradedSign R n`. -/
private theorem negOnePow_zsmul_eq_gradedSign_smul {V : Type*} [AddCommGroup V] [Module R V]
    (n : ℤ) (v : V) : ((n.negOnePow : ℤ)) • v = DifferentialGraded.gradedSign R n • v := by
  rw [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]

/-- The graded Leibniz rule for the pure tensors of `N ⊗_B N'`, with the sign as a scalar. -/
theorem compPure_d' (N : Bimodule A B) (N' : Bimodule B C) {q : ℤ} (y : N.rightModule.M)
    (hy : y ∈ N.rightModule.grading q) (y' : N'.rightModule.M) :
    (compTensor N N').rightModule.d (compPure N N' y y') =
      compPure N N' (N.rightModule.d y) y' +
        DifferentialGraded.gradedSign R q • compPure N N' y (N'.rightModule.d y') := by
  rw [← negOnePow_zsmul_eq_gradedSign_smul]
  exact (tensorPure N' N.rightModule).map_d q ⟨y, hy⟩ y'

/-- The graded Leibniz rule for the pure tensors of `M ⊗_A (N ⊗_B N')`, with the sign as a
scalar. -/
theorem assocPure_d' (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ} (x : M.M) (hx : x ∈ M.grading p)
    (z : (compTensor N N').rightModule.M) :
    (tensorObj (compTensor N N') M).d (assocPure N N' M x z) =
      assocPure N N' M (M.d x) z +
        DifferentialGraded.gradedSign R p •
          assocPure N N' M x ((compTensor N N').rightModule.d z) := by
  rw [← negOnePow_zsmul_eq_gradedSign_smul]
  exact (tensorPure (compTensor N N') M).map_d p ⟨x, hx⟩ z

/-! ### The pairing is a balanced bilinear map -/

/-- **The pairing `(x, y) ↦ (y' ↦ x ⊗ (y ⊗ y'))` is a balanced bilinear map** from `M` and `N`
into `Hom^•_C(N', M ⊗_A (N ⊗_B N'))`. The three conditions are the corresponding conditions for
the two layers of pure tensors, read through the presentation of the internal hom: the graded
Leibniz rule twice, with the Koszul signs matching by
`DifferentialGraded.gradedSign_add`; the balancing of the outer pure tensors over `A` against the
left action on `N ⊗_B N'`; and the balancing of the inner ones over `B` against the right action
on the internal hom, which is precomposition with the left action on `N'`. -/
def assocInvBalanced (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    BalancedBilinearMap M N (assocHomPresentation N N' M).module where
  toLinearMap := assocInvTotal N N' M
  map_grading p q x y := assocInvTotal_mem N N' M x y
  map_d p x y := by
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, smul_add, hy, hy']
      abel
    | @homogeneous q y =>
      have hsign : ((p.negOnePow : ℤ)) • assocInvTotal N N' M (x : M.M)
            (N.rightModule.d (y : N.rightModule.M)) =
          DifferentialGraded.gradedSign R p • assocInvTotal N N' M (x : M.M)
            (N.rightModule.d (y : N.rightModule.M)) := by
        rw [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]
      rw [hsign]
      refine assocEval_injOn N N' M (p + q + 1) ?_ ?_ fun y' => ?_
      · exact (assocHomPresentation N N' M).module.d_mem (p + q) _
          (assocInvTotal_mem N N' M x y)
      · refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
        · have h := assocInvTotal_mem' N N' M (M.d (x : M.M))
            (M.d_mem p (x : M.M) x.property) (y : N.rightModule.M) y.property
          rwa [show p + 1 + q = p + q + 1 from by ring] at h
        · have h := assocInvTotal_mem' N N' M (x : M.M) x.property
            (N.rightModule.d (y : N.rightModule.M))
            (N.rightModule.d_mem q (y : N.rightModule.M) y.property)
          rwa [show p + (q + 1) = p + q + 1 from by ring] at h
      · rw [assocEval_d N N' M (p + q) _ (assocInvTotal_mem N N' M x y) y',
          assocEval_assocInvTotal' N N' M (x : M.M) x.property (y : N.rightModule.M)
            y.property y',
          assocEval_assocInvTotal' N N' M (x : M.M) x.property (y : N.rightModule.M)
            y.property (N'.rightModule.d y'),
          map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
          assocEval_assocInvTotal' N N' M (M.d (x : M.M)) (M.d_mem p (x : M.M) x.property)
            (y : N.rightModule.M) y.property y',
          assocEval_assocInvTotal' N N' M (x : M.M) x.property
            (N.rightModule.d (y : N.rightModule.M))
            (N.rightModule.d_mem q (y : N.rightModule.M) y.property) y',
          assocPure_d' N N' M (x : M.M) x.property (compPure N N' (y : N.rightModule.M) y'),
          compPure_d' N N' (y : N.rightModule.M) y.property y', map_add, map_smul,
          smul_add, smul_smul, ← DifferentialGraded.gradedSign_add p q]
        abel
  balance p q n x y a := by
    refine assocEval_injOn N N' M (p + n + q) ?_ ?_ fun y' => ?_
    · have h := assocInvTotal_mem' N N' M (MulOpposite.op (a : A.A) • (x : M.M))
        (M.smul_mem p n (x : M.M) (a : A.A) x.property a.property) (y : N.rightModule.M)
        y.property
      exact h
    · have h := assocInvTotal_mem' N N' M (x : M.M) x.property
        (leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) (y : N.rightModule.M))
        (by
          rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
            totalizeCochain_apply_of_eq B N.rightModule n q (q + n) rfl
              (N.leftAction.1.action n a) y]
          exact ((N.leftAction.1.action n a).v q (q + n) (by omega) y).property)
      rw [show p + (q + n) = p + n + q from by ring] at h
      have he : leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A)
            (y : N.rightModule.M) =
          ((show N.rightModule.grading (q + n) from
            (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M) := by
        rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a]
        exact totalizeCochain_apply_of_eq B N.rightModule n q (q + n) rfl
          (N.leftAction.1.action n a) y
      rwa [he] at h
    · have he : leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A)
            (y : N.rightModule.M) =
          ((show N.rightModule.grading (q + n) from
            (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M) := by
        rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a]
        exact totalizeCochain_apply_of_eq B N.rightModule n q (q + n) rfl
          (N.leftAction.1.action n a) y
      rw [← he,
        assocEval_assocInvTotal' N N' M (MulOpposite.op (a : A.A) • (x : M.M))
          (M.smul_mem p n (x : M.M) (a : A.A) x.property a.property) (y : N.rightModule.M)
          y.property y',
        assocEval_assocInvTotal' N N' M (x : M.M) x.property
          (leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) (y : N.rightModule.M))
          (by rw [he]
              exact ((N.leftAction.1.action n a).v q (q + n) (by omega) y).property) y',
        ← compPure_leftActionTotal N N' a (y : N.rightModule.M) y',
        ← tensorPure_balance_total (compTensor N N') M a (x : M.M)
          (compPure N N' (y : N.rightModule.M) y')]
  map_right x y b := by
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
    | @homogeneous p x =>
      induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
      | zero => simp
      | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
      | @homogeneous q y =>
        induction b using DirectSum.Decomposition.inductionOn B.grading with
        | zero => simp
        | add b b' hb hb' =>
          simp only [MulOpposite.op_add, add_smul, map_add, hb, hb']
        | @homogeneous m' b =>
          refine assocEval_injOn N N' M (p + q + m') ?_ ?_ fun y' => ?_
          · have h := assocInvTotal_mem' N N' M (x : M.M) x.property
              (MulOpposite.op (b : B.A) • (y : N.rightModule.M))
              (N.rightModule.smul_mem q m' (y : N.rightModule.M) (b : B.A) y.property
                b.property)
            rwa [show p + (q + m') = p + q + m' from by ring] at h
          · exact (assocHomPresentation N N' M).module.smul_mem (p + q) m' _ (b : B.A)
              (assocInvTotal_mem N N' M x y) b.property
          · rw [assocEval_assocInvTotal' N N' M (x : M.M) x.property
                (MulOpposite.op (b : B.A) • (y : N.rightModule.M))
                (N.rightModule.smul_mem q m' (y : N.rightModule.M) (b : B.A) y.property
                  b.property) y',
              assocEval_op_smul N N' M _ (assocInvTotal_mem N N' M x y) b y',
              assocEval_assocInvTotal' N N' M (x : M.M) x.property (y : N.rightModule.M)
                y.property _,
              compPure_balance_total N N' b (y : N.rightModule.M) y']

/-! ### The comparison -/

/-- The homomorphism `M ⊗_A N ⟶ Hom^•_C(N', M ⊗_A (N ⊗_B N'))` through which the pairing
factors. -/
def assocPsi (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    tensorObj N M ⟶ (assocHomPresentation N N' M).module :=
  ((tensorDGFunctor N).universal M (assocHomPresentation N N' M).module
    (assocInvBalanced N N' M)).choose

/-- The homomorphism `assocPsi` carries the pure tensor `x ⊗ y` to the pairing of `x` and `y`. -/
theorem assocPsi_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M) :
    (assocPsi N N' M).toFun ((tensorPure N M).toLinearMap x y) = assocInvTotal N N' M x y :=
  ((tensorDGFunctor N).universal M (assocHomPresentation N N' M).module
    (assocInvBalanced N N' M)).choose_spec.1 x y

/-- **The comparison `(M ⊗_A N) ⊗_B N' ⟶ M ⊗_A (N ⊗_B N')`.** -/
def assocInverse (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    tensorObj N' (tensorObj N M) ⟶ tensorObj (compTensor N N') M :=
  (exists_tensorHomLift N' (tensorObj N M) (assocPsi N N' M)).choose

/-- For homogeneous `w ∈ M ⊗_A N`, the comparison carries `w ⊗ y'` to the evaluation of
`assocPsi N N' M w` at `y'`. -/
theorem assocInverse_apply_homogeneous (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ} (w : (tensorObj N M).grading p)
    (y' : N'.rightModule.M) :
    (assocInverse N N' M).toFun
        ((tensorPure N' (tensorObj N M)).toLinearMap (w : (tensorObj N M).M) y') =
      assocEval N N' M ((assocPsi N N' M).toFun (w : (tensorObj N M).M)) y' := by
  rw [assocInverse,
    (exists_tensorHomLift N' (tensorObj N M) (assocPsi N N' M)).choose_spec p w y',
    assocEval_apply N N' M p _ ((assocPsi N N' M).map_grading p
      (w : (tensorObj N M).M) w.property)]

/-- The comparison carries `w ⊗ y'` to the evaluation of `assocPsi N N' M w` at `y'`. -/
theorem assocInverse_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (w : (tensorObj N M).M)
    (y' : N'.rightModule.M) :
    (assocInverse N N' M).toFun
        ((tensorPure N' (tensorObj N M)).toLinearMap w y') =
      assocEval N N' M ((assocPsi N N' M).toFun w) y' := by
  induction w using DirectSum.Decomposition.inductionOn (tensorObj N M).grading with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw']
  | @homogeneous p w => exact assocInverse_apply_homogeneous N N' M w y'

/-- **The comparison carries `(x ⊗ y) ⊗ y'` to `x ⊗ (y ⊗ y')`.** -/
theorem assocInverse_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M)
    (y' : N'.rightModule.M) :
    (assocInverse N N' M).toFun
        ((tensorPure N' (tensorObj N M)).toLinearMap
          ((tensorPure N M).toLinearMap x y) y') =
      assocPure N N' M x (compPure N N' y y') := by
  rw [assocInverse_apply, assocPsi_pure]
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | @homogeneous p x =>
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y y'' hy hy'' => simp only [map_add, LinearMap.add_apply, hy, hy'']
    | @homogeneous q y => exact assocEval_assocInvTotal N N' M x y y'

end DifferentialGraded.Bimodule

end
