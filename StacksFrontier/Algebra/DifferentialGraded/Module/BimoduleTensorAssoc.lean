module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorPureSpan

/-! # Associativity of the relative tensor product with a bimodule

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule, let `N'` be a differential graded
`(B, C)`-bimodule and write `N'' = N ⊗_B N'` for the composite differential graded
`(A, C)`-bimodule of Tag 0BZ3. For a right differential graded `A`-module `M` the two iterated
relative tensor products `M ⊗_A N''` and `(M ⊗_A N) ⊗_B N'` agree.

This file builds the comparison in the direction `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'`, which the
functoriality of the tensor functor of Tag 09LM supplies directly: for a homogeneous `x ∈ M^p`
the map `y ↦ x ⊗ y` is a homogeneous right `B`-linear map `N ⟶ M ⊗_A N` of degree `p`, and its
image under the differential graded tensor functor with `N'` is a homogeneous map
`N'' ⟶ (M ⊗_A N) ⊗_B N'` of degree `p`, `R`-linearly in `x` and compatibly with the differential
and with the two actions. The resulting balanced bilinear map factors through `M ⊗_A N''`.

## Main definitions

* `DifferentialGraded.Bimodule.assocHomLeft`: the homogeneous right `B`-linear map
  `y ↦ x ⊗ y` attached to a homogeneous element of `M`.
* `DifferentialGraded.Bimodule.assocTotal`: the balanced bilinear map
  `(x, z) ↦ x ⊗ z` underlying the comparison, `R`-bilinear on the whole of `M` and of `N''`.
* `DifferentialGraded.Bimodule.assocForward`: the comparison
  `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'`.

## Main results

* `DifferentialGraded.Bimodule.compTensor_leftActionTotal_eq`: the left `A`-action on `N ⊗_B N'`
  is the image of left multiplication on `N` under the differential graded tensor functor, as an
  identity of `R`-linear endomorphisms.
* `DifferentialGraded.Bimodule.assocForward_pure`: the comparison carries `x ⊗ (y ⊗ y')` to
  `(x ⊗ y) ⊗ y'`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product, its universal property and its functoriality;
  [Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3) is the composite bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-! ### The two pure tensors, at the spelling of the composite bimodule

The right differential graded `C`-module underlying `N'' = N ⊗_B N'` is the relative tensor
product `tensorObj N' N.rightModule`, by `DifferentialGraded.Bimodule.compTensor_rightModule`,
which holds by unfolding. The two spellings are therefore interchangeable, but only one of them
lets the pure tensors of `N''` be fed to the pure tensors of `M ⊗_A N''` in a *syntactically*
well-typed application, which is what a rewrite needs; the two abbreviations below pin that
spelling. -/

/-- The pure tensors `y ⊗ y'` of `N'' = N ⊗_B N'`, read into the right differential graded
`C`-module underlying the composite bimodule. -/
abbrev compPure (N : Bimodule A B) (N' : Bimodule B C) :
    N.rightModule.M →ₗ[R] N'.rightModule.M →ₗ[R] (compTensor N N').rightModule.M :=
  (tensorPure N' N.rightModule).toLinearMap

/-- The pure tensors `x ⊗ z` of `M ⊗_A N''`. -/
abbrev assocPure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    M.M →ₗ[R] (compTensor N N').rightModule.M →ₗ[R] (tensorObj (compTensor N N') M).M :=
  (tensorPure (compTensor N N') M).toLinearMap

/-! ### The left action on the composite bimodule, as an endomorphism -/

/-- The left action of a homogeneous element of `A` on `N ⊗_B N'` is the image of left
multiplication by that element on `N` under the differential graded tensor functor with `N'`. -/
theorem compTensor_leftActionTotal_eq (N : Bimodule A B) (N' : Bimodule B C) {n : ℤ}
    (a : A.grading n) :
    leftActionTotal A C (compTensor N N').rightModule (compTensor N N').leftAction.1 (a : A.A) =
      ((tensorDGFunctor N').functor.map (leftMulHomogeneous N a)).1 := by
  rw [leftActionTotal_apply A C (compTensor N N').rightModule (compTensor N N').leftAction.1 n a]
  show totalizeCochain C (tensorObj N' N.rightModule) n (compAction N N' n a) = _
  rw [compAction_apply, totalizeCochain_homogeneousMapCochain]

/-- The left action of a homogeneous `a : A^n` on a homogeneous `y : M^q` is the component of
the cochain `L.action n a` from degree `q` to degree `q + n`. -/
private theorem leftActionTotal_apply_grading {M : DifferentialGradedModule.{u, u, u} B}
    (L : A.LeftAction M.toCochainComplex) {n q : ℤ} (a : A.grading n) (y : M.grading q) :
    leftActionTotal A B M L (a : A.A) (y : M.M) =
      ((show M.grading (q + n) from (L.action n a).v q (q + n) (by omega) y) : M.M) := by
  rw [leftActionTotal_apply A B M L n a]
  exact totalizeCochain_apply_of_eq B M n q (q + n) rfl (L.action n a) y

/-! ### The pure tensors of a fixed homogeneous element, as a homogeneous map -/

/-- For a homogeneous `x ∈ M^p` the map `y ↦ x ⊗ y` is a homogeneous right `B`-linear map
`N ⟶ M ⊗_A N` of degree `p`. -/
def assocHomLeft (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ}
    (x : M.grading p) : HomogeneousMap B N.rightModule (tensorObj N M) p :=
  ⟨(tensorPure N M).toLinearMap (x : M.M), by
    rw [mem_homogeneousMapSubmodule]
    refine ⟨fun i y hy => ?_, fun b y => (tensorPure N M).map_right (x : M.M) y b⟩
    simpa only [add_comm p i] using (tensorPure N M).map_grading p i x ⟨y, hy⟩⟩

/-- The underlying linear map of `y ↦ x ⊗ y` is the pure-tensor map at `x`. -/
@[simp] theorem assocHomLeft_val (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    {p : ℤ} (x : M.grading p) :
    (assocHomLeft N M x).1 = (tensorPure N M).toLinearMap (x : M.M) := rfl

/-- The map `y ↦ x ⊗ y` is additive in `x`. -/
theorem assocHomLeft_add (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ}
    (x x' : M.grading p) :
    assocHomLeft N M (x + x') = assocHomLeft N M x + assocHomLeft N M x' :=
  Subtype.ext (by
    show (tensorPure N M).toLinearMap ((x : M.M) + (x' : M.M)) = _
    rw [map_add]
    rfl)

/-- The map `y ↦ x ⊗ y` is `R`-linear in `x`. -/
theorem assocHomLeft_smul (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ}
    (r : R) (x : M.grading p) :
    assocHomLeft N M (r • x) = r • assocHomLeft N M x :=
  Subtype.ext (by
    show (tensorPure N M).toLinearMap (r • (x : M.M)) = _
    rw [map_smul]
    rfl)

/-- The differential of `y ↦ x ⊗ y` is `y ↦ (d x) ⊗ y`: the Leibniz rule for the pure tensors,
rearranged. -/
theorem assocHomLeft_d (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ}
    (x : M.grading p) :
    (dgCategory.{u, u, u} B).d (assocHomLeft N M x) =
      assocHomLeft N M (⟨M.d (x : M.M), M.d_mem p (x : M.M) x.property⟩ : M.grading (p + 1)) := by
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  have hd := (tensorPure N M).map_d p x y
  show (tensorObj N M).d ((tensorPure N M).toLinearMap (x : M.M) y) -
    DifferentialGraded.gradedSign R p •
      (tensorPure N M).toLinearMap (x : M.M) (N.rightModule.d y) = _
  rw [hd, ← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]
  show _ = (tensorPure N M).toLinearMap (M.d (x : M.M)) y
  abel

/-- Translating a homogeneous element of `M` by a homogeneous element of `A` composes the map
`y ↦ x ⊗ y` with the left multiplication on `N`: the pure tensors are balanced. -/
theorem assocHomLeft_op_smul (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    {p n : ℤ} (x : M.grading p) (a : A.grading n) :
    assocHomLeft N M
        (⟨MulOpposite.op (a : A.A) • (x : M.M),
          M.smul_mem p n (x : M.M) (a : A.A) x.property a.property⟩ : M.grading (p + n)) =
      (dgCategory.{u, u, u} B).comp (rfl : p + n = p + n) (assocHomLeft N M x)
        (leftMulHomogeneous N a) := by
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  show (tensorPure N M).toLinearMap (MulOpposite.op (a : A.A) • (x : M.M)) y =
    (tensorPure N M).toLinearMap (x : M.M)
      (leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) y)
  induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | @homogeneous q y =>
    rw [(tensorPure N M).balance p q n x y a,
      leftActionTotal_apply_grading N.leftAction.1 a y]

/-! ### The comparison `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'` -/

/-- The comparison on a homogeneous piece of `M`: the image of `y ↦ x ⊗ y` under the differential
graded tensor functor with `N'`, as an `R`-linear map in `x`. -/
def assocRow (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (p : ℤ) :
    M.grading p →ₗ[R]
      ((compTensor N N').rightModule.M →ₗ[R] (tensorObj N' (tensorObj N M)).M) where
  toFun x := ((tensorDGFunctor N').functor.map (assocHomLeft N M x)).1
  map_add' x x' := by
    rw [assocHomLeft_add, (tensorDGFunctor N').functor.map_add]
    rfl
  map_smul' r x := by
    rw [RingHom.id_apply, assocHomLeft_smul, (tensorDGFunctor N').functor.map_smul]
    rfl

/-- The value of the comparison on a homogeneous `x ∈ M^p`. -/
@[simp] theorem assocRow_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (p : ℤ) (x : M.grading p) :
    assocRow N N' M p x = ((tensorDGFunctor N').functor.map (assocHomLeft N M x)).1 := rfl

/-- The comparison `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'`, as an `R`-bilinear map on the whole of `M`
and of `N''`. -/
def assocTotal (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    M.M →ₗ[R] ((compTensor N N').rightModule.M →ₗ[R] (tensorObj N' (tensorObj N M)).M) :=
  (DirectSum.toModule R ℤ _ (assocRow N N' M)).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- On a homogeneous `x ∈ M^p` the total comparison is its degree-`p` row. -/
theorem assocTotal_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ} (x : M.grading p) :
    assocTotal N N' M (x : M.M) = ((tensorDGFunctor N').functor.map (assocHomLeft N M x)).1 := by
  show (DirectSum.toModule R ℤ _ (assocRow N N' M))
    ((DirectSum.decomposeLinearEquiv M.grading) (x : M.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rfl

/-- `DifferentialGraded.Bimodule.assocTotal_apply` with the homogeneous element and its
membership given separately, so that a rewrite can target a specific element of `M`. -/
theorem assocTotal_apply' (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ} (x : M.M) (hx : x ∈ M.grading p) :
    assocTotal N N' M x =
      ((tensorDGFunctor N').functor.map (assocHomLeft N M ⟨x, hx⟩)).1 :=
  assocTotal_apply N N' M ⟨x, hx⟩

/-- The left action of a homogeneous element of `A` on a homogeneous element of `N ⊗_B N'`, as
the image of left multiplication under the differential graded tensor functor. -/
theorem compTensor_leftAct_eq (N : Bimodule A B) (N' : Bimodule B C) {n q : ℤ}
    (a : A.grading n) (z : (compTensor N N').rightModule.grading q) :
    ((tensorDGFunctor N').functor.map (leftMulHomogeneous N a)).1
        (z : (compTensor N N').rightModule.M) =
      ((show (compTensor N N').rightModule.grading (q + n) from
        ((compTensor N N').leftAction.1.action n a).v q (q + n) (by omega) z) :
          (compTensor N N').rightModule.M) := by
  rw [← compTensor_leftActionTotal_eq N N' a]
  exact leftActionTotal_apply_grading (compTensor N N').leftAction.1 a z

/-- The comparison on a pure tensor of a homogeneous element of `M`. -/
theorem assocTotal_apply_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ} (x : M.grading p)
    (y : N.rightModule.M) (y' : N'.rightModule.M) :
    assocTotal N N' M (x : M.M)
        ((tensorPure N' N.rightModule).toLinearMap y y') =
      (tensorPure N' (tensorObj N M)).toLinearMap
        ((tensorPure N M).toLinearMap (x : M.M) y) y' := by
  rw [assocTotal_apply]
  exact (tensorDGFunctor N').map_pure (assocHomLeft N M x) y y'

/-- The comparison is right `C`-linear in the second variable: the image of a homogeneous map
under the differential graded tensor functor is a morphism of the differential graded category of
right differential graded `C`-modules. -/
theorem assocTotal_op_smul (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M)
    (z : (compTensor N N').rightModule.M) (c : C.A) :
    assocTotal N N' M x (MulOpposite.op c • z) =
      MulOpposite.op c • assocTotal N N' M x z := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
  | @homogeneous p x =>
    rw [assocTotal_apply]
    exact ((tensorDGFunctor N').functor.map (assocHomLeft N M x)).2.2 c z

/-- **The comparison is a balanced bilinear map.** It adds degrees and satisfies the graded
Leibniz rule because the differential graded tensor functor commutes with the differential, it is
balanced over `A` because that functor preserves composition and carries left multiplication on
`N` to the left action on `N ⊗_B N'`, and it is right `C`-linear because the functor lands in
right `C`-linear maps. -/
def assocBalanced (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    BalancedBilinearMap M (compTensor N N') (tensorObj N' (tensorObj N M)) where
  toLinearMap := assocTotal N N' M
  map_grading p q x z := by
    rw [assocTotal_apply]
    have h := ((tensorDGFunctor N').functor.map (assocHomLeft N M x)).2.1 q
      (z : (compTensor N N').rightModule.M) z.property
    rw [add_comm q p] at h
    exact h
  map_d p x z := by
    have h := congrArg Subtype.val ((tensorDGFunctor N').functor.map_d (assocHomLeft N M x))
    rw [assocHomLeft_d] at h
    have hz := LinearMap.congr_fun h z
    have e1 : assocTotal N N' M (M.d (x : M.M)) z =
        (tensorObj N' (tensorObj N M)).d (assocTotal N N' M (x : M.M) z) -
          DifferentialGraded.gradedSign R p •
            assocTotal N N' M (x : M.M) ((compTensor N N').rightModule.d z) := by
      rw [assocTotal_apply' N N' M (M.d (x : M.M)) (M.d_mem p (x : M.M) x.property),
        assocTotal_apply' N N' M (x : M.M) x.property]
      exact hz
    rw [e1, ← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]
    abel
  balance p q n x z a := by
    have h := congrArg Subtype.val
      ((tensorDGFunctor N').functor.map_comp (rfl : p + n = p + n)
        (assocHomLeft N M x) (leftMulHomogeneous N a))
    rw [← assocHomLeft_op_smul] at h
    have hz := LinearMap.congr_fun h (z : (compTensor N N').rightModule.M)
    rw [assocTotal_apply' N N' M (MulOpposite.op (a : A.A) • (x : M.M))
        (M.smul_mem p n (x : M.M) (a : A.A) x.property a.property),
      assocTotal_apply' N N' M (x : M.M) x.property]
    exact hz.trans (congrArg
      (fun w => ((tensorDGFunctor N').functor.map (assocHomLeft N M x)).1 w)
      (compTensor_leftAct_eq N N' a z))
  map_right x z c := assocTotal_op_smul N N' M x z c

/-- **The comparison `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'`**, the unique homomorphism of right
differential graded `C`-modules carrying `x ⊗ (y ⊗ y')` to `(x ⊗ y) ⊗ y'`. -/
def assocForward (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    tensorObj (compTensor N N') M ⟶ tensorObj N' (tensorObj N M) :=
  ((tensorDGFunctor (compTensor N N')).universal M (tensorObj N' (tensorObj N M))
    (assocBalanced N N' M)).choose

/-- The comparison `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'` on a pure tensor `x ⊗ z`. -/
theorem assocForward_apply (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M)
    (z : (compTensor N N').rightModule.M) :
    (assocForward N N' M).toFun ((tensorPure (compTensor N N') M).toLinearMap x z) =
      assocTotal N N' M x z :=
  ((tensorDGFunctor (compTensor N N')).universal M (tensorObj N' (tensorObj N M))
    (assocBalanced N N' M)).choose_spec.1 x z

/-- The comparison, read on the pure tensors of `N ⊗_B N'`, as an identity of `R`-linear maps in
the first variable. -/
theorem assocTotal_flip_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (y : N.rightModule.M)
    (y' : N'.rightModule.M) :
    (assocTotal N N' M).flip ((tensorPure N' N.rightModule).toLinearMap y y') =
      ((tensorPure N' (tensorObj N M)).toLinearMap.flip y').comp
        ((tensorPure N M).toLinearMap.flip y) := by
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | @homogeneous p x => exact assocTotal_apply_pure N N' M x y y'

/-- The comparison, read on the pure tensors of `N ⊗_B N'`. -/
theorem assocTotal_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M)
    (y' : N'.rightModule.M) :
    assocTotal N N' M x ((tensorPure N' N.rightModule).toLinearMap y y') =
      (tensorPure N' (tensorObj N M)).toLinearMap
        ((tensorPure N M).toLinearMap x y) y' :=
  LinearMap.congr_fun (assocTotal_flip_pure N N' M y y') x

/-- **The comparison carries `x ⊗ (y ⊗ y')` to `(x ⊗ y) ⊗ y'`.** -/
theorem assocForward_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M)
    (y' : N'.rightModule.M) :
    (assocForward N N' M).toFun
        ((tensorPure (compTensor N N') M).toLinearMap x
          ((tensorPure N' N.rightModule).toLinearMap y y')) =
      (tensorPure N' (tensorObj N M)).toLinearMap
        ((tensorPure N M).toLinearMap x y) y' :=
  (assocForward_apply N N' M x _).trans (assocTotal_pure N N' M x y y')

end DifferentialGraded.Bimodule

end
