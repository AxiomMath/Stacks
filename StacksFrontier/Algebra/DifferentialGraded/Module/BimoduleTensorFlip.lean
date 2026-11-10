module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleToTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap

/-! # The relative tensor product is symmetric across the graded opposite

Let `R` be a commutative ring, `(A, d)` a differential graded `R`-algebra and `V` a differential
graded `(A, R)`-bimodule, the base ring being placed in degree zero. For a right differential
graded `A`-module `M` the relative tensor product `M ⊗_A V` of Tag 09LM is isomorphic to
`Ṽ ⊗_{A^{opp}} M̂`, where `Ṽ` is the left differential graded `A`-module underlying `V` read as a
right differential graded `A^{opp}`-module by Tag 0FQ0 and `M̂` is `M` read as a differential
graded `(A^{opp}, R)`-bimodule as in
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleFlip.lean`. The isomorphism carries the
pure tensor `x ⊗ y` to `(-1)^{(deg x)(deg y)} y ⊗ x` and is natural in `M`.

## Main definitions

* `DifferentialGraded.Bimodule.flipModule`: the right differential graded `A^{opp}`-module `Ṽ`.
* `DifferentialGraded.Bimodule.psiBilinear` and `DifferentialGraded.Bimodule.phiBilinear`: the two
  balanced bilinear maps `(x, y) ↦ ± y ⊗ x` and `(y, x) ↦ ± x ⊗ y`.
* `DifferentialGraded.Bimodule.tensorFlipIso`: the isomorphism `M ⊗_A V ≅ Ṽ ⊗_{A^{opp}} M̂` of
  right differential graded `R`-modules.

## Main results

* `DifferentialGraded.Bimodule.tensorFlipIso_hom_pure`: the isomorphism on pure tensors.
* `DifferentialGraded.Bimodule.tensorFlipIso_naturality`: the isomorphism is natural in `M`, the
  transformation on the right-hand side being the one of Tag 09S3 attached to the homomorphism of
  bimodules `M̂ ⟶ M̂'`.

## Implementation notes

*Why the right algebra has to be the base ring.* The relative tensor product is characterized by
its universal property, which describes homomorphisms out of `M ⊗_A V` into right differential
graded `B`-modules only. For a general `B` the flipped product `Ṽ ⊗_{A^{opp}} M̂` carries a *left*
`B`-action, not a right one, so one of the two comparisons could not be written down. Over
`B = R` in degree zero the two coincide, which is why `V` is taken to be an `(A, R)`-bimodule; a
bimodule over a general `B` is brought into this form by
`DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso`, which says that restricting the
right algebra does not change the relative tensor product.

*The signs.* The comparison carries the Koszul sign `(-1)^{(deg x)(deg y)}`, which depends on both
degrees and is therefore not a map of either factor. It is assembled from the quadratic sign twist
of each of the three graded modules involved by
`DifferentialGraded.gradedSignTwist_bilinear`, so each of the two comparisons is a composite of
`R`-linear maps and all the sign bookkeeping happens once.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) for the relative tensor
  product, [Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0) for the identification of left
  modules with right modules over the graded opposite.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### The left module read over the graded opposite -/

/-- The left differential graded `A`-module underlying a differential graded `(A, R)`-bimodule,
read as a right differential graded `A^{opp}`-module through Tag 0FQ0. -/
abbrev flipModule (V : Bimodule A (degreeZero R R)) :
    DifferentialGradedModule.{u, u, u} (oppAlgebra A) :=
  (leftRightEquivalence R A).equivalence.functor.obj (toLeftModule A (degreeZero R R) V)

/-- The identification of the module underlying `flipModule V` with the module underlying `V`. -/
abbrev flipUnderlying (V : Bimodule A (degreeZero R R)) :
    (flipModule V).M ≃ₗ[R] V.rightModule.M :=
  (leftRightEquivalence R A).underlying (toLeftModule A (degreeZero R R) V)

/-- `flipUnderlying V` preserves degrees: `x` has degree `n` in `flipModule V` if and only if its
image has degree `n` in `V`. -/
theorem flipUnderlying_grading (V : Bimodule A (degreeZero R R)) (n : ℤ) (x : (flipModule V).M) :
    x ∈ (flipModule V).grading n ↔ flipUnderlying V x ∈ V.rightModule.grading n :=
  (leftRightEquivalence R A).grading _ n x

/-- The inverse of `flipUnderlying V` carries elements of degree `n` of `V` to elements of degree
`n` of `flipModule V`. -/
theorem flipUnderlying_symm_grading (V : Bimodule A (degreeZero R R)) {n : ℤ}
    {y : V.rightModule.M} (hy : y ∈ V.rightModule.grading n) :
    (flipUnderlying V).symm y ∈ (flipModule V).grading n := by
  rw [flipUnderlying_grading, LinearEquiv.apply_symm_apply]
  exact hy

/-- `flipUnderlying V` commutes with the differentials. -/
theorem flipUnderlying_d (V : Bimodule A (degreeZero R R)) (x : (flipModule V).M) :
    flipUnderlying V ((flipModule V).d x) = V.rightModule.d (flipUnderlying V x) :=
  (leftRightEquivalence R A).differential _ x

/-- The inverse of `flipUnderlying V` commutes with the differentials. -/
theorem flipUnderlying_symm_d (V : Bimodule A (degreeZero R R)) (y : V.rightModule.M) :
    (flipModule V).d ((flipUnderlying V).symm y) =
      (flipUnderlying V).symm (V.rightModule.d y) := by
  apply (flipUnderlying V).injective
  rw [flipUnderlying_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **The right action of `A^{opp}` on `Ṽ` is the left action of `A` on `V` with the Koszul
sign.** This is the content of Tag 0FQ0. -/
theorem flipUnderlying_action (V : Bimodule A (degreeZero R R)) {m n : ℤ}
    {a : (oppAlgebra A).A} (ha : a ∈ (oppAlgebra A).grading m)
    {x : (flipModule V).M} (hx : x ∈ (flipModule V).grading n) :
    flipUnderlying V (MulOpposite.op a • x) =
      (m * n).negOnePow • leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1
        ((opposite R A).equiv a) (flipUnderlying V x) :=
  (leftRightEquivalence R A).action _ m n a x ha hx

/-- The left action of an element `a` of degree `n` of `A` on an element `y` of degree `q` of `V`
is the component in degree `q` of the cochain map by which `a` acts. -/
theorem leftActionTotal_eq_action_v (V : Bimodule A (degreeZero R R)) {n q : ℤ} (a : A.grading n)
    (y : V.rightModule.grading q) :
    leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A)
        (y : V.rightModule.M) =
      ((show V.rightModule.grading (q + n) from
        (V.leftAction.1.action n a).v q (q + n) (by omega) y) : V.rightModule.M) := by
  rw [leftActionTotal_apply A (degreeZero R R) V.rightModule V.leftAction.1 n a,
    totalizeCochain_apply_of_eq (degreeZero R R) V.rightModule n q (q + n) (by omega)
      (V.leftAction.1.action n a) y]
  rfl

/-- The left action of an element of degree `n` of `A` on an element of degree `q` of `V` has
degree `q + n`. -/
theorem leftActionTotal_mem (V : Bimodule A (degreeZero R R)) {n q : ℤ} (a : A.grading n)
    (y : V.rightModule.grading q) :
    leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A)
        (y : V.rightModule.M) ∈ V.rightModule.grading (q + n) :=
  leftActionTotal_apply_mem A (degreeZero R R) V.rightModule V.leftAction.1 a y

/-! ### Signs -/

/-- `(-1)^{m + n} = (-1)^m (-1)^n` in `R`. -/
theorem negOnePowR_add (m n : ℤ) :
    (((m + n).negOnePow : ℤ) : R) = ((m.negOnePow : ℤ) : R) * ((n.negOnePow : ℤ) : R) := by
  rw [Int.negOnePow_add, Units.val_mul, Int.cast_mul]

/-- `(-1)^{2m} = 1` in `R`. -/
theorem negOnePowR_two_mul (m : ℤ) : (((2 * m).negOnePow : ℤ) : R) = 1 := by
  rw [Int.negOnePow_two_mul]
  norm_num

/-- `(-1)^{(p + 1) q} = (-1)^{p q} (-1)^q` in `R`. -/
theorem signR_succ_left (p q : ℤ) :
    ((((p + 1) * q).negOnePow : ℤ) : R) =
      (((p * q).negOnePow : ℤ) : R) * ((q.negOnePow : ℤ) : R) := by
  rw [show (p + 1) * q = p * q + q by ring, negOnePowR_add]

/-- `(-1)^p (-1)^{p (q + 1)} = (-1)^{p q}` in `R`. -/
theorem signR_succ_right (p q : ℤ) :
    ((p.negOnePow : ℤ) : R) * (((p * (q + 1)).negOnePow : ℤ) : R) =
      (((p * q).negOnePow : ℤ) : R) := by
  rw [show p * (q + 1) = p + p * q by ring, negOnePowR_add, ← mul_assoc, ← negOnePowR_add,
    show p + p = 2 * p by ring, negOnePowR_two_mul, one_mul]

/-- `(-1)^m (-1)^m = 1` in `R`. -/
theorem negOnePowR_self_mul (m : ℤ) :
    ((m.negOnePow : ℤ) : R) * ((m.negOnePow : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, show m + m = 2 * m by ring,
    negOnePowR_two_mul]

/-- The Koszul sign of the balance relation: moving a homogeneous scalar of degree `n` from the
left factor to the right factor costs `(-1)^{n p}` on one side and `(-1)^{n q}` on the other, and
the two shifts of the bidegree sign agree. -/
theorem signR_balance (n p q : ℤ) :
    ((((p + n) * q).negOnePow : ℤ) : R) =
      (((p * (q + n)).negOnePow : ℤ) : R) * (((n * q).negOnePow : ℤ) : R) *
        (((n * p).negOnePow : ℤ) : R) := by
  rw [show (p + n) * q = p * q + n * q by ring, show p * (q + n) = p * q + p * n by ring,
    negOnePowR_add, negOnePowR_add, show n * p = p * n by ring]
  linear_combination (-((((p * q).negOnePow : ℤ) : R) * (((n * q).negOnePow : ℤ) : R))) *
    negOnePowR_self_mul (R := R) (p * n)

/-- The right action of `A^{opp}` on `Ṽ`, with the sign read in the base ring. -/
theorem flipUnderlying_action' (V : Bimodule A (degreeZero R R)) {m n : ℤ}
    {a : (oppAlgebra A).A} (ha : a ∈ (oppAlgebra A).grading m)
    {x : (flipModule V).M} (hx : x ∈ (flipModule V).grading n) :
    flipUnderlying V (MulOpposite.op a • x) =
      (((m * n).negOnePow : ℤ) : R) •
        leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1
          ((opposite R A).equiv a) (flipUnderlying V x) := by
  rw [flipUnderlying_action V ha hx, Units.smul_def, ← Int.cast_smul_eq_zsmul R]

/-! ### The comparison from `M ⊗_A V` to `Ṽ ⊗_{A^{opp}} M̂` -/

variable (V : Bimodule A (degreeZero R R)) (M : DifferentialGradedModule.{u, u, u} A)

/-- The pure tensors of `Ṽ ⊗_{A^{opp}} M̂`, read in the other order and without the Koszul sign. -/
def flipTensorPure :
    M.M →ₗ[R] V.rightModule.M →ₗ[R] (tensorObj' (flip M) (flipModule V)).M :=
  (((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap.flip).compl₂
    (flipUnderlying V).symm.toLinearMap

/-- `flipTensorPure V M x y` is the pure tensor of `(flipUnderlying V).symm y` and `x`. -/
theorem flipTensorPure_apply (x : M.M) (y : V.rightModule.M) :
    flipTensorPure V M x y =
      ((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap
        ((flipUnderlying V).symm y) x := rfl

/-- The flipped pure tensor of elements of degrees `p` and `q` has degree `p + q`. -/
theorem flipTensorPure_mem {p q : ℤ} {x : M.M} (hx : x ∈ M.grading p) {y : V.rightModule.M}
    (hy : y ∈ V.rightModule.grading q) :
    flipTensorPure V M x y ∈ (tensorObj' (flip M) (flipModule V)).grading (p + q) := by
  rw [flipTensorPure_apply, add_comm p q]
  exact ((tensorDGFunctor (flip M)).pure (flipModule V)).map_grading q p
    ⟨_, flipUnderlying_symm_grading V hy⟩ ⟨x, hx⟩

/-- **The comparison `M ⊗_A V ⟶ Ṽ ⊗_{A^{opp}} M̂` on pure tensors**: it sends `x ⊗ y` to
`(-1)^{(deg x)(deg y)} y ⊗ x`, the sign being produced by the three quadratic sign twists. -/
def psiLinear : M.M →ₗ[R] V.rightModule.M →ₗ[R] (tensorObj' (flip M) (flipModule V)).M :=
  (((flipTensorPure V M).comp (gradedSignTwist R M.M M.grading)).compl₂
      (gradedSignTwist R V.rightModule.M V.rightModule.grading)).compr₂
    (gradedSignTwist R (tensorObj' (flip M) (flipModule V)).M
      (tensorObj' (flip M) (flipModule V)).grading)

/-- On elements `x` of degree `p` and `y` of degree `q`, `psiLinear V M x y` is
`(-1)^{p q} • flipTensorPure V M x y`. -/
theorem psiLinear_apply_mem {p q : ℤ} {x : M.M} (hx : x ∈ M.grading p) {y : V.rightModule.M}
    (hy : y ∈ V.rightModule.grading q) :
    psiLinear V M x y = (((p * q).negOnePow : ℤ) : R) • flipTensorPure V M x y :=
  gradedSignTwist_bilinear M.grading V.rightModule.grading _ (flipTensorPure V M) hx hy
    (flipTensorPure_mem V M hx hy)

/-- The Leibniz rule for the flipped pure tensors: for `y` of degree `q` the differential of
`flipTensorPure V M x y` is `flipTensorPure V M x (d y) + (-1)^q • flipTensorPure V M (d x) y`. -/
theorem flipTensorPure_map_d {q : ℤ} {y : V.rightModule.M} (hy : y ∈ V.rightModule.grading q)
    (x : M.M) :
    (tensorObj' (flip M) (flipModule V)).d (flipTensorPure V M x y) =
      flipTensorPure V M x (V.rightModule.d y) +
        ((q.negOnePow : ℤ) : R) • flipTensorPure V M (M.d x) y := by
  have h := ((tensorDGFunctor (flip M)).pure (flipModule V)).map_d q
    ⟨(flipUnderlying V).symm y, flipUnderlying_symm_grading V hy⟩ x
  rw [flipTensorPure_apply, flipTensorPure_apply, flipTensorPure_apply]
  rw [show (flipUnderlying V).symm (V.rightModule.d y) =
      (flipModule V).d ((flipUnderlying V).symm y) from (flipUnderlying_symm_d V y).symm]
  rw [← Int.cast_smul_eq_zsmul R (q.negOnePow : ℤ)] at h
  exact h

/-- **The balance relation for the flipped pure tensors.** Moving a homogeneous scalar of `A`
across costs the Koszul sign on each side, and the two agree up to the signs of the bidegrees. -/
theorem flipTensorPure_balance {p q n : ℤ} {x : M.M} (hx : x ∈ M.grading p)
    {y : V.rightModule.M} (hy : y ∈ V.rightModule.grading q) (a : A.grading n) :
    (((n * q).negOnePow : ℤ) : R) • flipTensorPure V M x
        (leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A) y) =
      (((n * p).negOnePow : ℤ) : R) •
        flipTensorPure V M (MulOpposite.op (a : A.A) • x) y := by
  have hab : (opposite R A).equiv ((opposite R A).equiv.symm (a : A.A)) = (a : A.A) :=
    LinearEquiv.apply_symm_apply _ _
  have habar : (opposite R A).equiv.symm (a : A.A) ∈ (oppAlgebra A).grading n := by
    rw [(opposite R A).mem_grading_iff n _, hab]
    exact a.property
  have hbal := ((tensorDGFunctor (flip M)).pure (flipModule V)).balance q p n
    ⟨(flipUnderlying V).symm y, flipUnderlying_symm_grading V hy⟩ ⟨x, hx⟩ ⟨_, habar⟩
  have hl : MulOpposite.op ((opposite R A).equiv.symm (a : A.A)) •
        ((flipUnderlying V).symm y) =
      (((n * q).negOnePow : ℤ) : R) • (flipUnderlying V).symm
        (leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A) y) := by
    apply (flipUnderlying V).injective
    rw [flipUnderlying_action' V habar (flipUnderlying_symm_grading V hy), hab,
      LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  have hr : ((show (flip M).rightModule.grading (p + n) from
          ((flip M).leftAction.1.action n ⟨_, habar⟩).v p (p + n) (by omega) ⟨x, hx⟩) :
        (flip M).rightModule.M) =
      (((n * p).negOnePow : ℤ) : R) • (MulOpposite.op (a : A.A) • x) := by
    rw [flip_leftAction M ⟨_, habar⟩ ⟨x, hx⟩, oppLeftActionRingHom_apply_mem M habar hx, hab]
  rw [hl, hr] at hbal
  calc (((n * q).negOnePow : ℤ) : R) • flipTensorPure V M x
          (leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A) y)
      = ((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap
          ((((n * q).negOnePow : ℤ) : R) • (flipUnderlying V).symm
            (leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A) y)) x := by
        rw [map_smul]
        exact (LinearMap.smul_apply _ _ x).symm
    _ = ((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap
          ((flipUnderlying V).symm y)
          ((((n * p).negOnePow : ℤ) : R) • (MulOpposite.op (a : A.A) • x)) := hbal
    _ = (((n * p).negOnePow : ℤ) : R) •
          flipTensorPure V M (MulOpposite.op (a : A.A) • x) y :=
        map_smul _ _ _

/-- The balance relation for the flipped pure tensors, solved for the left-hand side: moving `a` of
degree `n` across costs the sign `(-1)^{n q} (-1)^{n p}`. -/
theorem flipTensorPure_balance' {p q n : ℤ} {x : M.M} (hx : x ∈ M.grading p)
    {y : V.rightModule.M} (hy : y ∈ V.rightModule.grading q) (a : A.grading n) :
    flipTensorPure V M x
        (leftActionTotal A (degreeZero R R) V.rightModule V.leftAction.1 (a : A.A) y) =
      ((((n * q).negOnePow : ℤ) : R) * (((n * p).negOnePow : ℤ) : R)) •
        flipTensorPure V M (MulOpposite.op (a : A.A) • x) y := by
  rw [← smul_smul, ← flipTensorPure_balance V M hx hy a, smul_smul, negOnePowR_self_mul,
    one_smul]

/-- **The comparison `M ⊗_A V ⟶ Ṽ ⊗_{A^{opp}} M̂`, as a balanced bilinear map.** -/
def psiBilinear : BalancedBilinearMap M V (tensorObj' (flip M) (flipModule V)) where
  toLinearMap := psiLinear V M
  map_grading p q x y := by
    rw [psiLinear_apply_mem V M x.property y.property]
    exact Submodule.smul_mem _ _ (flipTensorPure_mem V M x.property y.property)
  map_d p x y := by
    induction y using DirectSum.Decomposition.inductionOn V.rightModule.grading with
    | zero => simp
    | add y z hy hz =>
      rw [map_add, map_add, map_add, map_add, map_add, smul_add, hy, hz]
      abel
    | @homogeneous q y =>
      rw [psiLinear_apply_mem V M x.property y.property,
        psiLinear_apply_mem V M (M.d_mem p x x.property) y.property,
        psiLinear_apply_mem V M x.property (V.rightModule.d_mem q y y.property),
        map_smul, flipTensorPure_map_d V M y.property,
        ← Int.cast_smul_eq_zsmul R (p.negOnePow : ℤ), smul_add, smul_smul, smul_smul,
        signR_succ_left p q, signR_succ_right p q]
      abel
  balance p q n x y a := by
    rw [← leftActionTotal_eq_action_v V a y,
      psiLinear_apply_mem V M (M.smul_mem p n x a x.property a.property) y.property,
      psiLinear_apply_mem V M x.property (leftActionTotal_mem V a y),
      flipTensorPure_balance' V M x.property y.property a, smul_smul, signR_balance n p q,
      mul_assoc]
  map_right x y b := by
    rw [op_smul_eq_smul_of_smul_one V.rightModule (show b = b • (1 : (degreeZero R R).A) by simp) y,
      op_smul_eq_smul_of_smul_one (tensorObj' (flip M) (flipModule V))
        (show b = b • (1 : (degreeZero R R).A) by simp) (psiLinear V M x y)]
    exact map_smul (psiLinear V M x) b y

/-- The sign identity `(-1)^{(q + n) p} (-1)^{n q} = (-1)^{q (p + n)} (-1)^{n p}` in `R`. -/
theorem signR_balance' (n p q : ℤ) :
    ((((q + n) * p).negOnePow : ℤ) : R) * (((n * q).negOnePow : ℤ) : R) =
      (((q * (p + n)).negOnePow : ℤ) : R) * (((n * p).negOnePow : ℤ) : R) := by
  rw [signR_balance n q p]
  linear_combination ((((q * (p + n)).negOnePow : ℤ) : R) * (((n * p).negOnePow : ℤ) : R)) *
    negOnePowR_self_mul (R := R) (n * q)

/-! ### The comparison from `Ṽ ⊗_{A^{opp}} M̂` to `M ⊗_A V` -/

/-- The pure tensors of `M ⊗_A V`, read in the other order and without the Koszul sign. -/
def tensorPureFlip :
    (flipModule V).M →ₗ[R] (flip M).rightModule.M →ₗ[R] (tensorObj' V M).M :=
  (((tensorDGFunctor V).pure M).toLinearMap.flip).comp (flipUnderlying V).toLinearMap

/-- `tensorPureFlip V M z x` is the pure tensor of `x` and `flipUnderlying V z`. -/
theorem tensorPureFlip_apply (z : (flipModule V).M) (x : (flip M).rightModule.M) :
    tensorPureFlip V M z x =
      ((tensorDGFunctor V).pure M).toLinearMap x (flipUnderlying V z) := rfl

/-- The pure tensor `tensorPureFlip V M z x` of elements of degrees `q` and `p` has degree
`q + p`. -/
theorem tensorPureFlip_mem {q p : ℤ} {z : (flipModule V).M} (hz : z ∈ (flipModule V).grading q)
    {x : (flip M).rightModule.M} (hx : x ∈ (flip M).rightModule.grading p) :
    tensorPureFlip V M z x ∈ (tensorObj' V M).grading (q + p) := by
  rw [tensorPureFlip_apply, add_comm q p]
  exact ((tensorDGFunctor V).pure M).map_grading p q ⟨x, hx⟩
    ⟨_, (flipUnderlying_grading V q z).1 hz⟩

/-- **The comparison `Ṽ ⊗_{A^{opp}} M̂ ⟶ M ⊗_A V` on pure tensors**: it sends `y ⊗ x` to
`(-1)^{(deg y)(deg x)} x ⊗ y`. -/
def phiLinear :
    (flipModule V).M →ₗ[R] (flip M).rightModule.M →ₗ[R] (tensorObj' V M).M :=
  (((tensorPureFlip V M).comp
        (gradedSignTwist R (flipModule V).M (flipModule V).grading)).compl₂
      (gradedSignTwist R (flip M).rightModule.M (flip M).rightModule.grading)).compr₂
    (gradedSignTwist R (tensorObj' V M).M (tensorObj' V M).grading)

/-- On elements `z` of degree `q` and `x` of degree `p`, `phiLinear V M z x` is
`(-1)^{q p} • tensorPureFlip V M z x`. -/
theorem phiLinear_apply_mem {q p : ℤ} {z : (flipModule V).M} (hz : z ∈ (flipModule V).grading q)
    {x : (flip M).rightModule.M} (hx : x ∈ (flip M).rightModule.grading p) :
    phiLinear V M z x = (((q * p).negOnePow : ℤ) : R) • tensorPureFlip V M z x :=
  gradedSignTwist_bilinear (flipModule V).grading (flip M).rightModule.grading _
    (tensorPureFlip V M) hz hx (tensorPureFlip_mem V M hz hx)

/-- The Leibniz rule for `tensorPureFlip`: for `x` of degree `p` the differential of
`tensorPureFlip V M z x` is `tensorPureFlip V M z (d x) + (-1)^p • tensorPureFlip V M (d z) x`. -/
theorem tensorPureFlip_map_d {p : ℤ} (z : (flipModule V).M) {x : (flip M).rightModule.M}
    (hx : x ∈ (flip M).rightModule.grading p) :
    (tensorObj' V M).d (tensorPureFlip V M z x) =
      tensorPureFlip V M z ((flip M).rightModule.d x) +
        ((p.negOnePow : ℤ) : R) • tensorPureFlip V M ((flipModule V).d z) x := by
  have h := ((tensorDGFunctor V).pure M).map_d p ⟨x, hx⟩ (flipUnderlying V z)
  rw [← Int.cast_smul_eq_zsmul R (p.negOnePow : ℤ)] at h
  rw [tensorPureFlip_apply, tensorPureFlip_apply, tensorPureFlip_apply, flipUnderlying_d]
  exact h

/-- **The comparison `Ṽ ⊗_{A^{opp}} M̂ ⟶ M ⊗_A V`, as a balanced bilinear map.** -/
def phiBilinear : BalancedBilinearMap (flipModule V) (flip M) (tensorObj' V M) where
  toLinearMap := phiLinear V M
  map_grading q p z x := by
    rw [phiLinear_apply_mem V M z.property x.property]
    exact Submodule.smul_mem _ _ (tensorPureFlip_mem V M z.property x.property)
  map_d q z x := by
    induction x using DirectSum.Decomposition.inductionOn (flip M).rightModule.grading with
    | zero => simp
    | add x x' hx hx' =>
      rw [map_add, map_add, map_add, map_add, map_add, smul_add, hx, hx']
      abel
    | @homogeneous p x =>
      rw [phiLinear_apply_mem V M z.property x.property,
        phiLinear_apply_mem V M ((flipModule V).d_mem q z z.property) x.property,
        phiLinear_apply_mem V M z.property
          ((flip M).rightModule.d_mem p x x.property),
        map_smul, tensorPureFlip_map_d V M (z : (flipModule V).M) x.property,
        ← Int.cast_smul_eq_zsmul R (q.negOnePow : ℤ), smul_add, smul_smul, smul_smul,
        signR_succ_left q p, signR_succ_right q p]
      abel
  balance q p n z x a := by
    have haA : (opposite R A).equiv (a : (oppAlgebra A).A) ∈ A.grading n :=
      ((opposite R A).mem_grading_iff n _).1 a.property
    have hez : flipUnderlying V (z : (flipModule V).M) ∈ V.rightModule.grading q :=
      (flipUnderlying_grading V q _).1 z.property
    have hbal := ((tensorDGFunctor V).pure M).balance p q n
      ⟨(x : (flip M).rightModule.M), x.property⟩ ⟨_, hez⟩ ⟨_, haA⟩
    rw [← leftActionTotal_eq_action_v V ⟨_, haA⟩ ⟨_, hez⟩] at hbal
    rw [flip_leftAction M a x, oppLeftActionRingHom_apply_mem M a.property x.property]
    rw [map_smul (phiLinear V M (z : (flipModule V).M)) (((n * p).negOnePow : ℤ) : R)]
    rw [phiLinear_apply_mem V M
        ((flipModule V).smul_mem q n z a z.property a.property) x.property,
      phiLinear_apply_mem V M z.property (M.smul_mem p n _ _ x.property haA),
      tensorPureFlip_apply, tensorPureFlip_apply,
      flipUnderlying_action' V a.property z.property]
    rw [map_smul (((tensorDGFunctor V).pure M).toLinearMap (x : (flip M).rightModule.M))
      (((n * q).negOnePow : ℤ) : R)]
    rw [hbal, smul_smul, smul_smul]
    congr 1
    rw [signR_balance' n p q]
    ring
  map_right z x b := by
    rw [op_smul_eq_smul_of_smul_one (flip M).rightModule
        (show b = b • (1 : (degreeZero R R).A) by simp) x,
      op_smul_eq_smul_of_smul_one (tensorObj' V M)
        (show b = b • (1 : (degreeZero R R).A) by simp) (phiLinear V M z x)]
    exact map_smul (phiLinear V M z) b x

/-! ### The isomorphism -/

/-- **The comparison `M ⊗_A V ⟶ Ṽ ⊗_{A^{opp}} M̂`**, the lift of
`DifferentialGraded.Bimodule.psiBilinear` through the universal property of Tag 09LM. -/
def psi : tensorObj' V M ⟶ tensorObj' (flip M) (flipModule V) :=
  ((tensorDGFunctor V).universal M _ (psiBilinear V M)).choose

/-- `psi V M` sends the pure tensor `x ⊗ y` to `psiLinear V M x y`. -/
theorem psi_pure (x : M.M) (y : V.rightModule.M) :
    (psi V M).toFun (((tensorDGFunctor V).pure M).toLinearMap x y) = psiLinear V M x y :=
  ((tensorDGFunctor V).universal M _ (psiBilinear V M)).choose_spec.1 x y

/-- **The comparison `Ṽ ⊗_{A^{opp}} M̂ ⟶ M ⊗_A V`**, the lift of
`DifferentialGraded.Bimodule.phiBilinear` through the universal property of Tag 09LM. -/
def phi : tensorObj' (flip M) (flipModule V) ⟶ tensorObj' V M :=
  ((tensorDGFunctor (flip M)).universal (flipModule V) _ (phiBilinear V M)).choose

/-- `phi V M` sends the pure tensor `z ⊗ x` to `phiLinear V M z x`. -/
theorem phi_pure (z : (flipModule V).M) (x : (flip M).rightModule.M) :
    (phi V M).toFun
        (((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap z x) =
      phiLinear V M z x :=
  ((tensorDGFunctor (flip M)).universal (flipModule V) _ (phiBilinear V M)).choose_spec.1 z x

/-- `phi V M` undoes `psi V M` on the pure tensor of two homogeneous elements. -/
theorem psi_phi_pure {p q : ℤ} {x : M.M} (hx : x ∈ M.grading p) {y : V.rightModule.M}
    (hy : y ∈ V.rightModule.grading q) :
    (phi V M).toFun ((psi V M).toFun (((tensorDGFunctor V).pure M).toLinearMap x y)) =
      ((tensorDGFunctor V).pure M).toLinearMap x y := by
  rw [psi_pure, psiLinear_apply_mem V M hx hy, map_smul (phi V M).toFun,
    flipTensorPure_apply, phi_pure,
    phiLinear_apply_mem V M (flipUnderlying_symm_grading V hy) hx, tensorPureFlip_apply,
    LinearEquiv.apply_symm_apply, smul_smul, show q * p = p * q from mul_comm q p,
    negOnePowR_self_mul, one_smul]

/-- `psi V M` undoes `phi V M` on the pure tensor of two homogeneous elements. -/
theorem phi_psi_pure {q p : ℤ} {z : (flipModule V).M} (hz : z ∈ (flipModule V).grading q)
    {x : M.M} (hx : x ∈ M.grading p) :
    (psi V M).toFun ((phi V M).toFun
        (((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap z x)) =
      ((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap z x := by
  rw [phi_pure, phiLinear_apply_mem V M hz hx, map_smul (psi V M).toFun,
    tensorPureFlip_apply, psi_pure,
    psiLinear_apply_mem V M hx ((flipUnderlying_grading V q z).1 hz), flipTensorPure_apply,
    LinearEquiv.symm_apply_apply, smul_smul, show p * q = q * p from mul_comm p q,
    negOnePowR_self_mul, one_smul]

/-- **The flip of the relative tensor product**: `M ⊗_A V ≅ Ṽ ⊗_{A^{opp}} M̂` as right
differential graded modules over the base ring in degree zero, carrying the pure tensor `x ⊗ y`
to `(-1)^{(deg x)(deg y)} y ⊗ x`. -/
def tensorFlipIso : tensorObj' V M ≅ tensorObj' (flip M) (flipModule V) where
  hom := psi V M
  inv := phi V M
  hom_inv_id := by
    refine tensorObj_hom_ext' V M _ (DifferentialGradedModule.Hom.id _) fun x y => ?_
    change (phi V M).toFun ((psi V M).toFun (((tensorDGFunctor V).pure M).toLinearMap x y)) =
      ((tensorDGFunctor V).pure M).toLinearMap x y
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | @homogeneous p x =>
      induction y using DirectSum.Decomposition.inductionOn V.rightModule.grading with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | @homogeneous q y => exact psi_phi_pure V M x.property y.property
  inv_hom_id := by
    refine tensorObj_hom_ext' (flip M) (flipModule V) _
      (DifferentialGradedModule.Hom.id _) fun z x => ?_
    change (psi V M).toFun ((phi V M).toFun
        (((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap z x)) =
      ((tensorDGFunctor (flip M)).pure (flipModule V)).toLinearMap z x
    induction z using DirectSum.Decomposition.inductionOn (flipModule V).grading with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
    | @homogeneous q z =>
      induction x using DirectSum.Decomposition.inductionOn (flip M).rightModule.grading with
      | zero => simp
      | add x x' hx hx' => simp only [map_add, hx, hx']
      | @homogeneous p x => exact phi_psi_pure V M z.property x.property

/-- The forward map of `tensorFlipIso V M` is `psi V M`. -/
@[simp] theorem tensorFlipIso_hom : (tensorFlipIso V M).hom = psi V M := rfl

/-- The inverse map of `tensorFlipIso V M` is `phi V M`. -/
@[simp] theorem tensorFlipIso_inv : (tensorFlipIso V M).inv = phi V M := rfl

/-- `tensorFlipIso V M` sends the pure tensor `x ⊗ y` to `psiLinear V M x y`, that is, to
`(-1)^{(deg x)(deg y)} y ⊗ x` for homogeneous `x` and `y`. -/
theorem tensorFlipIso_hom_pure (x : M.M) (y : V.rightModule.M) :
    (tensorFlipIso V M).hom.toFun (((tensorDGFunctor V).pure M).toLinearMap x y) =
      psiLinear V M x y :=
  psi_pure V M x y

/-! ### Naturality in the module -/

/-- **The flip is natural in `M`.** On the right-hand side the module `M` sits in the bimodule
slot, so the transformation it induces is the one of Tag 09S3 attached to the homomorphism of
bimodules `M̂ ⟶ M̂'`. -/
theorem psi_naturality {M₁ M₂ : DifferentialGradedModule.{u, u, u} A} (f : M₁ ⟶ M₂) :
    (tensorCompFunctor V).map f ≫ psi V M₂ =
      psi V M₁ ≫ tensorHomOfBimoduleHom (flipMap f) (flipModule V) := by
  refine tensorObj_hom_ext' V M₁ _ _ fun x y => ?_
  change (psi V M₂).toFun (((tensorCompFunctor V).map f).toFun
      (((tensorDGFunctor V).pure M₁).toLinearMap x y)) =
    (tensorHomOfBimoduleHom (flipMap f) (flipModule V)).toFun
      ((psi V M₁).toFun (((tensorDGFunctor V).pure M₁).toLinearMap x y))
  rw [tensorCompFunctor_map_pure' V f, psi_pure, psi_pure]
  induction x using DirectSum.Decomposition.inductionOn M₁.grading with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | @homogeneous p x =>
    induction y using DirectSum.Decomposition.inductionOn V.rightModule.grading with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | @homogeneous q y =>
      rw [psiLinear_apply_mem V M₂ (f.map_grading p (x : M₁.M) x.property) y.property,
        psiLinear_apply_mem V M₁ x.property y.property,
        map_smul (tensorHomOfBimoduleHom (flipMap f) (flipModule V)).toFun,
        flipTensorPure_apply, flipTensorPure_apply, tensorHomOfBimoduleHom_pure]
      rfl

/-- The isomorphism `DifferentialGraded.Bimodule.tensorFlipIso` is natural in `M`. -/
theorem tensorFlipIso_naturality {M₁ M₂ : DifferentialGradedModule.{u, u, u} A} (f : M₁ ⟶ M₂) :
    (tensorCompFunctor V).map f ≫ (tensorFlipIso V M₂).hom =
      (tensorFlipIso V M₁).hom ≫ tensorHomOfBimoduleHom (flipMap f) (flipModule V) :=
  psi_naturality V f

end DifferentialGraded.Bimodule

end
