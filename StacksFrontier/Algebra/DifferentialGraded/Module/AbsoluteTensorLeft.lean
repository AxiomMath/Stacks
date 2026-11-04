module

public import StacksFrontier.Algebra.DGA.BimoduleTensorExact
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTotalization
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorAlgebraComparison
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductInclusion

/-!
# Tensoring a bimodule with an algebra on the left

Let `R` be a commutative ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded
`R`-algebras. For a differential graded `(A, B)`-bimodule `N` the tensor product `C ⊗_R N` of the
complex underlying `C` with the complex underlying `N`, with `B` acting on the second factor, is a
right differential graded `B`-module. It computes the relative tensor product of the right
differential graded `A`-module `A ⊗_R C` — the algebra `A ⊗_R C` of Tag 065W, read over `A`
through `a ↦ a ⊗ 1` — with `N`:
`(A ⊗_R C) ⊗_A N = C ⊗_R N` as right differential graded `B`-modules.

This is the mirror of `DifferentialGraded.absBalanceIso`, which identifies `M ⊗_B (B ⊗_R C)` with
`M ⊗_R C` for a right differential graded `B`-module `M`: there the base-changed algebra is the
*bimodule* and the module is carried along, here it is the *module* and the bimodule is carried
along. That is the variance needed when the module is the one whose orthogonality to the acyclic
modules is known and the bimodule is the one that varies.

## Main definitions

* `DifferentialGradedModule.absoluteTensorLeft`: the right differential graded `B`-module
  `C ⊗_R M`, with `B` acting on the second factor and with the signed tensor differential.
* `DifferentialGraded.absLeftTwist`: multiplication by `(-1)^(deg a · deg c)` on `A ⊗_R C`,
  followed by the interchange of the two factors.
* `DifferentialGraded.absLeftUnbalance`: the bilinear map
  `(a ⊗ c, y) ↦ (-1)^(deg a · deg c) c ⊗ a y` underlying the identification, and
  `DifferentialGraded.absLeftBalanceForward`,
  `DifferentialGraded.absLeftBalanceInverse`: the two homomorphisms of differential graded
  `B`-modules it produces.

## Main results

* `DifferentialGraded.absLeftBalanceIso`: the identification
  `(A ⊗_R C) ⊗_A N = C ⊗_R N` of right differential graded `B`-modules.

## Implementation notes

*Why the module has to be built by hand.* The relative tensor product with a bimodule is
characterized by its universal property (`DifferentialGraded.Bimodule.tensorDGFunctor`) and has
no presentation, so the only way to compute `(A ⊗_R C) ⊗_A N` is to exhibit a concrete
differential graded `B`-module with the same universal property.
`DifferentialGradedModule.absoluteTensorLeft` is that module: its grading is spanned by the pure
tensors of homogeneous elements and its direct-sum decomposition is the regrouping of the
bigraded pieces `C^p ⊗_R M^q` by total degree, exactly as for
`DifferentialGradedModule.absoluteTensor`.

*Where the sign comes from.* Moving a homogeneous `a : A^i` across a homogeneous `c : C^j` in
`A ⊗_R C` in order to let it act on `N` costs the Koszul sign `(-1)^(i j)`: the right action of
`A` on `A ⊗_R C` is multiplication by `a' ⊗ 1`, which by Tag 065W carries the sign
`(-1)^(deg c · deg a')`, and `(-1)^(j k) (-1)^((i + k) j) = (-1)^(i j)` is exactly what makes the
map balanced. The sign depends on both degrees, so it is not an endomorphism of either factor; it
is read off the bigraded decomposition of `A ⊗_R C` by `DifferentialGraded.absLeftTwist`, which
also performs the interchange of the factors, and
`DifferentialGraded.absLeftTwist_tmul_of_mem` is the only place the decomposition is used.

*Two spellings of one module.* The right differential graded `A`-module underlying `A ⊗_R C` is
reached through `DifferentialGradedModule.restrictScalars`, and rewriting does not see through
that spelling. As in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorAlgebraComparison.lean`, the pure
tensors are therefore read once at the graded tensor product itself and every statement below is
given at that spelling.

*Universes.* The differential graded algebras and their modules live in a single universe `u`,
following the encoding of Tag 09JJ used throughout this chapter.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product with a bimodule, [Tag 065W](https://stacks.math.columbia.edu/tag/065W) the tensor
  product of differential graded algebras and [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
  the notion of a differential graded bimodule.
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is where the
  identification below is used.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {B : DifferentialGradedAlgebra.{u, u} R}
  (C : DifferentialGradedAlgebra.{u, u} R) (M : DifferentialGradedModule.{u, u, u} B)

/-! ### The grading and the differential -/

/-- The degree-`n` part of `C ⊗_R M` is spanned by the pure tensors whose factors have degrees
adding up to `n`. -/
def absLeftGrading (n : ℤ) : Submodule R (C.A ⊗[R] M.M) :=
  Submodule.span R {x | ∃ (p q : ℤ) (b : C.A) (a : M.M),
    b ∈ C.grading p ∧ a ∈ M.grading q ∧ p + q = n ∧ x = b ⊗ₜ[R] a}

/-- The signed tensor differential `d_C ⊗ 1 + (-1)^deg ⊗ d_M` on `C ⊗_R M`. -/
def absLeftDifferential : (C.A ⊗[R] M.M) →ₗ[R] (C.A ⊗[R] M.M) :=
  TensorProduct.map C.d LinearMap.id +
    TensorProduct.map (DifferentialGradedAlgebra.koszulSign C) M.d

/-- The differential of `C ⊗_R M` on a pure tensor `b ⊗ a` with `b` of degree `p`:
`d (b ⊗ a) = d b ⊗ a + (-1)^p b ⊗ d a`. -/
theorem absLeftDifferential_tmul (p : ℤ) (b : C.grading p) (a : M.M) :
    absLeftDifferential C M ((b : C.A) ⊗ₜ[R] a) =
      (C.d b ⊗ₜ[R] a : C.A ⊗[R] M.M) + (p.negOnePow : ℤ) • ((b : C.A) ⊗ₜ[R] M.d a) := by
  simp only [absLeftDifferential, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, DifferentialGradedAlgebra.koszulSign_apply_coe]
  simp only [← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul']

/-! ### The direct sum decomposition -/

/-- Regrouping the bigraded pieces of `C ⊗_R M` by their total degree. -/
def absLeftFiberEquiv :
    (⨁ pq : ℤ × ℤ, C.grading pq.1 ⊗[R] M.grading pq.2) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        C.grading pq.val.1 ⊗[R] M.grading pq.val.2) := by
  let e₁ :
      (⨁ k : (n : ℤ) × {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        C.grading k.2.val.1 ⊗[R] M.grading k.2.val.2) ≃ₗ[R]
        (⨁ pq : ℤ × ℤ, C.grading pq.1 ⊗[R] M.grading pq.2) :=
    DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2))
  exact e₁.symm.trans (DirectSum.sigmaLcurryEquiv R
    (δ := fun (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) ↦
      C.grading pq.val.1 ⊗[R] M.grading pq.val.2))

/-- The bigraded pieces of `C ⊗_R M` of total degree `n`. -/
abbrev absLeftComponents (n : ℤ) : Type u :=
  ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}, C.grading pq.val.1 ⊗[R] M.grading pq.val.2

/-- The decomposition of `C ⊗_R M` into bigraded pieces, regrouped by total degree. -/
def absLeftTotalEquiv :
    (C.A ⊗[R] M.M) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        C.grading pq.val.1 ⊗[R] M.grading pq.val.2) :=
  ((TensorProduct.congr (DirectSum.decomposeLinearEquiv C.grading)
    (DirectSum.decomposeLinearEquiv M.grading)).trans
    (TensorProduct.directSum R R (fun p ↦ C.grading p) (fun q ↦ M.grading q))).trans
      (absLeftFiberEquiv C M)

/-- Regrouping by total degree sends the bigraded piece of bidegree `(p, q)` to the summand of
total degree `p + q`. -/
theorem absLeftFiberEquiv_lof (p q : ℤ) (x : C.grading p ⊗[R] M.grading q) :
    absLeftFiberEquiv C M (DirectSum.lof R _ _ (p, q) x) =
      DirectSum.lof R _ _ (p + q) (DirectSum.lof R _ _ ⟨(p, q), rfl⟩ x) := by
  show DirectSum.sigmaFiberAddEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)
      (DirectSum.of (fun pq : ℤ × ℤ ↦ C.grading pq.1 ⊗[R] M.grading pq.2) (p, q) x) = _
  exact DirectSum.sigmaFiberAddEquiv_of
    (β := fun pq : ℤ × ℤ ↦ C.grading pq.1 ⊗[R] M.grading pq.2)
    (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) (p, q) x

/-- The decomposition of `C ⊗_R M` sends a pure tensor of homogeneous elements of degrees `p`
and `q` to its bigraded piece in total degree `p + q`. -/
theorem absLeftTotalEquiv_tmul (p q : ℤ) (b : C.grading p) (a : M.grading q) :
    absLeftTotalEquiv C M ((b : C.A) ⊗ₜ[R] (a : M.M)) =
      DirectSum.lof R ℤ (absLeftComponents C M) (p + q)
        (DirectSum.lof R _
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = p + q} ↦
            C.grading pq.val.1 ⊗[R] M.grading pq.val.2)
          ⟨(p, q), rfl⟩ (b ⊗ₜ[R] a)) := by
  simp only [absLeftTotalEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe]
  convert absLeftFiberEquiv_lof C M p q (b ⊗ₜ[R] a) using 1
  exact congrArg (absLeftFiberEquiv C M) (by
    simpa only [DirectSum.lof_eq_of] using
      (TensorProduct.directSum_lof_tmul_lof R R
        (M₁ := fun p ↦ C.grading p) (M₂ := fun q ↦ M.grading q) p b q a))

/-- The inclusion of the bigraded pieces of total degree `n` into `C ⊗_R M`. -/
def absLeftFiberMap (n : ℤ) : absLeftComponents C M n →ₗ[R] (C.A ⊗[R] M.M) :=
  (absLeftTotalEquiv C M).symm.toLinearMap ∘ₗ DirectSum.lof R ℤ (absLeftComponents C M) n

/-- The inclusion of the bigraded pieces of total degree `n` sends a pure tensor of homogeneous
elements to the same pure tensor in `C ⊗_R M`. -/
theorem absLeftFiberMap_lof_tmul (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (b : C.grading pq.val.1) (a : M.grading pq.val.2) :
    absLeftFiberMap C M n (DirectSum.lof R _ _ pq (b ⊗ₜ[R] a)) = ((b : C.A) ⊗ₜ[R] (a : M.M)) := by
  apply (absLeftTotalEquiv C M).injective
  obtain ⟨⟨p, q⟩, h⟩ := pq
  subst n
  simpa [absLeftFiberMap] using (absLeftTotalEquiv_tmul C M p q b a).symm

/-- The bigraded pieces of total degree `n` land in the degree-`n` part of `C ⊗_R M`. -/
theorem absLeftFiberMap_mem (n : ℤ) (x : absLeftComponents C M n) :
    absLeftFiberMap C M n x ∈ absLeftGrading C M n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using (absLeftGrading C M n).add_mem hx hy
  | of pq x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using (absLeftGrading C M n).add_mem hx hy
    | tmul b a =>
      rw [← DirectSum.lof_eq_of (R := R), absLeftFiberMap_lof_tmul]
      exact Submodule.subset_span
        ⟨pq.val.1, pq.val.2, (b : C.A), (a : M.M), b.property, a.property, pq.property, rfl⟩

/-- The degree-`n` part of `C ⊗_R M` is exactly the image of the bigraded pieces of total
degree `n`. -/
theorem absLeftFiberMap_range_eq (n : ℤ) :
    LinearMap.range (absLeftFiberMap C M n) = absLeftGrading C M n := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact absLeftFiberMap_mem C M n y
  · apply Submodule.span_le.mpr
    rintro x ⟨p, q, b, a, hb, ha, hpq, rfl⟩
    exact ⟨DirectSum.lof R _ _ (⟨(p, q), hpq⟩ : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
      (⟨b, hb⟩ ⊗ₜ[R] ⟨a, ha⟩), absLeftFiberMap_lof_tmul C M n ⟨(p, q), hpq⟩ ⟨b, hb⟩ ⟨a, ha⟩⟩

/-- The degree-`n` part of `C ⊗_R M` is the direct sum of the bigraded pieces of total
degree `n`. -/
def absLeftComponentEquiv (n : ℤ) :
    absLeftComponents C M n ≃ₗ[R] absLeftGrading C M n := by
  have hinj : Function.Injective (absLeftFiberMap C M n) := by
    intro x y h
    apply DirectSum.of_injective n
    have h' := congrArg (absLeftTotalEquiv C M) h
    simpa [absLeftFiberMap, DirectSum.lof_eq_of] using h'
  exact (LinearEquiv.ofInjective (absLeftFiberMap C M n) hinj).trans
    (LinearEquiv.ofEq _ _ (absLeftFiberMap_range_eq C M n))

/-- The identification of the bigraded pieces of total degree `n` with the degree-`n` part is
the inclusion into `C ⊗_R M`. -/
theorem absLeftComponentEquiv_coe (n : ℤ) (x : absLeftComponents C M n) :
    ((absLeftComponentEquiv C M n x : absLeftGrading C M n) : C.A ⊗[R] M.M) =
      absLeftFiberMap C M n x := rfl

/-- The grading of `C ⊗_R M` is a direct sum decomposition. -/
def absLeftGradingEquiv : (C.A ⊗[R] M.M) ≃ₗ[R] (⨁ n : ℤ, absLeftGrading C M n) :=
  (absLeftTotalEquiv C M).trans (DirectSum.congrLinearEquiv (absLeftComponentEquiv C M))

/-- The direct sum decomposition sends an element of the degree-`n` part to the summand `n`. -/
theorem absLeftGradingEquiv_coe (n : ℤ) (x : absLeftGrading C M n) :
    absLeftGradingEquiv C M (x : C.A ⊗[R] M.M) = DirectSum.lof R _ _ n x := by
  obtain ⟨y, rfl⟩ := (absLeftComponentEquiv C M n).surjective x
  suffices h : (DirectSum.congrLinearEquiv (absLeftComponentEquiv C M))
        (DirectSum.lof R ℤ (absLeftComponents C M) n y) =
      DirectSum.lof R ℤ (fun i ↦ absLeftGrading C M i) n (absLeftComponentEquiv C M n y) by
    simpa [absLeftGradingEquiv, absLeftComponentEquiv_coe, absLeftFiberMap] using h
  show (DirectSum.lmap (fun i ↦ (absLeftComponentEquiv C M i).toLinearMap))
    (DirectSum.lof R ℤ (absLeftComponents C M) n y) = _
  simp

/-- The inverse of the direct sum decomposition is the sum of the inclusions of the graded
pieces. -/
theorem absLeftGradingEquiv_symm_eq_coe :
    (absLeftGradingEquiv C M).symm.toLinearMap =
      DirectSum.coeLinearMap (absLeftGrading C M) := by
  ext n x
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply]
  rw [DirectSum.coeLinearMap_lof]
  exact (LinearEquiv.symm_apply_eq _).mpr (absLeftGradingEquiv_coe C M n x).symm

/-- The grading of `C ⊗_R M` as a `DirectSum.Decomposition`. -/
@[instance_reducible]
def absLeftDecomposition : DirectSum.Decomposition (absLeftGrading C M) := by
  apply DirectSum.Decomposition.ofLinearMap (absLeftGrading C M)
    (absLeftGradingEquiv C M).toLinearMap
  · rw [← absLeftGradingEquiv_symm_eq_coe]
    ext x
    simp
  · rw [← absLeftGradingEquiv_symm_eq_coe]
    ext x
    simp

/-! ### The differential graded module -/

/-- A pure tensor of homogeneous elements of degrees `p` and `q` has degree `p + q`. -/
theorem absLeftTmul_mem (p q : ℤ) (b : C.A) (a : M.M) (hb : b ∈ C.grading p)
    (ha : a ∈ M.grading q) :
    (b ⊗ₜ[R] a : C.A ⊗[R] M.M) ∈ absLeftGrading C M (p + q) :=
  Submodule.subset_span ⟨p, q, b, a, hb, ha, rfl, rfl⟩

/-- The differential of `C ⊗_R M` raises degrees by one. -/
theorem absLeftDifferential_mem (n : ℤ) (x : C.A ⊗[R] M.M)
    (hx : x ∈ absLeftGrading C M n) :
    absLeftDifferential C M x ∈ absLeftGrading C M (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, b, a, hb, ha, hpq, rfl⟩ := hx
    rw [show b = (⟨b, hb⟩ : C.grading p) from rfl, absLeftDifferential_tmul]
    apply Submodule.add_mem
    · convert absLeftTmul_mem C M (p + 1) q (C.d b) a (C.d_mem p b hb) ha using 1
      congr 1
      omega
    · apply zsmul_mem
      convert absLeftTmul_mem C M p (q + 1) b (M.d a) hb (M.d_mem q a ha) using 1
      congr 1
      omega
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (absLeftGrading C M (n + 1)).add_mem ihx ihy
  | smul r x hx ih => simpa using (absLeftGrading C M (n + 1)).smul_mem r ih

/-- The differential of `C ⊗_R M` squares to zero on a pure tensor whose first factor is
homogeneous. -/
theorem absLeftDifferential_sq_tmul (p : ℤ) (b : C.grading p) (a : M.M) :
    absLeftDifferential C M (absLeftDifferential C M ((b : C.A) ⊗ₜ[R] a)) = 0 := by
  have hb : C.d (b : C.A) ∈ C.grading (p + 1) := C.d_mem p b b.property
  have hC : C.d (C.d (b : C.A)) = 0 := by simpa using LinearMap.congr_fun C.d_comp_d (b : C.A)
  have hM : M.d (M.d a) = 0 := by simpa using LinearMap.congr_fun M.d_comp_d a
  rw [absLeftDifferential_tmul, map_add, map_zsmul,
    absLeftDifferential_tmul C M (p + 1) ⟨C.d b, hb⟩ a,
    absLeftDifferential_tmul C M p b (M.d a)]
  simp only [hC, hM, TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add,
    add_zero, smul_zero]
  rw [Int.negOnePow_succ]
  simpa only [Units.val_neg, neg_zsmul] using
    (neg_add_cancel ((p.negOnePow : ℤ) • ((C.d b : C.A) ⊗ₜ[R] M.d a : C.A ⊗[R] M.M)))

/-- The differential of `C ⊗_R M` squares to zero. -/
theorem absLeftDifferential_sq :
    absLeftDifferential C M ∘ₗ absLeftDifferential C M = 0 := by
  apply LinearMap.ext; intro x
  show absLeftDifferential C M (absLeftDifferential C M x) = 0
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul b a =>
    induction b using DirectSum.Decomposition.inductionOn C.grading with
    | zero => simp
    | add b b' hb hb' => simp [TensorProduct.add_tmul, map_add, hb, hb']
    | homogeneous b => exact absLeftDifferential_sq_tmul C M _ b a

/-- The right `B`-action on `C ⊗_R M`, on the second factor. -/
@[instance_reducible]
def absLeftRightModule : Module (MulOpposite B.A) (C.A ⊗[R] M.M) :=
  (TensorProduct.comm R C.A M.M).toAddEquiv.module _

attribute [local instance] absLeftRightModule

/-- The right `B`-action on `C ⊗_R M` is compatible with the `R`-module structure. -/
theorem absLeftRightScalarTower : IsScalarTower R (MulOpposite B.A) (C.A ⊗[R] M.M) :=
  (TensorProduct.comm R C.A M.M).isScalarTower _

attribute [local instance] absLeftRightScalarTower

/-- `B` acts on a pure tensor through its second factor. -/
theorem absLeft_smul_tmul (b : C.A) (x : M.M) (a : B.A) :
    MulOpposite.op a • (b ⊗ₜ[R] x) = b ⊗ₜ[R] (MulOpposite.op a • x) := by
  show (TensorProduct.comm R M.M C.A)
    (MulOpposite.op a • (TensorProduct.comm R C.A M.M) (b ⊗ₜ[R] x)) = _
  simp [TensorProduct.smul_tmul']

/-- The right action of a homogeneous element of `B` of degree `m` raises degrees by `m`. -/
theorem absLeft_smul_mem (n m : ℤ) (x : C.A ⊗[R] M.M) (a : B.A)
    (hx : x ∈ absLeftGrading C M n) (ha : a ∈ B.grading m) :
    MulOpposite.op a • x ∈ absLeftGrading C M (n + m) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, b, y, hb, hy, rfl, rfl⟩ := hz
    rw [absLeft_smul_tmul]
    simpa only [add_assoc] using absLeftTmul_mem C M p (q + m) b _ hb
      (M.smul_mem q m y a hy ha)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ ih

/-- The graded Leibniz rule for the right `B`-action on `C ⊗_R M`. -/
theorem absLeft_leibniz (n m : ℤ) (z : C.A ⊗[R] M.M) (a : B.A)
    (hz : z ∈ absLeftGrading C M n) (ha : a ∈ B.grading m) :
    absLeftDifferential C M (MulOpposite.op a • z) =
      MulOpposite.op a • absLeftDifferential C M z +
        (n.negOnePow : ℤ) • (MulOpposite.op (B.d a) • z) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, b, y, hb, hy, rfl, rfl⟩ := hz
    rw [absLeft_smul_tmul, show b = (⟨b, hb⟩ : C.grading p) from rfl,
      absLeftDifferential_tmul, absLeftDifferential_tmul, smul_add,
      smul_comm (MulOpposite.op a) (p.negOnePow : ℤ), absLeft_smul_tmul, absLeft_smul_tmul,
      absLeft_smul_tmul, M.leibniz q m y a hy ha]
    simp only [TensorProduct.tmul_add, ← Int.cast_smul_eq_zsmul R, TensorProduct.tmul_smul,
      smul_add, smul_smul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
    abel
  | zero => simp
  | add x y hx hy ihx ihy => simp only [smul_add, map_add, ihx, ihy]; abel
  | smul r x hx ih =>
    simp only [smul_comm (MulOpposite.op a) r, smul_comm (MulOpposite.op (B.d a)) r,
      map_smul, ih, smul_add, smul_comm (n.negOnePow : ℤ) r]

attribute [local instance] absLeftDecomposition

/-- **`C ⊗_R M`**: a differential graded `R`-algebra `C`, tensored over the base ring with a right
differential graded `B`-module `M`, is a right differential graded `B`-module, with `B` acting on
the second factor and with the signed tensor differential. -/
@[reducible]
def absoluteTensorLeft : DifferentialGradedModule.{u, u, u} B where
  M := C.A ⊗[R] M.M
  grading := absLeftGrading C M
  smul_mem := absLeft_smul_mem C M
  d := absLeftDifferential C M
  d_comp_d := absLeftDifferential_sq C M
  d_mem := absLeftDifferential_mem C M
  leibniz := absLeft_leibniz C M

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance] DifferentialGradedModule.absLeftRightModule
  DifferentialGradedModule.absLeftRightScalarTower
  DifferentialGradedModule.absLeftDecomposition

variable {R : Type u} [CommRing R] (A B C : DifferentialGradedAlgebra.{u, u} R)

/-! ### The Koszul twist on `A ⊗_R C` -/

/-- The decomposition of `A ⊗_R C` into its bigraded pieces `A^p ⊗_R C^q`. -/
def absLeftBidegree :
    (A.A ⊗[R] C.A) ≃ₗ[R] (⨁ pq : ℤ × ℤ, A.grading pq.1 ⊗[R] C.grading pq.2) :=
  (TensorProduct.congr (DirectSum.decomposeLinearEquiv A.grading)
    (DirectSum.decomposeLinearEquiv C.grading)).trans
    (TensorProduct.directSum R R (fun p ↦ A.grading p) (fun q ↦ C.grading q))

/-- The decomposition of `A ⊗_R C` sends a pure tensor of homogeneous elements of degrees `p`
and `q` to its bigraded piece `(p, q)`. -/
theorem absLeftBidegree_tmul (p q : ℤ) (a : A.grading p) (c : C.grading q) :
    absLeftBidegree A C ((a : A.A) ⊗ₜ[R] (c : C.A)) =
      DirectSum.lof R _ _ (p, q) (a ⊗ₜ[R] c) := by
  simp only [absLeftBidegree, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe]
  simpa only [DirectSum.lof_eq_of] using
    (TensorProduct.directSum_lof_tmul_lof R R
      (M₁ := fun p ↦ A.grading p) (M₂ := fun q ↦ C.grading q) p a q c)

/-- **The Koszul twist.** Multiplication by `(-1)^(deg a · deg c)` on `A ⊗_R C`, followed by the
interchange of the two factors. This is the sign that moving a homogeneous element of `A` across a
homogeneous element of `C` costs. -/
def absLeftTwist : (A.A ⊗[R] C.A) →ₗ[R] (C.A ⊗[R] A.A) :=
  (DirectSum.toModule R (ℤ × ℤ) (C.A ⊗[R] A.A) (fun pq ↦
    ((pq.1 * pq.2 : ℤ).negOnePow : ℤ) •
      ((TensorProduct.comm R A.A C.A).toLinearMap ∘ₗ
        TensorProduct.map (A.grading pq.1).subtype (C.grading pq.2).subtype))) ∘ₗ
    (absLeftBidegree A C).toLinearMap

/-- The Koszul twist on a pure tensor of homogeneous elements of degrees `p` and `q`:
`a ⊗ c ↦ (-1)^(p q) c ⊗ a`. -/
theorem absLeftTwist_tmul_of_mem (p q : ℤ) (a : A.grading p) (c : C.grading q) :
    absLeftTwist A C ((a : A.A) ⊗ₜ[R] (c : C.A)) =
      (((p * q).negOnePow : ℤ)) • ((c : C.A) ⊗ₜ[R] (a : A.A)) := by
  rw [absLeftTwist]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    absLeftBidegree_tmul, DirectSum.toModule_lof, LinearMap.smul_apply, TensorProduct.map_tmul,
    Submodule.coe_subtype, TensorProduct.comm_tmul]

/-! ### The unbalanced bilinear map -/

/-- The left action of `A` on a differential graded `(A, B)`-bimodule, as a bilinear map. -/
abbrev absLeftAct (N : Bimodule A B) : A.A →ₗ[R] N.rightModule.M →ₗ[R] N.rightModule.M :=
  leftActionTotal A B N.rightModule N.leftAction.1

/-- The left action of a homogeneous element of `A` on a homogeneous element of the bimodule,
read off the total action. -/
theorem absLeftAct_coe (N : Bimodule A B) {n q : ℤ} (a : A.grading n)
    (y : N.rightModule.grading q) :
    absLeftAct A B N (a : A.A) (y : N.rightModule.M) =
      ((show N.rightModule.grading (q + n) from
        (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M) := by
  rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
    totalizeCochain_apply_of_eq B N.rightModule n q (q + n) rfl
      (N.leftAction.1.action n a) y]
  rfl

/-- The total left action is right `B`-linear in the second variable, for arbitrary scalars. -/
theorem absLeftAct_op_smul (N : Bimodule A B) (a : A.A) (b : B.A) (y : N.rightModule.M) :
    absLeftAct A B N a (MulOpposite.op b • y) =
      MulOpposite.op b • absLeftAct A B N a y := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha', smul_add]
  | @homogeneous n a =>
    induction b using DirectSum.Decomposition.inductionOn B.grading with
    | zero => simp
    | add b b' hb hb' =>
      simp only [MulOpposite.op_add, add_smul, map_add, hb, hb']
    | @homogeneous q b =>
      exact leftActionTotal_commutes A B N.rightModule N.leftAction.1
        (fun n a => N.leftAction.2 n a) a b y

/-- `(a ⊗ c, y) ↦ (-1)^(deg a · deg c) c ⊗ a y`, as a linear map out of the tensor product. -/
def absLeftUnbalanceLinear (N : Bimodule A B) :
    ((A.A ⊗[R] C.A) ⊗[R] N.rightModule.M) →ₗ[R] (C.A ⊗[R] N.rightModule.M) :=
  TensorProduct.map LinearMap.id (TensorProduct.lift (absLeftAct A B N)) ∘ₗ
    (TensorProduct.assoc R C.A A.A N.rightModule.M).toLinearMap ∘ₗ
    TensorProduct.map (absLeftTwist A C) LinearMap.id

/-- **`(a ⊗ c, y) ↦ (-1)^(deg a · deg c) c ⊗ a y`**, the bilinear map that undoes the balancing
over `A`. -/
def absLeftUnbalance (N : Bimodule A B) :
    (A.grading ᵍ⊗[R] C.grading) →ₗ[R] N.rightModule.M →ₗ[R] (C.A ⊗[R] N.rightModule.M) :=
  (TensorProduct.curry (absLeftUnbalanceLinear A B C N)).comp
    (GradedTensorProduct.of R A.grading C.grading).symm.toLinearMap

/-- The unbalanced map on a pure tensor of homogeneous elements of degrees `p` and `q`:
`(a ⊗ c, y) ↦ (-1)^(p q) c ⊗ a y`. -/
theorem absLeftUnbalance_tmul_of_mem (N : Bimodule A B) (p q : ℤ) (a : A.grading p)
    (c : C.grading q) (y : N.rightModule.M) :
    absLeftUnbalance A B C N
        (((a : A.A) ᵍ⊗ₜ[R] (c : C.A) : A.grading ᵍ⊗[R] C.grading)) y =
      (((p * q).negOnePow : ℤ)) • ((c : C.A) ⊗ₜ[R] absLeftAct A B N (a : A.A) y) := by
  have hof : (GradedTensorProduct.of R A.grading C.grading).symm
      (((a : A.A) ᵍ⊗ₜ[R] (c : C.A) : A.grading ᵍ⊗[R] C.grading)) =
      ((a : A.A) ⊗ₜ[R] (c : C.A)) := rfl
  rw [absLeftUnbalance]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hof,
    TensorProduct.curry_apply, absLeftUnbalanceLinear, TensorProduct.map_tmul,
    LinearMap.id_apply, absLeftTwist_tmul_of_mem]
  simp only [← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul', map_smul,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lift.tmul]

/-- The unbalanced map on a pure tensor of homogeneous elements of degrees `p` and `q`, with the
elements given together with their membership proofs. -/
theorem absLeftUnbalance_tmul_mem (N : Bimodule A B) (p q : ℤ) (a : A.A) (ha : a ∈ A.grading p)
    (c : C.A) (hc : c ∈ C.grading q) (y : N.rightModule.M) :
    absLeftUnbalance A B C N ((a ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) y =
      (((p * q).negOnePow : ℤ)) • (c ⊗ₜ[R] absLeftAct A B N a y) :=
  absLeftUnbalance_tmul_of_mem A B C N p q ⟨a, ha⟩ ⟨c, hc⟩ y

/-- The left action of a product of homogeneous elements is the composite of the actions. -/
theorem absLeftAct_mul (N : Bimodule A B) {n m : ℤ} (a : A.A) (ha : a ∈ A.grading n) (b : A.A)
    (hb : b ∈ A.grading m) (y : N.rightModule.M) :
    absLeftAct A B N (a * b) y = absLeftAct A B N a (absLeftAct A B N b y) := by
  have h := leftActionTotal_mul A B N.rightModule N.leftAction.1 ⟨a, ha⟩ ⟨b, hb⟩
  rw [← leftActionTotal_apply A B N.rightModule N.leftAction.1 n ⟨a, ha⟩,
    ← leftActionTotal_apply A B N.rightModule N.leftAction.1 m ⟨b, hb⟩] at h
  exact LinearMap.congr_fun h y

/-- Induction on `A ⊗_R C`: a statement closed under sums and scalars that holds on the pure
tensors of homogeneous elements holds everywhere. -/
private theorem absLeft_tensor_induction {motive : (A.grading ᵍ⊗[R] C.grading) → Prop}
    (h0 : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (r : R) x, motive x → motive (r • x))
    (hgen : ∀ (p q : ℤ) (a : A.A) (b : C.A), a ∈ A.grading p → b ∈ C.grading q →
      motive ((a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] C.grading)))
    (x : A.grading ᵍ⊗[R] C.grading) : motive x := by
  have := totalDecomposition A C
  induction x using DirectSum.Decomposition.inductionOn (tensorProductGrading A C) with
  | zero => exact h0
  | add z w hz hw => exact hadd z w hz hw
  | @homogeneous p x =>
    exact tensorProductGrading_induction A C p h0 hadd hsmul
      (fun p q a b ha hb _ => hgen p q a b ha hb) x.1 x.2

/-- The product of `a' ⊗ c` and `a ⊗ 1` for homogeneous `c` and `a`, with the Koszul sign. -/
private theorem absLeft_tmul_mul_tmul_one (j n : ℤ) (a' a : A.A) (c : C.A) (hc : c ∈ C.grading j)
    (ha : a ∈ A.grading n) :
    ((a' ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) *
        ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading) =
      (((j * n).negOnePow : ℤ)) • (((a' * a) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) := by
  have h := GradedTensorProduct.tmul_coe_mul_coe_tmul A.grading C.grading a'
    (⟨c, hc⟩ : C.grading j) (⟨a, ha⟩ : A.grading n) (1 : C.A)
  rwa [mul_one, ← Int.negOnePow_def, Units.smul_def] at h

/-! ### The four properties of the unbalanced map -/

/-- The unbalanced map adds degrees. -/
theorem absLeftUnbalance_mem (N : Bimodule A B) (p q : ℤ) (x : A.grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading A C p) (y : N.rightModule.M)
    (hy : y ∈ N.rightModule.grading q) :
    absLeftUnbalance A B C N x y ∈ absLeftGrading C N.rightModule (p + q) := by
  refine tensorProductGrading_induction A C p (motive := fun z =>
      absLeftUnbalance A B C N z y ∈ absLeftGrading C N.rightModule (p + q))
    (by simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _)
    (fun z w hz hw => by
      simp only [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hz hw)
    (fun r z hz => by
      simp only [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ r hz) ?_ x hx
  intro i j a c ha hc hij
  rw [absLeftUnbalance_tmul_mem A B C N i j a ha c hc y]
  refine zsmul_mem ?_ _
  have h := absLeftTmul_mem C N.rightModule j (q + i) c (absLeftAct A B N a y) hc
    (leftActionTotal_apply_mem A B N.rightModule N.leftAction.1 ⟨a, ha⟩ ⟨y, hy⟩)
  rwa [show j + (q + i) = p + q by omega] at h

/-- The unbalanced map satisfies the graded Leibniz rule, on a pure tensor of homogeneous
elements. -/
theorem absLeftUnbalance_d_tmul (N : Bimodule A B) (i j : ℤ) (a : A.A) (ha : a ∈ A.grading i)
    (c : C.A) (hc : c ∈ C.grading j) (y : N.rightModule.M) :
    absLeftDifferential C N.rightModule
        (absLeftUnbalance A B C N ((a ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) y) =
      absLeftUnbalance A B C N
          (tensorProductDifferential A C ((a ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading))) y +
        (((i + j).negOnePow : ℤ)) • absLeftUnbalance A B C N
          ((a ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) (N.rightModule.d y) := by
  have hda : A.d a ∈ A.grading (i + 1) := A.d_mem i a ha
  have hdc : C.d c ∈ C.grading (j + 1) := C.d_mem j c hc
  have hleib : N.rightModule.d (absLeftAct A B N a y) =
      absLeftAct A B N (A.d a) y + (i.negOnePow : ℤ) • absLeftAct A B N a (N.rightModule.d y) :=
    leftActionTotal_leibniz A B N.rightModule N.leftAction.1 ⟨a, ha⟩ y
  rw [absLeftUnbalance_tmul_mem A B C N i j a ha c hc y,
    tensorProductDifferential_tmul_of_mem i a ha c]
  simp only [← Int.cast_smul_eq_zsmul R, map_smul, LinearMap.smul_apply, map_add,
    LinearMap.add_apply]
  rw [absLeftDifferential_tmul C N.rightModule j ⟨c, hc⟩ (absLeftAct A B N a y),
    absLeftUnbalance_tmul_mem A B C N (i + 1) j (A.d a) hda c hc y,
    absLeftUnbalance_tmul_mem A B C N i (j + 1) a ha (C.d c) hdc y,
    absLeftUnbalance_tmul_mem A B C N i j a ha c hc (N.rightModule.d y), hleib]
  have e1 : (((i + 1) * j).negOnePow : ℤ) = ((i * j).negOnePow : ℤ) * (j.negOnePow : ℤ) := by
    rw [show (i + 1) * j = i * j + j by ring, Int.negOnePow_add, Units.val_mul]
  have e2 : ((i.negOnePow : ℤ)) * ((i * (j + 1)).negOnePow : ℤ) = ((i * j).negOnePow : ℤ) := by
    rw [show i * (j + 1) = i * j + i by ring, Int.negOnePow_add, Units.val_mul, ← mul_assoc,
      mul_comm ((i.negOnePow : ℤ)) ((i * j).negOnePow : ℤ), mul_assoc, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, mul_one]
  have e3 : (((i + j).negOnePow : ℤ)) = (i.negOnePow : ℤ) * (j.negOnePow : ℤ) := by
    rw [Int.negOnePow_add, Units.val_mul]
  simp only [← Int.cast_smul_eq_zsmul R, TensorProduct.tmul_add, TensorProduct.tmul_smul,
    smul_add, smul_smul, e1, e3, ← Int.cast_mul]
  rw [e2]
  push_cast
  module

/-- The unbalanced map satisfies the graded Leibniz rule. -/
theorem absLeftUnbalance_d (N : Bimodule A B) (p : ℤ) (x : A.grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading A C p) (y : N.rightModule.M) :
    absLeftDifferential C N.rightModule (absLeftUnbalance A B C N x y) =
      absLeftUnbalance A B C N (tensorProductDifferential A C x) y +
        (p.negOnePow : ℤ) • absLeftUnbalance A B C N x (N.rightModule.d y) := by
  refine tensorProductGrading_induction A C p (motive := fun z =>
      absLeftDifferential C N.rightModule (absLeftUnbalance A B C N z y) =
        absLeftUnbalance A B C N (tensorProductDifferential A C z) y +
          (p.negOnePow : ℤ) • absLeftUnbalance A B C N z (N.rightModule.d y))
    (by simp) ?_ ?_ ?_ x hx
  · intro z w hz hw
    simp only [map_add, LinearMap.add_apply, hz, hw, smul_add]
    abel
  · intro r z hz
    simp only [map_smul, LinearMap.smul_apply, hz, smul_add, smul_comm (p.negOnePow : ℤ) r]
  · intro i j a c ha hc hij
    subst hij
    exact absLeftUnbalance_d_tmul A B C N i j a ha c hc y

/-- The unbalanced map is balanced over `A`, on a pure tensor of homogeneous elements. -/
theorem absLeftUnbalance_balance_tmul (N : Bimodule A B) (i j n : ℤ) (a' : A.A)
    (ha' : a' ∈ A.grading i) (c : C.A) (hc : c ∈ C.grading j) (a : A.A) (ha : a ∈ A.grading n)
    (y : N.rightModule.M) :
    absLeftUnbalance A B C N
        (((a' ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) *
          ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading)) y =
      absLeftUnbalance A B C N ((a' ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading))
        (absLeftAct A B N a y) := by
  have hmul : a' * a ∈ A.grading (i + n) := SetLike.mul_mem_graded ha' ha
  rw [absLeft_tmul_mul_tmul_one A C j n a' a c hc ha]
  simp only [← Int.cast_smul_eq_zsmul R, map_smul, LinearMap.smul_apply]
  rw [absLeftUnbalance_tmul_mem A B C N (i + n) j (a' * a) hmul c hc y,
    absLeftUnbalance_tmul_mem A B C N i j a' ha' c hc (absLeftAct A B N a y),
    absLeftAct_mul A B N a' ha' a ha y]
  have e : (((j * n : ℤ).negOnePow : ℤ)) * (((i + n) * j).negOnePow : ℤ) =
      ((i * j).negOnePow : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add,
      show j * n + (i + n) * j = i * j + 2 * (n * j) by ring, Int.negOnePow_add,
      Int.negOnePow_two_mul, mul_one]
  simp only [← Int.cast_smul_eq_zsmul R, smul_smul, ← Int.cast_mul]
  rw [e]

/-- The unbalanced map is balanced over `A`: moving a homogeneous `a` from the right action on
`A ⊗_R C` to the left action on the bimodule does not change it. -/
theorem absLeftUnbalance_balance (N : Bimodule A B) (p n : ℤ) (x : A.grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading A C p) (a : A.A) (ha : a ∈ A.grading n)
    (y : N.rightModule.M) :
    absLeftUnbalance A B C N
        (x * ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading)) y =
      absLeftUnbalance A B C N x (absLeftAct A B N a y) := by
  refine tensorProductGrading_induction A C p (motive := fun z =>
      absLeftUnbalance A B C N
          (z * ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading)) y =
        absLeftUnbalance A B C N z (absLeftAct A B N a y))
    (by simp) ?_ ?_ ?_ x hx
  · intro z w hz hw
    simp only [add_mul, map_add, LinearMap.add_apply, hz, hw]
  · intro r z hz
    simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply, hz]
  · intro i j a' c ha' hc _
    exact absLeftUnbalance_balance_tmul A B C N i j n a' ha' c hc a ha y

/-- The unbalanced map is right `B`-linear in the second variable. -/
theorem absLeftUnbalance_op_smul (N : Bimodule A B) (x : A.grading ᵍ⊗[R] C.grading)
    (y : N.rightModule.M) (b : B.A) :
    absLeftUnbalance A B C N x (MulOpposite.op b • y) =
      MulOpposite.op b • absLeftUnbalance A B C N x y := by
  refine absLeft_tensor_induction A C (motive := fun z =>
      absLeftUnbalance A B C N z (MulOpposite.op b • y) =
        MulOpposite.op b • absLeftUnbalance A B C N z y)
    (by simp) (fun z w hz hw => by simp only [map_add, LinearMap.add_apply, hz, hw, smul_add])
    (fun r z hz => by
      simp only [map_smul, LinearMap.smul_apply, hz, smul_comm (MulOpposite.op b) r])
    ?_ x
  intro i j a c ha hc
  rw [absLeftUnbalance_tmul_mem A B C N i j a ha c hc (MulOpposite.op b • y),
    absLeftUnbalance_tmul_mem A B C N i j a ha c hc y, absLeftAct_op_smul,
    ← absLeft_smul_tmul, smul_comm]

/-! ### The identification of the relative with the absolute tensor product -/

/-- `A ⊗_R C` of Tag 065W, read as a right differential graded `A`-module through `a ↦ a ⊗ 1`. -/
abbrev absLeftSource : DifferentialGradedModule.{u, u, u} A :=
  restrictScalars (tensorInclLeft A C) (regularModule (tensorProduct A C))

/-- The right `A`-action on `A ⊗_R C` is right multiplication by `a ⊗ 1`. -/
theorem absLeftSource_op_smul (x : (absLeftSource A C).M) (a : A.A) :
    MulOpposite.op a • x =
      (show A.grading ᵍ⊗[R] C.grading from x) *
        ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading) := rfl

/-- The identification `(A ⊗_R C) ⊗_A N = C ⊗_R N`, as a balanced bilinear map:
`(a ⊗ c, y) ↦ (-1)^(deg a · deg c) c ⊗ a y`. -/
def absLeftUnbalanceBalanced (N : Bimodule A B) :
    Bimodule.BalancedBilinearMap (absLeftSource A C) N (absoluteTensorLeft C N.rightModule) where
  toLinearMap := absLeftUnbalance A B C N
  map_grading p q x y := absLeftUnbalance_mem A B C N p q x.1 x.2 y.1 y.2
  map_d p x y := absLeftUnbalance_d A B C N p x.1 x.2 y
  balance p q n x y a := by
    rw [absLeftSource_op_smul, ← absLeftAct_coe]
    exact absLeftUnbalance_balance A B C N p n x.1 x.2 a.1 a.2 y.1
  map_right x y b := absLeftUnbalance_op_smul A B C N x y b

/-- The relative tensor product `(A ⊗_R C) ⊗_A N`, as a right differential graded `B`-module. -/
abbrev absLeftRelative (N : Bimodule A B) : DifferentialGradedModule.{u, u, u} B :=
  Bimodule.tensorObj N (absLeftSource A C)

/-- The universal pure tensors into `(A ⊗_R C) ⊗_A N`. -/
abbrev absLeftPure (N : Bimodule A B) :
    Bimodule.BalancedBilinearMap (absLeftSource A C) N (absLeftRelative A B C N) :=
  Bimodule.tensorPure N (absLeftSource A C)

/-- The universal pure tensors `x ⊗ y`, with the first argument read in the graded tensor product
`A ⊗_R C` itself rather than through the restriction of scalars. -/
def absLeftPureBilinear (N : Bimodule A B) :
    (A.grading ᵍ⊗[R] C.grading) →ₗ[R] N.rightModule.M →ₗ[R] (absLeftRelative A B C N).M :=
  (absLeftPure A B C N).toLinearMap

/-- The pure tensors add degrees. -/
theorem absLeftPureBilinear_mem (N : Bimodule A B) (p q : ℤ)
    (x : A.grading ᵍ⊗[R] C.grading) (hx : x ∈ tensorProductGrading A C p)
    (y : N.rightModule.M) (hy : y ∈ N.rightModule.grading q) :
    absLeftPureBilinear A B C N x y ∈ (absLeftRelative A B C N).grading (p + q) :=
  (absLeftPure A B C N).map_grading p q ⟨x, hx⟩ ⟨y, hy⟩

/-- The pure tensors satisfy the graded Leibniz rule. -/
theorem absLeftPureBilinear_d (N : Bimodule A B) (p : ℤ)
    (x : A.grading ᵍ⊗[R] C.grading) (hx : x ∈ tensorProductGrading A C p)
    (y : N.rightModule.M) :
    (absLeftRelative A B C N).d (absLeftPureBilinear A B C N x y) =
      absLeftPureBilinear A B C N (tensorProductDifferential A C x) y +
        (p.negOnePow : ℤ) • absLeftPureBilinear A B C N x (N.rightModule.d y) :=
  (absLeftPure A B C N).map_d p ⟨x, hx⟩ y

/-- The pure tensors are right `B`-linear in the second variable. -/
theorem absLeftPureBilinear_op_smul (N : Bimodule A B) (x : A.grading ᵍ⊗[R] C.grading)
    (y : N.rightModule.M) (b : B.A) :
    absLeftPureBilinear A B C N x (MulOpposite.op b • y) =
      MulOpposite.op b • absLeftPureBilinear A B C N x y :=
  (absLeftPure A B C N).map_right x y b

/-- The pure tensors are balanced over `A`, for homogeneous arguments. -/
theorem absLeftPureBilinear_balance_of_mem (N : Bimodule A B) (p q n : ℤ)
    (x : A.grading ᵍ⊗[R] C.grading) (hx : x ∈ tensorProductGrading A C p)
    (a : A.A) (ha : a ∈ A.grading n) (y : N.rightModule.M)
    (hy : y ∈ N.rightModule.grading q) :
    absLeftPureBilinear A B C N
        (x * ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading)) y =
      absLeftPureBilinear A B C N x (absLeftAct A B N a y) := by
  have h := (absLeftPure A B C N).balance p q n ⟨x, hx⟩ ⟨y, hy⟩ ⟨a, ha⟩
  rw [absLeftSource_op_smul, ← absLeftAct_coe] at h
  exact h

/-- The pure tensors are balanced over `A`: moving a homogeneous `a` from the right action on
`A ⊗_R C` to the left action on the bimodule does not change them. -/
theorem absLeftPureBilinear_balance (N : Bimodule A B) (n : ℤ)
    (x : A.grading ᵍ⊗[R] C.grading) (a : A.A) (ha : a ∈ A.grading n) (y : N.rightModule.M) :
    absLeftPureBilinear A B C N
        (x * ((a ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading)) y =
      absLeftPureBilinear A B C N x (absLeftAct A B N a y) := by
  have := totalDecomposition A C
  induction x using DirectSum.Decomposition.inductionOn (tensorProductGrading A C) with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, LinearMap.add_apply, hx, hx']
  | @homogeneous p x =>
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | @homogeneous q y =>
      exact absLeftPureBilinear_balance_of_mem A B C N p q n x.1 x.2 a ha y.1 y.2

/-- On `1 ⊗ c` the unbalanced map is the plain pure tensor. -/
theorem absLeftUnbalance_one_tmul (N : Bimodule A B) (c : C.A) (y : N.rightModule.M) :
    absLeftUnbalance A B C N (((1 : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) y =
      (c ⊗ₜ[R] y : C.A ⊗[R] N.rightModule.M) := by
  induction c using DirectSum.Decomposition.inductionOn C.grading with
  | zero =>
    have h : (((1 : A.A) ᵍ⊗ₜ[R] (0 : C.A)) : A.grading ᵍ⊗[R] C.grading) = 0 := by
      show (GradedTensorProduct.of R A.grading C.grading) ((1 : A.A) ⊗ₜ[R] (0 : C.A)) = 0
      rw [TensorProduct.tmul_zero, map_zero]
    rw [h]
    simp
  | add c c' hc hc' =>
    have h : (((1 : A.A) ᵍ⊗ₜ[R] (c + c')) : A.grading ᵍ⊗[R] C.grading) =
        (((1 : A.A) ᵍ⊗ₜ[R] c) : A.grading ᵍ⊗[R] C.grading) +
          (((1 : A.A) ᵍ⊗ₜ[R] c') : A.grading ᵍ⊗[R] C.grading) := by
      show (GradedTensorProduct.of R A.grading C.grading) ((1 : A.A) ⊗ₜ[R] (c + c')) = _
      rw [TensorProduct.tmul_add, map_add]
    rw [h, map_add, LinearMap.add_apply, hc, hc', TensorProduct.add_tmul]
  | @homogeneous j c =>
    rw [absLeftUnbalance_tmul_mem A B C N 0 j 1 (SetLike.one_mem_graded A.grading) (c : C.A)
      c.property y]
    simp only [zero_mul, Int.negOnePow_zero, Units.val_one, one_smul]
    rw [show absLeftAct A B N (1 : A.A) y = y from
      LinearMap.congr_fun (leftActionTotal_one A B N.rightModule N.leftAction.1) y]

/-- The identification, as a homomorphism out of the relative tensor product: the unique
homomorphism of differential graded `B`-modules sending `(a ⊗ c) ⊗ y` to
`(-1)^(deg a · deg c) c ⊗ a y`. -/
def absLeftBalanceForward (N : Bimodule A B) :
    absLeftRelative A B C N ⟶ absoluteTensorLeft C N.rightModule :=
  ((Bimodule.tensorDGFunctor N).universal (absLeftSource A C)
    (absoluteTensorLeft C N.rightModule) (absLeftUnbalanceBalanced A B C N)).choose

/-- The forward identification sends the image `(a ⊗ c) ⊗ y` of the pure tensors to its value
under the unbalanced map. -/
theorem absLeftBalanceForward_pure (N : Bimodule A B) (x : A.grading ᵍ⊗[R] C.grading)
    (y : N.rightModule.M) :
    (absLeftBalanceForward A B C N).toFun (absLeftPureBilinear A B C N x y) =
      absLeftUnbalance A B C N x y :=
  ((Bimodule.tensorDGFunctor N).universal (absLeftSource A C)
    (absoluteTensorLeft C N.rightModule) (absLeftUnbalanceBalanced A B C N)).choose_spec.1 x y

/-- `c ⊗ y ↦ (1 ⊗ c) ⊗ y`, the inverse of the identification, as a linear map. -/
def absLeftBalanceInverseLinear (N : Bimodule A B) :
    (C.A ⊗[R] N.rightModule.M) →ₗ[R] (absLeftRelative A B C N).M :=
  TensorProduct.lift ((absLeftPureBilinear A B C N).comp
    (GradedTensorProduct.includeRight A.grading C.grading).toLinearMap)

/-- The inverse of the identification on a pure tensor: `c ⊗ y ↦ (1 ⊗ c) ⊗ y`. -/
theorem absLeftBalanceInverseLinear_tmul (N : Bimodule A B) (c : C.A) (y : N.rightModule.M) :
    absLeftBalanceInverseLinear A B C N (c ⊗ₜ[R] y) =
      absLeftPureBilinear A B C N
        (((1 : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) y := rfl

/-- The inverse of the identification, as a homomorphism of differential graded `B`-modules. -/
def absLeftBalanceInverse (N : Bimodule A B) :
    absoluteTensorLeft C N.rightModule ⟶ absLeftRelative A B C N where
  toFun := absLeftBalanceInverseLinear A B C N
  map_smul z b := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul c y =>
      rw [absLeft_smul_tmul, absLeftBalanceInverseLinear_tmul,
        absLeftBalanceInverseLinear_tmul, absLeftPureBilinear_op_smul]
  map_grading n z hz := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, c, y, hc, hy, rfl, rfl⟩ := hz
      rw [absLeftBalanceInverseLinear_tmul]
      exact absLeftPureBilinear_mem A B C N p q _ (one_tmul_mem_grading A C p c hc) y hy
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  map_d := by
    apply LinearMap.ext; intro z
    change absLeftBalanceInverseLinear A B C N (absLeftDifferential C N.rightModule z) =
      (absLeftRelative A B C N).d (absLeftBalanceInverseLinear A B C N z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c y =>
      induction c using DirectSum.Decomposition.inductionOn C.grading with
      | zero => simp
      | add c c' hc hc' => simp only [TensorProduct.add_tmul, map_add, hc, hc']
      | @homogeneous p c =>
        rw [absLeftDifferential_tmul, map_add, map_zsmul,
          absLeftBalanceInverseLinear_tmul, absLeftBalanceInverseLinear_tmul,
          absLeftBalanceInverseLinear_tmul,
          absLeftPureBilinear_d A B C N p _ (one_tmul_mem_grading A C p (c : C.A) c.property) y,
          tensorProductDifferential_one_tmul A C (c : C.A)]

/-- The inverse undoes the identification on every pure tensor. -/
theorem absLeftBalanceInverse_unbalance (N : Bimodule A B) (x : A.grading ᵍ⊗[R] C.grading)
    (y : N.rightModule.M) :
    absLeftBalanceInverseLinear A B C N (absLeftUnbalance A B C N x y) =
      absLeftPureBilinear A B C N x y := by
  refine absLeft_tensor_induction A C (motive := fun z =>
      absLeftBalanceInverseLinear A B C N (absLeftUnbalance A B C N z y) =
        absLeftPureBilinear A B C N z y)
    (by simp) (fun z w hz hw => by simp only [map_add, LinearMap.add_apply, hz, hw])
    (fun r z hz => by simp only [map_smul, LinearMap.smul_apply, hz]) ?_ x
  intro i j a c ha hc
  have hbal := absLeftPureBilinear_balance A B C N i
    (((1 : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) a ha y
  rw [absLeft_tmul_mul_tmul_one A C j i 1 a c hc ha, one_mul] at hbal
  rw [absLeftUnbalance_tmul_mem A B C N i j a ha c hc y,
    ← Int.cast_smul_eq_zsmul R, map_smul, absLeftBalanceInverseLinear_tmul, ← hbal]
  simp only [← Int.cast_smul_eq_zsmul R, map_smul, LinearMap.smul_apply, smul_smul,
    ← Int.cast_mul]
  rw [show (((i * j).negOnePow : ℤ)) * (((j * i).negOnePow : ℤ)) = 1 by
    rw [← Units.val_mul, ← Int.negOnePow_add, show i * j + j * i = 2 * (i * j) by ring,
      Int.negOnePow_two_mul, Units.val_one]]
  simp

/-- **The identification `(A ⊗_R C) ⊗_A N = C ⊗_R N`.** The relative tensor product of the right
differential graded `A`-module `A ⊗_R C` with a differential graded `(A, B)`-bimodule `N` is the
absolute tensor product `C ⊗_R N`, as right differential graded `B`-modules. -/
def absLeftBalanceIso (N : Bimodule A B) :
    absLeftRelative A B C N ≅ absoluteTensorLeft C N.rightModule where
  hom := absLeftBalanceForward A B C N
  inv := absLeftBalanceInverse A B C N
  hom_inv_id := by
    refine Bimodule.tensorObj_hom_ext N (absLeftSource A C) _ _ fun x y => ?_
    exact (congrArg (absLeftBalanceInverse A B C N).toFun
      (absLeftBalanceForward_pure A B C N x y)).trans
      (absLeftBalanceInverse_unbalance A B C N x y)
  inv_hom_id := by
    apply DifferentialGradedModule.Hom.ext
    apply TensorProduct.ext'
    intro c y
    change (absLeftBalanceForward A B C N).toFun
      (absLeftBalanceInverseLinear A B C N (c ⊗ₜ[R] y)) = c ⊗ₜ[R] y
    rw [absLeftBalanceInverseLinear_tmul, absLeftBalanceForward_pure,
      absLeftUnbalance_one_tmul]

end DifferentialGraded

end
