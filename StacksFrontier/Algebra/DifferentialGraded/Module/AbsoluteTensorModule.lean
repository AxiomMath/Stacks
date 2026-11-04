module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorLeft
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeTensorKFlat

/-!
# Tensoring a differential graded module with a differential graded module

Let `R` be a commutative ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras, let
`L` be a right differential graded `A`-module and let `N` be a right differential graded
`B`-module. The tensor product `L ⊗_R N` of the complex underlying `L` with the complex
underlying `N`, with `B` acting on the second factor, is a right differential graded `B`-module.

This is the absolute tensor product with *no algebra on either side*: the left factor enters only
through its grading and its differential, so the construction applies to an arbitrary differential
graded module in that slot. `DifferentialGradedModule.absoluteTensorLeft` is the special case in
which the left factor is the regular module of a differential graded algebra, and
`DifferentialGradedModule.absoluteTensor` is the mirror case with the algebra on the right.

## Main definitions

* `DifferentialGradedModule.absoluteTensorModule`: the right differential graded `B`-module
  `L ⊗_R N`, with `B` acting on the second factor and with the signed tensor differential.

## Main results

* `DifferentialGradedModule.absModTmul_mem`: a pure tensor of homogeneous elements is homogeneous
  of the sum of the degrees.
* `DifferentialGradedModule.absModDifferential_tmul`: the differential on a pure tensor whose left
  factor is homogeneous.
* `DifferentialGradedModule.absMod_smul_tmul`: the right `B`-action on a pure tensor.

## Implementation notes

*Why the module has to be built by hand.* The grading of `L ⊗_R N` is spanned by the pure tensors
of homogeneous elements, and the direct-sum decomposition it has to carry is the regrouping of the
bigraded pieces `L^p ⊗_R N^q` by total degree. That regrouping is `absModTotalEquiv`, assembled
from `TensorProduct.directSum` and `DirectSum.sigmaLcurryEquiv` exactly as for
`DifferentialGradedModule.absoluteTensorLeft`; the `leibniz`, `smul_mem` and `d_mem` fields are
then proved by induction over the spanning set.

*Universes.* The differential graded algebras and their modules live in a single universe `u`,
following the encoding of Tag 09JJ used throughout this chapter.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W) is the tensor product of
  differential graded algebras, whose signed differential this one copies, and
  [Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) is the notion of a differential graded
  module.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedModule

section KoszulSign

variable {R : Type u} [CommRing R]

end KoszulSign

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
  (L : DifferentialGradedModule.{u, u, u} A) (N : DifferentialGradedModule.{u, u, u} B)

/-! ### The grading and the differential -/

/-- The degree-`n` part of `L ⊗_R N` is spanned by the pure tensors whose factors have degrees
adding up to `n`. -/
def absModGrading (n : ℤ) : Submodule R (L.M ⊗[R] N.M) :=
  Submodule.span R {x | ∃ (p q : ℤ) (b : L.M) (a : N.M),
    b ∈ L.grading p ∧ a ∈ N.grading q ∧ p + q = n ∧ x = b ⊗ₜ[R] a}

/-- The signed tensor differential `d_L ⊗ 1 + (-1)^deg ⊗ d_N` on `L ⊗_R N`. -/
def absModDifferential : (L.M ⊗[R] N.M) →ₗ[R] (L.M ⊗[R] N.M) :=
  TensorProduct.map L.d LinearMap.id + TensorProduct.map (absKoszulSign L) N.d

/-- On a pure tensor `b ⊗ a` with `b` of degree `p`, the differential is
`d b ⊗ a + (-1)^p • (b ⊗ d a)`. -/
theorem absModDifferential_tmul (p : ℤ) (b : L.grading p) (a : N.M) :
    absModDifferential L N ((b : L.M) ⊗ₜ[R] a) =
      (L.d b ⊗ₜ[R] a : L.M ⊗[R] N.M) + (p.negOnePow : ℤ) • ((b : L.M) ⊗ₜ[R] N.d a) := by
  simp only [absModDifferential, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, absKoszulSign_apply_coe]
  simp only [← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul']

/-! ### The direct sum decomposition -/

/-- Regrouping the bigraded pieces of `L ⊗_R N` by their total degree. -/
def absModFiberEquiv :
    (⨁ pq : ℤ × ℤ, L.grading pq.1 ⊗[R] N.grading pq.2) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        L.grading pq.val.1 ⊗[R] N.grading pq.val.2) := by
  let e₁ :
      (⨁ k : (n : ℤ) × {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        L.grading k.2.val.1 ⊗[R] N.grading k.2.val.2) ≃ₗ[R]
        (⨁ pq : ℤ × ℤ, L.grading pq.1 ⊗[R] N.grading pq.2) :=
    DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2))
  exact e₁.symm.trans (DirectSum.sigmaLcurryEquiv R
    (δ := fun (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) ↦
      L.grading pq.val.1 ⊗[R] N.grading pq.val.2))

/-- The bigraded pieces of `L ⊗_R N` of total degree `n`. -/
abbrev absModComponents (n : ℤ) : Type u :=
  ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}, L.grading pq.val.1 ⊗[R] N.grading pq.val.2

/-- The decomposition of `L ⊗_R N` into bigraded pieces, regrouped by total degree. -/
def absModTotalEquiv :
    (L.M ⊗[R] N.M) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        L.grading pq.val.1 ⊗[R] N.grading pq.val.2) :=
  ((TensorProduct.congr (DirectSum.decomposeLinearEquiv L.grading)
    (DirectSum.decomposeLinearEquiv N.grading)).trans
    (TensorProduct.directSum R R (fun p ↦ L.grading p) (fun q ↦ N.grading q))).trans
      (absModFiberEquiv L N)

/-- `absModFiberEquiv` sends the bigraded piece of bidegree `(p, q)` to the summand of total
degree `p + q` indexed by `(p, q)`. -/
theorem absModFiberEquiv_lof (p q : ℤ) (x : L.grading p ⊗[R] N.grading q) :
    absModFiberEquiv L N (DirectSum.lof R _ _ (p, q) x) =
      DirectSum.lof R _ _ (p + q) (DirectSum.lof R _ _ ⟨(p, q), rfl⟩ x) := by
  change DirectSum.sigmaFiberAddEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)
      (DirectSum.of (fun pq : ℤ × ℤ ↦ L.grading pq.1 ⊗[R] N.grading pq.2) (p, q) x) = _
  exact DirectSum.sigmaFiberAddEquiv_of
    (β := fun pq : ℤ × ℤ ↦ L.grading pq.1 ⊗[R] N.grading pq.2)
    (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) (p, q) x

/-- `absModTotalEquiv` sends a pure tensor of elements of degrees `p` and `q` to the corresponding
element of the summand of total degree `p + q` indexed by `(p, q)`. -/
theorem absModTotalEquiv_tmul (p q : ℤ) (b : L.grading p) (a : N.grading q) :
    absModTotalEquiv L N ((b : L.M) ⊗ₜ[R] (a : N.M)) =
      DirectSum.lof R ℤ (absModComponents L N) (p + q)
        (DirectSum.lof R _
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = p + q} ↦
            L.grading pq.val.1 ⊗[R] N.grading pq.val.2)
          ⟨(p, q), rfl⟩ (b ⊗ₜ[R] a)) := by
  simp only [absModTotalEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe]
  convert absModFiberEquiv_lof L N p q (b ⊗ₜ[R] a) using 1
  exact congrArg (absModFiberEquiv L N) (by
    simpa only [DirectSum.lof_eq_of] using
      (TensorProduct.directSum_lof_tmul_lof R R
        (M₁ := fun p ↦ L.grading p) (M₂ := fun q ↦ N.grading q) p b q a))

/-- The inclusion of the bigraded pieces of total degree `n` into `L ⊗_R N`. -/
def absModFiberMap (n : ℤ) : absModComponents L N n →ₗ[R] (L.M ⊗[R] N.M) :=
  (absModTotalEquiv L N).symm.toLinearMap ∘ₗ DirectSum.lof R ℤ (absModComponents L N) n

/-- `absModFiberMap` sends a pure tensor in the bigraded piece indexed by `pq` to the same pure
tensor in `L ⊗_R N`. -/
theorem absModFiberMap_lof_tmul (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (b : L.grading pq.val.1) (a : N.grading pq.val.2) :
    absModFiberMap L N n (DirectSum.lof R _ _ pq (b ⊗ₜ[R] a)) = ((b : L.M) ⊗ₜ[R] (a : N.M)) := by
  apply (absModTotalEquiv L N).injective
  obtain ⟨⟨p, q⟩, rfl⟩ := pq
  simpa [absModFiberMap] using (absModTotalEquiv_tmul L N p q b a).symm

/-- `absModFiberMap` takes values in the degree-`n` part of `L ⊗_R N`. -/
theorem absModFiberMap_mem (n : ℤ) (x : absModComponents L N n) :
    absModFiberMap L N n x ∈ absModGrading L N n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using (absModGrading L N n).add_mem hx hy
  | of pq x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using (absModGrading L N n).add_mem hx hy
    | tmul b a =>
      rw [← DirectSum.lof_eq_of (R := R), absModFiberMap_lof_tmul]
      exact Submodule.subset_span
        ⟨pq.val.1, pq.val.2, (b : L.M), (a : N.M), b.property, a.property, pq.property, rfl⟩

/-- The range of `absModFiberMap` in degree `n` is the degree-`n` part of `L ⊗_R N`. -/
theorem absModFiberMap_range_eq (n : ℤ) :
    LinearMap.range (absModFiberMap L N n) = absModGrading L N n := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro x ⟨y, rfl⟩
    exact absModFiberMap_mem L N n y
  · rintro x ⟨p, q, b, a, hb, ha, hpq, rfl⟩
    exact ⟨_, absModFiberMap_lof_tmul L N n ⟨(p, q), hpq⟩ ⟨b, hb⟩ ⟨a, ha⟩⟩

/-- The degree-`n` part of `L ⊗_R N` is the direct sum of the bigraded pieces of total
degree `n`. -/
def absModComponentEquiv (n : ℤ) :
    absModComponents L N n ≃ₗ[R] absModGrading L N n := by
  have hinj : Function.Injective (absModFiberMap L N n) := by
    intro x y h
    apply DirectSum.of_injective n
    simpa [absModFiberMap, DirectSum.lof_eq_of] using congrArg (absModTotalEquiv L N) h
  exact (LinearEquiv.ofInjective (absModFiberMap L N n) hinj).trans
    (LinearEquiv.ofEq _ _ (absModFiberMap_range_eq L N n))

/-- The underlying element of `absModComponentEquiv L N n x` is `absModFiberMap L N n x`. -/
theorem absModComponentEquiv_coe (n : ℤ) (x : absModComponents L N n) :
    ((absModComponentEquiv L N n x : absModGrading L N n) : L.M ⊗[R] N.M) =
      absModFiberMap L N n x := rfl

/-- The grading of `L ⊗_R N` is a direct sum decomposition. -/
def absModGradingEquiv : (L.M ⊗[R] N.M) ≃ₗ[R] (⨁ n : ℤ, absModGrading L N n) :=
  (absModTotalEquiv L N).trans (DirectSum.congrLinearEquiv (absModComponentEquiv L N))

/-- `absModGradingEquiv` sends an element of the degree-`n` part to itself in the summand of
degree `n`. -/
theorem absModGradingEquiv_coe (n : ℤ) (x : absModGrading L N n) :
    absModGradingEquiv L N (x : L.M ⊗[R] N.M) = DirectSum.lof R _ _ n x := by
  obtain ⟨y, rfl⟩ := (absModComponentEquiv L N n).surjective x
  suffices h : (DirectSum.congrLinearEquiv (absModComponentEquiv L N))
        (DirectSum.lof R ℤ (absModComponents L N) n y) =
      DirectSum.lof R ℤ (fun i ↦ absModGrading L N i) n (absModComponentEquiv L N n y) by
    simpa [absModGradingEquiv, absModComponentEquiv_coe, absModFiberMap] using h
  change (DirectSum.lmap (fun i ↦ (absModComponentEquiv L N i).toLinearMap))
    (DirectSum.lof R ℤ (absModComponents L N) n y) = _
  simp

/-- The inverse of `absModGradingEquiv` is the sum of the inclusions of the graded pieces. -/
theorem absModGradingEquiv_symm_eq_coe :
    (absModGradingEquiv L N).symm.toLinearMap =
      DirectSum.coeLinearMap (absModGrading L N) := by
  ext n x
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply]
  rw [DirectSum.coeLinearMap_lof]
  exact (LinearEquiv.symm_apply_eq _).mpr (absModGradingEquiv_coe L N n x).symm

/-- The grading `absModGrading` of `L ⊗_R N` is a direct sum decomposition. -/
@[instance_reducible]
def absModDecomposition : DirectSum.Decomposition (absModGrading L N) := by
  apply DirectSum.Decomposition.ofLinearMap (absModGrading L N)
    (absModGradingEquiv L N).toLinearMap <;>
  · rw [← absModGradingEquiv_symm_eq_coe]
    ext x
    simp

/-! ### The differential graded module -/

/-- A pure tensor of elements of degrees `p` and `q` lies in degree `p + q`. -/
theorem absModTmul_mem (p q : ℤ) (b : L.M) (a : N.M) (hb : b ∈ L.grading p)
    (ha : a ∈ N.grading q) :
    (b ⊗ₜ[R] a : L.M ⊗[R] N.M) ∈ absModGrading L N (p + q) :=
  Submodule.subset_span ⟨p, q, b, a, hb, ha, rfl, rfl⟩

/-- The differential of `L ⊗_R N` raises degree by one. -/
theorem absModDifferential_mem (n : ℤ) (x : L.M ⊗[R] N.M)
    (hx : x ∈ absModGrading L N n) :
    absModDifferential L N x ∈ absModGrading L N (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, b, a, hb, ha, hpq, rfl⟩ := hx
    rw [show b = (⟨b, hb⟩ : L.grading p) from rfl, absModDifferential_tmul]
    apply Submodule.add_mem
    · convert absModTmul_mem L N (p + 1) q (L.d b) a (L.d_mem p b hb) ha using 1
      congr 1
      omega
    · apply zsmul_mem
      convert absModTmul_mem L N p (q + 1) b (N.d a) hb (N.d_mem q a ha) using 1
      congr 1
      omega
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (absModGrading L N (n + 1)).add_mem ihx ihy
  | smul r x hx ih => simpa using (absModGrading L N (n + 1)).smul_mem r ih

/-- The differential of `L ⊗_R N` squares to zero on a pure tensor with homogeneous left
factor. -/
theorem absModDifferential_sq_tmul (p : ℤ) (b : L.grading p) (a : N.M) :
    absModDifferential L N (absModDifferential L N ((b : L.M) ⊗ₜ[R] a)) = 0 := by
  have hL : L.d (L.d (b : L.M)) = 0 := LinearMap.congr_fun L.d_comp_d (b : L.M)
  have hN : N.d (N.d a) = 0 := LinearMap.congr_fun N.d_comp_d a
  rw [absModDifferential_tmul, map_add, map_zsmul,
    absModDifferential_tmul L N (p + 1) ⟨L.d b, L.d_mem p b b.property⟩ a,
    absModDifferential_tmul L N p b (N.d a)]
  simp only [hL, hN, TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add,
    add_zero, smul_zero]
  rw [Int.negOnePow_succ]
  simpa only [Units.val_neg, neg_zsmul] using
    (neg_add_cancel ((p.negOnePow : ℤ) • ((L.d b : L.M) ⊗ₜ[R] N.d a : L.M ⊗[R] N.M)))

/-- The differential of `L ⊗_R N` squares to zero. -/
theorem absModDifferential_sq :
    absModDifferential L N ∘ₗ absModDifferential L N = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  change absModDifferential L N (absModDifferential L N x) = 0
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul b a =>
    induction b using DirectSum.Decomposition.inductionOn L.grading with
    | zero => simp
    | add b b' hb hb' => simp [TensorProduct.add_tmul, map_add, hb, hb']
    | homogeneous b => exact absModDifferential_sq_tmul L N _ b a

/-- The right `B`-action on `L ⊗_R N`, on the second factor. -/
@[instance_reducible]
def absModRightModule : Module (MulOpposite B.A) (L.M ⊗[R] N.M) :=
  (TensorProduct.comm R L.M N.M).toAddEquiv.module _

attribute [local instance] absModRightModule

/-- The `R`-action and the right `B`-action on `L ⊗_R N` form a scalar tower. -/
theorem absModRightScalarTower : IsScalarTower R (MulOpposite B.A) (L.M ⊗[R] N.M) :=
  (TensorProduct.comm R L.M N.M).isScalarTower _

attribute [local instance] absModRightScalarTower

/-- The right action of `a ∈ B` on a pure tensor `b ⊗ x` is `b ⊗ x a`. -/
theorem absMod_smul_tmul (b : L.M) (x : N.M) (a : B.A) :
    MulOpposite.op a • (b ⊗ₜ[R] x) = b ⊗ₜ[R] (MulOpposite.op a • x) := by
  change (TensorProduct.comm R N.M L.M)
    (MulOpposite.op a • (TensorProduct.comm R L.M N.M) (b ⊗ₜ[R] x)) = _
  simp [TensorProduct.smul_tmul']

/-- The right action of an element of `B` of degree `m` sends degree `n` of `L ⊗_R N` to degree
`n + m`. -/
theorem absMod_smul_mem (n m : ℤ) (x : L.M ⊗[R] N.M) (a : B.A)
    (hx : x ∈ absModGrading L N n) (ha : a ∈ B.grading m) :
    MulOpposite.op a • x ∈ absModGrading L N (n + m) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, b, y, hb, hy, rfl, rfl⟩ := hz
    rw [absMod_smul_tmul]
    simpa only [add_assoc] using absModTmul_mem L N p (q + m) b _ hb
      (N.smul_mem q m y a hy ha)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ ih

/-- The Leibniz rule for the right `B`-action on `L ⊗_R N`: for `z` of degree `n` and `a ∈ B`,
`d(z a) = d(z) a + (-1)^n z d(a)`. -/
theorem absMod_leibniz (n m : ℤ) (z : L.M ⊗[R] N.M) (a : B.A)
    (hz : z ∈ absModGrading L N n) (ha : a ∈ B.grading m) :
    absModDifferential L N (MulOpposite.op a • z) =
      MulOpposite.op a • absModDifferential L N z +
        (n.negOnePow : ℤ) • (MulOpposite.op (B.d a) • z) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, b, y, hb, hy, rfl, rfl⟩ := hz
    rw [absMod_smul_tmul, show b = (⟨b, hb⟩ : L.grading p) from rfl,
      absModDifferential_tmul, absModDifferential_tmul, smul_add,
      smul_comm (MulOpposite.op a) (p.negOnePow : ℤ), absMod_smul_tmul, absMod_smul_tmul,
      absMod_smul_tmul, N.leibniz q m y a hy ha]
    simp only [TensorProduct.tmul_add, ← Int.cast_smul_eq_zsmul R, TensorProduct.tmul_smul,
      smul_add, smul_smul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
    abel
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [smul_add, map_add, ihx, ihy]
    abel
  | smul r x hx ih =>
    simp only [smul_comm (MulOpposite.op a) r, smul_comm (MulOpposite.op (B.d a)) r,
      map_smul, ih, smul_add, smul_comm (n.negOnePow : ℤ) r]

attribute [local instance] absModDecomposition

/-- **`L ⊗_R N`**: a right differential graded `A`-module `L`, tensored over the base ring with a
right differential graded `B`-module `N`, is a right differential graded `B`-module, with `B`
acting on the second factor and with the signed tensor differential. Neither factor is required
to be an algebra: the left one enters only through its grading and its differential. -/
@[reducible]
def absoluteTensorModule : DifferentialGradedModule.{u, u, u} B where
  M := L.M ⊗[R] N.M
  grading := absModGrading L N
  smul_mem := absMod_smul_mem L N
  d := absModDifferential L N
  d_comp_d := absModDifferential_sq L N
  d_mem := absModDifferential_mem L N
  leibniz := absMod_leibniz L N

end DifferentialGradedModule

end
