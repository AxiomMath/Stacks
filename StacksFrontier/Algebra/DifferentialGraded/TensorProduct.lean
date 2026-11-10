module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Tensor products of differential graded algebras

For differential graded algebras `(A, d)` and `(B, d)` over a commutative ring `R`, the tensor
product `A ⊗_R B` is again a differential graded algebra: its multiplication carries the Koszul
sign, `(a ⊗ b) · (a' ⊗ b') = (-1)^(deg b · deg a') (a a' ⊗ b b')`, its grading is the total
degree, and its differential is `d (a ⊗ b) = d a ⊗ b + (-1)^(deg a) (a ⊗ d b)`.

## Main definitions

* `DifferentialGradedAlgebra.tensorProductGrading`: the total grading, spanned by the
  homogeneous pure tensors of a given total degree.
* `DifferentialGradedAlgebra.tensorProductDifferential`: the signed tensor differential.
* `DifferentialGradedAlgebra.TensorProductData`: the differential graded algebra axioms for
  these explicit data.
* `DifferentialGradedAlgebra.gradedTensorProduct`: the verification of those axioms, and
  `DifferentialGradedAlgebra.tensorProduct`: the resulting differential graded algebra.

## Main results

* `DifferentialGradedAlgebra.tmul_mem_grading`: a pure tensor of homogeneous elements of degrees
  `p` and `q` has degree `p + q`.
* `DifferentialGradedAlgebra.tensorProductDifferential_tmul`: the signed differential formula on
  a pure tensor whose first factor is homogeneous.

## Implementation notes

The underlying algebra is Mathlib's `GradedTensorProduct`, which already has the Koszul-signed
multiplication; its underlying module is identified with `A ⊗_R B` by `GradedTensorProduct.of`.
The total grading is defined as the span of the homogeneous pure tensors of the given total
degree, and the direct-sum decomposition it carries is obtained by reorganizing
`A ⊗_R B = ⨁_(p,q) A^p ⊗ B^q` along the fibres of `(p, q) ↦ p + q`; the chain of equivalences
`totalEquiv`, `componentEquiv` and `gradingEquiv` performs that reorganization.

The construction produces a concrete `DifferentialGradedAlgebra`, so it can serve directly as
the coefficient algebra for differential graded modules; it is stated through
`TensorProductData` so that the grading and the differential appearing in the result are the two
explicit ones defined here rather than whichever ones a bundled construction happens to choose.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
-/

@[expose] public section

universe u

namespace DifferentialGradedAlgebra

open scoped TensorProduct DirectSum

variable {R : Type u} [CommRing R]
variable (A : DifferentialGradedAlgebra R)
variable (B : DifferentialGradedAlgebra R)

add_to_stacks 065W "the Koszul-signed underlying algebra" GradedTensorProduct
add_to_sga "7 XII 1.9" GradedTensorProduct
add_to_stacks 065W "the underlying module identification" GradedTensorProduct.of
add_to_stacks 065W "the homogeneous multiplication formula"
  GradedTensorProduct.tmul_coe_mul_coe_tmul
add_to_sga "7 XII 1.9" "more general" GradedTensorProduct.tmul_coe_mul_coe_tmul

/-- The degree-`n` part is spanned by pure tensors whose factors have degrees
adding to `n`. -/
@[stacks 065W "the total grading"]
public noncomputable def tensorProductGrading (n : ℤ) :
    Submodule R (A.grading ᵍ⊗[R] B.grading) :=
  Submodule.span R {x | ∃ (p q : ℤ) (a : A.A) (b : B.A),
    a ∈ A.grading p ∧ b ∈ B.grading q ∧ p + q = n ∧ x = a ᵍ⊗ₜ[R] b}

/-- Multiplication by `(-1)^p` on the degree-`p` part of `A`. -/
public noncomputable def koszulSign : A.A →ₗ[R] A.A :=
  (DirectSum.toModule R ℤ A.A fun p ↦
      (p.negOnePow : ℤ) • (A.grading p).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv A.grading).toLinearMap

/-- The signed tensor differential `d_A ⊗ 1 + (-1)^deg ⊗ d_B`. -/
@[stacks 065W "the signed differential", sga "4 XVII 1.1.10" "(i)"]
public noncomputable def tensorProductDifferential :
    (A.grading ᵍ⊗[R] B.grading) →ₗ[R] (A.grading ᵍ⊗[R] B.grading) :=
  (GradedTensorProduct.of R A.grading B.grading).toLinearMap ∘ₗ
    (TensorProduct.map A.d LinearMap.id +
      TensorProduct.map (koszulSign A) B.d) ∘ₗ
    (GradedTensorProduct.of R A.grading B.grading).symm.toLinearMap

/-- On a homogeneous element of degree `p`, `koszulSign` is multiplication by `(-1)^p`. -/
public lemma koszulSign_apply_coe (p : ℤ) (a : A.grading p) :
    koszulSign A a = (p.negOnePow : ℤ) • (a : A.A) := by
  simp [koszulSign, DirectSum.toModule_lof]

/-- An integer scalar on the first factor of a pure tensor can be taken out. -/
private theorem of_zsmul_tmul (n : ℤ) (x : A.A) (y : B.A) :
    (GradedTensorProduct.of R A.grading B.grading) ((n • x) ⊗ₜ[R] y) =
      n • (GradedTensorProduct.of R A.grading B.grading) (x ⊗ₜ[R] y) := by
  rw [← Int.cast_smul_eq_zsmul R, ← TensorProduct.smul_tmul',
    LinearEquiv.map_smul, Int.cast_smul_eq_zsmul]

/-- The signed differential on a pure tensor whose first factor has degree `p`, with the sign
written as the integer `(-1)^p`. -/
public lemma tensorProductDifferential_tmul_aux (p : ℤ) (a : A.grading p) (b : B.A) :
    tensorProductDifferential A B ((a : A.A) ᵍ⊗ₜ[R] b) =
      (A.d a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) +
        (p.negOnePow : ℤ) • ((a : A.A) ᵍ⊗ₜ[R] B.d b) := by
  simp [tensorProductDifferential, GradedTensorProduct.tmul, koszulSign_apply_coe]
  simpa only [zsmul_eq_mul, Int.coe_negOnePow] using
    of_zsmul_tmul A B (p.negOnePow : ℤ) (a : A.A) (B.d b)

/-- The signed differential on a pure tensor whose first factor has degree `p`, with the sign
acting as the unit `(-1)^p`. -/
public lemma tensorProductDifferential_tmul_aux' (p : ℤ) (a : A.grading p) (b : B.A) :
    tensorProductDifferential A B ((a : A.A) ᵍ⊗ₜ[R] b) =
      (A.d a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) +
        p.negOnePow • ((a : A.A) ᵍ⊗ₜ[R] B.d b) := by
  simpa only [Units.smul_def] using tensorProductDifferential_tmul_aux A B p a b

/-- Regrouping `⨁_(p,q) A^p ⊗ B^q` along the fibres of `(p, q) ↦ p + q`. -/
public noncomputable def fiberEquiv :
    (⨁ pq : ℤ × ℤ, A.grading pq.1 ⊗[R] B.grading pq.2) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        A.grading pq.val.1 ⊗[R] B.grading pq.val.2) := by
  let e₁ :
      (⨁ k : (n : ℤ) × {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        A.grading k.2.val.1 ⊗[R] B.grading k.2.val.2) ≃ₗ[R]
        (⨁ pq : ℤ × ℤ, A.grading pq.1 ⊗[R] B.grading pq.2) :=
    DirectSum.lequivCongrLeft R
      (Equiv.sigmaFiberEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2))
  exact e₁.symm.trans (DirectSum.sigmaLcurryEquiv R
    (δ := fun (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) ↦
      A.grading pq.val.1 ⊗[R] B.grading pq.val.2))

/-- The summands `A^p ⊗ B^q` with `p + q = n`, assembled into one direct sum. -/
public abbrev totalComponents (n : ℤ) : Type _ :=
  ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
    A.grading pq.val.1 ⊗[R] B.grading pq.val.2

/-- The graded tensor product `A ⊗_R B`, decomposed as `⨁_n ⨁_(p + q = n) A^p ⊗ B^q`. -/
public noncomputable def totalEquiv :
    (A.grading ᵍ⊗[R] B.grading) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        A.grading pq.val.1 ⊗[R] B.grading pq.val.2) :=
  ((GradedTensorProduct.auxEquiv R A.grading B.grading).trans
    (TensorProduct.directSum R R (fun p ↦ A.grading p) (fun q ↦ B.grading q))).trans
      (fiberEquiv A B)

/-- `fiberEquiv` sends the `(p, q)` summand into the fibre over `p + q`. -/
public lemma fiberEquiv_lof (p q : ℤ)
    (x : A.grading p ⊗[R] B.grading q) :
    fiberEquiv A B (DirectSum.lof R _ _ (p, q) x) =
      DirectSum.lof R _ _ (p + q)
        (DirectSum.lof R _ _ ⟨(p, q), rfl⟩ x) := by
  change DirectSum.sigmaFiberAddEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)
      (DirectSum.of (fun pq : ℤ × ℤ ↦ A.grading pq.1 ⊗[R] B.grading pq.2) (p, q) x) = _
  exact DirectSum.sigmaFiberAddEquiv_of
    (β := fun pq : ℤ × ℤ ↦ A.grading pq.1 ⊗[R] B.grading pq.2)
    (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) (p, q) x

/-- `totalEquiv` sends a pure tensor of homogeneous elements of degrees `p` and `q` to its
component in the fibre over `p + q`. -/
public lemma totalEquiv_tmul (p q : ℤ) (a : A.grading p) (b : B.grading q) :
    totalEquiv A B ((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) =
      DirectSum.lof R ℤ (totalComponents A B) (p + q)
        (DirectSum.lof R _
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = p + q} ↦
            A.grading pq.val.1 ⊗[R] B.grading pq.val.2)
          ⟨(p, q), rfl⟩ (a ⊗ₜ[R] b)) := by
  simp only [totalEquiv, LinearEquiv.trans_apply, GradedTensorProduct.auxEquiv_tmul,
    DirectSum.decompose_coe]
  convert fiberEquiv_lof A B p q (a ⊗ₜ[R] b) using 1
  exact congrArg (fiberEquiv A B) (by
    simpa only [DirectSum.lof_eq_of] using
      (TensorProduct.directSum_lof_tmul_lof R R
        (M₁ := fun p ↦ A.grading p) (M₂ := fun q ↦ B.grading q) p a q b))

/-- The inclusion of the fibre over `n` into the graded tensor product. -/
public noncomputable def fiberMap (n : ℤ) :
    totalComponents A B n →ₗ[R] (A.grading ᵍ⊗[R] B.grading) :=
  (totalEquiv A B).symm.toLinearMap ∘ₗ
    DirectSum.lof R ℤ (totalComponents A B) n

/-- `fiberMap` sends the pure tensor of a summand to the corresponding pure tensor. -/
public lemma fiberMap_lof_tmul (n : ℤ)
    (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (a : A.grading pq.val.1) (b : B.grading pq.val.2) :
    fiberMap A B n (DirectSum.lof R _ _ pq (a ⊗ₜ[R] b)) =
      ((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) := by
  apply (totalEquiv A B).injective
  obtain ⟨⟨p, q⟩, h⟩ := pq
  subst n
  simpa [fiberMap] using (totalEquiv_tmul A B p q a b).symm

/-- The fibre over `n` lands in the degree-`n` part of the total grading. -/
public lemma fiberMap_mem (n : ℤ) (x : totalComponents A B n) :
    fiberMap A B n x ∈ tensorProductGrading A B n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using (tensorProductGrading A B n).add_mem hx hy
  | of pq x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa using (tensorProductGrading A B n).add_mem hx hy
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (R := R), fiberMap_lof_tmul]
      exact Submodule.subset_span ⟨pq.val.1, pq.val.2, (a : A.A), (b : B.A), a.property, b.property,
        pq.property, rfl⟩

/-- The degree-`n` part of the total grading is exactly the image of the fibre over `n`. -/
public lemma fiberMap_range_eq (n : ℤ) :
    LinearMap.range (fiberMap A B n) = tensorProductGrading A B n := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact fiberMap_mem A B n y
  · apply Submodule.span_le.mpr
    rintro x ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    let pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} := ⟨(p, q), hpq⟩
    refine ⟨DirectSum.lof R _ _ pq (⟨a, ha⟩ ⊗ₜ[R] ⟨b, hb⟩), ?_⟩
    exact fiberMap_lof_tmul A B n pq ⟨a, ha⟩ ⟨b, hb⟩

/-- The fibre over `n` is isomorphic to the degree-`n` part of the total grading. -/
public noncomputable def componentEquiv (n : ℤ) :
    totalComponents A B n ≃ₗ[R] tensorProductGrading A B n := by
  have hinj : Function.Injective (fiberMap A B n) := by
    intro x y h
    apply DirectSum.of_injective n
    simpa [fiberMap, DirectSum.lof_eq_of] using congrArg (totalEquiv A B) h
  exact (LinearEquiv.ofInjective (fiberMap A B n) hinj).trans
    (LinearEquiv.ofEq _ _ (fiberMap_range_eq A B n))

/-- `componentEquiv` is `fiberMap` after forgetting the grading. -/
public lemma componentEquiv_coe (n : ℤ) (x : totalComponents A B n) :
    ((componentEquiv A B n x : tensorProductGrading A B n) :
      A.grading ᵍ⊗[R] B.grading) = fiberMap A B n x := rfl

/-- The graded tensor product as the direct sum of the parts of its total grading. -/
public noncomputable def gradingEquiv :
    (A.grading ᵍ⊗[R] B.grading) ≃ₗ[R]
      (⨁ n : ℤ, tensorProductGrading A B n) :=
  (totalEquiv A B).trans (DirectSum.congrLinearEquiv (componentEquiv A B))

/-- `gradingEquiv` sends an element of the degree-`n` part to the `n`-th summand. -/
public lemma gradingEquiv_coe (n : ℤ) (x : tensorProductGrading A B n) :
    gradingEquiv A B (x : A.grading ᵍ⊗[R] B.grading) =
      DirectSum.lof R _ _ n x := by
  obtain ⟨y, rfl⟩ := (componentEquiv A B n).surjective x
  suffices h :
      (DirectSum.congrLinearEquiv (componentEquiv A B))
          (DirectSum.lof R ℤ (totalComponents A B) n y) =
        DirectSum.lof R ℤ (fun i ↦ tensorProductGrading A B i) n
          (componentEquiv A B n y) by
    simpa [gradingEquiv, componentEquiv_coe, fiberMap] using h
  change (DirectSum.lmap (fun i ↦ (componentEquiv A B i).toLinearMap))
      (DirectSum.lof R ℤ (totalComponents A B) n y) = _
  simp

/-- The inverse of `gradingEquiv` is the sum of the inclusions of the graded parts. -/
public lemma gradingEquiv_symm_eq_coe :
    (gradingEquiv A B).symm.toLinearMap =
      DirectSum.coeLinearMap (tensorProductGrading A B) := by
  ext n x
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply]
  rw [DirectSum.coeLinearMap_lof]
  exact (LinearEquiv.symm_apply_eq _).mpr (gradingEquiv_coe A B n x).symm

/-- The total grading is a direct-sum decomposition of the graded tensor product. -/
@[instance_reducible]
public noncomputable def totalDecomposition :
    DirectSum.Decomposition (tensorProductGrading A B) := by
  apply DirectSum.Decomposition.ofLinearMap (tensorProductGrading A B)
    (gradingEquiv A B).toLinearMap
  · rw [← gradingEquiv_symm_eq_coe]
    ext x
    simp
  · rw [← gradingEquiv_symm_eq_coe]
    ext x
    simp

/-- A pure tensor of homogeneous elements of degrees `p` and `q` has total degree `p + q`. -/
public lemma tmul_mem_total (p q : ℤ) (a : A.A) (b : B.A)
    (ha : a ∈ A.grading p) (hb : b ∈ B.grading q) :
    (a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) ∈
      tensorProductGrading A B (p + q) :=
  Submodule.subset_span ⟨p, q, a, b, ha, hb, rfl, rfl⟩

/-- The total grading is multiplicative. -/
public theorem totalGradedMonoid :
    SetLike.GradedMonoid (tensorProductGrading A B) where
  one_mem := by
    have h := tmul_mem_total A B 0 0 (1 : A.A) (1 : B.A)
      (SetLike.one_mem_graded A.grading) (SetLike.one_mem_graded B.grading)
    simpa [GradedTensorProduct.tmul, ← GradedTensorProduct.of_one,
      Algebra.TensorProduct.one_def] using h
  mul_mem n m x y hx hy := by
    have h : (tensorProductGrading A B n).map₂
        (Algebra.lmul R (A.grading ᵍ⊗[R] B.grading))
        (tensorProductGrading A B m) ≤ tensorProductGrading A B (n + m) := by
      rw [tensorProductGrading, tensorProductGrading, Submodule.map₂_span_span]
      apply Submodule.span_le.mpr
      rintro z ⟨x, ⟨p, q, a, b, ha, hb, hpn, rfl⟩,
        y, ⟨r, s, c, d, hc, hd, hrm, rfl⟩, rfl⟩
      change (a ᵍ⊗ₜ[R] b) * (c ᵍ⊗ₜ[R] d) ∈ tensorProductGrading A B (n + m)
      rw [GradedTensorProduct.tmul_coe_mul_coe_tmul A.grading B.grading
        a ⟨b, hb⟩ ⟨c, hc⟩ d]
      rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
      apply Submodule.smul_mem
      have hp : a * c ∈ A.grading (p + r) := SetLike.mul_mem_graded ha hc
      have hq : b * d ∈ B.grading (q + s) := SetLike.mul_mem_graded hb hd
      convert tmul_mem_total A B (p + r) (q + s) (a * c) (b * d) hp hq using 1
      congr 1
      omega
    exact h (Submodule.apply_mem_map₂ _ hx hy)

/-- The graded tensor product is a graded algebra for the total grading. -/
@[instance_reducible]
public noncomputable def totalGradedAlgebra :
    GradedAlgebra (tensorProductGrading A B) := by
  letI : SetLike.GradedMonoid (tensorProductGrading A B) := totalGradedMonoid A B
  letI : DirectSum.Decomposition (tensorProductGrading A B) := totalDecomposition A B
  exact DirectSum.IsInternal.gradedAlgebra
    (DirectSum.Decomposition.isInternal (tensorProductGrading A B))

/-- The signed differential raises the total degree by one. -/
public lemma differential_mem_total (n : ℤ)
    (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B n) :
    tensorProductDifferential A B x ∈ tensorProductGrading A B (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hx
    rw [show a = (⟨a, ha⟩ : A.grading p) from rfl]
    rw [tensorProductDifferential_tmul_aux]
    apply Submodule.add_mem
    · convert tmul_mem_total A B (p + 1) q (A.d a) b (A.d_mem p a ha) hb using 1
      congr 1
      omega
    · apply zsmul_mem
      convert tmul_mem_total A B p (q + 1) a (B.d b) ha (B.d_mem q b hb) using 1
      congr 1
      omega
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (tensorProductGrading A B (n + 1)).add_mem ihx ihy
  | smul r x hx ih => simpa using (tensorProductGrading A B (n + 1)).smul_mem r ih

/-- The signed differential squares to zero on a pure tensor whose first factor is
homogeneous. -/
public lemma differential_sq_tmul (p : ℤ) (a : A.grading p) (b : B.A) :
    tensorProductDifferential A B
      (tensorProductDifferential A B ((a : A.A) ᵍ⊗ₜ[R] b)) = 0 := by
  have ha : A.d (a : A.A) ∈ A.grading (p + 1) := A.d_mem p a a.property
  have hA : A.d (A.d (a : A.A)) = 0 := by simpa using LinearMap.congr_fun A.d_comp_d (a : A.A)
  have hB : B.d (B.d b) = 0 := by simpa using LinearMap.congr_fun B.d_comp_d b
  rw [tensorProductDifferential_tmul_aux, map_add, map_zsmul]
  rw [tensorProductDifferential_tmul_aux A B (p + 1) ⟨A.d a, ha⟩ b,
    tensorProductDifferential_tmul_aux A B p a (B.d b)]
  simp only [hA, hB, GradedTensorProduct.tmul, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, map_zero, zero_add, add_zero, smul_zero]
  rw [Int.negOnePow_succ]
  simpa only [Units.val_neg, neg_zsmul] using
    (neg_add_cancel ((p.negOnePow : ℤ) •
      ((A.d a : A.A) ᵍ⊗ₜ[R] B.d b : A.grading ᵍ⊗[R] B.grading)))

/-- The signed differential squares to zero. -/
public lemma differential_sq_zero_total :
    tensorProductDifferential A B ∘ₗ tensorProductDifferential A B = 0 := by
  apply LinearMap.ext; intro x
  change tensorProductDifferential A B (tensorProductDifferential A B x) = 0
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of R A.grading B.grading).surjective x
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a b =>
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add a a' ha ha' =>
      simp [TensorProduct.add_tmul, map_add, ha, ha']
    | homogeneous a => exact differential_sq_tmul A B _ a b

/-- The Koszul sign rule for the product of two pure tensors of homogeneous elements. -/
public lemma tmul_mul (p q r s : ℤ)
    (a : A.grading p) (b : B.grading q)
    (c : A.grading r) (d : B.grading s) :
    ((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) *
        ((c : A.A) ᵍ⊗ₜ[R] (d : B.A)) =
      (q * r).negOnePow •
        (((a : A.A) * c) ᵍ⊗ₜ[R] ((b : B.A) * d) :
          A.grading ᵍ⊗[R] B.grading) := by
  simpa only [Int.negOnePow_def] using
    (GradedTensorProduct.tmul_coe_mul_coe_tmul A.grading B.grading
      (a : A.A) b c (d : B.A))

/-- A unit scalar on the left factor of a product can be taken out. -/
public lemma units_smul_mul (u : ℤˣ)
    (x y : A.grading ᵍ⊗[R] B.grading) :
    (u • x) * y = u • (x * y) := by
  exact smul_mul_assoc u x y

/-- A unit scalar on the right factor of a product can be taken out. -/
public lemma mul_units_smul (u : ℤˣ)
    (x y : A.grading ᵍ⊗[R] B.grading) :
    x * (u • y) = u • (x * y) := by
  exact mul_smul_comm u x y

/-- The graded pure tensor is additive in its first factor. -/
public lemma tmul_add_left (x x' : A.A) (y : B.A) :
    ((x + x') ᵍ⊗ₜ[R] y : A.grading ᵍ⊗[R] B.grading) =
      (x ᵍ⊗ₜ[R] y) + (x' ᵍ⊗ₜ[R] y) := by simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]

/-- The graded pure tensor is additive in its second factor. -/
public lemma tmul_add_right (x : A.A) (y y' : B.A) :
    (x ᵍ⊗ₜ[R] (y + y') : A.grading ᵍ⊗[R] B.grading) =
      (x ᵍ⊗ₜ[R] y) + (x ᵍ⊗ₜ[R] y') := by simp [GradedTensorProduct.tmul, TensorProduct.tmul_add]

/-- A unit scalar on the first factor of a graded pure tensor can be taken out. -/
public lemma units_smul_tmul_left (u : ℤˣ) (x : A.A) (y : B.A) :
    ((u • x) ᵍ⊗ₜ[R] y : A.grading ᵍ⊗[R] B.grading) =
      u • (x ᵍ⊗ₜ[R] y) := by
  change (GradedTensorProduct.of R A.grading B.grading) ((u • x) ⊗ₜ[R] y) =
    u • (GradedTensorProduct.of R A.grading B.grading) (x ⊗ₜ[R] y)
  exact of_zsmul_tmul A B u x y

/-- A unit scalar on the second factor of a graded pure tensor can be taken out. -/
public lemma units_smul_tmul_right (u : ℤˣ) (x : A.A) (y : B.A) :
    (x ᵍ⊗ₜ[R] (u • y) : A.grading ᵍ⊗[R] B.grading) =
      u • (x ᵍ⊗ₜ[R] y) := by
  simp only [GradedTensorProduct.tmul, Units.smul_def,
    ← Int.cast_smul_eq_zsmul R, TensorProduct.tmul_smul, LinearEquiv.map_smul]

/-- The graded Leibniz rule for the signed differential on a product of two pure tensors of
homogeneous elements. -/
public lemma differential_leibniz_tmul (p q r s : ℤ)
    (a : A.grading p) (b : B.grading q)
    (c : A.grading r) (d : B.grading s) :
    tensorProductDifferential A B
      (((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) *
        ((c : A.A) ᵍ⊗ₜ[R] (d : B.A))) =
      tensorProductDifferential A B ((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) *
        ((c : A.A) ᵍ⊗ₜ[R] (d : B.A)) +
      (p + q).negOnePow •
        (((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) *
          tensorProductDifferential A B ((c : A.A) ᵍ⊗ₜ[R] (d : B.A))) := by
  have hab : (a : A.A) * c ∈ A.grading (p + r) := SetLike.mul_mem_graded a.property c.property
  have hbd : (b : B.A) * d ∈ B.grading (q + s) := SetLike.mul_mem_graded b.property d.property
  have hda : A.d (a : A.A) ∈ A.grading (p + 1) := A.d_mem p a a.property
  have hdb : B.d (b : B.A) ∈ B.grading (q + 1) := B.d_mem q b b.property
  have hdc : A.d (c : A.A) ∈ A.grading (r + 1) := A.d_mem r c c.property
  have hdd : B.d (d : B.A) ∈ B.grading (s + 1) := B.d_mem s d d.property
  have hA : A.d ((a : A.A) * c) =
      A.d a * c + p.negOnePow • ((a : A.A) * A.d c) := by
    simpa only [Units.smul_def] using
      (A.leibniz p r (a : A.A) (c : A.A) a.property c.property)
  have hB : B.d ((b : B.A) * d) =
      B.d b * d + q.negOnePow • ((b : B.A) * B.d d) := by
    simpa only [Units.smul_def] using
      (B.leibniz q s (b : B.A) (d : B.A) b.property d.property)
  rw [tmul_mul A B p q r s a b c d, map_zsmul_unit,
    tensorProductDifferential_tmul_aux' A B (p + r) ⟨_, hab⟩ ((b : B.A) * d)]
  rw [tensorProductDifferential_tmul_aux' A B p a b,
    tensorProductDifferential_tmul_aux' A B r c d]
  simp only [mul_add, add_mul, smul_add]
  rw [hA, hB]
  simp only [tmul_add_left, tmul_add_right, units_smul_tmul_left,
    units_smul_tmul_right, smul_add, units_smul_mul, mul_units_smul, smul_smul]
  rw [tmul_mul A B (p + 1) q r s ⟨A.d a, hda⟩ b c d,
    tmul_mul A B p (q + 1) r s a ⟨B.d b, hdb⟩ c d,
    tmul_mul A B p q (r + 1) s a b ⟨A.d c, hdc⟩ d,
    tmul_mul A B p q r (s + 1) a b c ⟨B.d d, hdd⟩]
  simp only [smul_smul]
  have hs2 : (q * r).negOnePow * (p + r).negOnePow =
      p.negOnePow * ((q + 1) * r).negOnePow := by
    simp only [Int.negOnePow_add, add_mul, one_mul]
    ac_rfl
  have hs3 : (q * r).negOnePow * p.negOnePow =
      (p + q).negOnePow * (q * (r + 1)).negOnePow := by
    simp only [Int.negOnePow_add, mul_add, mul_one]
    calc
      (q * r).negOnePow * p.negOnePow =
          p.negOnePow * (q * r).negOnePow := by ac_rfl
      _ = p.negOnePow * ((q.negOnePow * q.negOnePow) * (q * r).negOnePow) := by
        rw [Int.units_mul_self, one_mul]
      _ = p.negOnePow * q.negOnePow * ((q * r).negOnePow * q.negOnePow) := by ac_rfl
  have hs4 : (q * r).negOnePow * ((p + r).negOnePow * q.negOnePow) =
      (p + q).negOnePow * r.negOnePow * (q * r).negOnePow := by
    simp only [Int.negOnePow_add]
    ac_rfl
  rw [hs2, hs3, hs4]; abel

/-- The graded Leibniz rule for the signed differential and the total grading. -/
public lemma differential_leibniz_total (n m : ℤ)
    (x y : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B n)
    (hy : y ∈ tensorProductGrading A B m) :
    tensorProductDifferential A B (x * y) =
      tensorProductDifferential A B x * y +
        (n.negOnePow : ℤ) • (x * tensorProductDifferential A B y) := by
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, s, c, d, hc, hd, hrm, rfl⟩ := hy
      subst n
      simpa only [Units.smul_def] using
        (differential_leibniz_tmul A B p q r s ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩)
    | zero => simp
    | add y z hy hz ihy ihz =>
      simp [mul_add, map_add, smul_add, ihy, ihz]; abel
    | smul t y hy ih =>
      rw [Algebra.mul_smul_comm t (a ᵍ⊗ₜ[R] b) y, map_smul, ih]
      rw [smul_add, map_smul,
        Algebra.mul_smul_comm t ((tensorProductDifferential A B) (a ᵍ⊗ₜ[R] b)) y,
        Algebra.mul_smul_comm t (a ᵍ⊗ₜ[R] b) ((tensorProductDifferential A B) y),
        smul_comm]
  | zero => simp
  | add x z hx hz ihx ihz =>
    simp [add_mul, map_add, smul_add, ihx y hy, ihz y hy]; abel
  | smul t x hx ih =>
    rw [Algebra.smul_mul_assoc t x y, map_smul, ih y hy]
    rw [smul_add, map_smul,
      Algebra.smul_mul_assoc t ((tensorProductDifferential A B) x) y,
      Algebra.smul_mul_assoc t x ((tensorProductDifferential A B) y),
      smul_comm]

/-- The tensor-product data, with the total grading and signed differential
fixed above, satisfy the differential graded algebra axioms. -/
public structure TensorProductData where
  /-- The total grading makes the graded tensor product a graded algebra. -/
  [gradedAlgebra : GradedAlgebra (tensorProductGrading A B)]
  /-- The signed differential squares to zero. -/
  differential_comp_differential :
    tensorProductDifferential A B ∘ₗ tensorProductDifferential A B = 0
  /-- The signed differential raises the total degree by one. -/
  differential_mem : ∀ (n : ℤ) (x : A.grading ᵍ⊗[R] B.grading),
    x ∈ tensorProductGrading A B n →
      tensorProductDifferential A B x ∈ tensorProductGrading A B (n + 1)
  /-- The graded Leibniz rule. -/
  leibniz : ∀ (n m : ℤ) (x y : A.grading ᵍ⊗[R] B.grading),
    x ∈ tensorProductGrading A B n → y ∈ tensorProductGrading A B m →
      tensorProductDifferential A B (x * y) =
        tensorProductDifferential A B x * y +
          (n.negOnePow : ℤ) • (x * tensorProductDifferential A B y)

namespace TensorProductData

/-- Regard the tensor-product data as a concrete differential graded algebra. -/
@[implicit_reducible]
public noncomputable def toDifferentialGradedAlgebra
    (T : TensorProductData A B) : DifferentialGradedAlgebra R := by
  letI := T.gradedAlgebra
  exact
    { A := A.grading ᵍ⊗[R] B.grading
      grading := tensorProductGrading A B
      d := tensorProductDifferential A B
      d_comp_d := T.differential_comp_differential
      d_mem := T.differential_mem
      leibniz := T.leibniz }

end TensorProductData

/-- The tensor product differential graded algebra with the specified carrier,
total grading, Koszul multiplication, and signed differential. -/
@[stacks 065W "the differential graded algebra construction", implicit_reducible]
public noncomputable def gradedTensorProduct : TensorProductData A B where
  gradedAlgebra := totalGradedAlgebra A B
  differential_comp_differential := differential_sq_zero_total A B
  differential_mem := differential_mem_total A B
  leibniz := differential_leibniz_total A B

/-- The tensor product as a coefficient algebra for differential graded modules. -/
@[stacks 065W "the coefficient differential graded algebra", sga "4 XVII 1.1.10" "(i)"]
public noncomputable abbrev tensorProduct : DifferentialGradedAlgebra R :=
  (gradedTensorProduct A B).toDifferentialGradedAlgebra

/-- A pure tensor of elements in degrees `p` and `q` has degree `p + q`. -/
@[stacks 065W "the degree of a pure tensor"]
public lemma tmul_mem_grading (p q : ℤ) (a : A.A) (b : B.A)
    (ha : a ∈ A.grading p) (hb : b ∈ B.grading q) :
    (a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) ∈
      (tensorProduct A B).grading (p + q) :=
  tmul_mem_total A B p q a b ha hb

/-- On a pure tensor whose first factor has degree `p`, the tensor-product
differential is `d a ⊗ₜ b + (-1)^p • (a ⊗ₜ d b)`. -/
@[stacks 065W "the homogeneous differential formula"]
public lemma tensorProductDifferential_tmul (p : ℤ) (a : A.grading p) (b : B.A) :
    (tensorProduct A B).d (((a : A.A) ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading)) =
      (A.d a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) +
        (p.negOnePow : ℤ) • ((a : A.A) ᵍ⊗ₜ[R] B.d b) :=
  tensorProductDifferential_tmul_aux A B p a b

end DifferentialGradedAlgebra
