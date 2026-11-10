module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLeftPropertyP
public import StacksFrontier.Homology.KFlat.QuasiIso

/-!
# Composition of derived tensor products over a K-flat algebra

Let `R` be a ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded `R`-algebras.
Stacks Tag 09S4 says that when `C` is K-flat as a complex of `R`-modules the canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of Tag 0BZ4 is an isomorphism in
`D(C, d)`, and that the conclusion of Tag 0BZ5 — the composite of two derived tensor functors is
a derived tensor functor — is therefore valid.

The content of the proof is the identification `M ⊗_B {}_B(B ⊗_R C)_C = M ⊗_R C` for a right
differential graded `B`-module `M`. Granting it, tensoring with the base-change bimodule is, on
underlying complexes, the total complex of the tensor product with `C` over `R`, which carries
quasi-isomorphisms to quasi-isomorphisms when `C` is K-flat (Tag 06Y0); so the plain tensor
functor already computes the derived one and the comparison of Tag 09LS is invertible, which at
`(A ⊗_R B)_B` is the map of Tag 0BZ4.

## Main definitions

* `DifferentialGradedModule.absoluteTensor`: the right differential graded `C`-module `M ⊗_R C`,
  with `C` acting on the second factor and with the signed tensor differential.
* `DifferentialGraded.absUnbalance`: the bilinear map `(x, b ⊗ c) ↦ (x · b) ⊗ c` underlying the
  identification, and `DifferentialGraded.absBalanceForward`,
  `DifferentialGraded.absBalanceInverse`: the two homomorphisms of differential graded
  `C`-modules it produces.
* `DifferentialGraded.absTensorComplex`: the total complex `Tot(M ⊗_R C)` of the tensor product
  double complex of the complexes underlying `M` and `C`.
* `DifferentialGraded.absRightTensorMap`: tensoring a homomorphism with `C` over `R`, on total
  complexes.

## Main results

* `DifferentialGraded.absBalanceIso`: the identification
  `M ⊗_B {}_B(B ⊗_R C)_C = M ⊗_R C` of right differential graded `C`-modules.
* `DifferentialGraded.absTotalIso` and `DifferentialGraded.absBalancedComplexIso`: the complex
  underlying `M ⊗_R C`, and hence the one underlying `M ⊗_B {}_B(B ⊗_R C)_C`, is the total
  complex `Tot(M ⊗_R C)`.
* `DifferentialGraded.tensorPreservesQuasiIso_baseChangeBimodule`: Tag 06Y0 for the base-change
  bimodule — tensoring with `{}_B(B ⊗_R C)_C` preserves quasi-isomorphisms when `C` is K-flat.
* `DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_of_kFlat`: **the first
  conclusion of Tag 09S4**, that the map of Tag 0BZ4 is an isomorphism.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlat`: the conclusion of Tag 0BZ5
  under K-flatness of `C`, with the inputs of Tag 0BZ5 itself still taken as hypotheses. The
  second conclusion of Tag 09S4 is obtained from it, with those hypotheses discharged, as
  `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatAlgebra` in
  `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorBaseChangeSecondVariable.lean`;
  the dévissage that discharges the last of them is proved there, which is why it cannot be
  stated in this file.

## Implementation notes

*Why `M ⊗_R C` has to be built by hand.* The relative tensor product with a bimodule is
characterized by its universal property (`DifferentialGraded.Bimodule.tensorDGFunctor`) and has
no presentation, so the only way to compute `M ⊗_B {}_B(B ⊗_R C)_C` is to exhibit a concrete
differential graded `C`-module with the same universal property. That module is
`DifferentialGradedModule.absoluteTensor`, on the underlying `R`-module `M ⊗_R C`; its grading
is spanned by the pure tensors of homogeneous elements and its direct-sum decomposition is the
regrouping of the bigraded pieces `M^p ⊗_R C^q` by total degree, which is also what identifies
its complex with the total complex.

*Two spellings of one module.* The right differential graded `B`-module underlying
`{}_B(B ⊗_R C)_C` is `B ⊗_R C` reached through the bimodule structure, and rewriting does not
see through that spelling. As in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorAlgebraComparison.lean`, the pure
tensors are therefore read once at the graded tensor product itself, as
`DifferentialGraded.absRelativePureBilinear`, and every statement below is given at that
spelling.

*The lifted monoidal structure.* `CochainComplex.KFlat` (Tag 06XZ) is stated against the
large-universe monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Monoidal/LargeUniverse.lean`, whose tensor unit is
`ULift R`; Mathlib's own instance on `ModuleCat.{u} R` has higher priority and would otherwise be
selected here, where the module universe equals the ring's. The two lifted instances are
therefore raised to local instances for this file, so that the total complexes formed below are
the ones K-flatness speaks about.

*Universes.* The differential graded algebras and their modules live in a single universe `u`,
following the encoding of Tag 09JJ used throughout this chapter; K-flatness is then taken at
`CochainComplex.KFlat.{u, u}`, where the module universe coincides with the ring's.

## References

* [Stacks Project, Tag 09S4](https://stacks.math.columbia.edu/tag/09S4); the map it is about is
  [Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the lemma whose conclusion it revalidates
  is [Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), the input of its proof is
  [Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0), K-flatness is
  [Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ), the derived tensor product and its
  comparison with the plain one are [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2), and the plain tensor functor is
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM).
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {B : DifferentialGradedAlgebra.{u, u} R}
  (M : DifferentialGradedModule.{u, u, u} B) (C : DifferentialGradedAlgebra.{u, u} R)

/-- The degree-`n` part of `M ⊗_R C` is spanned by the pure tensors whose factors have degrees
adding up to `n`. -/
def absTensorGrading (n : ℤ) : Submodule R (M.M ⊗[R] C.A) :=
  Submodule.span R {x | ∃ (p q : ℤ) (a : M.M) (b : C.A),
    a ∈ M.grading p ∧ b ∈ C.grading q ∧ p + q = n ∧ x = a ⊗ₜ[R] b}

/-- Multiplication by `(-1)^p` on the degree-`p` part of `M`. -/
def absKoszulSign : M.M →ₗ[R] M.M :=
  (DirectSum.toModule R ℤ M.M fun p ↦ (p.negOnePow : ℤ) • (M.grading p).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- The signed tensor differential `d_M ⊗ 1 + (-1)^deg ⊗ d_C` on `M ⊗_R C`. -/
def absTensorDifferential : (M.M ⊗[R] C.A) →ₗ[R] (M.M ⊗[R] C.A) :=
  TensorProduct.map M.d LinearMap.id + TensorProduct.map (absKoszulSign M) C.d

/-- The Koszul sign acts on a homogeneous element of degree `p` by `(-1)^p`. -/
theorem absKoszulSign_apply_coe (p : ℤ) (a : M.grading p) :
    absKoszulSign M a = (p.negOnePow : ℤ) • (a : M.M) := by
  simp [absKoszulSign, DirectSum.toModule_lof]

/-- The signed tensor differential on a pure tensor `a ⊗ b` with `a` of degree `p`:
`d(a ⊗ b) = d a ⊗ b + (-1)^p a ⊗ d b`, the sign as an integer. -/
theorem absTensorDifferential_tmul (p : ℤ) (a : M.grading p) (b : C.A) :
    absTensorDifferential M C ((a : M.M) ⊗ₜ[R] b) =
      (M.d a ⊗ₜ[R] b : M.M ⊗[R] C.A) + (p.negOnePow : ℤ) • ((a : M.M) ⊗ₜ[R] C.d b) := by
  simp only [absTensorDifferential, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, absKoszulSign_apply_coe]
  simp only [← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul']

/-- `absTensorDifferential_tmul` with the sign `(-1)^p` acting as a unit of `ℤ`. -/
theorem absTensorDifferential_tmul' (p : ℤ) (a : M.grading p) (b : C.A) :
    absTensorDifferential M C ((a : M.M) ⊗ₜ[R] b) =
      (M.d a ⊗ₜ[R] b : M.M ⊗[R] C.A) + p.negOnePow • ((a : M.M) ⊗ₜ[R] C.d b) := by
  simpa only [Units.smul_def] using absTensorDifferential_tmul M C p a b

/-! ### The direct sum decomposition -/

/-- Regrouping the bigraded pieces of `M ⊗_R C` by their total degree. -/
def absFiberEquiv :
    (⨁ pq : ℤ × ℤ, M.grading pq.1 ⊗[R] C.grading pq.2) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        M.grading pq.val.1 ⊗[R] C.grading pq.val.2) := by
  let e₁ :
      (⨁ k : (n : ℤ) × {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        M.grading k.2.val.1 ⊗[R] C.grading k.2.val.2) ≃ₗ[R]
        (⨁ pq : ℤ × ℤ, M.grading pq.1 ⊗[R] C.grading pq.2) :=
    DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2))
  exact e₁.symm.trans (DirectSum.sigmaLcurryEquiv R
    (δ := fun (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) ↦
      M.grading pq.val.1 ⊗[R] C.grading pq.val.2))

/-- The bigraded pieces of `M ⊗_R C` of total degree `n`. -/
abbrev absTotalComponents (n : ℤ) : Type u :=
  ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}, M.grading pq.val.1 ⊗[R] C.grading pq.val.2

/-- The decomposition of `M ⊗_R C` into bigraded pieces, regrouped by total degree. -/
def absTotalEquiv :
    (M.M ⊗[R] C.A) ≃ₗ[R]
      (⨁ n : ℤ, ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
        M.grading pq.val.1 ⊗[R] C.grading pq.val.2) :=
  ((TensorProduct.congr (DirectSum.decomposeLinearEquiv M.grading)
    (DirectSum.decomposeLinearEquiv C.grading)).trans
    (TensorProduct.directSum R R (fun p ↦ M.grading p) (fun q ↦ C.grading q))).trans
      (absFiberEquiv M C)

/-- Regrouping by total degree sends the bigraded piece of index `(p, q)` to the summand of
total degree `p + q`. -/
theorem absFiberEquiv_lof (p q : ℤ) (x : M.grading p ⊗[R] C.grading q) :
    absFiberEquiv M C (DirectSum.lof R _ _ (p, q) x) =
      DirectSum.lof R _ _ (p + q) (DirectSum.lof R _ _ ⟨(p, q), rfl⟩ x) := by
  change DirectSum.sigmaFiberAddEquiv (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)
      (DirectSum.of (fun pq : ℤ × ℤ ↦ M.grading pq.1 ⊗[R] C.grading pq.2) (p, q) x) = _
  exact DirectSum.sigmaFiberAddEquiv_of
    (β := fun pq : ℤ × ℤ ↦ M.grading pq.1 ⊗[R] C.grading pq.2)
    (fun pq : ℤ × ℤ ↦ pq.1 + pq.2) (p, q) x

/-- The decomposition of `M ⊗_R C` sends a pure tensor of homogeneous elements of degrees `p`
and `q` to the corresponding bigraded piece in total degree `p + q`. -/
theorem absTotalEquiv_tmul (p q : ℤ) (a : M.grading p) (b : C.grading q) :
    absTotalEquiv M C ((a : M.M) ⊗ₜ[R] (b : C.A)) =
      DirectSum.lof R ℤ (absTotalComponents M C) (p + q)
        (DirectSum.lof R _
          (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = p + q} ↦
            M.grading pq.val.1 ⊗[R] C.grading pq.val.2)
          ⟨(p, q), rfl⟩ (a ⊗ₜ[R] b)) := by
  simp only [absTotalEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe]
  convert absFiberEquiv_lof M C p q (a ⊗ₜ[R] b) using 1
  exact congrArg (absFiberEquiv M C) (by
    simpa only [DirectSum.lof_eq_of] using
      (TensorProduct.directSum_lof_tmul_lof R R
        (M₁ := fun p ↦ M.grading p) (M₂ := fun q ↦ C.grading q) p a q b))

/-- The inclusion of the bigraded pieces of total degree `n` into `M ⊗_R C`. -/
def absFiberMap (n : ℤ) : absTotalComponents M C n →ₗ[R] (M.M ⊗[R] C.A) :=
  (absTotalEquiv M C).symm.toLinearMap ∘ₗ DirectSum.lof R ℤ (absTotalComponents M C) n

/-- The inclusion of the bigraded pieces sends a pure tensor to the corresponding pure tensor of
`M ⊗_R C`. -/
theorem absFiberMap_lof_tmul (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (a : M.grading pq.val.1) (b : C.grading pq.val.2) :
    absFiberMap M C n (DirectSum.lof R _ _ pq (a ⊗ₜ[R] b)) = ((a : M.M) ⊗ₜ[R] (b : C.A)) := by
  apply (absTotalEquiv M C).injective
  obtain ⟨⟨p, q⟩, h⟩ := pq
  subst n
  simpa [absFiberMap] using (absTotalEquiv_tmul M C p q a b).symm

/-- The bigraded pieces of total degree `n` land in the degree-`n` part of `M ⊗_R C`. -/
theorem absFiberMap_mem (n : ℤ) (x : absTotalComponents M C n) :
    absFiberMap M C n x ∈ absTensorGrading M C n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using (absTensorGrading M C n).add_mem hx hy
  | of pq x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa using (absTensorGrading M C n).add_mem hx hy
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (R := R), absFiberMap_lof_tmul]
      exact Submodule.subset_span
        ⟨pq.val.1, pq.val.2, (a : M.M), (b : C.A), a.property, b.property, pq.property, rfl⟩

/-- The degree-`n` part of `M ⊗_R C` is exactly the image of the bigraded pieces of total
degree `n`. -/
theorem absFiberMap_range_eq (n : ℤ) :
    LinearMap.range (absFiberMap M C n) = absTensorGrading M C n := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro x ⟨y, rfl⟩
    exact absFiberMap_mem M C n y
  · rintro x ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    exact ⟨DirectSum.lof R _ _ (⟨(p, q), hpq⟩ : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
      (⟨a, ha⟩ ⊗ₜ[R] ⟨b, hb⟩), absFiberMap_lof_tmul M C n ⟨(p, q), hpq⟩ ⟨a, ha⟩ ⟨b, hb⟩⟩

/-- The degree-`n` part of `M ⊗_R C` is the direct sum of the bigraded pieces of total
degree `n`. -/
def absComponentEquiv (n : ℤ) :
    absTotalComponents M C n ≃ₗ[R] absTensorGrading M C n := by
  have hinj : Function.Injective (absFiberMap M C n) := by
    intro x y h
    apply DirectSum.of_injective n
    simpa [absFiberMap, DirectSum.lof_eq_of] using congrArg (absTotalEquiv M C) h
  exact (LinearEquiv.ofInjective (absFiberMap M C n) hinj).trans
    (LinearEquiv.ofEq _ _ (absFiberMap_range_eq M C n))

/-- The identification of the bigraded pieces with the degree-`n` part is the inclusion
`absFiberMap` on underlying elements. -/
theorem absComponentEquiv_coe (n : ℤ) (x : absTotalComponents M C n) :
    ((absComponentEquiv M C n x : absTensorGrading M C n) : M.M ⊗[R] C.A) =
      absFiberMap M C n x := rfl

/-- The grading of `M ⊗_R C` is a direct sum decomposition. -/
def absGradingEquiv : (M.M ⊗[R] C.A) ≃ₗ[R] (⨁ n : ℤ, absTensorGrading M C n) :=
  (absTotalEquiv M C).trans (DirectSum.congrLinearEquiv (absComponentEquiv M C))

/-- The decomposition of `M ⊗_R C` sends an element of the degree-`n` part to its own summand. -/
theorem absGradingEquiv_coe (n : ℤ) (x : absTensorGrading M C n) :
    absGradingEquiv M C (x : M.M ⊗[R] C.A) = DirectSum.lof R _ _ n x := by
  obtain ⟨y, rfl⟩ := (absComponentEquiv M C n).surjective x
  suffices h : (DirectSum.congrLinearEquiv (absComponentEquiv M C))
        (DirectSum.lof R ℤ (absTotalComponents M C) n y) =
      DirectSum.lof R ℤ (fun i ↦ absTensorGrading M C i) n (absComponentEquiv M C n y) by
    simpa [absGradingEquiv, absComponentEquiv_coe, absFiberMap] using h
  change (DirectSum.lmap (fun i ↦ (absComponentEquiv M C i).toLinearMap))
    (DirectSum.lof R ℤ (absTotalComponents M C) n y) = _
  simp

/-- The inverse of the decomposition of `M ⊗_R C` is the sum of the inclusions of the graded
pieces. -/
theorem absGradingEquiv_symm_eq_coe :
    (absGradingEquiv M C).symm.toLinearMap =
      DirectSum.coeLinearMap (absTensorGrading M C) := by
  ext n x
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply]
  rw [DirectSum.coeLinearMap_lof]
  exact (LinearEquiv.symm_apply_eq _).mpr (absGradingEquiv_coe M C n x).symm

/-- The grading of `M ⊗_R C` by total degree, as a direct sum decomposition. -/
@[instance_reducible]
def absTotalDecomposition : DirectSum.Decomposition (absTensorGrading M C) := by
  apply DirectSum.Decomposition.ofLinearMap (absTensorGrading M C)
    (absGradingEquiv M C).toLinearMap
  · rw [← absGradingEquiv_symm_eq_coe]
    ext x
    simp
  · rw [← absGradingEquiv_symm_eq_coe]
    ext x
    simp

/-- A pure tensor of homogeneous elements of degrees `p` and `q` has degree `p + q`. -/
theorem absTmul_mem (p q : ℤ) (a : M.M) (b : C.A) (ha : a ∈ M.grading p) (hb : b ∈ C.grading q) :
    (a ⊗ₜ[R] b : M.M ⊗[R] C.A) ∈ absTensorGrading M C (p + q) :=
  Submodule.subset_span ⟨p, q, a, b, ha, hb, rfl, rfl⟩

/-- The signed tensor differential raises the degree by one. -/
theorem absTensorDifferential_mem (n : ℤ) (x : M.M ⊗[R] C.A)
    (hx : x ∈ absTensorGrading M C n) :
    absTensorDifferential M C x ∈ absTensorGrading M C (n + 1) := by
  refine (Submodule.span_le (p := (absTensorGrading M C (n + 1)).comap
    (absTensorDifferential M C))).2 ?_ hx
  rintro x ⟨p, q, a, b, ha, hb, hpq, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, show a = (⟨a, ha⟩ : M.grading p) from rfl,
    absTensorDifferential_tmul]
  apply Submodule.add_mem
  · convert absTmul_mem M C (p + 1) q (M.d a) b (M.d_mem p a ha) hb using 1
    congr 1
    omega
  · apply zsmul_mem
    convert absTmul_mem M C p (q + 1) a (C.d b) ha (C.d_mem q b hb) using 1
    congr 1
    omega

/-- The signed tensor differential squares to zero on a pure tensor with homogeneous first
factor. -/
theorem absTensorDifferential_sq_tmul (p : ℤ) (a : M.grading p) (b : C.A) :
    absTensorDifferential M C (absTensorDifferential M C ((a : M.M) ⊗ₜ[R] b)) = 0 := by
  have ha : M.d (a : M.M) ∈ M.grading (p + 1) := M.d_mem p a a.property
  have hM : M.d (M.d (a : M.M)) = 0 := by simpa using LinearMap.congr_fun M.d_comp_d (a : M.M)
  have hC : C.d (C.d b) = 0 := by simpa using LinearMap.congr_fun C.d_comp_d b
  rw [absTensorDifferential_tmul, map_add, map_zsmul,
    absTensorDifferential_tmul M C (p + 1) ⟨M.d a, ha⟩ b,
    absTensorDifferential_tmul M C p a (C.d b)]
  simp only [hM, hC, TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add,
    add_zero, smul_zero]
  rw [Int.negOnePow_succ]
  simpa only [Units.val_neg, neg_zsmul] using
    (neg_add_cancel ((p.negOnePow : ℤ) • ((M.d a : M.M) ⊗ₜ[R] C.d b : M.M ⊗[R] C.A)))

/-- The signed tensor differential squares to zero. -/
theorem absTensorDifferential_sq :
    absTensorDifferential M C ∘ₗ absTensorDifferential M C = 0 := by
  apply LinearMap.ext; intro x
  change absTensorDifferential M C (absTensorDifferential M C x) = 0
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a b =>
    induction a using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add a a' ha ha' => simp [TensorProduct.add_tmul, map_add, ha, ha']
    | homogeneous a => exact absTensorDifferential_sq_tmul M C _ a b

/-- The right `C`-action on `M ⊗_R C`, on the second factor. -/
@[instance_reducible]
def absTensorRightModule : Module (MulOpposite C.A) (M.M ⊗[R] C.A) :=
  (TensorProduct.comm R M.M C.A).toAddEquiv.module _

attribute [local instance] absTensorRightModule

/-- The scalars of `R` and the right `C`-action on `M ⊗_R C` form a scalar tower. -/
theorem absTensorRightScalarTower : IsScalarTower R (MulOpposite C.A) (M.M ⊗[R] C.A) :=
  (TensorProduct.comm R M.M C.A).isScalarTower _

attribute [local instance] absTensorRightScalarTower

/-- The right action of `b` on a pure tensor `x ⊗ y` is `x ⊗ (y * b)`. -/
theorem absTensor_smul_tmul (x : M.M) (y b : C.A) :
    MulOpposite.op b • (x ⊗ₜ[R] y) = x ⊗ₜ[R] (y * b) := by
  change (TensorProduct.comm R C.A M.M)
    (MulOpposite.op b • (TensorProduct.comm R M.M C.A) (x ⊗ₜ[R] y)) = _
  simp [TensorProduct.smul_tmul', MulOpposite.smul_eq_mul_unop]

/-- The right `C`-action on `M ⊗_R C` adds degrees. -/
theorem absTensor_smul_mem (n m : ℤ) (x : M.M ⊗[R] C.A) (b : C.A)
    (hx : x ∈ absTensorGrading M C n) (hb : b ∈ C.grading m) :
    MulOpposite.op b • x ∈ absTensorGrading M C (n + m) := by
  refine (Submodule.span_le (p := (absTensorGrading M C (n + m)).comap
    (DistribSMul.toLinearMap R _ (MulOpposite.op b)))).2 ?_ hx
  rintro z ⟨p, q, x, y, hxp, hy, rfl, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, DistribSMul.toLinearMap_apply,
    absTensor_smul_tmul]
  simpa only [add_assoc] using absTmul_mem M C p (q + m) x (y * b) hxp
    (SetLike.mul_mem_graded hy hb)

/-- The graded Leibniz rule for the right `C`-action on `M ⊗_R C`:
`d(z · b) = d z · b + (-1)^n z · d b` for `z` of degree `n`. -/
theorem absTensor_leibniz (n m : ℤ) (z : M.M ⊗[R] C.A) (b : C.A)
    (hz : z ∈ absTensorGrading M C n) (hb : b ∈ C.grading m) :
    absTensorDifferential M C (MulOpposite.op b • z) =
      MulOpposite.op b • absTensorDifferential M C z +
        (n.negOnePow : ℤ) • (MulOpposite.op (C.d b) • z) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, x, y, hx, hy, rfl, rfl⟩ := hz
    rw [absTensor_smul_tmul, show x = (⟨x, hx⟩ : M.grading p) from rfl,
      absTensorDifferential_tmul, absTensorDifferential_tmul, smul_add,
      smul_comm (MulOpposite.op b) (p.negOnePow : ℤ), absTensor_smul_tmul, absTensor_smul_tmul,
      absTensor_smul_tmul, C.leibniz q m y b hy hb]
    simp only [TensorProduct.tmul_add, ← Int.cast_smul_eq_zsmul R, TensorProduct.tmul_smul,
      smul_add, smul_smul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
    abel
  | zero => simp
  | add x y hx hy ihx ihy => simp only [smul_add, map_add, ihx, ihy]; abel
  | smul r x hx ih =>
    simp only [smul_comm (MulOpposite.op b) r, smul_comm (MulOpposite.op (C.d b)) r,
      map_smul, ih, smul_add, smul_comm (n.negOnePow : ℤ) r]

attribute [local instance] absTotalDecomposition

/-- `M ⊗_R C`: a right differential graded `C`-module `M` over `B`, tensored over the base ring
with a differential graded `R`-algebra `C`, is a right differential graded `C`-module, with `C`
acting on the second factor and with the signed tensor differential. -/
@[reducible]
def absoluteTensor : DifferentialGradedModule.{u, u, u} C where
  M := M.M ⊗[R] C.A
  grading := absTensorGrading M C
  smul_mem := absTensor_smul_mem M C
  d := absTensorDifferential M C
  d_comp_d := absTensorDifferential_sq M C
  d_mem := absTensorDifferential_mem M C
  leibniz := absTensor_leibniz M C

end DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {B : DifferentialGradedAlgebra.{u, u} R}

/-- The right action of `B` on a right differential graded `B`-module, as a bilinear map. -/
def rightActionBilinear (M : DifferentialGradedModule.{u, u, u} B) :
    M.M →ₗ[R] B.A →ₗ[R] M.M where
  toFun x :=
    { toFun := fun b => MulOpposite.op b • x
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_assoc] }
  map_add' := by intros; ext; simp [smul_add]
  map_smul' := by
    intro r x; ext b
    exact smul_comm (MulOpposite.op b) r x

/-- `rightActionBilinear M x b` is the right action `x · b`. -/
@[simp] theorem rightActionBilinear_apply (M : DifferentialGradedModule.{u, u, u} B)
    (x : M.M) (b : B.A) : rightActionBilinear M x b = MulOpposite.op b • x := rfl

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance] DifferentialGradedModule.absTensorRightModule
  DifferentialGradedModule.absTensorRightScalarTower
  DifferentialGradedModule.absTotalDecomposition

attribute [local instance 10000] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal

attribute [local implicit_reducible] DifferentialGradedModule.toCochainComplex
  DifferentialGradedModule.absTensorGrading

variable {R : Type u} [CommRing R] (B C : DifferentialGradedAlgebra.{u, u} R)

/-- `(x, b ⊗ c) ↦ (x · b) ⊗ c`, the bilinear map that undoes the balancing over `B`. -/
def absUnbalance (M : DifferentialGradedModule.{u, u, u} B) :
    M.M →ₗ[R] (B.grading ᵍ⊗[R] C.grading) →ₗ[R] (M.M ⊗[R] C.A) :=
  ((TensorProduct.mk R M.M (B.A ⊗[R] C.A)).compr₂
    ((TensorProduct.map (TensorProduct.lift (rightActionBilinear M)) LinearMap.id).comp
      (TensorProduct.assoc R M.M B.A C.A).symm.toLinearMap)).compl₂
        (GradedTensorProduct.of R B.grading C.grading).symm.toLinearMap

/-- `absUnbalance` sends `x` and `b ⊗ c` to `(x · b) ⊗ c`. -/
theorem absUnbalance_tmul (M : DifferentialGradedModule.{u, u, u} B) (x : M.M) (b : B.A)
    (c : C.A) :
    absUnbalance B C M x ((b ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading)) =
      (MulOpposite.op b • x) ⊗ₜ[R] c := by
  simp [absUnbalance, GradedTensorProduct.tmul]

/-- `absUnbalance` adds degrees. -/
theorem absUnbalance_mem (M : DifferentialGradedModule.{u, u, u} B) (p q : ℤ) (x : M.grading p)
    (y : (baseChangeBimodule B C).rightModule.grading q) :
    absUnbalance B C M (x : M.M) (y : (baseChangeBimodule B C).rightModule.M) ∈
      absTensorGrading M C (p + q) := by
  refine tensorProductGrading_induction B C q (motive := fun z =>
      absUnbalance B C M (x : M.M) z ∈ absTensorGrading M C (p + q))
    (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun z w hz hw => by rw [map_add]; exact Submodule.add_mem _ hz hw)
    (fun r z hz => by rw [map_smul]; exact Submodule.smul_mem _ r hz) ?_ y.1 y.2
  intro i j b c hb hc hij
  rw [absUnbalance_tmul]
  have h := absTmul_mem M C (p + i) j (MulOpposite.op b • (x : M.M)) c
    (M.smul_mem p i _ _ x.property hb) hc
  rwa [show p + i + j = p + q by omega] at h

/-- `absUnbalance` is right `C`-linear in its second argument. -/
theorem absUnbalance_smul (M : DifferentialGradedModule.{u, u, u} B) (x : M.M)
    (y : B.grading ᵍ⊗[R] C.grading) (c : C.A) :
    absUnbalance B C M x (y * ((1 : B.A) ᵍ⊗ₜ[R] c)) =
      MulOpposite.op c • absUnbalance B C M x y := by
  induction y using gradedTensor_induction with
  | add z w hz hw => rw [add_mul, map_add, hz, hw, map_add, smul_add]
  | tmul b c₀ =>
    rw [tmul_mul_one_tmul, absUnbalance_tmul, absUnbalance_tmul, absTensor_smul_tmul]

/-- `absUnbalance` is balanced over `B`: `(x · a, y)` and `(x, (a ⊗ 1) y)` have the same image. -/
theorem absUnbalance_balance (M : DifferentialGradedModule.{u, u, u} B) (x : M.M) (a : B.A)
    (y : B.grading ᵍ⊗[R] C.grading) :
    absUnbalance B C M (MulOpposite.op a • x) y =
      absUnbalance B C M x ((a ᵍ⊗ₜ[R] (1 : C.A)) * y) := by
  induction y using gradedTensor_induction with
  | add z w hz hw => rw [map_add, hz, hw, mul_add, map_add]
  | tmul b c =>
    rw [absUnbalance_tmul, tmul_one_mul_tmul, absUnbalance_tmul, MulOpposite.op_mul, mul_smul]

/-- `absUnbalance` satisfies the graded Leibniz rule, for `x` homogeneous of degree `p`. -/
theorem absUnbalance_d (M : DifferentialGradedModule.{u, u, u} B) (p : ℤ) (x : M.grading p)
    (y : B.grading ᵍ⊗[R] C.grading) :
    absTensorDifferential M C (absUnbalance B C M (x : M.M) y) =
      absUnbalance B C M (M.d x) y +
        (p.negOnePow : ℤ) • absUnbalance B C M (x : M.M) (tensorProductDifferential B C y) := by
  induction y using gradedTensor_induction with
  | add z w hz hw =>
    rw [map_add, map_add, map_add, map_add, map_add, hz, hw, smul_add]
    abel
  | tmul b c =>
    induction b using DirectSum.Decomposition.inductionOn B.grading with
    | zero => simp [GradedTensorProduct.tmul]
    | add b b' hb hb' =>
      rw [tmul_add_left, map_add, map_add, map_add, map_add, map_add, hb, hb', smul_add]
      abel
    | @homogeneous i b =>
      rw [absUnbalance_tmul, tensorProductDifferential_tmul_of_mem i (b : B.A) b.property c,
        map_add, map_zsmul, absUnbalance_tmul, absUnbalance_tmul,
        show MulOpposite.op (b : B.A) • (x : M.M) =
          (⟨_, M.smul_mem p i _ _ x.property b.property⟩ : M.grading (p + i)) from rfl,
        absTensorDifferential_tmul, M.leibniz p i _ _ x.property b.property]
      simp only [TensorProduct.add_tmul, ← Int.cast_smul_eq_zsmul R, TensorProduct.smul_tmul',
        smul_add, smul_smul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
      abel

/-- The identification `M ⊗_B {}_B(B ⊗_R C)_C = M ⊗_R C`, as a balanced bilinear map:
`(x, b ⊗ c) ↦ (x · b) ⊗ c`. -/
def absUnbalanceBalanced (M : DifferentialGradedModule.{u, u, u} B) :
    Bimodule.BalancedBilinearMap M (baseChangeBimodule B C) (absoluteTensor M C) where
  toLinearMap := absUnbalance B C M
  map_grading p q x y := absUnbalance_mem B C M p q x y
  map_d p x y := absUnbalance_d B C M p x y
  balance p q n x y a := by
    rw [baseChangeBimodule_leftAction]
    exact absUnbalance_balance B C M x.1 a.1 y.1
  map_right x y c := by
    rw [baseChangeBimodule_op_smul]
    exact absUnbalance_smul B C M x y c

/-! ### The identification of the relative with the absolute tensor product -/

/-- The relative tensor product `M ⊗_B {}_B(B ⊗_R C)_C`, as a right differential graded
`C`-module. -/
abbrev absRelativeTensor (M : DifferentialGradedModule.{u, u, u} B) :
    DifferentialGradedModule.{u, u, u} C :=
  Bimodule.tensorObj (baseChangeBimodule B C) M

/-- The universal pure tensors into `M ⊗_B {}_B(B ⊗_R C)_C`. -/
abbrev absRelativePure (M : DifferentialGradedModule.{u, u, u} B) :
    Bimodule.BalancedBilinearMap M (baseChangeBimodule B C) (absRelativeTensor B C M) :=
  Bimodule.tensorPure (baseChangeBimodule B C) M

/-- The universal pure tensors `x ⊗ y`, with the second argument read in the graded tensor
product `B ⊗_R C` itself rather than through the bimodule structure. -/
def absRelativePureBilinear (M : DifferentialGradedModule.{u, u, u} B) :
    M.M →ₗ[R] (B.grading ᵍ⊗[R] C.grading) →ₗ[R] (absRelativeTensor B C M).M :=
  (absRelativePure B C M).toLinearMap

/-- The pure tensors are right `C`-linear in the second variable. -/
theorem absRelativePureBilinear_mul_one_tmul (M : DifferentialGradedModule.{u, u, u} B)
    (x : M.M) (y : B.grading ᵍ⊗[R] C.grading) (c : C.A) :
    absRelativePureBilinear B C M x
        (y * (((1 : B.A) ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading))) =
      MulOpposite.op c • absRelativePureBilinear B C M x y :=
  (absRelativePure B C M).map_right x y c

/-- The pure tensors add degrees. -/
theorem absRelativePureBilinear_mem (M : DifferentialGradedModule.{u, u, u} B) (p q : ℤ)
    (x : M.M) (hx : x ∈ M.grading p) (y : B.grading ᵍ⊗[R] C.grading)
    (hy : y ∈ tensorProductGrading B C q) :
    absRelativePureBilinear B C M x y ∈ (absRelativeTensor B C M).grading (p + q) :=
  (absRelativePure B C M).map_grading p q ⟨x, hx⟩ ⟨y, hy⟩

/-- The pure tensors satisfy the graded Leibniz rule. -/
theorem absRelativePureBilinear_d (M : DifferentialGradedModule.{u, u, u} B) (p : ℤ)
    (x : M.grading p) (y : B.grading ᵍ⊗[R] C.grading) :
    (absRelativeTensor B C M).d (absRelativePureBilinear B C M (x : M.M) y) =
      absRelativePureBilinear B C M (M.d x) y +
        (p.negOnePow : ℤ) •
          absRelativePureBilinear B C M (x : M.M) (tensorProductDifferential B C y) :=
  (absRelativePure B C M).map_d p x y

/-- The pure tensors are balanced over `B`, for homogeneous arguments. -/
theorem absRelativePureBilinear_balance_of_mem (M : DifferentialGradedModule.{u, u, u} B)
    (p q n : ℤ) (x : M.M) (hx : x ∈ M.grading p) (y : B.grading ᵍ⊗[R] C.grading)
    (hy : y ∈ tensorProductGrading B C q) (b : B.grading n) :
    absRelativePureBilinear B C M (MulOpposite.op (b : B.A) • x) y =
      absRelativePureBilinear B C M x
        ((((b : B.A) ᵍ⊗ₜ[R] (1 : C.A)) : B.grading ᵍ⊗[R] C.grading) * y) := by
  have h := (absRelativePure B C M).balance p q n ⟨x, hx⟩ ⟨y, hy⟩ b
  rw [baseChangeBimodule_leftAction] at h
  exact h

/-- The pure tensors are balanced over `B`: moving `b` from the right action on `M` to the left
action on `B ⊗_R C` does not change them. -/
theorem absRelativePureBilinear_balance (M : DifferentialGradedModule.{u, u, u} B) (b : B.A)
    (x : M.M) (y : B.grading ᵍ⊗[R] C.grading) :
    absRelativePureBilinear B C M (MulOpposite.op b • x) y =
      absRelativePureBilinear B C M x
        (((b ᵍ⊗ₜ[R] (1 : C.A)) : B.grading ᵍ⊗[R] C.grading) * y) := by
  have := totalDecomposition B C
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero => simp [GradedTensorProduct.tmul]
  | add b b' hb hb' =>
    simp only [MulOpposite.op_add, add_smul, map_add, LinearMap.add_apply, hb, hb',
      tmul_add_left, add_mul]
  | @homogeneous n b =>
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x x' hx hx' => simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
    | @homogeneous p x =>
      induction y using DirectSum.Decomposition.inductionOn (tensorProductGrading B C) with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
      | @homogeneous q y =>
        exact absRelativePureBilinear_balance_of_mem B C M p q n x.1 x.2 y.1 y.2 b

/-- `x ⊗ c ↦ x ⊗ (1 ⊗ c)`, the inverse of the identification, as a linear map. -/
def absBalanceInverseLinear (M : DifferentialGradedModule.{u, u, u} B) :
    (M.M ⊗[R] C.A) →ₗ[R] (absRelativeTensor B C M).M :=
  TensorProduct.lift ((absRelativePureBilinear B C M).compl₂
    (GradedTensorProduct.includeRight B.grading C.grading).toLinearMap)

/-- The inverse of the identification sends `x ⊗ c` to the pure tensor `x ⊗ (1 ⊗ c)`. -/
theorem absBalanceInverseLinear_tmul (M : DifferentialGradedModule.{u, u, u} B) (x : M.M)
    (c : C.A) :
    absBalanceInverseLinear B C M (x ⊗ₜ[R] c) =
      absRelativePureBilinear B C M x
        (((1 : B.A) ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading)) := rfl

/-- The inverse of the identification, as a homomorphism of differential graded `C`-modules. -/
def absBalanceInverse (M : DifferentialGradedModule.{u, u, u} B) :
    absoluteTensor M C ⟶ absRelativeTensor B C M where
  toFun := absBalanceInverseLinear B C M
  map_smul z c := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul x a =>
      rw [absTensor_smul_tmul, absBalanceInverseLinear_tmul, absBalanceInverseLinear_tmul,
        ← absRelativePureBilinear_mul_one_tmul, tmul_mul_one_tmul B C 1 a c]
  map_grading n z hz := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, x, c, hx, hc, rfl, rfl⟩ := hz
      rw [absBalanceInverseLinear_tmul]
      exact absRelativePureBilinear_mem B C M p q x hx _ (one_tmul_mem_grading B C q c hc)
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  map_d := by
    apply LinearMap.ext; intro z
    change absBalanceInverseLinear B C M (absTensorDifferential M C z) =
      (absRelativeTensor B C M).d (absBalanceInverseLinear B C M z)
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c =>
      induction x using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | @homogeneous p x =>
        rw [absTensorDifferential_tmul, map_add, map_zsmul, absBalanceInverseLinear_tmul,
          absBalanceInverseLinear_tmul, absBalanceInverseLinear_tmul,
          absRelativePureBilinear_d B C M p x
            (((1 : B.A) ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading)),
          tensorProductDifferential_one_tmul B C c]

/-- The identification, as a homomorphism out of the relative tensor product: the unique
homomorphism of differential graded `C`-modules sending `x ⊗ (b ⊗ c)` to `(x · b) ⊗ c`. -/
def absBalanceForward (M : DifferentialGradedModule.{u, u, u} B) :
    absRelativeTensor B C M ⟶ absoluteTensor M C :=
  ((Bimodule.tensorDGFunctor (baseChangeBimodule B C)).universal M (absoluteTensor M C)
    (absUnbalanceBalanced B C M)).choose

/-- The identification sends the pure tensor `x ⊗ y` to `absUnbalance x y`. -/
theorem absBalanceForward_pure (M : DifferentialGradedModule.{u, u, u} B) (x : M.M)
    (y : B.grading ᵍ⊗[R] C.grading) :
    (absBalanceForward B C M).toFun (absRelativePureBilinear B C M x y) =
      absUnbalance B C M x y :=
  ((Bimodule.tensorDGFunctor (baseChangeBimodule B C)).universal M (absoluteTensor M C)
    (absUnbalanceBalanced B C M)).choose_spec.1 x y

/-- The inverse undoes the identification on every pure tensor. -/
theorem absBalanceInverse_unbalance (M : DifferentialGradedModule.{u, u, u} B) (x : M.M)
    (y : B.grading ᵍ⊗[R] C.grading) :
    absBalanceInverseLinear B C M (absUnbalance B C M x y) =
      absRelativePureBilinear B C M x y := by
  induction y using gradedTensor_induction with
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  | tmul b c =>
    rw [absUnbalance_tmul, absBalanceInverseLinear_tmul, absRelativePureBilinear_balance,
      tmul_one_mul_tmul B C b 1 c, mul_one]

/-- **The identification `M ⊗_B {}_B(B ⊗_R C)_C = M ⊗_R C`.** The relative tensor product of a
right differential graded `B`-module with the base-change bimodule `{}_B(B ⊗_R C)_C` is the
absolute tensor product `M ⊗_R C`, as right differential graded `C`-modules. -/
def absBalanceIso (M : DifferentialGradedModule.{u, u, u} B) :
    absRelativeTensor B C M ≅ absoluteTensor M C where
  hom := absBalanceForward B C M
  inv := absBalanceInverse B C M
  hom_inv_id := by
    refine Bimodule.tensorObj_hom_ext (baseChangeBimodule B C) M _ _ fun x y => ?_
    exact (congrArg (absBalanceInverse B C M).toFun (absBalanceForward_pure B C M x y)).trans
      (absBalanceInverse_unbalance B C M x y)
  inv_hom_id := by
    apply DifferentialGradedModule.Hom.ext
    apply TensorProduct.ext'
    intro x c
    change (absBalanceForward B C M).toFun (absBalanceInverseLinear B C M (x ⊗ₜ[R] c)) =
      x ⊗ₜ[R] c
    rw [absBalanceInverseLinear_tmul, absBalanceForward_pure, absUnbalance_tmul]
    simp


/-! ### The identification of the underlying complexes -/

/-- The total complex `Tot(M ⊗_R C)` of the tensor product double complex of the complexes
underlying `M` and `C`. -/
abbrev absTensorComplex (M : DifferentialGradedModule.{u, u, u} B) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.tensorObj M.toCochainComplex (regularModule C).toCochainComplex

/-- The bigraded summand `M^p ⊗_R C^q`, mapped into the degree-`n` part of `M ⊗_R C`. -/
def absTotalForwardSummand (M : DifferentialGradedModule.{u, u, u} B) (p q : ℤ) {n : ℤ}
    (h : p + q = n) :
    ModuleCat.of R (M.grading p ⊗[R] C.grading q) ⟶
      (absoluteTensor M C).toCochainComplex.X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict _
    (TensorProduct.map (M.grading p).subtype (C.grading q).subtype) (by
      intro z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
      | tmul x y =>
        subst n
        exact absTmul_mem M C p q x y x.property y.property)

/-- The inclusion of the bigraded summand `M^p ⊗_R C^q` into the total complex. -/
abbrev absTensorInclusion (M : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ)
    (h : p + q = n) :
    ModuleCat.of R (M.grading p ⊗[R] C.grading q) ⟶ (absTensorComplex B C M).X n :=
  HomologicalComplex.ιTensorObj M.toCochainComplex (regularModule C).toCochainComplex p q n h

/-- The degree-`n` component of the map from the total complex to the complex underlying
`M ⊗_R C`. -/
abbrev absTotalForward (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    (absTensorComplex B C M).X n ⟶ (absoluteTensor M C).toCochainComplex.X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => absTotalForwardSummand B C M p q h)

/-- The map from the total complex sends the image of `x ⊗ y` under the inclusion of the
summand `M^p ⊗_R C^q` to the pure tensor `x ⊗ y`. -/
theorem absTotalForward_ι (M : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ) (h : p + q = n)
    (x : M.grading p) (y : C.grading q) :
    (absTotalForward B C M n) (absTensorInclusion B C M p q n h (x ⊗ₜ[R] y)) =
      ⟨(x : M.M) ⊗ₜ[R] (y : C.A), by
        subst n; exact absTmul_mem M C p q x y x.property y.property⟩ := by
  have h' := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := M.toCochainComplex) (K₂ := (regularModule C).toCochainComplex)
    (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
    (fun p q h => absTotalForwardSummand B C M p q h) p q h
  exact congrArg (fun f => f (x ⊗ₜ[R] y)) h'

/-- The map from the bigraded pieces of total degree `n` into the total complex. -/
def absTotalBackwardLinear (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    absTotalComponents M C n →ₗ[R] ((absTensorComplex B C M).X n) :=
  DirectSum.toModule R _ _ (fun pq =>
    (absTensorInclusion B C M pq.val.1 pq.val.2 n pq.property).hom)

/-- The map from the bigraded pieces into the total complex is, on the piece of index `pq`, the
inclusion of that summand. -/
theorem absTotalBackwardLinear_lof (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ)
    (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) (z : M.grading pq.val.1 ⊗[R] C.grading pq.val.2) :
    absTotalBackwardLinear B C M n (DirectSum.lof R _ _ pq z) =
      absTensorInclusion B C M pq.val.1 pq.val.2 n pq.property z := by
  simp only [absTotalBackwardLinear, DirectSum.toModule_lof]

/-- The degree-`n` component of the map from the complex underlying `M ⊗_R C` to the total
complex: the bigraded decomposition of the degree-`n` part, followed by the inclusions. -/
def absTotalBackward (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    (absoluteTensor M C).toCochainComplex.X n ⟶ (absTensorComplex B C M).X n :=
  ModuleCat.ofHom (absTotalBackwardLinear B C M n ∘ₗ (absComponentEquiv M C n).symm.toLinearMap)

/-- The map into the total complex sends the pure tensor `x ⊗ y` of homogeneous elements to its
image under the inclusion of the summand `M^p ⊗_R C^q`. -/
theorem absTotalBackward_pure (M : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ)
    (h : p + q = n) (x : M.grading p) (y : C.grading q) :
    (absTotalBackward B C M n)
        ⟨(x : M.M) ⊗ₜ[R] (y : C.A), by
          subst n; exact absTmul_mem M C p q x y x.property y.property⟩ =
      absTensorInclusion B C M p q n h (x ⊗ₜ[R] y) := by
  have he : (absComponentEquiv M C n).symm
        ⟨(x : M.M) ⊗ₜ[R] (y : C.A), by
          subst n; exact absTmul_mem M C p q x y x.property y.property⟩ =
      DirectSum.lof R {pq : ℤ × ℤ // pq.1 + pq.2 = n}
        (fun pq => M.grading pq.val.1 ⊗[R] C.grading pq.val.2) ⟨(p, q), h⟩ (x ⊗ₜ[R] y) := by
    apply (absComponentEquiv M C n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (absFiberMap_lof_tmul M C n ⟨(p, q), h⟩ x y).symm
  change absTotalBackwardLinear B C M n ((absComponentEquiv M C n).symm _) = _
  rw [he, absTotalBackwardLinear_lof]

/-- Composing the map from the bigraded pieces into the total complex with the map out of it
gives the identification of the bigraded pieces with the degree-`n` part. -/
theorem absTotalForward_comp_backwardLinear (M : DifferentialGradedModule.{u, u, u} B)
    (n : ℤ) :
    (absTotalForward B C M n).hom ∘ₗ absTotalBackwardLinear B C M n =
      (absComponentEquiv M C n).toLinearMap := by
  refine DirectSum.linearMap_ext R fun pq => TensorProduct.ext' fun x y => ?_
  change (absTotalForward B C M n).hom (absTotalBackwardLinear B C M n
    (DirectSum.lof R _ _ pq (x ⊗ₜ[R] y))) = absComponentEquiv M C n (DirectSum.lof R _ _ pq _)
  rw [absTotalBackwardLinear_lof]
  apply Subtype.ext
  rw [absComponentEquiv_coe, absFiberMap_lof_tmul]
  exact congrArg Subtype.val (absTotalForward_ι B C M pq.val.1 pq.val.2 n pq.property x y)

/-- The map into the total complex is a right inverse of the map out of it, in degree `n`. -/
theorem absTotalBackward_forward (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    absTotalBackward B C M n ≫ absTotalForward B C M n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  change (absTotalForward B C M n).hom ∘ₗ
      (absTotalBackwardLinear B C M n ∘ₗ (absComponentEquiv M C n).symm.toLinearMap) =
    LinearMap.id
  rw [← LinearMap.comp_assoc, absTotalForward_comp_backwardLinear]
  exact LinearMap.ext (absComponentEquiv M C n).apply_symm_apply

/-- The map into the total complex is a left inverse of the map out of it, in degree `n`. -/
theorem absTotalForward_backward (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    absTotalForward B C M n ≫ absTotalBackward B C M n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (absTotalBackward B C M n) ((absTotalForward B C M n)
    (absTensorInclusion B C M p q n h (x ⊗ₜ[R] y))) = _
  rw [absTotalForward_ι, absTotalBackward_pure]
  rfl

/-- The maps out of the total complex commute with the differentials. -/
theorem absTotalForward_comm (M : DifferentialGradedModule.{u, u, u} B) (n m : ℤ)
    (h : n + 1 = m) :
    absTotalForward B C M n ≫ (absoluteTensor M C).toCochainComplex.d n m =
      (absTensorComplex B C M).d n m ≫ absTotalForward B C M m := by
  subst m
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  have ha : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p + 1, q) = n + 1 := by
    change p + q = n at hpq
    change p + 1 + q = n + 1
    omega
  have hb : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q + 1) = n + 1 := by
    change p + q = n at hpq
    change p + (q + 1) = n + 1
    omega
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq (K₁ := M.toCochainComplex)
      (K₂ := (regularModule C).toCochainComplex)
      (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
      h₁ q (n + 1) ha,
    HomologicalComplex.mapBifunctor.d₂_eq (K₁ := M.toCochainComplex)
      (K₂ := (regularModule C).toCochainComplex)
      (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
      p h₂ (n + 1) hb]
  simp only [absTotalForward, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [ComplexShape.ε₁, ComplexShape.ε₂]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change C.grading q at y
  apply Subtype.ext
  dsimp [absTotalForwardSummand]
  simp only [DifferentialGradedModule.toCochainComplex_d]
  dsimp
  simp only [one_smul]
  exact absTensorDifferential_tmul' M C p x y

/-- **The total complex of `M ⊗_R C` is the complex underlying the differential graded module
`M ⊗_R C`.** In each degree this is the decomposition of the degree-`n` part of `M ⊗_R C` into
its bigraded pieces, and the two differentials agree because both carry the Koszul sign. -/
def absTotalIso (M : DifferentialGradedModule.{u, u, u} B) :
    absTensorComplex B C M ≅ (absoluteTensor M C).toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ⟨absTotalForward B C M n, absTotalBackward B C M n,
      absTotalForward_backward B C M n, absTotalBackward_forward B C M n⟩)
    (fun n m h => absTotalForward_comm B C M n m h)


/-! ### Tensoring with the base-change bimodule is tensoring with `C` over `R` -/

/-- The ordinary tensor functor with the base-change bimodule, on a pure tensor. -/
theorem absRelativePureBilinear_map {P M : DifferentialGradedModule.{u, u, u} B} (f : P ⟶ M)
    (x : P.M) (y : B.grading ᵍ⊗[R] C.grading) :
    ((Bimodule.tensorCompFunctor (baseChangeBimodule B C)).map f).toFun
        (absRelativePureBilinear B C P x y) =
      absRelativePureBilinear B C M (f.toFun x) y :=
  Bimodule.tensorCompFunctor_map_pure (baseChangeBimodule B C) f x y

/-- The complex underlying `M ⊗_B {}_B(B ⊗_R C)_C` is the total complex `Tot(M ⊗_R C)`. -/
def absBalancedComplexIso (M : DifferentialGradedModule.{u, u, u} B) :
    absTensorComplex B C M ≅ (absRelativeTensor B C M).toCochainComplex :=
  absTotalIso B C M ≪≫
    (forgetToCochainComplex C).mapIso (absBalanceIso B C M).symm

/-- The identification of the total complex with the complex underlying
`M ⊗_B {}_B(B ⊗_R C)_C` sends the image of `x ⊗ y` to the pure tensor `x ⊗ (1 ⊗ y)`. -/
theorem absBalancedComplexIso_pure (M : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ)
    (h : p + q = n) (x : M.grading p) (y : C.grading q) :
    ((absBalancedComplexIso B C M).hom.f n
        (absTensorInclusion B C M p q n h (x ⊗ₜ[R] y)) :
      (absRelativeTensor B C M).grading n).val =
      absRelativePureBilinear B C M (x : M.M)
        (((1 : B.A) ᵍ⊗ₜ[R] (y : C.A) : B.grading ᵍ⊗[R] C.grading)) := by
  change (absBalanceInverse B C M).toFun
    (show (absoluteTensor M C).grading n from
      absTotalForward B C M n (absTensorInclusion B C M p q n h (x ⊗ₜ[R] y))).val = _
  rw [absTotalForward_ι]
  rfl

/-- Tensoring a homomorphism of differential graded `B`-modules with `C` over `R`, on total
complexes. -/
def absRightTensorMap {P M : DifferentialGradedModule.{u, u, u} B} (f : P ⟶ M) :
    absTensorComplex B C P ⟶ absTensorComplex B C M :=
  HomologicalComplex.tensorHom ((forgetToCochainComplex B).map f) (𝟙 _)

/-- The identification of the total complex with the complex underlying
`M ⊗_B {}_B(B ⊗_R C)_C` is natural in `M`. -/
theorem absBalancedComplexIso_naturality {P M : DifferentialGradedModule.{u, u, u} B}
    (f : P ⟶ M) :
    absRightTensorMap B C f ≫ (absBalancedComplexIso B C M).hom =
      (absBalancedComplexIso B C P).hom ≫ (forgetToCochainComplex C).map
        ((Bimodule.tensorCompFunctor (baseChangeBimodule B C)).map f) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change HomologicalComplex.ιTensorObj _ _ p q n h ≫
      (HomologicalComplex.tensorHom ((forgetToCochainComplex B).map f) (𝟙 _)).f n ≫ _ = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  apply Subtype.ext
  change ((absBalancedComplexIso B C M).hom.f n
      (absTensorInclusion B C M p q n h (((forgetToCochainComplex B).map f).f p x ⊗ₜ[R] y)) :
        (absRelativeTensor B C M).grading n).val =
    ((Bimodule.tensorCompFunctor (baseChangeBimodule B C)).map f).toFun
      ((absBalancedComplexIso B C P).hom.f n
        (absTensorInclusion B C P p q n h (x ⊗ₜ[R] y)) :
          (absRelativeTensor B C P).grading n).val
  rw [absBalancedComplexIso_pure, absBalancedComplexIso_pure, absRelativePureBilinear_map]
  rfl

/-- When `C` is K-flat as a complex of `R`-modules, tensoring with `C` over `R` carries a
quasi-isomorphism of the underlying complexes to a quasi-isomorphism of total complexes
(Stacks Tag 06Y0). -/
theorem absRightTensorMap_quasiIso
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex)
    {P M : DifferentialGradedModule.{u, u, u} B} (f : P ⟶ M)
    (hf : QuasiIso ((forgetToCochainComplex B).map f)) :
    QuasiIso (absRightTensorMap B C f) := by
  have hf' := (HomotopyCategory.quotient_map_mem_quasiIso_iff
    ((forgetToCochainComplex B).map f)).2 hf
  have h := (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso
    (regularModule C).toCochainComplex hC) _ hf'
  change HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright _).map ((forgetToCochainComplex B).map f)) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

/-- **Tensoring with `{}_B(B ⊗_R C)_C` carries quasi-isomorphisms to quasi-isomorphisms when `C`
is K-flat as a complex of `R`-modules.** On underlying complexes, tensoring with the base-change
bimodule over `B` is tensoring with `C` over `R`, and a K-flat complex preserves
quasi-isomorphisms by Stacks Tag 06Y0. -/
theorem tensorPreservesQuasiIso_baseChangeBimodule
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex) :
    Bimodule.TensorPreservesQuasiIso (baseChangeBimodule B C) := by
  intro P M f hf
  have := absRightTensorMap_quasiIso B C hC f hf
  have h1 : QuasiIso ((absBalancedComplexIso B C P).hom ≫ (forgetToCochainComplex C).map
      ((Bimodule.tensorCompFunctor (baseChangeBimodule B C)).map f)) := by
    rw [← absBalancedComplexIso_naturality B C f]
    exact (quasiIso_iff_comp_right (absRightTensorMap B C f)
      (absBalancedComplexIso B C M).hom).2 inferInstance
  exact (quasiIso_iff_comp_left (absBalancedComplexIso B C P).hom _).1 h1

end DifferentialGraded

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- **Stacks Tag 09S4, first conclusion.** *"Let `R` be a ring. Let `(A, d)`, `(B, d)`, and
`(C, d)` be differential graded `R`-algebras. If `C` is K-flat as a complex of `R`-modules, then
(0BZ4) is an isomorphism."*

The map of Tag 0BZ4 is
`DifferentialGraded.derivedTensorBaseChangeComparison`, the canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` in `D(C, d)`, and K-flatness is
`CochainComplex.KFlat` (Tag 06XZ) of the complex of `R`-modules underlying `C`.

The source's argument is followed: on underlying complexes, tensoring over `B` with
`{}_B(B ⊗_R C)_C` is tensoring over `R` with `C`, so by Tag 06Y0 it carries quasi-isomorphisms to
quasi-isomorphisms; hence the plain tensor functor already computes the derived one and the
comparison of Tag 09LS is invertible everywhere, in particular at `(A ⊗_R B)_B`, which by
`DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_iff` is the assertion. -/
@[stacks 09S4 "the canonical map (0BZ4) is an isomorphism"]
theorem isIso_derivedTensorBaseChangeComparison_of_kFlat
    (A B C : DifferentialGradedAlgebra.{u, u} R)
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex) :
    IsIso (derivedTensorBaseChangeComparison A B C) := by
  have := isIso_derivedTensorFunctorCounit_of_preservesQuasiIso (baseChangeBimodule B C)
    (tensorPreservesQuasiIso_baseChangeBimodule B C hC)
  exact (isIso_derivedTensorBaseChangeComparison_iff A B C).2 inferInstance

/-- **The conclusion of Tag 0BZ5 under K-flatness of `C`.** The conclusion of Tag 0BZ5 is that
the composite of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for the bimodule
`N'' = Ñ ⊗_B Ñ'` of `DifferentialGraded.Bimodule.compTensorResolution`.

What Tag 09S4 contributes over Tag 0BZ5 is exactly the hypothesis of Tag 0BZ5, the invertibility
of the map of Tag 0BZ4, and that is what is discharged here from K-flatness of `C`. The four
remaining arguments are the inputs of Tag 0BZ5 itself, each a different Stacks result and each
named: `hAB` and `hBC` are the second assertion of Tag 09S3, `hcomp` is Tag 0BZ3, and `hdev` is
the dévissage performed in the proof of Tag 0BZ5. They are documented at
`DifferentialGraded.Bimodule.QuasiIsoInvertsDerivedTensor`,
`DifferentialGraded.Bimodule.DerivedTensorCompositionData` and
`DifferentialGraded.Bimodule.BaseChangeDevissage`, and all four are proved in this development;
`hdev` is proved downstream of this file, so the second conclusion of Tag 09S4 — this statement
with all four discharged, and K-flatness of `C` its only hypothesis — is
`DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatAlgebra` in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorBaseChangeSecondVariable.lean`. -/
def derivedTensorFunctorCompIsoOfKFlat
    (hAB : QuasiIsoInvertsDerivedTensor A B) (hBC : QuasiIsoInvertsDerivedTensor B C)
    (hcomp : DerivedTensorCompositionData A B C) (hdev : BaseChangeDevissage A B C)
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIso hAB hBC hcomp hdev
    (isIso_derivedTensorBaseChangeComparison_of_kFlat A B C hC) N N'

end DifferentialGraded.Bimodule

end
