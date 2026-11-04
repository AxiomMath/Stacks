module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorInclusion
public import StacksFrontier.Algebra.DifferentialGraded.Module.RestrictionDGFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor

/-!
# The canonical map from the derived to the plain tensor product of three algebras

Let `R` be a ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded `R`-algebras.
Write `(A ⊗_R B)_B` for the differential graded algebra `A ⊗_R B` viewed as a right differential
graded `B`-module through `b ↦ 1 ⊗ b`, and `{}_B(B ⊗_R C)_C` for `B ⊗_R C` viewed as a
differential graded `(B, C)`-bimodule, with `B` acting on the left through `b ↦ b ⊗ 1` and `C` on
the right through `c ↦ 1 ⊗ c`. This file constructs the canonical map

`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C`

in `D(C, d)`. It is the comparison of the derived with the plain tensor product — the counit of
the Kan extension defining `- ⊗_B^𝐋 {}_B(B ⊗_R C)_C` — evaluated at `A ⊗_R B`, followed by the
identification of the plain relative tensor product
`(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C` with `A ⊗_R B ⊗_R C`, which is constructed here as an
isomorphism of right differential graded `C`-modules.

## Main definitions

* `DifferentialGraded.baseChangeModule` and `DifferentialGraded.baseChangeBimodule`: the two
  objects `(A ⊗_R B)_B` and `{}_B(B ⊗_R C)_C`.
* `DifferentialGraded.Bimodule.restrictRight`: a differential graded `(A, S)`-bimodule, restricted
  on the right along a homomorphism `C → S` of differential graded algebras.
* `DifferentialGraded.comparisonBilinear`: the balanced bilinear map
  `(s, b ⊗ c) ↦ (s · (1 ⊗ b)) ⊗ c` underlying the identification, and
  `DifferentialGraded.comparisonHom`,
  `DifferentialGraded.comparisonInv`: the two homomorphisms of differential graded `C`-modules it
  produces.
* `DifferentialGraded.derivedTensorBaseChangeComparison`: the canonical map in `D(C, d)`.

## Main results

* `DifferentialGraded.tripleTensorIso`: the identification
  `(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C = (A ⊗_R B ⊗_R C)_C`, as an isomorphism of right differential
  graded `C`-modules.
* `DifferentialGraded.comparisonHom_pure` and
  `DifferentialGraded.comparisonInvLinear_tmul`: the formulas pinning the two directions of the
  identification down on pure tensors.

## Implementation notes

*The triple tensor product is nested on the left.* The target is
`(A ⊗_R B) ⊗_R C`, the tensor product of the differential graded algebra `A ⊗_R B` with `C`;
viewed as a right `C`-module it is `baseChangeModule (tensorProduct A B) C`, so the same
construction serves for the source and for the target.

*The forward direction is a definite description.* Tensoring with a bimodule is characterized by
its universal property (`DifferentialGraded.Bimodule.tensorDGFunctor`), so `comparisonHom` is the
unique homomorphism out of `(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C` with the effect on pure tensors
given by `comparisonHom_pure`. The inverse direction is built directly from the universal pure
tensors.

*Two spellings of one module.* The underlying module of `tensorProduct A B` is
`A.grading ᵍ⊗[R] B.grading`, and that of `baseChangeModule A B` is the same type reached through
the differential graded algebra and module structures. Instance resolution and rewriting do not
see through the second spelling, so the statements below are given at the first: a homogeneous
element is passed as an element together with its membership in `tensorProductGrading`, rather
than as an element of the subtype, and `pureBilinear` is the universal balanced bilinear map read
at that spelling.

*Universes.* The bimodules used here have the base ring, the algebras and the modules in a single
universe, so the three algebras are taken at `DifferentialGradedAlgebra.{u, u}`.

## References

* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4)
* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2)
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)
* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra.{u, u} R)

/-- On the pure tensor `1 ⊗ b`, the signed tensor differential is `1 ⊗ d b`. -/
theorem tensorProductDifferential_one_tmul (b : B.A) :
    tensorProductDifferential A B (((1 : A.A) ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading)) =
      ((1 : A.A) ᵍ⊗ₜ[R] (B.d b) : A.grading ᵍ⊗[R] B.grading) := by
  rw [tensorProductDifferential_tmul_aux A B 0 ⟨1, SetLike.one_mem_graded A.grading⟩ b]
  simp [DifferentialGradedAlgebra.d_one A, GradedTensorProduct.tmul]

/-- Multiplying a pure tensor on the right by `1 ⊗ b'` multiplies its right factor by `b'`. -/
theorem tmul_mul_one_tmul (a : A.A) (b b' : B.A) :
    ((a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) * ((1 : A.A) ᵍ⊗ₜ[R] b')) =
      (a ᵍ⊗ₜ[R] (b * b') : A.grading ᵍ⊗[R] B.grading) := by
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero => simp [GradedTensorProduct.tmul]
  | add x y hx hy => rw [tmul_add_right, add_mul, hx, hy, add_mul, tmul_add_right]
  | @homogeneous q b =>
    exact GradedTensorProduct.tmul_coe_mul_one_tmul A.grading B.grading a b b'

/-- Multiplying a pure tensor on the left by `a ⊗ 1` multiplies its left factor by `a`. -/
theorem tmul_one_mul_tmul (a a' : A.A) (b : B.A) :
    (((a ᵍ⊗ₜ[R] (1 : B.A) : A.grading ᵍ⊗[R] B.grading)) * (a' ᵍ⊗ₜ[R] b)) =
      ((a * a') ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) := by
  induction a' using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [GradedTensorProduct.tmul]
  | add x y hx hy => rw [tmul_add_left, mul_add, hx, hy, mul_add, tmul_add_left]
  | @homogeneous p a' =>
    exact GradedTensorProduct.tmul_one_mul_coe_tmul A.grading B.grading a a' b

/-- A degree-`n` element of `A ⊗_R B` is an `R`-linear combination of pure tensors of
homogeneous elements whose degrees add up to `n`. -/
theorem tensorProductGrading_induction (n : ℤ)
    {motive : (A.grading ᵍ⊗[R] B.grading) → Prop} (h0 : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (r : R) x, motive x → motive (r • x))
    (hgen : ∀ (p q : ℤ) (a : A.A) (b : B.A), a ∈ A.grading p → b ∈ B.grading q → p + q = n →
      motive ((a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading)))
    (x : A.grading ᵍ⊗[R] B.grading) (hx : x ∈ tensorProductGrading A B n) : motive x := by
  refine Submodule.span_induction (p := fun z _ => motive z) ?_ h0 (fun x y _ _ => hadd x y)
    (fun r x _ => hsmul r x) hx
  rintro z ⟨p, q, a, b, ha, hb, hpq, rfl⟩
  exact hgen p q a b ha hb hpq

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A S C : DifferentialGradedAlgebra.{u, u} R}

/-- A homogeneous right `S`-linear map between differential graded `S`-modules is a homogeneous
right `C`-linear map between their restrictions along a homomorphism `ψ : C → S`. -/
def restrictScalarsHomogeneousMap (ψ : C.Hom S) {M N : DifferentialGradedModule.{u, u, u} S}
    {n : ℤ} (f : HomogeneousMap S M N n) :
    HomogeneousMap C (restrictScalars ψ M) (restrictScalars ψ N) n :=
  ⟨f.1, f.2.1, fun c x => f.2.2 (ψ.toAlgebraHom c) x⟩

/-- Restricting the right scalars of a differential graded `(A, S)`-bimodule along a
homomorphism `ψ : C → S` leaves the left `A`-action untouched and keeps it right linear, so it
is a differential graded `(A, C)`-bimodule structure on the restricted module. -/
def restrictScalarsBimoduleStructure (ψ : C.Hom S) {M : DifferentialGradedModule.{u, u, u} S}
    (L : BimoduleStructure A S M) : BimoduleStructure A C (restrictScalars ψ M) :=
  ⟨L.1, fun n a => by
    obtain ⟨g, hg⟩ := L.2 n a
    exact ⟨restrictScalarsHomogeneousMap ψ g, hg⟩⟩

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A B C : DifferentialGradedAlgebra.{u, u} R)

/-- A differential graded `(A, S)`-bimodule, restricted on the right along a homomorphism
`ψ : C → S` of differential graded algebras. -/
def Bimodule.restrictRight {A S C : DifferentialGradedAlgebra.{u, u} R} (ψ : C.Hom S)
    (N : Bimodule A S) : Bimodule A C where
  rightModule := restrictScalars ψ N.rightModule
  leftAction := restrictScalarsBimoduleStructure ψ N.leftAction

/-- `(A ⊗_R B)_B`: the differential graded algebra `A ⊗_R B`, viewed as a right differential
graded `B`-module through `b ↦ 1 ⊗ b`. -/
def baseChangeModule : DifferentialGradedModule.{u, u, u} B :=
  tensorRestrictRight A B (regularModule (tensorProduct A B))

/-- `{}_B(B ⊗_R C)_C`: the differential graded algebra `B ⊗_R C`, viewed as a differential
graded `(B, C)`-bimodule, with `B` acting on the left through `b ↦ b ⊗ 1` and `C` on the right
through `c ↦ 1 ⊗ c`. -/
def baseChangeBimodule : Bimodule B C :=
  Bimodule.restrictRight (tensorIncludeRightHom B C)
    (Bimodule.regular (tensorIncludeLeftHom B C))

/-! ### The identification of the plain tensor product with the triple tensor product -/

/-- Every element of `X ⊗_R Y` is a sum of pure tensors. -/
theorem gradedTensor_induction {X Y : DifferentialGradedAlgebra.{u, u} R}
    {motive : (X.grading ᵍ⊗[R] Y.grading) → Prop}
    (zero : motive 0)
    (tmul : ∀ (x : X.A) (y : Y.A), motive ((x ᵍ⊗ₜ[R] y : X.grading ᵍ⊗[R] Y.grading)))
    (add : ∀ z w, motive z → motive w → motive (z + w))
    (z : X.grading ᵍ⊗[R] Y.grading) : motive z := by
  obtain ⟨w, rfl⟩ := (GradedTensorProduct.of R X.grading Y.grading).surjective z
  induction w using TensorProduct.induction_on with
  | zero => simpa using zero
  | tmul x y => exact tmul x y
  | add z w hz hw => rw [map_add]; exact add _ _ hz hw

/-- An integer multiple can be moved out of the left factor of a pure tensor. -/
theorem zsmul_tmul_left {X Y : DifferentialGradedAlgebra.{u, u} R}
    (n : ℤ) (x : X.A) (y : Y.A) :
    (((n • x) ᵍ⊗ₜ[R] y : X.grading ᵍ⊗[R] Y.grading)) =
      n • ((x ᵍ⊗ₜ[R] y : X.grading ᵍ⊗[R] Y.grading)) := by
  show (GradedTensorProduct.of R X.grading Y.grading) ((n • x) ⊗ₜ[R] y) =
    n • (GradedTensorProduct.of R X.grading Y.grading) (x ⊗ₜ[R] y)
  rw [← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R, ← TensorProduct.smul_tmul',
    LinearEquiv.map_smul]

/-- Right multiplication by `1 ⊗ b` on `A ⊗_R B`, as a bilinear map. -/
def mulIncludeRightₗ :
    (A.grading ᵍ⊗[R] B.grading) →ₗ[R] B.A →ₗ[R] (A.grading ᵍ⊗[R] B.grading) :=
  (LinearMap.mul R (A.grading ᵍ⊗[R] B.grading)).compl₂
    (GradedTensorProduct.includeRight A.grading B.grading).toLinearMap

/-- `s ⊗ (b ⊗ c) ↦ (s · (1 ⊗ b)) ⊗ c`, on the absolute tensor product. -/
def comparisonLinear :
    ((A.grading ᵍ⊗[R] B.grading) ⊗[R] (B.grading ᵍ⊗[R] C.grading)) →ₗ[R]
      ((tensorProduct A B).grading ᵍ⊗[R] C.grading) :=
  (GradedTensorProduct.of R (tensorProduct A B).grading C.grading).toLinearMap ∘ₗ
    TensorProduct.map (TensorProduct.lift (mulIncludeRightₗ A B)) LinearMap.id ∘ₗ
    (TensorProduct.assoc R (A.grading ᵍ⊗[R] B.grading) B.A C.A).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id
      (GradedTensorProduct.of R B.grading C.grading).symm.toLinearMap

/-- `(s, b ⊗ c) ↦ (s · (1 ⊗ b)) ⊗ c`, the bilinear map underlying the identification. -/
def comparisonBilinear :
    (A.grading ᵍ⊗[R] B.grading) →ₗ[R] (B.grading ᵍ⊗[R] C.grading) →ₗ[R]
      ((tensorProduct A B).grading ᵍ⊗[R] C.grading) :=
  TensorProduct.curry (comparisonLinear A B C)

/-- The comparison bilinear map sends `(s, b ⊗ c)` to `(s · (1 ⊗ b)) ⊗ c`. -/
theorem comparisonBilinear_tmul (s : A.grading ᵍ⊗[R] B.grading) (b : B.A) (c : C.A) :
    comparisonBilinear A B C s ((b ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading)) =
      (((s * ((1 : A.A) ᵍ⊗ₜ[R] b)) ᵍ⊗ₜ[R] c) :
        (tensorProduct A B).grading ᵍ⊗[R] C.grading) := by
  simp [comparisonBilinear, comparisonLinear, mulIncludeRightₗ, GradedTensorProduct.tmul]

/-- The right `B`-action on `(A ⊗_R B)_B` is right multiplication by `1 ⊗ b`. -/
theorem baseChangeModule_op_smul (x : (baseChangeModule A B).M) (b : B.A) :
    MulOpposite.op b • x =
      (show A.grading ᵍ⊗[R] B.grading from x) * ((1 : A.A) ᵍ⊗ₜ[R] b) := rfl

/-- The right `C`-action on `{}_B(B ⊗_R C)_C` is right multiplication by `1 ⊗ c`. -/
theorem baseChangeBimodule_op_smul (y : (baseChangeBimodule B C).rightModule.M) (c : C.A) :
    MulOpposite.op c • y =
      (show B.grading ᵍ⊗[R] C.grading from y) * ((1 : B.A) ᵍ⊗ₜ[R] c) := rfl

/-- The left `B`-action on `{}_B(B ⊗_R C)_C` is left multiplication by `b ⊗ 1`. -/
theorem baseChangeBimodule_leftAction (n q : ℤ) (b : B.grading n)
    (y : (baseChangeBimodule B C).rightModule.grading q) :
    ((show (baseChangeBimodule B C).rightModule.grading (q + n) from
      ((baseChangeBimodule B C).leftAction.1.action n b).v q (q + n) (by omega) y) :
        (baseChangeBimodule B C).rightModule.M) =
      (((b : B.A) ᵍ⊗ₜ[R] (1 : C.A)) : B.grading ᵍ⊗[R] C.grading) *
        (show B.grading ᵍ⊗[R] C.grading from (y : (baseChangeBimodule B C).rightModule.M)) :=
  regularBimoduleStructure_action (tensorIncludeLeftHom B C) n q b y

/-- `1 ⊗ b` has the degree of `b`. -/
theorem one_tmul_mem_grading (i : ℤ) (b : B.A) (hb : b ∈ B.grading i) :
    (((1 : A.A) ᵍ⊗ₜ[R] b) : A.grading ᵍ⊗[R] B.grading) ∈ tensorProductGrading A B i := by
  simpa only [zero_add] using
    tmul_mem_total A B 0 i 1 b (SetLike.one_mem_graded A.grading) hb

/-- Right multiplication by `1 ⊗ b` raises the degree of an element of `A ⊗_R B` by that of `b`. -/
private theorem mul_one_tmul_mem_grading (p i : ℤ) (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B p) (b : B.A) (hb : b ∈ B.grading i) :
    (x * (((1 : A.A) ᵍ⊗ₜ[R] b) : A.grading ᵍ⊗[R] B.grading)) ∈
      tensorProductGrading A B (p + i) := by
  have := totalGradedMonoid A B
  exact SetLike.mul_mem_graded hx (one_tmul_mem_grading A B i b hb)

/-- A linear map sends a degree-`n` element of `A ⊗_R B` into a submodule as soon as it does so on
the pure tensors of homogeneous elements whose degrees add up to `n`. -/
private theorem map_mem_of_tmul_mem {M : Type*} [AddCommGroup M] [Module R M] (P : Submodule R M)
    (f : (A.grading ᵍ⊗[R] B.grading) →ₗ[R] M) (n : ℤ)
    (h : ∀ (p q : ℤ) (a : A.A) (b : B.A), a ∈ A.grading p → b ∈ B.grading q → p + q = n →
      f (a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) ∈ P)
    (x : A.grading ᵍ⊗[R] B.grading) (hx : x ∈ tensorProductGrading A B n) : f x ∈ P :=
  tensorProductGrading_induction A B n (motive := fun z => f z ∈ P)
    (by rw [map_zero]; exact P.zero_mem)
    (fun z w hz hw => by rw [map_add]; exact P.add_mem hz hw)
    (fun r z hz => by rw [map_smul]; exact P.smul_mem r hz) h x hx

/-- The comparison bilinear map adds degrees. -/
theorem comparisonBilinear_mem_grading (p q : ℤ) (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B p) (y : B.grading ᵍ⊗[R] C.grading)
    (hy : y ∈ tensorProductGrading B C q) :
    comparisonBilinear A B C x y ∈ tensorProductGrading (tensorProduct A B) C (p + q) := by
  refine map_mem_of_tmul_mem B C _ (comparisonBilinear A B C x) q ?_ y hy
  intro i j b c hb hc hij
  rw [comparisonBilinear_tmul]
  have h2 := tmul_mem_total (tensorProduct A B) C (p + i) j _ c
    (mul_one_tmul_mem_grading A B p i x hx b hb) hc
  rwa [show p + i + j = p + q by omega] at h2

/-- The differential of the tensor product algebra is the signed tensor differential. -/
theorem tensorProduct_d_apply {X Y : DifferentialGradedAlgebra.{u, u} R}
    (z : X.grading ᵍ⊗[R] Y.grading) :
    (tensorProduct X Y).d z = tensorProductDifferential X Y z := rfl

/-- The comparison bilinear map satisfies the graded Leibniz rule. -/
theorem comparisonBilinear_d (p : ℤ) (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B p) (y : B.grading ᵍ⊗[R] C.grading) :
    tensorProductDifferential (tensorProduct A B) C (comparisonBilinear A B C x y) =
      comparisonBilinear A B C (tensorProductDifferential A B x) y +
        (p.negOnePow : ℤ) •
          comparisonBilinear A B C x (tensorProductDifferential B C y) := by
  induction y using gradedTensor_induction with
  | zero => simp
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
      have h1b := one_tmul_mem_grading A B i (b : B.A) b.property
      have hxb := mul_one_tmul_mem_grading A B p i x hx (b : B.A) b.property
      rw [comparisonBilinear_tmul, comparisonBilinear_tmul,
        tensorProductDifferential_tmul_aux (tensorProduct A B) C (p + i) ⟨_, hxb⟩ c,
        tensorProductDifferential_tmul_aux B C i b c, map_add, map_zsmul,
        comparisonBilinear_tmul, comparisonBilinear_tmul]
      simp only [tensorProduct_d_apply]
      rw [differential_leibniz_total A B p i x _ hx h1b,
        tensorProductDifferential_one_tmul A B (b : B.A),
        tmul_add_left, zsmul_tmul_left, Int.negOnePow_add, Units.val_mul, mul_smul, smul_add]
      abel

/-- The comparison bilinear map is balanced over `B`: moving `1 ⊗ a` across from the right
action on `A ⊗_R B` to the left action on `B ⊗_R C` does not change its value. -/
theorem comparisonBilinear_balance (s : A.grading ᵍ⊗[R] B.grading) (a : B.A)
    (y : B.grading ᵍ⊗[R] C.grading) :
    comparisonBilinear A B C
        (s * (((1 : A.A) ᵍ⊗ₜ[R] a) : A.grading ᵍ⊗[R] B.grading)) y =
      comparisonBilinear A B C s
        ((((a ᵍ⊗ₜ[R] (1 : C.A)) : B.grading ᵍ⊗[R] C.grading)) * y) := by
  induction y using gradedTensor_induction with
  | zero => simp
  | add z w hz hw => rw [map_add, hz, hw, mul_add, map_add]
  | tmul b c =>
    rw [comparisonBilinear_tmul, tmul_one_mul_tmul, comparisonBilinear_tmul, mul_assoc,
      tmul_mul_one_tmul]

/-- The comparison bilinear map is right `C`-linear in its second variable. -/
theorem comparisonBilinear_mul_one_tmul (s : A.grading ᵍ⊗[R] B.grading)
    (y : B.grading ᵍ⊗[R] C.grading) (c : C.A) :
    comparisonBilinear A B C s
        (y * (((1 : B.A) ᵍ⊗ₜ[R] c) : B.grading ᵍ⊗[R] C.grading)) =
      comparisonBilinear A B C s y *
        (((1 : (tensorProduct A B).A) ᵍ⊗ₜ[R] c) :
          (tensorProduct A B).grading ᵍ⊗[R] C.grading) := by
  induction y using gradedTensor_induction with
  | zero => simp
  | add z w hz hw => rw [add_mul, map_add, hz, hw, map_add, add_mul]
  | tmul b c₀ =>
    rw [tmul_mul_one_tmul, comparisonBilinear_tmul, comparisonBilinear_tmul, tmul_mul_one_tmul]

/-- The identification `(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C = (A ⊗_R B ⊗_R C)_C`, as a balanced
bilinear map: `(s, b ⊗ c) ↦ (s · (1 ⊗ b)) ⊗ c`. -/
def comparisonBalanced :
    Bimodule.BalancedBilinearMap (baseChangeModule A B) (baseChangeBimodule B C)
      (baseChangeModule (tensorProduct A B) C) where
  toLinearMap := comparisonBilinear A B C
  map_grading p q x y := comparisonBilinear_mem_grading A B C p q x.1 x.2 y.1 y.2
  map_d p x y := comparisonBilinear_d A B C p x.1 x.2 y
  balance p q n x y a := by
    rw [baseChangeBimodule_leftAction]
    exact comparisonBilinear_balance A B C x.1 a.1 y.1
  map_right x y c := comparisonBilinear_mul_one_tmul A B C x y c

/-- The plain tensor product `(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C`, as a right differential graded
`C`-module. -/
abbrev plainTensorObj : DifferentialGradedModule.{u, u, u} C :=
  (Bimodule.tensorDGFunctor (baseChangeBimodule B C)).functor.obj (baseChangeModule A B)

/-- The universal balanced bilinear map into the plain tensor product. -/
abbrev pureMap :
    Bimodule.BalancedBilinearMap (baseChangeModule A B) (baseChangeBimodule B C)
      (plainTensorObj A B C) :=
  (Bimodule.tensorDGFunctor (baseChangeBimodule B C)).pure (baseChangeModule A B)

/-- The universal pure tensors `s ⊗ y`, with the two arguments read in the graded tensor
products `A ⊗_R B` and `B ⊗_R C` themselves. -/
def pureBilinear :
    (A.grading ᵍ⊗[R] B.grading) →ₗ[R] (B.grading ᵍ⊗[R] C.grading) →ₗ[R]
      (plainTensorObj A B C).M :=
  (pureMap A B C).toLinearMap

/-- The pure tensors are right `C`-linear in the second variable. -/
theorem pureBilinear_mul_one_tmul (x : A.grading ᵍ⊗[R] B.grading)
    (y : B.grading ᵍ⊗[R] C.grading) (c : C.A) :
    pureBilinear A B C x (y * (((1 : B.A) ᵍ⊗ₜ[R] c) : B.grading ᵍ⊗[R] C.grading)) =
      MulOpposite.op c • pureBilinear A B C x y :=
  (pureMap A B C).map_right x y c

/-- The pure tensors add degrees. -/
theorem pureBilinear_mem_grading (p q : ℤ) (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B p) (y : B.grading ᵍ⊗[R] C.grading)
    (hy : y ∈ tensorProductGrading B C q) :
    pureBilinear A B C x y ∈ (plainTensorObj A B C).grading (p + q) :=
  (pureMap A B C).map_grading p q ⟨x, hx⟩ ⟨y, hy⟩

/-- The pure tensors satisfy the graded Leibniz rule. -/
theorem pureBilinear_d (p : ℤ) (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B p) (y : B.grading ᵍ⊗[R] C.grading) :
    (plainTensorObj A B C).d (pureBilinear A B C x y) =
      pureBilinear A B C (tensorProductDifferential A B x) y +
        (p.negOnePow : ℤ) • pureBilinear A B C x (tensorProductDifferential B C y) :=
  (pureMap A B C).map_d p ⟨x, hx⟩ y

/-- The pure tensors are balanced over `B`: moving `1 ⊗ b` from the right action on `A ⊗_R B`
to the left action on `B ⊗_R C` does not change them. -/
theorem pureBilinear_balance_of_mem (p q n : ℤ) (x : A.grading ᵍ⊗[R] B.grading)
    (hx : x ∈ tensorProductGrading A B p) (y : B.grading ᵍ⊗[R] C.grading)
    (hy : y ∈ tensorProductGrading B C q) (b : B.grading n) :
    pureBilinear A B C (x * (((1 : A.A) ᵍ⊗ₜ[R] (b : B.A)) : A.grading ᵍ⊗[R] B.grading)) y =
      pureBilinear A B C x
        ((((b : B.A) ᵍ⊗ₜ[R] (1 : C.A)) : B.grading ᵍ⊗[R] C.grading) * y) := by
  have h := (pureMap A B C).balance p q n ⟨x, hx⟩ ⟨y, hy⟩ b
  rwa [baseChangeBimodule_leftAction] at h

/-- The plain tensor product computed by the functor on differential graded modules is the
value of the differential graded tensor functor. -/
theorem tensorCompFunctor_obj_eq :
    (Bimodule.tensorCompFunctor (baseChangeBimodule B C)).obj (baseChangeModule A B) =
      plainTensorObj A B C := rfl

/-- The unit of `A ⊗_R B` is `1 ⊗ 1`. -/
theorem one_tmul_one : (((1 : A.A) ᵍ⊗ₜ[R] (1 : B.A)) : A.grading ᵍ⊗[R] B.grading) = 1 := rfl

/-- The pure-tensor formula for the signed tensor differential, with the homogeneity of the
left factor as a hypothesis. -/
theorem tensorProductDifferential_tmul_of_mem {X Y : DifferentialGradedAlgebra.{u, u} R} (p : ℤ)
    (a : X.A) (ha : a ∈ X.grading p) (b : Y.A) :
    tensorProductDifferential X Y ((a ᵍ⊗ₜ[R] b : X.grading ᵍ⊗[R] Y.grading)) =
      ((X.d a) ᵍ⊗ₜ[R] b : X.grading ᵍ⊗[R] Y.grading) +
        (p.negOnePow : ℤ) • ((a ᵍ⊗ₜ[R] Y.d b : X.grading ᵍ⊗[R] Y.grading)) :=
  tensorProductDifferential_tmul_aux X Y p ⟨a, ha⟩ b

/-- The universal property of the plain tensor product, applied to the comparison bilinear
map: there is a unique homomorphism of differential graded `C`-modules out of
`(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C` sending `s ⊗ (b ⊗ c)` to `(s · (1 ⊗ b)) ⊗ c`. -/
theorem universalProperty :
    ∃! g : DifferentialGradedModule.Hom (plainTensorObj A B C)
        (baseChangeModule (tensorProduct A B) C),
      ∀ (x : (baseChangeModule A B).M) (y : (baseChangeBimodule B C).rightModule.M),
        g.toFun ((pureMap A B C).toLinearMap x y) =
          (comparisonBalanced A B C).toLinearMap x y :=
  (Bimodule.tensorDGFunctor (baseChangeBimodule B C)).universal (baseChangeModule A B)
    (baseChangeModule (tensorProduct A B) C) (comparisonBalanced A B C)

/-- The identification `(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C = (A ⊗_R B ⊗_R C)_C`, in the direction
out of the plain tensor product: the unique homomorphism of differential graded `C`-modules
sending the pure tensor `s ⊗ (b ⊗ c)` to `(s · (1 ⊗ b)) ⊗ c`. -/
def comparisonHom : DifferentialGradedModule.Hom (plainTensorObj A B C)
    (baseChangeModule (tensorProduct A B) C) :=
  (universalProperty A B C).choose

/-- `comparisonHom` sends the pure tensor `s ⊗ y` to `comparisonBilinear s y`, and is the unique
homomorphism of differential graded `C`-modules that does so. -/
theorem comparisonHom_pure (x : A.grading ᵍ⊗[R] B.grading) (y : B.grading ᵍ⊗[R] C.grading) :
    (comparisonHom A B C).toFun (pureBilinear A B C x y) = comparisonBilinear A B C x y :=
  (universalProperty A B C).choose_spec.1 x y

/-- The differential of `(A ⊗_R B)_B` is the signed tensor differential of `A ⊗_R B`. -/
theorem baseChangeModule_d (x : A.grading ᵍ⊗[R] B.grading) :
    (baseChangeModule A B).d x = tensorProductDifferential A B x := rfl

/-- `s ⊗ c ↦ s ⊗ (1 ⊗ c)`, the inverse of the identification
`(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C = (A ⊗_R B ⊗_R C)_C`, as a linear map. -/
def comparisonInvLinear :
    ((tensorProduct A B).grading ᵍ⊗[R] C.grading) →ₗ[R] (plainTensorObj A B C).M :=
  TensorProduct.lift ((pureBilinear A B C).compl₂
      (GradedTensorProduct.includeRight B.grading C.grading).toLinearMap) ∘ₗ
    (GradedTensorProduct.of R (tensorProduct A B).grading C.grading).symm.toLinearMap

/-- The inverse identification sends `s ⊗ c` to the pure tensor `s ⊗ (1 ⊗ c)`. -/
theorem comparisonInvLinear_tmul (s : A.grading ᵍ⊗[R] B.grading) (c : C.A) :
    comparisonInvLinear A B C (((s ᵍ⊗ₜ[R] c) : (tensorProduct A B).grading ᵍ⊗[R] C.grading)) =
      pureBilinear A B C s (((1 : B.A) ᵍ⊗ₜ[R] c) : B.grading ᵍ⊗[R] C.grading) := rfl

/-- The inverse identification is right `C`-linear. -/
theorem comparisonInvLinear_mul_one_tmul (z : (tensorProduct A B).grading ᵍ⊗[R] C.grading)
    (c : C.A) :
    comparisonInvLinear A B C
        (z * (((1 : (tensorProduct A B).A) ᵍ⊗ₜ[R] c) :
          (tensorProduct A B).grading ᵍ⊗[R] C.grading)) =
      MulOpposite.op c • comparisonInvLinear A B C z := by
  induction z using gradedTensor_induction with
  | zero => simp
  | add u v hu hv => simp only [add_mul, map_add, hu, hv, smul_add]
  | tmul s c₀ =>
    rw [tmul_mul_one_tmul (tensorProduct A B) C s c₀ c, comparisonInvLinear_tmul,
      comparisonInvLinear_tmul, ← pureBilinear_mul_one_tmul,
      tmul_mul_one_tmul B C 1 c₀ c]

/-- The inverse identification preserves degrees. -/
theorem comparisonInvLinear_mem_grading (k : ℤ) (z : (tensorProduct A B).grading ᵍ⊗[R] C.grading)
    (hz : z ∈ tensorProductGrading (tensorProduct A B) C k) :
    comparisonInvLinear A B C z ∈ (plainTensorObj A B C).grading k := by
  refine map_mem_of_tmul_mem (tensorProduct A B) C _ (comparisonInvLinear A B C) k ?_ z hz
  intro i j s c hs hc hij
  rw [comparisonInvLinear_tmul]
  have h := pureBilinear_mem_grading A B C i j s hs _ (one_tmul_mem_grading B C j c hc)
  rwa [hij] at h

/-- The inverse identification commutes with the differentials. -/
theorem comparisonInvLinear_d (z : (tensorProduct A B).grading ᵍ⊗[R] C.grading) :
    comparisonInvLinear A B C (tensorProductDifferential (tensorProduct A B) C z) =
      (plainTensorObj A B C).d (comparisonInvLinear A B C z) := by
  induction z using gradedTensor_induction with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul s c =>
    induction s using DirectSum.Decomposition.inductionOn (tensorProduct A B).grading with
    | zero => simp [GradedTensorProduct.tmul]
    | add s s' hs hs' => simp only [tmul_add_left, map_add, hs, hs']
    | @homogeneous i s =>
      rw [tensorProductDifferential_tmul_of_mem i s.1 s.2 c, map_add, map_zsmul,
        comparisonInvLinear_tmul, comparisonInvLinear_tmul, comparisonInvLinear_tmul,
        pureBilinear_d A B C i s.1 s.2 (((1 : B.A) ᵍ⊗ₜ[R] c) : B.grading ᵍ⊗[R] C.grading)]
      simp only [tensorProduct_d_apply, tensorProductDifferential_one_tmul]

/-- The inverse identification `(A ⊗_R B ⊗_R C)_C → (A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C`, as a
homomorphism of differential graded `C`-modules. -/
def comparisonInv : DifferentialGradedModule.Hom
    (baseChangeModule (tensorProduct A B) C) (plainTensorObj A B C) where
  toFun := comparisonInvLinear A B C
  map_smul z c := comparisonInvLinear_mul_one_tmul A B C z c
  map_grading k z hz := comparisonInvLinear_mem_grading A B C k z hz
  map_d := LinearMap.ext fun z => comparisonInvLinear_d A B C z

/-- The pure tensors are balanced over `B`, with no homogeneity assumption. -/
theorem pureBilinear_balance (b : B.A) (x : A.grading ᵍ⊗[R] B.grading)
    (y : B.grading ᵍ⊗[R] C.grading) :
    pureBilinear A B C (x * (((1 : A.A) ᵍ⊗ₜ[R] b) : A.grading ᵍ⊗[R] B.grading)) y =
      pureBilinear A B C x ((((b ᵍ⊗ₜ[R] (1 : C.A)) : B.grading ᵍ⊗[R] C.grading)) * y) := by
  have := totalDecomposition A B
  have := totalDecomposition B C
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero => simp [GradedTensorProduct.tmul]
  | add b b' hb hb' =>
    simp only [tmul_add_right, mul_add, map_add, LinearMap.add_apply, hb, hb', tmul_add_left,
      add_mul]
  | @homogeneous n b =>
    induction x using DirectSum.Decomposition.inductionOn (tensorProductGrading A B) with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add, LinearMap.add_apply, hx, hx']
    | @homogeneous p x =>
      induction y using DirectSum.Decomposition.inductionOn (tensorProductGrading B C) with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
      | @homogeneous q y => exact pureBilinear_balance_of_mem A B C p q n x.1 x.2 y.1 y.2 b

/-- The inverse identification undoes the identification on every pure tensor. -/
theorem comparisonInvLinear_comparisonBilinear (x : A.grading ᵍ⊗[R] B.grading)
    (y : B.grading ᵍ⊗[R] C.grading) :
    comparisonInvLinear A B C (comparisonBilinear A B C x y) = pureBilinear A B C x y := by
  induction y using gradedTensor_induction with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b c =>
    rw [comparisonBilinear_tmul, comparisonInvLinear_tmul, pureBilinear_balance,
      tmul_one_mul_tmul, mul_one]

/-- The identification
`(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C = (A ⊗_R B ⊗_R C)_C`: the plain relative tensor product of the
two base-change bimodules is the triple tensor product, as right differential graded
`C`-modules. -/
@[stacks 0BZ4 "the identification of the plain tensor products"]
def tripleTensorIso : plainTensorObj A B C ≅ baseChangeModule (tensorProduct A B) C where
  hom := comparisonHom A B C
  inv := comparisonInv A B C
  hom_inv_id := by
    refine ((Bimodule.tensorDGFunctor (baseChangeBimodule B C)).universal
      (baseChangeModule A B) (plainTensorObj A B C) (pureMap A B C)).unique ?_ ?_
    · exact fun x y => (congrArg (comparisonInv A B C).toFun (comparisonHom_pure A B C x y)).trans
        (comparisonInvLinear_comparisonBilinear A B C x y)
    · exact fun _ _ => rfl
  inv_hom_id := by
    apply DifferentialGradedModule.Hom.ext
    apply GradedTensorProduct.hom_ext (𝒜 := (tensorProduct A B).grading) (ℬ := C.grading)
    apply TensorProduct.ext'
    intro s c
    change (comparisonHom A B C).toFun (comparisonInvLinear A B C
        (((s ᵍ⊗ₜ[R] c) : (tensorProduct A B).grading ᵍ⊗[R] C.grading))) =
      ((s ᵍ⊗ₜ[R] c) : (tensorProduct A B).grading ᵍ⊗[R] C.grading)
    rw [comparisonInvLinear_tmul, comparisonHom_pure, comparisonBilinear_tmul, one_tmul_one,
      mul_one]

/-- The canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` in `D(C, d)`. It is the comparison of
the derived with the plain tensor product at the right differential graded `B`-module
`A ⊗_R B`, followed by the identification of the plain tensor product
`(A ⊗_R B)_B ⊗_B {}_B(B ⊗_R C)_C` with `A ⊗_R B ⊗_R C`. -/
@[stacks 0BZ4 "the canonical map in D(C, d)"]
def derivedTensorBaseChangeComparison :
    (Bimodule.derivedTensorFunctor (baseChangeBimodule B C)).obj
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj (baseChangeModule A B))) ⟶
      (quasiIsomorphisms' C).Q.obj
        ((toHomotopyCategory C).obj (baseChangeModule (tensorProduct A B) C)) :=
  (Bimodule.derivedTensorFunctorCounit (baseChangeBimodule B C)).app
      ((toHomotopyCategory B).obj (baseChangeModule A B)) ≫
    (quasiIsomorphisms' C).Q.map
      ((Bimodule.tensorCompFunctor_quotient (baseChangeBimodule B C)).inv.app
        (baseChangeModule A B)) ≫
    (quasiIsomorphisms' C).Q.map ((toHomotopyCategory C).map (tripleTensorIso A B C).hom)

end DifferentialGraded

end
