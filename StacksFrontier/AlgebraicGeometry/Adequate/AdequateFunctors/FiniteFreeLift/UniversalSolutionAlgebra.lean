module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksFrontier.Algebra.Module.Adequate.Laurent
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.BaseChange
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFullness
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The universal solution algebra of a map between finite free modules

This file is the first part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift`. It sets up the
coefficient family of a tensor with Laurent polynomial coefficients, the module-valued functor
`AdequateFunctor.moduleExtensionOfCarrier` of an `A`-module, the grading of the symmetric
algebra by symmetric powers and its graded Laurent map, and the universal solution algebra of
the relations imposed by a map `d` between finite free modules, together with the algebra maps
out of it classifying tuples that satisfy those relations.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
-/

@[expose] public section

open CategoryTheory
universe w v u z u₁ v₁

namespace AdequateFunctor


open scoped DirectSum
open TensorProduct

/-- A tensor with Laurent polynomial coefficients, read as the finitely supported family of
its coefficients. -/
noncomputable def laurentTensorCoefficientsLarge (A : Type u) (B : Type v)
    (M : Type w) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] :
    (LaurentPolynomial B ⊗[A] M) ≃ₗ[A] ℤ →₀ (B ⊗[A] M) := by
  let e : LaurentPolynomial B ≃ₗ[A] ℤ →₀ B :=
    (AddMonoidAlgebra.coeffLinearEquiv B).restrictScalars A
  let e' : (LaurentPolynomial B ⊗[A] M) ≃ₗ[A] (ℤ →₀ B) ⊗[A] M :=
    TensorProduct.congr e (LinearEquiv.refl A M)
  let e'' : ((ℤ →₀ B) ⊗[A] M) ≃ₗ[A] ℤ →₀ (B ⊗[A] M) :=
    (TensorProduct.finsuppLeft A B B M ℤ).restrictScalars A
  exact e'.trans e''

/-- The coefficient family of a pure tensor is the coefficient family of the polynomial,
tensored with the module element. -/
private lemma laurentTensorCoefficientsLarge_tmul (A : Type u) (B : Type v)
    (M : Type w) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (p : LaurentPolynomial B) (m : M) (k : ℤ) :
    laurentTensorCoefficientsLarge A B M (p ⊗ₜ[A] m) k = p.coeff k ⊗ₜ[A] m := by
  simp [laurentTensorCoefficientsLarge, TensorProduct.finsuppLeft_apply_tmul_apply]

/-- The inclusion of `B` into its Laurent polynomial algebra as the constants. -/
public noncomputable def constantLaurentMapLarge (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : B →ₐ[A] LaurentPolynomial B where
  toRingHom := LaurentPolynomial.C
  commutes' _ := rfl

/-- The coefficient family of `T ^ k` times a constant tensor is concentrated in degree `k`. -/
lemma laurentTensorCoefficientsLarge_weightedConstant {A : Type u} {B : Type v}
    {M : Type z} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (k : ℤ) (y : TensorProduct A B M) :
    laurentTensorCoefficientsLarge A B M
      ((LaurentPolynomial.T k : LaurentPolynomial B) •
        (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) y) =
      Finsupp.single k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
      apply Finsupp.ext
      intro j
      show laurentTensorCoefficientsLarge A B M
        ((LaurentPolynomial.T k * LaurentPolynomial.C b) ⊗ₜ[A] m) j = _
      rw [laurentTensorCoefficientsLarge_tmul]
      rw [mul_comm (LaurentPolynomial.T k) (LaurentPolynomial.C b)]
      have hc : (LaurentPolynomial.C b * LaurentPolynomial.T k).coeff j =
          if k = j then b else 0 := by
        rw [← LaurentPolynomial.single_eq_C_mul_T]
        show (Finsupp.single k b) j = _
        simp only [Finsupp.single_apply]
      rw [hc]
      by_cases hkj : k = j <;> simp [hkj]
  | add y y' hy hy' =>
      simp only [map_add, smul_add, hy, hy', Finsupp.single_add]

/-- The module-valued functor `B ↦ B ⊗[A] M` associated to an `A`-module `M`. -/
@[implicit_reducible]
public noncomputable def moduleExtensionOfCarrier (A : Type u) [CommRing A]
    (M : Type w) [AddCommGroup M] [Module A M] :
    ModuleValuedFunctor.{max u v w, v} A :=
  moduleExtension A (ModuleCat.of A M)

/-- The `n`-th symmetric power of `V`, as a submodule of the symmetric algebra. -/
public def symmetricPower (A : Type u) (V : Type v) [CommRing A] [AddCommGroup V] [Module A V]
    (n : ℕ) : Submodule A (SymmetricAlgebra A V) :=
  (LinearMap.range (SymmetricAlgebra.ι A V)) ^ n

/-- The symmetric powers form a graded monoid inside the symmetric algebra. -/
@[ega "II 1.7.1" "partial"]
public noncomputable instance symmetricPowerGradedMonoid (A : Type u) (V : Type v) [CommRing A]
    [AddCommGroup V] [Module A V] : SetLike.GradedMonoid (symmetricPower A V) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι A V))

/-- The inclusion of `V` into the direct sum of the symmetric powers, landing in degree one. -/
public noncomputable def gradedInclusion (A : Type u) (V : Type v) [CommRing A]
    [AddCommGroup V] [Module A V] :
    V →ₗ[A] ⨁ n : ℕ, symmetricPower A V n :=
  DirectSum.lof A ℕ (fun n => ↥(symmetricPower A V n)) 1 ∘ₗ
    (SymmetricAlgebra.ι A V).codRestrict _ (fun x => by
      simpa only [symmetricPower, pow_one] using
        LinearMap.mem_range_self (SymmetricAlgebra.ι A V) x)

/-- The symmetric powers make the symmetric algebra a graded algebra. -/
@[ega "II 1.7.1"]
public noncomputable instance symmetricAlgebraGradedAlgebra (A : Type u) (V : Type v) [CommRing A]
    [AddCommGroup V] [Module A V] : GradedAlgebra (symmetricPower A V) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (gradedInclusion A V))
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      change (DirectSum.coeAlgHom (symmetricPower A V))
        (SymmetricAlgebra.lift (gradedInclusion A V) (SymmetricAlgebra.ι A V x)) =
          SymmetricAlgebra.ι A V x
      rw [SymmetricAlgebra.lift_ι_apply]
      rw [gradedInclusion, LinearMap.coe_comp, Function.comp_apply, DirectSum.lof_eq_of,
        DirectSum.coeAlgHom_of]
      rfl)
    (fun i x => by
      obtain ⟨x, hx⟩ := x
      dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r =>
        rw [AlgHom.commutes, DirectSum.algebraMap_apply]
        rfl
      | add x y i hx hy ihx ihy =>
        rw [map_add, ihx, ihy, ← map_add]
        rfl
      | mem_mul m hm i x hx ih =>
        obtain ⟨_, rfl⟩ := hm
        rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply]
        change gradedInclusion A V _ * _ = _
        simp only [gradedInclusion, LinearMap.coe_comp, Function.comp_apply, DirectSum.lof_eq_of]
        rw [DirectSum.of_mul_of]
        exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl))

/-- The algebra map sending a homogeneous element of degree `d` to itself times `T ^ d`. -/
public noncomputable def gradedLaurentMapLarge (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] : B →ₐ[A] LaurentPolynomial B := by
  let f : ∀ d, 𝒜 d →+ LaurentPolynomial B := fun d ↦
    (AddMonoidHom.mulRight (LaurentPolynomial.T (d : ℤ))).comp
      ((LaurentPolynomial.C : B →+* LaurentPolynomial B).toAddMonoidHom.comp
        (𝒜 d).subtype.toAddMonoidHom)
  let g : (⨁ d, 𝒜 d) →+* LaurentPolynomial B := DirectSum.liftRingHom
    ⟨fun {d} ↦ f d, by simp [f], by
      intro i j x y
      simp only [f, AddMonoidHom.mulRight_apply, AddMonoidHom.coe_comp,
        Function.comp_apply, RingHom.toAddMonoidHom_eq_coe]
      change LaurentPolynomial.C ((x : B) * (y : B)) *
        LaurentPolynomial.T ((i + j : ℕ) : ℤ) = _
      rw [map_mul, Nat.cast_add, LaurentPolynomial.T_add]
      change LaurentPolynomial.C (x : B) * LaurentPolynomial.C (y : B) *
        (LaurentPolynomial.T (i : ℤ) * LaurentPolynomial.T (j : ℤ)) =
        (LaurentPolynomial.C (x : B) * LaurentPolynomial.T (i : ℤ)) *
          (LaurentPolynomial.C (y : B) * LaurentPolynomial.T (j : ℤ))
      ring⟩
  exact
    { toRingHom := g.comp (DirectSum.decomposeAlgEquiv 𝒜).toRingEquiv.toRingHom
      commutes' := by
        intro a
        change g (DirectSum.decompose 𝒜 (algebraMap A B a)) = _
        rw [DirectSum.decompose_algebraMap]
        change (DirectSum.toAddMonoid (fun d ↦ f d))
          (algebraMap A (⨁ d, 𝒜 d) a) = _
        rw [DirectSum.algebraMap_apply, DirectSum.toAddMonoid_of]
        simp [f] }

/-- On a homogeneous element of degree `d`, the graded Laurent map multiplies by `T ^ d`. -/
public lemma gradedLaurentMapLarge_mem (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (d : ℕ) (x : B)
    (hx : x ∈ 𝒜 d) :
    gradedLaurentMapLarge A B 𝒜 x =
      LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ) := by
  show (DirectSum.liftRingHom _) (DirectSum.decompose 𝒜 x) = _
  rw [DirectSum.decompose_of_mem 𝒜 hx]
  simp [DirectSum.liftRingHom_apply]

/-- A generator of the symmetric algebra lies in the first symmetric power. -/
private lemma symmetricAlgebra_generator_mem_degree_one (A : Type u) (V : Type z) [CommRing A]
    [AddCommGroup V] [Module A V] (v : V) :
    SymmetricAlgebra.ι A V v ∈ symmetricPower A V 1 := by
  simp [symmetricPower]

/-- On a generator of the symmetric algebra the graded Laurent map multiplies by `T`. -/
public lemma gradedLaurentMapLarge_symmetricAlgebra_generator (A : Type u) (V : Type z)
    [CommRing A] [AddCommGroup V] [Module A V] (v : V) :
    gradedLaurentMapLarge A (SymmetricAlgebra A V) (symmetricPower A V)
      (SymmetricAlgebra.ι A V v) =
      LaurentPolynomial.C (SymmetricAlgebra.ι A V v) * LaurentPolynomial.T 1 := by
  simpa using gradedLaurentMapLarge_mem A _ (symmetricPower A V) 1 _
    (symmetricAlgebra_generator_mem_degree_one A V v)

/-- On a generator of the symmetric algebra the graded Laurent map multiplies by `T`, in the
small-universe form. -/
lemma gradedLaurentMap_symmetricAlgebra_generator (A V : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] (v : V) :
    Laurent.gradedLaurentMap A (SymmetricAlgebra A V) (symmetricPower A V)
      (SymmetricAlgebra.ι A V v) =
        LaurentPolynomial.C (SymmetricAlgebra.ι A V v) * LaurentPolynomial.T 1 := by
  show (DirectSum.liftRingHom _) (DirectSum.decompose (symmetricPower A V)
    (SymmetricAlgebra.ι A V v)) = _
  rw [DirectSum.decompose_of_mem (symmetricPower A V)
    (symmetricAlgebra_generator_mem_degree_one A V v)]
  simp [DirectSum.liftRingHom_apply]

/-- The transpose of a map between finite free modules, in the standard bases. -/
public noncomputable def transposeLinearMap {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) :
    (Fin m → A) →ₗ[A] (Fin n → A) :=
  LinearMap.pi fun i => ∑ j, d (Pi.single i 1) j • LinearMap.proj j

/-- The transpose is given in coordinates by the transposed matrix. -/
private lemma transposeLinearMap_apply {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (y : Fin m → A) (i : Fin n) :
    transposeLinearMap A d y i = ∑ j, y j * d (Pi.single i 1) j := by
  simp [transposeLinearMap, LinearMap.pi_apply, LinearMap.sum_apply, mul_comm]

/-- The transpose of a standard basis vector is the `j`-th column of `d`. -/
private lemma transposeLinearMap_single {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (j : Fin m) :
    transposeLinearMap A d (Pi.single j 1) = ∑ i, d (Pi.single i 1) j • Pi.single i 1 := by
  ext i
  simp [transposeLinearMap_apply, Pi.single_apply]

/-- The module of universal solutions of the relations imposed by `d`: the cokernel of the
transpose of `d`. -/
public abbrev universalSolutionModule {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) :=
  (Fin n → A) ⧸ LinearMap.range (transposeLinearMap A d)

/-- The symmetric algebra on the module of universal solutions of `d`. -/
public abbrev universalSolutionAlgebra {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) :=
  SymmetricAlgebra A (universalSolutionModule A d)

/-- The `i`-th universal solution, as an element of the universal solution algebra. -/
public noncomputable def universalSolutionVariable {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (i : Fin n) : universalSolutionAlgebra A d :=
  SymmetricAlgebra.ι A (universalSolutionModule A d)
    (Submodule.mkQ (LinearMap.range (transposeLinearMap A d)) (Pi.single i 1))

/-- The universal solutions satisfy the relations imposed by `d`. -/
private lemma universalSolution_relation {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (j : Fin m) :
    ∑ i, d (Pi.single i 1) j • universalSolutionVariable A d i = 0 := by
  let q : (Fin n → A) →ₗ[A] universalSolutionModule A d :=
    Submodule.mkQ (LinearMap.range (transposeLinearMap A d))
  have hq : q (transposeLinearMap A d (Pi.single j 1)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨Pi.single j 1, rfl⟩
  have hq' := congrArg (fun x : universalSolutionModule A d =>
    SymmetricAlgebra.ι A (universalSolutionModule A d) x) hq
  rw [transposeLinearMap_single] at hq'
  simpa [universalSolutionVariable, q] using hq'

/-- The map from the symmetric algebra on `V` to the symmetric algebra on its universe lift. -/
private noncomputable def symmetricAlgebraUp {V : Type u} (A : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] :
    SymmetricAlgebra A V →ₐ[A] SymmetricAlgebra A (ULift.{v} V) :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι A (ULift.{v} V)).comp
      (ULift.moduleEquiv.{u, u, v}.symm.toLinearMap))

/-- The map from the symmetric algebra on the universe lift of `V` back to that on `V`. -/
private noncomputable def symmetricAlgebraDown {V : Type u} (A : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] :
    SymmetricAlgebra A (ULift.{v} V) →ₐ[A] SymmetricAlgebra A V :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι A V).comp
      (ULift.moduleEquiv.{u, u, v}.toLinearMap))

/-- The universal solution algebra, with its carrier lifted to a larger universe. -/
public abbrev universalSolutionAlgebraLifted {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) :=
  SymmetricAlgebra A (ULift.{v} (universalSolutionModule A d))

/-- The `i`-th universal solution in the universe-lifted algebra. -/
public noncomputable def universalSolutionVariableLifted {n m : ℕ} (A : Type u)
    [CommRing A] (d : (Fin n → A) →ₗ[A] (Fin m → A)) (i : Fin n) :
    universalSolutionAlgebraLifted A d :=
  SymmetricAlgebra.ι A (ULift.{v} (universalSolutionModule A d))
    (ULift.up (Submodule.mkQ (LinearMap.range (transposeLinearMap A d)) (Pi.single i 1)))

/-- The universe-lifted universal solutions satisfy the relations imposed by `d`. -/
public lemma universalSolution_relation_lifted {n m : ℕ} (A : Type u)
    [CommRing A] (d : (Fin n → A) →ₗ[A] (Fin m → A)) (j : Fin m) :
    ∑ i, d (Pi.single i 1) j • universalSolutionVariableLifted A d i = 0 := by
  let upAlg := symmetricAlgebraUp (A := A) (V := universalSolutionModule A d)
  have hu (i : Fin n) : upAlg (universalSolutionVariable A d i) =
      universalSolutionVariableLifted A d i := by
    simp [upAlg, symmetricAlgebraUp, universalSolutionVariable,
      universalSolutionVariableLifted, SymmetricAlgebra.lift_ι_apply]
  have h := congrArg upAlg (universalSolution_relation A d j)
  rw [map_sum] at h
  simp only [map_smul, hu] at h
  rwa [map_zero] at h

/-- The element of `B ⊗[A] (Fin n → A)` with coordinates the given tuple. -/
noncomputable def tupleTensor {n : ℕ} (A : Type u) (B : Type v)
    [CommRing A] [CommRing B]
    [Algebra A B] (x : Fin n → B) : TensorProduct A B (Fin n → A) :=
  ∑ i, x i ⊗ₜ[A] Pi.single i 1

/-- Applying the base change of `d` to a coordinate tuple gives the matrix product of `d` with
that tuple. -/
lemma piScalarRight_baseChange_tupleTensor {n m : ℕ} (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (x : Fin n → B) (j : Fin m) :
    TensorProduct.piScalarRight A B B (Fin m)
        (d.baseChange B (tupleTensor A B x)) j =
      ∑ i, d (Pi.single i 1) j • x i := by
  simp [tupleTensor, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, LinearMap.baseChange_tmul]

/-- The tuple of universal solutions is killed by the base change of `d`. -/
lemma universalSolution_tuple_in_ker {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) :
    d.baseChange (universalSolutionAlgebra A d)
      (tupleTensor A (universalSolutionAlgebra A d)
        (universalSolutionVariable A d)) = 0 := by
  apply (TensorProduct.piScalarRight A (universalSolutionAlgebra A d)
    (universalSolutionAlgebra A d) (Fin m)).injective
  ext j
  rw [piScalarRight_baseChange_tupleTensor]
  exact universalSolution_relation A d j

/-- The linear map out of `Fin n → A` determined by the images of the standard basis. -/
public noncomputable def linearMapOfTuple {n : ℕ} (A : Type u) (C : Type z) [CommRing A]
    [AddCommGroup C] [Module A C] (x : Fin n → C) : (Fin n → A) →ₗ[A] C :=
  ∑ i, LinearMap.smulRight (LinearMap.proj i) (x i)

/-- The map determined by a tuple sends the `i`-th basis vector to the `i`-th entry. -/
lemma linearMapOfTuple_single {n : ℕ} (A : Type u) (C : Type z) [CommRing A]
    [AddCommGroup C] [Module A C] (x : Fin n → C) (i : Fin n) :
    linearMapOfTuple A C x (Pi.single i 1) = x i := by
  simp [linearMapOfTuple, LinearMap.proj_apply]

/-- The transpose is determined by its values on the standard basis. -/
private lemma transposeLinearMap_eq_sum_basis {n m : ℕ} (A : Type u) [CommRing A]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (y : Fin m → A) :
    transposeLinearMap A d y = ∑ j, y j • transposeLinearMap A d (Pi.single j 1) := by
  have hy : y = ∑ j, y j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  calc
    transposeLinearMap A d y =
        transposeLinearMap A d (∑ j, y j • Pi.single j 1) := congrArg _ hy
    _ = ∑ j, y j • transposeLinearMap A d (Pi.single j 1) := by simp

/-- Evaluating the map of a tuple on a transposed basis vector gives the `j`-th relation. -/
private lemma linearMapOfTuple_transpose_single {n m : ℕ} (A : Type u) (C : Type z) [CommRing A]
    [CommRing C] [Algebra A C] (d : (Fin n → A) →ₗ[A] (Fin m → A))
    (x : Fin n → C) (j : Fin m) :
    linearMapOfTuple A C x (transposeLinearMap A d (Pi.single j 1)) =
      ∑ i, d (Pi.single i 1) j • x i := by
  rw [transposeLinearMap_single]
  simp [linearMapOfTuple, LinearMap.proj_apply,
    Pi.single_apply]

/-- A tuple satisfying the relations of `d` induces a map out of the universal solution
module. -/
public noncomputable def universalSolutionLinearMap {n m : ℕ} (A : Type u) (C : Type z)
    [CommRing A] [CommRing C] [Algebra A C]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (x : Fin n → C)
    (hrel : ∀ j, ∑ i, d (Pi.single i 1) j • x i = 0) :
    universalSolutionModule A d →ₗ[A] C :=
  Submodule.liftQ (LinearMap.range (transposeLinearMap A d))
    (linearMapOfTuple A C x) (by
      rintro _ ⟨y, rfl⟩
      rw [transposeLinearMap_eq_sum_basis]
      simp [linearMapOfTuple_transpose_single, hrel])

/-- A tuple satisfying the relations of `d` induces an algebra map out of the universal
solution algebra. -/
public noncomputable def universalSolutionAlgHom {n m : ℕ} (A : Type u) (C : Type z)
    [CommRing A] [CommRing C] [Algebra A C]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (x : Fin n → C)
    (hrel : ∀ j, ∑ i, d (Pi.single i 1) j • x i = 0) :
    universalSolutionAlgebra A d →ₐ[A] C :=
  SymmetricAlgebra.lift (universalSolutionLinearMap A C d x hrel)

/-- The induced algebra map sends the `i`-th universal solution to the `i`-th entry of the
tuple. -/
public lemma universalSolutionAlgHom_variable {n m : ℕ} (A : Type u) (C : Type z)
    [CommRing A] [CommRing C] [Algebra A C]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (x : Fin n → C)
    (hrel : ∀ j, ∑ i, d (Pi.single i 1) j • x i = 0) (i : Fin n) :
    universalSolutionAlgHom A C d x hrel (universalSolutionVariable A d i) = x i := by
  simp [universalSolutionAlgHom, universalSolutionVariable,
    SymmetricAlgebra.lift_ι_apply, universalSolutionLinearMap,
    Submodule.liftQ_apply, linearMapOfTuple_single]

end AdequateFunctor
