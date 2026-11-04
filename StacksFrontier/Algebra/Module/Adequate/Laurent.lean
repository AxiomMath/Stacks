module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Adequate functors and the Laurent-polynomial test algebra

Base change along the Laurent polynomial algebra `A[T, T⁻¹]` detects the weight decomposition
of a module-valued functor that preserves flat base change.  This file isolates the
weight-space decomposition it produces and uses it to lift a natural transformation defined on
units.

## References

* [Stacks Project, Tag 06UY](https://stacks.math.columbia.edu/tag/06UY)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
-/

@[expose] public section

namespace AdequateFunctor.Laurent

section

open CategoryTheory
open scoped DirectSum

universe u


/-- The structure-ring functor on the double opposite of the category of commutative
`A`-algebras. -/
public abbrev algebraRingFunctor (A : Type u) [CommRing A] :
    (CommAlgCat.{u} A)ᵒᵖᵒᵖ ⥤ RingCat.{u} :=
  unopUnop (CommAlgCat.{u} A) ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙
    forget₂ CommRingCat.{u} RingCat.{u}

/-- A module-valued functor on commutative `A`-algebras. -/
public abbrev ModuleValuedFunctor (A : Type u) [CommRing A] :=
  PresheafOfModules.{u} (algebraRingFunctor A)

/-- The constant-polynomial algebra map `B → B[T,T⁻¹]`. -/
public noncomputable def constantLaurentMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] LaurentPolynomial B where
  toRingHom := LaurentPolynomial.C
  commutes' _ := rfl

/-- The algebra map from a graded algebra to its Laurent polynomial algebra which sends a
homogeneous element of degree `d` to that element times `T d`. -/
@[ega "II 8.3.9" "partial"]
public noncomputable def gradedLaurentMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
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
      change LaurentPolynomial.C ((x : B) * (y : B)) * LaurentPolynomial.T ((i + j : ℕ) : ℤ) = _
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

/-- The weight-`k` part of `F(B)` consists of those elements whose images under the constant
and grading maps differ by multiplication by `T k`. -/
@[stacks 06UY]
public def weightSpace (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (F : ModuleValuedFunctor A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    Set (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :=
  {ξ | (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) ξ =
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) ξ}

end

section

open CategoryTheory
open scoped TensorProduct

universe u v w


open AdequateFunctor.Laurent

/-- A module-valued functor preserves flat base change if its canonical map from extension of
scalars is an isomorphism.  The displayed condition on pure tensors identifies the isomorphism
with the canonical one. -/
public def PreservesFlatBaseChange (A : Type u) [CommRing A]
    (F : ModuleValuedFunctor A) : Prop :=
  ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C),
    letI : Algebra B C := f.toRingHom.toAlgebra
    Module.Flat B C →
      ∃ e : (C ⊗[B] F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[C]
          F.obj (Opposite.op (Opposite.op (CommAlgCat.of A C))),
        ∀ x, e (1 ⊗ₜ[B] x) = F.map ((CommAlgCat.ofHom f).op.op) x

/-- The `A`-algebra endomorphism of a nonnegatively graded algebra obtained by projecting onto
degree zero and including the degree-zero part back into the algebra. -/
public noncomputable def degreeZeroProjection (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] : B →ₐ[A] B where
  toRingHom := GradedRing.projZeroRingHom 𝒜
  commutes' a := by
    change GradedRing.projZeroRingHom 𝒜 (algebraMap A B a) = algebraMap A B a
    rw [GradedRing.projZeroRingHom_apply]
    rw [DirectSum.decompose_algebraMap]
    simp [DirectSum.algebraMap_apply]

private lemma gradedLaurentMap_of_mem (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (d : ℕ) (b : B) (hb : b ∈ 𝒜 d) :
    gradedLaurentMap A B 𝒜 b =
      LaurentPolynomial.C b * LaurentPolynomial.T (d : ℤ) := by
  show (DirectSum.liftRingHom _) (DirectSum.decompose 𝒜 b) = _
  rw [DirectSum.decompose_of_mem 𝒜 hb]
  simp [DirectSum.liftRingHom_apply]

private lemma gradedLaurentMap_of_mem_zero (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (b : B) (hb : b ∈ 𝒜 0) :
    gradedLaurentMap A B 𝒜 b = constantLaurentMap A B b := by
  rw [gradedLaurentMap_of_mem A B 𝒜 0 b hb, Nat.cast_zero, LaurentPolynomial.T_zero, mul_one]
  rfl

/-- Two algebra homomorphisms out of a graded algebra agree if they agree on homogeneous
elements. -/
private lemma algHom_ext_of_mem_graded {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (f g : B →ₐ[A] C)
    (h : ∀ d b, b ∈ 𝒜 d → f b = g b) : f = g := by
  classical
  ext b
  rw [← DirectSum.sum_support_decompose 𝒜 b, map_sum, map_sum]
  exact Finset.sum_congr rfl fun d _ ↦ h d _ (DirectSum.decompose 𝒜 b d).property

private lemma gradedLaurentMap_comp_degreeZeroProjection (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (gradedLaurentMap A B 𝒜).comp (degreeZeroProjection A B 𝒜) =
      (constantLaurentMap A B).comp (degreeZeroProjection A B 𝒜) := by
  apply AlgHom.ext
  intro b
  show (gradedLaurentMap A B 𝒜) (degreeZeroProjection A B 𝒜 b) =
    (constantLaurentMap A B) (degreeZeroProjection A B 𝒜 b)
  apply gradedLaurentMap_of_mem_zero
  show (GradedRing.projZeroRingHom 𝒜 b) ∈ 𝒜 0
  rw [GradedRing.projZeroRingHom_apply]
  exact (DirectSum.decompose 𝒜 b 0).property

private noncomputable def evalLaurentOne (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : LaurentPolynomial B →ₐ[A] B where
  toRingHom := LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
  commutes' a := by
    change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
      (LaurentPolynomial.C (algebraMap A B a)) = algebraMap A B a
    simp

private lemma evalLaurentOne_comp_constant (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    (evalLaurentOne A B).comp (constantLaurentMap A B) = AlgHom.id A B := by
  apply AlgHom.ext
  intro b
  show LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ) (LaurentPolynomial.C b) = b
  simp

private lemma evalLaurentOne_comp_graded (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (evalLaurentOne A B).comp (gradedLaurentMap A B 𝒜) = AlgHom.id A B := by
  refine algHom_ext_of_mem_graded 𝒜 _ _ fun d b hb ↦ ?_
  show (evalLaurentOne A B) (gradedLaurentMap A B 𝒜 b) = b
  rw [gradedLaurentMap_of_mem A B 𝒜 d b hb]
  show LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
    (LaurentPolynomial.C b * LaurentPolynomial.T (d : ℤ)) = b
  simp

private instance laurentFlat (B : Type u) [CommRing B] :
    Module.Flat B (LaurentPolynomial B) := Module.Flat.of_free

/-- Coefficients of a tensor with a Laurent polynomial in its left factor. -/
private noncomputable def laurentTensorCoefficients (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M] :
    (LaurentPolynomial B ⊗[B] M) ≃ₗ[B] (ℤ →₀ M) :=
  TensorProduct.congr (AddMonoidAlgebra.coeffLinearEquiv B) (.refl B M) ≪≫ₗ
    TensorProduct.finsuppScalarLeft B M ℤ

private lemma laurentTensorCoefficients_tmul (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M]
    (p : LaurentPolynomial B) (m : M) (k : ℤ) :
    laurentTensorCoefficients B M (p ⊗ₜ[B] m) k = p.coeff k • m := by
  simp [laurentTensorCoefficients]

private lemma laurentTensorCoefficients_symm_apply (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M] (y : ℤ →₀ M) :
    (laurentTensorCoefficients B M).symm y =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, hy, hz, Finsupp.sum_add_index]
    · simp
    · intro k hk m n
      simp [TensorProduct.tmul_add]
  | single k m =>
    apply (laurentTensorCoefficients B M).injective
    ext j
    simp [laurentTensorCoefficients_tmul, Finsupp.single_apply]

private lemma laurentTensorCoefficients_sum_tmul (B : Type u) [CommRing B]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module B N]
    (y : ℤ →₀ M) (f : ℤ → M → N) (hf : ∀ k, f k 0 = 0) (j : ℤ) :
    laurentTensorCoefficients B N
      (y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] f k m)) j =
      f j (y j) := by
  simp only [Finsupp.sum, map_sum]
  rw [Finset.sum_apply']
  simp_rw [laurentTensorCoefficients_tmul B N]
  simp only [LaurentPolynomial.T_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finsupp.mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  intro h
  simpa [h] using (hf j).symm

private lemma laurentCoefficients_sum_of_counit (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M]
    (δ : M → LaurentPolynomial B ⊗[B] M)
    (ε : (LaurentPolynomial B ⊗[B] M) →ₗ[B] M)
    (hε : ∀ k m, ε ((LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) = m)
    (hεδ : ∀ m, ε (δ m) = m) (x : M) :
    (laurentTensorCoefficients B M (δ x)).sum (fun _ m ↦ m) = x := by
  let y := laurentTensorCoefficients B M (δ x)
  have hδ : δ x = y.sum (fun k m ↦
      (LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) := by
    calc
      δ x = (laurentTensorCoefficients B M).symm y := by simp [y]
      _ = _ := laurentTensorCoefficients_symm_apply B M y
  have h := congrArg ε hδ
  simp only [map_sum, Finsupp.sum] at h
  simpa only [hεδ, hε, Finsupp.sum, y] using h.symm

private noncomputable def laurentCounit (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M] :
    (LaurentPolynomial B ⊗[B] M) →ₗ[B] M :=
  (Finsupp.lsum B (fun _ : ℤ ↦ LinearMap.id)).comp
    (laurentTensorCoefficients B M).toLinearMap

private lemma laurentCounit_tmul_T (B : Type u) [CommRing B]
    (M : Type u) [AddCommGroup M] [Module B M] (k : ℤ) (m : M) :
    laurentCounit B M ((LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) = m := by
  simp only [laurentCounit, LinearMap.coe_comp, Finsupp.coe_lsum, Finsupp.sum, LinearMap.id_coe,
    id_eq, LinearEquiv.coe_coe, Function.comp_apply, laurentTensorCoefficients_tmul,
    LaurentPolynomial.T_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finsupp.mem_support_iff, ↓reduceIte, ne_eq, ite_eq_left_iff, not_not]
  intro hm
  simp [hm]

private lemma flatBaseChange_tmul (A B C : Type u) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] (F : ModuleValuedFunctor A)
    (f : B →ₐ[A] C) :
    ∀ (e : (C ⊗[B] F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[C]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A C)))),
      (∀ x, e (1 ⊗ₜ[B] x) = F.map ((CommAlgCat.ofHom f).op.op) x) →
      ∀ c x, e (c ⊗ₜ[B] x) = c • F.map ((CommAlgCat.ofHom f).op.op) x := by
  intro e he c x
  have h : c ⊗ₜ[B] x = c • ((1 : C) ⊗ₜ[B] x) := by
    simp [TensorProduct.smul_tmul']
  rw [h, map_smul, he]
  rfl

private lemma laurentModule_eq (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    @Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMap A B).toRingHom.toAlgebra) =
      (AddMonoidAlgebra.instModule : Module B (LaurentPolynomial B)) := by
  apply Module.ext'
  intro b p
  show LaurentPolynomial.C b * p = b • p
  ext k
  rw [← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.coeff_single_zero_mul,
    AddMonoidAlgebra.coeff_smul_apply]
  exact (smul_eq_mul b (p.coeff k)).symm

private lemma laurentAddCommMonoid_eq (B : Type u) [CommRing B] :
    (CommRing.toCommSemiring.toAddCommMonoid : AddCommMonoid (LaurentPolynomial B)) =
      AddMonoidAlgebra.instAddCommMonoid := by
  rfl

private lemma laurentModule_heq (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    HEq
      (letI : AddCommMonoid (LaurentPolynomial B) :=
          (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
       letI : Algebra B (LaurentPolynomial B) :=
          (AdequateFunctor.Laurent.constantLaurentMap A B).toRingHom.toAlgebra
       (Algebra.toModule : Module B (LaurentPolynomial B)))
      (AddMonoidAlgebra.instModule : Module B (LaurentPolynomial B)) := by
  exact heq_of_eq (laurentModule_eq A B)

private noncomputable def tensorTransport (R : Type u) (P : Type v) (M : Type w)
    [CommRing R] [CommRing P] [Algebra R P] [AddCommGroup M] [Module R M]
    (s t : AddCommMonoid P) (ms : @Module R P _ s) (mt : @Module R P _ t)
    (hs : s = t) (hm : HEq ms mt) :
    (letI : AddCommMonoid P := s
     letI : Module R P := ms
     P ⊗[R] M) ≃ₗ[R]
    (letI : AddCommMonoid P := t
     letI : Module R P := mt
     P ⊗[R] M) := by
  cases hs
  cases hm
  exact LinearEquiv.refl R _

private lemma tensorTransport_tmul (R : Type u) (P : Type v) (M : Type w)
    [CommRing R] [CommRing P] [Algebra R P] [AddCommGroup M] [Module R M]
    (s t : AddCommMonoid P) (ms : @Module R P _ s) (mt : @Module R P _ t)
    (hs : s = t) (hm : HEq ms mt) (p : P) (m : M) :
    (tensorTransport R P M s t ms mt hs hm)
      (letI : AddCommMonoid P := s
       letI : Module R P := ms
       p ⊗ₜ[R] m) =
      (letI : AddCommMonoid P := t
       letI : Module R P := mt
       p ⊗ₜ[R] m) := by
  cases hs
  cases hm
  rfl

private lemma tensorTransport_symm_tmul (R : Type u) (P : Type v) (M : Type w)
    [CommRing R] [CommRing P] [Algebra R P] [AddCommGroup M] [Module R M]
    (s t : AddCommMonoid P) (ms : @Module R P _ s) (mt : @Module R P _ t)
    (hs : s = t) (hm : HEq ms mt) (p : P) (m : M) :
    (tensorTransport R P M s t ms mt hs hm).symm
      (letI : AddCommMonoid P := t
       letI : Module R P := mt
       p ⊗ₜ[R] m) =
      (letI : AddCommMonoid P := s
       letI : Module R P := ms
       p ⊗ₜ[R] m) := by
  apply (tensorTransport R P M s t ms mt hs hm).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (tensorTransport_tmul R P M s t ms mt hs hm p m).symm

private noncomputable def laurentTensorTransport (A B M : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M] :
    (letI : AddCommMonoid (LaurentPolynomial B) :=
        (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
     letI : Algebra B (LaurentPolynomial B) :=
        (AdequateFunctor.Laurent.constantLaurentMap A B).toRingHom.toAlgebra
     letI : Module B (LaurentPolynomial B) := Algebra.toModule
     LaurentPolynomial B ⊗[B] M) ≃ₗ[B] (LaurentPolynomial B ⊗[B] M) := by
  exact tensorTransport B (LaurentPolynomial B) M
    ((inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid)
    AddMonoidAlgebra.instAddCommMonoid
    (@Algebra.toModule B (LaurentPolynomial B) _ _
      ((AdequateFunctor.Laurent.constantLaurentMap A B).toRingHom.toAlgebra))
    AddMonoidAlgebra.instModule
    (laurentAddCommMonoid_eq B) (laurentModule_heq A B)

private lemma laurentTensorTransport_symm_tmul (A B M : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    (p : LaurentPolynomial B) (m : M) :
    (laurentTensorTransport A B M).symm (p ⊗ₜ[B] m) =
      (letI : AddCommMonoid (LaurentPolynomial B) :=
          (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
       letI : Algebra B (LaurentPolynomial B) :=
          (AdequateFunctor.Laurent.constantLaurentMap A B).toRingHom.toAlgebra
       letI : Module B (LaurentPolynomial B) := Algebra.toModule
       p ⊗ₜ[B] m) := by
  exact tensorTransport_symm_tmul B (LaurentPolynomial B) M
    ((inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid)
    AddMonoidAlgebra.instAddCommMonoid
    (@Algebra.toModule B (LaurentPolynomial B) _ _
      ((AdequateFunctor.Laurent.constantLaurentMap A B).toRingHom.toAlgebra))
    AddMonoidAlgebra.instModule
    (laurentAddCommMonoid_eq B) (laurentModule_heq A B) p m


private lemma laurentBaseChange (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A) (hF : PreservesFlatBaseChange A F) :
    letI : AddCommMonoid (LaurentPolynomial B) :=
      (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
    letI : Algebra B (LaurentPolynomial B) :=
      (constantLaurentMap A B).toRingHom.toAlgebra
    letI : Module B (LaurentPolynomial B) := Algebra.toModule
    ∃ e : (LaurentPolynomial B ⊗[B]
        F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
        F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))),
      ∀ x, e (1 ⊗ₜ[B] x) =
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x := by
  have hflat : @Module.Flat B (LaurentPolynomial B) _ _
      (@Algebra.toModule B (LaurentPolynomial B) _ _
        ((constantLaurentMap A B).toRingHom.toAlgebra)) := by
    rw [laurentModule_eq A B]
    exact laurentFlat B
  exact hF B (LaurentPolynomial B) (constantLaurentMap A B) hflat

private lemma laurentBaseChangeCanonical (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A) (hF : PreservesFlatBaseChange A F) :
    ∃ e : (LaurentPolynomial B ⊗[B]
        F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
        F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))),
      ∀ x, e (1 ⊗ₜ[B] x) =
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x := by
  classical
  obtain ⟨e, he⟩ := laurentBaseChange A B F hF
  let M := F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))
  let t := laurentTensorTransport A B M
  let e' : (LaurentPolynomial B ⊗[B] M) ≃+
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    { toEquiv := t.symm.toEquiv.trans e.toEquiv
      map_add' := by intro x y; simp [map_add] }
  have he' (x : M) : e' (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x := by
    show e (t.symm (1 ⊗ₜ[B] x)) = _
    rw [laurentTensorTransport_symm_tmul A B M]
    exact he x
  have he'_tmul (q : LaurentPolynomial B) (x : M) :
      e' (q ⊗ₜ[B] x) = q • F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x := by
    show e (t.symm (q ⊗ₜ[B] x)) = _
    rw [laurentTensorTransport_symm_tmul A B M]
    let : AddCommMonoid (LaurentPolynomial B) :=
      (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
    let : Algebra B (LaurentPolynomial B) :=
      (constantLaurentMap A B).toRingHom.toAlgebra
    let : Module B (LaurentPolynomial B) := Algebra.toModule
    exact flatBaseChange_tmul A B (LaurentPolynomial B) F
      (constantLaurentMap A B) e he q x
  let eₚ : (LaurentPolynomial B ⊗[B] M) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) := {
    toAddEquiv := e'
    map_smul' := by
      intro p z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul q x =>
          rw [TensorProduct.smul_tmul']
          show e' ((p * q) ⊗ₜ[B] x) = p • e' (q ⊗ₜ[B] x)
          rw [he'_tmul, he'_tmul, mul_smul]
          rfl
      | add z w hz hw =>
          rw [smul_add]
          show e' (p • z + p • w) = p • e' (z + w)
          rw [e'.map_add, e'.map_add, smul_add]
          exact congrArg₂ (· + ·) hz hw
  }
  exact ⟨eₚ, he'⟩

private lemma laurentBaseChange_weightedSum (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (e : (LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (he : ∀ x, e (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x)
    (y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    e ((laurentTensorCoefficients B
      (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))).symm y) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
  rw [laurentTensorCoefficients_symm_apply]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact flatBaseChange_tmul A B (LaurentPolynomial B) F
    (constantLaurentMap A B) e he (LaurentPolynomial.T k) (y k)

/-- Functoriality along two composites that agree as algebra maps gives the same result. -/
private lemma map_map_eq_of_comp_eq (A : Type u) [CommRing A] (F : ModuleValuedFunctor A)
    {B C C' D : Type u} [CommRing B] [CommRing C] [CommRing C'] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A C'] [Algebra A D]
    (u : B →ₐ[A] C) (v : C →ₐ[A] D) (u' : B →ₐ[A] C') (v' : C' →ₐ[A] D)
    (h : v.comp u = v'.comp u') (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom v).op.op) (F.map ((CommAlgCat.ofHom u).op.op) x) =
      F.map ((CommAlgCat.ofHom v').op.op) (F.map ((CommAlgCat.ofHom u').op.op) x) := by
  rw [← F.map_comp_apply, ← F.map_comp_apply]
  exact congrArg (fun p : B →ₐ[A] D ↦ F.map (CommAlgCat.ofHom p).op.op x) h

/-- Functoriality along an algebra map with a left inverse is a section. -/
private lemma map_map_eq_self_of_comp_eq_id (A : Type u) [CommRing A] (F : ModuleValuedFunctor A)
    {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (u : B →ₐ[A] C) (v : C →ₐ[A] B) (h : v.comp u = AlgHom.id A B)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom v).op.op) (F.map ((CommAlgCat.ofHom u).op.op) x) = x := by
  rw [map_map_eq_of_comp_eq A F u v (AlgHom.id A B) (AlgHom.id A B) h x]
  have : (CommAlgCat.ofHom (AlgHom.id A B)).op.op = 𝟙 _ := rfl
  rw [this]
  simp
  rfl

private lemma laurentBaseChange_eval_tmul_T (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (e : (LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (he : ∀ x, e (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x)
    (k : ℤ) (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op)
      (e ((LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m)) = m := by
  rw [flatBaseChange_tmul A B (LaurentPolynomial B) F
    (constantLaurentMap A B) e he]
  let m' : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m
  show F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') = m
  rw [F.map_smul]
  have ht : evalLaurentOne A B (LaurentPolynomial.T k) = 1 := by
    show LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ) (LaurentPolynomial.T k) = 1
    simp
  show evalLaurentOne A B (LaurentPolynomial.T k) •
      F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op) m' = m
  rw [ht, one_smul, map_map_eq_self_of_comp_eq_id A F _ _ (evalLaurentOne_comp_constant A B)]

private lemma laurentBaseChange_eval (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (e : (LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (he : ∀ x, e (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x)
    (z : LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op) (e z) =
      laurentCounit B (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) z := by
  let y := laurentTensorCoefficients B
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) z
  have hz : z = y.sum (fun k m ↦
      (LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) := by
    calc
      z = (laurentTensorCoefficients B _).symm y := by simp [y]
      _ = _ := laurentTensorCoefficients_symm_apply B _ y
  rw [hz]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact (laurentBaseChange_eval_tmul_T A B F e he k (y k)).trans
    (laurentCounit_tmul_T B _ k (y k)).symm

private lemma laurentBaseChange_eval_graded (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (he : ∀ x, e (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    laurentCounit B (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
      (e.symm (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x)) = x := by
  rw [← laurentBaseChange_eval A B F e he]
  let m' : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x
  show F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op) (e (e.symm m')) = x
  rw [e.apply_symm_apply]
  exact map_map_eq_self_of_comp_eq_id A F _ _ (evalLaurentOne_comp_graded A B 𝒜) x

private noncomputable def outerTUnit (B : Type u) [CommRing B] :
    (LaurentPolynomial (LaurentPolynomial B))ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

private noncomputable def innerTUnit (B : Type u) [CommRing B] :
    (LaurentPolynomial (LaurentPolynomial B))ˣ where
  val := LaurentPolynomial.C (LaurentPolynomial.T 1)
  inv := LaurentPolynomial.C (LaurentPolynomial.T (-1))
  val_inv := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  inv_val := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num

private lemma outerTUnit_zpow (B : Type u) [CommRing B] (k : ℤ) :
    ((outerTUnit B ^ k : (LaurentPolynomial (LaurentPolynomial B))ˣ) :
      LaurentPolynomial (LaurentPolynomial B)) =
      LaurentPolynomial.T k := by
  induction k using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    show LaurentPolynomial.T k * LaurentPolynomial.T 1 = LaurentPolynomial.T (k + 1)
    rw [← LaurentPolynomial.T_add]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    show (LaurentPolynomial.T (-(k : ℤ)) : LaurentPolynomial (LaurentPolynomial B)) *
      LaurentPolynomial.T (-1) = LaurentPolynomial.T (-(k : ℤ) - 1)
    rw [← LaurentPolynomial.T_add]
    congr 1

private lemma innerTUnit_zpow (B : Type u) [CommRing B] (k : ℤ) :
    ((innerTUnit B ^ k : (LaurentPolynomial (LaurentPolynomial B))ˣ) :
      LaurentPolynomial (LaurentPolynomial B)) =
      LaurentPolynomial.C (LaurentPolynomial.T k) := by
  induction k using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    show LaurentPolynomial.C (LaurentPolynomial.T k) *
      LaurentPolynomial.C (LaurentPolynomial.T 1) =
      LaurentPolynomial.C (LaurentPolynomial.T (k + 1))
    rw [← map_mul, ← LaurentPolynomial.T_add]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    show LaurentPolynomial.C (LaurentPolynomial.T (-(k : ℤ)) : LaurentPolynomial B) *
      LaurentPolynomial.C (LaurentPolynomial.T (-1) : LaurentPolynomial B) =
      LaurentPolynomial.C (LaurentPolynomial.T (-(k : ℤ) - 1) : LaurentPolynomial B)
    rw [← map_mul, ← LaurentPolynomial.T_add]
    congr 2

private noncomputable def diagonalLaurentMap (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : LaurentPolynomial B →ₐ[A]
      LaurentPolynomial (LaurentPolynomial B) where
  toRingHom := LaurentPolynomial.eval₂
    ((constantLaurentMap A (LaurentPolynomial B)).toRingHom.comp
      (constantLaurentMap A B).toRingHom)
    (outerTUnit B * innerTUnit B)
  commutes' a := by
    rw [← (constantLaurentMap A B).commutes a]
    change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C (algebraMap A B a)) = _
    rw [LaurentPolynomial.eval₂_C]
    change (constantLaurentMap A (LaurentPolynomial B))
      ((constantLaurentMap A B) (algebraMap A B a)) = _
    rw [(constantLaurentMap A B).commutes]
    exact (constantLaurentMap A (LaurentPolynomial B)).commutes a

private noncomputable def gradedOuterLaurentMap (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    LaurentPolynomial B →ₐ[A] LaurentPolynomial (LaurentPolynomial B) where
  toRingHom := LaurentPolynomial.eval₂
    ((constantLaurentMap A (LaurentPolynomial B)).toRingHom.comp
      (gradedLaurentMap A B 𝒜).toRingHom)
    (outerTUnit B)
  commutes' a := by
    rw [← (constantLaurentMap A B).commutes a]
    change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C (algebraMap A B a)) = _
    rw [LaurentPolynomial.eval₂_C]
    change (constantLaurentMap A (LaurentPolynomial B))
      ((gradedLaurentMap A B 𝒜) (algebraMap A B a)) = _
    rw [(gradedLaurentMap A B 𝒜).commutes]
    exact (constantLaurentMap A (LaurentPolynomial B)).commutes a

private lemma diagonalLaurentMap_C (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (b : B) :
    diagonalLaurentMap A B (LaurentPolynomial.C b) =
      LaurentPolynomial.C (LaurentPolynomial.C b) := by
  show (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C b) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma gradedOuterLaurentMap_C (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (b : B) :
    gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.C b) =
      LaurentPolynomial.C (gradedLaurentMap A B 𝒜 b) := by
  show (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C b) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma diagonalLaurentMap_T (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (k : ℤ) :
    diagonalLaurentMap A B (LaurentPolynomial.T k) =
      LaurentPolynomial.T k * LaurentPolynomial.C (LaurentPolynomial.T k) := by
  show (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T k) = _
  rw [LaurentPolynomial.eval₂_T,
    mul_zpow (outerTUnit B) (innerTUnit B) k, Units.val_mul,
    outerTUnit_zpow, innerTUnit_zpow]

private lemma gradedOuterLaurentMap_T (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  show (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T k) = _
  rw [LaurentPolynomial.eval₂_T, outerTUnit_zpow]

private lemma diagonal_comp_graded (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (diagonalLaurentMap A B).comp (gradedLaurentMap A B 𝒜) =
      (gradedOuterLaurentMap A B 𝒜).comp (gradedLaurentMap A B 𝒜) := by
  refine algHom_ext_of_mem_graded 𝒜 _ _ fun d b hb ↦ ?_
  show diagonalLaurentMap A B (gradedLaurentMap A B 𝒜 b) =
    gradedOuterLaurentMap A B 𝒜 (gradedLaurentMap A B 𝒜 b)
  rw [gradedLaurentMap_of_mem A B 𝒜 d b hb]
  rw [map_mul, map_mul, diagonalLaurentMap_C, diagonalLaurentMap_T,
    gradedOuterLaurentMap_C, gradedOuterLaurentMap_T]
  rw [gradedLaurentMap_of_mem A B 𝒜 d b hb]
  rw [map_mul]
  ring

private lemma diagonal_comp_constant (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    (diagonalLaurentMap A B).comp (constantLaurentMap A B) =
      (constantLaurentMap A (LaurentPolynomial B)).comp (constantLaurentMap A B) := by
  apply AlgHom.ext
  intro b
  exact diagonalLaurentMap_C A B b

private lemma gradedOuter_comp_constant (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (gradedOuterLaurentMap A B 𝒜).comp (constantLaurentMap A B) =
      (constantLaurentMap A (LaurentPolynomial B)).comp (gradedLaurentMap A B 𝒜) := by
  apply AlgHom.ext
  intro b
  exact gradedOuterLaurentMap_C A B 𝒜 b

private lemma map_gradedOuter_weightedTerm (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
      ((LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) =
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op)
          (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) m) := by
  let m' : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m
  show F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') = _
  rw [F.map_smul]
  show gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.T k) •
    F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op) m' = _
  rw [gradedOuterLaurentMap_T]
  show (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
    F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
      (F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) = _
  rw [map_map_eq_of_comp_eq A F _ _ _ _ (gradedOuter_comp_constant A B 𝒜) m]
  rfl

private lemma map_diagonal_weightedTerm (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A) (k : ℤ)
    (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
      ((LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) =
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op)
          ((LaurentPolynomial.T k : LaurentPolynomial B) •
            F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
  let m' : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m
  show F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') =
    (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op)
        ((LaurentPolynomial.T k : LaurentPolynomial B) • m')
  rw [F.map_smul]
  show diagonalLaurentMap A B (LaurentPolynomial.T k) •
    F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op) m' = _
  rw [diagonalLaurentMap_T]
  have hc : F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op) m' =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) m' := by
    exact map_map_eq_of_comp_eq A F _ _ _ _ (diagonal_comp_constant A B) m
  rw [hc]
  rw [F.map_smul]
  let m'' : F.obj (Opposite.op (Opposite.op
      (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))) :=
    F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) m'
  show ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) *
      LaurentPolynomial.C (LaurentPolynomial.T k)) • m'' =
    (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
      (LaurentPolynomial.C (LaurentPolynomial.T k)) • m''
  exact mul_smul (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B))
    (LaurentPolynomial.C (LaurentPolynomial.T k)) m''

private lemma outerBaseChange_gradedTerm (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
        ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))))
    (he : ∀ z, e (1 ⊗ₜ[LaurentPolynomial B] z) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) z)
    (k : ℤ) (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    e ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
      LaurentPolynomial B]
        F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) m) =
      F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
        ((LaurentPolynomial.T k : LaurentPolynomial B) •
          F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
  let m' : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) m
  show e ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
    LaurentPolynomial B] m') = _
  rw [flatBaseChange_tmul A (LaurentPolynomial B)
    (LaurentPolynomial (LaurentPolynomial B)) F
    (constantLaurentMap A (LaurentPolynomial B)) e he]
  exact (map_gradedOuter_weightedTerm A B F 𝒜 k m).symm

private lemma outerBaseChange_diagonalTerm (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
        ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))))
    (he : ∀ z, e (1 ⊗ₜ[LaurentPolynomial B] z) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) z)
    (k : ℤ) (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    e ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
      LaurentPolynomial B]
        ((LaurentPolynomial.T k : LaurentPolynomial B) •
          F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m)) =
      F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
        ((LaurentPolynomial.T k : LaurentPolynomial B) •
          F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
  let m' : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m
  show e ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
    LaurentPolynomial B] m') = _
  rw [flatBaseChange_tmul A (LaurentPolynomial B)
    (LaurentPolynomial (LaurentPolynomial B)) F
    (constantLaurentMap A (LaurentPolynomial B)) e he]
  exact (map_diagonal_weightedTerm A B F k m).symm

private lemma laurentCoefficients_eq_of_tensor_sum (R : Type u) [CommRing R]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R N]
    (y : ℤ →₀ M) (f g : ℤ → M → N)
    (hf : ∀ k, f k 0 = 0) (hg : ∀ k, g k 0 = 0)
    (h : (y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial R) ⊗ₜ[R]
        f k m) : LaurentPolynomial R ⊗[R] N) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial R) ⊗ₜ[R] g k m)) :
    ∀ k, f k (y k) = g k (y k) := by
  intro k
  have hk := congrArg (fun z : LaurentPolynomial R ⊗[R] N ↦
    laurentTensorCoefficients R N z k) h
  rw [laurentTensorCoefficients_sum_tmul R M N y f hf k,
    laurentTensorCoefficients_sum_tmul R M N y g hg k] at hk
  exact hk

private lemma finsupp_sum_map_congr (M N P Q : Type u)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (y : ℤ →₀ M) (f : ℤ → M → N) (g : ℤ → M → P)
    (L : N →+ Q) (K : P →+ Q) (h : ∀ k m, L (f k m) = K (g k m)) :
    L (y.sum f) = K (y.sum g) := by
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl (fun k hk ↦ h k (y k))

-- The coefficient comparison normalizes two nested Laurent tensor expansions.
private lemma weightCoefficients_of_expansion (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
        ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))))
    (he : ∀ z, e (1 ⊗ₜ[LaurentPolynomial B] z) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) z)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hy : F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m)) :
    ∀ k, y k ∈ weightSpace A B F 𝒜 k := by
  have hcomm :
      F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
        (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) =
      F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
        (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) :=
    map_map_eq_of_comp_eq A F _ _ _ _ (diagonal_comp_graded A B 𝒜).symm x
  let gradedValue (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) m
  let weightedValue (k : ℤ)
      (m : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m
  have hs :
      y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] gradedValue m) =
      y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] weightedValue k m) := by
    have hG : e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] gradedValue m)) =
      F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
        (y.sum weightedValue) := by
      exact finsupp_sum_map_congr _ _ _ _ y
        (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] gradedValue m) weightedValue e.toLinearMap.toAddMonoidHom
        (F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)).toAddMonoidHom
        (outerBaseChange_gradedTerm A B F 𝒜 e he)
    have hD : e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] weightedValue k m)) =
      F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
        (y.sum weightedValue) := by
      exact finsupp_sum_map_congr _ _ _ _ y
        (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] weightedValue k m) weightedValue e.toLinearMap.toAddMonoidHom
        (F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)).toAddMonoidHom
        (outerBaseChange_diagonalTerm A B F e he)
    apply e.injective
    calc
      e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] gradedValue m)) =
        F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
          (y.sum weightedValue) := hG
      _ = F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
          (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) := by
            rw [hy]
            simp only [weightedValue]
            rfl
      _ = F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
          (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) := hcomm
      _ = F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
          (y.sum weightedValue) := by
            rw [hy]
            simp only [weightedValue]
            rfl
      _ = e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] weightedValue k m)) := hD.symm
  have hz₁ : ∀ (j : ℤ), gradedValue
      (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) = 0 := by
    intro j
    exact map_zero _
  have hz₂ : ∀ (j : ℤ), weightedValue j
      (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) = 0 := by
    intro j
    show (LaurentPolynomial.T j : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op)
        (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) = 0
    rw [map_zero]
    exact smul_zero _
  have hcoeff := laurentCoefficients_eq_of_tensor_sum (LaurentPolynomial B)
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    y (fun _ m ↦ gradedValue m) weightedValue hz₁ hz₂ hs
  intro k
  show weightedValue k (y k) = gradedValue (y k)
  exact (hcoeff k).symm

private lemma map_sum_of_weights (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hy : ∀ k, y k ∈ weightSpace A B F 𝒜 k) :
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op)
      (y.sum (fun _ m ↦ m)) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact (hy k).symm

private lemma weightDecomposition_unique (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (he : ∀ x, e (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (y z : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hy : ∀ k, y k ∈ weightSpace A B F 𝒜 k)
    (hz : ∀ k, z k ∈ weightSpace A B F 𝒜 k)
    (hyx : y.sum (fun _ m ↦ m) = x) (hzx : z.sum (fun _ m ↦ m) = x) : y = z := by
  apply (laurentTensorCoefficients B
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))).symm.injective
  apply e.injective
  rw [laurentBaseChange_weightedSum A B F e he y,
    laurentBaseChange_weightedSum A B F e he z]
  rw [← map_sum_of_weights A B F 𝒜 y hy,
    ← map_sum_of_weights A B F 𝒜 z hz, hyx, hzx]

/-- Every element of the value of a flat-base-change-compatible module-valued functor on a
graded algebra has a unique finite decomposition into elements of its integer weight spaces. -/
@[stacks 06UZ "part (1)"]
public lemma existsUnique_finsupp_weightSpace_eq (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor A) (hF : PreservesFlatBaseChange A F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    ∃! y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))),
      (∀ k, y k ∈ weightSpace A B F 𝒜 k) ∧ y.sum (fun _ z ↦ z) = x := by
  classical
  obtain ⟨e₁, he₁⟩ := laurentBaseChangeCanonical A B F hF
  obtain ⟨e₂, he₂⟩ := laurentBaseChangeCanonical A (LaurentPolynomial B) F hF
  let z : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) :=
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x
  let y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))) :=
    laurentTensorCoefficients B
      (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) (e₁.symm z)
  have hy : F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
    show z = y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m)
    have hzy : z = e₁ ((laurentTensorCoefficients B
        (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))).symm y) := by
      rw [← e₁.apply_symm_apply z]
      congr 1
      simp [y]
    exact hzy.trans (laurentBaseChange_weightedSum A B F e₁ he₁ y)
  have hw : ∀ k, y k ∈ weightSpace A B F 𝒜 k :=
    weightCoefficients_of_expansion A B F 𝒜 e₂ he₂ x y hy
  have hsum : y.sum (fun _ m ↦ m) = x := by
    exact laurentCoefficients_sum_of_counit B
      (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
      (fun m ↦ e₁.symm
        (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) m))
      (laurentCounit B
        (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))))
      (laurentCounit_tmul_T B
        (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))))
      (laurentBaseChange_eval_graded A B F 𝒜 e₁ he₁) x
  refine ⟨y, ⟨hw, hsum⟩, ?_⟩
  intro y' hy'
  exact weightDecomposition_unique A B F 𝒜 e₁ he₁ x y' y
    hy'.1 hw hy'.2 hsum

/-- The endomorphism induced by projection of a graded algebra onto degree zero takes every
element of the functor's value into its weight-zero space. -/
@[stacks 06UZ "part (2)"]
public lemma map_degreeZeroProjection_mem_weightSpace_zero (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom (degreeZeroProjection A B 𝒜)).op.op) x ∈
      weightSpace A B F 𝒜 0 := by
  show (LaurentPolynomial.T 0 : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op)
        (F.map ((CommAlgCat.ofHom (degreeZeroProjection A B 𝒜)).op.op) x) =
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op)
        (F.map ((CommAlgCat.ofHom (degreeZeroProjection A B 𝒜)).op.op) x)
  rw [LaurentPolynomial.T_zero, one_smul]
  exact map_map_eq_of_comp_eq A F _ _ _ _ (gradedLaurentMap_comp_degreeZeroProjection A B 𝒜).symm x

end

section

open CategoryTheory Opposite

universe u v


/-- The functor sending an `A`-algebra to its underlying commutative ring. The
double opposite presents it in the variance required by `PresheafOfModules`. -/
public abbrev algebraCommRingFunctor (A : Type u) [CommRing A] :
    ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} :=
  (opOpEquivalence (CommAlgCat.{u} A)).functor ⋙
    forget₂ (CommAlgCat.{u} A) CommRingCat.{u}


attribute [local instance 0] CategoryTheory.ReflQuiver.toQuiver

/-- An additive natural transformation of module-valued functors which commutes
with multiplication by units is induced by a morphism of module-valued
functors, provided the target commutes with flat base change. -/
@[stacks 06V5]
public theorem naturalTransformation_lifts_of_units_of_flatBaseChange
    (A : Type u) [CommRing A]
    (F G : PresheafOfModules.{v} (algebraRingFunctor A))
    (φ : F.presheaf ⟶ G.presheaf)
    (hunit : ∀ (B : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ)
      (x : F.obj B) (a : Units ((algebraRingFunctor A).obj B)),
      φ.app B ((a : (algebraRingFunctor A).obj B) • x) =
        (a : (algebraRingFunctor A).obj B) • (φ.app B x : G.obj B))
    (hbase : ∀ {B B' : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ} (f : B ⟶ B'),
      letI : Algebra ((algebraCommRingFunctor A).obj B)
          ((algebraCommRingFunctor A).obj B') :=
        ((algebraCommRingFunctor A).map f).hom.toAlgebra
      Module.Flat ((algebraCommRingFunctor A).obj B)
          ((algebraCommRingFunctor A).obj B') →
        ∃ e : TensorProduct ((algebraCommRingFunctor A).obj B)
              ((algebraCommRingFunctor A).obj B') (G.obj B) ≃ₗ[
                (algebraCommRingFunctor A).obj B'] G.obj B',
          ∀ x : G.obj B,
            e ((1 : (algebraCommRingFunctor A).obj B') ⊗ₜ[
              (algebraCommRingFunctor A).obj B] x) = G.map f x) :
    ∃ ψ : F ⟶ G,
      (PresheafOfModules.toPresheaf (algebraRingFunctor A)).map ψ = φ := by
  let ψ : F ⟶ G :=
    { app := fun B ↦
        ModuleCat.ofHom
        { toFun := φ.app B
          map_add' := (φ.app B).hom.map_add
          map_smul' := by
            intro b x
            rcases B with ⟨B⟩
            rcases B with ⟨B⟩
            change B at b
            by_cases hR : Nontrivial B
            swap
            · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp hR
              let : Subsingleton (G.obj (Opposite.op (Opposite.op B))) :=
                Module.subsingleton B _
              exact Subsingleton.elim _ _
            let : Nontrivial B := hR
            let p : Polynomial B := Polynomial.X ^ 2 -
              Polynomial.C b * Polynomial.X + 1
            have hpdeg : p.IsMonicOfDegree 2 := Polynomial.isMonicOfDegree_sub_add_two b 1
            have hp : p.Monic := hpdeg.monic
            let S := AdjoinRoot p
            let algAS : Algebra A S :=
              ((algebraMap B S).comp (algebraMap A B)).toAlgebra
            let g : B →ₐ[A] S :=
              { algebraMap B S with commutes' := fun _ ↦ rfl }
            let B' : ((CommAlgCat A)ᵒᵖ)ᵒᵖ :=
              Opposite.op (Opposite.op (CommAlgCat.of A S))
            let f : Opposite.op (Opposite.op B) ⟶ B' :=
              (ConcreteCategory.ofHom g : B ⟶ CommAlgCat.of A S).op.op
            let r : S := AdjoinRoot.root p
            have hr : r * (algebraMap B S b - r) = 1 := by
              have hroot : r ^ 2 - algebraMap B S b * r + 1 = 0 := by
                have h : Polynomial.aeval r p = 0 :=
                  (AdjoinRoot.aeval_eq p).trans AdjoinRoot.mk_self
                simpa only [p, map_add, map_sub, map_pow, map_mul,
                  Polynomial.aeval_X, Polynomial.aeval_C, map_one] using h
              rw [mul_sub]
              linear_combination -hroot
            have hr' : (algebraMap B S b - r) * r = 1 := by simpa only [mul_comm] using hr
            let ur : Units S := ⟨r, algebraMap B S b - r, hr, hr'⟩
            let us : Units S := ⟨algebraMap B S b - r, r, hr', hr⟩
            have hsum : (ur : S) + (us : S) = algebraMap B S b := by dsimp [ur, us]; abel
            have hff₀ : (algebraMap B S).FaithfullyFlat := by
              let : Module.Free B S := hp.free_adjoinRoot
              let : Nontrivial S := by
                exact (AdjoinRoot.of.injective_of_monic_of_degree_pos hp (by
                  rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpdeg.natDegree_eq]
                  norm_num)).nontrivial
              rw [RingHom.faithfullyFlat_algebraMap_iff]
              infer_instance
            let q := ((algebraCommRingFunctor A).map f).hom
            have hq : q = algebraMap B S := by rfl
            have hff : q.FaithfullyFlat := by rwa [hq]
            let : Algebra ((algebraCommRingFunctor A).obj
                (Opposite.op (Opposite.op B)))
                ((algebraCommRingFunctor A).obj B') := q.toAlgebra
            obtain ⟨e, he⟩ := hbase f (by
              exact RingHom.FaithfullyFlat.flat hff)
            have hinj : Function.Injective (fun y : G.obj (Opposite.op (Opposite.op B)) ↦
                e (1 ⊗ₜ[↑((algebraCommRingFunctor A).obj
                  (Opposite.op (Opposite.op B)))] y)) := e.injective.comp
              (faithfullyFlat_tensor_mk_injective
                q hff (G.obj (Opposite.op (Opposite.op B))))
            have hGinj : Function.Injective (G.map f) := by
              intro y z hyz
              apply hinj
              dsimp only
              rw [he y, he z]
              exact hyz
            have hnat (z : F.obj (Opposite.op (Opposite.op B))) :
                φ.app B' (F.map f z) =
                  G.map f (φ.app (Opposite.op (Opposite.op B)) z) :=
              ConcreteCategory.congr_hom (φ.naturality f) z
            apply hGinj
            rw [← hnat (b • x), F.map_smul]
            simp only [RingHom.id_apply]
            let y : G.obj (Opposite.op (Opposite.op B)) :=
              φ.app (Opposite.op (Opposite.op B)) x
            show φ.app B' ((algebraRingFunctor A).map f b • F.map f x) =
              G.map f (b • y)
            rw [G.map_smul]
            let φ' : F.obj B' →+ G.obj B' :=
              { toFun := fun z ↦ φ.app B' z
                map_zero' := (φ.app B').hom.map_zero
                map_add' := (φ.app B').hom.map_add }
            show φ' (q b • F.map f x) = q b • G.map f y
            rw [hq]
            -- `φ'` bundles `φ.app B'` so that the scalar action on `G.obj B'`
            -- resolves; the cost is that `hunit` and `hnat`, stated for
            -- `φ.app B'`, no longer match syntactically under its coercion, and
            -- their scalar actions come from a different (defeq) instance path.
            -- Restating each step in the goal's own spelling and discharging it
            -- by a *term* lets definitional unification absorb that, which is
            -- what `erw` was doing here before.
            have hmapAdd : φ' ((ur : S) • F.map f x + (us : S) • F.map f x) =
                φ' ((ur : S) • F.map f x) + φ' ((us : S) • F.map f x) :=
              φ'.map_add _ _
            have hur : φ' ((ur : S) • F.map f x) = (ur : S) • φ' (F.map f x) :=
              hunit B' (F.map f x) ur
            have hus : φ' ((us : S) • F.map f x) = (us : S) • φ' (F.map f x) :=
              hunit B' (F.map f x) us
            have hu : φ' ((algebraMap B S b) • F.map f x) =
                (algebraMap B S b) • φ' (F.map f x) := by
              rw [← hsum, add_smul, add_smul, hmapAdd, hur, hus]
            have hnat' : φ' (F.map f x) = G.map f y := hnat x
            rw [hu, hnat']
            rfl }
      naturality := by
        intro B B' f
        ext x
        exact CategoryTheory.congr_fun (φ.naturality f) x }
  refine ⟨ψ, ?_⟩
  ext B x
  rfl

end

end AdequateFunctor.Laurent

end
