module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Algebra.Module.Adequate.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Laurent weight decomposition at independent universes

`StacksFrontier/Algebra/Module/Adequate/Laurent.lean` proves the weight decomposition of
Tag 06UZ for a module-valued functor whose values live in the same universe as the
algebras it is defined on.  The adequacy predicates of
`StacksFrontier/Algebra/Module/Adequate/Defs.lean`, by contrast, are stated for module-valued
functors whose value universe is independent of the algebra universe.  This file re-derives
the weight decomposition in that generality.

The development is carried out for a base ring `A : Type u`, an algebra universe `uB` and a
value universe `uM`, all three unrelated; the shape wanted by `Defs.lean`, namely
`AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`, is the instance
`uB = max u v`, `uM = max u v w`, recorded at the end of the file.

## References

* [Stacks Project, Tag 06UY](https://stacks.math.columbia.edu/tag/06UY)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
-/

@[expose] public section

namespace AdequateFunctor.LaurentLarge

section Coefficients

open scoped TensorProduct

universe ur um un uq

/-- Coefficients of a tensor with a Laurent polynomial in its left factor.  Unlike the
diagonal version, the ring and the module may live in unrelated universes. -/
private noncomputable def laurentTensorCoefficients (B : Type ur) [CommRing B]
    (M : Type um) [AddCommGroup M] [Module B M] :
    (LaurentPolynomial B ⊗[B] M) ≃ₗ[B] (ℤ →₀ M) :=
  TensorProduct.congr (AddMonoidAlgebra.coeffLinearEquiv B) (.refl B M) ≪≫ₗ
    TensorProduct.finsuppScalarLeft B M ℤ

private lemma laurentTensorCoefficients_tmul (B : Type ur) [CommRing B]
    (M : Type um) [AddCommGroup M] [Module B M]
    (p : LaurentPolynomial B) (m : M) (k : ℤ) :
    laurentTensorCoefficients B M (p ⊗ₜ[B] m) k = p.coeff k • m := by
  simp [laurentTensorCoefficients]

private lemma laurentTensorCoefficients_symm_apply (B : Type ur) [CommRing B]
    (M : Type um) [AddCommGroup M] [Module B M] (y : ℤ →₀ M) :
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

private lemma laurentTensorCoefficients_sum_tmul (B : Type ur) [CommRing B]
    (M : Type um) (N : Type un) [AddCommGroup M] [AddCommGroup N] [Module B N]
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

private noncomputable def laurentCounit (B : Type ur) [CommRing B]
    (M : Type um) [AddCommGroup M] [Module B M] :
    (LaurentPolynomial B ⊗[B] M) →ₗ[B] M :=
  (Finsupp.lsum B (fun _ : ℤ ↦ LinearMap.id)).comp
    (laurentTensorCoefficients B M).toLinearMap

private lemma laurentCounit_tmul_T (B : Type ur) [CommRing B]
    (M : Type um) [AddCommGroup M] [Module B M] (k : ℤ) (m : M) :
    laurentCounit B M ((LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) = m := by
  simp only [laurentCounit, LinearMap.coe_comp, Finsupp.coe_lsum, Finsupp.sum, LinearMap.id_coe,
    id_eq, LinearEquiv.coe_coe, Function.comp_apply, laurentTensorCoefficients_tmul,
    LaurentPolynomial.T_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finsupp.mem_support_iff, ↓reduceIte, ne_eq, ite_eq_left_iff, not_not]
  intro hm
  simp [hm]

private lemma laurentCoefficients_sum_of_counit (B : Type ur) [CommRing B]
    (M : Type um) [AddCommGroup M] [Module B M]
    (δ : M → LaurentPolynomial B ⊗[B] M)
    (ε : (LaurentPolynomial B ⊗[B] M) →ₗ[B] M)
    (hε : ∀ k m, ε ((LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) = m)
    (hεδ : ∀ m, ε (δ m) = m) (x : M) :
    (laurentTensorCoefficients B M (δ x)).sum (fun _ m ↦ m) = x := by
  let y := laurentTensorCoefficients B M (δ x)
  have hδ : δ x = y.sum (fun k m ↦
      (LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m) :=
    ((laurentTensorCoefficients B M).symm_apply_apply (δ x)).symm.trans
      (laurentTensorCoefficients_symm_apply B M y)
  simpa only [map_sum, Finsupp.sum, hεδ, hε, y] using (congrArg ε hδ).symm

public lemma laurentCoefficients_eq_of_tensor_sum (R : Type ur) [CommRing R]
    (M : Type um) (N : Type un) [AddCommGroup M] [AddCommGroup N] [Module R N]
    (y : ℤ →₀ M) (f g : ℤ → M → N)
    (hf : ∀ k, f k 0 = 0) (hg : ∀ k, g k 0 = 0)
    (h : (y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial R) ⊗ₜ[R]
        f k m) : LaurentPolynomial R ⊗[R] N) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial R) ⊗ₜ[R] g k m)) :
    ∀ k, f k (y k) = g k (y k) := by
  intro k
  have hk := congrArg (fun z : LaurentPolynomial R ⊗[R] N ↦
    laurentTensorCoefficients R N z k) h
  rwa [laurentTensorCoefficients_sum_tmul R M N y f hf k,
    laurentTensorCoefficients_sum_tmul R M N y g hg k] at hk

/-- The four carriers genuinely sit in four different universes once the value universe of
the functor is released from the algebra universe: `N` below is a tensor product of an
algebra with a value, so it lives in the join of the two. -/
public lemma finsupp_sum_map_congr (M : Type ur) (N : Type um) (P : Type un) (Q : Type uq)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (y : ℤ →₀ M) (f : ℤ → M → N) (g : ℤ → M → P)
    (L : N →+ Q) (K : P →+ Q) (h : ∀ k m, L (f k m) = K (g k m)) :
    L (y.sum f) = K (y.sum g) := by
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl (fun k hk ↦ h k (y k))

/-- Move a tensor product across two propositionally equal module structures on its left
factor.  The equality is consumed by `cases` at the definition site, so no `HEq` goal ever
reaches a tactic block downstream. -/
private noncomputable def tensorTransport (R : Type ur) (P : Type um) (M : Type un)
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

private lemma tensorTransport_tmul (R : Type ur) (P : Type um) (M : Type un)
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

private lemma tensorTransport_symm_tmul (R : Type ur) (P : Type um) (M : Type un)
    [CommRing R] [CommRing P] [Algebra R P] [AddCommGroup M] [Module R M]
    (s t : AddCommMonoid P) (ms : @Module R P _ s) (mt : @Module R P _ t)
    (hs : s = t) (hm : HEq ms mt) (p : P) (m : M) :
    (tensorTransport R P M s t ms mt hs hm).symm
      (letI : AddCommMonoid P := t
       letI : Module R P := mt
       p ⊗ₜ[R] m) =
      (letI : AddCommMonoid P := s
       letI : Module R P := ms
       p ⊗ₜ[R] m) :=
  (LinearEquiv.symm_apply_eq _).2 (tensorTransport_tmul R P M s t ms mt hs hm p m).symm

end Coefficients

section Apparatus

open CategoryTheory
open scoped DirectSum TensorProduct

universe u uB uM

/-- The structure-ring functor on the double opposite of the category of commutative
`A`-algebras with carriers in an arbitrary universe `uB`. -/
public abbrev ringDiagram (A : Type u) [CommRing A] :
    (CommAlgCat.{uB} A)ᵒᵖᵒᵖ ⥤ RingCat.{uB} :=
  unopUnop (CommAlgCat.{uB} A) ⋙ forget₂ (CommAlgCat.{uB} A) CommRingCat.{uB} ⋙
    forget₂ CommRingCat.{uB} RingCat.{uB}

set_option linter.checkUnivs false in
/-- A module-valued functor on commutative `A`-algebras whose algebra universe `uB` and
value universe `uM` are unrelated to each other and to the universe of `A`. -/
public abbrev ModuleValuedFunctor (A : Type u) [CommRing A] :=
  PresheafOfModules.{uM} (ringDiagram.{u, uB} A)

/-- The constant-polynomial algebra map `B → B[T,T⁻¹]`. -/
public noncomputable def constantLaurentMap (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] : B →ₐ[A] LaurentPolynomial B where
  toRingHom := LaurentPolynomial.C
  commutes' _ := rfl

/-- The algebra map from a graded algebra to its Laurent polynomial algebra which sends a
homogeneous element of degree `d` to that element times `T d`. -/
@[ega "II 8.3.9" "partial"]
public noncomputable def gradedLaurentMap (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    B →ₐ[A] LaurentPolynomial B := by
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
public def weightSpace (A : Type u) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (F : ModuleValuedFunctor.{u, uB, uM} A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (k : ℤ) : Set (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :=
  {ξ | (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) ξ =
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) ξ}

/-- A module-valued functor preserves flat base change if its canonical map from extension of
scalars is an isomorphism.  The displayed condition on pure tensors identifies the isomorphism
with the canonical one. -/
public def PreservesFlatBaseChange (A : Type u) [CommRing A]
    (F : ModuleValuedFunctor.{u, uB, uM} A) : Prop :=
  ∀ (B C : Type uB) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C),
    letI : Algebra B C := f.toRingHom.toAlgebra
    Module.Flat B C →
      ∃ e : (C ⊗[B] F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[C]
          F.obj (Opposite.op (Opposite.op (CommAlgCat.of A C))),
        ∀ x, e (1 ⊗ₜ[B] x) = F.map ((CommAlgCat.ofHom f).op.op) x

private noncomputable def evalLaurentOne (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] : LaurentPolynomial B →ₐ[A] B where
  toRingHom := LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
  commutes' a := by
    change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
      (LaurentPolynomial.C (algebraMap A B a)) = algebraMap A B a
    simp

private lemma evalLaurentOne_comp_constant (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] :
    (evalLaurentOne A B).comp (constantLaurentMap A B) = AlgHom.id A B := by
  refine AlgHom.ext fun b ↦ ?_
  change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ) (LaurentPolynomial.C b) = b
  simp

private lemma gradedLaurentMap_of_mem (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (d : ℕ) (b : B) (hb : b ∈ 𝒜 d) :
    gradedLaurentMap A B 𝒜 b =
      LaurentPolynomial.C b * LaurentPolynomial.T (d : ℤ) := by
  change (DirectSum.liftRingHom _) (DirectSum.decompose 𝒜 b) = _
  rw [DirectSum.decompose_of_mem 𝒜 hb]
  simp [DirectSum.liftRingHom_apply]

private lemma evalLaurentOne_comp_graded (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (evalLaurentOne A B).comp (gradedLaurentMap A B 𝒜) = AlgHom.id A B := by
  refine AlgHom.ext fun b ↦ ?_
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 b]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 b]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  change (evalLaurentOne A B) ((gradedLaurentMap A B 𝒜)
      ↑((DirectSum.decompose 𝒜 b) d)) = _
  rw [gradedLaurentMap_of_mem A B 𝒜 d _ (DirectSum.decompose 𝒜 b d).property]
  change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
    (LaurentPolynomial.C _ * LaurentPolynomial.T (d : ℤ)) = _
  simp

/-- Composition in the double opposite of `CommAlgCat` is composition of algebra maps.
Proved once for abstract algebra maps; substituting the Laurent-polynomial algebras into the
proof instead makes the kernel unfold three concrete `AlgHom` structures. -/
private lemma opop_comp (A : Type u) [CommRing A] (X Y Z : Type uB) [CommRing X]
    [CommRing Y] [CommRing Z] [Algebra A X] [Algebra A Y] [Algebra A Z]
    (p : X →ₐ[A] Y) (q : Y →ₐ[A] Z) :
    ((CommAlgCat.ofHom p).op.op ≫ (CommAlgCat.ofHom q).op.op :
        Opposite.op (Opposite.op (CommAlgCat.of A X)) ⟶
          Opposite.op (Opposite.op (CommAlgCat.of A Z))) =
      (CommAlgCat.ofHom (q.comp p)).op.op := rfl

/-- Applying the restriction along `q` after the one along `p` is the identity when
`q ∘ p = id`. -/
private lemma map_map_of_comp_eq_id (A : Type u) [CommRing A] (X Y : Type uB) [CommRing X]
    [CommRing Y] [Algebra A X] [Algebra A Y] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (p : X →ₐ[A] Y) (q : Y →ₐ[A] X) (h : q.comp p = AlgHom.id A X)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A X)))) :
    F.map (CommAlgCat.ofHom q).op.op (F.map (CommAlgCat.ofHom p).op.op x) = x := by
  rw [← F.map_comp_apply, opop_comp, h]
  simp
  rfl

/-- Two composites of restriction maps agree when the composites of algebra maps do. -/
private lemma map_map_eq_of_comp_eq (A : Type u) [CommRing A] (X Y Y' Z : Type uB)
    [CommRing X] [CommRing Y] [CommRing Y'] [CommRing Z] [Algebra A X] [Algebra A Y]
    [Algebra A Y'] [Algebra A Z] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (p : X →ₐ[A] Y) (q : Y →ₐ[A] Z) (p' : X →ₐ[A] Y') (q' : Y' →ₐ[A] Z)
    (h : q.comp p = q'.comp p') (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A X)))) :
    F.map (CommAlgCat.ofHom q).op.op (F.map (CommAlgCat.ofHom p).op.op x) =
      F.map (CommAlgCat.ofHom q').op.op (F.map (CommAlgCat.ofHom p').op.op x) := by
  rw [← F.map_comp_apply, ← F.map_comp_apply, opop_comp, opop_comp, h]

private instance laurentFlat (B : Type uB) [CommRing B] :
    Module.Flat B (LaurentPolynomial B) := Module.Flat.of_free

private lemma flatBaseChange_tmul (A : Type u) (B C : Type uB) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C]
    (F : ModuleValuedFunctor.{u, uB, uM} A) (f : B →ₐ[A] C) :
    ∀ (e : (C ⊗[B] F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[C]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A C)))),
      (∀ x, e (1 ⊗ₜ[B] x) = F.map ((CommAlgCat.ofHom f).op.op) x) →
      ∀ c x, e (c ⊗ₜ[B] x) = c • F.map ((CommAlgCat.ofHom f).op.op) x := by
  intro e he c x
  rw [show c ⊗ₜ[B] x = c • ((1 : C) ⊗ₜ[B] x) by simp [TensorProduct.smul_tmul'], map_smul, he]
  rfl

private lemma laurentModule_eq (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] :
    @Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMap A B).toRingHom.toAlgebra) =
      (AddMonoidAlgebra.instModule : Module B (LaurentPolynomial B)) := by
  apply Module.ext'
  intro b p
  change LaurentPolynomial.C b * p = b • p
  ext k
  rw [← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.coeff_single_zero_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

private lemma laurentAddCommMonoid_eq (B : Type uB) [CommRing B] :
    (CommRing.toCommSemiring.toAddCommMonoid : AddCommMonoid (LaurentPolynomial B)) =
      AddMonoidAlgebra.instAddCommMonoid := rfl

private lemma laurentModule_heq (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] :
    HEq
      (letI : AddCommMonoid (LaurentPolynomial B) :=
          (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
       letI : Algebra B (LaurentPolynomial B) :=
          (constantLaurentMap A B).toRingHom.toAlgebra
       (Algebra.toModule : Module B (LaurentPolynomial B)))
      (AddMonoidAlgebra.instModule : Module B (LaurentPolynomial B)) :=
  heq_of_eq (laurentModule_eq A B)

private noncomputable def laurentTensorTransport (A : Type u) (B : Type uB) (M : Type uM)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M] :
    (letI : AddCommMonoid (LaurentPolynomial B) :=
        (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
     letI : Algebra B (LaurentPolynomial B) :=
        (constantLaurentMap A B).toRingHom.toAlgebra
     letI : Module B (LaurentPolynomial B) := Algebra.toModule
     LaurentPolynomial B ⊗[B] M) ≃ₗ[B] (LaurentPolynomial B ⊗[B] M) :=
  tensorTransport B (LaurentPolynomial B) M
    ((inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid)
    AddMonoidAlgebra.instAddCommMonoid
    (@Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMap A B).toRingHom.toAlgebra))
    AddMonoidAlgebra.instModule
    (laurentAddCommMonoid_eq B) (laurentModule_heq A B)

private lemma laurentTensorTransport_symm_tmul (A : Type u) (B : Type uB) (M : Type uM)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    (p : LaurentPolynomial B) (m : M) :
    (laurentTensorTransport A B M).symm (p ⊗ₜ[B] m) =
      (letI : AddCommMonoid (LaurentPolynomial B) :=
          (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
       letI : Algebra B (LaurentPolynomial B) :=
          (constantLaurentMap A B).toRingHom.toAlgebra
       letI : Module B (LaurentPolynomial B) := Algebra.toModule
       p ⊗ₜ[B] m) :=
  tensorTransport_symm_tmul B (LaurentPolynomial B) M
    ((inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid)
    AddMonoidAlgebra.instAddCommMonoid
    (@Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMap A B).toRingHom.toAlgebra))
    AddMonoidAlgebra.instModule
    (laurentAddCommMonoid_eq B) (laurentModule_heq A B) p m

private lemma laurentBaseChange (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (hF : PreservesFlatBaseChange A F) :
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

private lemma laurentBaseChangeCanonical (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (hF : PreservesFlatBaseChange A F) :
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
      map_add' _ _ := by simp [map_add] }
  have he' (x : M) : e' (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x := by
    change e (t.symm (1 ⊗ₜ[B] x)) = _
    rw [laurentTensorTransport_symm_tmul A B M]
    exact he x
  have he'_tmul (q : LaurentPolynomial B) (x : M) :
      e' (q ⊗ₜ[B] x) = q • F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x := by
    change e (t.symm (q ⊗ₜ[B] x)) = _
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
      induction z using TensorProduct.inductionOn with
      | tmul q x =>
          rw [TensorProduct.smul_tmul']
          change e' ((p * q) ⊗ₜ[B] x) = p • e' (q ⊗ₜ[B] x)
          rw [he'_tmul, he'_tmul, mul_smul]
          rfl
      | add z w hz hw =>
          rw [smul_add]
          change e' (p • z + p • w) = p • e' (z + w)
          rw [e'.map_add, e'.map_add, smul_add]
          exact congrArg₂ (· + ·) hz hw
  }
  exact ⟨eₚ, he'⟩

private lemma laurentBaseChange_weightedSum (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
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
  exact Finset.sum_congr rfl fun k _ ↦ flatBaseChange_tmul A B (LaurentPolynomial B) F
    (constantLaurentMap A B) e he (LaurentPolynomial.T k) (y k)

private lemma laurentBaseChange_eval_tmul_T (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
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
  change F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') = m
  rw [F.map_smul]
  have ht : evalLaurentOne A B (LaurentPolynomial.T k) = 1 := by
    change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ) (LaurentPolynomial.T k) = 1
    simp
  change evalLaurentOne A B (LaurentPolynomial.T k) •
      F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op) m' = m
  rw [ht, one_smul]
  exact map_map_of_comp_eq_id A B (LaurentPolynomial B) F _ _ (evalLaurentOne_comp_constant A B) m

private lemma laurentBaseChange_eval (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (e : (LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ≃ₗ[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (he : ∀ x, e (1 ⊗ₜ[B] x) =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) x)
    (z : LaurentPolynomial B ⊗[B]
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op) (e z) =
      laurentCounit B (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) z := by
  obtain ⟨y, rfl⟩ := (laurentTensorCoefficients B
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))).symm.surjective z
  rw [laurentTensorCoefficients_symm_apply]
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (laurentBaseChange_eval_tmul_T A B F e he k (y k)).trans
    (laurentCounit_tmul_T B _ k (y k)).symm

private lemma laurentBaseChange_eval_graded (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
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
  change F.map ((CommAlgCat.ofHom (evalLaurentOne A B)).op.op) (e (e.symm m')) = x
  rw [e.apply_symm_apply]
  exact map_map_of_comp_eq_id A B (LaurentPolynomial B) F _ _ (evalLaurentOne_comp_graded A B 𝒜) x

private noncomputable def outerTUnit (B : Type uB) [CommRing B] :
    (LaurentPolynomial (LaurentPolynomial B))ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

private noncomputable def innerTUnit (B : Type uB) [CommRing B] :
    (LaurentPolynomial (LaurentPolynomial B))ˣ where
  val := LaurentPolynomial.C (LaurentPolynomial.T 1)
  inv := LaurentPolynomial.C (LaurentPolynomial.T (-1))
  val_inv := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  inv_val := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num

private lemma outerTUnit_zpow (B : Type uB) [CommRing B] (k : ℤ) :
    ((outerTUnit B ^ k : (LaurentPolynomial (LaurentPolynomial B))ˣ) :
      LaurentPolynomial (LaurentPolynomial B)) =
      LaurentPolynomial.T k := by
  induction k using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    change LaurentPolynomial.T k * LaurentPolynomial.T 1 = LaurentPolynomial.T (k + 1)
    rw [← LaurentPolynomial.T_add]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    change (LaurentPolynomial.T (-(k : ℤ)) : LaurentPolynomial (LaurentPolynomial B)) *
      LaurentPolynomial.T (-1) = LaurentPolynomial.T (-(k : ℤ) - 1)
    rw [← LaurentPolynomial.T_add]
    congr 1

private lemma innerTUnit_zpow (B : Type uB) [CommRing B] (k : ℤ) :
    ((innerTUnit B ^ k : (LaurentPolynomial (LaurentPolynomial B))ˣ) :
      LaurentPolynomial (LaurentPolynomial B)) =
      LaurentPolynomial.C (LaurentPolynomial.T k) := by
  induction k using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    change LaurentPolynomial.C (LaurentPolynomial.T k) *
      LaurentPolynomial.C (LaurentPolynomial.T 1) =
      LaurentPolynomial.C (LaurentPolynomial.T (k + 1))
    rw [← map_mul, ← LaurentPolynomial.T_add]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    change LaurentPolynomial.C (LaurentPolynomial.T (-(k : ℤ)) : LaurentPolynomial B) *
      LaurentPolynomial.C (LaurentPolynomial.T (-1) : LaurentPolynomial B) =
      LaurentPolynomial.C (LaurentPolynomial.T (-(k : ℤ) - 1) : LaurentPolynomial B)
    rw [← map_mul, ← LaurentPolynomial.T_add]
    congr 2

private noncomputable def diagonalLaurentMap (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] : LaurentPolynomial B →ₐ[A]
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

private noncomputable def gradedOuterLaurentMap (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
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

private lemma diagonalLaurentMap_C (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (b : B) :
    diagonalLaurentMap A B (LaurentPolynomial.C b) =
      LaurentPolynomial.C (LaurentPolynomial.C b) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C b) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma gradedOuterLaurentMap_C (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (b : B) :
    gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.C b) =
      LaurentPolynomial.C (gradedLaurentMap A B 𝒜 b) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C b) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma diagonalLaurentMap_T (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (k : ℤ) :
    diagonalLaurentMap A B (LaurentPolynomial.T k) =
      LaurentPolynomial.T k * LaurentPolynomial.C (LaurentPolynomial.T k) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T k) = _
  rw [LaurentPolynomial.eval₂_T,
    mul_zpow (outerTUnit B) (innerTUnit B) k, Units.val_mul,
    outerTUnit_zpow, innerTUnit_zpow]

private lemma gradedOuterLaurentMap_T (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T k) = _
  rw [LaurentPolynomial.eval₂_T, outerTUnit_zpow]

private lemma diagonal_comp_graded (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (diagonalLaurentMap A B).comp (gradedLaurentMap A B 𝒜) =
      (gradedOuterLaurentMap A B 𝒜).comp (gradedLaurentMap A B 𝒜) := by
  have h (d : ℕ) (b : B) (hb : b ∈ 𝒜 d) :
      diagonalLaurentMap A B (gradedLaurentMap A B 𝒜 b) =
        gradedOuterLaurentMap A B 𝒜 (gradedLaurentMap A B 𝒜 b) := by
    rw [gradedLaurentMap_of_mem A B 𝒜 d b hb, map_mul, map_mul, diagonalLaurentMap_C,
      diagonalLaurentMap_T, gradedOuterLaurentMap_C, gradedOuterLaurentMap_T,
      gradedLaurentMap_of_mem A B 𝒜 d b hb, map_mul]
    ring
  refine AlgHom.ext fun b ↦ ?_
  change diagonalLaurentMap A B (gradedLaurentMap A B 𝒜 b) =
    gradedOuterLaurentMap A B 𝒜 (gradedLaurentMap A B 𝒜 b)
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 b]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 b]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun d _ ↦ h d _ (DirectSum.decompose 𝒜 b d).property

private lemma diagonal_comp_constant (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] :
    (diagonalLaurentMap A B).comp (constantLaurentMap A B) =
      (constantLaurentMap A (LaurentPolynomial B)).comp (constantLaurentMap A B) :=
  AlgHom.ext fun b ↦ diagonalLaurentMap_C A B b

private lemma gradedOuter_comp_constant (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (gradedOuterLaurentMap A B 𝒜).comp (constantLaurentMap A B) =
      (constantLaurentMap A (LaurentPolynomial B)).comp (gradedLaurentMap A B 𝒜) :=
  AlgHom.ext fun b ↦ gradedOuterLaurentMap_C A B 𝒜 b

private lemma map_gradedOuter_weightedTerm (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
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
  change F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') = _
  rw [F.map_smul]
  change gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.T k) •
    F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op) m' = _
  rw [gradedOuterLaurentMap_T]
  change (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
    F.map ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
      (F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) = _
  congr 1
  exact map_map_eq_of_comp_eq A _ _ _ _ F _ _ _ _ (gradedOuter_comp_constant A B 𝒜) m

private lemma map_diagonal_weightedTerm (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A) (k : ℤ)
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
  change F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') =
    (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op)
        ((LaurentPolynomial.T k : LaurentPolynomial B) • m')
  rw [F.map_smul]
  change diagonalLaurentMap A B (LaurentPolynomial.T k) •
    F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op) m' = _
  rw [diagonalLaurentMap_T]
  have hc : F.map ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op) m' =
      F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) m' :=
    map_map_eq_of_comp_eq A _ _ _ _ F _ _ _ _ (diagonal_comp_constant A B) m
  rw [hc, F.map_smul]
  let m'' : F.obj (Opposite.op (Opposite.op
      (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))) :=
    F.map ((CommAlgCat.ofHom (constantLaurentMap A (LaurentPolynomial B))).op.op) m'
  change ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) *
      LaurentPolynomial.C (LaurentPolynomial.T k)) • m'' =
    (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
      (LaurentPolynomial.C (LaurentPolynomial.T k)) • m''
  exact mul_smul (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B))
    (LaurentPolynomial.C (LaurentPolynomial.T k)) m''

private lemma outerBaseChange_gradedTerm (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial B))))) ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
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
  change e ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
    LaurentPolynomial B] m') = _
  rw [flatBaseChange_tmul A (LaurentPolynomial B)
    (LaurentPolynomial (LaurentPolynomial B)) F
    (constantLaurentMap A (LaurentPolynomial B)) e he]
  exact (map_gradedOuter_weightedTerm A B F 𝒜 k m).symm

private lemma outerBaseChange_diagonalTerm (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial B))))) ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
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
  change e ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
    LaurentPolynomial B] m') = _
  rw [flatBaseChange_tmul A (LaurentPolynomial B)
    (LaurentPolynomial (LaurentPolynomial B)) F
    (constantLaurentMap A (LaurentPolynomial B)) e he]
  exact (map_diagonal_weightedTerm A B F k m).symm

/-- Termwise comparison of `e` with a restriction map gives the comparison of the sums. -/
private lemma outerBaseChange_sum (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (P : LaurentPolynomial B →ₐ[A] LaurentPolynomial (LaurentPolynomial B))
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial B))))) ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))))
    (f : ℤ → F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))) →
      F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    (h : ∀ k m, e
      ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[LaurentPolynomial B]
        f k m) =
      F.map ((CommAlgCat.ofHom P).op.op)
        ((LaurentPolynomial.T k : LaurentPolynomial B) •
          F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m))
    (y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    e (y.sum (fun k m ↦
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
        LaurentPolynomial B] f k m)) =
      F.restrictₛₗ ((CommAlgCat.ofHom P).op.op)
        (y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
          (F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m :
            F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B))))))) :=
  finsupp_sum_map_congr _ _ _ _ y
    (fun k m ↦ ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
      LaurentPolynomial B] f k m :
        LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
          F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B))))))
    (fun k m ↦ ((LaurentPolynomial.T k : LaurentPolynomial B) •
      (F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m :
        F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B))))) :
        F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B))))))
    e.toLinearMap.toAddMonoidHom
    (F.restrictₛₗ ((CommAlgCat.ofHom P).op.op)).toAddMonoidHom h

/-- Two restriction maps with a common first leg agree on the image of that leg.  Stated
abstractly: at independent universes the kernel cannot afford to verify this shape with the
three Laurent-polynomial algebras substituted in. -/
private lemma map_eq_of_comp_eq (A : Type u) [CommRing A]
    (F : ModuleValuedFunctor.{u, uB, uM} A)
    {X Y Z : (CommAlgCat.{uB} A)ᵒᵖᵒᵖ} (g : X ⟶ Y) (f d : Y ⟶ Z) (h : g ≫ f = g ≫ d)
    (x : F.obj X) : F.map f (F.map g x) = F.map d (F.map g x) :=
  (F.map_comp_apply g f x).symm.trans
    ((F.congr_map_apply h x).trans (F.map_comp_apply g d x))

/-- The previous lemma in the spelling the coefficient comparison needs.  The conversion
between `restrictₛₗ` and `map` is definitional but not syntactic, so it is discharged here,
where `F`, the morphisms and the element are all variables: performing it with the three
Laurent-polynomial algebras substituted in is what times the kernel out. -/
private lemma restrictₛₗ_eq_of_comp_eq (A : Type u) [CommRing A]
    (F : ModuleValuedFunctor.{u, uB, uM} A)
    {X Y Z : (CommAlgCat.{uB} A)ᵒᵖᵒᵖ} (g : X ⟶ Y) (f d : Y ⟶ Z) (h : g ≫ f = g ≫ d)
    (x : F.obj X) :
    F.restrictₛₗ f (F.map g x) = F.restrictₛₗ d (F.map g x) :=
  map_eq_of_comp_eq A F g f d h x

/-- Functoriality through two Laurent-polynomial extensions, at the level of morphisms. -/
private lemma gradedOuter_comp_eq (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op ≫
        (CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op :
      Opposite.op (Opposite.op (CommAlgCat.of A B)) ⟶
        Opposite.op (Opposite.op
          (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))) =
    (CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op ≫
      (CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op := by
  rw [opop_comp A B (LaurentPolynomial B) (LaurentPolynomial (LaurentPolynomial B)),
    opop_comp A B (LaurentPolynomial B) (LaurentPolynomial (LaurentPolynomial B)),
    diagonal_comp_graded A B 𝒜]

/-- Functoriality through two Laurent-polynomial extensions.  The composite is split into
named abstract steps so that no implicit argument has to be recovered by unifying against the
concrete triple composite. -/
private lemma gradedOuter_eq_diagonal_map (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
      (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) =
    F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
      (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) :=
  restrictₛₗ_eq_of_comp_eq A F _ _ _ (gradedOuter_comp_eq A B 𝒜) x

/-- The coefficient comparison normalizes two nested Laurent tensor expansions. -/
private lemma weightCoefficients_of_expansion (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
      F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (LaurentPolynomial B))))) ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
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
    apply e.injective
    calc
      e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] gradedValue m)) =
        F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
          (y.sum weightedValue) :=
        outerBaseChange_sum A B F _ e (fun _ m ↦ gradedValue m)
          (fun k m ↦ outerBaseChange_gradedTerm A B F 𝒜 e he k m) y
      _ = F.restrictₛₗ ((CommAlgCat.ofHom (gradedOuterLaurentMap A B 𝒜)).op.op)
          (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) := by
            rw [hy]
            simp only [weightedValue]
            rfl
      _ = F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
          (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x) :=
            gradedOuter_eq_diagonal_map A B F 𝒜 x
      _ = F.restrictₛₗ ((CommAlgCat.ofHom (diagonalLaurentMap A B)).op.op)
          (y.sum weightedValue) := by
            rw [hy]
            simp only [weightedValue]
            rfl
      _ = e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] weightedValue k m)) :=
        (outerBaseChange_sum A B F _ e weightedValue
          (fun k m ↦ outerBaseChange_diagonalTerm A B F e he k m) y).symm
  have hz₁ : ∀ (j : ℤ), gradedValue
      (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) = 0 := fun _ ↦ map_zero _
  have hz₂ : ∀ (j : ℤ), weightedValue j
      (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) = 0 := by
    intro j
    change (LaurentPolynomial.T j : LaurentPolynomial B) •
      F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op)
        (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) = 0
    rw [map_zero, smul_zero]
  intro k
  change weightedValue k (y k) = gradedValue (y k)
  exact (laurentCoefficients_eq_of_tensor_sum (LaurentPolynomial B)
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))))
    y (fun _ m ↦ gradedValue m) weightedValue hz₁ hz₂ hs k).symm

private lemma map_sum_of_weights (A : Type u) (B : Type uB) [CommRing A] [CommRing B]
    [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hy : ∀ k, y k ∈ weightSpace A B F 𝒜 k) :
    F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op)
      (y.sum (fun _ m ↦ m)) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (hy k).symm

private lemma weightDecomposition_unique (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
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
    laurentBaseChange_weightedSum A B F e he z, ← map_sum_of_weights A B F 𝒜 y hy,
    ← map_sum_of_weights A B F 𝒜 z hz, hyx, hzx]

/-- Every element of the value of a flat-base-change-compatible module-valued functor on a
graded algebra has a unique finite decomposition into elements of its integer weight spaces.

This is Tag 06UZ (1) with the algebra universe `uB` and the value universe `uM` independent
of one another and of the universe of the base ring. -/
public lemma existsUnique_finsupp_weightSpace_eq_aux (A : Type u) (B : Type uB) [CommRing A]
    [CommRing B] [Algebra A B] (F : ModuleValuedFunctor.{u, uB, uM} A)
    (hF : PreservesFlatBaseChange A F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    ∃! y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))),
      (∀ k, y k ∈ weightSpace A B F 𝒜 k) ∧ y.sum (fun _ z ↦ z) = x := by
  classical
  obtain ⟨e₁, he₁⟩ := laurentBaseChangeCanonical A B F hF
  obtain ⟨e₂, he₂⟩ := laurentBaseChangeCanonical A (LaurentPolynomial B) F hF
  let y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))) :=
    laurentTensorCoefficients B (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
      (e₁.symm (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x))
  have hy : F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) x =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map ((CommAlgCat.ofHom (constantLaurentMap A B)).op.op) m) := by
    rw [← laurentBaseChange_weightedSum A B F e₁ he₁ y]
    simp only [y, LinearEquiv.symm_apply_apply]
    exact (e₁.apply_symm_apply _).symm
  have hw : ∀ k, y k ∈ weightSpace A B F 𝒜 k :=
    weightCoefficients_of_expansion A B F 𝒜 e₂ he₂ x y hy
  have hsum : y.sum (fun _ m ↦ m) = x :=
    laurentCoefficients_sum_of_counit B
      (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
      (fun m ↦ e₁.symm
        (F.map ((CommAlgCat.ofHom (gradedLaurentMap A B 𝒜)).op.op) m))
      (laurentCounit B
        (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))))
      (laurentCounit_tmul_T B
        (F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))))
      (laurentBaseChange_eval_graded A B F 𝒜 e₁ he₁) x
  exact ⟨y, ⟨hw, hsum⟩, fun y' hy' ↦ weightDecomposition_unique A B F 𝒜 e₁ he₁ x y' y
    hy'.1 hw hy'.2 hsum⟩

end Apparatus

section Large

open CategoryTheory
open scoped TensorProduct

universe u v w

/-- Tag 06UZ (1) in the universe discipline of
`StacksFrontier/Algebra/Module/Adequate/Defs.lean`: the module-valued functor takes its values
in `Type (max u v w)` while its algebras have carriers in `Type (max u v)`, so that the value
universe `w` is independent of the universe `v` of the algebras and of the universe `u` of
the base ring.

Every element of `F(B)` has a unique finitely supported decomposition into elements of the
integer weight spaces of a grading of `B`. -/
public lemma existsUnique_finsupp_weightSpace_eq_large (A : Type u) (B : Type (max u v))
    [CommRing A] [CommRing B] [Algebra A B]
    (F : AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A)
    (hF : PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    ∃! y : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))),
      (∀ k, y k ∈ weightSpace.{u, max u v, max u v w} A B F 𝒜 k) ∧
        y.sum (fun _ z ↦ z) = x :=
  existsUnique_finsupp_weightSpace_eq_aux.{u, max u v, max u v w} A B F hF 𝒜 x

end Large

end AdequateFunctor.LaurentLarge

end
