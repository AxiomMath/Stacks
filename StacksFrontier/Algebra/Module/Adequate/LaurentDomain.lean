module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.Algebra.Module.Adequate.DomainValues
public import StacksFrontier.Algebra.Module.Adequate.LaurentLarge
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift

/-!
# Tag 06UZ (1) on a restricted domain of algebras

Let `A` be a ring, `Q` a property of commutative `A`-algebras, and `F` a module-valued functor
defined only on the full subcategory of algebras satisfying `Q`. If `B` is a graded algebra of
that domain, and `Q` is closed under Laurent polynomial extension, then every element of `F(B)`
has a unique finitely supported decomposition into elements of the integer weight spaces of the
grading. This is [Stacks, Tag 06UZ] (1) on a restricted domain.

`StacksFrontier.Algebra.Module.Adequate.LaurentLarge` proves the same statement for a functor on
*all* commutative `A`-algebras; that proof is left untouched, and nothing here depends on its
conclusion. The restricted-domain statement is not an instance of it: the functors the splitting
argument of [Stacks, Tag 06V7] applies it to — the middle term of an extension — are not
restrictions of functors on all algebras, which is exactly why the domain has to be carried
through the argument rather than enlarged.

## Main results

* `AdequateFunctor.LaurentDomain.existsUnique_finsupp_weightSpace_eq` — [Stacks, Tag 06UZ] (1)
  on a restricted domain.
* `AdequateFunctor.LaurentDomain.weightSpace_eq_zero_of_mem_two_weights` — an element with two
  distinct weights is zero.

## Implementation notes

The argument is the one of the full-domain proof and evaluates `F` at exactly three algebras:
`B`, its Laurent polynomial algebra `B[T, T⁻¹]`, and the double Laurent polynomial algebra
`B[T, T⁻¹][S, S⁻¹]`. The domain must therefore contain all three, which is why the statements
below carry `Q (CommAlgCat.of A B)` together with the two iterated Laurent memberships rather
than a single closure hypothesis: iterating the closure is the caller's business, and a caller
holding `∀ R, Q R → Q R[T, T⁻¹]` supplies all three.

Only two instances of flat base change are consumed, both internal to the domain:
`B → B[T, T⁻¹]` and `B[T, T⁻¹] → B[T, T⁻¹][S, S⁻¹]`. Accordingly the hypothesis is
`AdequateFunctor.LaurentDomain.PreservesFlatBaseChange`, which quantifies over the domain only.

Following the full-domain proof, the three Laurent-polynomial algebras are never substituted
into a proof obligation about the shape of a composite. Composition identities are proved once
for *variable* morphisms of the domain (`map_eq_of_comp_eq`, `restrictₛₗ_eq_of_comp_eq`) and
then applied, so the kernel is never asked to unify at the concrete nested arguments.

The `LaurentPolynomial B`-module structure that flat base change produces comes from
`(constantLaurentMapLarge A B).toRingHom.toAlgebra`, while the one the coefficient apparatus uses
is `AddMonoidAlgebra.instModule`. These are propositionally but not definitionally equal; the
discrepancy is absorbed once, at the definition site, by `tensorTransport`, so that no `HEq` goal
reaches a tactic block downstream.

## References

* [Stacks Project, Tag 06UY](https://stacks.math.columbia.edu/tag/06UY)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace AdequateFunctor.LaurentDomain

/-! ### Coefficients of a Laurent tensor

Nothing in this section mentions a module-valued functor: these are statements about a module
over a ring and its Laurent tensor product. -/

section Coefficients

universe ur um un uq

/-- Coefficients of a tensor with a Laurent polynomial in its left factor. The ring and the
module may live in unrelated universes. -/
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
    rw [map_add, hy, hz, Finsupp.sum_add_index] <;> simp [TensorProduct.tmul_add]
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
  simpa only [hεδ, hε, map_sum, Finsupp.sum, y] using (congrArg ε hδ).symm

private alias laurentCoefficients_eq_of_tensor_sum :=
  AdequateFunctor.LaurentLarge.laurentCoefficients_eq_of_tensor_sum

/-- The four carriers genuinely sit in four different universes once the value universe of the
functor is released from the algebra universe. -/
private alias finsupp_sum_map_congr := AdequateFunctor.LaurentLarge.finsupp_sum_map_congr

/-- Move a tensor product across two propositionally equal module structures on its left
factor. The equality is consumed by `cases` at the definition site, so no `HEq` goal ever
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
  (tensorTransport R P M s t ms mt hs hm).symm_apply_eq.mpr
    (tensorTransport_tmul R P M s t ms mt hs hm p m).symm

end Coefficients

/-! ### The algebra maps of the argument

Nothing in this section mentions a module-valued functor either: these are the five algebra maps
between `B`, `B[T, T⁻¹]` and `B[T, T⁻¹][S, S⁻¹]` that the argument uses, and the identities
among their composites. -/

section AlgebraMaps

universe u uB uM

variable (A : Type u) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]

/-- Evaluate a Laurent polynomial at `1`, the counit of the grading. -/
private noncomputable def evalLaurentOne : LaurentPolynomial B →ₐ[A] B where
  toRingHom := LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
  commutes' a := by
    change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
      (LaurentPolynomial.C (algebraMap A B a)) = algebraMap A B a
    simp

private lemma evalLaurentOne_comp_constant :
    (evalLaurentOne A B).comp (constantLaurentMapLarge A B) = AlgHom.id A B := by
  apply AlgHom.ext
  intro b
  change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ) (LaurentPolynomial.C b) = b
  simp

/-- Algebra maps out of a graded algebra agree once they agree on every graded piece. -/
private lemma algHom_ext_of_graded (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {C : Type*}
    [CommRing C] [Algebra A C] {f g : B →ₐ[A] C} (h : ∀ d b, b ∈ 𝒜 d → f b = g b) : f = g := by
  refine AlgHom.ext fun b ↦ ?_
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add m m' hm hm' => rw [map_add, map_add, hm, hm']

private lemma evalLaurentOne_comp_graded (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (evalLaurentOne A B).comp (gradedLaurentMapLarge A B 𝒜) = AlgHom.id A B := by
  refine algHom_ext_of_graded A B 𝒜 fun d b hb ↦ ?_
  change (evalLaurentOne A B) (gradedLaurentMapLarge A B 𝒜 b) = b
  rw [gradedLaurentMapLarge_mem A B 𝒜 d b hb]
  change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
    (LaurentPolynomial.C _ * LaurentPolynomial.T (d : ℤ)) = _
  simp

private instance laurentFlat : Module.Flat B (LaurentPolynomial B) := Module.Flat.of_free

private lemma laurentModule_eq :
    @Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMapLarge A B).toRingHom.toAlgebra) =
      (AddMonoidAlgebra.instModule : Module B (LaurentPolynomial B)) := by
  apply Module.ext'
  intro b p
  change LaurentPolynomial.C b * p = b • p
  ext k
  rw [← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.coeff_single_zero_mul,
    AddMonoidAlgebra.coeff_smul_apply]
  exact (smul_eq_mul b (p.coeff k)).symm

private lemma laurentAddCommMonoid_eq :
    (CommRing.toCommSemiring.toAddCommMonoid : AddCommMonoid (LaurentPolynomial B)) =
      AddMonoidAlgebra.instAddCommMonoid :=
  rfl

private lemma laurentModule_heq :
    HEq
      (letI : AddCommMonoid (LaurentPolynomial B) :=
          (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
       letI : Algebra B (LaurentPolynomial B) :=
          (constantLaurentMapLarge A B).toRingHom.toAlgebra
       (Algebra.toModule : Module B (LaurentPolynomial B)))
      (AddMonoidAlgebra.instModule : Module B (LaurentPolynomial B)) :=
  heq_of_eq (laurentModule_eq A B)

private noncomputable def outerTUnit : (LaurentPolynomial (LaurentPolynomial B))ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

private noncomputable def innerTUnit : (LaurentPolynomial (LaurentPolynomial B))ˣ where
  val := LaurentPolynomial.C (LaurentPolynomial.T 1)
  inv := LaurentPolynomial.C (LaurentPolynomial.T (-1))
  val_inv := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  inv_val := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num

/-- Integer powers of a unit are given by any family that is multiplicative in its index. -/
private lemma val_zpow_eq_of_add {S : Type*} [Ring S] (u : Sˣ) (t : ℤ → S) (h0 : t 0 = 1)
    (h : ∀ j k, t (j + k) = t j * t k) (hu : t 1 = u) (hu' : t (-1) = ↑u⁻¹) (k : ℤ) :
    ((u ^ k : Sˣ) : S) = t k := by
  induction k using Int.induction_on with
  | zero => simp [h0]
  | succ k ih => rw [zpow_add_one, Units.val_mul, ih, ← hu, ← h]
  | pred k ih => rw [zpow_sub_one, Units.val_mul, ih, ← hu', ← h, sub_eq_add_neg]

private lemma outerTUnit_zpow (k : ℤ) :
    ((outerTUnit B ^ k : (LaurentPolynomial (LaurentPolynomial B))ˣ) :
      LaurentPolynomial (LaurentPolynomial B)) =
      LaurentPolynomial.T k :=
  val_zpow_eq_of_add _ _ LaurentPolynomial.T_zero LaurentPolynomial.T_add rfl rfl k

private lemma innerTUnit_zpow (k : ℤ) :
    ((innerTUnit B ^ k : (LaurentPolynomial (LaurentPolynomial B))ˣ) :
      LaurentPolynomial (LaurentPolynomial B)) =
      LaurentPolynomial.C (LaurentPolynomial.T k) :=
  val_zpow_eq_of_add _ (fun k ↦ LaurentPolynomial.C (LaurentPolynomial.T k))
    (by simp [LaurentPolynomial.T_zero])
    (fun j k ↦ by simp only [LaurentPolynomial.T_add, map_mul]) rfl rfl k

/-- The map `B[T, T⁻¹] → B[T, T⁻¹][S, S⁻¹]` sending `T` to `S · T`. -/
private noncomputable def diagonalLaurentMap : LaurentPolynomial B →ₐ[A]
    LaurentPolynomial (LaurentPolynomial B) where
  toRingHom := LaurentPolynomial.eval₂
    ((constantLaurentMapLarge A (LaurentPolynomial B)).toRingHom.comp
      (constantLaurentMapLarge A B).toRingHom)
    (outerTUnit B * innerTUnit B)
  commutes' a := by
    rw [← (constantLaurentMapLarge A B).commutes a]
    change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C (algebraMap A B a)) = _
    rw [LaurentPolynomial.eval₂_C]
    change (constantLaurentMapLarge A (LaurentPolynomial B))
      ((constantLaurentMapLarge A B) (algebraMap A B a)) = _
    rw [(constantLaurentMapLarge A B).commutes]
    exact (constantLaurentMapLarge A (LaurentPolynomial B)).commutes a

/-- The map `B[T, T⁻¹] → B[T, T⁻¹][S, S⁻¹]` grading the coefficients and sending `T` to `S`. -/
private noncomputable def gradedOuterLaurentMap (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    LaurentPolynomial B →ₐ[A] LaurentPolynomial (LaurentPolynomial B) where
  toRingHom := LaurentPolynomial.eval₂
    ((constantLaurentMapLarge A (LaurentPolynomial B)).toRingHom.comp
      (gradedLaurentMapLarge A B 𝒜).toRingHom)
    (outerTUnit B)
  commutes' a := by
    rw [← (constantLaurentMapLarge A B).commutes a]
    change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C (algebraMap A B a)) = _
    rw [LaurentPolynomial.eval₂_C]
    change (constantLaurentMapLarge A (LaurentPolynomial B))
      ((gradedLaurentMapLarge A B 𝒜) (algebraMap A B a)) = _
    rw [(gradedLaurentMapLarge A B 𝒜).commutes]
    exact (constantLaurentMapLarge A (LaurentPolynomial B)).commutes a

private lemma diagonalLaurentMap_C (b : B) :
    diagonalLaurentMap A B (LaurentPolynomial.C b) =
      LaurentPolynomial.C (LaurentPolynomial.C b) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C b) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma gradedOuterLaurentMap_C (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (b : B) :
    gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.C b) =
      LaurentPolynomial.C (gradedLaurentMapLarge A B 𝒜 b) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.C b) = _
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma diagonalLaurentMap_T (k : ℤ) :
    diagonalLaurentMap A B (LaurentPolynomial.T k) =
      LaurentPolynomial.T k * LaurentPolynomial.C (LaurentPolynomial.T k) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T k) = _
  rw [LaurentPolynomial.eval₂_T,
    mul_zpow (outerTUnit B) (innerTUnit B) k, Units.val_mul,
    outerTUnit_zpow, innerTUnit_zpow]

private lemma gradedOuterLaurentMap_T (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T k) = _
  rw [LaurentPolynomial.eval₂_T, outerTUnit_zpow]

private lemma diagonal_comp_graded (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (diagonalLaurentMap A B).comp (gradedLaurentMapLarge A B 𝒜) =
      (gradedOuterLaurentMap A B 𝒜).comp (gradedLaurentMapLarge A B 𝒜) := by
  refine algHom_ext_of_graded A B 𝒜 fun d b hb ↦ ?_
  change diagonalLaurentMap A B (gradedLaurentMapLarge A B 𝒜 b) =
    gradedOuterLaurentMap A B 𝒜 (gradedLaurentMapLarge A B 𝒜 b)
  rw [gradedLaurentMapLarge_mem A B 𝒜 d b hb, map_mul, map_mul, diagonalLaurentMap_C,
    diagonalLaurentMap_T, gradedOuterLaurentMap_C, gradedOuterLaurentMap_T,
    gradedLaurentMapLarge_mem A B 𝒜 d b hb, map_mul]
  ring

private lemma diagonal_comp_constant :
    (diagonalLaurentMap A B).comp (constantLaurentMapLarge A B) =
      (constantLaurentMapLarge A (LaurentPolynomial B)).comp (constantLaurentMapLarge A B) :=
  AlgHom.ext fun b ↦ diagonalLaurentMap_C A B b

private lemma gradedOuter_comp_constant (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] :
    (gradedOuterLaurentMap A B 𝒜).comp (constantLaurentMapLarge A B) =
      (constantLaurentMapLarge A (LaurentPolynomial B)).comp (gradedLaurentMapLarge A B 𝒜) :=
  AlgHom.ext fun b ↦ gradedOuterLaurentMap_C A B 𝒜 b

/-- Move the tensor product of a value with the Laurent polynomial algebra across the two
module structures on the latter. -/
private noncomputable def laurentTensorTransport (M : Type uM) [AddCommGroup M] [Module B M] :
    (letI : AddCommMonoid (LaurentPolynomial B) :=
        (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
     letI : Algebra B (LaurentPolynomial B) :=
        (constantLaurentMapLarge A B).toRingHom.toAlgebra
     letI : Module B (LaurentPolynomial B) := Algebra.toModule
     LaurentPolynomial B ⊗[B] M) ≃ₗ[B] (LaurentPolynomial B ⊗[B] M) :=
  tensorTransport B (LaurentPolynomial B) M
    ((inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid)
    AddMonoidAlgebra.instAddCommMonoid
    (@Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMapLarge A B).toRingHom.toAlgebra))
    AddMonoidAlgebra.instModule
    (laurentAddCommMonoid_eq B) (laurentModule_heq A B)

private lemma laurentTensorTransport_symm_tmul (M : Type uM) [AddCommGroup M] [Module B M]
    (p : LaurentPolynomial B) (m : M) :
    (laurentTensorTransport A B M).symm (p ⊗ₜ[B] m) =
      (letI : AddCommMonoid (LaurentPolynomial B) :=
          (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
       letI : Algebra B (LaurentPolynomial B) :=
          (constantLaurentMapLarge A B).toRingHom.toAlgebra
       letI : Module B (LaurentPolynomial B) := Algebra.toModule
       p ⊗ₜ[B] m) :=
  tensorTransport_symm_tmul B (LaurentPolynomial B) M
    ((inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid)
    AddMonoidAlgebra.instAddCommMonoid
    (@Algebra.toModule B (LaurentPolynomial B) _ _
      ((constantLaurentMapLarge A B).toRingHom.toAlgebra))
    AddMonoidAlgebra.instModule
    (laurentAddCommMonoid_eq B) (laurentModule_heq A B) p m

end AlgebraMaps

/-! ### The argument on the restricted domain -/

section Domain

universe uM u v

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

variable (Q)

/-- Flat base change along `B → B[T, T⁻¹]`, in the module structure the hypothesis produces. -/
private lemma laurentBaseChange (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (hF : PreservesFlatBaseChange Q F) :
    letI : AddCommMonoid (LaurentPolynomial B) :=
      (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
    letI : Algebra B (LaurentPolynomial B) :=
      (constantLaurentMapLarge A B).toRingHom.toAlgebra
    letI : Module B (LaurentPolynomial B) := Algebra.toModule
    ∃ e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
        F.obj (algObj Q (LaurentPolynomial B) hL),
      ∀ x, e (1 ⊗ₜ[B] x) =
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x := by
  have hflat : @Module.Flat B (LaurentPolynomial B) _ _
      (@Algebra.toModule B (LaurentPolynomial B) _ _
        ((constantLaurentMapLarge A B).toRingHom.toAlgebra)) := by
    rw [laurentModule_eq A B]
    exact laurentFlat B
  exact hF B (LaurentPolynomial B) hB hL (constantLaurentMapLarge A B) hflat

/-- Flat base change along `B → B[T, T⁻¹]`, in the canonical module structure. -/
private lemma laurentBaseChangeCanonical (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (hF : PreservesFlatBaseChange Q F) :
    ∃ e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
        F.obj (algObj Q (LaurentPolynomial B) hL),
      ∀ x, e (1 ⊗ₜ[B] x) =
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x := by
  classical
  obtain ⟨e, he⟩ := laurentBaseChange Q B hB hL F hF
  let M : Type uM := F.obj (algObj Q B hB)
  let t := laurentTensorTransport.{u, max u v, uM} A B M
  let e₀ : (LaurentPolynomial B ⊗[B] M) ≃ F.obj (algObj Q (LaurentPolynomial B) hL) :=
    t.symm.toEquiv.trans e.toEquiv
  have h₀ : ∀ x y : LaurentPolynomial B ⊗[B] M, e₀ (x + y) = e₀ x + e₀ y := by
    intro x y
    change e (t.symm (x + y)) = e (t.symm x) + e (t.symm y)
    rw [map_add, map_add]
  let e' : (LaurentPolynomial B ⊗[B] M) ≃+ F.obj (algObj Q (LaurentPolynomial B) hL) :=
    { toEquiv := e₀, map_add' := h₀ }
  have he' (x : M) : e' (1 ⊗ₜ[B] x) =
      F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x := by
    change e (t.symm (1 ⊗ₜ[B] x)) = _
    rw [laurentTensorTransport_symm_tmul A B M]
    exact he x
  have he'_tmul (q : LaurentPolynomial B) (x : M) :
      e' (q ⊗ₜ[B] x) = q • F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x := by
    change e (t.symm (q ⊗ₜ[B] x)) = _
    rw [laurentTensorTransport_symm_tmul A B M]
    let : AddCommMonoid (LaurentPolynomial B) :=
      (inferInstance : CommRing (LaurentPolynomial B)).toCommSemiring.toAddCommMonoid
    let : Algebra B (LaurentPolynomial B) :=
      (constantLaurentMapLarge A B).toRingHom.toAlgebra
    let : Module B (LaurentPolynomial B) := Algebra.toModule
    exact flatBaseChange_tmul Q B (LaurentPolynomial B) hB hL F
      (constantLaurentMapLarge A B) e he q x
  let eₚ : (LaurentPolynomial B ⊗[B] M) ≃ₗ[LaurentPolynomial B]
      F.obj (algObj Q (LaurentPolynomial B) hL) := {
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

private lemma laurentBaseChange_weightedSum (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
      F.obj (algObj Q (LaurentPolynomial B) hL))
    (he : ∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x)
    (y : ℤ →₀ F.obj (algObj Q B hB)) :
    e ((laurentTensorCoefficients B (F.obj (algObj Q B hB))).symm y) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m) := by
  rw [laurentTensorCoefficients_symm_apply]
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ flatBaseChange_tmul Q B (LaurentPolynomial B) hB hL F
    (constantLaurentMapLarge A B) e he (LaurentPolynomial.T k) (y k)

/-- Evaluating at `1` undoes any algebra map `B → B[T, T⁻¹]` that it is a retraction of. -/
private lemma map_evalLaurentOne_map (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (f : B →ₐ[A] LaurentPolynomial B)
    (hf : (evalLaurentOne A B).comp f = AlgHom.id A B) (m : F.obj (algObj Q B hB)) :
    F.map (algMor Q (evalLaurentOne A B) hL hB) (F.map (algMor Q f hB hL) m) = m := by
  rw [map_algMor_comp F f (evalLaurentOne A B) hB hL hB, map_algMor_congr F hf hB hB,
    map_algMor_id]

private lemma laurentBaseChange_eval_tmul_T (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
      F.obj (algObj Q (LaurentPolynomial B) hL))
    (he : ∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x)
    (k : ℤ) (m : F.obj (algObj Q B hB)) :
    F.map (algMor Q (evalLaurentOne A B) hL hB)
      (e ((LaurentPolynomial.T k : LaurentPolynomial B) ⊗ₜ[B] m)) = m := by
  rw [flatBaseChange_tmul Q B (LaurentPolynomial B) hB hL F (constantLaurentMapLarge A B) e he]
  let m' : F.obj (algObj Q (LaurentPolynomial B) hL) :=
    F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m
  change F.map (algMor Q (evalLaurentOne A B) hL hB)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') = m
  rw [F.map_smul]
  have ht : evalLaurentOne A B (LaurentPolynomial.T k) = 1 := by
    change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ) (LaurentPolynomial.T k) = 1
    simp
  change evalLaurentOne A B (LaurentPolynomial.T k) •
      F.map (algMor Q (evalLaurentOne A B) hL hB) m' = m
  rw [ht, one_smul]
  exact map_evalLaurentOne_map Q B hB hL F _ (evalLaurentOne_comp_constant A B) m

private lemma laurentBaseChange_eval (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
      F.obj (algObj Q (LaurentPolynomial B) hL))
    (he : ∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x)
    (z : LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) :
    F.map (algMor Q (evalLaurentOne A B) hL hB) (e z) =
      laurentCounit B (F.obj (algObj Q B hB)) z := by
  obtain ⟨y, rfl⟩ := (laurentTensorCoefficients B (F.obj (algObj Q B hB))).symm.surjective z
  rw [laurentTensorCoefficients_symm_apply]
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦
    (laurentBaseChange_eval_tmul_T Q B hB hL F e he k (y k)).trans
      (laurentCounit_tmul_T B _ k (y k)).symm

private lemma laurentBaseChange_eval_graded (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
      F.obj (algObj Q (LaurentPolynomial B) hL))
    (he : ∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x)
    (x : F.obj (algObj Q B hB)) :
    laurentCounit B (F.obj (algObj Q B hB))
      (e.symm (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x)) = x := by
  rw [← laurentBaseChange_eval Q B hB hL F e he]
  let m' : F.obj (algObj Q (LaurentPolynomial B) hL) :=
    F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x
  change F.map (algMor Q (evalLaurentOne A B) hL hB) (e (e.symm m')) = x
  rw [e.apply_symm_apply]
  exact map_evalLaurentOne_map Q B hB hL F _ (evalLaurentOne_comp_graded A B 𝒜) x

/-- Two composites of transition maps agree when the composites of morphisms agree. Stated
abstractly: at independent universes the kernel cannot afford to verify this shape with the
three Laurent-polynomial algebras substituted in. -/
private lemma map_map_eq_of_comp_eq (F : ModuleValuedFunctorOn.{uM} Q.ι)
    {X Y Y' Z : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (g' : X ⟶ Y') (f : Y ⟶ Z) (f' : Y' ⟶ Z)
    (h : g ≫ f = g' ≫ f') (x : F.obj X) : F.map f (F.map g x) = F.map f' (F.map g' x) :=
  (F.map_comp_apply g f x).symm.trans ((F.congr_map_apply h x).trans (F.map_comp_apply g' f' x))

private lemma map_gradedOuter_weightedTerm (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) (m : F.obj (algObj Q B hB)) :
    F.map (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL)
      ((LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m) =
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
        F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL)
          (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) m) := by
  let m' : F.obj (algObj Q (LaurentPolynomial B) hL) :=
    F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m
  change F.map (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') = _
  rw [F.map_smul]
  change gradedOuterLaurentMap A B 𝒜 (LaurentPolynomial.T k) •
    F.map (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL) m' = _
  rw [gradedOuterLaurentMap_T]
  refine congrArg (fun z => (LaurentPolynomial.T k :
    LaurentPolynomial (LaurentPolynomial B)) • z) ?_
  refine map_map_eq_of_comp_eq Q F _ _ _ _ ?_ _
  rw [algMor_comp, algMor_comp, gradedOuter_comp_constant A B 𝒜]

private lemma map_diagonal_weightedTerm (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (k : ℤ) (m : F.obj (algObj Q B hB)) :
    F.map (algMor Q (diagonalLaurentMap A B) hL hLL)
      ((LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m) =
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
        F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL)
          ((LaurentPolynomial.T k : LaurentPolynomial B) •
            F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m) := by
  let m' : F.obj (algObj Q (LaurentPolynomial B) hL) :=
    F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m
  change F.map (algMor Q (diagonalLaurentMap A B) hL hLL)
    ((LaurentPolynomial.T k : LaurentPolynomial B) • m') =
    (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
      F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL)
        ((LaurentPolynomial.T k : LaurentPolynomial B) • m')
  rw [F.map_smul]
  change diagonalLaurentMap A B (LaurentPolynomial.T k) •
    F.map (algMor Q (diagonalLaurentMap A B) hL hLL) m' = _
  rw [diagonalLaurentMap_T]
  have hc : F.map (algMor Q (diagonalLaurentMap A B) hL hLL) m' =
      F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL) m' := by
    refine map_map_eq_of_comp_eq Q F _ _ _ _ ?_ _
    rw [algMor_comp, algMor_comp, diagonal_comp_constant A B]
  rw [hc, F.map_smul]
  let m'' : F.obj (algObj Q (LaurentPolynomial (LaurentPolynomial B)) hLL) :=
    F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL) m'
  change ((LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) *
      LaurentPolynomial.C (LaurentPolynomial.T k)) • m'' =
    (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
      (LaurentPolynomial.C (LaurentPolynomial.T k)) • m''
  exact mul_smul (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B))
    (LaurentPolynomial.C (LaurentPolynomial.T k)) m''

/-- Two restriction maps with a common first leg agree on the image of that leg. Stated
abstractly: at independent universes the kernel cannot afford to verify this shape with the
three Laurent-polynomial algebras substituted in. -/
private lemma map_eq_of_comp_eq (F : ModuleValuedFunctorOn.{uM} Q.ι)
    {X Y Z : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (f d : Y ⟶ Z) (h : g ≫ f = g ≫ d)
    (x : F.obj X) : F.map f (F.map g x) = F.map d (F.map g x) :=
  (F.map_comp_apply g f x).symm.trans
    ((F.congr_map_apply h x).trans (F.map_comp_apply g d x))


/-- Termwise comparison of the flat base change expansion along `B[T, T⁻¹] → B[T, T⁻¹][S, S⁻¹]`
with the image of a weighted sum under a transition map. -/
private lemma outerBaseChange_sum (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (φ : algObj Q (LaurentPolynomial B) hL ⟶
      algObj Q (LaurentPolynomial (LaurentPolynomial B)) hLL)
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
        F.obj (algObj Q (LaurentPolynomial B) hL)) ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
      F.obj (algObj Q (LaurentPolynomial (LaurentPolynomial B)) hLL))
    (he : ∀ z, e (1 ⊗ₜ[LaurentPolynomial B] z) =
      F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL) z)
    (f g : ℤ → F.obj (algObj Q B hB) → F.obj (algObj Q (LaurentPolynomial B) hL))
    (hfg : ∀ k m, F.map φ (g k m) =
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) •
        F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL) (f k m))
    (y : ℤ →₀ F.obj (algObj Q B hB)) :
    e (y.sum (fun k m ↦
      (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
        LaurentPolynomial B] f k m)) = F.restrictₛₗ φ (y.sum g) :=
  finsupp_sum_map_congr _ _ _ _ y _ _ e.toLinearMap.toAddMonoidHom
    (F.restrictₛₗ φ).toAddMonoidHom fun k m ↦
      (flatBaseChange_tmul Q (LaurentPolynomial B) (LaurentPolynomial (LaurentPolynomial B))
        hL hLL F (constantLaurentMapLarge A (LaurentPolynomial B)) e he _ _).trans (hfg k m).symm

/-- Functoriality through two Laurent-polynomial extensions. -/
private lemma gradedOuter_eq_diagonal_map (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (x : F.obj (algObj Q B hB)) :
    F.restrictₛₗ (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL)
      (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x) =
    F.restrictₛₗ (algMor Q (diagonalLaurentMap A B) hL hLL)
      (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x) :=
  map_map_eq_of_comp_eq Q F _ _ _ _
    (by rw [algMor_comp, algMor_comp, diagonal_comp_graded A B 𝒜]) x

/-- The coefficient comparison normalizes two nested Laurent tensor expansions. -/
private lemma weightCoefficients_of_expansion (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial (LaurentPolynomial B) ⊗[LaurentPolynomial B]
        F.obj (algObj Q (LaurentPolynomial B) hL)) ≃ₗ[LaurentPolynomial (LaurentPolynomial B)]
      F.obj (algObj Q (LaurentPolynomial (LaurentPolynomial B)) hLL))
    (he : ∀ z, e (1 ⊗ₜ[LaurentPolynomial B] z) =
      F.map (algMor Q (constantLaurentMapLarge A (LaurentPolynomial B)) hL hLL) z)
    (x : F.obj (algObj Q B hB)) (y : ℤ →₀ F.obj (algObj Q B hB))
    (hy : F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m)) :
    ∀ k, y k ∈ weightSpace Q B hB hL F 𝒜 k := by
  let gradedValue (m : F.obj (algObj Q B hB)) :
      F.obj (algObj Q (LaurentPolynomial B) hL) :=
    F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) m
  let weightedValue (k : ℤ) (m : F.obj (algObj Q B hB)) :
      F.obj (algObj Q (LaurentPolynomial B) hL) :=
    (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m
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
        F.restrictₛₗ (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL)
          (y.sum weightedValue) := 
          outerBaseChange_sum Q B hB hL hLL F (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL)
            e he (fun _ m ↦ gradedValue m) weightedValue
            (map_gradedOuter_weightedTerm Q B hB hL hLL F 𝒜) y
      _ = F.restrictₛₗ (algMor Q (gradedOuterLaurentMap A B 𝒜) hL hLL)
          (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x) := by
            rw [hy]
            simp only [weightedValue]
            rfl
      _ = F.restrictₛₗ (algMor Q (diagonalLaurentMap A B) hL hLL)
          (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x) :=
            gradedOuter_eq_diagonal_map Q B hB hL hLL F 𝒜 x
      _ = F.restrictₛₗ (algMor Q (diagonalLaurentMap A B) hL hLL)
          (y.sum weightedValue) := by
            rw [hy]
            simp only [weightedValue]
            rfl
      _ = e (y.sum (fun k m ↦
        (LaurentPolynomial.T k : LaurentPolynomial (LaurentPolynomial B)) ⊗ₜ[
          LaurentPolynomial B] weightedValue k m)) :=
        (outerBaseChange_sum Q B hB hL hLL F (algMor Q (diagonalLaurentMap A B) hL hLL)
          e he weightedValue weightedValue (map_diagonal_weightedTerm Q B hB hL hLL F) y).symm
  have hz₂ : ∀ (j : ℤ), weightedValue j (0 : F.obj (algObj Q B hB)) = 0 := by
    intro j
    change (LaurentPolynomial.T j : LaurentPolynomial B) •
      F.map (algMor Q (constantLaurentMapLarge A B) hB hL)
        (0 : F.obj (algObj Q B hB)) = 0
    rw [map_zero, smul_zero]
  intro k
  change weightedValue k (y k) = gradedValue (y k)
  exact (laurentCoefficients_eq_of_tensor_sum (LaurentPolynomial B)
    (F.obj (algObj Q B hB)) (F.obj (algObj Q (LaurentPolynomial B) hL))
    y (fun _ m ↦ gradedValue m) weightedValue (fun _ ↦ map_zero _) hz₂ hs k).symm

private lemma map_sum_of_weights (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (y : ℤ →₀ F.obj (algObj Q B hB))
    (hy : ∀ k, y k ∈ weightSpace Q B hB hL F 𝒜 k) :
    F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) (y.sum (fun _ m ↦ m)) =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m) := by
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (hy k).symm

private lemma weightDecomposition_unique (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (e : (LaurentPolynomial B ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[LaurentPolynomial B]
      F.obj (algObj Q (LaurentPolynomial B) hL))
    (he : ∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q (constantLaurentMapLarge A B) hB hL) x)
    (x : F.obj (algObj Q B hB)) (y z : ℤ →₀ F.obj (algObj Q B hB))
    (hy : ∀ k, y k ∈ weightSpace Q B hB hL F 𝒜 k)
    (hz : ∀ k, z k ∈ weightSpace Q B hB hL F 𝒜 k)
    (hyx : y.sum (fun _ m ↦ m) = x) (hzx : z.sum (fun _ m ↦ m) = x) : y = z := by
  apply (laurentTensorCoefficients B (F.obj (algObj Q B hB))).symm.injective
  apply e.injective
  rw [laurentBaseChange_weightedSum Q B hB hL F e he y,
    laurentBaseChange_weightedSum Q B hB hL F e he z, ← map_sum_of_weights Q B hB hL F 𝒜 y hy,
    ← map_sum_of_weights Q B hB hL F 𝒜 z hz, hyx, hzx]

/-- **Stacks 06UZ (1) on a restricted domain of algebras.** Every element of the value of a
module-valued functor on a domain of algebras at a graded algebra of that domain has a unique
finite decomposition into elements of its integer weight spaces, provided the functor commutes
with flat base change inside the domain and the domain contains the two iterated Laurent
polynomial algebras of the graded algebra.

No `@[stacks]` attribute is placed here: the tagged statement of 06UZ (1) is
`AdequateFunctor.Laurent.existsUnique_finsupp_weightSpace_eq`, over all commutative algebras,
and this is that statement transported to a restricted domain. -/
public lemma existsUnique_finsupp_weightSpace_eq (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (hF : PreservesFlatBaseChange Q F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (x : F.obj (algObj Q B hB)) :
    ∃! y : ℤ →₀ F.obj (algObj Q B hB),
      (∀ k, y k ∈ weightSpace Q B hB hL F 𝒜 k) ∧ y.sum (fun _ z ↦ z) = x := by
  classical
  obtain ⟨e₁, he₁⟩ := laurentBaseChangeCanonical Q B hB hL F hF
  obtain ⟨e₂, he₂⟩ := laurentBaseChangeCanonical Q (LaurentPolynomial B) hL hLL F hF
  let z : F.obj (algObj Q (LaurentPolynomial B) hL) :=
    F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x
  let y : ℤ →₀ F.obj (algObj Q B hB) :=
    laurentTensorCoefficients B (F.obj (algObj Q B hB)) (e₁.symm z)
  have hy : F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) x =
      y.sum (fun k m ↦ (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) m) :=
    ((e₁.apply_symm_apply z).symm.trans (congrArg e₁
      ((laurentTensorCoefficients B _).symm_apply_apply (e₁.symm z)).symm)).trans
      (laurentBaseChange_weightedSum Q B hB hL F e₁ he₁ y)
  have hw : ∀ k, y k ∈ weightSpace Q B hB hL F 𝒜 k :=
    weightCoefficients_of_expansion Q B hB hL hLL F 𝒜 e₂ he₂ x y hy
  have hsum : y.sum (fun _ m ↦ m) = x :=
    laurentCoefficients_sum_of_counit B (F.obj (algObj Q B hB))
      (fun m ↦ e₁.symm (F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) m))
      (laurentCounit B (F.obj (algObj Q B hB)))
      (laurentCounit_tmul_T B (F.obj (algObj Q B hB)))
      (laurentBaseChange_eval_graded Q B hB hL F 𝒜 e₁ he₁) x
  exact ⟨y, ⟨hw, hsum⟩,
    fun y' hy' ↦ weightDecomposition_unique Q B hB hL F 𝒜 e₁ he₁ x y' y hy'.1 hw hy'.2 hsum⟩

/-- An element lying in two distinct weight spaces of a functor commuting with flat base change
inside the domain is zero. -/
public lemma weightSpace_eq_zero_of_mem_two_weights (B : Type (max u v)) [CommRing B]
    [Algebra A B] (hB : Q (CommAlgCat.of A B))
    (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (hF : PreservesFlatBaseChange Q F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {k l : ℤ} (hkl : k ≠ l)
    {x : F.obj (algObj Q B hB)}
    (hk : x ∈ weightSpace Q B hB hL F 𝒜 k)
    (hl : x ∈ weightSpace Q B hB hL F 𝒜 l) : x = 0 := by
  classical
  obtain ⟨y, -, hyuniq⟩ :=
    existsUnique_finsupp_weightSpace_eq Q B hB hL hLL F hF 𝒜 x
  have hsingle (j : ℤ) :
      Finsupp.sum (Finsupp.single j x) (fun _ z => z) = x := by simp
  have hs (m : ℤ) (hm : x ∈ weightSpace Q B hB hL F 𝒜 m) (j : ℤ) :
      (Finsupp.single m x : ℤ →₀ F.obj (algObj Q B hB)) j ∈ weightSpace Q B hB hL F 𝒜 j := by
    by_cases hj : j = m
    · simpa [hj] using hm
    · simpa [Finsupp.single_apply, Ne.symm hj] using weightSpace_zero_mem hB hL F 𝒜 j
  have hval := congrArg (fun z : ℤ →₀ F.obj (algObj Q B hB) => z k)
    ((hyuniq _ ⟨hs k hk, hsingle k⟩).trans (hyuniq _ ⟨hs l hl, hsingle l⟩).symm)
  simpa [Finsupp.single_eq_of_ne hkl] using hval

end Domain

end AdequateFunctor.LaurentDomain

end
