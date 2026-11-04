module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerTensorBaseChange
public import StacksFrontier.Homology.Tor.TorOnePresentationKernel
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The cokernel in degree `-2` of `(A ⊗_R B) ⊗_B L ⟶ L_A` is `Tor_1^R(A, B)`

Let `P = R[X] → B` be a presentation with generators `f_t` of its kernel `I`, and let
`P_A = A[X] → A ⊗_R B` be its base change, with generators `1 ⊗ f_t`. This file proves the last
step of the proof of [Stacks, Tag 09DB]: the cokernel of the degree `-2` component
`(A ⊗_R B) ⊗_B (Rel/TrivRel) → Rel_A/TrivRel_A` of the map of Lichtenbaum–Schlessinger complexes
is `Tor_1^R(A, B)`, as an `A ⊗_R B`-module.

Write `F = ⊕_t P` and `F_A = ⊕_t P_A`. The map
`μ : F_A → A ⊗_R I`, `e_t ↦ 1 ⊗ f_t`, is onto, carries `Rel_A` onto
`Ker(A ⊗_R I → A ⊗_R P) = Tor_1^R(A, B)` (`RingTheory.TorIndependence.torOnePresentationKerEquiv`),
and its kernel is the image of `A ⊗_R Rel` (right exactness of `A ⊗_R -` applied to
`Rel → F → I → 0`), which is also the kernel of `Rel_A → coker`.

## Main definitions

* `CommAlgCat.torOneTensorProductModule`: `Tor_1^R(A, B)` with its canonical
  `A ⊗_R B`-module structure.

## Main results

* `Algebra.Presentation.cokernelNegTwoLinearEquiv`: the cokernel of the degree `-2` component is
  `A ⊗_R B`-linearly equivalent to `Tor_1^R(A, B)`.
* `Algebra.Presentation.cokernelNegTwoIsoTorOne`: the cokernel of the degree `-2` component is
  isomorphic to `CommAlgCat.torOneTensorProductModule R A B`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

universe u

namespace Algebra.Presentation

open RingTheory.TorIndependence

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-! ### `A ⊗_R M` and the extension of scalars along `R → A` -/

/-- `A`, read as an `R`-module in the two ways. -/
def restrictSelfEquiv :
    A ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) where
  toFun a := a
  invFun a := a
  map_add' _ _ := rfl
  map_smul' r a := (Algebra.smul_def r a).trans rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `A ⊗_R M` is the extension of scalars of `M` along `R → A`. -/
def tensorExtEquiv (M : Type u) [AddCommGroup M] [Module R M] :
    A ⊗[R] M ≃+ (extA R A).obj (ModuleCat.of R M) :=
  (_root_.TensorProduct.congr (restrictSelfEquiv A) (LinearEquiv.refl R M)).toAddEquiv

/-- `tensorExtEquiv` sends `a ⊗ m` to `a ⊗ m`. -/
theorem tensorExtEquiv_tmul (M : Type u) [AddCommGroup M] [Module R M] (a : A) (m : M) :
    tensorExtEquiv A M (a ⊗ₜ m) = a ⊗ₜ[R, algebraMap R A] m :=
  rfl

/-- `tensorExtEquiv` is `A`-linear. -/
theorem tensorExtEquiv_smul (M : Type u) [AddCommGroup M] [Module R M] (a : A)
    (w : A ⊗[R] M) : tensorExtEquiv A M (a • w) = a • tensorExtEquiv A M w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a' m =>
    rw [TensorProduct.smul_tmul', tensorExtEquiv_tmul, tensorExtEquiv_tmul]
    exact (ModuleCat.ExtendScalars.smul_tmul (algebraMap R A) a a' (M := ModuleCat.of R M) m).symm
  | add w w' hw hw' => rw [smul_add, map_add, map_add, hw, hw', smul_add]

/-- Under `tensorExtEquiv`, extension of scalars of an `R`-linear map `g` is `g.baseChange A`. -/
theorem extA_map_tensorExtEquiv {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (g : M →ₗ[R] N) (w : A ⊗[R] M) :
    ((extA R A).map (ModuleCat.ofHom g)).hom (tensorExtEquiv A M w) =
      tensorExtEquiv A N (g.baseChange A w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a m => rfl
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]

/-! ### The map `μ : F_A → A ⊗_R I` -/

section Mu

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type u} [CommRing B] [Algebra R B] {X T : Type u} (P : Presentation R B X T)

/-- Multiplication by the generator `f_t`, as a map `P → I`. -/
def mulRelation (t : T) : P.Ring →ₗ[R] presentationKer P where
  toFun p := ⟨p * P.relation t, P.ker.mul_mem_left p (P.relation_mem_ker t)⟩
  map_add' p q := Subtype.ext (add_mul p q _)
  map_smul' r p := Subtype.ext (smul_mul_assoc r p _)

/-- The map `F = ⊕_t P → I`, `e_t ↦ f_t`. -/
def relationToKer : (T →₀ P.Ring) →ₗ[R] presentationKer P :=
  Finsupp.lsum R P.mulRelation

/-- The map `F → I`, read in `P`, is `relationMap P`. -/
theorem coe_relationToKer (y : T →₀ P.Ring) : (P.relationToKer y : P.Ring) = relationMap P y := by
  rw [relationToKer, Finsupp.lsum_apply, relationMap_apply, Finsupp.sum, Finsupp.sum,
    Submodule.coe_sum]
  rfl

/-- The map `F → I`, `e_t ↦ f_t`, is onto. -/
theorem relationToKer_surjective : Function.Surjective P.relationToKer := by
  intro i
  have hi : (i : P.Ring) ∈ Submodule.span P.Ring (Set.range P.relation) := by
    rw [← Ideal.span, P.span_range_relation_eq_ker]
    exact i.2
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hi
  refine ⟨c, Subtype.ext ?_⟩
  rw [coe_relationToKer, relationMap_apply, ← hc]
  rfl

/-- The sequence `Rel → F → I` is exact. -/
theorem relationToKer_exact :
    Function.Exact ((relations P).restrictScalars R).subtype P.relationToKer := by
  intro y
  constructor
  · intro hy
    refine ⟨⟨y, ?_⟩, rfl⟩
    have := congrArg Subtype.val hy
    rw [coe_relationToKer] at this
    exact LinearMap.mem_ker.2 this
  · rintro ⟨r, rfl⟩
    exact Subtype.ext ((coe_relationToKer P _).trans (LinearMap.mem_ker.1 r.2))

/-- The component `P_A → A ⊗_R I`, `q ↦ q · (1 ⊗ f_t)`. -/
def muComponent (t : T) :
    (P.tensorBaseChange A).Ring →ₗ[A] (extA R A).obj (ModuleCat.of R (presentationKer P)) where
  toFun q := tensorExtEquiv A _
    ((P.mulRelation t).baseChange A ((MvPolynomial.algebraTensorAlgEquiv R A).symm q))
  map_add' q q' := by rw [map_add, map_add, map_add]
  map_smul' a q := by
    rw [map_smul, LinearMap.map_smul, tensorExtEquiv_smul]
    rfl

/-- **The map `μ : F_A → A ⊗_R I`**, `e_t ↦ 1 ⊗ f_t`. -/
def mu : ((T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) →ₗ[A]
    (extA R A).obj (ModuleCat.of R (presentationKer P)) :=
  Finsupp.lsum A (Sum.elim (P.muComponent A) fun e => e.elim)

/-- `μ` sends `q · e_t` to `q · (1 ⊗ f_t)`. -/
theorem mu_single_inl (t : T) (q : (P.tensorBaseChange A).Ring) :
    P.mu A (Finsupp.single (Sum.inl t) q) = P.muComponent A t q := by
  rw [mu, Finsupp.lsum_single]
  rfl

/-- On the image of `p ∈ P` in `P_A`, the component of `μ` at `t` is `1 ⊗ p f_t`. -/
theorem muComponent_map (t : T) (p : P.Ring) :
    P.muComponent A t (MvPolynomial.map (algebraMap R A) p) =
      tensorExtEquiv A _ ((1 : A) ⊗ₜ[R] P.mulRelation t p) := by
  show tensorExtEquiv A _ ((P.mulRelation t).baseChange A
    ((MvPolynomial.algebraTensorAlgEquiv R A).symm (MvPolynomial.map (algebraMap R A) p))) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, LinearMap.baseChange_tmul]

/-- `μ` on the image of `F → F_A` is `1 ⊗ (F → I)`. -/
theorem mu_freeMap (y : T →₀ P.Ring) :
    P.mu A ((P.tensorBaseChangeHom A).freeMap y) =
      tensorExtEquiv A _ ((1 : A) ⊗ₜ[R] P.relationToKer y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, TensorProduct.tmul_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, TensorProduct.tmul_add, map_add]
  | single t p =>
    rw [LichtenbaumSchlessingerHom.freeMap_single, mu_single_inl, tensorBaseChangeHom_ringHom,
      muComponent_map]
    congr 1
    rw [relationToKer, Finsupp.lsum_single]

/-- Base change of multiplication by `x` is multiplication by `1 ⊗ x`. -/
private theorem baseChange_mulLeft_apply {S : Type u} [CommRing S] [Algebra R S] (x : S)
    (w : A ⊗[R] S) : (LinearMap.mulLeft R x).baseChange A w = ((1 : A) ⊗ₜ[R] x) * w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero]
  | tmul a p => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.baseChange_tmul]; rfl
  | add w w' hw hw' => rw [mul_add, map_add, hw, hw']

/-- `μ` intertwines multiplication by a variable on `F_A` with multiplication by it on `I`. -/
theorem mu_X_smul (i : X) (x : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) :
    P.mu A ((MvPolynomial.X i : (P.tensorBaseChange A).Ring) • x) =
      ((extA R A).map (presentationKerMul P (MvPolynomial.X i))).hom (P.mu A x) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [smul_zero, map_zero, map_zero]
  | add x x' hx hx' => rw [smul_add, map_add, map_add, hx, hx', map_add]
  | single t' q =>
    rcases t' with t | e
    · rw [Finsupp.smul_single, mu_single_inl, mu_single_inl, smul_eq_mul]
      show tensorExtEquiv A _ ((P.mulRelation t).baseChange A
          ((MvPolynomial.algebraTensorAlgEquiv R A).symm (MvPolynomial.X i * q))) =
        ((extA R A).map (ModuleCat.ofHom _)).hom (tensorExtEquiv A _ ((P.mulRelation t).baseChange A
          ((MvPolynomial.algebraTensorAlgEquiv R A).symm q)))
      rw [extA_map_tensorExtEquiv, map_mul, MvPolynomial.algebraTensorAlgEquiv_symm_X]
      congr 1
      rw [← baseChange_mulLeft_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      exact congrArg (fun f : _ →ₗ[R] _ => f.baseChange A _)
        (LinearMap.ext fun p => Subtype.ext (mul_assoc _ _ _))
    · exact e.elim

/-- The map `A ⊗_R I → A ⊗_R P`. -/
abbrev kerInclusion : (extA R A).obj (ModuleCat.of R (presentationKer P)) ⟶
    (extA R A).obj (ModuleCat.of R P.Ring) :=
  (extA R A).map (ModuleCat.ofHom (presentationKer P).subtype)

/-- An element of `A ⊗_R I` lies in `Ker(A ⊗_R I → A ⊗_R P)` exactly when its image in
`A ⊗_R P` vanishes. -/
theorem mem_presentationTensorKer_iff (z : (extA R A).obj (ModuleCat.of R (presentationKer P))) :
    z ∈ presentationTensorKer A P ↔ (kerInclusion A P).hom z = 0 :=
  Iff.rfl

/-- `μ` followed by `A ⊗_R I → A ⊗_R P` is the map `F_A → P_A`, read in `A ⊗_R P`. -/
theorem extA_map_mu (x : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) :
    (kerInclusion A P).hom (P.mu A x) =
      tensorExtEquiv A P.Ring
        ((MvPolynomial.algebraTensorAlgEquiv R A).symm (relationMap (P.tensorBaseChange A) x)) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add, map_add]
  | single t' q =>
    rcases t' with t | e
    · rw [mu_single_inl, relationMap_single, tensorBaseChange_relation, map_mul,
        MvPolynomial.algebraTensorAlgEquiv_symm_map]
      show (kerInclusion A P).hom
          (tensorExtEquiv A _ ((P.mulRelation t).baseChange A
            ((MvPolynomial.algebraTensorAlgEquiv R A).symm q))) = _
      rw [kerInclusion, extA_map_tensorExtEquiv]
      congr 1
      rw [mul_comm, ← baseChange_mulLeft_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      exact congrArg (fun f : _ →ₗ[R] _ => f.baseChange A _) (LinearMap.ext fun p => mul_comm _ _)
    · exact e.elim

/-- An element of `F_A` is a relation exactly when its image under `μ` lies in
`Ker(A ⊗_R I → A ⊗_R P)`. -/
theorem mem_relations_iff_mu (x : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) :
    x ∈ relations (P.tensorBaseChange A) ↔ P.mu A x ∈ presentationTensorKer A P := by
  rw [mem_presentationTensorKer_iff, extA_map_mu, (tensorExtEquiv A P.Ring).map_eq_zero_iff,
    map_eq_zero_iff _ (MvPolynomial.algebraTensorAlgEquiv R A).symm.injective]
  rfl

/-- `μ` is onto. -/
theorem mu_surjective : Function.Surjective (P.mu A) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a i =>
    obtain ⟨y, rfl⟩ := P.relationToKer_surjective i
    refine ⟨(show A from a) • (P.tensorBaseChangeHom A).freeMap y, ?_⟩
    rw [map_smul, mu_freeMap, ← tensorExtEquiv_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    rfl
  | add z z' hz hz' =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨x', rfl⟩ := hz'
    exact ⟨x + x', map_add _ _ _⟩

/-- The map `F → F_A`, as an `R`-linear map. -/
def freeMapR : (T →₀ P.Ring) →ₗ[R] ((T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) where
  toFun := (P.tensorBaseChangeHom A).freeMap
  map_add' := map_add _
  map_smul' r y := by
    rw [← IsScalarTower.algebraMap_smul P.Ring r y, map_smulₛₗ, tensorBaseChangeHom_ringHom,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]
    rfl

/-- The map `A ⊗_R F → F_A`, `a ⊗ y ↦ a · y`. -/
def tensorFreeMap : A ⊗[R] (T →₀ P.Ring) →ₗ[A]
    ((T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) :=
  LinearMap.liftBaseChange A (P.freeMapR A)

/-- `μ` composed with `A ⊗_R F → F_A` is the base change of `F → I`. -/
theorem mu_tensorFreeMap (w : A ⊗[R] (T →₀ P.Ring)) :
    P.mu A (P.tensorFreeMap A w) = tensorExtEquiv A _ (P.relationToKer.baseChange A w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a y =>
    rw [tensorFreeMap, LinearMap.liftBaseChange_tmul, map_smul]
    show a • P.mu A ((P.tensorBaseChangeHom A).freeMap y) = _
    rw [mu_freeMap, ← tensorExtEquiv_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      LinearMap.baseChange_tmul]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]

/-- The map `A ⊗_R F → F_A` is onto. -/
theorem tensorFreeMap_surjective : Function.Surjective (P.tensorFreeMap A) := by
  intro x
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x x' hx hx' =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hx'
    exact ⟨w + w', map_add _ _ _⟩
  | single t' q =>
    rcases t' with t | e
    · obtain ⟨w, rfl⟩ := (MvPolynomial.algebraTensorAlgEquiv R A).surjective q
      induction w using TensorProduct.induction_on with
      | zero => exact ⟨0, by rw [map_zero, map_zero, Finsupp.single_zero]⟩
      | tmul a p =>
        refine ⟨a ⊗ₜ Finsupp.single t p, ?_⟩
        rw [tensorFreeMap, LinearMap.liftBaseChange_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul,
          ← Finsupp.smul_single]
        show a • (P.tensorBaseChangeHom A).freeMap (Finsupp.single t p) = _
        rw [LichtenbaumSchlessingerHom.freeMap_single, tensorBaseChangeHom_ringHom]
      | add w w' hw hw' =>
        obtain ⟨v, hv⟩ := hw
        obtain ⟨v', hv'⟩ := hw'
        exact ⟨v + v', by rw [map_add, hv, hv', map_add, Finsupp.single_add]⟩
    · exact e.elim

/-- The span `P_A · Rel` of the image of the relations of `P` in `F_A`. -/
abbrev relationsImage : Submodule (P.tensorBaseChange A).Ring
    ((T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) :=
  Submodule.span _ (Set.range fun r : relations P =>
    (P.tensorBaseChangeHom A).freeMap (r : T →₀ P.Ring))

/-- **The kernel of `μ` is contained in `P_A · Rel`**: right exactness of `A ⊗_R -` on
`Rel → F → I → 0`. -/
theorem mem_relationsImage_of_mu_eq_zero
    (x : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) (hx : P.mu A x = 0) :
    x ∈ P.relationsImage A := by
  obtain ⟨w, rfl⟩ := P.tensorFreeMap_surjective A x
  rw [mu_tensorFreeMap, (tensorExtEquiv A _).map_eq_zero_iff, LinearMap.baseChange_eq_ltensor]
    at hx
  obtain ⟨z, rfl⟩ := ((lTensor_exact A P.relationToKer_exact
    P.relationToKer_surjective) w).1 hx
  clear hx
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul a r =>
    rw [LinearMap.lTensor_tmul, tensorFreeMap, LinearMap.liftBaseChange_tmul,
      ← IsScalarTower.algebraMap_smul (P.tensorBaseChange A).Ring a]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  | add z z' hz hz' => rw [map_add, map_add]; exact add_mem hz hz'

/-- The kernel of `μ` is stable under multiplication by elements of `P_A`. -/
theorem mu_smul_eq_zero (c : (P.tensorBaseChange A).Ring) :
    ∀ x : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring, P.mu A x = 0 →
      P.mu A (c • x) = 0 := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    intro x hx
    rw [← MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_smul, map_smul, hx, smul_zero]
  | add p q hp hq =>
    intro x hx
    rw [add_smul, map_add, hp x hx, hq x hx, add_zero]
  | mul_X p i hp =>
    intro x hx
    rw [mul_smul]
    exact hp _ (by rw [mu_X_smul, hx, map_zero])

/-- The elements of `F_A` killed by `μ`, a `P_A`-submodule. -/
def muKer : Submodule (P.tensorBaseChange A).Ring
    ((T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) where
  carrier := {x | P.mu A x = 0}
  add_mem' {x x'} hx hx' := by
    change P.mu A (x + x') = 0
    rw [map_add, show P.mu A x = 0 from hx, show P.mu A x' = 0 from hx', add_zero]
  zero_mem' := map_zero _
  smul_mem' c x hx := P.mu_smul_eq_zero A c x hx

/-- **The kernel of `μ` is `P_A · Rel`.** -/
theorem mu_eq_zero_iff (x : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) :
    P.mu A x = 0 ↔ x ∈ P.relationsImage A := by
  refine ⟨P.mem_relationsImage_of_mu_eq_zero A x, fun hx => ?_⟩
  have h : P.relationsImage A ≤ P.muKer A := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    show P.mu A _ = 0
    rw [mu_freeMap, ((relationToKer_exact P) (r : T →₀ P.Ring)).2 ⟨r, rfl⟩,
      TensorProduct.tmul_zero, map_zero]
  exact h hx

end Mu

/-! ### The cokernel in degree `-2` -/

section Cokernel

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type u} [CommRing B] [Algebra R B] {X T : Type u} (P : Presentation R B X T)

/-- The image `P_A · (Rel/TrivRel)` of the relations of `P` in `Rel_A/TrivRel_A`. -/
abbrev relationQuotientImage : Submodule (P.tensorBaseChange A).Ring
    (relationQuotient (P.tensorBaseChange A)) :=
  Submodule.span _ (Set.range (P.tensorBaseChangeHom A).relationQuotientMap)

/-- The component of `tensorBaseChangeComplexMap` in degree `n` sends `1 ⊗ z` to the image of
`z` under `(P.tensorBaseChangeHom A).complexMap`. -/
theorem tensorBaseChangeComplexMap_f_one_tmul (n : ℤ)
    (z : (lichtenbaumSchlessingerComplex P).complex.X n) :
    ((P.tensorBaseChangeComplexMap A).f n).hom
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap B (A ⊗[R] B))).unit.app _ z) =
      ((P.tensorBaseChangeHom A).complexMap.f n).hom z := by
  rw [tensorBaseChangeComplexMap_f]
  exact congrArg (fun φ => φ.hom z)
    (((ModuleCat.extendRestrictScalarsAdj (algebraMap B (A ⊗[R] B))).homEquiv _ _).apply_symm_apply
      ((P.tensorBaseChangeHom A).complexMap.f n))

/-- `1 ⊗ -` on `Rel_A/TrivRel_A`, landing in the degree `-2` term of `L_A`. -/
def relationOneTmul (n : relationQuotient (P.tensorBaseChange A)) :
    (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex.X (-2) :=
  (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationIso.inv.hom
    ((1 : A ⊗[R] B) ⊗ₜ[(P.tensorBaseChange A).Ring] n)

/-- `relationOneTmul` is additive. -/
theorem relationOneTmul_add (n n' : relationQuotient (P.tensorBaseChange A)) :
    P.relationOneTmul A (n + n') = P.relationOneTmul A n + P.relationOneTmul A n' := by
  rw [relationOneTmul, TensorProduct.tmul_add, map_add]
  rfl

/-- `relationOneTmul` is linear along `P_A → A ⊗_R B`. -/
theorem relationOneTmul_smul (q : (P.tensorBaseChange A).Ring)
    (n : relationQuotient (P.tensorBaseChange A)) :
    P.relationOneTmul A (q • n) = algebraMap _ (A ⊗[R] B) q • P.relationOneTmul A n := by
  rw [relationOneTmul, relationOneTmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- `1 ⊗` the image of `n ∈ Rel/TrivRel` in `Rel_A/TrivRel_A` is the image under the degree
`-2` component of `1 ⊗ (1 ⊗ n)`. -/
theorem relationOneTmul_relationQuotientMap (n : relationQuotient P) :
    P.relationOneTmul A ((P.tensorBaseChangeHom A).relationQuotientMap n) =
      ((P.tensorBaseChangeComplexMap A).f (-2)).hom
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap B (A ⊗[R] B))).unit.app _
          ((lichtenbaumSchlessingerComplex P).relationIso.inv.hom ((1 : B) ⊗ₜ[P.Ring] n))) := by
  rw [tensorBaseChangeComplexMap_f_one_tmul, LichtenbaumSchlessingerHom.complexMap_f,
    LichtenbaumSchlessingerHom.complexMapComponent_negTwo]
  have h := LichtenbaumSchlessingerHom.complexMapTwo_apply (P.tensorBaseChangeHom A)
    ((lichtenbaumSchlessingerComplex P).relationIso.inv.hom ((1 : B) ⊗ₜ[P.Ring] n))
  rw [Iso.inv_hom_id_apply, LichtenbaumSchlessingerHom.relationTensorMap_tmul, map_one] at h
  rw [relationOneTmul, ← h]
  exact Iso.hom_inv_id_apply _ _

/-- `P_A · (Rel/TrivRel)` is stable under multiplication by elements of `A ⊗_R B`. -/
theorem smul_mem_relationQuotientImage (c : A ⊗[R] B)
    (w : relationQuotient (P.tensorBaseChange A)) (hw : w ∈ P.relationQuotientImage A) :
    letI := (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationModule
    c • w ∈ P.relationQuotientImage A := by
  let := (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationModule
  obtain ⟨q, rfl⟩ := (P.tensorBaseChange A).algebraMap_surjective c
  rw [(lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).algebraMap_smul_relation]
  exact Submodule.smul_mem _ q hw

/-- The degree `-2` term of `L_A`, read as `Rel_A/TrivRel_A`. -/
def relationRead (v : (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex.X (-2)) :
    relationQuotient (P.tensorBaseChange A) :=
  letI := (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationModule
  (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationBaseChangeEquiv
    ((lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationIso.hom.hom v)

/-- `relationRead` is a left inverse of `relationOneTmul`. -/
theorem relationRead_relationOneTmul (n : relationQuotient (P.tensorBaseChange A)) :
    P.relationRead A (P.relationOneTmul A n) = n := by
  rw [relationRead, relationOneTmul, Iso.inv_hom_id_apply]
  exact (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationBaseChangeEquiv_tmul n

/-- `relationRead` is `A ⊗_R B`-linear. -/
theorem relationRead_smul (c : A ⊗[R] B)
    (v : (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex.X (-2)) :
    letI := (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationModule
    P.relationRead A (c • v) = c • P.relationRead A v := by
  let := (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationModule
  rw [relationRead, relationRead, map_smul, map_smul]

/-- Every element of the image of the degree `-2` component, read in `Rel_A/TrivRel_A`, lies in
`P_A · (Rel/TrivRel)`. -/
theorem relationRead_tensorBaseChangeComplexMap_mem
    (x : (ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).obj
      ((lichtenbaumSchlessingerComplex P).complex.X (-2))) :
    P.relationRead A (((P.tensorBaseChangeComplexMap A).f (-2)).hom x) ∈
      P.relationQuotientImage A := by
  let := (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationModule
  have key : ∀ z : (lichtenbaumSchlessingerComplex P).complex.X (-2),
      P.relationRead A (((P.tensorBaseChangeHom A).complexMap.f (-2)).hom z) ∈
        P.relationQuotientImage A := by
    intro z
    rw [LichtenbaumSchlessingerHom.complexMap_f,
      LichtenbaumSchlessingerHom.complexMapComponent_negTwo]
    show (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationBaseChangeEquiv
      ((lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationIso.hom
        ((P.tensorBaseChangeHom A).complexMapTwo z)) ∈ _
    rw [LichtenbaumSchlessingerHom.complexMapTwo_apply]
    generalize (lichtenbaumSchlessingerComplex P).relationIso.hom z = w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | tmul b n =>
      rw [LichtenbaumSchlessingerHom.relationTensorMap_tmul,
        show algebraMap B (A ⊗[R] B) b ⊗ₜ[(P.tensorBaseChange A).Ring]
            (P.tensorBaseChangeHom A).relationQuotientMap n =
          algebraMap B (A ⊗[R] B) b • ((1 : A ⊗[R] B) ⊗ₜ[(P.tensorBaseChange A).Ring]
            (P.tensorBaseChangeHom A).relationQuotientMap n) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul,
        (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationBaseChangeEquiv_tmul]
      exact P.smul_mem_relationQuotientImage A _ _ (Submodule.subset_span ⟨n, rfl⟩)
    | add w w' hw hw' => rw [map_add, map_add]; exact add_mem hw hw'
  let E := (ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).obj
    ((lichtenbaumSchlessingerComplex P).complex.X (-2))
  let Θ : E →+ relationQuotient (P.tensorBaseChange A) :=
    { toFun := fun v => P.relationRead A (((P.tensorBaseChangeComplexMap A).f (-2)).hom v)
      map_zero' := by
        rw [map_zero, relationRead, map_zero, map_zero]
      map_add' := fun v v' => by
        rw [map_add, relationRead, relationRead, relationRead, map_add, map_add] }
  suffices hΘ : ∀ v : E, v ∈ (P.relationQuotientImage A).toAddSubgroup.comap Θ from hΘ x
  intro v
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add v v' hv hv' => exact add_mem hv hv'
  | tmul c z =>
    have e : (c ⊗ₜ[B] z : E) = (show A ⊗[R] B from c) •
        (show E from (ModuleCat.extendRestrictScalarsAdj (algebraMap B (A ⊗[R] B))).unit.app _ z) :=
      ((ModuleCat.ExtendScalars.smul_tmul (algebraMap B (A ⊗[R] B)) (show A ⊗[R] B from c) 1
        (M := (lichtenbaumSchlessingerComplex P).complex.X (-2)) z).trans
          (by rw [mul_one]; rfl)).symm
    have h1 : Θ (c ⊗ₜ[B] z) = (show A ⊗[R] B from c) •
        P.relationRead A (((P.tensorBaseChangeHom A).complexMap.f (-2)).hom z) :=
      (congrArg Θ e).trans ((congrArg (P.relationRead A)
        ((LinearMap.map_smul ((P.tensorBaseChangeComplexMap A).f (-2)).hom _ _).trans
          (congrArg _ (P.tensorBaseChangeComplexMap_f_one_tmul A (-2) z)))).trans
        (P.relationRead_smul A _ _))
    show Θ (c ⊗ₜ[B] z) ∈ P.relationQuotientImage A
    rw [h1]
    exact P.smul_mem_relationQuotientImage A _ _ (key z)

/-- **The image of the degree `-2` component** is `P_A · (Rel/TrivRel)`. -/
theorem relationOneTmul_mem_range_iff (n : relationQuotient (P.tensorBaseChange A)) :
    P.relationOneTmul A n ∈ LinearMap.range ((P.tensorBaseChangeComplexMap A).f (-2)).hom ↔
      n ∈ P.relationQuotientImage A := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← P.relationRead_relationOneTmul A n, ← hx]
    exact P.relationRead_tensorBaseChangeComplexMap_mem A x
  · intro hn
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨n₀, rfl⟩ := hn
      exact ⟨_, (P.relationOneTmul_relationQuotientMap A n₀).symm⟩
    | zero =>
      rw [relationOneTmul, TensorProduct.tmul_zero, map_zero]
      exact zero_mem _
    | add n n' _ _ hn hn' => rw [relationOneTmul_add]; exact add_mem hn hn'
    | smul q n _ hn => rw [relationOneTmul_smul]; exact Submodule.smul_mem _ _ hn

end Cokernel

/-! ### The two quotients of `Rel_A` -/

section Quotients

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type u} [CommRing B] [Algebra R B] {X T : Type u} (P : Presentation R B X T)

/-- The trivial relations of `P_A` lie in the span of the image of the relations of `P`. -/
theorem trivialRelations_le_span :
    trivialRelations (P.tensorBaseChange A) ≤
      Submodule.span _ (Set.range (P.tensorBaseChangeHom A).relationsMap) := by
  rw [trivialRelations, Submodule.span_le]
  rintro _ ⟨⟨s', t'⟩, rfl⟩
  rcases s' with s | e
  · rcases t' with t | e
    · exact Submodule.subset_span ⟨trivialRelationInRelations P s t,
        LichtenbaumSchlessingerHom.relationsMap_trivialRelationInRelations _ s t⟩
    · exact e.elim
  · exact e.elim

/-- **The class of a relation of `P_A` lies in `P_A · (Rel/TrivRel)` exactly when the relation
lies in `P_A · Rel`.** -/
theorem mk_mem_relationQuotientImage_iff (r : relations (P.tensorBaseChange A)) :
    Submodule.Quotient.mk r ∈ P.relationQuotientImage A ↔
      (r : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) ∈ P.relationsImage A := by
  let S := Submodule.span (P.tensorBaseChange A).Ring
    (Set.range (P.tensorBaseChangeHom A).relationsMap)
  have hr : Set.range (P.tensorBaseChangeHom A).relationQuotientMap =
      Set.range ((trivialRelations (P.tensorBaseChange A)).mkQ ∘
        (P.tensorBaseChangeHom A).relationsMap) := by
    ext n
    constructor
    · rintro ⟨n₀, rfl⟩
      obtain ⟨r₀, rfl⟩ := Submodule.mkQ_surjective _ n₀
      exact ⟨r₀, rfl⟩
    · rintro ⟨r₀, rfl⟩
      exact ⟨Submodule.Quotient.mk r₀, rfl⟩
  have hW : P.relationQuotientImage A = S.map (trivialRelations (P.tensorBaseChange A)).mkQ := by
    rw [Submodule.map_span, ← Set.range_comp, ← hr]
  have hS : S.map (relations (P.tensorBaseChange A)).subtype = P.relationsImage A := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hW, ← Submodule.mkQ_apply, ← Submodule.mem_comap, Submodule.comap_map_mkQ,
    sup_eq_right.2 (P.trivialRelations_le_span A), ← hS]
  refine ⟨fun h => ⟨r, h, rfl⟩, ?_⟩
  rintro ⟨r', h, hr'⟩
  rwa [Subtype.ext hr'] at h

/-- The cokernel of `(A ⊗_R B) ⊗_B L ⟶ L_A` in degree `-2`. -/
abbrev cokernelNegTwo : ModuleCat.{u} (A ⊗[R] B) :=
  cokernel ((P.tensorBaseChangeComplexMap A).f (-2))

/-- The map `Rel_A → Coker((A ⊗_R B) ⊗_B L ⟶ L_A)` in degree `-2`. -/
def relationsToCokernel : relations (P.tensorBaseChange A) →+ P.cokernelNegTwo A where
  toFun r := (cokernel.π ((P.tensorBaseChangeComplexMap A).f (-2))).hom
    (P.relationOneTmul A (Submodule.Quotient.mk r))
  map_zero' := by
    rw [Submodule.Quotient.mk_zero, relationOneTmul, TensorProduct.tmul_zero, map_zero, map_zero]
  map_add' r r' := by
    rw [Submodule.Quotient.mk_add, relationOneTmul_add, map_add]

/-- `relationsToCokernel` is linear along `P_A → A ⊗_R B`. -/
theorem relationsToCokernel_smul (q : (P.tensorBaseChange A).Ring)
    (r : relations (P.tensorBaseChange A)) :
    P.relationsToCokernel A (q • r) = algebraMap _ (A ⊗[R] B) q • P.relationsToCokernel A r := by
  show (cokernel.π ((P.tensorBaseChangeComplexMap A).f (-2))).hom
      (P.relationOneTmul A (Submodule.Quotient.mk (q • r))) = _
  rw [Submodule.Quotient.mk_smul, relationOneTmul_smul, map_smul]
  rfl

/-- The kernel of `Rel_A → Coker` is `P_A · Rel`. -/
theorem relationsToCokernel_eq_zero_iff (r : relations (P.tensorBaseChange A)) :
    P.relationsToCokernel A r = 0 ↔
      (r : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) ∈ P.relationsImage A := by
  rw [← P.mk_mem_relationQuotientImage_iff A, ← P.relationOneTmul_mem_range_iff A]
  let f := (P.tensorBaseChangeComplexMap A).f (-2)
  have h := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom f
  show (cokernel.π f).hom _ = 0 ↔ _
  have key := congrArg (fun φ => φ.hom (P.relationOneTmul A (Submodule.Quotient.mk r))) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Submodule.mkQ_apply] at key
  constructor
  · intro h0
    rw [h0, map_zero] at key
    exact (Submodule.Quotient.mk_eq_zero _).1 key.symm
  · intro hmem
    rw [(Submodule.Quotient.mk_eq_zero _).2 hmem] at key
    exact (ConcreteCategory.injective_of_mono_of_preservesPullback
      (ModuleCat.cokernelIsoRangeQuotient f).hom) (key.trans (map_zero _).symm)

/-- The map `Rel_A → Coker` is onto. -/
theorem relationsToCokernel_surjective : Function.Surjective (P.relationsToCokernel A) := by
  intro k
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (cokernel.π ((P.tensorBaseChangeComplexMap A).f (-2)))) k
  have hw : ∀ w : (A ⊗[R] B) ⊗[(P.tensorBaseChange A).Ring]
      relationQuotient (P.tensorBaseChange A),
      ∃ n, w = (1 : A ⊗[R] B) ⊗ₜ[(P.tensorBaseChange A).Ring] n := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    | tmul c n =>
      obtain ⟨q, rfl⟩ := (P.tensorBaseChange A).algebraMap_surjective c
      refine ⟨q • n, ?_⟩
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    | add w w' hw hw' =>
      obtain ⟨n, rfl⟩ := hw
      obtain ⟨n', rfl⟩ := hw'
      exact ⟨n + n', (TensorProduct.tmul_add _ _ _).symm⟩
  obtain ⟨n, hn⟩ :=
    hw ((lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationIso.hom.hom v)
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ n
  refine ⟨r, ?_⟩
  show (cokernel.π ((P.tensorBaseChangeComplexMap A).f (-2))).hom
    ((lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).relationIso.inv.hom
      ((1 : A ⊗[R] B) ⊗ₜ[(P.tensorBaseChange A).Ring] Submodule.Quotient.mk r)) = _
  rw [Submodule.mkQ_apply] at hn
  rw [← hn, Iso.hom_inv_id_apply]

end Quotients

/-! ### The map `Rel_A → Tor_1^R(A, B)` -/

section TorMap

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type u} [CommRing B] [Algebra R B] {X T : Type u} (P : Presentation R B X T)

/-- The map `Rel_A → Tor_1^R(A, B)`: `μ` followed by the identification of
`Ker(A ⊗_R I → A ⊗_R P)` with `Tor_1^R(A, B)`. -/
def relationsToTor : relations (P.tensorBaseChange A) →+ TorChangeOfRings.torObj R 1 A B where
  toFun r := (torOnePresentationKerEquiv A P).symm
    ⟨P.mu A r, (P.mem_relations_iff_mu A r).1 r.2⟩
  map_zero' := by
    rw [AddEquiv.symm_apply_eq, map_zero]
    exact Subtype.ext (map_zero _)
  map_add' r r' := by
    rw [AddEquiv.symm_apply_eq, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact Subtype.ext (map_add _ _ _)

/-- The image of `relationsToTor r` in `Ker(A ⊗_R I → A ⊗_R P)` is `μ r`. -/
theorem torOnePresentationKerEquiv_relationsToTor (r : relations (P.tensorBaseChange A)) :
    (torOnePresentationKerEquiv A P (P.relationsToTor A r)).1 = P.mu A r := by
  show (torOnePresentationKerEquiv A P ((torOnePresentationKerEquiv A P).symm _)).1 = _
  rw [AddEquiv.apply_symm_apply]

/-- The kernel of `Rel_A → Tor_1^R(A, B)` is `P_A · Rel`. -/
theorem relationsToTor_eq_zero_iff (r : relations (P.tensorBaseChange A)) :
    P.relationsToTor A r = 0 ↔
      (r : (T ⊕ PEmpty.{u + 1}) →₀ (P.tensorBaseChange A).Ring) ∈ P.relationsImage A := by
  rw [← P.mu_eq_zero_iff A]
  constructor
  · intro h
    have := P.torOnePresentationKerEquiv_relationsToTor A r
    rw [h, map_zero] at this
    exact this.symm
  · intro h
    apply (torOnePresentationKerEquiv A P).injective
    rw [map_zero]
    exact Subtype.ext ((P.torOnePresentationKerEquiv_relationsToTor A r).trans h)

/-- The map `Rel_A → Tor_1^R(A, B)` is onto. -/
theorem relationsToTor_surjective : Function.Surjective (P.relationsToTor A) := by
  intro y
  obtain ⟨x, hx⟩ := P.mu_surjective A (torOnePresentationKerEquiv A P y).1
  have hrel : x ∈ relations (P.tensorBaseChange A) := by
    rw [P.mem_relations_iff_mu A, hx]
    exact (torOnePresentationKerEquiv A P y).2
  exact ⟨⟨x, hrel⟩, (torOnePresentationKerEquiv A P).injective
    (Subtype.ext ((P.torOnePresentationKerEquiv_relationsToTor A _).trans hx))⟩

/-- `relationsToTor` intertwines multiplication by a constant `a ∈ A` on `Rel_A` with the action
of multiplication by `a` on `Tor_1^R(A, B)` in the first variable. -/
theorem relationsToTor_C_smul (a : A) (r : relations (P.tensorBaseChange A)) :
    P.relationsToTor A ((MvPolynomial.C a : (P.tensorBaseChange A).Ring) • r) =
      ((Tor (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).app (ModuleCat.of R B)
          (P.relationsToTor A r) := by
  apply (torOnePresentationKerEquiv A P).injective
  apply Subtype.ext
  rw [torOnePresentationKerEquiv_smul, torOnePresentationKerEquiv_relationsToTor,
    torOnePresentationKerEquiv_relationsToTor, Submodule.coe_smul, ← MvPolynomial.algebraMap_eq,
    IsScalarTower.algebraMap_smul, map_smul]

/-- `relationsToTor` intertwines multiplication by a variable `X_i` on `Rel_A` with the action of
multiplication by its image in `B` on `Tor_1^R(A, B)` in the second variable. -/
theorem relationsToTor_X_smul (i : X) (r : relations (P.tensorBaseChange A)) :
    P.relationsToTor A ((MvPolynomial.X i : (P.tensorBaseChange A).Ring) • r) =
      (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B (P.val i)))) (P.relationsToTor A r) := by
  have hval : P.val i = algebraMap P.Ring B (MvPolynomial.X i) := by
    rw [P.algebraMap_apply, MvPolynomial.aeval_X]
  apply (torOnePresentationKerEquiv A P).injective
  apply Subtype.ext
  rw [hval, torOnePresentationKerEquiv_mul, torOnePresentationKerEquiv_relationsToTor,
    torOnePresentationKerEquiv_relationsToTor, Submodule.coe_smul, mu_X_smul]

end TorMap

end Algebra.Presentation

namespace CommAlgCat

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B]

/-- **`Tor_1^R(A, B)` as an `A ⊗_R B`-module**, with its canonical structure: `a ⊗ b` acts as
functoriality of `Tor` along multiplication by `a` in the first variable and by `b` in the
second (`TorChangeOfRings.System.IsCanonical.action_tmul`). -/
def torOneTensorProductModule : ModuleCat.{u} (A ⊗[R] B) :=
  letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  ModuleCat.of (A ⊗[R] B) (TorChangeOfRings.torObj R 1 A B)

/-- Multiplication by `1` is the identity. -/
private theorem ofHom_mulLinear_one (R M : Type u) [CommRing R] [CommRing M] [Algebra R M] :
    ModuleCat.ofHom (TorChangeOfRings.mulLinear R M 1) = 𝟙 (ModuleCat.of R M) := by
  ext z
  exact one_mul z

/-- `a ⊗ 1` acts on `Tor_1^R(A, B)` by functoriality along multiplication by `a` on `A`. -/
theorem torOneTensorProductModule_tmul_one_smul (a : A) (y : torOneTensorProductModule R A B) :
    ((a ⊗ₜ[R] (1 : B) : A ⊗[R] B) • y) =
      ((Tor (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R A a))).app (ModuleCat.of R B) y := by
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  refine ((TorChangeOfRings.canonicalLaws TorChangeOfRings.canonicalSystem_nonempty).action_tmul
    R A B 1 a 1 (y : TorChangeOfRings.torObj R 1 A B)).trans ?_
  rw [ofHom_mulLinear_one, CategoryTheory.Functor.map_id, Category.comp_id]

/-- `1 ⊗ b` acts on `Tor_1^R(A, B)` by functoriality along multiplication by `b` on `B`. -/
theorem torOneTensorProductModule_one_tmul_smul (b : B) (y : torOneTensorProductModule R A B) :
    (((1 : A) ⊗ₜ[R] b : A ⊗[R] B) • y) =
      (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).map
        (ModuleCat.ofHom (TorChangeOfRings.mulLinear R B b))) y := by
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  refine ((TorChangeOfRings.canonicalLaws TorChangeOfRings.canonicalSystem_nonempty).action_tmul
    R A B 1 1 b (y : TorChangeOfRings.torObj R 1 A B)).trans ?_
  rw [ofHom_mulLinear_one, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

end CommAlgCat

namespace Algebra.Presentation

open RingTheory.TorIndependence

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

section Final

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B : Type u} [CommRing B] [Algebra R B] {X T : Type u} (P : Presentation R B X T)

/-- `relationsToTor` is linear along `P_A → A ⊗_R B`, for the canonical `A ⊗_R B`-module
structure on `Tor_1^R(A, B)`. -/
theorem relationsToTor_smul (q : (P.tensorBaseChange A).Ring) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
    ∀ r : relations (P.tensorBaseChange A),
      P.relationsToTor A (q • r) = algebraMap _ (A ⊗[R] B) q • P.relationsToTor A r := by
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  induction q using MvPolynomial.induction_on with
  | C a =>
    intro r
    have h : algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B) (MvPolynomial.C a) =
        a ⊗ₜ[R] (1 : B) := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      rfl
    rw [h]
    exact (P.relationsToTor_C_smul A a r).trans
      (CommAlgCat.torOneTensorProductModule_tmul_one_smul R A B a (P.relationsToTor A r)).symm
  | add p q hp hq =>
    intro r
    rw [add_smul, map_add, hp, hq, map_add, add_smul]
  | mul_X p i hp =>
    intro r
    have h : algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B) (MvPolynomial.X i) =
        (1 : A) ⊗ₜ[R] P.val i := by
      rw [(P.tensorBaseChange A).algebraMap_apply, MvPolynomial.aeval_X, tensorBaseChange_val]
    calc P.relationsToTor A ((p * MvPolynomial.X i) • r)
        = P.relationsToTor A (p • ((MvPolynomial.X i : (P.tensorBaseChange A).Ring) • r)) := by
          rw [mul_smul]
      _ = algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B) p • P.relationsToTor A
            ((MvPolynomial.X i : (P.tensorBaseChange A).Ring) • r) := hp _
      _ = algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B) p •
            (((1 : A) ⊗ₜ[R] P.val i : A ⊗[R] B) • P.relationsToTor A r) :=
          congrArg _ ((P.relationsToTor_X_smul A i r).trans
            (CommAlgCat.torOneTensorProductModule_one_tmul_smul R A B (P.val i)
              (P.relationsToTor A r)).symm)
      _ = algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B) (p * MvPolynomial.X i) •
            P.relationsToTor A r := by
          rw [map_mul, h, mul_smul]

/-- **The cokernel in degree `-2` of `(A ⊗_R B) ⊗_B L ⟶ L_A` is `Tor_1^R(A, B)`**, as an
`A ⊗_R B`-linear map onto `Tor_1^R(A, B)` with its canonical module structure. Both are quotients
of `Rel_A` by `P_A · Rel`: the cokernel by `Algebra.Presentation.relationsToCokernel_eq_zero_iff`,
and `Tor_1^R(A, B)` by `Algebra.Presentation.relationsToTor_eq_zero_iff`. -/
def cokernelNegTwoLinearEquiv :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
    P.cokernelNegTwo A ≃ₗ[A ⊗[R] B] TorChangeOfRings.torObj R 1 A B :=
  letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  letI mC : Module (P.tensorBaseChange A).Ring (P.cokernelNegTwo A) :=
    Module.compHom _ (algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B))
  letI mT : Module (P.tensorBaseChange A).Ring (TorChangeOfRings.torObj R 1 A B) :=
    Module.compHom _ (algebraMap (P.tensorBaseChange A).Ring (A ⊗[R] B))
  let π : relations (P.tensorBaseChange A) →ₗ[(P.tensorBaseChange A).Ring] P.cokernelNegTwo A :=
    { toFun := P.relationsToCokernel A
      map_add' := map_add _
      map_smul' := P.relationsToCokernel_smul A }
  let Ξ : relations (P.tensorBaseChange A) →ₗ[(P.tensorBaseChange A).Ring]
      TorChangeOfRings.torObj R 1 A B :=
    { toFun := P.relationsToTor A
      map_add' := map_add _
      map_smul' := fun q r => P.relationsToTor_smul A q r }
  have hker : LinearMap.ker π = LinearMap.ker Ξ := by
    ext r
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    exact (P.relationsToCokernel_eq_zero_iff A r).trans (P.relationsToTor_eq_zero_iff A r).symm
  let eQ : P.cokernelNegTwo A ≃ₗ[(P.tensorBaseChange A).Ring] TorChangeOfRings.torObj R 1 A B :=
    (π.quotKerEquivOfSurjective (P.relationsToCokernel_surjective A)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
        Ξ.quotKerEquivOfSurjective (P.relationsToTor_surjective A)
  { eQ.toAddEquiv with
    map_smul' := fun c x => by
      obtain ⟨q, rfl⟩ := (P.tensorBaseChange A).algebraMap_surjective c
      exact eQ.map_smul q x }

/-- **The cokernel in degree `-2` of `(A ⊗_R B) ⊗_B L ⟶ L_A` is `Tor_1^R(A, B)`**, as an
isomorphism of `A ⊗_R B`-modules. -/
def cokernelNegTwoIsoTorOne :
    P.cokernelNegTwo A ≅ CommAlgCat.torOneTensorProductModule R A B :=
  letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  { hom := ConcreteCategory.ofHom (C := ModuleCat (A ⊗[R] B)) (X := P.cokernelNegTwo A)
      (Y := CommAlgCat.torOneTensorProductModule R A B) (P.cokernelNegTwoLinearEquiv A).toLinearMap
    inv := ConcreteCategory.ofHom (C := ModuleCat (A ⊗[R] B))
      (X := CommAlgCat.torOneTensorProductModule R A B) (Y := P.cokernelNegTwo A)
      (P.cokernelNegTwoLinearEquiv A).symm.toLinearMap
    hom_inv_id := by
      ext x
      exact (P.cokernelNegTwoLinearEquiv A).symm_apply_apply x
    inv_hom_id := by
      ext x
      exact (P.cokernelNegTwoLinearEquiv A).apply_symm_apply x }

end Final

end Algebra.Presentation
