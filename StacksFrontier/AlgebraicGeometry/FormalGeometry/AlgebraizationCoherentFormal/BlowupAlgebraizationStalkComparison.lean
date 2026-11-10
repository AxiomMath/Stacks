module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationDepthComparison
public import StacksFrontier.RingTheory.AdicCompletion.ModuleEquivOfQuotientEquiv

/-!
# The completed stalk of the pullback to the blowup, in the proof of Stacks 0EJK

In Situation [Stacks, Tag 0EHC] let `b : X' ⟶ X = Spec(A)` be the blowup of `I`, `U' = b⁻¹(U)`,
`(ℱₙ)` an object of `Coh(U, I𝒪_U)`, `y'` a point of `U'` and `y = b(y')`. The proof of
[Stacks, Tag 0EJK] uses, with "details omitted", that the completed stalk at `y'` of the pullback
`(b|_{U'}^*ℱₙ)` is the base change `𝒪_{X',y'}^∧ ⊗_{𝒪_{X,y}^∧} ℱ_y^∧` of the completed stalk at `y`.
This file supplies those details and draws the consequence: the inequalities (0EJL) and (0EJM)
of the source hold at every point of the exceptional divisor.

The argument is level by level. By [Stacks, Tag 0098] the stalk of `b^*ℱₙ` at `y'` is
`𝒪_{U',y'} ⊗_{𝒪_{U,y}} ℱ_{n,y}`, naturally in `n`; the stalk `ℱ_{n,y}` is the level-`n` reduction
`M / J^{n+1} M` of `M = ℱ_y^∧`, `J` the stalk of `I𝒪_U`; and for any module `M` over the
`J`-adic completion `Ô` of a ring `O` and any `O`-algebra `O'`, the `k`-th infinitesimal
neighbourhood of `Ô' ⊗_Ô M` for the `JO'`-adic topology is `O' ⊗_O (M / J^k M)`
(`Stacks.Algebraization.tensorQuotientEquivCompletedTensorQuotient`). The completed stalk of the
pullback and the finite, hence complete, `Ô'`-module `Ô' ⊗_Ô M` therefore have the same
infinitesimal neighbourhoods, compatibly, and are identified. A chart of the blowup through `y'`
then identifies the completed local rings with `(A_𝔮)^∧` and `(A[I/a]_Q)^∧`.

## Main definitions

* `Stacks.Algebraization.tensorQuotientEquivCompletedTensorQuotient` — the levels of a completed
  base change: `O' ⊗_O (M / J^k M) ≅ (Ô' ⊗_Ô M) / J'^k`.
* `Stacks.Algebraization.blowupPullbackFormalStalkQuotientEquiv` — the levels of the completed
  stalk of the pullback to the blowup.

## Main results

* `Stacks.Algebraization.exists_adicCompletion_addEquiv_of_quotientEquiv` — an adic completion
  identified with a complete module over the completed ring, level by level.
* `Stacks.Algebraization.BlowupChartPoint.completedStalkComparison` — the completed stalk of
  `(b|_{U'}^*ℱₙ)` at `y'` is `(A[I/a]_Q)^∧ ⊗_{(A_𝔮)^∧} ℱ_y^∧`, for every chart through `y'`.
* `Stacks.Algebraization.exists_depthAddDimAddDistance_le_blowup` — (0EJL) and (0EJM) at every
  point of `U'` on the exceptional divisor.

## Implementation notes

The ideal of `𝒪_{U',y'}` defining the completion is the stalk of `I𝒪_{U'}`, which is the extension
of the stalk of `I𝒪_U` only up to equality; the level computation is therefore stated for an
ideal `J'` of `O'` with `JO' = J'` and an algebra structure `Ô → Ô'` equal to the map of
completions, rather than for `JO'` itself.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace Stacks.Algebraization

/-- If `s ∈ R^∧` reduces to `o` modulo `I ^ n`, then `s • t - o • t ∈ I ^ n T`. -/
private theorem smul_sub_smul_mem_pow_smul_top {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    {T : Type*} [AddCommGroup T] [Module R T] [Module (AdicCompletion I R) T]
    [IsScalarTower R (AdicCompletion I R) T] (n : ℕ) (s : AdicCompletion I R) (o : R)
    (ho : AdicCompletion.evalₐ I n s = Ideal.Quotient.mk (I ^ n) o) (t : T) :
    s • t - o • t ∈ (I ^ n • ⊤ : Submodule R T) := by
  have hker : s - algebraMap R (AdicCompletion I R) o ∈
      RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, ho,
      show algebraMap R (AdicCompletion I R) o = AdicCompletion.of I R o from rfl,
      AdicCompletion.evalₐ_of, sub_self]
  rw [AdicCompletion.ker_evalₐ I hI, ← Ideal.map_pow] at hker
  have h := Submodule.smul_mem_smul hker (Submodule.mem_top (x := t))
  rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top, sub_smul, algebraMap_smul] at h
  exact h

section LevelBaseChange

variable {O : Type*} [CommRing O] (O' : Type*) [CommRing O'] [Algebra O O'] (J : Ideal O)
  (J' : Ideal O') [Algebra (AdicCompletion J O) (AdicCompletion J' O')]
  (hJ' : J.map (algebraMap O O') = J')

local notation "Ô" => AdicCompletion J O
local notation "Ô'" => AdicCompletion J' O'

variable {J'} in
/-- The two maps `O → Ô'` agree, when `Ô → Ô'` is the map of completions. -/
theorem algebraMap_algebraMap_of_eq_adicCompletionMap
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s) (o : O) :
    algebraMap Ô Ô' (algebraMap O Ô o) = algebraMap O Ô' o := by
  rw [hψ]
  refine (RingHom.congr_fun (adicCompletionMap_comp_algebraMap (algebraMap O O') J J'
    hJ'.le) o).trans ?_
  exact (IsScalarTower.algebraMap_apply O O' _ o).symm

variable (M : Type*) [AddCommGroup M] [Module (AdicCompletion J O) M] [Module O M]
  [IsScalarTower O (AdicCompletion J O) M]

omit [Algebra (AdicCompletion J O) (AdicCompletion J' O')] [Module (AdicCompletion J O) M]
  [IsScalarTower O (AdicCompletion J O) M] in
include hJ' in
/-- `(JO')^k` kills `O' ⊗_O (M / J^k M)`. -/
theorem isTorsionBySet_tensor_quotient_pow (k : ℕ) :
    Module.IsTorsionBySet O' (O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M))) ((J' ^ k : Ideal O') :
      Set O') := by
  intro x a
  have hle : J' ^ k ≤ Module.annihilator O' (O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M))) := by
    rw [← hJ', ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro y
    rw [algebraMap_smul]
    induction y using TensorProduct.inductionOn with
    | tmul b q =>
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul,
        (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hj Submodule.mem_top),
        TensorProduct.tmul_zero]
    | add y z hy hz => rw [smul_add, hy, hz, add_zero]
  exact (Module.mem_annihilator.mp (hle a.2)) x

variable {J'} in
/-- The map `M → Ô' ⊗_Ô M`, `m ↦ 1 ⊗ m`, as an `O`-linear map. -/
def oneTmulLinearMap
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s) :
    M →ₗ[O] Ô' ⊗[Ô] M where
  toFun m := 1 ⊗ₜ m
  map_add' _ _ := TensorProduct.tmul_add _ _ _
  map_smul' o m := by
    rw [RingHom.id_apply, TensorProduct.smul_tmul', ← algebraMap_smul Ô o m,
      ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one,
      algebraMap_algebraMap_of_eq_adicCompletionMap O' J hJ' hψ]

variable {J'} in
/-- The `O'`-linear map `O' ⊗_O (M / J^k M) → (Ô' ⊗_Ô M) / J'^k`, `a ⊗ m ↦ a ⊗ m`. -/
def tensorQuotientToCompletedTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s) (k : ℕ) :
    O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M)) →ₗ[O']
      (Ô' ⊗[Ô] M) ⧸ (J' ^ k • ⊤ : Submodule O' (Ô' ⊗[Ô] M)) :=
  LinearMap.liftBaseChange O'
    ((J ^ k • ⊤ : Submodule O M).liftQ
      (((J' ^ k • ⊤ : Submodule O' (Ô' ⊗[Ô] M)).mkQ.restrictScalars O).comp
        (oneTmulLinearMap O' J hJ' M hψ))
      (by
        rw [Submodule.smul_le]
        intro j hj m _
        rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, LinearMap.restrictScalars_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul O' j]
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [← hJ', ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hj))

variable {J'} in
/-- `tensorQuotientToCompletedTensorQuotient` sends `a ⊗ [m]` to the class of `a • 1 ⊗ m`. -/
theorem tensorQuotientToCompletedTensorQuotient_tmul
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s) (k : ℕ)
    (a : O') (m : M) :
    tensorQuotientToCompletedTensorQuotient O' J hJ' M hψ k (a ⊗ₜ Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (a • (1 : Ô') ⊗ₜ[Ô] m) := by
  rw [tensorQuotientToCompletedTensorQuotient, LinearMap.liftBaseChange_tmul]
  rfl

variable {J'} in
/-- `O' ⊗_O (M / J^k M)` as a module over `O' / J'^k`. -/
abbrev tensorQuotientModule (k : ℕ) :
    Module (O' ⧸ J' ^ k) (O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M))) :=
  (isTorsionBySet_tensor_quotient_pow O' J J' hJ' M k).module

/-- The image of `s ∈ Ô` in `M / J^k M` acts through any lift of its reduction modulo `J^k`. -/
theorem smul_mk_eq_of_evalₐ (hJ : J.FG) (k : ℕ) (s : Ô) (o : O)
    (ho : AdicCompletion.evalₐ J k s = Ideal.Quotient.mk (J ^ k) o) (m : M) :
    (Submodule.Quotient.mk (s • m) : M ⧸ (J ^ k • ⊤ : Submodule O M)) =
      Submodule.Quotient.mk (o • m) := by
  rw [Submodule.Quotient.eq]
  exact smul_sub_smul_mem_pow_smul_top J hJ k s o ho m

variable {J'} in
/-- The additive map `Ô' ⊗_Ô M → O' ⊗_O (M / J^k M)`, `r ⊗ m ↦ r ⊗ m`, `Ô'` acting on the target
through its reduction modulo `J'^k`. -/
def completedTensorToTensorQuotientAddHom
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) :
    Ô' ⊗[Ô] M →+ O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M)) :=
  letI := tensorQuotientModule O' J hJ' M k
  TensorProduct.liftAddHom
    { toFun := fun r =>
        { toFun := fun m => AdicCompletion.evalₐ J' k r •
            ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M)))
          map_zero' := by rw [Submodule.Quotient.mk_zero, TensorProduct.tmul_zero, smul_zero]
          map_add' := fun m m' => by
            rw [Submodule.Quotient.mk_add, TensorProduct.tmul_add, smul_add] }
      map_zero' := by
        ext m
        change AdicCompletion.evalₐ J' k 0 •
          ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M))) = 0
        rw [map_zero, zero_smul]
      map_add' := fun r r' => by
        ext m
        change AdicCompletion.evalₐ J' k (r + r') •
            ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M))) =
          AdicCompletion.evalₐ J' k r •
            ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M))) +
          AdicCompletion.evalₐ J' k r' •
            ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M)))
        rw [map_add, add_smul] }
    (fun s r m => by
      obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J k s)
      change AdicCompletion.evalₐ J' k (s • r) •
          ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M))) =
        AdicCompletion.evalₐ J' k r •
          ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk (s • m) : M ⧸ (J ^ k • ⊤ : Submodule O M)))
      rw [smul_mk_eq_of_evalₐ J M hJ k s o ho.symm m, Algebra.smul_def, map_mul, mul_comm,
        mul_smul, hψ, adicCompletionMap_evalₐ, ← ho, Ideal.quotientMap_mk,
        Module.IsTorsionBySet.mk_smul, Submodule.Quotient.mk_smul, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one])

variable {J'} in
/-- `completedTensorToTensorQuotientAddHom` sends `r ⊗ m` to `r̄ • (1 ⊗ [m])`, where `r̄` is the
reduction of `r` modulo `J'^k`. -/
theorem completedTensorToTensorQuotientAddHom_tmul
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) (r : Ô') (m : M) :
    letI := tensorQuotientModule O' J hJ' M k
    completedTensorToTensorQuotientAddHom O' J hJ' M hψ hJ k (r ⊗ₜ m) =
      AdicCompletion.evalₐ J' k r •
        ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M))) :=
  rfl

variable {J'} in
/-- `completedTensorToTensorQuotientAddHom` is `O'`-linear. -/
def completedTensorToTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) :
    Ô' ⊗[Ô] M →ₗ[O'] O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M)) where
  __ := completedTensorToTensorQuotientAddHom O' J hJ' M hψ hJ k
  map_smul' a t := by
    let := tensorQuotientModule O' J hJ' M k
    simp only [AddMonoidHom.toFun_eq_coe, RingHom.id_apply]
    induction t using TensorProduct.inductionOn with
    | tmul r m =>
      rw [TensorProduct.smul_tmul', completedTensorToTensorQuotientAddHom_tmul,
        completedTensorToTensorQuotientAddHom_tmul, Algebra.smul_def, map_mul, mul_smul,
        show algebraMap O' Ô' a = AdicCompletion.of J' O' a from rfl, AdicCompletion.evalₐ_of,
        Module.IsTorsionBySet.mk_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

variable {J'} in
/-- The `O'`-linear map `(Ô' ⊗_Ô M) / J'^k → O' ⊗_O (M / J^k M)`. -/
def completedTensorQuotientToTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) :
    (Ô' ⊗[Ô] M) ⧸ (J' ^ k • ⊤ : Submodule O' (Ô' ⊗[Ô] M)) →ₗ[O']
      O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M)) :=
  (J' ^ k • ⊤ : Submodule O' (Ô' ⊗[Ô] M)).liftQ
    (completedTensorToTensorQuotient O' J hJ' M hψ hJ k)
    (by
      rw [Submodule.smul_le]
      intro a ha t _
      rw [LinearMap.mem_ker, map_smul]
      exact isTorsionBySet_tensor_quotient_pow O' J J' hJ' M k (a := ⟨a, ha⟩))

variable {J'} in
/-- `tensorQuotientToCompletedTensorQuotient` is a left inverse of
`completedTensorQuotientToTensorQuotient`. -/
theorem tensorQuotientToCompletedTensorQuotient_completedTensorQuotientToTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) (t : Ô' ⊗[Ô] M) :
    tensorQuotientToCompletedTensorQuotient O' J hJ' M hψ k
        (completedTensorQuotientToTensorQuotient O' J hJ' M hψ hJ k (Submodule.Quotient.mk t)) =
      Submodule.Quotient.mk t := by
  let := tensorQuotientModule O' J hJ' M k
  induction t using TensorProduct.inductionOn with
  | tmul r m =>
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J' k r)
    change tensorQuotientToCompletedTensorQuotient O' J hJ' M hψ k
      (AdicCompletion.evalₐ J' k r •
        ((1 : O') ⊗ₜ[O] (Submodule.Quotient.mk m : M ⧸ (J ^ k • ⊤ : Submodule O M)))) = _
    rw [← ho, Module.IsTorsionBySet.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      tensorQuotientToCompletedTensorQuotient_tmul, Submodule.Quotient.eq]
    have h := smul_sub_smul_mem_pow_smul_top J' (hJ' ▸ hJ.map _) k r o ho.symm
      ((1 : Ô') ⊗ₜ[Ô] m)
    rw [← neg_mem_iff, neg_sub]
    rwa [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, map_add, map_add, hx, hy]

variable {J'} in
/-- `completedTensorQuotientToTensorQuotient` is a left inverse of
`tensorQuotientToCompletedTensorQuotient`. -/
theorem completedTensorQuotientToTensorQuotient_tensorQuotientToCompletedTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) (x : O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M))) :
    completedTensorQuotientToTensorQuotient O' J hJ' M hψ hJ k
        (tensorQuotientToCompletedTensorQuotient O' J hJ' M hψ k x) = x := by
  let := tensorQuotientModule O' J hJ' M k
  induction x using TensorProduct.inductionOn with
  | tmul a q =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [tensorQuotientToCompletedTensorQuotient_tmul]
    change completedTensorToTensorQuotientAddHom O' J hJ' M hψ hJ k (a • (1 : Ô') ⊗ₜ[Ô] m) = _
    rw [TensorProduct.smul_tmul', completedTensorToTensorQuotientAddHom_tmul, Algebra.smul_def,
      mul_one, show algebraMap O' Ô' a = AdicCompletion.of J' O' a from rfl,
      AdicCompletion.evalₐ_of, Module.IsTorsionBySet.mk_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {J'} in
/-- **The levels of a completed base change.** Let `J ⊆ O` be finitely generated, `J' = JO'`, and
`M` a module over the `J`-adic completion `Ô` of `O`. The `k`-th infinitesimal neighbourhood of
`Ô' ⊗_Ô M` for the `J'`-adic topology is `O' ⊗_O (M / J^k M)`. -/
def tensorQuotientEquivCompletedTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) :
    O' ⊗[O] (M ⧸ (J ^ k • ⊤ : Submodule O M)) ≃ₗ[O']
      (Ô' ⊗[Ô] M) ⧸ (J' ^ k • ⊤ : Submodule O' (Ô' ⊗[Ô] M)) where
  __ := tensorQuotientToCompletedTensorQuotient O' J hJ' M hψ k
  invFun := completedTensorQuotientToTensorQuotient O' J hJ' M hψ hJ k
  left_inv := completedTensorQuotientToTensorQuotient_tensorQuotientToCompletedTensorQuotient
    O' J hJ' M hψ hJ k
  right_inv y := by
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact tensorQuotientToCompletedTensorQuotient_completedTensorQuotientToTensorQuotient
      O' J hJ' M hψ hJ k t

variable {J'} in
/-- `tensorQuotientEquivCompletedTensorQuotient` sends `a ⊗ [m]` to the class of `a • 1 ⊗ m`. -/
theorem tensorQuotientEquivCompletedTensorQuotient_tmul
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) (k : ℕ) (a : O') (m : M) :
    tensorQuotientEquivCompletedTensorQuotient O' J hJ' M hψ hJ k
        (a ⊗ₜ Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (a • (1 : Ô') ⊗ₜ[Ô] m) :=
  tensorQuotientToCompletedTensorQuotient_tmul O' J hJ' M hψ k a m

variable {J'} in
/-- The levels of `tensorQuotientEquivCompletedTensorQuotient` are compatible with the
transition maps. -/
theorem transitionMap_tensorQuotientEquivCompletedTensorQuotient
    (hψ : ∀ s, algebraMap Ô Ô' s = adicCompletionMap (algebraMap O O') J J' hJ'.le s)
    (hJ : J.FG) {k k' : ℕ} (h : k ≤ k') (x : O' ⊗[O] (M ⧸ (J ^ k' • ⊤ : Submodule O M))) :
    AdicCompletion.transitionMap J' (Ô' ⊗[Ô] M) h
        (tensorQuotientEquivCompletedTensorQuotient O' J hJ' M hψ hJ k' x) =
      tensorQuotientEquivCompletedTensorQuotient O' J hJ' M hψ hJ k
        (LinearMap.baseChange O' (AdicCompletion.transitionMap J M h) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a q =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.baseChange_tmul, tensorQuotientEquivCompletedTensorQuotient_tmul]
    exact (tensorQuotientEquivCompletedTensorQuotient_tmul O' J hJ' M hψ hJ k a m).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end LevelBaseChange

section CompleteOfLevels

variable {R : Type*} [CommRing R] (I : Ideal R) {L T : Type*} [AddCommGroup L] [Module R L]
  [AddCommGroup T] [Module R T] [Module (AdicCompletion I R) T]
  [IsScalarTower R (AdicCompletion I R) T]

/-- For a module `T` over the `I`-adic completion of `R`, `I` finitely generated, the canonical map
`T → T^∧` is linear over the completed ring. -/
theorem adicCompletion_of_smul (hI : I.FG) (r : AdicCompletion I R) (t : T) :
    AdicCompletion.of I T (r • t) = r • AdicCompletion.of I T t := by
  refine AdicCompletion.ext fun n => ?_
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n r)
  rw [AdicCompletion.smul_eval, AdicCompletion.val_smul_eq_evalₐ_smul, ← ho]
  change Submodule.Quotient.mk (r • t) = Ideal.Quotient.mk (I ^ n) o • Submodule.Quotient.mk t
  rw [Module.Quotient.mk_smul_mk, Submodule.Quotient.eq]
  exact smul_sub_smul_mem_pow_smul_top I hI n r o ho.symm t

/-- **An adic completion identified with a complete module level by level.** Let `I ⊆ R` be
finitely generated, `L` an `R`-module and `T` an `I`-adically complete module over the completion
`R^∧`. Compatible `R`-linear identifications `L / I^{n+1} L ≅ T / I^{n+1} T` give an additive
identification of `L^∧` with `T`, linear over `R^∧`. -/
theorem exists_adicCompletion_addEquiv_of_quotientEquiv (hI : I.FG) [IsAdicComplete I T]
    (E : ∀ n : ℕ, (L ⧸ (I ^ (n + 1) • ⊤ : Submodule R L)) ≃ₗ[R]
      (T ⧸ (I ^ (n + 1) • ⊤ : Submodule R T)))
    (hE : ∀ {m n : ℕ} (h : m ≤ n) (x : L ⧸ (I ^ (n + 1) • ⊤ : Submodule R L)),
      AdicCompletion.transitionMap I T (Nat.succ_le_succ h) (E n x) =
        E m (AdicCompletion.transitionMap I L (Nat.succ_le_succ h) x)) :
    ∃ Φ : AdicCompletion I L ≃+ T,
      ∀ (r : AdicCompletion I R) (x : AdicCompletion I L), Φ (r • x) = r • Φ x := by
  have hL : Subsingleton (L ⧸ (I ^ 0 • ⊤ : Submodule R L)) := by
    rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  have hT : Subsingleton (T ⧸ (I ^ 0 • ⊤ : Submodule R T)) := by
    rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  let e : ∀ n : ℕ, (L ⧸ (I ^ n • ⊤ : Submodule R L)) ≃ₗ[R] (T ⧸ (I ^ n • ⊤ : Submodule R T)) :=
    fun n => match n with
    | 0 =>
      { toFun := 0
        invFun := 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        map_smul' := fun _ _ => Subsingleton.elim _ _ }
    | n + 1 => E n
  have he : ∀ {m n : ℕ} (h : m ≤ n) (x : L ⧸ (I ^ n • ⊤ : Submodule R L)),
      AdicCompletion.transitionMap I T h ((e n).toAddEquiv x) =
        (e m).toAddEquiv (AdicCompletion.transitionMap I L h x) := by
    intro m n h x
    cases m with
    | zero => exact Subsingleton.elim _ _
    | succ m =>
      cases n with
      | zero => omega
      | succ n => exact hE (Nat.le_of_succ_le_succ h) x
  have hσ : ∀ (n : ℕ) (r : AdicCompletion I R) (x : L ⧸ (I ^ n • ⊤ : Submodule R L)),
      (e n).toAddEquiv (r.val n • x) = (id r).val n • (e n).toAddEquiv x := by
    intro n r x
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n r)
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [id, AdicCompletion.val_smul_eq_evalₐ_smul, AdicCompletion.val_smul_eq_evalₐ_smul, ← ho,
      Module.Quotient.mk_smul_mk]
    change (e n) (Submodule.Quotient.mk (o • l)) =
      Ideal.Quotient.mk (I ^ n) o • (e n) (Submodule.Quotient.mk l)
    rw [Submodule.Quotient.mk_smul, map_smul]
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ ((e n) (Submodule.Quotient.mk l))
    rw [← ht, Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_smul]
  let Ψ := AdicCompletion.addEquivOfQuotientEquiv I I (fun n => (e n).toAddEquiv) he
  have hΨ := AdicCompletion.addEquivOfQuotientEquiv_smul I I (fun n => (e n).toAddEquiv) he id hσ
  refine ⟨Ψ.trans (AdicCompletion.ofLinearEquiv I T).symm.toAddEquiv, fun r x => ?_⟩
  change (AdicCompletion.ofLinearEquiv I T).symm (Ψ (r • x)) =
    r • (AdicCompletion.ofLinearEquiv I T).symm (Ψ x)
  rw [hΨ]
  apply (AdicCompletion.ofLinearEquiv I T).injective
  rw [LinearEquiv.apply_symm_apply]
  change id r • Ψ x = AdicCompletion.of I T (r • (AdicCompletion.ofLinearEquiv I T).symm (Ψ x))
  rw [adicCompletion_of_smul I hI]
  change id r • Ψ x = r • (AdicCompletion.ofLinearEquiv I T)
    ((AdicCompletion.ofLinearEquiv I T).symm (Ψ x))
  rw [LinearEquiv.apply_symm_apply]
  rfl

end CompleteOfLevels

section TensorTransport

/-- **Base change along compatible ring isomorphisms.** If `α : A ≅ B` and `β : A' ≅ B'` are ring
isomorphisms compatible with `A → A'` and `B → B'`, and `M` is a module over `A` and over `B`
compatibly with `α`, then `A' ⊗_A M` and `B' ⊗_B M` are identified, semilinearly over `β`. -/
theorem exists_tensorProduct_addEquiv_of_ringEquiv {A A' B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra A A'] [Algebra B B'] (α : A ≃+* B) (β : A' ≃+* B')
    (hsq : ∀ a, algebraMap B B' (α a) = β (algebraMap A A' a)) (M : Type*) [AddCommGroup M]
    [Module A M] [Module B M] (hM : ∀ (a : A) (m : M), α a • m = a • m) :
    ∃ Φ : A' ⊗[A] M ≃+ B' ⊗[B] M, ∀ (r : A') (x : A' ⊗[A] M), Φ (r • x) = β r • Φ x := by
  let F : A' ⊗[A] M →+ B' ⊗[B] M := TensorProduct.liftAddHom
    { toFun := fun r => (TensorProduct.mk B B' M (β r)).toAddMonoidHom
      map_zero' := by ext m; simp
      map_add' := fun r r' => by ext m; simp }
    (fun a r m => by
      change β (a • r) ⊗ₜ[B] m = β r ⊗ₜ[B] (a • m)
      rw [Algebra.smul_def, map_mul, ← hsq, ← Algebra.smul_def, TensorProduct.smul_tmul, hM])
  let G : B' ⊗[B] M →+ A' ⊗[A] M := TensorProduct.liftAddHom
    { toFun := fun r => (TensorProduct.mk A A' M (β.symm r)).toAddMonoidHom
      map_zero' := by ext m; simp
      map_add' := fun r r' => by ext m; simp }
    (fun b r m => by
      change β.symm (b • r) ⊗ₜ[A] m = β.symm r ⊗ₜ[A] (b • m)
      obtain ⟨a, rfl⟩ := α.surjective b
      rw [Algebra.smul_def, map_mul, hsq, RingEquiv.symm_apply_apply, ← Algebra.smul_def,
        TensorProduct.smul_tmul, hM])
  have hF : ∀ (r : A') (m : M), F (r ⊗ₜ m) = β r ⊗ₜ m := fun _ _ => rfl
  have hG : ∀ (r : B') (m : M), G (r ⊗ₜ m) = β.symm r ⊗ₜ m := fun _ _ => rfl
  have hGF : ∀ x, G (F x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r m => rw [hF, hG, RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hFG : ∀ y, F (G y) = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul r m => rw [hG, hF, RingEquiv.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let Φ : A' ⊗[A] M ≃+ B' ⊗[B] M :=
    { F with
      invFun := G
      left_inv := hGF
      right_inv := hFG }
  refine ⟨Φ, fun r x => ?_⟩
  change F (r • x) = β r • F x
  induction x using TensorProduct.inductionOn with
  | tmul r' m => rw [TensorProduct.smul_tmul', hF, hF, TensorProduct.smul_tmul', smul_eq_mul,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Base change carries a commutative square with two equivalences as sides to a commutative
square. -/
theorem baseChange_symm_comp_eq {R A P Q P' Q' : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup P'] [Module R P']
    [AddCommGroup Q'] [Module R Q'] (e : P ≃ₗ[R] Q) (e' : P' ≃ₗ[R] Q') (u : P →ₗ[R] P')
    (v : Q →ₗ[R] Q') (hsq : ∀ p, v (e p) = e' (u p)) (w : A ⊗[R] Q) :
    LinearMap.baseChange A u (LinearEquiv.baseChange R A Q P e.symm w) =
      LinearEquiv.baseChange R A Q' P' e'.symm (LinearMap.baseChange A v w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a q =>
    rw [LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearEquiv.baseChange_tmul]
    obtain ⟨p, rfl⟩ := e.surjective q
    rw [LinearEquiv.symm_apply_apply, hsq, LinearEquiv.symm_apply_apply]
  | add w w' hw hw' => simp only [map_add, hw, hw']

end TensorTransport

section Congr

/-- **Transport of completions along algebra equivalences commutes with the maps of
completions**, for a commutative square of rings `χ ∘ f = f' ∘ φ` with `f`, `f'` equivalences. -/
theorem adicCompletionMap_congrAlgEquiv {A R S A' R' S' : Type*} [CommRing A] [CommRing R]
    [CommRing S] [Algebra A R] [Algebra A S] [CommRing A'] [CommRing R'] [CommRing S']
    [Algebra A' R'] [Algebra A' S'] {I : Ideal R} {J : Ideal S} {I' : Ideal R'} {J' : Ideal S'}
    (f : R ≃ₐ[A] S) (hIJ : J = I.map (f : R →+* S)) (f' : R' ≃ₐ[A'] S')
    (hIJ' : J' = I'.map (f' : R' →+* S')) (φ : R →+* R') (hφ : I.map φ ≤ I') (χ : S →+* S')
    (hχ : J.map χ ≤ J') (hsq : ∀ r, χ (f r) = f' (φ r)) (x : AdicCompletion I R) :
    adicCompletionMap χ J J' hχ (AdicCompletion.congrAlgEquiv f hIJ x) =
      AdicCompletion.congrAlgEquiv f' hIJ' (adicCompletionMap φ I I' hφ x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicCompletionMap_evalₐ,
    show AdicCompletion.evalₐ J n (AdicCompletion.congrAlgEquiv f hIJ x) =
      AdicCompletion.congrQuotientEquiv f hIJ n (AdicCompletion.evalₐ I n x) from
    AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv I J _ _ n x,
    show AdicCompletion.evalₐ J' n (AdicCompletion.congrAlgEquiv f' hIJ'
        (adicCompletionMap φ I I' hφ x)) =
      AdicCompletion.congrQuotientEquiv f' hIJ' n
        (AdicCompletion.evalₐ I' n (adicCompletionMap φ I I' hφ x)) from
    AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv I' J' _ _ n _,
    adicCompletionMap_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  change Ideal.Quotient.mk (J' ^ n) (χ (f r)) = Ideal.Quotient.mk (J' ^ n) (f' (φ r))
  rw [hsq]

end Congr

section Blowup

attribute [local instance] BlowupChartPoint.baseModule BlowupChartPoint.completionAlgebra

variable {S : AlgebraizationSituation.{u}} {y' : (situationBlowUpU S).toScheme}

variable (S) (y') in
/-- The stalk of `I𝒪_{U'}` at `y'` is the extension of the stalk of `I𝒪_U` at `y = b(y')`. -/
theorem stalk_blowupIdealU_eq_map :
    IdealSheafData.stalk (blowupIdealU S) y' =
      (IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y')).map
        ((blowupRestrict S).stalkMap y').hom := by
  rw [← comap_idealOnOpen_blowupRestrict]
  exact IdealSheafData.stalk_comap _ _ _

/-- **The completed local rings, read on the chart, form a commutative square**: the map
`𝒪_{U,y}^∧ → 𝒪_{U',y'}^∧` induced by `b`, read through `BlowupChartPoint.baseCompletionEquiv` and
`BlowupChartPoint.chartCompletionEquiv`, is `(A_𝔮)^∧ → (A[I/a]_Q)^∧`. -/
theorem BlowupChartPoint.affineBlowupCompletionMap_baseCompletionEquiv (c : BlowupChartPoint S y')
    (x : completedLocalRing (idealOnOpen S) (blowupRestrict S y')) :
    affineBlowupCompletionMap (blowupCentreIdeal S) c.a c.Q.asIdeal (c.baseCompletionEquiv x) =
      c.chartCompletionEquiv (adicCompletionMap ((blowupRestrict S).stalkMap y').hom _ _
        (stalk_blowupIdealU_eq_map S y').ge x) := by
  let : Algebra (S.U.toScheme.presheaf.stalk (blowupRestrict S y'))
      (Localization.AtPrime (c.Q.asIdeal.under Γ(S.X, ⊤))) := c.baseStalkEquiv.toRingHom.toAlgebra
  let : Algebra ((situationBlowUpU S).toScheme.presheaf.stalk y')
      (Localization.AtPrime c.Q.asIdeal) := c.chartStalkEquiv.toRingHom.toAlgebra
  change adicCompletionMap _ _ _ _ (AdicCompletion.congrAlgEquiv (AlgEquiv.ofRingEquiv
      (R := S.U.toScheme.presheaf.stalk (blowupRestrict S y')) (f := c.baseStalkEquiv)
      fun _ => rfl) c.map_stalk_idealOnOpen.symm x) =
    AdicCompletion.congrAlgEquiv (AlgEquiv.ofRingEquiv
      (R := (situationBlowUpU S).toScheme.presheaf.stalk y') (f := c.chartStalkEquiv)
      fun _ => rfl) c.map_stalk_blowupIdealU.symm _
  exact adicCompletionMap_congrAlgEquiv _ _ _ _ _ _ _ _
    (fun r => (c.chartStalkEquiv_stalkMap r).symm) x

variable (S y') in
/-- The local ring `𝒪_{U',y'}` as an algebra over `𝒪_{U,y}`, `y = b(y')`, through the stalk map of
`b|_{U'}`. This is `Stacks.RelativeDifferentialStalkMap.algebraStalkMap`, named again at the
spelling `X.presheaf.stalk` of the local rings, at which instance search can find it. -/
abbrev blowupStalkAlgebra : Algebra (S.U.toScheme.presheaf.stalk (blowupRestrict S y'))
    ((situationBlowUpU S).toScheme.presheaf.stalk y') :=
  ((blowupRestrict S).stalkMap y').hom.toAlgebra

attribute [local instance] blowupStalkAlgebra

variable (S y') in
/-- The completed local ring `𝒪_{U',y'}^∧` as an algebra over `𝒪_{U,y}^∧`. -/
abbrev blowupCompletedLocalRingAlgebra :
    Algebra (completedLocalRing (idealOnOpen S) (blowupRestrict S y'))
      (completedLocalRing (blowupIdealU S) y') :=
  (adicCompletionMap (algebraMap _ _) _ _ (stalk_blowupIdealU_eq_map S y').symm.le).toAlgebra

attribute [local instance] blowupCompletedLocalRingAlgebra

/-- The level-`n` reduction `ℱ_x^∧ / ℐ_x^{n+1} ℱ_x^∧` of the completed stalk, the quotient taken by
a submodule over the local ring `𝒪_{X,x}`, is the stalk `ℱ_{n,x}`. -/
def completedStalkQuotientStalkIdealEquiv {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : Stacks.Coherent.CoherentAdicSystems I) (x : X) (n : ℕ) :
    (completedStalk I G x ⧸ (IdealSheafData.stalk I x ^ (n + 1) •
        ⊤ : Submodule (X.presheaf.stalk x) (completedStalk I G x))) ≃ₗ[X.presheaf.stalk x]
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (G.obj.obj (op n)) :=
  (Submodule.Quotient.equiv _ _ (formalStalkEquivCompletedStalk G x).symm
    (map_smul_top_linearEquiv _ _)).trans (formalStalkQuotientEquivStalk G x n)

/-- `completedStalkQuotientStalkIdealEquiv` is compatible with the transition maps. -/
theorem map_completedStalkQuotientStalkIdealEquiv {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : Stacks.Coherent.CoherentAdicSystems I) (x : X) {m n : ℕ}
    (h : m ≤ n) (q : completedStalk I G x ⧸ (IdealSheafData.stalk I x ^ (n + 1) •
        ⊤ : Submodule (X.presheaf.stalk x) (completedStalk I G x))) :
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map (G.obj.map (homOfLE h).op)).hom
        (completedStalkQuotientStalkIdealEquiv G x n q) =
      completedStalkQuotientStalkIdealEquiv G x m
        (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h) q) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact congrArg (fun f => f.hom (formalStalkEquivModuleStalkLimit G x
      ((formalStalkEquivCompletedStalk G x).symm a)))
    (limit.w (G.obj ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor X x) (homOfLE h).op)

variable (y') in
/-- **The levels of the completed stalk of the pullback.** The level-`n` reduction of the formal
stalk of `(b|_{U'}^*ℱₙ)` at `y'` is `𝒪_{U',y'} ⊗ ℱ_{n,y}` (Stacks 0098), which is the level-`n`
reduction of `𝒪_{U',y'}^∧ ⊗_{𝒪_{U,y}^∧} ℱ_y^∧`. -/
def blowupPullbackFormalStalkQuotientEquiv
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (n : ℕ) :
    (formalStalk (blowupPullbackSystem S F) y' ⧸
      (IdealSheafData.stalk (blowupIdealU S) y' ^ (n + 1) •
        ⊤ : Submodule ((situationBlowUpU S).toScheme.presheaf.stalk y')
          (formalStalk (blowupPullbackSystem S F) y'))) ≃ₗ[
        (situationBlowUpU S).toScheme.presheaf.stalk y']
      ((completedLocalRing (blowupIdealU S) y' ⊗[completedLocalRing (idealOnOpen S)
          (blowupRestrict S y')] completedStalk (idealOnOpen S) F (blowupRestrict S y')) ⧸
        (IdealSheafData.stalk (blowupIdealU S) y' ^ (n + 1) • ⊤ :
          Submodule ((situationBlowUpU S).toScheme.presheaf.stalk y')
            (completedLocalRing (blowupIdealU S) y' ⊗[completedLocalRing (idealOnOpen S)
              (blowupRestrict S y')] completedStalk (idealOnOpen S) F (blowupRestrict S y')))) :=
  (formalStalkQuotientEquivStalk (blowupPullbackSystem S F) y' n).trans
    ((((Stacks.ModuleSkyscraper.pullbackStalkIso (blowupRestrict S) y').app
      (F.obj.obj (op n))).symm.toLinearEquiv.trans
      (LinearEquiv.baseChange _ _ _ _
        (completedStalkQuotientStalkIdealEquiv F (blowupRestrict S y') n).symm)).trans
      (tensorQuotientEquivCompletedTensorQuotient _ _ (stalk_blowupIdealU_eq_map S y').symm _
        (fun _ => rfl) (Ideal.fg_of_isNoetherianRing _) (n + 1)))

variable (y') in
/-- `blowupPullbackFormalStalkQuotientEquiv` is the composite of `formalStalkQuotientEquivStalk`,
the inverse of the pullback stalk isomorphism, the base change of the inverse of
`completedStalkQuotientStalkIdealEquiv`, and `tensorQuotientEquivCompletedTensorQuotient`. -/
theorem blowupPullbackFormalStalkQuotientEquiv_apply
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (n : ℕ)
    (x : formalStalk (blowupPullbackSystem S F) y' ⧸
      (IdealSheafData.stalk (blowupIdealU S) y' ^ (n + 1) •
        ⊤ : Submodule ((situationBlowUpU S).toScheme.presheaf.stalk y')
          (formalStalk (blowupPullbackSystem S F) y'))) :
    blowupPullbackFormalStalkQuotientEquiv y' F n x =
      tensorQuotientEquivCompletedTensorQuotient _ _ (stalk_blowupIdealU_eq_map S y').symm _
        (fun _ => rfl) (Ideal.fg_of_isNoetherianRing _) (n + 1)
        (LinearEquiv.baseChange _ _ _ _
          (completedStalkQuotientStalkIdealEquiv F (blowupRestrict S y') n).symm
          (((Stacks.ModuleSkyscraper.pullbackStalkIso (blowupRestrict S) y').app
            (F.obj.obj (op n))).symm.toLinearEquiv
            (formalStalkQuotientEquivStalk (blowupPullbackSystem S F) y' n x))) :=
  rfl

variable (y') in
/-- `blowupPullbackFormalStalkQuotientEquiv` is compatible with the transition maps. -/
theorem transitionMap_blowupPullbackFormalStalkQuotientEquiv
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) {m n : ℕ} (h : m ≤ n)
    (x : formalStalk (blowupPullbackSystem S F) y' ⧸
      (IdealSheafData.stalk (blowupIdealU S) y' ^ (n + 1) •
        ⊤ : Submodule ((situationBlowUpU S).toScheme.presheaf.stalk y')
          (formalStalk (blowupPullbackSystem S F) y'))) :
    AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h)
        (blowupPullbackFormalStalkQuotientEquiv y' F n x) =
      blowupPullbackFormalStalkQuotientEquiv y' F m
        (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h) x) := by
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have ha : formalStalkQuotientEquivStalk (blowupPullbackSystem S F) y' m
        (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h) (Submodule.Quotient.mk l)) =
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor _ y').map
        ((blowupPullbackSystem S F).obj.map (homOfLE h).op)).hom
        (formalStalkQuotientEquivStalk (blowupPullbackSystem S F) y' n
          (Submodule.Quotient.mk l)) :=
    (congrArg (fun f => f.hom (formalStalkEquivModuleStalkLimit (blowupPullbackSystem S F) y' l))
      (limit.w ((blowupPullbackSystem S F).obj ⋙
        Stacks.ModuleSkyscraper.modulesStalkFunctor _ y') (homOfLE h).op)).symm
  have hb : ∀ z : (Stacks.ModuleSkyscraper.modulesStalkFunctor _ y').obj
      ((blowupPullbackSystem S F).obj.obj (op n)),
      ((Stacks.ModuleSkyscraper.pullbackStalkIso (blowupRestrict S) y').app
          (F.obj.obj (op m))).symm.toLinearEquiv
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor _ y').map
          ((blowupPullbackSystem S F).obj.map (homOfLE h).op)).hom z) =
      LinearMap.baseChange ((situationBlowUpU S).toScheme.presheaf.stalk y')
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme (blowupRestrict S y')).map
            (F.obj.map (homOfLE h).op)).hom
        (((Stacks.ModuleSkyscraper.pullbackStalkIso (blowupRestrict S) y').app
          (F.obj.obj (op n))).symm.toLinearEquiv z) := fun z =>
    congrArg (fun f => f.hom z)
      ((Stacks.ModuleSkyscraper.pullbackStalkIso (blowupRestrict S) y').inv.naturality
        (F.obj.map (homOfLE h).op))
  refine ((congrArg (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h))
    (blowupPullbackFormalStalkQuotientEquiv_apply y' F n _)).trans ?_).trans
    (blowupPullbackFormalStalkQuotientEquiv_apply y' F m _).symm
  refine (transitionMap_tensorQuotientEquivCompletedTensorQuotient
    ((situationBlowUpU S).toScheme.presheaf.stalk y')
    (IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y'))
    (stalk_blowupIdealU_eq_map S y').symm (completedStalk (idealOnOpen S) F (blowupRestrict S y'))
    (fun _ => rfl) (Ideal.fg_of_isNoetherianRing _) (Nat.succ_le_succ h) _).trans ?_
  refine congrArg (tensorQuotientEquivCompletedTensorQuotient
    ((situationBlowUpU S).toScheme.presheaf.stalk y')
    (IdealSheafData.stalk (idealOnOpen S) (blowupRestrict S y'))
    (stalk_blowupIdealU_eq_map S y').symm (completedStalk (idealOnOpen S) F (blowupRestrict S y'))
    (fun _ => rfl) (Ideal.fg_of_isNoetherianRing _) (m + 1)) ?_
  refine (baseChange_symm_comp_eq (A := (situationBlowUpU S).toScheme.presheaf.stalk y') _ _ _ _
    (map_completedStalkQuotientStalkIdealEquiv F _ h) _).trans ?_
  refine congrArg (LinearEquiv.baseChange _ ((situationBlowUpU S).toScheme.presheaf.stalk y') _ _
    (completedStalkQuotientStalkIdealEquiv F (blowupRestrict S y') m).symm) ?_
  exact (hb _).symm.trans (congrArg _ ha.symm)

/-- **The completed stalk of the pullback along a chart** ([Stacks, Tag 0EJK], "details omitted").
For a chart of the blowup through `y'`, the completed stalk at `y'` of the pullback `(b|_{U'}^*ℱₙ)`
is `(A[I/a]_Q)^∧ ⊗_{(A_𝔮)^∧} ℱ_y^∧`, semilinearly over
`BlowupChartPoint.chartCompletionEquiv`. -/
theorem BlowupChartPoint.completedStalkComparison (c : BlowupChartPoint S y')
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : c.CompletedStalkComparison F := by
  have hJ' : (IdealSheafData.stalk (blowupIdealU S) y').FG := Ideal.fg_of_isNoetherianRing _
  have : Module.Finite (completedLocalRing (idealOnOpen S) (blowupRestrict S y'))
      (completedStalk (idealOnOpen S) F (blowupRestrict S y')) := finite_completedStalk _ F _
  have : IsNoetherianRing (completedLocalRing (blowupIdealU S) y') :=
    AdicCompletion.isNoetherianRing _
  have : IsAdicComplete ((IdealSheafData.stalk (blowupIdealU S) y').map
      (algebraMap _ (completedLocalRing (blowupIdealU S) y')))
      (completedLocalRing (blowupIdealU S) y') :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hJ')
  have : IsAdicComplete (IdealSheafData.stalk (blowupIdealU S) y')
      (completedLocalRing (blowupIdealU S) y' ⊗[completedLocalRing (idealOnOpen S)
        (blowupRestrict S y')] completedStalk (idealOnOpen S) F (blowupRestrict S y')) :=
    (IsAdicComplete.map_algebraMap_iff (S := completedLocalRing (blowupIdealU S) y') _ _).mp
      (AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing _ _)
  obtain ⟨Φ₀, hΦ₀⟩ := exists_adicCompletion_addEquiv_of_quotientEquiv
    (IdealSheafData.stalk (blowupIdealU S) y') hJ' (blowupPullbackFormalStalkQuotientEquiv y' F)
    (fun h x => transitionMap_blowupPullbackFormalStalkQuotientEquiv y' F h x)
  obtain ⟨Φ₁, hΦ₁⟩ := exists_tensorProduct_addEquiv_of_ringEquiv c.baseCompletionEquiv
    c.chartCompletionEquiv (fun a => c.affineBlowupCompletionMap_baseCompletionEquiv a)
    (completedStalk (idealOnOpen S) F (blowupRestrict S y')) (fun a m => by
      change c.baseCompletionEquiv.symm (c.baseCompletionEquiv a) • m = a • m
      rw [RingEquiv.symm_apply_apply])
  refine ⟨Φ₀.trans Φ₁, fun r x => ?_⟩
  exact (congrArg Φ₁ (hΦ₀ r x)).trans (hΦ₁ r (Φ₀ x))

/-- **(0EJL) and (0EJM) at a point of the exceptional divisor.** Let `A` have a dualizing complex,
let the fibres of the blowup have dimension `< d`, and let `y'` be a point of `U'` on the
exceptional divisor with a prime `𝔭'` of `𝒪_{X',y'}^∧` not containing `I`. Then the prime `𝔭` of
`𝒪_{X,y}^∧`, `y = b(y')`, under `𝔭'` satisfies
`depth + dim + δ^Y_Z(y) ≤ depth' + dim' + δ^{Y'}_{Z'}(y') + (d - 1)` and `dim' ≤ dim`. -/
theorem exists_depthAddDimAddDistance_le_blowup (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K)
    (d : ℤ)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (y' : (situationBlowUpU S).toScheme) (e' : situationExceptional S)
    (he' : situationExceptionalι S e' = (situationBlowUpU S).ι y')
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hp' : ¬ completedLocalIdeal (blowupIdealU S) y' ≤ p'.asIdeal) :
    ∃ (y : S.U.toScheme) (z : S.Y) (_ : S.U.ι.base y = S.Yι.base z)
      (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)),
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal ∧
      depthAddDimAddDistance S F y z p ≤
        enatToEInt (completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p') +
          krullDimToEInt (ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal)) +
          enatToEInt (exceptionalDistance S e') + ((d - 1 : ℤ) : EInt) ∧
      krullDimToEInt (ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal)) ≤
        krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) := by
  obtain ⟨c⟩ := nonempty_blowupChartPoint S y'
  exact exists_depthAddDimAddDistance_le_blowup_of_comparison S hdual d hfib F y' e' he' p' hp' c
    (c.completedStalkComparison F)

end Blowup

end Stacks.Algebraization

end
