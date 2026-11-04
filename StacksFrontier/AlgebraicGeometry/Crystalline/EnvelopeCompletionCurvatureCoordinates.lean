module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCoordinates
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateFunctionals
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionFormsBasis

/-!
# Vanishing curvature over the completed envelope is commutation of the coordinate operators

Let `D` be the `p`-adic completion of the divided power envelope of a polynomial presentation
`A[x_i] ⊇ J` in finitely many variables, `Ω̂^*_D` its completed divided power forms, and
`∇ : M → M ⊗̂_D Ω̂¹_D` a completed connection on a `p`-adically complete `D`-module.  The
one-forms `Ω̂¹_D` are free on the `d x_i` (`Crystalline.envelopeCompletionFormsBasis`), so `∇` has
coordinate operators `θ_j` with `∇ m = ∑_j θ_j(m) ⊗ d x_j` (`Crystalline.coordOp`).  This module
proves that the two readings of integrability of Remark [Stacks, Tag 07I0] and of
[Stacks, Tag 07JD] agree there: the curvature `M → M ⊗̂ Ω¹ → M ⊗̂ Ω²` vanishes if and only if the
coordinate operators commute pairwise.

## The argument

The `d x_j` are closed, so `∇² m = ∑_{j,k} θ_k θ_j m ⊗ (d x_j ∧ d x_k)`
(`Crystalline.CompletedDeRham.differential_nabla_eq_sum_coordOp`).  If the operators commute the
terms indexed `(j, k)` and `(k, j)` cancel, the wedge of one-forms being alternating.  Conversely
the two-forms `d x_j ∧ d x_k` are detected by the `D`-linear functionals
`Crystalline.envelopeCompletionTwoFormCoord`, obtained from the coordinates of the basis by the
pairing of `⋀² Ω` with `⋀² Ω^∨` and extended to the completion, `D` being `p`-adically complete;
pushed through `M ⊗ Ω² → M`, `x ⊗ ω ↦ φ(ω) x`, level by level, they read off
`θ_a θ_c m - θ_c θ_a m = 0` from `∇² m = 0`, `M` being `p`-adically separated.

## Main results

* `Crystalline.CompletedDeRham.isCurvatureZero_of_coordOp_comm` and
  `Crystalline.CompletedDeRham.coordOp_comm_of_isCurvatureZero` — the two directions, for any
  graded family of forms whose one-forms have a finite basis of closed forms.
* `Crystalline.isCurvatureZero_envelopeCompletion_iff_coordOp_comm` — **over the completed
  envelope, the curvature of a completed connection vanishes if and only if its coordinate
  operators commute.**

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v uI

namespace Crystalline

/-! ### Detecting zero in a completed tensor product through a functional -/

section Detect

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega]
  [Module D Omega] {M : Type u} [AddCommGroup M] [Module D M]

/-- **A functional `x ⊗ ω ↦ c(ω) x` kills every tensor whose image in the completion is zero**,
provided `M` is `p`-adically separated: such a tensor lies in `p^n (M ⊗ Ω)` for every `n`, so its
image lies in `p^n M` for every `n`. -/
theorem dualTensorCoordinate_eq_zero_of_toCompletedTensor_eq_zero
    (hM : IsHausdorff (pAdicIdeal (A := D) p) M) (c : Omega →ₗ[D] D) {y : M ⊗[D] Omega}
    (hy : toCompletedTensor p D Omega M y = 0) : dualTensorCoordinate M c y = 0 := by
  refine hM.haus _ fun n ↦ ?_
  have h : (toCompletedTensor p D Omega M y).val n = 0 := by
    rw [hy]
    exact AdicCompletion.val_zero_apply _ _ n
  rw [toCompletedTensor, AdicCompletion.of_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h
  rw [SModEq.zero]
  exact map_mem_pow_smul_top_of_mem _ (dualTensorCoordinate M c) n h

end Detect

namespace CompletedDeRham

/-! ### The curvature in coordinates, for a finite basis of closed one-forms -/

section Generic

variable (p : ℕ) {D : Type u} [CommRing D] {Om : ℕ → Type u} [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] {wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)}
  {deRham : ∀ i, Om i →+ Om (i + 1)} {dmap : D → Om 1} {ι : Type uI} [Fintype ι]
  [DecidableEq ι] (b : Module.Basis ι D (Om 1)) {M : Type u} [AddCommGroup M] [Module D M]
  (hM : IsPAdicallyComplete p D M) (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- **The curvature of a completed connection in coordinates**: when the one-forms have a finite
basis `d x_j` of closed forms, `∇² m = ∑_{j,k} θ_k θ_j m ⊗ (d x_j ∧ d x_k)`, the `θ_j` being the
coordinate operators of `∇`. -/
theorem differential_nabla_eq_sum_coordOp (hb : ∀ j, deRham 1 (b j) = 0) (m : M) :
    differential p D Om wedge deRham M nabla hleib 1 (nabla m) =
      ∑ j, ∑ k, toCompletedTensor p D (Om (1 + 1)) M
        (coordOp p b hM nabla k (coordOp p b hM nabla j m) ⊗ₜ[D] wedge 1 (b j) (b k)) := by
  have hexp : IsFiniteCoordinateExpansion p D (Om 1) (⇑b) nabla (coordOp p b hM nabla)
      Finset.univ :=
    { sum_eq := fun m ↦ by rw [nabla_eq_sum_coordOp p b hM nabla m, map_sum]
      eq_zero_of_notMem := fun j hj _ ↦ absurd (Finset.mem_univ j) hj }
  rw [hexp.sum_eq m, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [differential_toCompletedTensor_tmul p D Om wedge deRham M nabla hleib (⇑b)
    (coordOp p b hM nabla) Finset.univ hexp, hb j, TensorProduct.tmul_zero, map_zero, add_zero]

/-- **Commuting coordinate operators give a connection of curvature zero**, the one-forms having
a finite basis of closed forms and the wedge of one-forms being alternating: in the expansion of
`Crystalline.CompletedDeRham.differential_nabla_eq_sum_coordOp` the terms indexed `(j, k)` and
`(k, j)` cancel. -/
theorem isCurvatureZero_of_coordOp_comm (hb : ∀ j, deRham 1 (b j) = 0)
    (halt : ∀ eta : Om 1, wedge 1 eta eta = 0)
    (hcomm : ∀ j k, coordOp p b hM nabla j ∘ coordOp p b hM nabla k =
      coordOp p b hM nabla k ∘ coordOp p b hM nabla j) :
    IsCurvatureZero p D Om wedge deRham M nabla hleib := by
  intro m
  have hanti : ∀ eta zeta : Om 1, wedge 1 eta zeta + wedge 1 zeta eta = 0 := fun eta zeta ↦ by
    have h0 := halt (eta + zeta)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h0
    exact (add_comm _ _).trans h0
  rw [differential_nabla_eq_sum_coordOp p b hM nabla hleib hb m, ← Finset.sum_product']
  refine Finset.sum_involution (fun a _ ↦ a.swap) (fun a _ ↦ ?_) (fun a _ hne ↦ ?_)
    (fun a _ ↦ Finset.mem_univ _) (fun a _ ↦ Prod.swap_swap a)
  · obtain ⟨j, k⟩ := a
    have hjk : coordOp p b hM nabla j (coordOp p b hM nabla k m) =
        coordOp p b hM nabla k (coordOp p b hM nabla j m) := congrFun (hcomm j k) m
    simp only [Prod.swap_prod_mk, hjk]
    rw [← map_add, ← TensorProduct.tmul_add, hanti, TensorProduct.tmul_zero, map_zero]
  · obtain ⟨j, k⟩ := a
    intro heq
    rw [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hne (by rw [halt, TensorProduct.tmul_zero, map_zero])

/-- **A connection of curvature zero has commuting coordinate operators**, given functionals
`φ_{ac}` on the two-forms detecting the wedges of the basis vectors,
`φ_{ac}(d x_j ∧ d x_k) = δ_{ka} δ_{jc} - δ_{kc} δ_{ja}`: applied to `∇² m = 0` through
`x ⊗ ω ↦ φ_{ac}(ω) x` they give `θ_a θ_c m - θ_c θ_a m = 0`. -/
theorem coordOp_comm_of_isCurvatureZero (hb : ∀ j, deRham 1 (b j) = 0)
    (phi : ι → ι → (Om (1 + 1) →ₗ[D] D))
    (hphi : ∀ a c j k, phi a c (wedge 1 (b j) (b k)) =
      (if k = a then 1 else 0) * (if j = c then 1 else 0) -
        (if k = c then 1 else 0) * (if j = a then 1 else 0))
    (hcurv : IsCurvatureZero p D Om wedge deRham M nabla hleib) (a c : ι) :
    coordOp p b hM nabla a ∘ coordOp p b hM nabla c =
      coordOp p b hM nabla c ∘ coordOp p b hM nabla a := by
  funext m
  have h0 : toCompletedTensor p D (Om (1 + 1)) M (∑ j, ∑ k,
      coordOp p b hM nabla k (coordOp p b hM nabla j m) ⊗ₜ[D] wedge 1 (b j) (b k)) = 0 := by
    have h := hcurv m
    rw [differential_nabla_eq_sum_coordOp p b hM nabla hleib hb m] at h
    simpa only [map_sum] using h
  have h1 := dualTensorCoordinate_eq_zero_of_toCompletedTensor_eq_zero p hM.toIsHausdorff
    (phi a c) h0
  simp only [map_sum, dualTensorCoordinate_tmul, hphi, sub_smul, ite_mul, one_mul, zero_mul,
    ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h1
  exact sub_eq_zero.mp h1

end Generic

end CompletedDeRham

/-! ### The completed envelope -/

section Envelope

variable {A : DividedPowerRing.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ) [Fact p.Prime]
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

omit [Fintype ι] [DecidableEq ι] [Fact p.Prime] in
/-- **The wedge of completed one-forms of `D` is alternating**: `η ∧ η = 0`.  The one-form `η` is
`1 ∧ η` for the unit zero-form `1`, and the wedge is alternating in that position by
`Crystalline.isGradedExterior_completedDividedPower`. -/
theorem envelopeCompletionFormsWedge_self (eta : envelopeCompletionForms E p hp 1) :
    envelopeCompletionFormsWedge E p hp 1 eta eta = 0 := by
  have h := (isGradedExterior_completedDividedPower p (A : Type u)
    (envelopeCompletion E p hp).dividedPowers).wedge_self 0
    (completedUnitZeroForm p (A : Type u) (envelopeCompletion E p hp).dividedPowers) eta
  rw [completedDividedPowerWedge_completedUnitZeroForm] at h
  exact h

/-- **The basis vectors `d x_j` of `Ω̂¹_D` are closed.** -/
theorem envelopeCompletionFormsDeRham_basis (j : ι) :
    completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers 1
      (envelopeCompletionFormsBasis E p hp j) = 0 := by
  rw [envelopeCompletionFormsBasis_apply]
  exact deRham_completedFormsDifferential p (A : Type u) _ _

/-- **The `a`-th coordinate of a divided power one-form of `D`**: its image in `Ω̂¹_D` read in
the basis `Crystalline.envelopeCompletionFormsBasis`. -/
def envelopeCompletionOneFormCoord (a : ι) :
    Module.Dual (envelopeCompletion E p hp : Type u)
      (dividedPowerDifferentials (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers) :=
  (envelopeCompletionFormsBasis E p hp).coord a ∘ₗ
    AdicCompletion.of (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p) _ ∘ₗ
      (exteriorPower.oneEquiv _ _).symm.toLinearMap

/-- The `a`-th coordinate of `d x_k` is `δ_{ka}`. -/
theorem envelopeCompletionOneFormCoord_differential (a k : ι) :
    envelopeCompletionOneFormCoord E p hp a
      (dividedPowerDifferential (A := (A : Type u)) (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionCoord E p hp k)) = if k = a then 1 else 0 := by
  have hb := envelopeCompletionFormsBasis_apply E p hp k
  simp only [envelopeCompletionFormsDifferential, completedDividedPowerDifferentialOnRing_eq,
    dividedPowerOneForm_apply] at hb
  simp only [envelopeCompletionOneFormCoord, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- **The functional `φ_{ac} : Ω̂²_D → D`** dual to `d x_a ∧ d x_c`: the pairing of `⋀² Ω` with
the wedge of the coordinates `a` and `c`, extended to the `p`-adic completion, which `D` is its
own completion. -/
def envelopeCompletionTwoFormCoord (a c : ι) :
    envelopeCompletionForms E p hp 2 →ₗ[(envelopeCompletion E p hp : Type u)]
      (envelopeCompletion E p hp : Type u) :=
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p)
      (envelopeCompletion E p hp : Type u)).symm.toLinearMap ∘ₗ
    (AdicCompletion.map (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p)
      (exteriorPower.pairingDual (envelopeCompletion E p hp : Type u) _ 2
        (exteriorPower.ιMulti _ 2 ![envelopeCompletionOneFormCoord E p hp a,
          envelopeCompletionOneFormCoord E p hp c]))).restrictScalars _

/-- **The functional `φ_{ac}` on `d x_j ∧ d x_k`** is `δ_{ka} δ_{jc} - δ_{kc} δ_{ja}`. -/
theorem envelopeCompletionTwoFormCoord_wedge (a c j k : ι) :
    envelopeCompletionTwoFormCoord E p hp a c
      (envelopeCompletionFormsWedge E p hp 1 (envelopeCompletionFormsBasis E p hp j)
        (envelopeCompletionFormsBasis E p hp k)) =
      (if k = a then 1 else 0) * (if j = c then 1 else 0) -
        (if k = c then 1 else 0) * (if j = a then 1 else 0) := by
  simp only [envelopeCompletionFormsBasis_apply, envelopeCompletionFormsDifferential,
    completedDividedPowerDifferentialOnRing_eq, envelopeCompletionFormsWedge,
    completedDividedPowerWedgeOnRing_apply, completedDividedPowerWedge_of_of,
    dividedPowerWedge_apply, dividedPowerOneForm_apply, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.oneEquiv_ιMulti, leftWedge_ιMulti]
  simp only [envelopeCompletionTwoFormCoord, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, AdicCompletion.map_of, LinearEquiv.coe_coe,
    AdicCompletion.ofLinearEquiv_symm_of, exteriorPower.pairingDual_ιMulti_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Fin.cons_zero, Fin.cons_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, envelopeCompletionOneFormCoord_differential]

/-- **Over the completed envelope, the curvature of a completed connection vanishes if and only if
its coordinate operators commute.**

`D` is the `p`-adic completion of the divided power envelope of a polynomial presentation in
finitely many variables, `Ω̂^*_D` its completed divided power forms, `M` a `p`-adically complete
`D`-module and `∇` a completed connection on it; the `θ_j` are the coordinate operators of `∇`
against the basis `d x_j` of `Ω̂¹_D`.  The composite `M → M ⊗̂ Ω¹ → M ⊗̂ Ω²` is zero — the
integrability of Remark [Stacks, Tag 07I0] — exactly when `θ_j θ_k = θ_k θ_j` for all `j, k`,
the integrability of [Stacks, Tag 07JD]. -/
theorem isCurvatureZero_envelopeCompletion_iff_coordOp_comm {M : Type u} [AddCommGroup M]
    [Module (envelopeCompletion E p hp : Type u) M]
    (hM : IsPAdicallyComplete p (envelopeCompletion E p hp : Type u) M)
    (nabla : CompletedConnection p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp) M) :
    CompletedDeRham.IsCurvatureZero p (envelopeCompletion E p hp : Type u)
        (envelopeCompletionForms E p hp) (envelopeCompletionFormsWedge E p hp)
        (completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers) M
        nabla (isGradedLeibniz_envelopeCompletionForms E p hp) ↔
      ∀ j k, coordOp p (envelopeCompletionFormsBasis E p hp) hM nabla j ∘
          coordOp p (envelopeCompletionFormsBasis E p hp) hM nabla k =
        coordOp p (envelopeCompletionFormsBasis E p hp) hM nabla k ∘
          coordOp p (envelopeCompletionFormsBasis E p hp) hM nabla j :=
  ⟨fun h j k ↦ CompletedDeRham.coordOp_comm_of_isCurvatureZero p
      (envelopeCompletionFormsBasis E p hp) hM nabla
      (isGradedLeibniz_envelopeCompletionForms E p hp)
      (envelopeCompletionFormsDeRham_basis E p hp) (envelopeCompletionTwoFormCoord E p hp)
      (envelopeCompletionTwoFormCoord_wedge E p hp) h j k,
    fun h ↦ CompletedDeRham.isCurvatureZero_of_coordOp_comm p
      (envelopeCompletionFormsBasis E p hp) hM nabla
      (isGradedLeibniz_envelopeCompletionForms E p hp)
      (envelopeCompletionFormsDeRham_basis E p hp) (envelopeCompletionFormsWedge_self E p hp) h⟩

end Envelope

end Crystalline

end
