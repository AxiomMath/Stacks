module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Deformation.Examples.Linear.LiftedPresentationAlgebra

/-!
# From an equality of first-order classes to a perturbation of the lifts

Let `P` be a graded `k`-algebra with grading `𝒜` and a weighted-homogeneous presentation

`k[X_i] ⟶ P`,  `X_i ↦ x_i ∈ 𝒜 (d i)`,  relations `F_j` of degree `e j`,

let `A` be a square-zero thickening of `k` with square-zero ideal `I` identified with a
`k`-module `V` through `I ≃ₗ[k] V`, and let `W` be the cokernel of the graded Jacobian of the
presentation.

A deformation `Q` of `P` over `A` with chosen homogeneous lifts of the generators has two
invariants of different strengths. The *first-order parts* of the relations are the elements
`r_j ∈ I ⊗[k] 𝒜 (e j)` naming the discrepancies `F_j(y)`; the *first-order class* is their image
in `W ⊗[k] V`, obtained by placing `r_j` in the `j`-th coordinate, reading `I` as `V` and passing
to the cokernel of the Jacobian. The class is the weaker datum, and it is the one that is an
invariant of the deformation: the parts depend on the chosen lifts, the class does not.

`GradedDeformation.exists_relationLift_common` needs the *parts* of two deformations to agree, and
what an isomorphism-class argument produces is agreement of their *classes*. This file bridges the
two, in the only way available: by *changing the lifts*. Two families of first-order parts with the
same class differ by an element of the image of the graded Jacobian, and the graded Jacobian is
exactly the effect on the parts of perturbing the lifts — so the parts can be made equal, and the
common family of lifted relations then exists.

That the difference is in the image of the Jacobian is right exactness of the tensor product:
`range jacobian → (∀ j, 𝒜 (e j)) → W` is exact, so tensoring with `V` keeps it exact, with no
flatness hypothesis on `V`. `TensorProduct.piRight` turns the collected parts into a single tensor
`(∀ j, 𝒜 (e j)) ⊗[k] V` on which the Jacobian acts, and the same interchange on the index set of
the generators turns the preimage back into a family of perturbations, one for each generator.

## Main definitions

* `GradedDeformation.piTensorRightEquiv`: the interchange of a finite product with a tensor
  factor, composed with the identification of that factor with `V`.

## Main results

* `GradedDeformation.sum_relationComponent_eq_rTensor_mkQ`: the first-order class of a family of
  first-order parts is the assembled family read in the cokernel of the Jacobian. This is what
  makes the class a *quotient* of the parts, hence what right exactness applies to.
* `GradedDeformation.piTensorRightEquiv_sum_lTensor_pderivValPiece`: the effect on the parts of a
  perturbation of the lifts is, after assembly, the graded Jacobian of that perturbation.
* `GradedDeformation.exists_perturbation_of_sum_relationComponent_eq`: two families of first-order
  parts with the same first-order class differ by the graded Jacobian of a perturbation.
* `GradedDeformation.exists_perturbation_of_firstOrderClass_eq`: the same for two deformations with
  equal first-order classes.
* `GradedDeformation.exists_relationLift_common_of_firstOrderClass_eq`: **two deformations with
  equal first-order classes have a common family of lifted relations**, after replacing the lifts
  of the generators in the first by a perturbation of them.

## Implementation notes

The core existence statement is proved for two arbitrary families of first-order parts rather than
for two deformations: nothing about a deformation enters it beyond the receptacles
`I ⊗[k] 𝒜 (e j)`, and keeping it free of the deformation data is what lets the `ι`-side and the
`σ`-side of the argument be the same lemma about `piTensorRightEquiv` twice.

The interchange `piTensorRightEquiv` needs `DecidableEq` on the index type, because it is built
from `Pi.single`. On the index set of the relations that instance is already present, being needed
to state the comparison with `W ⊗[k] V`; on the index set of the generators it is not, so the
existence statements take it from `classical` rather than carrying it as a hypothesis their
consumers would have to supply.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace GradedDeformation

universe w u v v₁ t t₂ x y

/-! ### Assembling a finite family of tensors into one -/

section Assembly

variable {k : Type w} [CommRing k]
  {N : Type u} [AddCommGroup N] [Module k N]
  {V : Type v} [AddCommGroup V] [Module k V]
  {κ : Type x} [Fintype κ] [DecidableEq κ]
  {M : κ → Type t} [∀ a, AddCommGroup (M a)] [∀ a, Module k (M a)]

/-- A finite family of tensors with a common left factor `N`, assembled into a single tensor of
the product with `N` read as `V`. This is `TensorProduct.piRight` backwards, followed by the
identification of the left factor with `V`; it is an equivalence because the index type is
finite. -/
noncomputable def piTensorRightEquiv (eV : N ≃ₗ[k] V) :
    (∀ a, N ⊗[k] M a) ≃ₗ[k] (∀ a, M a) ⊗[k] V :=
  (TensorProduct.piRight k k N M).symm ≪≫ₗ TensorProduct.comm k N (∀ a, M a) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl k (∀ a, M a)) eV

/-- The assembly of a family supported in one coordinate. -/
@[simp]
theorem piTensorRightEquiv_single (eV : N ≃ₗ[k] V) (a : κ) (n : N) (m : M a) :
    piTensorRightEquiv eV (Pi.single a (n ⊗ₜ[k] m)) = Pi.single a m ⊗ₜ[k] eV n := by
  simp [piTensorRightEquiv]

/-- The assembly of a family of pure tensors with a common left factor. -/
@[simp]
theorem piTensorRightEquiv_tmul (eV : N ≃ₗ[k] V) (n : N) (m : ∀ a, M a) :
    piTensorRightEquiv (M := M) eV (fun a ↦ n ⊗ₜ[k] m a) = m ⊗ₜ[k] eV n := by
  simp [piTensorRightEquiv]

/-- Applying a linear map to the assembly of a family equals summing over its coordinates. -/
private theorem sum_apply_piTensorRightEquiv_single {X : Type*} [AddCommGroup X] [Module k X]
    (eV : N ≃ₗ[k] V) (f : (∀ a, M a) ⊗[k] V →ₗ[k] X) (u : ∀ a, N ⊗[k] M a) :
    ∑ a, f (piTensorRightEquiv eV (Pi.single a (u a))) = f (piTensorRightEquiv eV u) := by
  rw [← map_sum, ← map_sum, Finset.univ_sum_single]

end Assembly

/-! ### The first-order class and the graded Jacobian through the assembly -/

section Bridge

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {V : Type t} [AddCommGroup V] [Module k V]
  {ι : Type x} [Fintype ι] [DecidableEq ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)

omit [DecidableEq ι] in
/-- The comparison of the receptacle of one relation with `W ⊗[k] V` is the assembly of the family
supported in that coordinate, read in the cokernel of the Jacobian. -/
theorem rTensor_mkQ_piTensorRightEquiv_single
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V) (j : σ)
    (z : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j))) :
    LinearMap.rTensor V (LinearMap.range pres.jacobian).mkQ
        (piTensorRightEquiv (M := fun j ↦ ↥(𝒜 (pres.relDegree j))) eV (Pi.single j z)) =
      relationComponent pres eV j z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => simp [relationComponent_tmul, LinearMap.coe_single]
  | add z z' hz hz' => rw [Pi.single_add, map_add, map_add, hz, hz', map_add]

omit [DecidableEq ι] in
/-- **The first-order class of a family of first-order parts is that family read in the cokernel of
the graded Jacobian.** The collected comparison with `W ⊗[k] V` of a family of elements of the
receptacles `I ⊗[k] 𝒜 (e j)` is the assembly of the family followed by the passage to the
cokernel.

This is what exhibits the class as a quotient of the parts, and hence what makes right exactness of
the tensor product applicable to the difference of two families with the same class. -/
theorem sum_relationComponent_eq_rTensor_mkQ
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (u : ∀ j, ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j))) :
    ∑ j, relationComponent pres eV j (u j) =
      LinearMap.rTensor V (LinearMap.range pres.jacobian).mkQ (piTensorRightEquiv eV u) := by
  rw [← sum_apply_piTensorRightEquiv_single]
  exact Finset.sum_congr rfl fun j _ ↦ (rTensor_mkQ_piTensorRightEquiv_single pres eV j (u j)).symm

omit [Fintype σ] [DecidableEq σ] in
/-- The `i`-th column of the graded Jacobian is multiplication by the value of `∂F_j/∂X_i`. -/
theorem jacobian_single_eq_pderivValPiece (j : σ) (i : ι) (y : ↥(𝒜 (pres.varDegree i))) :
    pres.jacobian (Pi.single i y) j = pderivValPiece pres j i y := by
  apply Subtype.ext
  rw [Algebra.WeightedHomogeneousPresentation.jacobian_apply_coe, coe_pderivValPiece,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i), Pi.single_eq_same]
  intro n _ hn
  rw [Pi.single_eq_of_ne hn, ZeroMemClass.coe_zero, zero_mul]

/-- The effect on the first-order parts of perturbing one generator is, after assembly, the graded
Jacobian of the perturbation placed in that coordinate. -/
theorem piTensorRightEquiv_lTensor_pderivValPiece
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V) (i : ι)
    (z : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i))) :
    piTensorRightEquiv (M := fun j ↦ ↥(𝒜 (pres.relDegree j))) eV
        (fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
          (pderivValPiece pres j i) z) =
      LinearMap.rTensor V pres.jacobian
        (piTensorRightEquiv (M := fun i ↦ ↥(𝒜 (pres.varDegree i))) eV (Pi.single i z)) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      have h0 : (fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
          (pderivValPiece pres j i) (0 : ↥(RingHom.ker (algebraMap A k)) ⊗[k]
            ↥(𝒜 (pres.varDegree i)))) = 0 := funext fun j ↦ map_zero _
      rw [h0, Pi.single_zero, map_zero, map_zero, map_zero]
  | tmul a y =>
      have hfun : (fun j ↦ pderivValPiece pres j i y) = pres.jacobian (Pi.single i y) :=
        funext fun j ↦ (jacobian_single_eq_pderivValPiece pres j i y).symm
      have hl : (fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
          (pderivValPiece pres j i) (a ⊗ₜ[k] y)) =
          fun j ↦ a ⊗ₜ[k] pderivValPiece pres j i y :=
        funext fun j ↦ LinearMap.lTensor_tmul _ _ _ _
      rw [hl, piTensorRightEquiv_tmul, piTensorRightEquiv_single, LinearMap.rTensor_tmul, hfun]
  | add z z' hz hz' =>
      have hadd : (fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
          (pderivValPiece pres j i) (z + z')) =
          (fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
            (pderivValPiece pres j i) z) +
            fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
              (pderivValPiece pres j i) z' := funext fun j ↦ map_add _ _ _
      rw [hadd, map_add, hz, hz', Pi.single_add, map_add, map_add]

/-- **The effect on the first-order parts of perturbing the lifts is the graded Jacobian.** The
change in the collected first-order parts caused by a perturbation of all the generators is, after
assembly, the graded Jacobian applied to the assembled perturbation.

Together with `GradedDeformation.sum_relationComponent_eq_rTensor_mkQ` this says that the
first-order class is the assembled parts modulo the perturbations, which is the statement right
exactness turns into an existence. -/
theorem piTensorRightEquiv_sum_lTensor_pderivValPiece
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (ξ : ∀ i, ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i))) :
    piTensorRightEquiv (M := fun j ↦ ↥(𝒜 (pres.relDegree j))) eV
        (fun j ↦ ∑ i, LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
          (pderivValPiece pres j i) (ξ i)) =
      LinearMap.rTensor V pres.jacobian
        (piTensorRightEquiv (M := fun i ↦ ↥(𝒜 (pres.varDegree i))) eV ξ) := by
  have hsplit : (fun j ↦ ∑ i, LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
        (pderivValPiece pres j i) (ξ i)) =
      ∑ i, fun j ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
        (pderivValPiece pres j i) (ξ i) :=
    funext fun j ↦ (Finset.sum_apply j Finset.univ
      (fun i (j : σ) ↦ LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
        (pderivValPiece pres j i) (ξ i))).symm
  rw [← sum_apply_piTensorRightEquiv_single, hsplit, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ piTensorRightEquiv_lTensor_pderivValPiece pres eV i (ξ i)

end Bridge

/-! ### Recovering the perturbation -/

section Perturbation

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {V : Type t} [AddCommGroup V] [Module k V]
  {ι : Type x} [Fintype ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)

/-- **Two families of first-order parts with the same first-order class differ by the graded
Jacobian of a perturbation of the generators.**

Their difference is killed by the passage to the cokernel of the Jacobian tensored with `V`, so by
right exactness of the tensor product it comes from `range jacobian ⊗[k] V`; the Jacobian is
surjective onto its range, so it comes from `(∀ i, 𝒜 (d i)) ⊗[k] V`; and the interchange with the
finite product turns that preimage into one perturbation for each generator. No flatness of `V` is
used: only right exactness. -/
theorem exists_perturbation_of_sum_relationComponent_eq
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (u u' : ∀ j, ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j)))
    (h : ∑ j, relationComponent pres eV j (u j) = ∑ j, relationComponent pres eV j (u' j)) :
    ∃ ξ : ∀ i, ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i)), ∀ j,
      u' j = u j + ∑ i, LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
        (pderivValPiece pres j i) (ξ i) := by
  classical
  have hker : piTensorRightEquiv (M := fun j ↦ ↥(𝒜 (pres.relDegree j))) eV u' -
      piTensorRightEquiv (M := fun j ↦ ↥(𝒜 (pres.relDegree j))) eV u ∈
      LinearMap.ker (LinearMap.rTensor V (LinearMap.range pres.jacobian).mkQ) := by
    rw [LinearMap.mem_ker, map_sub, ← sum_relationComponent_eq_rTensor_mkQ pres eV u',
      ← sum_relationComponent_eq_rTensor_mkQ pres eV u, h, sub_self]
  rw [rTensor_mkQ] at hker
  obtain ⟨w, hw⟩ := hker
  obtain ⟨c, hc⟩ := LinearMap.rTensor_surjective V
    (LinearMap.surjective_rangeRestrict pres.jacobian) w
  have hcomp : LinearMap.rTensor V (LinearMap.range pres.jacobian).subtype w =
      LinearMap.rTensor V pres.jacobian c := by
    rw [← hc, ← LinearMap.rTensor_comp_apply, LinearMap.subtype_comp_rangeRestrict]
  refine ⟨(piTensorRightEquiv (M := fun i ↦ ↥(𝒜 (pres.varDegree i))) eV).symm c, fun j ↦ ?_⟩
  have hkey : (fun j ↦ ∑ i, LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
      (pderivValPiece pres j i)
        ((piTensorRightEquiv (M := fun i ↦ ↥(𝒜 (pres.varDegree i))) eV).symm c i)) = u' - u := by
    apply (piTensorRightEquiv (M := fun j ↦ ↥(𝒜 (pres.relDegree j))) eV).injective
    rwa [piTensorRightEquiv_sum_lTensor_pderivValPiece, LinearEquiv.apply_symm_apply, map_sub,
      ← hcomp]
  exact sub_eq_iff_eq_add'.mp (congrFun hkey j).symm

end Perturbation

/-! ### The common family of lifted relations -/

section Pair

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬] [∀ d, Module.Flat A ↥(𝒬 d)]
  {Q' : Type t₂} [CommRing Q'] [Algebra A Q'] [Algebra k Q'] [IsScalarTower k A Q']
  {𝒬' : ℕ → Submodule A Q'} [GradedAlgebra 𝒬'] [∀ d, Module.Flat A ↥(𝒬' d)]
  {V : Type v₁} [AddCommGroup V] [Module k V]
  {red : Q →+* P} {red' : Q' →+* P}
  {ι : Type x} [Fintype ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ) {yl : ι → Q} {yl' : ι → Q'}

/-- **An equality of first-order classes is realised by a perturbation of the lifts.** If two
deformations of `P` over the same square-zero base have the same first-order class at the chosen
lifts of the generators, then the first-order parts of the relations in the second are those in
the first corrected by the graded Jacobian of a perturbation of the lifts.

This is `GradedDeformation.exists_perturbation_of_sum_relationComponent_eq` with the two families
of first-order parts taken to be those of the two deformations, using that the first-order class
is the collected comparison of the parts. -/
theorem exists_perturbation_of_firstOrderClass_eq
    {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
    {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}
    {hsmul' : ∀ (a : A) (q : Q'), red' (a • q) = algebraMap A k a • red' q}
    {hmem' : ∀ (d : ℕ) (q : Q'), q ∈ 𝒬' d → red' q ∈ 𝒜 d}
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hbc' : ∀ d, IsBaseChange k (gradedPiece red' hsmul' hmem' d))
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, yl' i ∈ 𝒬' (pres.varDegree i)) (hy' : ∀ i, red' (yl' i) = pres.val i)
    (hcls : firstOrderClass pres hret hsq hbc eV hyd hy =
      firstOrderClass pres hret hsq hbc' eV hyd' hy') :
    ∃ ξ : ∀ i, ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i)), ∀ j,
      relationFirstOrderPart pres hret hsq hbc' hyd' hy' j =
        relationFirstOrderPart pres hret hsq hbc hyd hy j +
          ∑ i, LinearMap.lTensor ↥(RingHom.ker (algebraMap A k))
            (pderivValPiece pres j i) (ξ i) :=
  exists_perturbation_of_sum_relationComponent_eq pres eV _ _ (by
    rw [← firstOrderClass_eq_sum pres hret hsq hbc eV hyd hy,
      ← firstOrderClass_eq_sum pres hret hsq hbc' eV hyd' hy']
    exact hcls)

/-- **Two deformations with equal first-order classes have a common family of lifted relations.**
The lifts of the generators in the first deformation are replaced by the perturbation of them which
makes the first-order parts of the relations agree with those in the second; the common family of
weighted-homogeneous lifts of the relations then exists, vanishing at the new lifts in the first
deformation and at the given lifts in the second.

This is the hypothesis of
`Deformation.Examples.ProjectiveGradedAlgebra.nonempty_fiber_iso_of_common_gradedPresentation`: the
two deformations are then quotients of one graded algebra `StacksDraft.liftedAlgebra R` compatibly
with their identifications of the special fibre, hence isomorphic over the base. -/
theorem exists_relationLift_common_of_firstOrderClass_eq
    (hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q)
    (hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d)
    (hsmul' : ∀ (a : A) (q : Q'), red' (a • q) = algebraMap A k a • red' q)
    (hmem' : ∀ (d : ℕ) (q : Q'), q ∈ 𝒬' d → red' q ∈ 𝒜 d)
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hbc' : ∀ d, IsBaseChange k (gradedPiece red' hsmul' hmem' d))
    {redₗ : Q →ₗ[A] P} (hredₗ : ∀ q : Q, redₗ q = red q) (hbcQ : IsBaseChange k redₗ)
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, yl' i ∈ 𝒬' (pres.varDegree i)) (hy' : ∀ i, red' (yl' i) = pres.val i)
    (hcls : firstOrderClass pres hret hsq hbc eV hyd hy =
      firstOrderClass pres hret hsq hbc' eV hyd' hy') :
    ∃ (z : ι → Q) (R : σ → MvPolynomial ι A),
      (∀ i, z i ∈ 𝒬 (pres.varDegree i)) ∧ (∀ i, red (z i) = pres.val i) ∧
        (∀ j, (R j).IsWeightedHomogeneous pres.varDegree (pres.relDegree j)) ∧
          (∀ j, MvPolynomial.map (algebraMap A k) (R j) = pres.relation j) ∧
            (∀ j, aeval z (R j) = 0) ∧ ∀ j, aeval yl' (R j) = 0 := by
  obtain ⟨ξ, hξ⟩ := exists_perturbation_of_firstOrderClass_eq pres hret hsq hbc hbc' eV hyd hy
    hyd' hy' hcls
  obtain ⟨z, hzd, hz, hzsub⟩ := exists_lifts_sub_kerElement pres hsmul hmem hret hsq hbc hyd hy
    fun i ↦ -ξ i
  have hparts : ∀ j, relationFirstOrderPart pres hret hsq hbc hzd hz j =
      relationFirstOrderPart pres hret hsq hbc' hyd' hy' j := fun j ↦ by
    rw [relationFirstOrderPart_eq_sub_sum pres hret hsq hbc hredₗ hbcQ hyd hy hzd hz
        (fun i ↦ -ξ i) hzsub j, hξ j]
    simp only [map_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  obtain ⟨R, hRhom, hRmap, hRz, hRy'⟩ := exists_relationLift_common pres hsmul hmem hsmul' hmem'
    hret hsq hbc hbc' hzd hz hyd' hy' hparts
  exact ⟨z, R, hzd, hz, hRhom, hRmap, hRz, hRy'⟩

end Pair

end GradedDeformation

end
