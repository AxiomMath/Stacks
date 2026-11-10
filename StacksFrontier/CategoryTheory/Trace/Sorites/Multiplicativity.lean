module

public import StacksFrontier.CategoryTheory.Trace.Preliminaries.QuotientModule
public import StacksFrontier.CategoryTheory.Trace.Sorites.DiagonalTensorEndomorphism
public import StacksFrontier.CategoryTheory.Trace.Sorites.TraceCoordinates
public import StacksCore.Tactic.StacksAttribute

/-!
# Multiplicativity of the group trace

The group trace of the tensor product of two equivariant endomorphisms is the product of
the group trace of the first endomorphism and the ordinary trace of the second.

## Main definitions

* `diagonalTensorGroupTrace` is the group trace of the tensor product of two equivariant
  endomorphisms.
* `commutativeAdditiveCommutatorQuotientEval` evaluates the additive commutator quotient of
  a commutative ring in the ring itself.

## Main results

* `groupTrace_diagonalTensorEndomorphism`: the group trace of the tensor product `u ⊗ v` of
  equivariant endomorphisms is the image of the group trace of `u` in `A` acting on the ordinary
  trace of `v`.

## References

* [Stacks Project, Tag 03UA](https://stacks.math.columbia.edu/tag/03UA)
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra

open CategoryTheory.FilteredDerived

open Stacks.Trace.Representation

universe uA uΛ uG uP uM

namespace Stacks.Trace

private noncomputable def weightedCoeffMap
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (c : G → Λ) : A[G] →ₗ[A] Λ[G] :=
  (Finsupp.linearCombination A (fun g : G ↦ (MonoidAlgebra.single g (c g) : Λ[G]))).comp
    (MonoidAlgebra.coeffLinearEquiv A (S := A) (M := G)).toLinearMap

private lemma weightedCoeffMap_sum_coeff
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (c : G → Λ) (r : A[G]) :
    weightedCoeffMap A Λ G c r =
      r.coeff.sum (fun g a => (MonoidAlgebra.single g (algebraMap A Λ a * c g) : Λ[G])) := by
  classical
  simp [weightedCoeffMap, Finsupp.linearCombination_apply, Algebra.smul_def]

private lemma weightedCoeffMap_single
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (c : G → Λ) (g : G) (a : A) :
    weightedCoeffMap A Λ G c (MonoidAlgebra.single g a) =
      MonoidAlgebra.single g (algebraMap A Λ a * c g) := by
  simp [weightedCoeffMap, Algebra.smul_def]

private lemma weightedCoeffMap_add
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (c d : G → Λ) (r : A[G]) :
    weightedCoeffMap A Λ G (c + d) r =
      weightedCoeffMap A Λ G c r + weightedCoeffMap A Λ G d r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single g a => simp [weightedCoeffMap_single, mul_add, MonoidAlgebra.single_add]

private lemma weightedCoeffMap_smul
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (a : Λ) (c : G → Λ) (r : A[G]) :
    weightedCoeffMap A Λ G (a • c) r = a • weightedCoeffMap A Λ G c r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | single g b =>
      rw [weightedCoeffMap_single, weightedCoeffMap_single, Pi.smul_apply, smul_eq_mul,
        MonoidAlgebra.smul_single', ← mul_assoc, Algebra.commutes, mul_assoc]

private lemma weightedCoeffMap_translate
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (g : G) (c : G → Λ) (r : A[G]) :
    weightedCoeffMap A Λ G (fun h => c (g⁻¹ * h))
        (MonoidAlgebra.single g (1 : A) * r) =
      MonoidAlgebra.single g (1 : Λ) * weightedCoeffMap A Λ G c r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | single h a => simp [MonoidAlgebra.single_mul_single, weightedCoeffMap_single]

private noncomputable def diagonalTensorCoordinate
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M]
    [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (σ : _root_.Representation Λ G M)
    (iP : P →ₗ[A[G]] (Fin n → A[G]))
    (iM : M →ₗ[Λ] (Fin m → Λ)) (i : Fin n) (j : Fin m) :
    TensorProduct A M P →ₗ[Λ] Λ[G] := by
  let pr : P →ₗ[A] A[G] :=
    (LinearMap.proj i).comp (iP.restrictScalars A)
  let ψ : M →ₗ[Λ] Λ := (LinearMap.proj j).comp iM
  let F : M →ₗ[Λ] (P →ₗ[A] Λ[G]) := {
    toFun := fun x ↦ (weightedCoeffMap A Λ G
      (fun g ↦ ψ (σ g⁻¹ x))).comp pr
    map_add' := by
      intro x y
      refine LinearMap.ext fun p ↦ ?_
      have hc : (fun g ↦ ψ (σ g⁻¹ (x + y))) =
          (fun g ↦ ψ (σ g⁻¹ x)) + (fun g ↦ ψ (σ g⁻¹ y)) := by
        funext g
        simp
      change weightedCoeffMap A Λ G _ (pr p) = _
      rw [hc, weightedCoeffMap_add]
      simp [LinearMap.comp_apply]
    map_smul' := by
      intro a x
      refine LinearMap.ext fun p ↦ ?_
      have hc : (fun g ↦ ψ (σ g⁻¹ (a • x))) =
          a • (fun g ↦ ψ (σ g⁻¹ x)) := by
        funext g
        simp [Pi.smul_apply]
      change weightedCoeffMap A Λ G _ (pr p) = _
      rw [hc, weightedCoeffMap_smul]
      simp [LinearMap.comp_apply] }
  exact TensorProduct.AlgebraTensorModule.lift F

private noncomputable def leftRegularRepresentation
    (Λ G : Type*) [Ring Λ] [Group G] : _root_.Representation Λ G Λ[G] where
  toFun g := {
    toFun := fun x ↦ (MonoidAlgebra.single g (1 : Λ) : Λ[G]) * x
    map_add' := by intros; exact mul_add _ _ _
    map_smul' := by
      intro a x
      ext h
      simp [MonoidAlgebra.coeff_single_mul_apply]
    }
  map_one' := by
    ext x
    simp [MonoidAlgebra.single_mul_single]
  map_mul' g h := by
    refine LinearMap.ext fun x ↦ ?_
    change (MonoidAlgebra.single (g * h) (1 : Λ) : Λ[G]) * x =
      (MonoidAlgebra.single g (1 : Λ) : Λ[G]) *
        ((MonoidAlgebra.single h (1 : Λ) : Λ[G]) * x)
    rw [← mul_assoc, MonoidAlgebra.single_mul_single]
    simp

private lemma leftRegular_smul_mul
    (Λ G : Type*) [Ring Λ] [Group G]
    (r x : Λ[G]) :
    (r • (show Representation.asModuleNC (leftRegularRepresentation Λ G) from x) :
      Representation.asModuleNC (leftRegularRepresentation Λ G)) = r * x := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      change (MonoidAlgebra.single g (1 : Λ) : Λ[G]) •
        (show Representation.asModuleNC (leftRegularRepresentation Λ G) from x) = _
      rw [single_smul_asModuleNC]
      simp only [one_smul, leftRegularRepresentation]
      rfl
  | add r s hr hs =>
      rw [add_smul, add_mul, hr, hs]
      rfl
  | smul a r hr =>
      have hs : ∀ y : Λ[G], MonoidAlgebra.single 1 a * y = a • y := by
        intro y
        ext g
        simp [MonoidAlgebra.coeff_single_mul_apply]
      change (a • r) • (show Representation.asModuleNC (leftRegularRepresentation Λ G) from x) = _
      rw [← hs r, mul_smul, single_smul_asModuleNC, map_one]
      rw [mul_assoc, hr, hs]
      rfl

private noncomputable def leftRegularAsModuleLinear
    (Λ G : Type*) [Ring Λ] [Group G] :
    Representation.asModuleNC (leftRegularRepresentation Λ G) →ₗ[Λ[G]] Λ[G] := {
  toFun := id
  map_add' := by intros; rfl
  map_smul' := leftRegular_smul_mul Λ G }

private lemma diagonalTensorCoordinate_equivariant
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (iP : P →ₗ[A[G]] (Fin n → A[G]))
    (iM : M →ₗ[Λ] (Fin m → Λ))
    (hρ : ∀ g p, (MonoidAlgebra.single g (1 : A) : A[G]) • p = ρ g p)
    (i : Fin n) (j : Fin m)
    (g : G) (m0 : M) (p0 : P) :
    diagonalTensorCoordinate A Λ G P M σ iP iM i j
        (σ g m0 ⊗ₜ[A] ρ g p0) =
      (MonoidAlgebra.single g (1 : Λ) : Λ[G]) *
        diagonalTensorCoordinate A Λ G P M σ iP iM i j
          (m0 ⊗ₜ[A] p0) := by
  let pr : P →ₗ[A] A[G] :=
    (LinearMap.proj i).comp (iP.restrictScalars A)
  let ψ : M →ₗ[Λ] Λ := (LinearMap.proj j).comp iM
  have hpr : pr (ρ g p0) = MonoidAlgebra.single g (1 : A) * pr p0 := by
    rw [← hρ g p0]
    simp [pr]
  have hc : (fun h ↦ ψ (σ h⁻¹ (σ g m0))) =
      (fun h ↦ ψ (σ (g⁻¹ * h)⁻¹ m0)) := by
    funext h
    simp [map_mul, mul_inv_rev]
  unfold diagonalTensorCoordinate
  rw [TensorProduct.AlgebraTensorModule.lift_tmul,
    TensorProduct.AlgebraTensorModule.lift_tmul]
  change weightedCoeffMap A Λ G _ (pr (ρ g p0)) =
    (MonoidAlgebra.single g (1 : Λ) : Λ[G]) *
      weightedCoeffMap A Λ G _ (pr p0)
  rw [hpr, hc]
  exact weightedCoeffMap_translate A Λ G g
    (fun k ↦ ψ (σ k⁻¹ m0)) (pr p0)

private noncomputable def diagonalTensorCoordinateGroupLinear
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (iP : P →ₗ[A[G]] (Fin n → A[G]))
    (iM : M →ₗ[Λ] (Fin m → Λ))
    (hρ : ∀ g p, (MonoidAlgebra.single g (1 : A) : A[G]) • p = ρ g p)
    (i : Fin n) (j : Fin m) :
    Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]]
      Representation.asModuleNC (leftRegularRepresentation Λ G) := {
  diagonalTensorCoordinate A Λ G P M σ iP iM i j with
  map_smul' := by
    intro r z
    have hequiv : ∀ g z,
        diagonalTensorCoordinate A Λ G P M σ iP iM i j
            ((Representation.tprodAlgebraReversed ρ σ) g z) =
          leftRegularRepresentation Λ G g
            (diagonalTensorCoordinate A Λ G P M σ iP iM i j z) := by
      intro g z
      induction z using TensorProduct.inductionOn with
      | tmul m p =>
          exact diagonalTensorCoordinate_equivariant A Λ G P M ρ σ iP iM hρ i j g m p
      | add x y hx hy => simp only [map_add, hx, hy]
    exact map_smul_asModuleNC (Representation.tprodAlgebraReversed ρ σ)
      (leftRegularRepresentation Λ G)
      (diagonalTensorCoordinate A Λ G P M σ iP iM i j) hequiv r z }

private lemma tensor_A_smul_groupAlgebra
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (a : A) (r : Λ[G])
    (z : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ)) :
    (a • r) • z = (algebraMap A Λ a) • (r • z) := by
  have ha : (a • r : Λ[G]) =
      (MonoidAlgebra.single 1 (algebraMap A Λ a) : Λ[G]) * r := by
    ext g
    simp [Algebra.smul_def]
  rw [ha, mul_smul, single_smul_asModuleNC, map_one]
  rfl

private lemma reversedTensor_tmul_add
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (m : M) (p q : P) :
    (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
      m ⊗ₜ[A] (p + q)) =
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        m ⊗ₜ[A] p) +
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        m ⊗ₜ[A] q) :=
  TensorProduct.tmul_add m p q

private lemma reversedTensor_scalar_smul_tmul
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (a : Λ) (m : M) (p : P) :
    a • (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
      m ⊗ₜ[A] p) =
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        (a • m) ⊗ₜ[A] p) := by
  change a • (m ⊗ₜ[A] p) = (a • m) ⊗ₜ[A] p
  exact TensorProduct.smul_tmul' a m p

private lemma reversedTensor_smul_balance
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (a : A) (m : M) (p : P) :
    (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
      (a • m) ⊗ₜ[A] p) =
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        m ⊗ₜ[A] (a • p)) :=
  TensorProduct.smul_tmul a m p

private noncomputable def diagonalTensorFreeProjection
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (pP : (Fin n → A[G]) →ₗ[A[G]] P) (pM : (Fin m → Λ) →ₗ[Λ] M) :
    (Fin n × Fin m → Λ[G]) →ₗ[Λ[G]]
      Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) := by
  let w : Fin n × Fin m →
      Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) := fun ij ↦
    (pM (standardBasisVector Λ (Fin m) ij.2)) ⊗ₜ[A]
      (pP (standardBasisVector A[G] (Fin n) ij.1))
  exact {
    toFun := fun x ↦ ∑ ij, x ij • w ij
    map_add' := by
      intro x y
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      change (∑ ij, (a * x ij) • w ij) = a • (∑ ij, x ij • w ij)
      simp only [mul_smul, Finset.smul_sum] }

private noncomputable def diagonalTensorFreeInclusion
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (iP : P →ₗ[A[G]] (Fin n → A[G])) (iM : M →ₗ[Λ] (Fin m → Λ))
    (hρ : ∀ g p, (MonoidAlgebra.single g (1 : A) : A[G]) • p = ρ g p) :
    Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) →ₗ[Λ[G]]
      (Fin n × Fin m → Λ[G]) := {
  toFun := fun z ij ↦
    let f := (leftRegularAsModuleLinear Λ G).comp
      (diagonalTensorCoordinateGroupLinear A Λ G P M ρ σ iP iM hρ ij.1 ij.2)
    f z
  map_add' := by
    intro x y
    funext ij
    exact LinearMap.map_add _ x y
  map_smul' := by
    intro a x
    funext ij
    let f := (leftRegularAsModuleLinear Λ G).comp
      (diagonalTensorCoordinateGroupLinear A Λ G P M ρ σ iP iM hρ ij.1 ij.2)
    simpa only [Pi.smul_apply, RingHom.id_apply] using f.map_smul a x }

private lemma diagonalTensorFreeCoordinateSum
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (pM : (Fin m → Λ) →ₗ[Λ] M) (iM : M →ₗ[Λ] (Fin m → Λ))
    (hm : pM.comp iM = LinearMap.id)
    (hρ : ∀ g p, (MonoidAlgebra.single g (1 : A) : A[G]) • p = ρ g p)
    (m₀ : M) (q : P) (r : A[G]) :
    (∑ j, weightedCoeffMap A Λ G (fun g => iM (σ g⁻¹ m₀) j) r •
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        (pM (standardBasisVector Λ (Fin m) j)) ⊗ₜ[A] q)) =
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        m₀ ⊗ₜ[A] (r • q)) := by
  classical
  induction r using MonoidAlgebra.induction_on with
  | of g =>
      simp only [MonoidAlgebra.of_apply, weightedCoeffMap_single, map_one, one_mul]
      have hsum : ∑ j, iM (σ g⁻¹ m₀) j • σ g (pM (standardBasisVector Λ (Fin m) j)) = m₀ := by
        simp_rw [← (σ g).map_smul, ← map_sum, ← splitExpansion Λ M pM iM hm (σ g⁻¹ m₀)]
        simp
      simp_rw [single_smul_reversed_tmul]
      change ∑ j, (iM (σ g⁻¹ m₀) j • σ g (pM (standardBasisVector Λ (Fin m) j))) ⊗ₜ[A] ρ g q =
        m₀ ⊗ₜ[A] ((MonoidAlgebra.single g (1 : A) : A[G]) • q)
      rw [← TensorProduct.sum_tmul, hsum, hρ]
  | add r s hr hs =>
      simp_rw [map_add]
      refine (Finset.sum_congr rfl fun j _ ↦ add_smul _ _ _).trans ?_
      rw [Finset.sum_add_distrib, hr, hs, add_smul]
      exact (TensorProduct.tmul_add (R := A) m₀ (r • q) (s • q)).symm
  | smul a r hr =>
      simp_rw [map_smul]
      refine (Finset.sum_congr rfl fun j _ ↦
        tensor_A_smul_groupAlgebra A Λ G P M ρ σ a _ _).trans ?_
      rw [← Finset.smul_sum, hr]
      change algebraMap A Λ a • (m₀ ⊗ₜ[A] (r • q)) = m₀ ⊗ₜ[A] ((a • r) • q)
      rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, smul_assoc]

private lemma diagonalTensorFreeInclusion_apply_tmul
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (iP : P →ₗ[A[G]] (Fin n → A[G])) (iM : M →ₗ[Λ] (Fin m → Λ))
    (hρ : ∀ g p, (MonoidAlgebra.single g (1 : A) : A[G]) • p = ρ g p)
    (i : Fin n) (j : Fin m) (m₀ : M) (p₀ : P) :
    (diagonalTensorFreeInclusion A Λ G P M ρ σ iP iM hρ
      (m₀ ⊗ₜ[A] p₀)) (i, j) =
      weightedCoeffMap A Λ G (fun g => iM (σ g⁻¹ m₀) j) ((iP p₀) i) := by
  change diagonalTensorCoordinateGroupLinear A Λ G P M ρ σ iP iM hρ i j
      (m₀ ⊗ₜ[A] p₀) = _
  change diagonalTensorCoordinate A Λ G P M σ iP iM i j
      (m₀ ⊗ₜ[A] p₀) = _
  simp [diagonalTensorCoordinate, LinearMap.comp_apply]

private lemma diagonalTensorFreeProjection_comp_inclusion
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (pP : (Fin n → A[G]) →ₗ[A[G]] P) (iP : P →ₗ[A[G]] (Fin n → A[G]))
    (hp : pP.comp iP = LinearMap.id)
    (pM : (Fin m → Λ) →ₗ[Λ] M) (iM : M →ₗ[Λ] (Fin m → Λ))
    (hm : pM.comp iM = LinearMap.id)
    (hρ : ∀ g p, (MonoidAlgebra.single g (1 : A) : A[G]) • p = ρ g p) :
    (diagonalTensorFreeProjection A Λ G P M ρ σ pP pM).comp
      (diagonalTensorFreeInclusion A Λ G P M ρ σ iP iM hρ) = LinearMap.id := by
  classical
  let pT := diagonalTensorFreeProjection A Λ G P M ρ σ pP pM
  let iT := diagonalTensorFreeInclusion A Λ G P M ρ σ iP iM hρ
  apply LinearMap.ext
  intro z
  change pT (iT z) = z
  induction z using TensorProduct.inductionOn with
  | tmul m0 p0 =>
      change (∑ ij, (diagonalTensorFreeInclusion A Λ G P M ρ σ iP iM hρ
          (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
            m0 ⊗ₜ[A] p0)) ij •
          (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
            (pM (standardBasisVector Λ (Fin m) ij.2)) ⊗ₜ[A]
              (pP (standardBasisVector A[G] (Fin n) ij.1)))) = _
      rw [Fintype.sum_prod_type]
      refine (Finset.sum_congr rfl fun i _ ↦
        diagonalTensorFreeCoordinateSum A Λ G P M ρ σ pM iM hm hρ m0
          (pP (standardBasisVector A[G] (Fin n) i)) ((iP p0) i)).trans ?_
      change (∑ i, m0 ⊗ₜ[A] ((iP p0) i • pP (standardBasisVector A[G] (Fin n) i))) = m0 ⊗ₜ[A] p0
      rw [← TensorProduct.tmul_sum, ← splitExpansion A[G] P pP iP hp p0]
  | add x y hx hy =>
      let x' : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) := x
      let y' : Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) := y
      change pT (iT (x' + y')) = x' + y'
      rw [iT.map_add, pT.map_add, hx, hy]

private lemma diagonalTensorFreeProjection_standardBasis
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    {n m : ℕ} (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (pP : (Fin n → A[G]) →ₗ[A[G]] P) (pM : (Fin m → Λ) →ₗ[Λ] M)
    (i : Fin n) (j : Fin m) :
    diagonalTensorFreeProjection A Λ G P M ρ σ pP pM
      (standardBasisVector Λ[G] (Fin n × Fin m) (i, j)) =
      (show Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) from
        pM (standardBasisVector Λ (Fin m) j) ⊗ₜ[A]
    pP (standardBasisVector A[G] (Fin n) i)) := by
  classical
  let w : Fin n × Fin m →
      Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ) := fun ij ↦
    (pM (standardBasisVector Λ (Fin m) ij.2)) ⊗ₜ[A]
      (pP (standardBasisVector A[G] (Fin n) ij.1))
  change (∑ ij : Fin n × Fin m,
      (standardBasisVector Λ[G] (Fin n × Fin m) (i, j)) ij • w ij) = w (i, j)
  simp [standardBasisVector]

private lemma weightedCoeffMap_coeff_one
    (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    (c : G → Λ) (r : A[G]) :
    (weightedCoeffMap A Λ G c r).coeff 1 =
      algebraMap A Λ (r.coeff 1) * c 1 := by
  classical
  rw [weightedCoeffMap_sum_coeff]
  suffices h : (∑ g ∈ r.coeff.support,
      (Finsupp.single g (algebraMap A Λ (r.coeff g) * c g) : G →₀ Λ) 1) =
      algebraMap A Λ (r.coeff 1) * c 1 by
    simpa [Finsupp.sum] using h
  rw [Finset.sum_eq_single 1]
  · simp
  · intro g hg hne
    simp [hne]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

private lemma diagonalTensorEndomorphism_conj_apply_tmul
    (A Λ G P M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (u : Module.End A[G] (Representation.asModuleNC ρ))
    (v : Module.End Λ[G] (Representation.asModuleNC σ))
    (m : M) (p : P) :
    ((Representation.tprodAlgebraCommModuleEquiv ρ σ).toLinearMap.comp
    ((diagonalTensorEndomorphism ρ σ u v).1.comp
      (Representation.tprodAlgebraCommModuleEquiv ρ σ).symm.toLinearMap))
        (m ⊗ₜ[A] p) =
      (show M from v (show Representation.asModuleNC σ from m)) ⊗ₜ[A]
        (show P from u (show Representation.asModuleNC ρ from p)) := by
  let e := Representation.tprodAlgebraCommModuleEquiv ρ σ
  have hs : e.symm (m ⊗ₜ[A] p) = p ⊗ₜ[A] m := by
    apply e.injective
    rw [Representation.tprodAlgebraCommModuleEquiv_apply_tmul]
    exact e.apply_symm_apply (m ⊗ₜ[A] p)
  change e ((diagonalTensorEndomorphism ρ σ u v).1 (e.symm (m ⊗ₜ[A] p))) = _
  rw [hs, (diagonalTensorEndomorphism ρ σ u v).2 p m]
  exact Representation.tprodAlgebraCommModuleEquiv_apply_tmul ρ σ (u p) (v m)

/-- Evaluation of the additive commutator quotient of a commutative ring in the ring
itself. -/
def commutativeAdditiveCommutatorQuotientEval
    (A : Type*) [CommRing A] : AdditiveCommutatorQuotient A →+ A :=
  QuotientAddGroup.lift (additiveCommutatorSubgroup A) (AddMonoidHom.id A) (by
    intro x hx
    change x = 0
    have hbot : additiveCommutatorSubgroup A = ⊥ := by
      rw [additiveCommutatorSubgroup, eq_bot_iff, AddSubgroup.closure_le]
      rintro x ⟨a, b, rfl⟩
      simp [mul_comm]
    rwa [hbot] at hx)

/-- The group trace of the tensor product of two equivariant endomorphisms, for the diagonal
action of `G` on the tensor product. -/
def diagonalTensorGroupTrace
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    [Module.Finite A[G] (asModuleNC ρ)] [Module.Projective A[G] (asModuleNC ρ)]
    [Module.Finite Λ M] [Module.Projective Λ M]
    (u : Module.End A[G] (asModuleNC ρ))
    (v : Module.End Λ[G] (asModuleNC σ)) :
    AdditiveCommutatorQuotient Λ := by
  letI := diagonalAction_module_finite ρ σ
  letI := diagonalAction_module_projective ρ σ
  exact groupTrace Λ G (asModuleNC (tprodAlgebra ρ σ))
    (diagonalTensorEndomorphism ρ σ u v).1

/-- The group trace is multiplicative for the diagonal tensor product action. -/
@[stacks 03UA,
  sga "4½ Rapport 5.8",
  sga "5 IIIB 5.12" "special case",
  sga "6 I 8.6" "Punctual (affine) case"]
lemma groupTrace_diagonalTensorEndomorphism
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    [Module.Finite A[G] (asModuleNC ρ)] [Module.Projective A[G] (asModuleNC ρ)]
    [Module.Finite Λ M] [Module.Projective Λ M]
    (u : Module.End A[G] (asModuleNC ρ))
    (v : Module.End Λ[G] (asModuleNC σ)) :
    diagonalTensorGroupTrace ρ σ u v =
      commutativeAdditiveCommutatorQuotientEval A
          (groupTrace A G (asModuleNC ρ) u) •
      projectiveModuleTrace Λ M
          (groupAlgebraEnd_restrictScalars σ v) := by
  classical
  let : Module A[G] P :=
    Representation.asModuleNC.moduleMonoidAlgebra ρ
  let : Module.Finite A[G] P := by
    change Module.Finite A[G] (Representation.asModuleNC ρ)
    infer_instance
  let : Module.Projective A[G] P := by
    change Module.Projective A[G] (Representation.asModuleNC ρ)
    infer_instance
  let : IsScalarTower A A[G] P :=
    IsScalarTower.of_algebraMap_smul (fun a p => by
      change (algebraMap A A[G] a) • (show Representation.asModuleNC ρ from p) =
        a • (show Representation.asModuleNC ρ from p)
      rw [show algebraMap A A[G] a = (MonoidAlgebra.single 1 (a : A) : A[G]) by simp,
        single_smul_asModuleNC, map_one]
      rfl)
  let := diagonalAction_module_finite ρ σ
  let := diagonalAction_module_projective ρ σ
  let hP := Module.Finite.exists_comp_eq_id_of_projective A[G] P
  let n := hP.choose
  let pP : (Fin n → A[G]) →ₗ[A[G]] P :=
    hP.choose_spec.choose
  let iP : P →ₗ[A[G]] (Fin n → A[G]) :=
    hP.choose_spec.choose_spec.choose
  have hp : pP.comp iP = LinearMap.id :=
    hP.choose_spec.choose_spec.choose_spec.2.2
  let hM := Module.Finite.exists_comp_eq_id_of_projective Λ M
  let m := hM.choose
  let pM : (Fin m → Λ) →ₗ[Λ] M := hM.choose_spec.choose
  let iM : M →ₗ[Λ] (Fin m → Λ) := hM.choose_spec.choose_spec.choose
  have hm : pM.comp iM = LinearMap.id :=
    hM.choose_spec.choose_spec.choose_spec.2.2
  have hρ (g : G) (p : P) :
      (MonoidAlgebra.single g (1 : A) : A[G]) •
          p = ρ g p := by
    change (MonoidAlgebra.single g (1 : A) : A[G]) •
        (show Representation.asModuleNC ρ from p) = ρ g p
    rw [single_smul_asModuleNC, one_smul]
  let e := Representation.tprodAlgebraCommModuleEquiv ρ σ
  let pT := diagonalTensorFreeProjection A Λ G P M ρ σ pP pM
  let iT := diagonalTensorFreeInclusion A Λ G P M ρ σ iP iM hρ
  let p : (Fin n × Fin m → Λ[G]) →ₗ[Λ[G]]
      Representation.asModuleNC (Representation.tprodAlgebra ρ σ) :=
    e.symm.toLinearMap.comp pT
  let i : Representation.asModuleNC (Representation.tprodAlgebra ρ σ) →ₗ[Λ[G]]
      (Fin n × Fin m → Λ[G]) := iT.comp e.toLinearMap
  have hpT := diagonalTensorFreeProjection_comp_inclusion A Λ G P M ρ σ
    pP iP hp pM iM hm hρ
  have hpi : p.comp i = LinearMap.id := by
    ext z
    change e.symm (pT (iT (e z))) = z
    rw [show pT (iT (e z)) = e z from LinearMap.congr_fun hpT (e z), e.symm_apply_apply]
  let f : Module.End Λ[G] (Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) :=
    (diagonalTensorEndomorphism ρ σ u v).1
  let uP : Module.End A[G] P := u
  let fT : Module.End Λ[G]
      (Representation.asModuleNC (Representation.tprodAlgebraReversed ρ σ)) :=
    e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  have htrace := groupTrace_eq_coeff_sum Λ G
    (Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) p i hpi f
  have hdiag (i₀ : Fin n) (j₀ : Fin m) :
      (i (f (p (standardBasisVector Λ[G] (Fin n × Fin m) (i₀, j₀))))
        (i₀, j₀)).coeff 1 =
      algebraMap A Λ
          ((iP (u (pP (standardBasisVector A[G] (Fin n) i₀))) i₀).coeff 1) *
        iM (groupAlgebraEnd_restrictScalars σ v
          (pM (standardBasisVector Λ (Fin m) j₀))) j₀ := by
    change (iT (fT (pT
      (standardBasisVector Λ[G] (Fin n × Fin m) (i₀, j₀))))
        (i₀, j₀)).coeff 1 = _
    dsimp [pT]
    rw [diagonalTensorFreeProjection_standardBasis]
    change (diagonalTensorFreeInclusion A Λ G P M ρ σ iP iM hρ
      ((Representation.tprodAlgebraCommModuleEquiv ρ σ).toLinearMap.comp
        ((diagonalTensorEndomorphism ρ σ u v).1.comp
          (Representation.tprodAlgebraCommModuleEquiv ρ σ).symm.toLinearMap)
        ((show Representation.asModuleNC
            (Representation.tprodAlgebraReversed ρ σ) from
          pM (standardBasisVector Λ (Fin m) j₀) ⊗ₜ[A]
            pP (standardBasisVector A[G] (Fin n) i₀))))
        (i₀, j₀)).coeff 1 = _
    rw [diagonalTensorEndomorphism_conj_apply_tmul,
      diagonalTensorFreeInclusion_apply_tmul,
      weightedCoeffMap_coeff_one]
    change algebraMap A Λ
      ((iP (u (pP (standardBasisVector A[G] (Fin n) i₀))) i₀).coeff 1) *
      iM (σ (1 : G)⁻¹
        (show M from v (show Representation.asModuleNC σ from
          pM (standardBasisVector Λ (Fin m) j₀)))) j₀ = _
    have hσ (x : M) : σ (1 : G) x = x := by simp
    rw [inv_one, hσ]
    rfl
  let a : Fin n → A := fun i₀ ↦
    (iP (u (pP (standardBasisVector A[G] (Fin n) i₀))) i₀).coeff 1
  let b : Fin m → Λ := fun j₀ ↦
    iM (groupAlgebraEnd_restrictScalars σ v
      (pM (standardBasisVector Λ (Fin m) j₀))) j₀
  have heval :
      commutativeAdditiveCommutatorQuotientEval A
          (groupTrace A G (Representation.asModuleNC ρ) u) =
        ∑ i₀, a i₀ := by
    change commutativeAdditiveCommutatorQuotientEval A
        (groupTrace A G P uP) = _
    rw [groupTrace_eq_coeff_sum A G P pP iP hp uP]
    simp [commutativeAdditiveCommutatorQuotientEval,
      additiveCommutatorQuotientMk, a, uP]
    rfl
  have hmoduleTrace :
      projectiveModuleTrace Λ M
          (groupAlgebraEnd_restrictScalars σ v) =
        additiveCommutatorQuotientMk Λ (∑ j₀, b j₀) := by
    rw [projectiveModuleTrace_eq_of_split Λ M
      (groupAlgebraEnd_restrictScalars σ v) pM iM hm,
      freeModuleTrace_apply]
    rfl
  change groupTrace Λ G
    (Representation.asModuleNC (Representation.tprodAlgebra ρ σ)) f = _
  rw [htrace, Fintype.sum_prod_type]
  simp_rw [hdiag]
  rw [heval, hmoduleTrace]
  let := additiveCommutatorQuotientModule A Λ
  have hsmul (x : Λ) :
      (∑ i₀, a i₀) •
          additiveCommutatorQuotientMk Λ x =
        additiveCommutatorQuotientMk Λ
          ((∑ i₀, a i₀) • x) :=
    (inducedAdditiveCommutatorQuotientModule A Λ).smul_mk
      (∑ i₀, a i₀) x
  change additiveCommutatorQuotientMk Λ
      (∑ i₀, ∑ j₀, algebraMap A Λ (a i₀) * b j₀) =
    (∑ i₀, a i₀) •
      additiveCommutatorQuotientMk Λ (∑ j₀, b j₀)
  rw [hsmul, Finset.smul_sum]
  simp only [Algebra.smul_def]
  congr 1
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_comm

end Stacks.Trace
