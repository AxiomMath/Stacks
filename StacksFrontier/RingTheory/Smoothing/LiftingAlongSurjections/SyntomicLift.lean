module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Different.Formula.SquarePresentation
public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Koszul.FlatQuotient
public import StacksFrontier.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smooth.SymmetricAlgebra
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension
public import StacksFrontier.RingTheory.Syntomic.BaseChange
public import StacksFrontier.RingTheory.Syntomic.Defs
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.RingTheory.Syntomic.Morphisms
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections.GlobalCompleteIntersectionLift

/-!
# Lifting syntomic algebras along a surjection

Let `R → R₀` be a surjective map of commutative rings with kernel `I`. Every syntomic
`R₀`-algebra `A₀` is the special fibre `A/IA` of a syntomic `R`-algebra `A`. A relative global
complete intersection enlargement of `A₀` is lifted to `R`; the conormal module is completed to a
finite free module and the symmetric algebra gives a smooth `R`-algebra with special fibre a
polynomial algebra over `A₀`; cutting by lifts of the variables, which are quasi-regular, gives a
lift which is syntomic after inverting one element congruent to `1` modulo `IA`.

## Main results

* `Stacks.Smoothing.exists_syntomic_lift_of_surjective`: a syntomic algebra over a quotient of
  the base lifts to a syntomic algebra over the base with the given special fibre.

## References

* [Stacks Project, Proposition 16.10.4, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/

@[expose] public section

open scoped TensorProduct

open RingTheory.Sequence

namespace Stacks.Smoothing

open Koszul

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u v w

/-- Syntomicity is invariant under an algebra equivalence. -/
private theorem syntomic_of_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T)
    (hS : Algebra.Syntomic R S) : Algebra.Syntomic R T := by
  let : Algebra.Syntomic R S := hS
  exact {
    flat := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    finitePresentation := Algebra.FinitePresentation.equiv e
    isLocalCompleteIntersection_fiber := fun p _ =>
      _root_.lci_transport p.ResidueField
        (Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField) e)
        (Algebra.Syntomic.isLocalCompleteIntersection_fiber p)
  }

/-- The symmetric algebra of a direct sum is the tensor product of symmetric algebras. -/
@[ega "II 1.7.1"]
private noncomputable def symmetricAlgebra_prodEquiv
    (A P Q : Type*) [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] :
    (SymmetricAlgebra A P ⊗[A] SymmetricAlgebra A Q) ≃ₐ[A]
      SymmetricAlgebra A (P × Q) := by
  let fP : P →ₗ[A] SymmetricAlgebra A (P × Q) :=
    (SymmetricAlgebra.ι A (P × Q)).comp (LinearMap.inl A P Q)
  let fQ : Q →ₗ[A] SymmetricAlgebra A (P × Q) :=
    (SymmetricAlgebra.ι A (P × Q)).comp (LinearMap.inr A P Q)
  let F : (SymmetricAlgebra A P ⊗[A] SymmetricAlgebra A Q) →ₐ[A]
      SymmetricAlgebra A (P × Q) :=
    Algebra.TensorProduct.lift (SymmetricAlgebra.lift fP)
      (SymmetricAlgebra.lift fQ) (fun _ _ => Commute.all _ _)
  let gP : P →ₗ[A] (SymmetricAlgebra A P ⊗[A] SymmetricAlgebra A Q) :=
    (Algebra.TensorProduct.includeLeft.toLinearMap).comp (SymmetricAlgebra.ι A P)
  let gQ : Q →ₗ[A] (SymmetricAlgebra A P ⊗[A] SymmetricAlgebra A Q) :=
    (Algebra.TensorProduct.includeRight.toLinearMap).comp (SymmetricAlgebra.ι A Q)
  let G : SymmetricAlgebra A (P × Q) →ₐ[A]
      (SymmetricAlgebra A P ⊗[A] SymmetricAlgebra A Q) :=
    SymmetricAlgebra.lift (gP.coprod gQ)
  refine AlgEquiv.ofAlgHom F G ?_ ?_
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    rintro ⟨p, q⟩
    change F (G (SymmetricAlgebra.ι A (P × Q) (p, q))) =
      SymmetricAlgebra.ι A (P × Q) (p, q)
    rw [SymmetricAlgebra.lift_ι_apply]
    change F (gP p + gQ q) = _
    simp only [Algebra.TensorProduct.lift, LinearMap.restrictScalars_self,
      Algebra.TensorProduct.toLinearMap_includeLeft, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mk_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Algebra.TensorProduct.toLinearMap_includeRight,
      Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply,
      TensorProduct.AlgebraTensorModule.lift_apply, map_add, TensorProduct.lift.tmul,
      LinearMap.coe_coe, map_one, AlgHom.coe_toLinearMap, SymmetricAlgebra.lift_ι_apply,
      LinearMap.coe_inl, LinearMap.mul_apply_apply, mul_one, LinearMap.coe_inr, one_mul,
      F, fP, fQ, gP, gQ]
    rw [← map_add]
    congr 1
    ext <;> simp
  · apply Algebra.TensorProduct.ext
    · apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro p
      change G (F ((SymmetricAlgebra.ι A P p) ⊗ₜ[A] 1)) =
        (SymmetricAlgebra.ι A P p) ⊗ₜ[A] 1
      simp [F, G, fP, fQ, gP, gQ, Algebra.TensorProduct.lift]
    · apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro q
      change G (F (1 ⊗ₜ[A] (SymmetricAlgebra.ι A Q q))) =
        1 ⊗ₜ[A] (SymmetricAlgebra.ι A Q q)
      simp [F, G, fP, fQ, gP, gQ, Algebra.TensorProduct.lift]

/-- A linear equivalence induces an equivalence of symmetric algebras. -/
private noncomputable def symmetricAlgebra_congr
    (A M N : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) : SymmetricAlgebra A M ≃ₐ[A] SymmetricAlgebra A N := by
  let F : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A N :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A N).comp e.toLinearMap)
  let G : SymmetricAlgebra A N →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp e.symm.toLinearMap)
  refine AlgEquiv.ofAlgHom F G ?_ ?_
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    simp [F, G]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    simp [F, G]

/-- Symmetric algebras commute with extension of scalars. -/
@[ega "II 1.7.2"]
private noncomputable def symmetricAlgebra_baseChangeEquiv
    (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] :
    (B ⊗[A] SymmetricAlgebra A M) ≃ₐ[B]
      SymmetricAlgebra B (B ⊗[A] M) := by
  let D := SymmetricAlgebra B (B ⊗[A] M)
  letI : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let tower : IsScalarTower A B D := inferInstance
  letI : IsScalarTower A B (B ⊗[A] M) := inferInstance
  letI : LinearMap.CompatibleSMul (B ⊗[A] M) D A B :=
    ⟨fun g a x => by
      rw [← smul_one_smul B a x, ← smul_one_smul B a (g x), map_smul]⟩
  let hι : (B ⊗[A] M) →ₗ[B] D := SymmetricAlgebra.ι B (B ⊗[A] M)
  let compatible : LinearMap.CompatibleSMul (B ⊗[A] M) D A B := inferInstance
  let hιA : (B ⊗[A] M) →ₗ[A] D :=
    @LinearMap.restrictScalars A B (B ⊗[A] M) D _ _ _ _ _ _ _ _ compatible hι
  let f : M →ₗ[A] D := hιA.comp (TensorProduct.mk A B M 1)
  let E : (SymmetricAlgebra A M →ₐ[A] D) ≃
      (B ⊗[A] SymmetricAlgebra A M →ₐ[B] D) :=
    @AlgHom.liftEquiv A B (SymmetricAlgebra A M) D _ _ _ _ _ _ _ _ tower
  let F : (B ⊗[A] SymmetricAlgebra A M) →ₐ[B] D :=
    E (SymmetricAlgebra.lift f)
  let G : D →ₐ[B] (B ⊗[A] SymmetricAlgebra A M) :=
    SymmetricAlgebra.lift (LinearMap.baseChange B (SymmetricAlgebra.ι A M))
  refine AlgEquiv.ofAlgHom F G ?_ ?_
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change F (G (SymmetricAlgebra.ι B (B ⊗[A] M) x)) =
      SymmetricAlgebra.ι B (B ⊗[A] M) x
    rw [SymmetricAlgebra.lift_ι_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      change (E (SymmetricAlgebra.lift f))
          (b ⊗ₜ[A] SymmetricAlgebra.ι A M m) =
        SymmetricAlgebra.ι B (B ⊗[A] M) (b ⊗ₜ[A] m)
      change b • (SymmetricAlgebra.lift f) (SymmetricAlgebra.ι A M m) = _
      rw [SymmetricAlgebra.lift_ι_apply]
      change b • SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] m) = _
      rw [← map_smul]
      congr 1
      simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy]
  · apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    change G (F (1 ⊗ₜ[A] SymmetricAlgebra.ι A M m)) =
      1 ⊗ₜ[A] SymmetricAlgebra.ι A M m
    change G ((E (SymmetricAlgebra.lift f))
      (1 ⊗ₜ[A] SymmetricAlgebra.ι A M m)) = _
    have hEval0 := @AlgHom.liftEquiv_tmul A B (SymmetricAlgebra A M) D
      _ _ _ _ _ _ _ _ tower (SymmetricAlgebra.lift f) (1 : B)
      (SymmetricAlgebra.ι A M m)
    have hEval : (E (SymmetricAlgebra.lift f))
        (1 ⊗ₜ[A] SymmetricAlgebra.ι A M m) = f m := by
      simpa only [E, one_smul, SymmetricAlgebra.lift_ι_apply] using hEval0
    rw [hEval]
    change G (SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] m)) = _
    rw [SymmetricAlgebra.lift_ι_apply, LinearMap.baseChange_tmul]

/-- Reduction of a symmetric algebra is the symmetric algebra of the reduced module. -/
private noncomputable def symmetricAlgebra_quotientEquiv
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (J : Ideal B) :
    (SymmetricAlgebra B M ⧸ J.map (algebraMap B (SymmetricAlgebra B M)))
      ≃ₐ[B ⧸ J] SymmetricAlgebra (B ⧸ J) ((B ⧸ J) ⊗[B] M) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (SymmetricAlgebra B M) J).trans
    (symmetricAlgebra_baseChangeEquiv B (B ⧸ J) M)

/-- A polynomial with zero constant term lies in the ideal generated by the variables. -/
private theorem mvPolynomial_ker_constantCoeff_eq_idealOfVars
    (σ A : Type*) [CommRing A] :
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ A →+* A) =
      MvPolynomial.idealOfVars σ A := by
  classical
  apply le_antisymm
  · intro p hp
    rw [MvPolynomial.idealOfVars, ← Set.image_univ]
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    have hm0 : m = 0 := by
      ext i
      by_contra hi
      exact h ⟨i, Set.mem_univ i, hi⟩
    have hcoeff : p.coeff 0 ≠ 0 := by
      simpa [hm0] using (MvPolynomial.mem_support_iff.mp hm)
    exact hcoeff (by simpa [MvPolynomial.constantCoeff_eq] using
      (RingHom.mem_ker.mp hp))
  · rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (MvPolynomial.constantCoeff_X A i)

/-- Evaluation at zero is the constant-coefficient homomorphism. -/
private theorem mvPolynomial_aeval_zero_eq_constantCoeff
    (R : Type*) [CommRing R] (m : ℕ) :
    (MvPolynomial.aeval (fun _ : Fin m => (0 : R))).toRingHom =
      (MvPolynomial.constantCoeff : MvPolynomial (Fin m) R →+* R) := by
  ext x
  · simp
  · show MvPolynomial.aeval (fun _ : Fin m => (0 : R)) (MvPolynomial.X x) =
      MvPolynomial.constantCoeff (MvPolynomial.X x)
    simp [MvPolynomial.aeval_X, MvPolynomial.constantCoeff_X]

/-- The constant coefficient of a polynomial ring is surjective. -/
private theorem mvPolynomial_constantCoeff_surjective (σ A : Type*) [CommRing A] :
    Function.Surjective (MvPolynomial.constantCoeff : MvPolynomial σ A →+* A) :=
  fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C σ a⟩

/-- Setting every polynomial variable to zero gives the coefficient ring. -/
private noncomputable def mvPolynomial_quotientVariablesEquiv
    (σ A : Type*) [CommRing A] :
    A ≃+* MvPolynomial σ A ⧸ MvPolynomial.idealOfVars σ A :=
  (RingHom.quotientKerEquivOfSurjective
    (mvPolynomial_constantCoeff_surjective σ A)).symm.trans
    (Ideal.quotEquivOfEq (mvPolynomial_ker_constantCoeff_eq_idealOfVars σ A))

/-- The identification of a ring with the polynomial algebra modulo its variables sends a scalar
to the class of the corresponding constant polynomial. -/
private theorem mvPolynomial_quotientVariablesEquiv_apply
    (σ A : Type*) [CommRing A] (a : A) :
    mvPolynomial_quotientVariablesEquiv σ A a =
      Ideal.Quotient.mk (MvPolynomial.idealOfVars σ A) (MvPolynomial.C a) := by
  have h := RingHom.quotientKerEquivOfSurjective_symm_apply
    (mvPolynomial_constantCoeff_surjective σ A) (MvPolynomial.C a)
  have h' := congrArg
    (Ideal.quotEquivOfEq (mvPolynomial_ker_constantCoeff_eq_idealOfVars σ A)) h
  rw [Ideal.quotEquivOfEq_mk] at h'
  simpa only [mvPolynomial_quotientVariablesEquiv, RingEquiv.trans_apply,
    MvPolynomial.constantCoeff_C] using h'

/-- The variables of a polynomial ring in finitely many variables form a quasi-regular
sequence. -/
private theorem mvPolynomial_X_isQuasiRegular (R : Type*) [CommRing R] (m : ℕ) :
    IsQuasiRegular (MvPolynomial (Fin m) R)
      (List.ofFn (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R)) := by
  let P : Algebra.Presentation R R (Fin m) (Fin m) := {
    val := fun _ => 0
    σ' := MvPolynomial.C
    aeval_val_σ' := by simp
    relation := MvPolynomial.X
    span_range_relation_eq_ker := by
      show MvPolynomial.idealOfVars (Fin m) R =
        RingHom.ker (MvPolynomial.aeval (fun _ : Fin m => (0 : R))).toRingHom
      rw [mvPolynomial_aeval_zero_eq_constantCoeff R m]
      exact (mvPolynomial_ker_constantCoeff_eq_idealOfVars (Fin m) R).symm
  }
  have hP : P.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection_of_card_eq (by simp)
  have hkos := RingHom.isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection P hP
  exact Koszul.isQuasiRegular_of_isH1RegularOn
    ((Koszul.isH1RegularOn_self_iff _).mpr (hkos 1 one_ne_zero))

/-- Cutting a flat finitely presented algebra by a sequence which is quasi-regular on the reduction
modulo `I`, with flat quotient there, leaves a flat local ring at every prime containing `I`. -/
private theorem flat_localization_quotient_of_isQuasiRegular
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (I : Ideal R) {r : ℕ} (f : Fin r → S)
    (hqr : IsQuasiRegular (S ⧸ I.map (algebraMap R S))
      (List.ofFn (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))
    (hflat : Module.Flat (R ⧸ I)
      ((S ⧸ I.map (algebraMap R S)) ⧸
        Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i)))))
    (q : Ideal (S ⧸ Ideal.span (Set.range f))) [q.IsPrime]
    (hI : I ≤ q.under R) :
    Module.Flat R (Localization.AtPrime q) := by
  let J := Ideal.span (Set.range f)
  let A := S ⧸ J
  let Q := q.comap (Ideal.Quotient.mk J)
  let p := Q.under R
  let T := Localization.AtPrime Q
  let P := Localization.AtPrime p
  have : Q.LiesOver p := ⟨rfl⟩
  let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsLocalHom (algebraMap P T) :=
    Localization.isLocalHom_localRingHom p Q (algebraMap R S) rfl
  have : Module.Flat P T :=
    (Module.flat_iff_of_isLocalization P p.primeCompl T).mpr inferInstance
  have hI' : I ≤ (IsLocalRing.maximalIdeal P).comap (algebraMap R P) := by
    intro x hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff P p x).mpr (hI hx)
  have hf : ∀ i, f i ∈ Q := by
    intro i
    show Ideal.Quotient.mk J (f i) ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))]
    exact q.zero_mem
  have hreg := isRegular_fiber (P := P) (T := T) p.primeCompl I hI' f
    (fun i ↦ (IsLocalization.AtPrime.to_map_mem_maximal_iff T Q (f i)).mpr (hf i))
    hqr hflat
  have hess : (algebraMap P T).EssentiallyOfFinitePresentation :=
    essentiallyOfFinitePresentation_localization (S := S) p.primeCompl Q.primeCompl
      (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have hreg' : IsRegular
      (T ⧸ ((IsLocalRing.maximalIdeal P).map (algebraMap P T) • (⊤ : Submodule T T)))
      (List.ofFn (fun i ↦ algebraMap S T (f i))) := by
    rwa [Ideal.smul_eq_mul, Ideal.mul_top]
  have ht := (Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
    (R := P) (S := T) (M := T) hess _ hreg').2 r
  have he : Ideal.ofList ((List.ofFn (fun i ↦ algebraMap S T (f i))).take r) •
      (⊤ : Submodule T T) = J.map (algebraMap S T) := by
    rw [List.take_of_length_le (by simp), Ideal.smul_eq_mul, Ideal.mul_top,
      Ideal.ofList_ofFn, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [he] at ht
  let X := T ⧸ J.map (algebraMap S T)
  have : Module.Flat P X := ht
  have : Module.Flat R X := Module.Flat.trans R P X
  have hM : Algebra.algebraMapSubmonoid A Q.primeCompl = q.primeCompl := by
    ext a
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro ha
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨s, ha, rfl⟩
  have : IsLocalization q.primeCompl X := hM ▸
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid A Q.primeCompl) X)
  have : IsScalarTower R A X := .of_algebraMap_eq fun _ ↦ rfl
  let e := (IsLocalization.algEquiv q.primeCompl X (Localization.AtPrime q)).restrictScalars R
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- Syntomicity descends along a bijective map of base rings. -/
private theorem syntomic_restrictScalars_of_bijective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (h : Function.Bijective (algebraMap R S)) [Algebra.Syntomic S T] :
    Algebra.Syntomic R T := by
  let e := RingEquiv.ofBijective (algebraMap R S) h
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower S R T := .of_algebraMap_eq fun s ↦ by
    obtain ⟨r, rfl⟩ := h.surjective s
    show algebraMap S T (algebraMap R S r) = algebraMap R T (e.symm (e r))
    rw [e.symm_apply_apply, ← IsScalarTower.algebraMap_apply R S T]
  have : Algebra.IsPushout S T R T := Algebra.IsPushout.of_bijective_left R T e.symm.bijective
  exact Algebra.IsPushout.syntomic S T R T

/-- A syntomic algebra over a field is a local complete intersection. -/
private theorem lci_of_syntomic_field {k S : Type*} [Field k] [CommRing S]
    [Algebra k S] [Algebra.Syntomic k S] : IsLocalCompleteIntersection k S := by
  let p : Ideal k := ⊥
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.IsPushout.isLocalCompleteIntersection_iff k p.ResidueField S
    (p.Fiber S)).mp (Algebra.Syntomic.isLocalCompleteIntersection_fiber p)

/-- If the reduction of `A` modulo `I` is syntomic over `R/I`, then the fibre of `A` at a prime
containing `I` is a complete intersection over the residue field. -/
private theorem completeIntersection_fiber_of_syntomic_quotient
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R)
    [Algebra.Syntomic (R ⧸ I) (A ⧸ I.map (algebraMap R A))]
    (q : Ideal A) [q.IsPrime] (hI : I ≤ q.under R) :
    IsCompleteIntersection (q.under R).ResidueField
      ((q.under R).Fiber (Localization.AtPrime q)) := by
  let p := q.under R
  let K := p.ResidueField
  let : Algebra (R ⧸ I) K :=
    (Ideal.Quotient.lift I (algebraMap R K) (by
      intro r hr
      exact Ideal.algebraMap_residueField_eq_zero.mpr (hI hr))).toAlgebra
  have : IsScalarTower R (R ⧸ I) K := .of_algebraMap_eq fun _ ↦ rfl
  let B := A ⧸ I.map (algebraMap R A)
  let : Algebra B (K ⊗[R ⧸ I] B) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.Syntomic K (K ⊗[R ⧸ I] B) :=
    Algebra.IsPushout.syntomic (R ⧸ I) B K _
  let e₀ := (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[R ⧸ I] K)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I)).trans
      (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) (R ⧸ I) K A)
  let e : (K ⊗[R ⧸ I] B) ≃ₐ[K] p.Fiber A :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun k ↦ by
      show e₀ (k ⊗ₜ[R ⧸ I] 1) = k ⊗ₜ[R] 1
      simp [e₀, Algebra.TensorProduct.one_def])
  have : Algebra.Syntomic K (p.Fiber A) := syntomic_of_algEquiv e inferInstance
  have hlci := lci_of_syntomic_field (k := K) (S := p.Fiber A)
  obtain ⟨Q, hQ, heq⟩ := Ideal.Fiber.exists_comap_includeRight_eq (R := R) q p rfl
  let : Algebra (p.Fiber A) (p.Fiber (Localization.AtPrime q)) :=
    (Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom R A (Localization.AtPrime q))).toRingHom.toAlgebra
  have := Ideal.Fiber.isLocalization_atPrime p Q q heq (Localization.AtPrime q)
  have : IsScalarTower K (p.Fiber A) (p.Fiber (Localization.AtPrime q)) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := p.Fiber A)
      (A := p.Fiber (Localization.AtPrime q)) fun x ↦ by
        simp [RingHom.algebraMap_toAlgebra]
  have h12 := (IsLocalCompleteIntersection.tfae K (p.Fiber A)).out 1 2
  exact h12.mp hlci Q _

/-- A finitely presented algebra that is flat at every prime and whose fibres at every prime are
complete intersections is syntomic. -/
private theorem syntomic_of_local_flat_and_completeIntersection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (h : ∀ (q : Ideal S) [q.IsPrime], Module.Flat R (Localization.AtPrime q) ∧
      IsCompleteIntersection (q.under R).ResidueField
        ((q.under R).Fiber (Localization.AtPrime q))) : Algebra.Syntomic R S := by
  have : Module.Flat R S := Module.flat_of_isLocalized_maximal S S
    (fun q _ ↦ Localization.AtPrime q) (fun q _ ↦ Algebra.linearMap S _) (fun q _ ↦ (h q).1)
  refine ⟨inferInstance, inferInstance, fun p _ ↦ ?_⟩
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  apply ((IsLocalCompleteIntersection.tfae p.ResidueField (p.Fiber S)).out 1 2).mpr
  intro Q hQ T _ _ _ _ _
  let q := Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)
  have hp : q.under R = p := by
    refine Eq.trans ?_ (Ideal.over_def Q p).symm
    ext r
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
      AlgHom.commutes]
  have hci := IsCompleteIntersection.fiber_congr hp (h q).2
  let : Algebra (p.Fiber S) (p.Fiber (Localization.AtPrime q)) :=
    (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (IsScalarTower.toAlgHom R S (Localization.AtPrime q))).toRingHom.toAlgebra
  have := Ideal.Fiber.isLocalization_atPrime p Q q rfl (Localization.AtPrime q)
  have : IsScalarTower p.ResidueField (p.Fiber S) (p.Fiber (Localization.AtPrime q)) :=
    IsScalarTower.of_algebraMap_eq (R := p.ResidueField) (S := p.Fiber S)
      (A := p.Fiber (Localization.AtPrime q)) fun x ↦ by
        simp [RingHom.algebraMap_toAlgebra]
  exact hci.of_algEquiv
    ((IsLocalization.algEquiv Q.primeCompl (p.Fiber (Localization.AtPrime q)) T).restrictScalars _)

/-- If every prime containing an ideal `J` has a syntomic localization away from some element
outside it, then one element congruent to `1` modulo `J` has syntomic localization. -/
private theorem exists_sub_one_mem_syntomic
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (J : Ideal S)
    (h : ∀ (q : Ideal S) [q.IsPrime], J ≤ q →
      ∃ s ∉ q, Algebra.Syntomic R (Localization.Away s)) :
    ∃ s : S, s - 1 ∈ J ∧ Algebra.Syntomic R (Localization.Away s) := by
  classical
  let U : Set S := {s | Algebra.Syntomic R (Localization.Away s)}
  have htop : J ⊔ Ideal.span U = ⊤ := by
    by_contra hn
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (J ⊔ Ideal.span U) hn
    have : q.IsMaximal := hq
    obtain ⟨s, hs, hsyn⟩ := h q (le_sup_left.trans hle)
    exact hs ((le_sup_right.trans hle) (Ideal.subset_span hsyn))
  obtain ⟨a, ha, s, hs, he⟩ := Submodule.mem_sup.mp
    (show (1 : S) ∈ J ⊔ Ideal.span U from by rw [htop]; trivial)
  refine ⟨s, ?_, ?_⟩
  · have : s - 1 = -a := by rw [← he]; ring
    exact this ▸ J.neg_mem ha
  apply syntomic_of_local_flat_and_completeIntersection
  intro q' hq'
  let q := q'.comap (algebraMap S (Localization.Away s))
  have hsq : s ∉ q := fun hm ↦ hq'.ne_top (Ideal.eq_top_of_isUnit_mem q' hm
    (IsLocalization.Away.algebraMap_isUnit s))
  have hu : ∃ t ∈ U, t ∉ q := by
    by_contra hn
    have hle : Ideal.span U ≤ q := Ideal.span_le.mpr (by
      intro t ht
      by_contra hnot
      exact hn ⟨t, ht, hnot⟩)
    exact hsq (hle hs)
  obtain ⟨t, ht, htq⟩ := hu
  have h13 := (Algebra.exists_notMem_syntomic_tfae (q.under R) q).out 1 3
  have hlocal := h13.mp ⟨t, htq, ht⟩
  obtain ⟨_, _, _, hflat, hci⟩ := hlocal
  rw [Localization.AtPrime.flat_localRingHom_iff] at hflat
  have : Module.Flat R (Localization.AtPrime q) := hflat
  have : IsLocalization.AtPrime (Localization.AtPrime q') q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers s)
      (Localization.AtPrime q') q'
  let e := (IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime q')).restrictScalars R
  have hp : q.under R = q'.under R := by
    show (q'.comap (algebraMap S (Localization.Away s))).comap (algebraMap R S) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  refine ⟨Module.Flat.of_linearEquiv e.symm.toLinearEquiv, ?_⟩
  exact IsCompleteIntersection.fiber_congr hp
    (hci.of_algEquiv (Algebra.TensorProduct.congr AlgEquiv.refl e))

/-- A syntomic algebra over a quotient of the base is the special fibre of a syntomic algebra over
the base: if `R → R₀` is surjective with kernel `I` and `R₀ → A₀` is syntomic, there is a syntomic
`R`-algebra `A` together with a ring equivalence `A₀ ≃ A/IA` compatible with the maps from `R`. -/
@[stacks 07M8 "syntomic lift"]
theorem exists_syntomic_lift_of_surjective
    (R : Type u) (R₀ : Type v) (A₀ : Type w) [CommRing R] [CommRing R₀] [CommRing A₀]
    [Algebra R R₀] [Algebra R₀ A₀]
    (hR : Function.Surjective (algebraMap R R₀))
    (hA₀ : Algebra.Syntomic R₀ A₀) :
    ∃ (A : Type (max u w)) (_ : CommRing A) (a : Algebra R A),
      letI := a
      Algebra.Syntomic R A ∧
        ∃ e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R A)
          (RingHom.ker (algebraMap R R₀)),
          ∀ r : R, e (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
            Ideal.Quotient.mk _ (algebraMap R A r) := by
  classical
  let : Algebra.Syntomic R₀ A₀ := hA₀
  obtain ⟨C₀, hC₀ring, aR₀C₀, aA₀C₀, hR₀A₀C₀, hC₀ft, g₀,
    n₀, P₀, e₀, hP₀fin, hP₀proj, hg₀, hsection₀, hC₀syn, hC₀gci, -⟩ :=
    exists_syntomic_free_conormal_enlargement hA₀
  let : CommRing C₀ := hC₀ring
  let : Algebra A₀ C₀ := aA₀C₀
  let : Algebra R₀ C₀ := aR₀C₀
  let : IsScalarTower R₀ A₀ C₀ := hR₀A₀C₀
  let : Algebra.IsRelativeGlobalCompleteIntersection R₀ C₀ := hC₀gci
  let P := P₀.toExtension.Cotangent
  let : Module.Finite A₀ P := hP₀fin
  let : Module.Projective A₀ P := hP₀proj
  obtain ⟨m, K, hKadd, hKmod, hKfin, hKproj, ⟨eK⟩⟩ :=
    Module.exists_finite_projective_complement (R := A₀) P
  let : AddCommGroup K := hKadd
  let : Module A₀ K := hKmod
  let : Module.Finite A₀ K := hKfin
  let : Module.Projective A₀ K := hKproj
  obtain ⟨C, hCring, aRC, hCgci, eC, heC⟩ :=
    exists_relativeGlobalCompleteIntersection_lift R R₀ C₀ hR
  let : CommRing C := hCring
  let : Algebra R C := aRC
  let : Algebra.IsRelativeGlobalCompleteIntersection R C := hCgci
  let : Algebra.Syntomic R C :=
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection R C
  let I : Ideal R := RingHom.ker (algebraMap R R₀)
  let J : Ideal C := I.map (algebraMap R C)
  let Cbar := C ⧸ J
  let : Algebra A₀ Cbar :=
    (eC.toRingHom.comp (algebraMap A₀ C₀)).toAlgebra
  let Kbar := Cbar ⊗[A₀] K
  have : Module.Finite Cbar Kbar := inferInstance
  have : Module.Projective Cbar Kbar := inferInstance
  obtain ⟨C', hC'ring, aCC', hEt, hq, Q, hQadd, hQmod, hQfin, hQproj, ⟨eQ⟩⟩ :=
    exists_etale_baseChange_finite_projective_lift J Kbar
  let : CommRing C' := hC'ring
  let : Algebra C C' := aCC'
  let : Algebra.Etale C C' := hEt
  let : AddCommGroup Q := hQadd
  let : Module C' Q := hQmod
  let : Module.Finite C' Q := hQfin
  let : Module.Projective C' Q := hQproj
  let : Algebra R C' := ((algebraMap C C').comp (algebraMap R C)).toAlgebra
  let : IsScalarTower R C C' := .of_algebraMap_eq' rfl
  let D := SymmetricAlgebra C' Q
  let : Algebra R D := ((algebraMap C' D).comp (algebraMap R C')).toAlgebra
  let : IsScalarTower R C' D := .of_algebraMap_eq' rfl
  let : Algebra.Syntomic C C' := Algebra.Smooth.syntomic C C'
  let : Algebra.Smooth C' D :=
    (symmetricAlgebra_smooth_iff_finite_projective C' Q).2
      ⟨hQfin, hQproj⟩
  let : Algebra.Syntomic C' D := Algebra.Smooth.syntomic C' D
  let : Algebra.Syntomic R C' := Algebra.Syntomic.comp R C C'
  have hDsyn : Algebra.Syntomic R D := Algebra.Syntomic.comp R C' D
  let J' : Ideal C' := J.map (algebraMap C C')
  let C'bar := C' ⧸ J'
  let q : Cbar →+* C'bar :=
    Ideal.quotientMap J' (algebraMap C C') Ideal.le_comap_map
  let qr : Cbar ≃+* C'bar := RingEquiv.ofBijective q hq
  let : RingHomInvPair qr.toRingHom qr.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv qr
  let : RingHomInvPair qr.symm.toRingHom qr.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm qr
  let : RingHomCompTriple qr.symm.toRingHom qr.toRingHom (RingHom.id C'bar) :=
    ⟨by ext x; exact qr.apply_symm_apply x⟩
  let : Algebra A₀ C'bar :=
    (qr.toRingHom.comp (algebraMap A₀ Cbar)).toAlgebra
  let qalg : Cbar ≃ₐ[A₀] C'bar := AlgEquiv.ofRingEquiv (f := qr) (fun _ => rfl)
  let qlin : Cbar ≃ₗ[A₀] C'bar := qalg.toLinearEquiv
  let eTensor : Kbar ≃ₛₗ[qr.toRingHom] (C'bar ⊗[A₀] K) :=
    { TensorProduct.congr qlin (LinearEquiv.refl A₀ K) with
      map_smul' := fun c x => by
        show (TensorProduct.congr qlin (LinearEquiv.refl A₀ K)) (c • x) =
          qr c • (TensorProduct.congr qlin (LinearEquiv.refl A₀ K)) x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
        | tmul x y =>
            rw [TensorProduct.smul_tmul', TensorProduct.congr_tmul,
              TensorProduct.congr_tmul, TensorProduct.smul_tmul']
            show qr (c * x) ⊗ₜ[A₀] y = (qr c * qr x) ⊗ₜ[A₀] y
            rw [map_mul] }
  let Qbar := C'bar ⊗[C'] Q
  let eKbarQ : (C'bar ⊗[A₀] K) ≃ₗ[C'bar] Qbar :=
    { eTensor.symm.toAddEquiv.trans eQ.toAddEquiv with
      map_smul' := fun c x => by
        show eQ (eTensor.symm (c • x)) = c • eQ (eTensor.symm x)
        rw [LinearEquiv.map_smulₛₗ eTensor.symm c x,
          LinearEquiv.map_smulₛₗ eQ
            ((RingEquiv.ofBijective q hq).symm.toRingHom c) (eTensor.symm x)]
        show (RingEquiv.ofBijective q hq)
          ((RingEquiv.ofBijective q hq).symm c) • eQ (eTensor.symm x) = _
        rw [(RingEquiv.ofBijective q hq).apply_symm_apply] }
  let : Algebra (C' ⧸ J')
      (D ⧸ J'.map (algebraMap C' D)) :=
    inferInstance
  let eD := symmetricAlgebra_quotientEquiv C' Q J'
  let eC₀bar : C₀ ≃ₐ[A₀] Cbar :=
    AlgEquiv.ofRingEquiv (f := eC) (fun _ => rfl)
  let eC'P : C'bar ≃ₐ[A₀] SymmetricAlgebra A₀ P :=
    (eC₀bar.trans qalg).symm.trans e₀
  let : Algebra A₀ (D ⧸ J'.map (algebraMap C' D)) :=
    ((algebraMap C'bar _).comp (algebraMap A₀ C'bar)).toAlgebra
  let : IsScalarTower A₀ C'bar (D ⧸ J'.map (algebraMap C' D)) :=
    .of_algebraMap_eq' rfl
  let : Algebra A₀ (SymmetricAlgebra C'bar Qbar) :=
    ((algebraMap C'bar _).comp (algebraMap A₀ C'bar)).toAlgebra
  let : IsScalarTower A₀ C'bar (SymmetricAlgebra C'bar Qbar) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A₀ (SymmetricAlgebra C'bar (C'bar ⊗[A₀] K)) :=
    ((algebraMap C'bar _).comp (algebraMap A₀ C'bar)).toAlgebra
  let : IsScalarTower A₀ C'bar (SymmetricAlgebra C'bar (C'bar ⊗[A₀] K)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eD₀ : (D ⧸ J'.map (algebraMap C' D)) ≃ₐ[A₀]
      SymmetricAlgebra C'bar Qbar :=
    AlgEquiv.ofRingEquiv (f := eD.toRingEquiv) (fun a => eD.commutes (algebraMap A₀ C'bar a))
  let eQcongr := symmetricAlgebra_congr C'bar Qbar (C'bar ⊗[A₀] K) eKbarQ.symm
  let eQcongr₀ : SymmetricAlgebra C'bar Qbar ≃ₐ[A₀]
      SymmetricAlgebra C'bar (C'bar ⊗[A₀] K) :=
    AlgEquiv.ofRingEquiv (f := eQcongr.toRingEquiv)
      (fun a => eQcongr.commutes (algebraMap A₀ C'bar a))
  let eBC := (symmetricAlgebra_baseChangeEquiv A₀ C'bar K).symm
  let eBC₀ : SymmetricAlgebra C'bar (C'bar ⊗[A₀] K) ≃ₐ[A₀]
      C'bar ⊗[A₀] SymmetricAlgebra A₀ K :=
    AlgEquiv.ofRingEquiv (f := eBC.toRingEquiv) (fun a => eBC.commutes (algebraMap A₀ C'bar a))
  let ePoly : (D ⧸ J'.map (algebraMap C' D)) ≃ₐ[A₀]
      MvPolynomial (Fin m) A₀ :=
    (eD₀.trans eQcongr₀).trans eBC₀ |>.trans
      ((Algebra.TensorProduct.congr eC'P
        (AlgEquiv.refl : SymmetricAlgebra A₀ K ≃ₐ[A₀] _)).trans
        ((symmetricAlgebra_prodEquiv A₀ P K).trans
          ((symmetricAlgebra_congr A₀ (P × K) (Fin m → A₀) eK.symm).trans
            (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun A₀ (Fin m))))))
  have hJD : J'.map (algebraMap C' D) = I.map (algebraMap R D) := by
    dsimp [J', J]
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  let L : Ideal D := J'.map (algebraMap C' D)
  have hR_Dbar (r : R) :
      Ideal.Quotient.mk L (algebraMap R D r) =
        algebraMap A₀ (D ⧸ L) (algebraMap R₀ A₀ (algebraMap R R₀ r)) := by
    have hC : eC (algebraMap A₀ C₀ (algebraMap R₀ A₀ (algebraMap R R₀ r))) =
        Ideal.Quotient.mk J (algebraMap R C r) := by
      rw [← IsScalarTower.algebraMap_apply R₀ A₀ C₀]
      exact heC r
    show Ideal.Quotient.mk L (algebraMap C' D (algebraMap C C' (algebraMap R C r))) =
      algebraMap C'bar (D ⧸ L)
        (qr (eC (algebraMap A₀ C₀ (algebraMap R₀ A₀ (algebraMap R R₀ r)))))
    rw [hC]
    rfl
  choose f hf using fun i : Fin m =>
    Ideal.Quotient.mk_surjective (ePoly.symm (MvPolynomial.X i))
  let Kideal : Ideal D := Ideal.span (Set.range f)
  let A := D ⧸ Kideal
  let : Algebra R A :=
    ((Ideal.Quotient.mk Kideal).comp (algebraMap R D)).toAlgebra
  have hgen (i : Fin m) : ePoly (Ideal.Quotient.mk L (f i)) =
      MvPolynomial.X i := by
    rw [hf i]
    exact ePoly.apply_symm_apply _
  have hmap : (I.map (algebraMap R D)).map (Ideal.Quotient.mk Kideal) =
      I.map (algebraMap R A) := by
    rw [Ideal.map_map]
    rfl
  have hIA : I.map (algebraMap R A) = L.map (Ideal.Quotient.mk Kideal) := by
    rw [show L = I.map (algebraMap R D) from hJD, hmap]
  have hKred : MvPolynomial.idealOfVars (Fin m) A₀ =
      (Kideal.map (Ideal.Quotient.mk L)).map ePoly.toRingEquiv := by
    simp only [Kideal, MvPolynomial.idealOfVars, Ideal.map_span,
      ← Set.range_comp, Function.comp_def]
    congr 1
    exact congrArg Set.range (funext fun i => (hgen i).symm)
  let eKred : (D ⧸ L) ⧸ Kideal.map (Ideal.Quotient.mk L) ≃+*
      MvPolynomial (Fin m) A₀ ⧸ MvPolynomial.idealOfVars (Fin m) A₀ :=
    Ideal.quotientEquiv _ _ ePoly.toRingEquiv hKred
  let eSwap : (D ⧸ Kideal) ⧸ L.map (Ideal.Quotient.mk Kideal) ≃+*
      (D ⧸ L) ⧸ Kideal.map (Ideal.Quotient.mk L) :=
    DoubleQuot.quotQuotEquivComm Kideal L
  let eFiber : A₀ ≃+* A ⧸ I.map (algebraMap R A) :=
    (((mvPolynomial_quotientVariablesEquiv (Fin m) A₀).trans eKred.symm).trans
      eSwap.symm).trans (Ideal.quotEquivOfEq hIA.symm)
  have hpoly (r : R) :
      ePoly (Ideal.Quotient.mk L (algebraMap R D r)) =
        MvPolynomial.C (algebraMap R₀ A₀ (algebraMap R R₀ r)) := by
    rw [hR_Dbar]
    exact ePoly.commutes _
  have hAfin : Algebra.FinitePresentation R A := by
    let : Algebra.Syntomic R D := hDsyn
    let : Algebra.FinitePresentation R D := hDsyn.finitePresentation
    exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range f))
  have heFiber : ∀ r : R,
      eFiber (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
        Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A r) := by
    intro r
    have hred : eKred.symm
        (Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin m) A₀)
          (MvPolynomial.C (algebraMap R₀ A₀ (algebraMap R R₀ r)))) =
        Ideal.Quotient.mk (Kideal.map (Ideal.Quotient.mk L))
          (Ideal.Quotient.mk L (algebraMap R D r)) := by
      refine eKred.symm_apply_eq.mpr ?_
      show Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin m) A₀)
          (MvPolynomial.C (algebraMap R₀ A₀ (algebraMap R R₀ r))) =
        Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin m) A₀)
          (ePoly (Ideal.Quotient.mk L (algebraMap R D r)))
      rw [hpoly]
    have hswap : eSwap.symm
        (Ideal.Quotient.mk (Kideal.map (Ideal.Quotient.mk L))
          (Ideal.Quotient.mk L (algebraMap R D r))) =
        Ideal.Quotient.mk (L.map (Ideal.Quotient.mk Kideal))
          (Ideal.Quotient.mk Kideal (algebraMap R D r)) :=
      eSwap.symm_apply_eq.mpr (DoubleQuot.quotQuotEquivComm_quotQuotMk Kideal L _)
    show eFiber (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
      Ideal.Quotient.mk (I.map (algebraMap R A))
        (Ideal.Quotient.mk Kideal (algebraMap R D r))
    simp only [eFiber, RingEquiv.trans_apply,
      mvPolynomial_quotientVariablesEquiv_apply, hred, hswap]
    exact Ideal.quotEquivOfEq_mk _ _
  let : Algebra R₀ (A ⧸ I.map (algebraMap R A)) :=
    (specialFiberBaseMap R R₀ A hR).toAlgebra
  let : IsScalarTower R R₀ (A ⧸ I.map (algebraMap R A)) :=
    .of_algebraMap_eq fun r => by
      exact (specialFiberBaseMap_comp R R₀ A hR r).symm
  have hAbarSyn : Algebra.Syntomic R₀ (A ⧸ I.map (algebraMap R A)) :=
    syntomic_of_algEquiv (specialFiberAlgEquiv R R₀ A₀ A hR eFiber heFiber) hA₀
  obtain ⟨g, hg, hAgsyn⟩ : ∃ g : A,
      g - 1 ∈ I.map (algebraMap R A) ∧
        Algebra.Syntomic R (Localization.Away g) := by
    let : Algebra (R ⧸ I) (A ⧸ I.map (algebraMap R A)) := inferInstance
    let eBase : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hR
    let : Algebra (R ⧸ I) R₀ := eBase.toRingHom.toAlgebra
    have : IsScalarTower (R ⧸ I) R₀ (A ⧸ I.map (algebraMap R A)) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (specialFiberBaseMap_comp R R₀ A hR r).symm
    let : Algebra.Syntomic R₀ (A ⧸ I.map (algebraMap R A)) := hAbarSyn
    have hbarSynQ : Algebra.Syntomic (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
      syntomic_restrictScalars_of_bijective eBase.bijective
    let hbarFlatQ := hbarSynQ.flat
    let E : (D ⧸ I.map (algebraMap R D)) ≃+* MvPolynomial (Fin m) A₀ :=
      (Ideal.quotEquivOfEq hJD.symm).trans ePoly.toRingEquiv
    have hE (i : Fin m) : E (Ideal.Quotient.mk (I.map (algebraMap R D)) (f i)) =
        MvPolynomial.X i :=
      hgen i
    have hqr : IsQuasiRegular (D ⧸ I.map (algebraMap R D))
        (List.ofFn (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R D)) (f i))) := by
      have h := isQuasiRegular_map_of_flat E.symm.toRingHom
        (RingHom.Flat.of_bijective E.symm.bijective) (mvPolynomial_X_isQuasiRegular A₀ m)
      have he (i : Fin m) : E.symm (MvPolynomial.X i) =
          Ideal.Quotient.mk (I.map (algebraMap R D)) (f i) :=
        E.symm_apply_eq.mpr (hE i).symm
      rw [List.map_ofFn] at h
      change IsQuasiRegular _ (List.ofFn (fun i ↦ E.symm (MvPolynomial.X i))) at h
      simpa only [he] using h
    let E₂ : ((D ⧸ I.map (algebraMap R D)) ⧸
        Kideal.map (Ideal.Quotient.mk (I.map (algebraMap R D)))) ≃+*
        A ⧸ I.map (algebraMap R A) :=
      (DoubleQuot.quotQuotEquivComm (I.map (algebraMap R D)) Kideal).trans
        (Ideal.quotEquivOfEq hmap)
    let E₂a : ((D ⧸ I.map (algebraMap R D)) ⧸
        Kideal.map (Ideal.Quotient.mk (I.map (algebraMap R D)))) ≃ₐ[R ⧸ I]
        A ⧸ I.map (algebraMap R A) :=
      AlgEquiv.ofRingEquiv (f := E₂) (fun x : R ⧸ I ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        show E₂ (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (algebraMap R D r))) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (algebraMap R D r))
        exact (congrArg (Ideal.quotEquivOfEq hmap)
          (DoubleQuot.quotQuotEquivComm_quotQuotMk
            (I.map (algebraMap R D)) Kideal (algebraMap R D r))).trans
              (Ideal.quotEquivOfEq_mk hmap _))
    have hflat : Module.Flat (R ⧸ I)
        ((D ⧸ I.map (algebraMap R D)) ⧸
          Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R D)) (f i)))) := by
      have he : Kideal.map (Ideal.Quotient.mk (I.map (algebraMap R D))) =
          Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R D)) (f i))) := by
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      exact Module.Flat.of_linearEquiv
        (((Ideal.quotientEquivAlgOfEq (R ⧸ I) he).symm.trans E₂a).toLinearEquiv)
    let : Algebra.FinitePresentation R A := hAfin
    let : Algebra.Syntomic R D := hDsyn
    apply exists_sub_one_mem_syntomic
    intro q hq hIq
    have hI : I ≤ q.under R := Ideal.map_le_iff_le_comap.mp hIq
    have hflatq : Module.Flat R (Localization.AtPrime q) :=
      flat_localization_quotient_of_isQuasiRegular I f hqr hflat q hI
    have hci := completeIntersection_fiber_of_syntomic_quotient I q hI
    obtain ⟨g, hg, hsyn⟩ :=
      @Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_of_flat R A _ _ _ _ q _
        hflatq hci
    exact ⟨g, hg, Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection R _⟩
  obtain ⟨eLoc, heLoc⟩ :=
    specialFiber_equiv_localizationAway R R₀ A₀ A eFiber heFiber g hg
  exact ⟨Localization.Away g, inferInstance, inferInstance, hAgsyn, eLoc, heLoc⟩

end Stacks.Smoothing

end
