module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConstantNumeratorFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.FiniteSupportAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.ReducedFactorPackages

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Prime-degree input: the equal-characteristic wild case

The all-conjugates equal-characteristic constant-Laurent branch and the equal-characteristic
wild prime-degree solver.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing
open scoped TensorProduct

namespace Stacks.EppTheorem

universe u v w uΩ

/-- A statement `∃ y, P k y` for all `k` in a finset can be made unconditional by a junk value. -/
private theorem exists_imp_of_forall_mem_exists {α β : Type*} [Nonempty β] (s : Finset α)
    (P : α → β → Prop) (h : ∀ k ∈ s, ∃ y, P k y) : ∀ k, ∃ y, k ∈ s → P k y := by
  classical
  intro k
  by_cases hk : k ∈ s
  · obtain ⟨y, hy⟩ := h k hk
    exact ⟨y, fun _ => hy⟩
  · exact ⟨Classical.arbitrary β, fun h => (hk h).elim⟩

/-- **The all-conjugates equal-characteristic constant-Laurent branch.**

The finitely many chosen `p ^ N`-th coefficient roots are absorbed into one finite
weakly-unramified extension `R / A`.  Every factor of the upper base change is matched with a
factor of the lower base change.  Degree-one factors are carried directly; degree-`p` factors are
solved by `exists_finite_extension_isWeakSolution_of_reentered_constant_laurent`.  Finally the
perfect-residue individual-factor combiner amalgamates all resulting solution fields.

This is the corrected replacement for the invalid single-factor reading of Tag 09ET: no chosen
factor is privileged, and the output is obtained only after every conjugate factor has been
discharged. -/
theorem exists_finite_extension_isWeakSolution_of_constant_laurent_of_charP
    (p : ℕ) (hp : p.Prime) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharP K p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    [Module.Finite L M] [IsGalois L M]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hepp : EppCondition A B p)
    (pi : A) (hpi : Irreducible pi) (N : ℕ) (hN : 0 < N)
    (xi : L) (z : M)
    (lift : ResidueField B → B)
    (hlift : ∀ x, residue B (lift x) = x)
    (liftMod : ResidueField B →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hliftMod : ∀ x, Ideal.Quotient.mk _ (lift x) = liftMod x)
    (coeff : ℕ → ResidueField B) (b : B)
    (hz : z ^ p - z = algebraMap L M xi)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (hexp : xi = (∑ k ∈ Finset.range N,
      algebraMap B L (lift (coeff k)) *
        (algebraMap B L (algebraMap A B pi))⁻¹ ^ (N - k)) + algebraMap B L b)
    (hperfect : ∀ k ∈ Finset.range N, ∀ m : ℕ,
      ∃ y : ResidueField B, y ^ (p ^ m) = coeff k) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution := by
  classical
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  choose rootCoeff hrootCoeff using
    exists_imp_of_forall_mem_exists (Finset.range N) (fun k (y : ResidueField B) =>
      y ^ (p ^ N) = coeff k) fun k hk => hperfect k hk N
  let support : Finset (ResidueField B) := (Finset.range N).image rootCoeff
  have hsupport : ∀ x ∈ support, x ∈ perfectCore (ResidueField B) p := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact mem_perfectCore_of_pow_eq
      (mem_perfectCore_iff.mpr (hperfect k hk)) (hrootCoeff k hk)
  obtain ⟨R, hRcomm, hRdom, hRdvr, hAR, hRfin, hARext, hRcomplete, hRperfect,
      K₁, hK₁field, hRK₁, hRfrac, hKK₁, hAK₁, hAKK₁, hARK₁, hK₁fin,
      hweakAR, hgalResidue, habs⟩ :=
    EppCondition.exists_fractionField_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
      (R := A) (K := K) (fun _ : ULift.{u} Unit => B) (fun _ => hepp)
      (fun _ => support) (fun _ => hsupport) 0
  let := hRcomm
  let := hRdom
  let := hRdvr
  let := hAR
  let := hRfin
  let := hARext
  let := hRcomplete
  let := hRperfect
  let := hK₁field
  let := hRK₁
  let := hRfrac
  let := hKK₁
  let := hAK₁
  let := hAKK₁
  let := hARK₁
  let := hK₁fin
  let : CharP K₁ p :=
    charP_of_injective_algebraMap (algebraMap K K₁).injective p
  let : HenselianLocalRing B := henselianLocalRing_of_isAdicComplete_maximalIdeal B
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
    let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
    let : Module.Finite B (integralClosure B M) :=
      (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
    let : Module.Finite B C := Module.Finite.equiv
      (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
    exact isAdicComplete_of_finite B C
  let : HenselianLocalRing C := henselianLocalRing_of_isAdicComplete_maximalIdeal C
  apply exists_finite_extension_isWeakSolution_of_forall_individualFactorSolutions
    A C K M K₁ R
  · intro a
    rw [← IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply A R K₁]
  · intro m F hFfield hKF hMF hK₁F hKMF hKK₁F hMfin decomp hleft hright
    let := hFfield
    let := hKF
    let := hMF
    let := hK₁F
    let := hKMF
    let := hKK₁F
    let := hMfin
    let : ∀ i, Algebra C (F i) := fun i =>
      ((algebraMap M (F i)).comp (algebraMap C M)).toAlgebra
    let : ∀ i, Algebra B (F i) := fun i =>
      ((algebraMap M (F i)).comp (algebraMap B M)).toAlgebra
    let : ∀ i, Algebra A (F i) := fun i =>
      ((algebraMap C (F i)).comp (algebraMap A C)).toAlgebra
    let : ∀ i, IsScalarTower C M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ i, IsScalarTower B M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ i, IsScalarTower A C (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ i, Algebra L (F i) := fun i =>
      ((algebraMap M (F i)).comp (algebraMap L M)).toAlgebra
    let : ∀ i, IsScalarTower L M (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ i, IsScalarTower B L (F i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply B M (F i),
          IsScalarTower.algebraMap_apply B L M]
        rfl
    let : ∀ i, IsScalarTower B C (F i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply B M (F i),
          IsScalarTower.algebraMap_apply B C M,
          ← IsScalarTower.algebraMap_apply C M (F i)]
    let : ∀ i, IsScalarTower K L (F i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply K M (F i),
          IsScalarTower.algebraMap_apply K L M]
        rfl
    obtain ⟨D⟩ := nonempty_integralClosureBaseChange A B K L K₁
    let := D.commRingL₁
    let := D.algebraKL₁
    let := D.algebraLL₁
    let := D.algebraK₁L₁
    obtain ⟨n, H, hHfield, hLH, hK₁H, hBH, hAH, hBLH, hABH, hAK₁H,
        hLHfin, hn, eH, heH⟩ := exists_finiteFieldFactors_of_package A B K L K₁ D
    let := hHfield
    let := hLH
    let := hK₁H
    let := hBH
    let := hAH
    let := hBLH
    let := hABH
    let := hAK₁H
    let := hLHfin
    let : ∀ j, Algebra K (H j) := fun j =>
      ((algebraMap K₁ (H j)).comp (algebraMap K K₁)).toAlgebra
    let : ∀ j, IsScalarTower K K₁ (H j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    let : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
      Ideal.Quotient.algebra K₁
    let eH' := reducedTensorFactorsEquiv K L K₁ D.L₁ H D.eL₁ eH D.eL₁_right heH
    have heHleft (j : Fin n) (x : L) :
        eH' (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x)) j =
            algebraMap L (H j) x :=
      reducedTensorFactorsEquiv_left K L K₁ D.L₁ H D.eL₁ eH
        D.eL₁_right heH D.eL₁_left x j
    have heHright (j : Fin n) (x : K₁) :
        eH' (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) j =
            algebraMap K₁ (H j) x := by
      show eH' (algebraMap K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) x) j = _
      rw [eH'.commutes]
      rfl
    let : ∀ j, IsScalarTower K L (H j) := fun j =>
      IsScalarTower.of_algebraMap_eq fun x => by
        have ht : (algebraMap K L x) ⊗ₜ[K] (1 : K₁) =
            (1 : L) ⊗ₜ[K] algebraMap K K₁ x := by
          show (Algebra.TensorProduct.includeLeft : L →ₐ[K] _) (algebraMap K L x) =
            (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] _) (algebraMap K K₁ x)
          rw [AlgHom.commutes, AlgHom.commutes]
        have hx := congrArg (fun t => eH' (Ideal.Quotient.mk _ t) j) ht
        change eH' (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁)
              (algebraMap K L x))) j =
          eH' (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
              (algebraMap K K₁ x))) j at hx
        rw [heHleft, heHright] at hx
        exact hx.symm
    let : Algebra K₁ (M ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    let phi (i : Fin m) : (M ⊗[K] K₁) →ₐ[K₁] F i :=
      { __ := ((Pi.evalAlgHom K F i).comp decomp.toAlgHom).toRingHom.comp
          (Ideal.Quotient.mk _)
        commutes' x := hright i x }
    have hphi (i : Fin m) (x : M) (y : K₁) :
        phi i (x ⊗ₜ[K] y) = algebraMap M (F i) x * algebraMap K₁ (F i) y := by
      rw [show x ⊗ₜ[K] y = (x ⊗ₜ[K] (1 : K₁)) * ((1 : M) ⊗ₜ[K] y) by
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul]
      show decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : M →ₐ[K] M ⊗[K] K₁) x)) i *
          decomp (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] M ⊗[K] K₁) y)) i = _
      rw [hleft, hright]
    have hphisurj (i : Fin m) : Function.Surjective (phi i) := by
      have hev : Function.Surjective (Pi.evalAlgHom K F i) := fun x =>
        ⟨Pi.single i x, by simp⟩
      exact hev.comp (decomp.surjective.comp Ideal.Quotient.mk_surjective)
    have hfac (i : Fin m) :=
      exists_fieldFactor_normal_and_finrank_le K L M K₁ (F i) H eH' heHleft
        (phi i) (hphi i) (hphisurj i)
    choose j g hLHF hfinHF hnormalHF hboundHF using hfac
    let : ∀ i, Algebra (H (j i)) (F i) := fun i => (g i).toRingHom.toAlgebra
    let : ∀ i, IsScalarTower L (H (j i)) (F i) := hLHF
    let : ∀ i, IsScalarTower K₁ (H (j i)) (F i) := fun i =>
      IsScalarTower.of_algHom (g i)
    let := hfinHF
    let : ∀ j, Algebra B (H j) := fun j =>
      ((algebraMap L (H j)).comp (algebraMap B L)).toAlgebra
    let : ∀ j, IsScalarTower B L (H j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ j, Algebra A (H j) := fun j =>
      ((algebraMap B (H j)).comp (algebraMap A B)).toAlgebra
    let : ∀ j, IsScalarTower A B (H j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ i, Algebra R (F i) := fun i =>
      ((algebraMap K₁ (F i)).comp (algebraMap R K₁)).toAlgebra
    let : ∀ i, IsScalarTower R K₁ (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    let : ∀ i, IsScalarTower A R (F i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A C K M K₁ F
          decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (F i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    let : ∀ i, IsScalarTower B (H (j i)) (F i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply B L (F i),
          IsScalarTower.algebraMap_apply L (H (j i)) (F i),
          ← IsScalarTower.algebraMap_apply B L (H (j i))]
    have hweakLower :=
      isWeaklyUnramified_integralClosure_factor_of_perfectResidue
        A B K L K₁ R hweak H (eH'.restrictScalars K) heHleft heHright
    intro i
    let E := H (j i)
    let FF := F i
    let T := integralClosure C FF
    let : Algebra R E :=
      ((algebraMap K₁ E).comp (algebraMap R K₁)).toAlgebra
    let : IsScalarTower R K₁ E := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower A K₁ E := IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap B E (algebraMap A B a) =
        algebraMap K₁ E (algebraMap A K₁ a)
      exact algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ H
        (eH'.restrictScalars K) heHleft heHright (j i) a
    let : FaithfulSMul R E :=
      (faithfulSMul_iff_algebraMap_injective R E).mpr
        ((algebraMap K₁ E).injective.comp (IsFractionRing.injective R K₁))
    let : IsScalarTower A R E := IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A K₁ E,
        IsScalarTower.algebraMap_apply A R K₁]
      rfl
    let S := integralClosure B E
    let : IsDiscreteValuationRing S := isDiscreteValuationRing_integralClosure_factor B L E
    let : Algebra R S := algebraIntegralClosureBase A B R E
    let : IsFractionRing S E := isFractionRing_integralClosure_factor B L E
    let : IsScalarTower R S E := isScalarTower_base_integralClosure_factor A B R E
    let : IsDiscreteValuationRing.IsExtension R S :=
      isExtension_base_integralClosure_factor A B R L E
    let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply A B E a)
    let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.ext
      show algebraMap B E (algebraMap A B a) =
        algebraMap K₁ E (algebraMap R K₁ (algebraMap A R a))
      rw [← IsScalarTower.algebraMap_apply A B E,
        ← IsScalarTower.algebraMap_apply A R K₁,
        ← IsScalarTower.algebraMap_apply A K₁ E]
    obtain ⟨_, _, _, hScomplete, _⟩ := integralClosure_isCompleteDVR B L E
    let : IsAdicComplete (maximalIdeal S) S := hScomplete
    let : IsDiscreteValuationRing T := isDiscreteValuationRing_integralClosure_factor C M FF
    let : FaithfulSMul R FF :=
      (faithfulSMul_iff_algebraMap_injective R FF).mpr
        ((algebraMap K₁ FF).injective.comp (IsFractionRing.injective R K₁))
    let : Algebra R T := algebraIntegralClosureBase A C R FF
    let : IsFractionRing T FF := isFractionRing_integralClosure_factor C M FF
    let : IsScalarTower R T FF := isScalarTower_base_integralClosure_factor A C R FF
    let : IsDiscreteValuationRing.IsExtension R T :=
      isExtension_base_integralClosure_factor A C R M FF
    let : Algebra S FF :=
      ((algebraMap E FF).comp (algebraMap S E)).toAlgebra
    let hSEFFTower : IsScalarTower S E FF := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower S E FF := hSEFFTower
    let : IsScalarTower B E FF := IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply B L (F i),
        IsScalarTower.algebraMap_apply B L E,
        IsScalarTower.algebraMap_apply L E FF]
    let : IsScalarTower R E FF := IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R K₁ FF,
        IsScalarTower.algebraMap_apply R K₁ E,
        IsScalarTower.algebraMap_apply K₁ E FF]
    let hRSFFTower : IsScalarTower R S FF := IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap K₁ FF (algebraMap R K₁ r) =
        algebraMap E FF (algebraMap S E (algebraMap R S r))
      rw [IsScalarTower.algebraMap_apply K₁ E FF,
        ← IsScalarTower.algebraMap_apply R K₁ E,
        IsScalarTower.algebraMap_apply R S E]
    let : IsScalarTower R S FF := hRSFFTower
    let algST : Algebra S T := (mapIntegralClosureOfTower B C E FF).toRingHom.toAlgebra
    let : Algebra S T := algST
    let hSTFFTower : IsScalarTower S T FF := IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap E FF x.1 = algebraMap E FF x.1
      rfl
    let : IsScalarTower S T FF := hSTFFTower
    let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => by
      apply IsFractionRing.injective T FF
      exact (IsScalarTower.algebraMap_apply R T FF r).symm.trans
        ((@IsScalarTower.algebraMap_apply R S FF _ _ _ _ _ _ hRSFFTower r).trans
          (@IsScalarTower.algebraMap_apply S T FF _ _ _ _ _ _ hSTFFTower _))
    let : IsDiscreteValuationRing.IsExtension S T :=
      (integralClosure_factor_isExtension B C L M E FF).choose_spec.choose_spec.1
    obtain ⟨_, _, _, hTcomplete, _⟩ := integralClosure_isCompleteDVR C M FF
    let : IsAdicComplete (maximalIdeal T) T := hTcomplete
    let : IsLocalHom (algebraMap B S) := inferInstance
    let : IsLocalHom (algebraMap A S) := by
      rw [IsScalarTower.algebraMap_eq A B S]
      infer_instance
    let : IsLocalHom (algebraMap R S) := isLocalHom_algebraMap_of_tower A R S
    let : IsScalarTower S T FF := hSTFFTower
    have hweakRS : IsDiscreteValuationRing.IsWeaklyUnramified R S := by
      simpa only [S, E] using hweakLower (j i)
    have hAS := artinSchreierFactorPackage_of_matching_reducedFactors
      K L M K₁ E FF p hp xi z hz hgen (phi i).toRingHom (hphi i) (hphisurj i)
    dsimp only at hAS
    rcases hAS with ⟨hzF, hgenF, hfinEF, hdegreeF⟩
    let := hfinEF
    rcases hdegreeF with ⟨hdegreeOne, hsurjEF⟩ | ⟨hdegreeP, hgalEF⟩
    · let : Algebra S T := algST
      let : IsScalarTower S T FF := hSTFFTower
      refine ⟨K₁, inferInstance, inferInstance, inferInstance,
        inferInstance, Module.Finite.self K₁, ?_⟩
      let hweakRT := @isWeaklyUnramified_of_finrank_eq_one R S T K₁ E FF
        _ _ _ _ _ _ _ _ _ _ _ _
        _ algST _ _ _ _ _
        _ hSTFFTower hSEFFTower
        _ _ _ _ _ _ _
        hweakRS hdegreeOne
      exact ⟨canonicalBaseChange R T K₁ FF K₁,
        isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField R T K₁ FF K₁ _ hweakRT⟩
    · let : Algebra S T := algST
      let : IsScalarTower S T FF := hSTFFTower
      let : IsGalois E FF := hgalEF
      have hresMap :
          (algebraMap (ResidueField B) (ResidueField S)) =
            IsLocalRing.ResidueField.map (algebraMap B S) := by
        refine RingHom.ext fun y => ?_
        obtain ⟨b₀, rfl⟩ := IsLocalRing.residue_surjective y
        rw [IsLocalRing.ResidueField.algebraMap_residue]
        exact (RingHom.congr_fun
          (IsLocalRing.ResidueField.map_comp_residue (algebraMap B S)) b₀).symm
      choose rootBase hrootBase using
        exists_imp_of_forall_mem_exists (Finset.range N) (fun k (r : ResidueField R) =>
          algebraMap (ResidueField R) (ResidueField S) r =
            IsLocalRing.ResidueField.map (algebraMap B S) (rootCoeff k)) fun k hk => by
          obtain ⟨r, hr⟩ := habs (ULift.up ()) (ResidueField S)
            (rootCoeff k) (Finset.mem_image_of_mem rootCoeff hk)
          exact ⟨r, by simpa only [pow_zero, pow_one, ← hresMap] using hr⟩
      exact exists_finite_extension_isWeakSolution_of_reentered_constant_laurent
        (algST := algST) (hSTF := hSTFFTower) (hSEF := hSEFFTower)
        p A B R S T K₁ L E FF hweakAR hweakRS
        (fun x => by
          show algebraMap L E (algebraMap B L x) = algebraMap S E (algebraMap B S x)
          rw [← IsScalarTower.algebraMap_apply B L E,
            ← IsScalarTower.algebraMap_apply B S E])
        pi hpi N lift hlift liftMod hliftMod coeff rootCoeff hrootCoeff rootBase hrootBase
        xi b hexp
        ((Algebra.TensorProduct.lift (Algebra.ofId E FF)
          (IsScalarTower.toAlgHom L M FF) (fun _ _ => .all _ _)) (1 ⊗ₜ[L] z))
        hzF hgenF

/-- **The equal-characteristic wild prime-degree solver.**

If an Artin--Schreier generator has integral parameter, Tag 09F0 makes the upper DVR weakly
unramified already, so the trivial base extension solves the layer.  Otherwise the prepared
Artin--Schreier alternative either supplies a solution directly or produces constant-Laurent
data.  The latter is discharged by the all-conjugates theorem above. -/
theorem exists_finite_extension_isWeakSolution_of_wild_charP
    (p : ℕ) (hp : p.Prime) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharP K p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    [Module.Finite L M] [IsGalois L M]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hepp : EppCondition A B p)
    (hdegree : Module.finrank L M = p) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution := by
  classical
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  by_cases hram : ∀ (η : L) (w : M), w ^ p - w = algebraMap L M η →
      Algebra.adjoin L {w} = ⊤ → η ∉ (algebraMap B L).range
  · rcases exists_finite_extension_isWeakSolution_or_constant_laurent_of_charP
        A B C K L M p hp hdegree hweak hram with hsol | hconstant
    · exact hsol
    · rcases hconstant with
        ⟨pi, N, xi, z, lift, liftMod, coeff, b, hpi, hN, hz, hgen,
          hlift, hliftMod, hexp, _hminimal, hperfect⟩
      exact exists_finite_extension_isWeakSolution_of_constant_laurent_of_charP
        p hp A B C K L M hweak hepp pi hpi N hN xi z lift hlift liftMod
        hliftMod coeff b hz hgen hexp hperfect
  · push Not at hram
    obtain ⟨xi, z, hz, hgen, hxi⟩ := hram
    obtain ⟨b, hb⟩ := hxi
    have hweakBC : IsDiscreteValuationRing.IsWeaklyUnramified B C :=
      isWeaklyUnramified_of_artinSchreier_integral B C L M p hp hdegree
        xi z hz hgen ⟨b, hb.symm⟩
    have hweakAC : IsDiscreteValuationRing.IsWeaklyUnramified A C :=
      isWeaklyUnramified_trans A B C hweak hweakBC
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.Finite.self K, canonicalBaseChange A C K M K, ?_⟩
    exact isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField
      A C K M K _ hweakAC

end Stacks.EppTheorem

end
