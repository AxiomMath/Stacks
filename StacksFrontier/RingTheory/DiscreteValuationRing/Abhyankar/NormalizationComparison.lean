module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AwayLocalizationField

/-!
# Abhyankar's lemma: normality of the reduced tensor product and comparison with the integral closure

The end of the namespace `ReducedTensorLocalization`: flatness of the reduced tensor product, the
fact that every localization of the reduced tensor product at a maximal ideal is a discrete
valuation ring, and the resulting normality of the reduced tensor product.

Then the first part of the namespace `IntegralClosureComparison`: the reduced tensor product and the
integral closure of `B` in the reduced compositum have the same total fraction ring, and the
comparison map from the reduced tensor product to that integral closure is surjective when the
reduced tensor product is normal.

## References

* [The Stacks Project, Tag 09EQ](https://stacks.math.columbia.edu/tag/09EQ)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁

open scoped TensorProduct

noncomputable section

namespace ReducedTensorLocalization

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem regular_in_quotient_nilradical
    (S : Type*) [CommRing S] (π : S) (hπ : π ∈ nonZeroDivisors S) :
    Ideal.Quotient.mk (nilradical S) π ∈
      nonZeroDivisors (S ⧸ nilradical S) := by
  refine mem_nonZeroDivisors_iff_left.mpr ?_
  intro y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpx : π * x ∈ nilradical S := Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa only [map_mul] using hy)
  obtain ⟨n, hn⟩ := mem_nilradical.mp hpx
  have hpxn : π ^ n * x ^ n = 0 := by simpa only [mul_pow] using hn
  have hxn : x ^ n = 0 :=
    (mem_nonZeroDivisors_iff_left.mp ((nonZeroDivisors S).pow_mem hπ n)) _ hpxn
  exact mem_nilradical.mpr ⟨n, hxn⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem flat_tensor_of_dvr_extension
    (A B D : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [CommRing D] [Algebra A D] :
    Module.Flat D (B ⊗[A] D) := by
  have : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A B)
  have : Module.Flat A B := inferInstance
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight A D B).symm.toLinearEquiv

/-- Over a flat algebra, the image of a nonzerodivisor is a nonzerodivisor. -/
private theorem algebraMap_mem_nonZeroDivisors_of_flat
    (D S : Type*) [CommRing D] [CommRing S] [Algebra D S] [Module.Flat D S]
    {r : D} (hr : r ∈ nonZeroDivisors D) : algebraMap D S r ∈ nonZeroDivisors S := by
  refine mem_nonZeroDivisors_iff_left.mpr fun x hx => ?_
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors hr).right_eq_zero_of_smul
    (by simpa only [Algebra.smul_def] using hx)

private theorem flat_nilradical_quotient_of_flat_over_dedekind
    (D S : Type*) [CommRing D] [IsDedekindDomain D]
    [CommRing S] [Algebra D S] [Module.Flat D S] :
    Module.Flat D (S ⧸ nilradical S) := by
  have : Module.IsTorsionFree D (S ⧸ nilradical S) := by
    refine ⟨fun r hr => ?_⟩
    have hrD : r ∈ nonZeroDivisors D := mem_nonZeroDivisors_iff_ne_zero.mpr hr.ne_zero
    have hrQ := regular_in_quotient_nilradical S (algebraMap D S r)
      (algebraMap_mem_nonZeroDivisors_of_flat D S hrD)
    refine isSMulRegular_iff_right_eq_zero_of_smul.mpr ?_
    intro x hx
    have hsquare : algebraMap D (S ⧸ nilradical S) r =
        Ideal.Quotient.mk (nilradical S) (algebraMap D S r) :=
      IsScalarTower.algebraMap_apply D S (S ⧸ nilradical S) r
    exact (mem_nonZeroDivisors_iff_left.mp hrQ) x
      (by simpa only [Algebra.smul_def, hsquare] using hx)
  infer_instance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem flat_reduced_tensor_of_dvr_extension
    (A B D : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [CommRing D] [IsDedekindDomain D] [Algebra A D] :
    Module.Flat D ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) := by
  let : Module.Flat D (B ⊗[A] D) := flat_tensor_of_dvr_extension A B D
  exact flat_nilradical_quotient_of_flat_over_dedekind D (B ⊗[A] D)

private theorem regular_local_parameter_after_flat_localization
    (D R : Type*) [CommRing D] [CommRing R] [Algebra D R] [Module.Flat D R]
    (m : Ideal D) [m.IsPrime] (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
    [IsScalarTower D (Localization.AtPrime m) (Localization.AtPrime q)]
    (π : Localization.AtPrime m) (hπ : π ∈ nonZeroDivisors (Localization.AtPrime m)) :
    algebraMap (Localization.AtPrime m) (Localization.AtPrime q) π ∈
      nonZeroDivisors (Localization.AtPrime q) := by
  have : Module.Flat R (Localization.AtPrime q) :=
    IsLocalization.flat (Localization.AtPrime q) q.primeCompl
  have : Module.Flat D (Localization.AtPrime q) :=
    Module.Flat.trans D R (Localization.AtPrime q)
  have : Module.Flat (Localization.AtPrime m) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime m) m.primeCompl
      (Localization.AtPrime q)).mpr
      (inferInstance : Module.Flat D (Localization.AtPrime q))
  exact algebraMap_mem_nonZeroDivisors_of_flat _ _ hπ

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem regular_selected_reduced_tensor_branch
    (A B D : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [CommRing D] [IsDedekindDomain D] [Algebra A D]
    (m : Ideal D) [m.IsPrime]
    (q : Ideal ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D))) [q.IsPrime]
    (algebraLoc : Algebra (Localization.AtPrime m) (Localization.AtPrime q))
    (hcomp : letI := algebraLoc
      ∀ c : D,
        algebraMap (Localization.AtPrime m) (Localization.AtPrime q)
          (algebraMap D (Localization.AtPrime m) c) =
        algebraMap ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) (Localization.AtPrime q)
          (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) c)))
    (π : Localization.AtPrime m) (hπ : π ∈ nonZeroDivisors (Localization.AtPrime m)) :
    letI := algebraLoc
    algebraMap (Localization.AtPrime m) (Localization.AtPrime q) π ∈
      nonZeroDivisors (Localization.AtPrime q) := by
  let R := (B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)
  let T := Localization.AtPrime q
  let : Algebra (Localization.AtPrime m) T := algebraLoc
  have hTower : IsScalarTower D (Localization.AtPrime m) T :=
    IsScalarTower.of_algebraMap_eq fun c => (hcomp c).symm
  let : IsScalarTower D (Localization.AtPrime m) T := hTower
  let : Module.Flat D R := flat_reduced_tensor_of_dvr_extension A B D
  exact regular_local_parameter_after_flat_localization D R m q π hπ

private theorem actual_selected_reduced_branch_isDVR
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (L₁ : Type uL₁) (A₁ : Type uA₁) (B₁ : Type uB₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hformal : RingHom.FormallySmoothNAdic.{max uA uB}
      (algebraMap A B) (IsLocalRing.maximalIdeal B))
    (q : Ideal B₁) [q.IsMaximal] :
    let S := B ⊗[A] A₁
    let R := S ⧸ nilradical S
    let m := q.comap (algebraMap A₁ B₁)
    let I : Ideal S := m.map
      (Algebra.TensorProduct.includeRight (R := A) (A := B))
    ∃ g : S →+* B₁, g.IsIntegral ∧ RingHom.ker g ≤ nilradical S ∧
      (∀ b : B,
        g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] S) b) =
          algebraMap B B₁ b) ∧
      (∀ a : A₁,
        g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) a) =
          algebraMap A₁ B₁ a) ∧
      ∃ rRed : Ideal R, ∃ _ : rRed.IsPrime,
      rRed.comap (Ideal.Quotient.mk (nilradical S)) = q.comap g ∧
      IsField (Localization.AtPrime rRed ⧸
        (I.map (Ideal.Quotient.mk (nilradical S))).map
          (algebraMap R (Localization.AtPrime rRed))) ∧
      ∃ algebraLoc : Algebra (Localization.AtPrime m) (Localization.AtPrime rRed),
        letI := algebraLoc
        ∃ π : Localization.AtPrime m, Irreducible π ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime rRed) =
            Ideal.span {algebraMap (Localization.AtPrime m) (Localization.AtPrime rRed) π} ∧
          IsArtinianRing (Localization.Away
            (algebraMap (Localization.AtPrime m) (Localization.AtPrime rRed) π)) ∧
          IsReduced (Localization.Away
            (algebraMap (Localization.AtPrime m) (Localization.AtPrime rRed) π)) ∧
          (∃ _ : IsDomain (Localization.AtPrime rRed),
            IsDiscreteValuationRing (Localization.AtPrime rRed)) := by
  let S := B ⊗[A] A₁
  let R := S ⧸ nilradical S
  let m : Ideal A₁ := q.comap (algebraMap A₁ B₁)
  have hEM := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare
  let : IsDedekindDomain A₁ := hEM.2.1
  let : IsDomain A₁ := IsDedekindDomain.toIsDomain
  obtain ⟨πA, hmaxA, _, ⟨genericIso, _, _⟩, _⟩ := hEM.2.2.2.1
  have hπA0 : πA ≠ 0 := by
    intro hz
    have hmax0 : IsLocalRing.maximalIdeal A = ⊥ := by simpa [hz] using hmaxA
    exact IsDiscreteValuationRing.not_isField A
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax0)
  have hπAIrr : Irreducible πA :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal πA hπA0 hmaxA
  obtain ⟨g, hIntegral, hNil, hleft, hright, hm, ⟨hDdomain, hDdvr⟩, rRed, hRedPrime,
      hPrime, hfieldRed, _, _, hprincipal⟩ :=
    actual_09EM_reduced_branch_specialFiber_isField
      A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
        hfieldSquare hringSquare hformal q
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  let : IsDomain (Localization.AtPrime m) := hDdomain
  let : IsDiscreteValuationRing (Localization.AtPrime m) := hDdvr
  obtain ⟨algebraLoc, hcomp, π, hπ, hmax⟩ := hprincipal
  obtain ⟨_, hExt⟩ := local_extension_equivalentClosure A K K₁ A₁ eA₁ m
  let : IsExtension A (Localization.AtPrime m) := hExt
  let : rRed.IsPrime := hRedPrime
  have hgeneric := selected_branch_away_artinian_of_base_extension
    A B A₁ K L K₁ m rRed algebraLoc hcomp πA hπAIrr genericIso π hπ
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime rRed) := algebraLoc
  let parameter : Localization.AtPrime rRed :=
    algebraMap (Localization.AtPrime m) (Localization.AtPrime rRed) π
  have hreg : parameter ∈ nonZeroDivisors (Localization.AtPrime rRed) :=
    regular_selected_reduced_tensor_branch A B A₁ m rRed algebraLoc hcomp π
      (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero)
  let : IsArtinianRing (Localization.Away parameter) := hgeneric.1
  let : IsReduced (Localization.Away parameter) := hgeneric.2
  have hfield : IsField (Localization.Away parameter) :=
    away_field_of_artinian (Localization.AtPrime rRed) parameter hreg hmax
  have hDVR := dvr_of_regular_principal_and_field_away
    (Localization.AtPrime rRed) parameter hreg hmax hfield
  exact ⟨g, hIntegral, hNil, hleft, hright, rRed, hRedPrime, hPrime, hfieldRed,
    algebraLoc, π, hπ,
    hmax, hgeneric.1, hgeneric.2, hDVR⟩

private theorem actual_every_reduced_maximal_isDVR
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (L₁ : Type uL₁) (A₁ : Type uA₁) (B₁ : Type uB₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hformal : RingHom.FormallySmoothNAdic.{max uA uB}
      (algebraMap A B) (IsLocalRing.maximalIdeal B))
    (mRed : Ideal ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁))) [mRed.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime mRed),
      IsDiscreteValuationRing (Localization.AtPrime mRed) := by
  let S := B ⊗[A] A₁
  let mk : S →+* (S ⧸ nilradical S) := Ideal.Quotient.mk (nilradical S)
  have hEM := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare
  obtain ⟨_, _, _, _, g₀, hIntegral₀, hNil₀, _, hleft₀, hright₀⟩ := hEM.2.2.2.1
  have hker : RingHom.ker g₀ ≤ mRed.comap mk := by
    intro x hx
    show mk x ∈ mRed
    have hzero : mk x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hNil₀ hx)
    rw [hzero]
    exact mRed.zero_mem
  let : (mRed.comap mk).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective mk Ideal.Quotient.mk_surjective
  let : Algebra S B₁ := g₀.toAlgebra
  let : Algebra.IsIntegral S B₁ := ⟨hIntegral₀⟩
  obtain ⟨q, hq, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (mRed.comap mk) hker
  let : q.IsMaximal := hq
  obtain ⟨g, _, _, hleft, hright, rRed, hRedPrime, hcontract, _, _, _, _, _, _, _, hDVR⟩ :=
    actual_selected_reduced_branch_isDVR A B K L K₁ L₁ A₁ B₁
      eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe hfieldSquare hringSquare hformal q
  have hg : g = g₀ := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext b
      exact (hleft b).trans (hleft₀ b).symm
    · ext d
      exact (hright d).trans (hright₀ d).symm
  have hRedEq : rRed = mRed :=
    Ideal.comap_injective_of_surjective mk Ideal.Quotient.mk_surjective (by
      calc
        _ = q.comap g := hcontract
        _ = q.comap g₀ := by rw [hg]
        _ = _ := hc)
  rcases hDVR with ⟨hDomain, hDVR⟩
  subst rRed
  exact ⟨hDomain, hDVR⟩

private theorem normalRing_of_dvr_maximal_localizations
    (R : Type*) [CommRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      ∃ _ : IsDomain (Localization.AtPrime m),
        IsDiscreteValuationRing (Localization.AtPrime m)) :
    IsNormalRing R := by
  refine isNormalRing_iff.mpr fun p hp => ?_
  let : p.IsPrime := hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top hp)
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  obtain ⟨hdomain, hdvr⟩ := h m
  let : IsDomain (Localization.AtPrime m) := hdomain
  let : IsDiscreteValuationRing (Localization.AtPrime m) := hdvr
  have hclosed : IsIntegrallyClosed (Localization.AtPrime m) := inferInstance
  let q : Ideal (Localization.AtPrime m) := p.map (algebraMap R (Localization.AtPrime m))
  let : q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m hpm
  have hcontract : q.comap (algebraMap R (Localization.AtPrime m)) = p :=
    Ideal.under_map_of_isLocalizationAtPrime m hpm
  have hlocal : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have hlocal' : IsLocalization.AtPrime (Localization.AtPrime q)
        (q.comap (algebraMap R (Localization.AtPrime m))) := inferInstance
    simpa only [hcontract] using hlocal'
  let : IsLocalization.AtPrime (Localization.AtPrime q) p := hlocal
  let : IsIntegrallyClosed (Localization.AtPrime m) := hclosed
  have hclosedq : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization
      (Localization.AtPrime q) q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsIntegrallyClosed (Localization.AtPrime q) := hclosedq
  let e : Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact ⟨Function.Injective.isDomain e.toRingHom e.injective,
    IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩

theorem actual_normal_ring_reduced_tensor
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (L₁ : Type uL₁) (A₁ : Type uA₁) (B₁ : Type uB₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hformal : RingHom.FormallySmoothNAdic.{max uA uB}
      (algebraMap A B) (IsLocalRing.maximalIdeal B)) :
    IsNormalRing ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁)) := by
  apply normalRing_of_dvr_maximal_localizations
  intro mRed hmRed
  let : mRed.IsMaximal := hmRed
  exact actual_every_reduced_maximal_isDVR A B K L K₁ L₁ A₁ B₁
    eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe hfieldSquare hringSquare hformal mRed

end ReducedTensorLocalization

namespace IntegralClosureComparison


private theorem integral_baseChange_surjective_of_closed_generic
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [FaithfulSMul S T]
    [Algebra.IsIntegral R S] [IsIntegrallyClosedIn R T] :
    Function.Surjective (algebraMap R S) := by
  intro y
  have hint : IsIntegral R (algebraMap S T y) :=
    (Algebra.IsIntegral.isIntegral y).map (IsScalarTower.toAlgHom R S T)
  obtain ⟨x, hx⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := R) (A := T)).mp hint
  refine ⟨x, ?_⟩
  apply FaithfulSMul.algebraMap_injective S T
  simpa only [← IsScalarTower.algebraMap_apply R S T] using hx

/-- The nilradical lies in the kernel of any ring map to a reduced ring. -/
private theorem nilradical_le_ker_of_isReduced
    (S W : Type*) [CommRing S] [CommRing W] [IsReduced W] (g : S →+* W) :
    nilradical S ≤ RingHom.ker g := fun _ hs =>
  RingHom.mem_ker.mpr (isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp hs).map g))

private theorem integral_of_quotient_lift
    (R S : Type*) [CommRing R] [CommRing S]
    (g : R →+* S) (hg : g.IsIntegral) (I : Ideal R)
    (hI : I ≤ RingHom.ker g) :
    (Ideal.Quotient.lift I g
      (fun _x hx => RingHom.mem_ker.mp (hI hx))).IsIntegral := by
  let gRed : (R ⧸ I) →+* S :=
    Ideal.Quotient.lift I g (fun x hx => RingHom.mem_ker.mp (hI hx))
  have hcomp : gRed.comp (Ideal.Quotient.mk I) = g := by
    ext x
    rfl
  have hLift : (gRed.comp (Ideal.Quotient.mk I)).IsIntegral := by
    simpa only [hcomp] using hg
  exact RingHom.IsIntegral.tower_top (Ideal.Quotient.mk I) gRed hLift

private theorem integrallyClosedIn_generic_of_normal
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (hNormal : IsNormalRing R)
    (e : FractionRing R ≃ₐ[R] T) : IsIntegrallyClosedIn R T := by
  let : IsIntegrallyClosedIn R (FractionRing R) :=
    hNormal.isIntegrallyClosed
  have hinj : Function.Injective (algebraMap R T) := by
    intro x y h
    apply (IsFractionRing.injective R (FractionRing R))
    apply e.injective
    simpa only [e.commutes] using h
  refine ⟨hinj, ?_⟩
  intro x
  constructor
  · intro hx
    have hx' : IsIntegral R (e.symm x) := hx.map e.symm.toAlgHom
    obtain ⟨r, hr⟩ := (IsIntegrallyClosedIn.isIntegral_iff
      (R := R) (A := FractionRing R)).mp hx'
    refine ⟨r, ?_⟩
    have he := congrArg e hr
    simpa only [e.commutes, e.apply_symm_apply] using he
  · rintro ⟨r, rfl⟩
    exact isIntegral_algebraMap

private theorem localization_map_nilradical
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (M : Submonoid R) [IsLocalization M T] :
    (nilradical R).map (algebraMap R T) = nilradical T := by
  simpa [nilradical] using
    (IsLocalization.map_radical (S := T) M (⊥ : Ideal R))

private theorem reduced_away_quotient_isLocalization
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (π : R) [IsLocalization.Away π T] :
    IsLocalization.Away (Ideal.Quotient.mk (nilradical R) π)
      (T ⧸ (nilradical R).map (algebraMap R T)) := by
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    Ideal.Quotient.algebraMap_eq] using
    (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ nilradical R) (Submonoid.powers π))
      (T ⧸ (nilradical R).map (algebraMap R T)))

private noncomputable def reductionRingEquiv_of_ringEquiv
    (T U : Type*) [CommRing T] [CommRing U] (e : T ≃+* U) :
    (T ⧸ nilradical T) ≃+* (U ⧸ nilradical U) := by
  have hker : RingHom.ker (e : T →+* U) ≤ (⊥ : Ideal T) := by
    rw [(RingHom.injective_iff_ker_eq_bot (e : T →+* U)).mp e.injective]
  have heq : nilradical U = (nilradical T).map (e : T →+* U) := by
    simpa [nilradical] using
      (Ideal.map_radical_of_surjective (f := (e : T →+* U))
        e.surjective (I := ⊥) hker).symm
  exact Ideal.quotientEquiv (nilradical T) (nilradical U) e heq

private theorem reduced_away_target_isLocalization
    (R T U V : Type*) [CommRing R] [CommRing T] [CommRing U] [CommRing V]
    [Algebra R T] (π : R) [IsLocalization.Away π T]
    (e : T ≃+* U) (eV : V ≃+* (U ⧸ nilradical U)) :
    let I := (nilradical R).map (algebraMap R T)
    let h : (T ⧸ I) ≃+* V :=
      (Ideal.quotEquivOfEq (localization_map_nilradical R T (Submonoid.powers π))).trans
        ((reductionRingEquiv_of_ringEquiv T U e).trans eV.symm)
    letI : Algebra (R ⧸ nilradical R) V :=
      (h.toRingHom.comp (algebraMap (R ⧸ nilradical R) (T ⧸ I))).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (nilradical R) π) V := by
  intro I h
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (Submonoid.powers (Ideal.Quotient.mk (nilradical R) π)) h).mp
      (reduced_away_quotient_isLocalization R T π)

private theorem isFractionRing_of_away_cofinal
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (π : R) (hreg : π ∈ nonZeroDivisors R)
    [IsLocalization.Away π T]
    (hcofinal : ∀ s : R, s ∈ nonZeroDivisors R → ∃ n : ℕ, s ∣ π ^ n) :
    IsFractionRing R T := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers π)
    (nonZeroDivisors R) ?_ ?_).mp inferInstance
  · rintro s ⟨n, rfl⟩
    exact pow_mem hreg n
  · intro s hs
    obtain ⟨n, hn⟩ := hcofinal s hs
    exact ⟨π ^ n, ⟨n, rfl⟩, hn⟩

private noncomputable def totalFractionEquiv_of_artinian_away_target
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (π : R) (hreg : π ∈ nonZeroDivisors R)
    [IsLocalization.Away π T] [IsArtinianRing T] :
    FractionRing R ≃ₐ[R] T := by
  letI : IsFractionRing R T := isFractionRing_of_away_cofinal R T π hreg
    (fun s hs => by
      have hregT : algebraMap R T s ∈ nonZeroDivisors T :=
        IsLocalization.nonZeroDivisors_le_comap (S := T) (Submonoid.powers π) hs
      exact (IsLocalization.Away.algebraMap_isUnit_iff π).mp
        (IsArtinianRing.isUnit_of_mem_nonZeroDivisors hregT))
  exact IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) T

private theorem artinian_reduced_generic_target
    (K L E U : Type*) [Field K] [Field L] [Field E] [CommRing U]
    [Algebra K L] [Algebra K E] [Module.Finite K E]
    (e : U ≃+* ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))) :
    IsArtinianRing U := by
  have : Module.Finite L (L ⊗[K] E) := inferInstance
  have : IsArtinianRing (L ⊗[K] E) := IsArtinianRing.of_finite L _
  have : IsArtinianRing ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) := inferInstance
  exact e.symm.isArtinianRing

private theorem reduced_away_action_compatible
    (S T U V W : Type*) [CommRing S] [CommRing T] [CommRing U]
    [CommRing V] [CommRing W] [Algebra S T] [Algebra W V]
    (π : S) [IsLocalization.Away π T]
    (e : T ≃+* U) (eV : V ≃+* (U ⧸ nilradical U))
    (g : S →+* W)
    (hcompat : ∀ s : S,
      Ideal.Quotient.mk (nilradical U) (e (algebraMap S T s)) =
        eV (algebraMap W V (g s))) :
    let I := (nilradical S).map (algebraMap S T)
    let eRed : (T ⧸ I) ≃+* V :=
      (Ideal.quotEquivOfEq (localization_map_nilradical S T (Submonoid.powers π))).trans
        ((reductionRingEquiv_of_ringEquiv T U e).trans eV.symm)
    letI : Algebra (S ⧸ nilradical S) V :=
      (eRed.toRingHom.comp (algebraMap (S ⧸ nilradical S) (T ⧸ I))).toAlgebra
    ∀ s : S, algebraMap (S ⧸ nilradical S) V
        (Ideal.Quotient.mk (nilradical S) s) = algebraMap W V (g s) := by
  intro I eRed s
  show eRed (algebraMap (S ⧸ nilradical S) (T ⧸ I)
    (Ideal.Quotient.mk (nilradical S) s)) = algebraMap W V (g s)
  show eRed (Ideal.Quotient.mk I (algebraMap S T s)) = algebraMap W V (g s)
  apply eV.injective
  simpa only [I, eRed, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
    reductionRingEquiv_of_ringEquiv,
    Ideal.quotientEquiv_mk, Ideal.quotEquivOfEq_mk] using hcompat s

private theorem generic_tensor_action_compatible
    (A B K L K₁ L₁ A₁ B₁ : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra A A₁] [Algebra A₁ B₁]
    [Algebra B B₁] [Algebra B L₁] [Algebra B₁ L₁]
    [Algebra K L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [IsScalarTower B L L₁] [IsScalarTower B B₁ L₁]
    (πA : A) (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (genericIso : Localization.Away (algebraMap A (B ⊗[A] A₁) πA) ≃+*
      L ⊗[K] K₁)
    (hleft : ∀ b : B,
      genericIso (algebraMap (B ⊗[A] A₁) _
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) b)) =
        (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁)
          (algebraMap B L b))
    (hright : ∀ a : A₁,
      genericIso (algebraMap (B ⊗[A] A₁) _
        ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a)) =
        (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
          ((eA₁ a : integralClosure A K₁) : K₁))
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (g : (B ⊗[A] A₁) →+* B₁)
    (hgB : ∀ b : B,
      g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) b) =
        algebraMap B B₁ b)
    (hgA : ∀ a : A₁,
      g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a) =
        algebraMap A₁ B₁ a)
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁)) :
    ∀ s : B ⊗[A] A₁,
      Ideal.Quotient.mk (nilradical (L ⊗[K] K₁))
        (genericIso (algebraMap (B ⊗[A] A₁) _ s)) =
          eL₁ (algebraMap B₁ L₁ (g s)) := by
  have hcomp : (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁))).comp
      (genericIso.toRingHom.comp (algebraMap (B ⊗[A] A₁) _)) =
      eL₁.toRingHom.comp ((algebraMap B₁ L₁).comp g) := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext b
      show Ideal.Quotient.mk _
        (genericIso (algebraMap (B ⊗[A] A₁) _ (b ⊗ₜ[A] 1))) =
        eL₁ (algebraMap B₁ L₁ (g (b ⊗ₜ[A] 1)))
      calc
        _ = Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeLeft : L →ₐ[K]
            L ⊗[K] K₁) (algebraMap B L b)) := congrArg (Ideal.Quotient.mk _) (hleft b)
        _ = _ := by
          rw [show g (b ⊗ₜ[A] 1) = algebraMap B B₁ b from hgB b,
            ← IsScalarTower.algebraMap_apply B B₁ L₁,
            IsScalarTower.algebraMap_apply B L L₁, eL₁_left]
    · ext a
      show Ideal.Quotient.mk _
        (genericIso (algebraMap (B ⊗[A] A₁) _ (1 ⊗ₜ[A] a))) =
        eL₁ (algebraMap B₁ L₁ (g (1 ⊗ₜ[A] a)))
      calc
        _ = Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K]
            L ⊗[K] K₁) (eA₁ a).1) := congrArg (Ideal.Quotient.mk _) (hright a)
        _ = _ := by
          rw [show g (1 ⊗ₜ[A] a) = algebraMap A₁ B₁ a from hgA a,
            hringSquare, eL₁_right]
  intro s
  exact DFunLike.congr_fun hcomp s

private theorem actual_reduced_tensor_compatible_fractionRing
    (A B K L K₁ L₁ A₁ B₁ : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁)) :
    let S := B ⊗[A] A₁
    let R := S ⧸ nilradical S
    ∃ algebraLoc : Algebra R L₁,
      letI := algebraLoc
      ∃ g₀ : S →+* B₁, g₀.IsIntegral ∧
        RingHom.ker g₀ ≤ nilradical S ∧
        (∀ b : B, g₀
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] S) b) =
            algebraMap B B₁ b) ∧
        (∀ a : A₁, g₀
          ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) a) =
            algebraMap A₁ B₁ a) ∧
        (∀ s : S, algebraMap R L₁ (Ideal.Quotient.mk (nilradical S) s) =
          algebraMap B₁ L₁ (g₀ s)) ∧
        Nonempty (FractionRing R ≃ₐ[R] L₁) := by
  let S := B ⊗[A] A₁
  let R := S ⧸ nilradical S
  have hEM := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare
  obtain ⟨πA, _, hregular, ⟨genericIso, hleft, hright⟩,
    g₀, hIntegral, hker, _, hgB, hgA⟩ := hEM.2.2.2.1
  let πS : S := algebraMap A S πA
  let πR : R := Ideal.Quotient.mk (nilradical S) πS
  let T := Localization.Away πS
  let U := L ⊗[K] K₁
  let I : Ideal T := (nilradical S).map (algebraMap S T)
  let eRed : (T ⧸ I) ≃+* L₁ :=
    (Ideal.quotEquivOfEq (localization_map_nilradical S T (Submonoid.powers πS))).trans
      ((reductionRingEquiv_of_ringEquiv T U genericIso).trans eL₁.symm.toRingEquiv)
  let algebraLoc : Algebra R L₁ :=
    (eRed.toRingHom.comp (algebraMap R (T ⧸ I))).toAlgebra
  let : Algebra R L₁ := algebraLoc
  have hcompat : ∀ s : S, algebraMap R L₁ (Ideal.Quotient.mk _ s) =
      algebraMap B₁ L₁ (g₀ s) :=
    reduced_away_action_compatible S T U L₁ B₁ πS genericIso eL₁.toRingEquiv g₀
      (generic_tensor_action_compatible A B K L K₁ L₁ A₁ B₁ πA eA₁
        genericIso hleft hright eL₁ eL₁_left eL₁_right g₀ hgB hgA hringSquare)
  let : IsLocalization.Away πR L₁ :=
    reduced_away_target_isLocalization S T U L₁ πS genericIso eL₁.toRingEquiv
  have hregS : πS ∈ nonZeroDivisors S :=
    isRegular_iff_mem_nonZeroDivisors.mp hregular
  have hregR : πR ∈ nonZeroDivisors R :=
    ReducedTensorLocalization.regular_in_quotient_nilradical S πS hregS
  let : IsArtinianRing L₁ :=
    artinian_reduced_generic_target K L K₁ L₁ eL₁.toRingEquiv
  exact ⟨algebraLoc, g₀, hIntegral, hker, hgB, hgA, hcompat,
    ⟨totalFractionEquiv_of_artinian_away_target R L₁ πR hregR⟩⟩

private theorem reduced_integral_comparison_surjective_of_normal
    (S W V : Type*) [CommRing S] [CommRing W] [CommRing V]
    [IsReduced W] [Algebra W V]
    (algebraLoc : Algebra (S ⧸ nilradical S) V)
    (g : S →+* W) (hgIntegral : g.IsIntegral)
    (hcompat : letI := algebraLoc
      ∀ s : S, algebraMap (S ⧸ nilradical S) V
        (Ideal.Quotient.mk (nilradical S) s) = algebraMap W V (g s))
    (hinj : Function.Injective (algebraMap W V))
    (hNormal : IsNormalRing (S ⧸ nilradical S))
    (eFrac : letI := algebraLoc
      FractionRing (S ⧸ nilradical S) ≃ₐ[S ⧸ nilradical S] V) :
    let hnil : nilradical S ≤ RingHom.ker g := nilradical_le_ker_of_isReduced S W g
    let gRed : (S ⧸ nilradical S) →+* W :=
      Ideal.Quotient.lift (nilradical S) g
        (fun _s hs => RingHom.mem_ker.mp (hnil hs))
    Function.Surjective gRed := by
  intro hnil gRed
  let : Algebra (S ⧸ nilradical S) W := gRed.toAlgebra
  let : Algebra (S ⧸ nilradical S) V := algebraLoc
  have hTower : IsScalarTower (S ⧸ nilradical S) W V :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact hcompat s)
  let : IsScalarTower (S ⧸ nilradical S) W V := hTower
  let : FaithfulSMul W V := (faithfulSMul_iff_algebraMap_injective W V).mpr hinj
  let : Algebra.IsIntegral (S ⧸ nilradical S) W :=
    ⟨integral_of_quotient_lift S W g hgIntegral (nilradical S) hnil⟩
  let : IsIntegrallyClosedIn (S ⧸ nilradical S) V :=
    integrallyClosedIn_generic_of_normal (S ⧸ nilradical S) V hNormal eFrac
  exact integral_baseChange_surjective_of_closed_generic
    (S ⧸ nilradical S) W V

private theorem faithful_reduced_integral_closure_target
    (B L₁ B₁ : Type*) [CommRing B] [CommRing L₁] [CommRing B₁]
    [Algebra B L₁] [Algebra B B₁] [Algebra B₁ L₁]
    [IsReduced L₁]
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eB₁_coe : ∀ x : B₁,
      ((eB₁ x : integralClosure B L₁) : L₁) = algebraMap B₁ L₁ x) :
    IsReduced B₁ ∧ Function.Injective (algebraMap B₁ L₁) := by
  have hinj : Function.Injective (algebraMap B₁ L₁) := by
    intro x y hxy
    apply eB₁.injective
    apply Subtype.ext
    simpa only [eB₁_coe] using hxy
  exact ⟨isReduced_of_injective (algebraMap B₁ L₁) hinj, hinj⟩

theorem actual_reduced_tensor_normalization_surjective_of_normal
    (A B K L K₁ L₁ A₁ B₁ : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁] [Algebra K₁ L₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B₁ L₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L L₁] [IsScalarTower K K₁ L₁] [IsScalarTower B L L₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x))
    (eL₁_right : ∀ x : K₁,
      eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x))
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) =
      algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁))
    (hNormal : IsNormalRing ((B ⊗[A] A₁) ⧸ nilradical (B ⊗[A] A₁))) :
    let S := B ⊗[A] A₁
    let R := S ⧸ nilradical S
    ∃ algebraLoc : Algebra R L₁,
      letI := algebraLoc
      ∃ g₀ : S →+* B₁, ∃ hnil : nilradical S ≤ RingHom.ker g₀,
      Function.Surjective (Ideal.Quotient.lift (nilradical S) g₀
        (fun _s hs => RingHom.mem_ker.mp (hnil hs))) ∧
      (∀ b : B, g₀
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] S) b) =
          algebraMap B B₁ b) ∧
      (∀ a : A₁, g₀
        ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) a) =
          algebraMap A₁ B₁ a) ∧
      (∀ s : S, algebraMap R L₁ (Ideal.Quotient.mk (nilradical S) s) =
        algebraMap B₁ L₁ (g₀ s)) ∧
      Nonempty (FractionRing R ≃ₐ[R] L₁) := by
  let S := B ⊗[A] A₁
  obtain ⟨algebraLoc, g₀, hIntegral, _, hleft, hright, hcompat, ⟨eFrac⟩⟩ :=
    actual_reduced_tensor_compatible_fractionRing
      A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
        hfieldSquare hringSquare
  have : IsReduced ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : IsReduced L₁ := isReduced_of_injective eL₁ eL₁.injective
  obtain ⟨hReduced, hinj⟩ :=
    faithful_reduced_integral_closure_target B L₁ B₁ eB₁ eB₁_coe
  let : IsReduced B₁ := hReduced
  refine ⟨algebraLoc, g₀, nilradical_le_ker_of_isReduced S B₁ g₀, ?_, hleft, hright, hcompat,
    ⟨eFrac⟩⟩
  exact reduced_integral_comparison_surjective_of_normal S B₁ L₁
    algebraLoc g₀ hIntegral hcompat hinj hNormal eFrac

end IntegralClosureComparison

end

end

end IsDiscreteValuationRing
