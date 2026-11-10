module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.TensorSpecialFiber

/-!
# Abhyankar's lemma: special fibres of the reduced branches

Continuing the namespace `ReducedTensorLocalization`: the special fibres of the branches of the
integral closure and of the reduced tensor product are fields, and the uniformizer of the base
stays a uniformizer of the selected branch.

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

private theorem selected_integralClosure_branch_specialFiber_isField
    (A B C D E : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [CommRing E]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing D]
    [Algebra A B] [Algebra A C] [Algebra C D] [Algebra C E]
    [Algebra A D] [IsScalarTower A C D]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A D)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    (g : (B ⊗[A] C) →+* E)
    (hright : ∀ c : C,
      g ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c) =
        algebraMap C E c)
    (Q : Ideal E) [Q.IsPrime]
    (hp : Q.comap (algebraMap C E) = p) :
    IsField (Localization.AtPrime (Q.comap g) ⧸
      (p.map (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
        (algebraMap (B ⊗[A] C) (Localization.AtPrime (Q.comap g)))) := by
  have : (Q.comap g).IsPrime := Ideal.IsPrime.comap g
  have hlie : (Q.comap g).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := B)) = p :=
    (tensor_branch_comap_right A B C E g hright Q).trans hp
  exact selected_global_tensor_specialFiber_isField A B C D hweak hsep p
    (Q.comap g) hlie

private theorem local_equivalentClosure_fractionRing
    (A K L B : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [CommRing B] [Algebra A B]
    (e : B ≃ₐ[A] integralClosure A L)
    (q : Ideal B) [q.IsPrime] :
    ∃ algebraLoc : Algebra (Localization.AtPrime q) L,
      letI := algebraLoc
      IsScalarTower A (Localization.AtPrime q) L ∧
        IsFractionRing (Localization.AtPrime q) L := by
  let : IsDomain B := e.toRingEquiv.isDomain_iff.mpr inferInstance
  let : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let : Algebra B L :=
    ((algebraMap (integralClosure A L) L).comp e.toRingHom).toAlgebra
  have : IsFractionRing B L :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
      (R := integralClosure A L) (S := L) e.symm.toRingEquiv).mp inferInstance
  have : IsScalarTower A B (Localization.AtPrime q) := inferInstance
  have : IsScalarTower A B L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap A L x =
        algebraMap (integralClosure A L) L (e (algebraMap A B x))
      rw [e.commutes x]
      exact (IsScalarTower.algebraMap_apply A (integralClosure A L) L x).symm)
  have hM : q.primeCompl ≤ (nonZeroDivisors B).comap (RingHom.id B) := by
    intro x hx
    exact q.primeCompl_le_nonZeroDivisors hx
  let g : Localization.AtPrime q →+* L :=
    IsLocalization.map (M := q.primeCompl) (S := Localization.AtPrime q)
      (T := nonZeroDivisors B) L (RingHom.id B) hM
  let : Algebra (Localization.AtPrime q) L := g.toAlgebra
  have : IsScalarTower B (Localization.AtPrime q) L :=
    IsScalarTower.of_algebraMap_eq' (by
      change algebraMap B L = g.comp (algebraMap B (Localization.AtPrime q))
      simp only [g, IsLocalization.map_comp, RingHom.comp_id])
  have : IsScalarTower A (Localization.AtPrime q) L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      calc
        algebraMap A L x = algebraMap B L (algebraMap A B x) :=
          IsScalarTower.algebraMap_apply A B L x
        _ = algebraMap (Localization.AtPrime q) L
              (algebraMap B (Localization.AtPrime q) (algebraMap A B x)) :=
          IsScalarTower.algebraMap_apply B (Localization.AtPrime q) L _
        _ = algebraMap (Localization.AtPrime q) L
              (algebraMap A (Localization.AtPrime q) x) := by
          rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)])
  exact ⟨inferInstance, inferInstance,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl _ L⟩

private theorem local_dvr_equivalentClosure
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    (e : B ≃ₐ[A] integralClosure A L)
    (q : Ideal B) [q.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have : Algebra.IsIntegral A B := (e.isIntegral_iff).mpr inferInstance
  have hAL : Function.Injective (algebraMap A L) :=
    algebraMap_injective_of_field_isFractionRing A L K L
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y h
    apply hAL
    have h := congrArg
      (fun b : B => algebraMap (integralClosure A L) L (e b)) h
    simpa only [e.commutes, IsScalarTower.algebraMap_apply A (integralClosure A L) L]
      using h
  have hnotField : ¬IsField B := by
    intro hfield
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hAB hfield)
  have hqne : q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (show q.IsMaximal from inferInstance) hnotField
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    B hqne (Localization.AtPrime q)

private theorem finite_residue_equivalentClosure
    (A K L B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    (e : B ≃ₐ[A] integralClosure A L)
    (q : Ideal B) [q.IsMaximal] :
    ∃ localHom : IsLocalHom (algebraMap A (Localization.AtPrime q)),
      letI := localHom
      Module.Finite (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) := by
  obtain ⟨algebraLoc, hTower, hFrac⟩ :=
    local_equivalentClosure_fractionRing A K L B e q
  let : Algebra (Localization.AtPrime q) L := algebraLoc
  let : IsScalarTower A (Localization.AtPrime q) L := hTower
  let : IsFractionRing (Localization.AtPrime q) L := hFrac
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    local_dvr_equivalentClosure A K L B e q
  have : Algebra.IsIntegral A B := (e.isIntegral_iff).mpr inferInstance
  have hqA : (q.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q
  have hloc : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap A (Localization.AtPrime q)) = IsLocalRing.maximalIdeal A := by
    rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q),
      ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).under B).comap
      (algebraMap A B) = IsLocalRing.maximalIdeal A
    rw [Localization.AtPrime.under_maximalIdeal]
    exact IsLocalRing.eq_maximalIdeal hqA
  have : IsLocalHom (algebraMap A (Localization.AtPrime q)) :=
    ((IsLocalRing.local_hom_TFAE _).out 1 5).mpr hloc
  have : FaithfulSMul A (Localization.AtPrime q) :=
    FaithfulSMul.of_field_isFractionRing A _ K L
  exact ⟨inferInstance,
    (residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank
      A (Localization.AtPrime q) K L).1⟩

theorem local_extension_equivalentClosure
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    (e : B ≃ₐ[A] integralClosure A L)
    (q : Ideal B) [q.IsMaximal] :
    ∃ _ : IsDiscreteValuationRing (Localization.AtPrime q),
      IsExtension A (Localization.AtPrime q) := by
  obtain ⟨algebraLoc, hTower, hFrac⟩ :=
    local_equivalentClosure_fractionRing A K L B e q
  let : Algebra (Localization.AtPrime q) L := algebraLoc
  let : IsScalarTower A (Localization.AtPrime q) L := hTower
  let : IsFractionRing (Localization.AtPrime q) L := hFrac
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    local_dvr_equivalentClosure A K L B e q
  obtain ⟨hlocal, _⟩ := finite_residue_equivalentClosure A K L B e q
  let : IsLocalHom (algebraMap A (Localization.AtPrime q)) := hlocal
  let : FaithfulSMul A (Localization.AtPrime q) :=
    FaithfulSMul.of_field_isFractionRing A _ K L
  exact ⟨inferInstance, ⟨⟩⟩

private theorem actual_09EM_branch_specialFiber_isField
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
    ∃ g : (B ⊗[A] A₁) →+* B₁,
      g.IsIntegral ∧ RingHom.ker g ≤ nilradical (B ⊗[A] A₁) ∧
      Function.Surjective (PrimeSpectrum.comap g) ∧
      (∀ x : B,
        g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) x) =
          algebraMap B B₁ x) ∧
      (∀ x : A₁,
        g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) x) =
          algebraMap A₁ B₁ x) ∧
      IsField (Localization.AtPrime (q.comap g) ⧸
        ((q.comap (algebraMap A₁ B₁)).map
          (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
          (algebraMap (B ⊗[A] A₁) (Localization.AtPrime (q.comap g)))) := by
  let : q.IsPrime := (inferInstance : q.IsMaximal).isPrime
  have hEM := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare
  let p : Ideal A₁ := q.comap (algebraMap A₁ B₁)
  have : p.IsMaximal := by
    rcases hEM with ⟨_, _, _, _, _, _, _, _, _, hmax, _⟩
    exact (hmax q (inferInstance : q.IsMaximal)).1
  let : p.IsPrime := (inferInstance : p.IsMaximal).isPrime
  let : IsDedekindDomain A₁ := hEM.2.1
  let : IsDomain A₁ := IsDedekindDomain.toIsDomain
  obtain ⟨hlocal, hfin⟩ := finite_residue_equivalentClosure A K K₁ A₁ eA₁ p
  let : IsLocalHom (algebraMap A (Localization.AtPrime p)) := hlocal
  let : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := hfin
  obtain ⟨π, hπ, hregular, he, g, hgintegral, hgker, hgprime, hleft, hright⟩ :=
    hEM.2.2.2.1
  obtain ⟨hweak, hsep⟩ := weaklyUnramified_and_separable_of_formallySmooth A B hformal
  refine ⟨g, hgintegral, hgker, hgprime, hleft, hright, ?_⟩
  exact selected_integralClosure_branch_specialFiber_isField A B A₁
    (Localization.AtPrime p) B₁
    hweak hsep p g hright q rfl

private theorem field_quotient_map_of_surjective
    (U V : Type*) [CommRing U] [CommRing V]
    (f : U →+* V) (hf : Function.Surjective f)
    (I : Ideal U) (hfield : IsField (U ⧸ I))
    (hker : RingHom.ker f ≤ I) : IsField (V ⧸ I.map f) := by
  let : I.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr hfield
  let : (I.map f).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hf hker
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance

private theorem nilradical_atPrime_map
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime] :
    (nilradical S).map (algebraMap S (Localization.AtPrime q)) =
      nilradical (Localization.AtPrime q) := by
  unfold nilradical
  rw [IsLocalization.map_radical q.primeCompl (Localization.AtPrime q)]
  simp

private theorem reduction_localization_atPrime
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime]
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk (nilradical S)) = q) :
    IsLocalization.AtPrime
      ((Localization.AtPrime q) ⧸
        (nilradical S).map (algebraMap S (Localization.AtPrime q))) p := by
  have hsub : Algebra.algebraMapSubmonoid (S ⧸ nilradical S) q.primeCompl =
      p.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      subst hp
      intro hmem
      refine hz ?_
      have hzz : (Ideal.Quotient.mk (nilradical S)) z =
          (Ideal.Quotient.mk (nilradical S)) y := by
        simpa [Ideal.Quotient.algebraMap_eq] using hzy
      simpa [Ideal.mem_comap, hzz] using hmem
    · intro hx
      exact ⟨y, by subst hp; exact hx, rfl⟩
  have hloc := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (M := q.primeCompl) (S := Localization.AtPrime q) (nilradical S)
  rwa [hsub] at hloc

private noncomputable def reduced_local_branch_algEquiv
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime]
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk (nilradical S)) = q) :
    ((Localization.AtPrime q) ⧸
      (nilradical S).map (algebraMap S (Localization.AtPrime q)))
      ≃ₐ[S ⧸ nilradical S] Localization.AtPrime p := by
  letI := reduction_localization_atPrime S q p hp
  exact IsLocalization.algEquiv p.primeCompl _ _

private theorem reduced_prime_over
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime] :
    ∃ p : Ideal (S ⧸ nilradical S),
      ∃ _ : p.IsPrime, p.comap (Ideal.Quotient.mk (nilradical S)) = q := by
  let f : S →+* S ⧸ nilradical S := Ideal.Quotient.mk _
  have hker : RingHom.ker f ≤ q := by
    simpa [f, Ideal.mk_ker] using (nilradical_le_prime q)
  refine ⟨q.map f, Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective hker, ?_⟩
  change (q.map f).comap f = q
  rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective q]
  exact sup_of_le_left (by simpa only [RingHom.ker_eq_comap_bot] using hker)

private theorem field_quotient_of_ringEquiv
    (U V : Type*) [CommRing U] [CommRing V]
    (e : U ≃+* V) (I : Ideal U)
    (hfield : IsField (U ⧸ I)) :
    IsField (V ⧸ I.map e.toRingHom) :=
  (Ideal.quotientEquiv I (I.map e.toRingHom) e rfl).symm.isField hfield

private theorem reduced_branch_fiber_field
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime]
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk (nilradical S)) = q)
    (I : Ideal (Localization.AtPrime q))
    (hfield : IsField (Localization.AtPrime q ⧸ I)) :
    IsField (Localization.AtPrime p ⧸
      (I.map (Ideal.Quotient.mk
        ((nilradical S).map (algebraMap S (Localization.AtPrime q))))).map
        (reduced_local_branch_algEquiv S q p hp).toRingHom) := by
  let U := Localization.AtPrime q
  let J := (nilradical S).map (algebraMap S U)
  let : I.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr hfield
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ I := by
    rw [Ideal.mk_ker, show J = nilradical U from nilradical_atPrime_map S q]
    exact nilradical_le_prime I
  have hred : IsField ((U ⧸ J) ⧸ I.map (Ideal.Quotient.mk J)) :=
    field_quotient_map_of_surjective U (U ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective I hfield hker
  exact field_quotient_of_ringEquiv (U ⧸ J) (Localization.AtPrime p)
    (reduced_local_branch_algEquiv S q p hp).toRingEquiv _ hred

private theorem reduced_branch_ideal_map_compatibility
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime]
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk (nilradical S)) = q)
    (I : Ideal S) :
    ((I.map (algebraMap S (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((nilradical S).map
        (algebraMap S (Localization.AtPrime q))))).map
      (reduced_local_branch_algEquiv S q p hp).toRingHom =
      (I.map (Ideal.Quotient.mk (nilradical S))).map
        (algebraMap (S ⧸ nilradical S) (Localization.AtPrime p)) := by
  let U := Localization.AtPrime q
  let J := (nilradical S).map (algebraMap S U)
  let e := reduced_local_branch_algEquiv S q p hp
  have hcomp : e.toRingHom.comp ((Ideal.Quotient.mk J).comp (algebraMap S U)) =
      (algebraMap (S ⧸ nilradical S) (Localization.AtPrime p)).comp
        (Ideal.Quotient.mk (nilradical S)) := by
    ext x
    exact e.commutes (Ideal.Quotient.mk (nilradical S) x)
  change ((I.map (algebraMap S U)).map (Ideal.Quotient.mk J)).map
      e.toRingHom = _
  rw [Ideal.map_map, Ideal.map_map]
  have hassoc : (e.toRingHom.comp (Ideal.Quotient.mk J)).comp (algebraMap S U) =
      e.toRingHom.comp ((Ideal.Quotient.mk J).comp (algebraMap S U)) := by
    ext x
    rfl
  rw [hassoc, hcomp, Ideal.map_map]

private theorem reduced_branch_fiber_field_of_raw_base_ideal
    (S : Type*) [CommRing S] (q : Ideal S) [q.IsPrime]
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk (nilradical S)) = q)
    (I : Ideal S)
    (hfield : IsField (Localization.AtPrime q ⧸
      I.map (algebraMap S (Localization.AtPrime q)))) :
    IsField (Localization.AtPrime p ⧸
      (I.map (Ideal.Quotient.mk (nilradical S))).map
        (algebraMap (S ⧸ nilradical S) (Localization.AtPrime p))) := by
  rw [← reduced_branch_ideal_map_compatibility S q p hp I]
  exact reduced_branch_fiber_field S q p hp
    (I.map (algebraMap S (Localization.AtPrime q))) hfield

private theorem local_base_ideal_square_for_uniformizer
    (C S : Type*) [CommRing C] [CommRing S]
    (ι : C →+* S) (m : Ideal C) [m.IsPrime]
    (q : Ideal S) [q.IsPrime] (hqm : q.comap ι = m)
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hpq : p.comap (Ideal.Quotient.mk (nilradical S)) = q) :
    letI : Algebra C (S ⧸ nilradical S) :=
      ((Ideal.Quotient.mk (nilradical S)).comp ι).toAlgebra
    letI : Algebra C (Localization.AtPrime p) :=
      ((algebraMap (S ⧸ nilradical S) (Localization.AtPrime p)).comp
        ((Ideal.Quotient.mk (nilradical S)).comp ι)).toAlgebra
    ∃ algebraLoc : Algebra (Localization.AtPrime m) (Localization.AtPrime p),
      letI := algebraLoc
      (∀ c : C, algebraMap (Localization.AtPrime m) (Localization.AtPrime p)
          (algebraMap C (Localization.AtPrime m) c) =
        algebraMap (S ⧸ nilradical S) (Localization.AtPrime p)
          (Ideal.Quotient.mk (nilradical S) (ι c))) ∧
      (((m.map ι).map (Ideal.Quotient.mk (nilradical S))).map
        (algebraMap (S ⧸ nilradical S) (Localization.AtPrime p))) =
        ((m.map (algebraMap C (Localization.AtPrime m))).map
          (algebraMap (Localization.AtPrime m) (Localization.AtPrime p))) := by
  let R := S ⧸ nilradical S
  let T := Localization.AtPrime p
  let f : C →+* R := (Ideal.Quotient.mk _).comp ι
  let : Algebra C R := f.toAlgebra
  let : Algebra C T := ((algebraMap R T).comp f).toAlgebra
  let : SMul C T := (inferInstance : Algebra C T).toSMul
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : IsScalarTower C R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hlie : p.LiesOver m := by
    apply Ideal.LiesOver.mk
    change m = p.comap f
    calc
      m = q.comap ι := hqm.symm
      _ = (p.comap (Ideal.Quotient.mk (nilradical S))).comap ι := by rw [hpq]
      _ = p.comap f := Ideal.comap_comap ι (Ideal.Quotient.mk (nilradical S))
  let : p.LiesOver m := hlie
  let : Algebra (Localization.AtPrime m) T :=
    Localization.AtPrime.algebraOfLiesOver m p
  let : IsScalarTower C (Localization.AtPrime m) T :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap C T c =
        (Localization.localRingHom m p f hlie.over)
          (algebraMap C (Localization.AtPrime m) c)
      simp only [Localization.localRingHom_to_map]
      rfl
  refine ⟨inferInstance, ?_, ?_⟩
  · intro c
    rw [← IsScalarTower.algebraMap_apply C (Localization.AtPrime m) T]
    rfl
  · calc
      (((m.map ι).map (Ideal.Quotient.mk (nilradical S))).map
          (algebraMap R T)) =
        m.map (algebraMap C T) := by
          rw [Ideal.map_map, Ideal.map_map]
          rfl
      _ = (m.map (algebraMap C (Localization.AtPrime m))).map
          (algebraMap (Localization.AtPrime m) T) := by
            rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

private theorem uniformizer_of_named_base_ideal
    (C S : Type*) [CommRing C] [CommRing S]
    (ι : C →+* S) (m : Ideal C) [m.IsPrime]
    (q : Ideal S) [q.IsPrime] (hqm : q.comap ι = m)
    (p : Ideal (S ⧸ nilradical S)) [p.IsPrime]
    (hpq : p.comap (Ideal.Quotient.mk (nilradical S)) = q)
    [IsDomain (Localization.AtPrime m)]
    [IsDiscreteValuationRing (Localization.AtPrime m)]
    (I : Ideal S) (hI : I = m.map ι)
    (hfield : IsField (Localization.AtPrime p ⧸
      ((I.map (Ideal.Quotient.mk (nilradical S))).map
        (algebraMap (S ⧸ nilradical S) (Localization.AtPrime p))))) :
    let R := Localization.AtPrime m
    let T := Localization.AtPrime p
    ∃ algebraLoc : Algebra R T, letI := algebraLoc
      (∀ c : C, algebraMap R T (algebraMap C R c) =
        algebraMap (S ⧸ nilradical S) T
          (Ideal.Quotient.mk (nilradical S) (ι c))) ∧
      ∃ π : R, Irreducible π ∧
        IsLocalRing.maximalIdeal T = Ideal.span {algebraMap R T π} := by
  rw [hI] at hfield
  obtain ⟨algebraLoc, hcomp, hsquare⟩ :=
    local_base_ideal_square_for_uniformizer C S ι m q hqm p hpq
  let R := Localization.AtPrime m
  let T := Localization.AtPrime p
  let : Algebra R T := algebraLoc
  have hfield' : IsField (T ⧸ (IsLocalRing.maximalIdeal R).map
      (algebraMap R T)) := by
    rwa [hsquare, Localization.AtPrime.map_eq_maximalIdeal] at hfield
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨algebraLoc, hcomp, π, hπ, ?_⟩
  have hmax : ((IsLocalRing.maximalIdeal R).map (algebraMap R T)).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ hfield'
  rw [← IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]

private theorem associated_base_uniformizers_of_extension
    (A D : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra A D] [IsExtension A D]
    (r : A) (hr : Irreducible r) (π : D) (hπ : Irreducible π) :
    let e := ramificationIndex A D
    1 ≤ e ∧ Associated (algebraMap A D r) (π ^ e) := by
  obtain ⟨hpos, _, _, hunit⟩ := ramificationIndex_characterization A D
  obtain ⟨unit, huniteq⟩ := hunit r hr π hπ
  exact ⟨hpos, huniteq ▸ associated_unit_mul_left _ _ unit.isUnit⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem associated_selected_raw_parameter
    (A B D : Type*) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D]
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
    (r : A) (π : Localization.AtPrime m) (e : ℕ)
    (hbase : Associated (algebraMap A (Localization.AtPrime m) r) (π ^ e)) :
    letI := algebraLoc
    Associated
      (algebraMap ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) (Localization.AtPrime q)
        (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] D)
            (algebraMap A B r))))
      ((algebraMap (Localization.AtPrime m) (Localization.AtPrime q) π) ^ e) := by
  let R := (B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)
  let T := Localization.AtPrime q
  let : Algebra (Localization.AtPrime m) T := algebraLoc
  have hleft : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] D)
        (algebraMap A B r) =
      (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D)
        (algebraMap A D r) :=
    congrFun (congrArg DFunLike.coe
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := A) (A := B) (B := D))) r
  have hmapped := hbase.map (algebraMap (Localization.AtPrime m) T)
  rw [hleft, ← hcomp (algebraMap A D r),
    ← IsScalarTower.algebraMap_apply A D (Localization.AtPrime m) r]
  simpa only [map_pow] using hmapped

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem associated_selected_raw_parameter_of_extension
    (A B D : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    (m : Ideal D) [m.IsPrime]
    [IsDomain (Localization.AtPrime m)]
    [IsDiscreteValuationRing (Localization.AtPrime m)]
    [IsExtension A (Localization.AtPrime m)]
    (q : Ideal ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D))) [q.IsPrime]
    (algebraLoc : Algebra (Localization.AtPrime m) (Localization.AtPrime q))
    (hcomp : letI := algebraLoc
      ∀ c : D,
        algebraMap (Localization.AtPrime m) (Localization.AtPrime q)
          (algebraMap D (Localization.AtPrime m) c) =
        algebraMap ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) (Localization.AtPrime q)
          (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) c)))
    (r : A) (hr : Irreducible r) (π : Localization.AtPrime m) (hπ : Irreducible π) :
    letI := algebraLoc
    let e := ramificationIndex A (Localization.AtPrime m)
    1 ≤ e ∧
    Associated
      (algebraMap ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) (Localization.AtPrime q)
        (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] D)
            (algebraMap A B r))))
      ((algebraMap (Localization.AtPrime m) (Localization.AtPrime q) π) ^ e) := by
  obtain ⟨hpos, hbase⟩ :=
    associated_base_uniformizers_of_extension A (Localization.AtPrime m) r hr π hπ
  exact ⟨hpos, associated_selected_raw_parameter A B D m q algebraLoc hcomp
    r π (ramificationIndex A (Localization.AtPrime m)) hbase⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem selected_branch_away_artinian_of_base_extension
    (A B D K L E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E] [Module.Finite K E]
    (m : Ideal D) [m.IsPrime]
    [IsDomain (Localization.AtPrime m)]
    [IsDiscreteValuationRing (Localization.AtPrime m)]
    [IsExtension A (Localization.AtPrime m)]
    (q : Ideal ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D))) [q.IsPrime]
    (algebraLoc : Algebra (Localization.AtPrime m) (Localization.AtPrime q))
    (hcomp : letI := algebraLoc
      ∀ c : D,
        algebraMap (Localization.AtPrime m) (Localization.AtPrime q)
          (algebraMap D (Localization.AtPrime m) c) =
        algebraMap ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) (Localization.AtPrime q)
          (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) c)))
    (r : A) (hr : Irreducible r)
    (genericEquiv : Localization.Away (algebraMap A (B ⊗[A] D) r) ≃+* (L ⊗[K] E))
    (π : Localization.AtPrime m) (hπ : Irreducible π) :
    letI := algebraLoc
    IsArtinianRing (Localization.Away (algebraMap (Localization.AtPrime m)
      (Localization.AtPrime q) π)) ∧
    IsReduced (Localization.Away (algebraMap (Localization.AtPrime m)
      (Localization.AtPrime q) π)) := by
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := algebraLoc
  obtain ⟨hpos, hassoc⟩ :=
    associated_selected_raw_parameter_of_extension A B D m q algebraLoc hcomp r hr π hπ
  have hraw : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] D)
      (algebraMap A B r) = algebraMap A (B ⊗[A] D) r := rfl
  rw [hraw] at hassoc
  exact selected_branch_away_artinian_reduced_of_generic_equiv
    A B D K L E r genericEquiv q
      (algebraMap (Localization.AtPrime m) (Localization.AtPrime q) π)
      (ramificationIndex A (Localization.AtPrime m)) (by omega) hassoc

theorem actual_09EM_reduced_branch_specialFiber_isField
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
    ∃ g : (B ⊗[A] A₁) →+* B₁,
      g.IsIntegral ∧ RingHom.ker g ≤ nilradical (B ⊗[A] A₁) ∧
      (∀ x : B, g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) x) =
        algebraMap B B₁ x) ∧
      (∀ x : A₁, g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) x) =
        algebraMap A₁ B₁ x) ∧
      (q.comap (algebraMap A₁ B₁)).IsMaximal ∧
      (∃ _ : IsDomain (Localization.AtPrime (q.comap (algebraMap A₁ B₁))),
        IsDiscreteValuationRing (Localization.AtPrime (q.comap (algebraMap A₁ B₁)))) ∧
      let S := B ⊗[A] A₁
      let R := S ⧸ nilradical S
      let I := (q.comap (algebraMap A₁ B₁)).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B))
      ∃ rRed : Ideal R, ∃ _ : rRed.IsPrime,
        rRed.comap (Ideal.Quotient.mk (nilradical S)) = q.comap g ∧
        IsField (Localization.AtPrime rRed ⧸
          (I.map (Ideal.Quotient.mk (nilradical S))).map
            (algebraMap R (Localization.AtPrime rRed))) ∧
        (∃ _ : IsDomain (Localization.AtPrime (q.comap (algebraMap A₁ B₁))),
          ∃ _ : IsDiscreteValuationRing
            (Localization.AtPrime (q.comap (algebraMap A₁ B₁))),
          ∃ algebraLoc : Algebra
            (Localization.AtPrime (q.comap (algebraMap A₁ B₁)))
            (Localization.AtPrime rRed),
            letI := algebraLoc
            (∀ c : A₁,
              algebraMap (Localization.AtPrime (q.comap (algebraMap A₁ B₁)))
                (Localization.AtPrime rRed)
                (algebraMap A₁ (Localization.AtPrime (q.comap (algebraMap A₁ B₁))) c) =
              algebraMap R (Localization.AtPrime rRed)
                (Ideal.Quotient.mk (nilradical S)
                  ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) c))) ∧
            ∃ π : Localization.AtPrime (q.comap (algebraMap A₁ B₁)),
              Irreducible π ∧
              IsLocalRing.maximalIdeal (Localization.AtPrime rRed) =
                Ideal.span {algebraMap
                              (Localization.AtPrime (q.comap (algebraMap A₁ B₁)))
                              (Localization.AtPrime rRed) π}) := by
  let S := B ⊗[A] A₁
  let I : Ideal S := (q.comap (algebraMap A₁ B₁)).map
    (Algebra.TensorProduct.includeRight (R := A) (A := B))
  have hEM := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
      hfieldSquare hringSquare
  let m : Ideal A₁ := q.comap (algebraMap A₁ B₁)
  have hm : m.IsMaximal := by
    rcases hEM with ⟨_, _, _, _, _, _, _, _, _, hmax, _⟩
    exact (hmax q (inferInstance : q.IsMaximal)).1
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  let : IsDedekindDomain A₁ := hEM.2.1
  let : IsDomain A₁ := IsDedekindDomain.toIsDomain
  have hDomain : IsDomain (Localization.AtPrime m) := inferInstance
  have hDVR : IsDiscreteValuationRing (Localization.AtPrime m) :=
    local_dvr_equivalentClosure A K K₁ A₁ eA₁ m
  obtain ⟨g, hIntegral, hNil, _, hleft, hright, hfield⟩ :=
    actual_09EM_branch_specialFiber_isField
      A B K L K₁ L₁ A₁ B₁ eL₁ eA₁ eB₁ eL₁_left eL₁_right eB₁_coe
        hfieldSquare hringSquare hformal q
  have : (q.comap g).IsPrime := Ideal.IsPrime.comap g
  obtain ⟨rRed, hRedPrime, hPrime⟩ := reduced_prime_over S (q.comap g)
  let R := S ⧸ nilradical S
  have hfieldRed : IsField (Localization.AtPrime rRed ⧸
      (I.map (Ideal.Quotient.mk (nilradical S))).map
        (algebraMap R (Localization.AtPrime rRed))) :=
    reduced_branch_fiber_field_of_raw_base_ideal S (q.comap g) rRed
      hPrime I hfield
  let ι : A₁ →+* S :=
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S).toRingHom
  have hI : I = m.map ι := rfl
  have hqm : (q.comap g).comap ι = m := by
    ext x
    change g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) x) ∈ q ↔
      algebraMap A₁ B₁ x ∈ q
    rw [hright x]
  let : IsDomain (Localization.AtPrime m) := hDomain
  let : IsDiscreteValuationRing (Localization.AtPrime m) := hDVR
  let : rRed.IsPrime := hRedPrime
  have hprincipal :
      ∃ algebraLoc : Algebra (Localization.AtPrime m) (Localization.AtPrime rRed),
        let := algebraLoc
        (∀ c : A₁,
          algebraMap (Localization.AtPrime m) (Localization.AtPrime rRed)
            (algebraMap A₁ (Localization.AtPrime m) c) =
          algebraMap R (Localization.AtPrime rRed)
            (Ideal.Quotient.mk (nilradical S)
              ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] S) c))) ∧
        ∃ π : Localization.AtPrime m, Irreducible π ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime rRed) =
            Ideal.span {algebraMap (Localization.AtPrime m)
                          (Localization.AtPrime rRed) π} :=
    uniformizer_of_named_base_ideal A₁ S ι m (q.comap g) hqm rRed hPrime
      I hI hfieldRed
  refine ⟨g, hIntegral, hNil, hleft, hright, hm, ⟨hDomain, hDVR⟩,
    rRed, hRedPrime, hPrime, hfieldRed, hDomain, hDVR, hprincipal⟩

end ReducedTensorLocalization

end

end

end IsDiscreteValuationRing
