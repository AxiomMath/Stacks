module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.ResidueFieldTensor

/-!
# Abhyankar's lemma: special fibres of the tensor product

The first part of the namespace `ReducedTensorLocalization`: for a formally smooth extension of
discrete valuation rings and a finite extension of the base, the generic fibre of the tensor
product is Artinian and reduced on the selected branches, and the special fibre of the tensor
product is computed at its localizations at primes over the maximal ideal, which are fields.

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


theorem weaklyUnramified_and_separable_of_formallySmooth
    (A : Type uA) (B : Type uB)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (hformal : RingHom.FormallySmoothNAdic.{max uA uB}
      (algebraMap A B) (IsLocalRing.maximalIdeal B)) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B ∧
    Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) := by
  obtain ⟨hweak, hsep⟩ :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mp
      hformal
  obtain ⟨_, hpow, _, _⟩ := ramificationIndex_characterization A B
  change ramificationIndex A B = 1 at hweak
  rw [hweak, pow_one] at hpow
  exact ⟨hpow, hsep⟩

private theorem reduced_residue_tensor_of_separable
    (k F E : Type*) [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E]
    (hsep : Algebra.IsSeparableExtension k F) :
    IsReduced (F ⊗[k] E) := by
  have hgeom : Algebra.IsGeometricallyReduced k F :=
    ((Algebra.isSeparableExtension_tfae k F (ringExpChar k)).out 1 4).mp hsep
  let : IsReduced (E ⊗[k] F) :=
    hgeom.isReduced_tensorProduct k E F
  exact isReduced_of_injective
    (Algebra.TensorProduct.comm k F E).toRingHom
    (Algebra.TensorProduct.comm k F E).injective

private theorem artinian_generic_tensor
    (K L E : Type*) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K E] :
    IsArtinianRing (L ⊗[K] E) := by
  have : Module.Finite L (L ⊗[K] E) := inferInstance
  exact IsArtinianRing.of_finite L _

private theorem artinian_away_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (r : R)
    [IsArtinianRing (Localization.Away r)] :
    IsArtinianRing (Localization.Away (f r)) := by
  let g : Localization.Away r →+* Localization.Away (f r) :=
    IsLocalization.Away.map _ _ f r
  let : Algebra (Localization.Away r) (Localization.Away (f r)) := g.toAlgebra
  have hg : Function.Surjective g := by
    apply (IsLocalization.Away.map_surjective_iff _ _ f r).2
    intro a
    obtain ⟨b, rfl⟩ := hf a
    exact ⟨b, 0, by simp⟩
  have : Module.Finite (Localization.Away r) (Localization.Away (f r)) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hg
  exact isArtinian_of_tower (Localization.Away r) inferInstance

private theorem isReduced_quotient_nilradical (T : Type*) [CommRing T] :
    IsReduced (T ⧸ nilradical T) :=
  (Ideal.isRadical_iff_quotient_reduced (nilradical T)).mp
    (Ideal.radical_isRadical (⊥ : Ideal T))

private theorem generic_reduced_tensor_artinian
    (T : Type*) [CommRing T] (r : T)
    [IsArtinianRing (Localization.Away r)] :
    IsArtinianRing
      (Localization.Away ((Ideal.Quotient.mk (nilradical T)) r)) ∧
    IsReduced
      (Localization.Away ((Ideal.Quotient.mk (nilradical T)) r)) := by
  have := isReduced_quotient_nilradical T
  constructor
  · exact artinian_away_of_surjective
      (Ideal.Quotient.mk (nilradical T))
      (Ideal.Quotient.mk_surjective) r
  · infer_instance

private theorem artinian_reduced_away_from_generic_equiv
    (A B D K L E : Type*) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D]
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K E]
    (π : A)
    (equiv : Localization.Away (algebraMap A (B ⊗[A] D) π) ≃+* (L ⊗[K] E)) :
    IsArtinianRing
      (Localization.Away
        (Ideal.Quotient.mk (nilradical (B ⊗[A] D))
          (algebraMap A (B ⊗[A] D) π))) ∧
    IsReduced
      (Localization.Away
        (Ideal.Quotient.mk (nilradical (B ⊗[A] D))
          (algebraMap A (B ⊗[A] D) π))) := by
  let : IsArtinianRing (L ⊗[K] E) := artinian_generic_tensor K L E
  let : IsArtinianRing (Localization.Away (algebraMap A (B ⊗[A] D) π)) :=
    equiv.symm.isArtinianRing
  exact generic_reduced_tensor_artinian (B ⊗[A] D) (algebraMap A (B ⊗[A] D) π)

private theorem artinian_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    [IsArtinianRing R] : IsArtinianRing S := by
  have hs : Function.Surjective (algebraMap R S) :=
    IsArtinianRing.localization_surjective M S
  have : Module.Finite R S :=
    Module.Finite.of_surjective (Algebra.linearMap R S) hs
  exact isArtinian_of_tower R inferInstance

private theorem local_branch_generic_artinian
    (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] (r : R)
    [IsArtinianRing (Localization.Away r)] :
    IsArtinianRing
      (Localization.Away (algebraMap R (Localization.AtPrime p) r)) := by
  let Rp := Localization.AtPrime p
  let W := Localization.Away r
  let Q := Localization.Away (algebraMap R Rp r)
  let : Algebra R Q :=
    ((algebraMap Rp Q).comp (algebraMap R Rp)).toAlgebra
  let : SMul R Q := Algebra.toSMul
  let : SMul Rp Q := Algebra.toSMul
  have : IsScalarTower R Rp Q := IsScalarTower.of_algebraMap_eq' rfl
  let g : W →+* Q := IsLocalization.Away.map W Q (algebraMap R Rp) r
  let : Algebra W Q := g.toAlgebra
  let : SMul W Q := Algebra.toSMul
  have : IsScalarTower R W Q := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change (algebraMap Rp Q) (algebraMap R Rp x) =
      g (algebraMap R W x)
    simp [g, IsLocalization.Away.map])
  let N := IsLocalization.localizationLocalizationSubmodule p.primeCompl
    (Submonoid.powers (algebraMap R Rp r))
  have : IsLocalization N Q :=
    IsLocalization.localization_localization_isLocalization p.primeCompl
      (Submonoid.powers (algebraMap R Rp r)) Q
  have hrN : r ∈ N := by
    rw [IsLocalization.mem_localizationLocalizationSubmodule]
    refine ⟨⟨(algebraMap R Rp) r, ?_⟩, 1, ?_⟩
    · exact ⟨1, by simp⟩
    · simp
  have hMN : Submonoid.powers r ≤ N := Submonoid.powers_le.mpr hrN
  have : IsLocalization (N.map (algebraMap R W)) Q :=
    IsLocalization.isLocalization_of_submonoid_le W Q
      (Submonoid.powers r) N hMN
  exact artinian_of_isLocalization (N.map (algebraMap R W))

private theorem local_branch_generic_reduced
    (R : Type*) [CommRing R] [IsReduced R]
    (p : Ideal R) [p.IsPrime] (r : R) :
    IsReduced
      (Localization.Away (algebraMap R (Localization.AtPrime p) r)) := by
  infer_instance

private theorem away_of_positive_power
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (t : R) (e : ℕ) (he : e ≠ 0)
    [IsLocalization.Away (t ^ e) S] : IsLocalization.Away t S := by
  have hu : IsUnit (algebraMap R S t) :=
    (isUnit_pow_iff he).mp (by
      simpa only [map_pow] using
        (IsLocalization.Away.algebraMap_isUnit (t ^ e) (S := S)))
  refine IsLocalization.Away.mk t hu ?_ ?_
  · intro z
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj (t ^ e) z
    exact ⟨e * n, a, by simpa only [map_pow, pow_mul] using hn⟩
  · intro a b hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (t ^ e) hab
    exact ⟨e * n, by simpa only [pow_mul] using hn⟩

private theorem away_of_associated_positive_power
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (r t : R) (e : ℕ) (he : e ≠ 0)
    (hassoc : Associated r (t ^ e))
    [IsLocalization.Away r S] : IsLocalization.Away t S := by
  let : IsLocalization.Away (t ^ e) S :=
    IsLocalization.Away.of_associated hassoc
  exact away_of_positive_power R S t e he

private theorem generic_reduced_artinian_change_parameter
    (R : Type*) [CommRing R] (r t : R) (e : ℕ) (he : e ≠ 0)
    (hassoc : Associated r (t ^ e))
    [IsArtinianRing (Localization.Away r)]
    [IsReduced (Localization.Away r)] :
    IsArtinianRing (Localization.Away t) ∧
      IsReduced (Localization.Away t) := by
  let : IsLocalization.Away t (Localization.Away r) :=
    away_of_associated_positive_power R _ r t e he hassoc
  let iso : Localization.Away t ≃ₐ[R] Localization.Away r :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  exact ⟨iso.symm.toRingEquiv.isArtinianRing,
    isReduced_of_injective iso.toRingHom iso.injective⟩

private theorem selected_branch_away_artinian_reduced
    (R : Type*) [CommRing R] [IsReduced R]
    (p : Ideal R) [p.IsPrime] (r : R)
    (π : Localization.AtPrime p) (e : ℕ) (he : e ≠ 0)
    (hassoc : Associated (algebraMap R (Localization.AtPrime p) r) (π ^ e))
    [IsArtinianRing (Localization.Away r)] :
    IsArtinianRing (Localization.Away π) ∧
      IsReduced (Localization.Away π) := by
  let : IsArtinianRing
      (Localization.Away (algebraMap R (Localization.AtPrime p) r)) :=
    local_branch_generic_artinian R p r
  let : IsReduced
      (Localization.Away (algebraMap R (Localization.AtPrime p) r)) :=
    local_branch_generic_reduced R p r
  exact generic_reduced_artinian_change_parameter
    (Localization.AtPrime p) _ π e he hassoc

theorem selected_branch_away_artinian_reduced_of_generic_equiv
    (A B D K L E : Type*) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D]
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K E]
    (πA : A)
    (equiv : Localization.Away (algebraMap A (B ⊗[A] D) πA) ≃+* (L ⊗[K] E))
    (q : Ideal ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D))) [q.IsPrime]
    (π : Localization.AtPrime q) (e : ℕ) (he : e ≠ 0)
    (hassoc : Associated
      (algebraMap ((B ⊗[A] D) ⧸ nilradical (B ⊗[A] D)) (Localization.AtPrime q)
        (Ideal.Quotient.mk _ (algebraMap A (B ⊗[A] D) πA)))
      (π ^ e)) :
    IsArtinianRing (Localization.Away π) ∧ IsReduced (Localization.Away π) := by
  let S := B ⊗[A] D
  let R := S ⧸ nilradical S
  let r : R := Ideal.Quotient.mk (nilradical S) (algebraMap A S πA)
  have hgeneric := artinian_reduced_away_from_generic_equiv A B D K L E πA equiv
  let : IsArtinianRing (Localization.Away r) := hgeneric.1
  let : IsReduced R := isReduced_quotient_nilradical S
  exact selected_branch_away_artinian_reduced R q r π e he hassoc

private noncomputable def tensor_quotient_specialFiber_equiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (J : Ideal C) :
    ((B ⊗[A] C) ⧸ J.map
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C)) ≃+*
      B ⊗[A] (C ⧸ J) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) A C B J).symm.toRingEquiv

private noncomputable def tensor_quotient_left_of_zero_ideal
    (A B E : Type*) [CommRing A] [CommRing B] [CommRing E]
    [Algebra A B] [Algebra A E] (J : Ideal B)
    (hzero : J.map (algebraMap B (B ⊗[A] E)) = ⊥) :
    B ⊗[A] E ≃+* (B ⧸ J) ⊗[A] E := by
  let equiv : ((B ⊗[A] E) ⧸ J.map (algebraMap B (B ⊗[A] E))) ≃+*
      B ⊗[A] E :=
    (Ideal.quotEquivOfEq hzero).trans (RingEquiv.quotientBot _)
  exact equiv.symm.trans
    ((Algebra.TensorProduct.quotientTensorEquiv (R := A) A E B J).symm.toRingEquiv)

private theorem tensor_base_ideal_vanishes
    (A B E : Type*) [CommRing A] [CommRing B] [CommRing E]
    [Algebra A B] [Algebra A E] (I : Ideal A)
    (hI : I ≤ RingHom.ker (algebraMap A E)) :
    (I.map (algebraMap A B)).map (algebraMap B (B ⊗[A] E)) = ⊥ := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B (B ⊗[A] E)]
  apply (Ideal.map_eq_bot_iff_le_ker (algebraMap A (B ⊗[A] E))).mpr
  intro a ha
  change algebraMap A (B ⊗[A] E) a = 0
  rw [Algebra.TensorProduct.algebraMap_apply', RingHom.mem_ker.mp (hI ha)]
  simp

private noncomputable def tensor_quotient_base_ideal_equiv
    (A B E : Type*) [CommRing A] [CommRing B] [CommRing E]
    [Algebra A B] [Algebra A E] (I : Ideal A)
    (hI : I ≤ RingHom.ker (algebraMap A E)) :
    B ⊗[A] E ≃+* (B ⧸ I.map (algebraMap A B)) ⊗[A] E :=
  tensor_quotient_left_of_zero_ideal A B E _
    (tensor_base_ideal_vanishes A B E I hI)

private noncomputable def tensor_to_residue_over_base
    (A B E : Type*) [CommRing A] [CommRing B] [CommRing E]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra A E]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hkill : IsLocalRing.maximalIdeal A ≤
      RingHom.ker (algebraMap A E)) :
    B ⊗[A] E ≃+* (IsLocalRing.ResidueField B) ⊗[A] E :=
  (tensor_quotient_base_ideal_equiv A B E (IsLocalRing.maximalIdeal A) hkill).trans
    (Algebra.TensorProduct.congr
      (Ideal.quotientEquivAlgOfEq A hweak)
      (AlgEquiv.refl (R := A) (A₁ := E))).toRingEquiv

private noncomputable def residue_tensor_change_base
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] :
    (IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
      (IsLocalRing.ResidueField C) ≃ₐ[IsLocalRing.ResidueField B]
    (IsLocalRing.ResidueField B) ⊗[A]
      (IsLocalRing.ResidueField C) := by
  have towerB : IsScalarTower A (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (IsLocalRing.ResidueField.map_residue (algebraMap A B) x).symm
  have towerC : IsScalarTower A (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (IsLocalRing.ResidueField.map_residue (algebraMap A C) x).symm
  letI := towerB
  letI := towerC
  haveI : TensorProduct.CompatibleSMul A (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField C) :=
    .of_algebraMap_surjective _ _ Ideal.Quotient.mk_surjective
  exact Algebra.TensorProduct.equivOfCompatibleSMul A (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B)
    (IsLocalRing.ResidueField C)

private noncomputable def tensor_specialFiber_residue_equiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hkill : IsLocalRing.maximalIdeal A ≤
      RingHom.ker (algebraMap A (IsLocalRing.ResidueField C))) :
    B ⊗[A] (IsLocalRing.ResidueField C) ≃+*
      (IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField C) :=
  (tensor_to_residue_over_base A B (IsLocalRing.ResidueField C) hweak hkill).trans
    (residue_tensor_change_base A B C).symm.toRingEquiv

private theorem local_residue_kills_source_maximal
    (A C : Type*) [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C]
    [Algebra A C] [IsLocalHom (algebraMap A C)] :
    IsLocalRing.maximalIdeal A ≤
      RingHom.ker (algebraMap A (IsLocalRing.ResidueField C)) := by
  have hcomap : (IsLocalRing.maximalIdeal C).comap (algebraMap A C) =
      IsLocalRing.maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap (algebraMap A C)
  intro a ha
  apply RingHom.mem_ker.mpr
  change (Ideal.Quotient.mk _ (algebraMap A C a)) = 0
  rw [← hcomap] at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

private noncomputable def tensor_specialFiber_quotient_equiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    ((B ⊗[A] C) ⧸ (IsLocalRing.maximalIdeal C).map
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C)) ≃+*
      (IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField C) :=
  (tensor_quotient_specialFiber_equiv A B C (IsLocalRing.maximalIdeal C)).trans
    (tensor_specialFiber_residue_equiv A B C hweak
      (local_residue_kills_source_maximal A C))

private theorem reduced_artinian_atPrime_isField
    (R : Type*) [CommRing R] [IsReduced R] [IsArtinianRing R]
    (p : Ideal R) [p.IsPrime] :
    IsField (Localization.AtPrime p) := by
  have : IsArtinianRing (Localization.AtPrime p) := artinian_of_isLocalization p.primeCompl
  have : IsReduced (Localization.AtPrime p) :=
    isReduced_localizationPreserves p.primeCompl _ inferInstance
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

private theorem selected_fiber_quotient_isField
    (C R : Type*) [CommRing C] [CommRing R]
    [IsLocalRing C] [Algebra C R]
    [IsReduced ((IsLocalRing.maximalIdeal C).Fiber R)]
    [IsArtinianRing ((IsLocalRing.maximalIdeal C).Fiber R)]
    (q : Ideal ((IsLocalRing.maximalIdeal C).Fiber R)) [q.IsPrime] :
    let r := q.comap
      (Algebra.TensorProduct.includeRight : R →ₐ[C]
        (IsLocalRing.maximalIdeal C).Fiber R)
    IsField ((Localization.AtPrime r) ⧸
      ((IsLocalRing.maximalIdeal C).map (algebraMap C R)).map
        (algebraMap R (Localization.AtPrime r))) := by
  dsimp only
  have hfield : IsField (Localization.AtPrime q) :=
    reduced_artinian_atPrime_isField _ q
  exact (Ideal.Fiber.algEquivAux₂ (IsLocalRing.maximalIdeal C) q).symm.toRingEquiv.isField hfield

private noncomputable def localFiber_equiv_quotient
    (C R : Type*) [CommRing C] [CommRing R]
    [IsLocalRing C] [Algebra C R] :
    (IsLocalRing.maximalIdeal C).Fiber R ≃+*
      R ⧸ (IsLocalRing.maximalIdeal C).map (algebraMap C R) := by
  let m := IsLocalRing.maximalIdeal C
  let residueEquiv : (C ⧸ m) ≃ₐ[C] m.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom C (C ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  exact ((Algebra.TensorProduct.congr residueEquiv.symm
    (AlgEquiv.refl : R ≃ₐ[C] R)).trans
    ((Algebra.TensorProduct.comm C (C ⧸ m) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R m).symm.restrictScalars C))).toRingEquiv

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem local_tensor_fiber_reduced_artinian
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    [Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C)] :
    IsReduced ((IsLocalRing.maximalIdeal C).Fiber (B ⊗[A] C)) ∧
      IsArtinianRing ((IsLocalRing.maximalIdeal C).Fiber (B ⊗[A] C)) := by
  let : Algebra C (B ⊗[A] C) :=
    (Algebra.TensorProduct.includeRight (R := A) (A := B)).toAlgebra
  let e : (IsLocalRing.maximalIdeal C).Fiber (B ⊗[A] C) ≃+*
      (IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField C) :=
    (localFiber_equiv_quotient C (B ⊗[A] C)).trans
      (tensor_specialFiber_quotient_equiv A B C hweak)
  have : IsReduced ((IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
      (IsLocalRing.ResidueField C)) :=
    reduced_residue_tensor_of_separable _ _ _ hsep
  have : IsArtinianRing ((IsLocalRing.ResidueField B) ⊗[IsLocalRing.ResidueField A]
      (IsLocalRing.ResidueField C)) :=
    artinian_generic_tensor _ _ _
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.symm.isArtinianRing⟩

private theorem selected_tensor_fiber_quotient_isField
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    [Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C)]
    (q : Ideal ((IsLocalRing.maximalIdeal C).Fiber (B ⊗[A] C))) [q.IsPrime] :
    let r := q.comap
      (Algebra.TensorProduct.includeRight : (B ⊗[A] C) →ₐ[C]
        (IsLocalRing.maximalIdeal C).Fiber (B ⊗[A] C))
    IsField ((Localization.AtPrime r) ⧸
      ((IsLocalRing.maximalIdeal C).map
        (algebraMap C (B ⊗[A] C))).map
          (algebraMap (B ⊗[A] C) (Localization.AtPrime r))) := by
  obtain ⟨hreduced, hartinian⟩ :=
    local_tensor_fiber_reduced_artinian A B C hweak hsep
  let := hreduced
  let := hartinian
  exact selected_fiber_quotient_isField C (B ⊗[A] C) q

private theorem exists_fiber_prime_over_local_branch
    (C R : Type*) [CommRing C] [CommRing R]
    [IsLocalRing C] [Algebra C R]
    (r : Ideal R) [r.IsPrime]
    (hlie : r.comap (algebraMap C R) =
      IsLocalRing.maximalIdeal C) :
    ∃ q : Ideal ((IsLocalRing.maximalIdeal C).Fiber R),
      q.IsPrime ∧
        q.comap (Algebra.TensorProduct.includeRight : R →ₐ[C]
          (IsLocalRing.maximalIdeal C).Fiber R) = r := by
  let : r.LiesOver (IsLocalRing.maximalIdeal C) := ⟨hlie.symm⟩
  let q : Ideal ((IsLocalRing.maximalIdeal C).Fiber R) :=
    ((PrimeSpectrum.primesOverOrderIsoFiber C R
      (IsLocalRing.maximalIdeal C))
        ⟨r, inferInstance, inferInstance⟩).asIdeal
  have : q.IsPrime := inferInstance
  refine ⟨q, inferInstance, ?_⟩
  rw [show q = ((PrimeSpectrum.primesOverOrderIsoFiber C R
      (IsLocalRing.maximalIdeal C))
        ⟨r, inferInstance, inferInstance⟩).asIdeal from rfl,
      ← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,
      OrderIso.symm_apply_apply]

/-- An `R`-algebra equivalence induces an equivalence of the quotients by the extension of `I`. -/
private noncomputable def quotient_map_equiv_of_algEquiv
    {R P Q : Type*} [CommRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    (e : P ≃ₐ[R] Q) (I : Ideal R) :
    (P ⧸ I.map (algebraMap R P)) ≃+* (Q ⧸ I.map (algebraMap R Q)) :=
  Ideal.quotientEquiv _ _ e.toRingEquiv (by
    rw [Ideal.map_map]
    exact (congrArg (I.map ·) (RingHom.ext e.commutes)).symm)

private noncomputable def localizedQuotient_equiv_of_prime_eq
    (R : Type*) [CommRing R] (I : Ideal R)
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p = q) :
    (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≃+*
      (Localization.AtPrime q ⧸ I.map (algebraMap R (Localization.AtPrime q))) := by
  have hM : p.primeCompl = q.primeCompl := by
    ext x
    change (x : R) ∉ p ↔ x ∉ q
    rw [hpq]
  letI : IsLocalization q.primeCompl (Localization.AtPrime p) := by
    rw [← hM]
    infer_instance
  let e : Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact quotient_map_equiv_of_algEquiv e I

private theorem selected_tensor_localization_quotient_isField
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    [Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C)]
    (r : Ideal (B ⊗[A] C)) [r.IsPrime]
    (hlie : r.comap (algebraMap C (B ⊗[A] C)) =
      IsLocalRing.maximalIdeal C) :
    IsField ((Localization.AtPrime r) ⧸
      ((IsLocalRing.maximalIdeal C).map
        (algebraMap C (B ⊗[A] C))).map
          (algebraMap (B ⊗[A] C) (Localization.AtPrime r))) := by
  obtain ⟨q, hprime, hq⟩ := exists_fiber_prime_over_local_branch
    C (B ⊗[A] C) r hlie
  let := hprime
  have hfield := selected_tensor_fiber_quotient_isField A B C hweak hsep q
  let e := localizedQuotient_equiv_of_prime_eq (B ⊗[A] C)
    ((IsLocalRing.maximalIdeal C).map (algebraMap C (B ⊗[A] C)))
    (q.comap (Algebra.TensorProduct.includeRight : (B ⊗[A] C) →ₐ[C]
      (IsLocalRing.maximalIdeal C).Fiber (B ⊗[A] C))) r hq
  exact e.symm.isField hfield

theorem tensor_branch_comap_right
    (A B C S : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing S]
    [Algebra A B] [Algebra A C] [Algebra C S]
    (g : (B ⊗[A] C) →+* S)
    (hright : ∀ c : C, g
      ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c) =
        algebraMap C S c)
    (q : Ideal S) :
    (q.comap g).comap
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) =
    q.comap (algebraMap C S) := by
  ext c
  simp only [Ideal.mem_comap, hright]

private theorem prime_over_base_prime_survives_localization
    (C R S : Type*) [CommRing C] [CommRing R] [CommRing S]
    [Algebra C R] [Algebra R S]
    (p : Ideal C) [p.IsPrime]
    [IsLocalization (p.primeCompl.map (algebraMap C R)) S]
    (r : Ideal R) [r.IsPrime]
    (hlie : r.comap (algebraMap C R) = p) :
    ∃ q : Ideal S, q.IsPrime ∧
      q.comap (algebraMap R S) = r := by
  have hdisj : Disjoint (r : Set R)
      (p.primeCompl.map (algebraMap C R)) :=
    Ideal.disjoint_map_primeCompl_iff_comap_le.mpr (le_of_eq hlie)
  let q : Ideal S := r.map (algebraMap R S)
  have hprime : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ S r inferInstance hdisj.symm
  refine ⟨q, hprime, ?_⟩
  exact IsLocalization.under_map_of_isPrime_disjoint _ S inferInstance hdisj.symm

/-- `B ⊗[A] D` is the localization of `B ⊗[A] C` at the image of `p.primeCompl`. -/
private theorem isLocalization_tensor_of_atPrime
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    [Algebra (B ⊗[A] C) (B ⊗[A] D)]
    (hf : algebraMap (B ⊗[A] C) (B ⊗[A] D) =
      (Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A C D)).toRingHom) :
    IsLocalization
      (p.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := B)))
      (B ⊗[A] D) := by
  have : IsScalarTower B (B ⊗[A] C) (B ⊗[A] D) :=
    IsScalarTower.of_algebraMap_eq (by
      intro x
      simp [hf, Algebra.TensorProduct.map_tmul])
  exact IsLocalization.tensorProduct_tensorProduct_right A B p.primeCompl D (by
    ext x
    simp [hf, Algebra.TensorProduct.map_tmul])

private theorem tensor_base_prime_survives_localization
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    (r : Ideal (B ⊗[A] C)) [r.IsPrime]
    (hlie : r.comap (Algebra.TensorProduct.includeRight (R := A) (A := B)) = p) :
    ∃ q : Ideal (B ⊗[A] D), q.IsPrime ∧
      q.comap ((Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A C D)).toRingHom) = r := by
  let : Algebra C (B ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
  let f : (B ⊗[A] C) →ₐ[A] (B ⊗[A] D) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A C D)
  let : Algebra (B ⊗[A] C) (B ⊗[A] D) := f.toAlgebra
  have : IsLocalization
      (p.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := B)))
      (B ⊗[A] D) := isLocalization_tensor_of_atPrime A B C D p rfl
  have : IsLocalization
      (p.primeCompl.map (algebraMap C (B ⊗[A] C))) (B ⊗[A] D) := by
    convert (inferInstance : IsLocalization
      (p.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := B)))
      (B ⊗[A] D)) using 1
    congr 1
  simpa [f, RingHom.algebraMap_toAlgebra] using
    prime_over_base_prime_survives_localization C (B ⊗[A] C) (B ⊗[A] D)
      p r hlie

private theorem tensor_basechange_ideal_map
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D]
    (I : Ideal C) :
    (I.map (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
      (Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A C D)).toRingHom =
      (I.map (algebraMap C D)).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)) := by
  change (I.map (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom).map
      (Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A C D)).toRingHom =
    (I.map (algebraMap C D)).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

private theorem base_maximal_ideal_after_tensor_localization
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D] [IsLocalRing D]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    (q : Ideal (B ⊗[A] D)) [q.IsPrime] :
    (((p.map (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
      (Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A C D)).toRingHom).map
      (algebraMap (B ⊗[A] D) (Localization.AtPrime q))) =
    (((IsLocalRing.maximalIdeal D).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
      (algebraMap (B ⊗[A] D) (Localization.AtPrime q))) := by
  rw [tensor_basechange_ideal_map A B C D p,
    IsLocalization.AtPrime.map_eq_maximalIdeal p D]

private noncomputable def atPrime_after_tensor_base_localization_equiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (q : Ideal S) [q.IsPrime] :
    Localization.AtPrime (q.comap (algebraMap R S)) ≃ₐ[R]
      Localization.AtPrime q := by
  letI : IsLocalization.AtPrime (Localization.AtPrime q)
      (q.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsLocalization.algEquiv
    (q.comap (algebraMap R S)).primeCompl
    (Localization.AtPrime (q.comap (algebraMap R S)))
    (Localization.AtPrime q)

private theorem field_quotient_of_tensor_base_localization
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (q : Ideal S) [q.IsPrime] (I : Ideal R)
    (hfield : IsField (Localization.AtPrime q ⧸
      I.map (algebraMap R (Localization.AtPrime q)))) :
    IsField (Localization.AtPrime (q.comap (algebraMap R S)) ⧸
      I.map (algebraMap R
        (Localization.AtPrime (q.comap (algebraMap R S))))) := by
  exact (quotient_map_equiv_of_algEquiv
    (atPrime_after_tensor_base_localization_equiv R S M q) I).isField hfield

private theorem tensor_localized_branch_contracts_to_maximal
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    [IsLocalRing D]
    (r : Ideal (B ⊗[A] C))
    (hlie : r.comap (Algebra.TensorProduct.includeRight (R := A) (A := B)) = p)
    (q : Ideal (B ⊗[A] D))
    (hq : q.comap ((Algebra.TensorProduct.map (AlgHom.id A B)
      (IsScalarTower.toAlgHom A C D)).toRingHom) = r) :
    q.comap (Algebra.TensorProduct.includeRight (R := A) (A := B)) =
      IsLocalRing.maximalIdeal D := by
  let f : (B ⊗[A] C) →ₐ[A] (B ⊗[A] D) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A C D)
  let : Algebra D (B ⊗[A] D) :=
    (Algebra.TensorProduct.includeRight (R := A) (A := B)).toAlgebra
  have hunder : (q.comap (algebraMap D (B ⊗[A] D))).comap
      (algebraMap C D) = p := by
    ext c
    change ((1 : B) ⊗ₜ[A] algebraMap C D c ∈ q) ↔ c ∈ p
    rw [← show f ((1 : B) ⊗ₜ[A] c) = (1 : B) ⊗ₜ[A] algebraMap C D c by
      simp [f, Algebra.TensorProduct.map_tmul]]
    change ((1 : B) ⊗ₜ[A] c ∈ q.comap f.toRingHom) ↔ c ∈ p
    rw [hq]
    exact (Ideal.ext_iff.mp hlie c)
  have heq := (IsLocalization.orderEmbedding p.primeCompl D).injective
    (hunder.trans (IsLocalization.AtPrime.under_maximalIdeal D p).symm)
  exact heq

private theorem selected_branch_localized_specialFiber_isField
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A D)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    (r : Ideal (B ⊗[A] C)) [r.IsPrime]
    (hlie : r.comap (Algebra.TensorProduct.includeRight (R := A) (A := B)) = p) :
    ∃ (q : Ideal (B ⊗[A] D)), ∃ hq : q.IsPrime,
      letI : q.IsPrime := hq
      q.comap ((Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A C D)).toRingHom) = r ∧
      IsField ((Localization.AtPrime q) ⧸
        ((IsLocalRing.maximalIdeal D).map
          (algebraMap D (B ⊗[A] D))).map
          (algebraMap (B ⊗[A] D) (Localization.AtPrime q))) := by
  obtain ⟨q, hprime, hq⟩ :=
    tensor_base_prime_survives_localization A B C D p r hlie
  let : q.IsPrime := hprime
  have hmax := tensor_localized_branch_contracts_to_maximal
    A B C D p r hlie q hq
  refine ⟨q, hprime, hq, ?_⟩
  exact selected_tensor_localization_quotient_isField A B D hweak hsep q hmax

theorem selected_global_tensor_specialFiber_isField
    (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    [Algebra A D] [IsScalarTower A C D]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A D)]
    (hweak : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)]
    (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p]
    (r : Ideal (B ⊗[A] C)) [r.IsPrime]
    (hlie : r.comap (Algebra.TensorProduct.includeRight (R := A) (A := B)) = p) :
    IsField (Localization.AtPrime r ⧸
      (p.map (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
        (algebraMap (B ⊗[A] C) (Localization.AtPrime r))) := by
  obtain ⟨q, hprime, hq, hfield⟩ :=
    selected_branch_localized_specialFiber_isField A B C D
      hweak hsep p r hlie
  let : q.IsPrime := hprime
  let f : (B ⊗[A] C) →ₐ[A] (B ⊗[A] D) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A C D)
  let : Algebra (B ⊗[A] C) (B ⊗[A] D) := f.toAlgebra
  have : IsLocalization
      (p.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := B)))
      (B ⊗[A] D) := isLocalization_tensor_of_atPrime A B C D p rfl
  have hideal :
      (p.map (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
          (algebraMap (B ⊗[A] C) (Localization.AtPrime q)) =
        ((IsLocalRing.maximalIdeal D).map (algebraMap D (B ⊗[A] D))).map
          (algebraMap (B ⊗[A] D) (Localization.AtPrime q)) := by
    have hrightIdeal :
        (IsLocalRing.maximalIdeal D).map (algebraMap D (B ⊗[A] D)) =
        (IsLocalRing.maximalIdeal D).map
          (Algebra.TensorProduct.includeRight (R := A) (A := B)) := by
      rfl
    rw [hrightIdeal]
    rw [IsScalarTower.algebraMap_eq (B ⊗[A] C) (B ⊗[A] D),
      ← Ideal.map_map]
    simpa [f, RingHom.algebraMap_toAlgebra] using
      base_maximal_ideal_after_tensor_localization A B C D p q
  have hfield' : IsField (Localization.AtPrime q ⧸
      (p.map (Algebra.TensorProduct.includeRight (R := A) (A := B))).map
        (algebraMap (B ⊗[A] C) (Localization.AtPrime q))) := by
    rw [hideal]
    exact hfield
  have hglobal := field_quotient_of_tensor_base_localization
    (B ⊗[A] C) (B ⊗[A] D)
    (p.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := B)))
    q (p.map (Algebra.TensorProduct.includeRight (R := A) (A := B))) hfield'
  have hqr : q.comap (algebraMap (B ⊗[A] C) (B ⊗[A] D)) = r := by
    simpa [f, RingHom.algebraMap_toAlgebra] using hq
  cases hqr
  exact hglobal

end ReducedTensorLocalization

end

end

end IsDiscreteValuationRing
