module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.StrictHenselization
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.StrictHenselization

/-!
# The generic point count and the generic separable degree

This file shows that a strict henselization of a local ring for a quasi-finite map of finite type
is finite over one of the target, compares compatible strict henselizations, and defines the
geometric point count of the generic fibre and the generic separable degree of a morphism,
together with their characterizing properties and their invariance under ind-étale maps.
-/

public section

open AlgebraicGeometry
open IsLocalRing
open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- A local ring is its own localization at its maximal ideal. -/
private theorem isLocalization_atPrime_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalization.AtPrime R (maximalIdeal R) :=
  IsLocalization.of_le_isUnit fun _ h => notMem_maximalIdeal.mp h

/-- The composite of local ring maps along a scalar tower is local. -/
private theorem isLocalHom_algebraMap_of_tower (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] :
    IsLocalHom (algebraMap R T) := by
  rw [IsScalarTower.algebraMap_eq R S T]
  exact RingHom.isLocalHom_comp _ _

private theorem isLocalHom_of_compatible_strictHenselizations
    {R S Rsh Ssh : Type u} [CommRing R] [CommRing S] [CommRing Rsh]
    [CommRing Ssh] [IsLocalRing R] [IsLocalRing S] [IsLocalRing Rsh] [IsLocalRing Ssh]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra R Rsh]
    [Algebra S Ssh] [IsLocalHom (algebraMap S Ssh)]
    [Algebra R Ssh] [Algebra Rsh Ssh] [IsScalarTower R S Ssh]
    [IsScalarTower R Rsh Ssh]
    (hmaximal : (maximalIdeal R).map (algebraMap R Rsh) = maximalIdeal Rsh) :
    IsLocalHom (algebraMap Rsh Ssh) := by
  apply ((local_hom_TFAE (algebraMap Rsh Ssh)).out 3 1).mp
  rw [← hmaximal, Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rsh Ssh]
  exact ((local_hom_TFAE (algebraMap R Ssh)).out 1 3).mp (isLocalHom_algebraMap_of_tower R S Ssh)

/-- For a quasi-finite map of finite type between local rings, a strict henselization of the
source is finite over one of the target, with purely inseparable residue field extension. -/
@[sga "4 XVII 6.2.6" "special case"]
private theorem finite_strictHenselization_of_finiteType
    {R S Rsh Ssh : Type u} [CommRing R] [CommRing S] [CommRing Rsh]
    [CommRing Ssh] [IsLocalRing R] [IsLocalRing S] [IsLocalRing Rsh]
    [IsLocalRing Ssh] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]
    [Algebra R Rsh] [Algebra S Ssh] [Algebra R Ssh] [Algebra Rsh Ssh]
    [IsScalarTower R S Ssh] [IsScalarTower R Rsh Ssh]
    [IsLocalHom (algebraMap Rsh Ssh)]
    (κR κS : Type u) [Field κR] [Field κS]
    [Algebra (maximalIdeal R).ResidueField κR]
    [Algebra (maximalIdeal S).ResidueField κS]
    [IsSepClosure (maximalIdeal R).ResidueField κR]
    [IsSepClosure (maximalIdeal S).ResidueField κS]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh) :
    Module.Finite Rsh Ssh ∧ Module.Finite (ResidueField Rsh) (ResidueField Ssh) ∧
      IsPurelyInseparable (ResidueField Rsh) (ResidueField Ssh) := by
  let := hRsh.isLocalHom
  let := hSsh.isLocalHom
  let := isHenselization_residueField_of_strictHenselization R κR Rsh hRsh
  let := isHenselization_residueField_of_strictHenselization S κS Ssh hSsh
  let := isSepClosure_residueField_of_strictHenselization R κR Rsh hRsh
  let := isSepClosure_residueField_of_strictHenselization S κS Ssh hSsh
  let := isLocalization_atPrime_maximalIdeal R
  let := isLocalization_atPrime_maximalIdeal S
  let : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  exact IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt
    (Rp := R) (Sq := S) (Rsh := Rsh) (Ssh := Ssh) (maximalIdeal R) (maximalIdeal S)

private theorem finite_strictHenselization_of_essFiniteType
    {R S Rsh Ssh : Type u} [CommRing R] [CommRing S] [CommRing Rsh]
    [CommRing Ssh] [IsLocalRing R] [IsLocalRing S] [IsLocalRing Rsh]
    [IsLocalRing Ssh] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    [Algebra R Rsh] [Algebra S Ssh] [Algebra R Ssh] [Algebra Rsh Ssh]
    [IsScalarTower R S Ssh] [IsScalarTower R Rsh Ssh]
    [IsLocalHom (algebraMap Rsh Ssh)]
    (κR κS : Type u) [Field κR] [Field κS]
    [Algebra (maximalIdeal R).ResidueField κR]
    [Algebra (maximalIdeal S).ResidueField κS]
    [IsSepClosure (maximalIdeal R).ResidueField κR]
    [IsSepClosure (maximalIdeal S).ResidueField κS]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh) :
    Module.Finite Rsh Ssh ∧ Module.Finite (ResidueField Rsh) (ResidueField Ssh) ∧
      IsPurelyInseparable (ResidueField Rsh) (ResidueField Ssh) := by
  let := hRsh.isLocalHom
  let := hSsh.isLocalHom
  let := isHenselization_residueField_of_strictHenselization R κR Rsh hRsh
  let := isHenselization_residueField_of_strictHenselization S κS Ssh hSsh
  let := isSepClosure_residueField_of_strictHenselization R κR Rsh hRsh
  let := isSepClosure_residueField_of_strictHenselization S κS Ssh hSsh
  let A := Algebra.EssFiniteType.subalgebra R S
  let M := Algebra.EssFiniteType.submonoid R S
  let prime : Ideal A := (maximalIdeal S).comap (algebraMap A S)
  let : prime.IsPrime := Ideal.comap_isPrime _ _
  let := isLocalization_atPrime_maximalIdeal R
  let := isLocalization_atPrime_maximalIdeal S
  let : IsLocalization.AtPrime S prime :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M S (maximalIdeal S)
  let : prime.LiesOver (maximalIdeal R) := by
    constructor
    change maximalIdeal R = ((maximalIdeal S).comap (algebraMap A S)).comap
      (algebraMap R A)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, maximalIdeal_comap]
  let equiv := AlgEquiv.restrictScalars R
    (IsLocalization.algEquiv prime.primeCompl S (Localization.AtPrime prime))
  let : Algebra.QuasiFiniteAt R prime :=
    Algebra.QuasiFinite.of_surjective_algHom equiv.toAlgHom equiv.surjective
  exact IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt
    (Rp := R) (Sq := S) (Rsh := Rsh) (Ssh := Ssh) (maximalIdeal R) prime

private theorem exists_compatible_algEquivs_of_strictHenselizations
    {R S R₁ R₂ S₁ S₂ : Type u}
    [CommRing R] [CommRing S] [CommRing R₁] [CommRing R₂]
    [CommRing S₁] [CommRing S₂] [IsLocalRing R] [IsLocalRing S]
    [IsLocalRing R₁] [IsLocalRing R₂] [IsLocalRing S₁] [IsLocalRing S₂]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    [Algebra R R₁] [Algebra R R₂] [Algebra S S₁] [Algebra S S₂]
    [Algebra R S₁] [Algebra R S₂] [Algebra R₁ S₁] [Algebra R₂ S₂]
    [IsScalarTower R S S₁] [IsScalarTower R S S₂]
    [IsScalarTower R R₁ S₁] [IsScalarTower R R₂ S₂]
    (κR₁ κR₂ κS₁ κS₂ : Type u)
    [Field κR₁] [Field κR₂] [Field κS₁] [Field κS₂]
    [Algebra (maximalIdeal R).ResidueField κR₁]
    [Algebra (maximalIdeal R).ResidueField κR₂]
    [Algebra (maximalIdeal S).ResidueField κS₁]
    [Algebra (maximalIdeal S).ResidueField κS₂]
    [IsSepClosure (maximalIdeal R).ResidueField κR₁]
    [IsSepClosure (maximalIdeal R).ResidueField κR₂]
    [IsSepClosure (maximalIdeal S).ResidueField κS₁]
    [IsSepClosure (maximalIdeal S).ResidueField κS₂]
    (hR₁ : Stacks.StrictHenselization.IsStrictHenselization R κR₁ R₁)
    (hR₂ : Stacks.StrictHenselization.IsStrictHenselization R κR₂ R₂)
    (hS₁ : Stacks.StrictHenselization.IsStrictHenselization S κS₁ S₁)
    (hS₂ : Stacks.StrictHenselization.IsStrictHenselization S κS₂ S₂) :
    ∃ equivR : R₁ ≃ₐ[R] R₂, ∃ equivS : S₁ ≃ₐ[S] S₂,
      ∀ element : R₁,
        equivS (algebraMap R₁ S₁ element) = algebraMap R₂ S₂ (equivR element) := by
  let := hR₁.isLocalHom
  let := hR₂.isLocalHom
  let := hS₁.isLocalHom
  let := hS₂.isLocalHom
  let := isLocalHom_algebraMap_of_tower R S S₁
  let := isLocalHom_algebraMap_of_tower R S S₂
  let := isLocalHom_of_compatible_strictHenselizations (S := S) (Ssh := S₁)
    hR₁.maximalIdeal_map
  let := isLocalHom_of_compatible_strictHenselizations (S := S) (Ssh := S₂)
    hR₂.maximalIdeal_map
  let := hR₁.henselian
  let := hR₂.henselian
  let := hS₂.henselian
  let := isSepClosure_residueField_of_strictHenselization R κR₁ R₁ hR₁
  let := isSepClosure_residueField_of_strictHenselization R κR₂ R₂ hR₂
  obtain ⟨_, _, hpure⟩ := finite_strictHenselization_of_essFiniteType
    (Rsh := R₂) (Ssh := S₂) κR₂ κS₂ hR₂ hS₂
  let := hpure
  obtain ⟨equivS⟩ := exists_algEquiv_of_strictHenselization S κS₁ κS₂ S₁ S₂ hS₁ hS₂
  let equivResidueS := (ResidueField.mapAlgEquiv' equivS).restrictScalars (ResidueField R)
  let inclusion₁ := IsScalarTower.toAlgHom (ResidueField R) (ResidueField R₁)
    (ResidueField S₁)
  let inclusion₂ := IsScalarTower.toAlgHom (ResidueField R) (ResidueField R₂)
    (ResidueField S₂)
  let residueHom := equivResidueS.toAlgHom.comp inclusion₁
  obtain ⟨factor, hfactor⟩ := exists_algHom_factor_of_isPurelyInseparable
    (B := ResidueField R₂) residueHom
  let equivResidueR := AlgEquiv.ofBijective factor
    (algHom_bijective_of_isSepClosure factor)
  have hcompat : equivResidueR.toRingHom.comp
      ((residue R₁).comp (algebraMap R R₁)) =
      (residue R₂).comp (algebraMap R R₂) := by
    ext element
    change factor (residue R₁ (algebraMap R R₁ element)) = _
    rw [← ResidueField.algebraMap_residue, factor.commutes,
      ResidueField.algebraMap_residue]
    rfl
  obtain ⟨equivR, hequivR⟩ := exists_algEquiv_of_indEtale_of_residueFieldEquiv
    hR₁.isFilteredColimitEtale hR₂.isFilteredColimitEtale equivResidueR.toRingEquiv hcompat
  let forward := (equivS.restrictScalars R).toAlgHom.comp
    (IsScalarTower.toAlgHom R R₁ S₁)
  let backward := (IsScalarTower.toAlgHom R R₂ S₂).comp equivR.toAlgHom
  have hforward : (residue S₂).comp forward.toRingHom =
      residueHom.toRingHom.comp (residue R₁) := by
    ext element
    change residue S₂ (equivS (algebraMap R₁ S₁ element)) =
      equivResidueS (inclusion₁ (residue R₁ element))
    change residue S₂ (equivS (algebraMap R₁ S₁ element)) =
      equivResidueS (algebraMap (ResidueField R₁) (ResidueField S₁) (residue R₁ element))
    rw [ResidueField.algebraMap_residue]
    exact (ResidueField.mapAlgEquiv'_residue equivS _).symm
  have hbackward : (residue S₂).comp backward.toRingHom =
      residueHom.toRingHom.comp (residue R₁) := by
    ext element
    change residue S₂ (algebraMap R₂ S₂ (equivR element)) = residueHom (residue R₁ element)
    rw [← ResidueField.algebraMap_residue (R := R₂) (S := S₂)]
    change inclusion₂ (residue R₂ (equivR element)) = residueHom (residue R₁ element)
    have hequivApply : residue R₂ (equivR element) = factor (residue R₁ element) :=
      RingHom.congr_fun hequivR element
    rw [hequivApply]
    exact AlgHom.congr_fun hfactor (residue R₁ element)
  have hcompatFinal : residueHom.toRingHom.comp
      ((residue R₁).comp (algebraMap R R₁)) =
      (residue S₂).comp (algebraMap R S₂) := by
    ext element
    change residueHom (residue R₁ (algebraMap R R₁ element)) =
      residue S₂ (algebraMap R S₂ element)
    have hforwardApply : residueHom (residue R₁ (algebraMap R R₁ element)) =
        residue S₂ (forward (algebraMap R R₁ element)) :=
      (RingHom.congr_fun hforward (algebraMap R R₁ element)).symm
    rw [hforwardApply]
    exact congrArg (residue S₂) (forward.commutes element)
  obtain ⟨_, _, hunique⟩ :=
    StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      hR₁.isFilteredColimitEtale residueHom.toRingHom hcompatFinal
  have hforwardLocal : IsLocalHom forward := by
    constructor
    intro element hunit
    change IsUnit (equivS (algebraMap R₁ S₁ element)) at hunit
    have hunit' : IsUnit (equivS.symm (equivS (algebraMap R₁ S₁ element))) :=
      hunit.map equivS.symm.toRingHom
    exact (inferInstance : IsLocalHom (algebraMap R₁ S₁)).map_nonunit element
      (by simpa only [AlgEquiv.symm_apply_apply] using hunit')
  have hbackwardLocal : IsLocalHom backward := by
    constructor
    intro element hunit
    have hunit' := (inferInstance : IsLocalHom (algebraMap R₂ S₂)).map_nonunit _ hunit
    simpa using hunit'.map equivR.symm.toRingHom
  have heq : forward = backward :=
    (hunique forward ⟨hforwardLocal, hforward⟩).trans
      (hunique backward ⟨hbackwardLocal, hbackward⟩).symm
  exact ⟨equivR, equivS, fun element => AlgHom.congr_fun heq element⟩

theorem existsUnique_minimalPrime_of_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization R κ Rsh)
    (hunibranch : _root_.IsGeometricallyUnibranch R) :
    ∃! prime : Ideal Rsh, prime ∈ minimalPrimes Rsh := by
  let := hsh.isLocalHom
  let quotientEquiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    AlgEquiv.Algebra.isSeparable quotientEquiv
  let : Algebra (ResidueField R) κ :=
    ((algebraMap (maximalIdeal R).ResidueField κ).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsSeparable (ResidueField R) κ :=
    Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κ
  let quotientEquivSh := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField Rsh) (maximalIdeal Rsh).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal Rsh))
  let equiv : κ ≃ₐ[ResidueField R] ResidueField Rsh :=
    { hsh.residueFieldEquiv.trans quotientEquivSh.symm.toRingEquiv with
      commutes' := by
        intro element
        obtain ⟨element, rfl⟩ := residue_surjective element
        apply quotientEquivSh.injective
        change quotientEquivSh (quotientEquivSh.symm
          (hsh.residueFieldEquiv (algebraMap (ResidueField R) κ (residue R element)))) = _
        rw [quotientEquivSh.apply_symm_apply, ResidueField.algebraMap_residue]
        change hsh.residueFieldEquiv
          (algebraMap (maximalIdeal R).ResidueField κ
            (algebraMap R (maximalIdeal R).ResidueField element)) =
          algebraMap Rsh (maximalIdeal Rsh).ResidueField (algebraMap R Rsh element)
        exact (RingHom.congr_fun hsh.residueFieldEquiv_comp
          (algebraMap R (maximalIdeal R).ResidueField element)).trans
          (Ideal.ResidueField.map_algebraMap _ _ _ _ _) }
  let : IsSepClosed (maximalIdeal Rsh).ResidueField := hsh.sepClosed
  let : IsSepClosed (ResidueField Rsh) :=
    IsSepClosed.of_ringEquiv quotientEquivSh.toRingEquiv
  let : IsSepClosure (ResidueField R) (ResidueField Rsh) :=
    ⟨inferInstance, AlgEquiv.Algebra.isSeparable equiv⟩
  let : IsHenselization R (ResidueField Rsh) Rsh :=
    ⟨hsh.henselian, hsh.isFilteredColimitEtale, RingEquiv.refl _, fun _ => rfl⟩
  exact (isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
    R Rsh (ResidueField Rsh)).mp hunibranch

/-- When the target is an algebraic closure, geometric points of a finite field
extension are counted by its separable degree. -/
private theorem algHom_card_eq_finSepDegree
    (F E K : Type*) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Algebra.IsAlgebraic F E] [IsAlgClosure F K] :
    Nat.card (E →ₐ[F] K) = Field.finSepDegree F E := by
  let _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  exact (Field.finSepDegree_eq_of_isAlgClosed F E K).symm

/-- The number of geometric points is unchanged when the finite algebra is
replaced by an isomorphic algebra. -/
private theorem algHom_card_eq_of_algEquiv
    (F E E' K : Type*) [CommSemiring F] [CommSemiring E] [CommSemiring E'] [CommSemiring K]
    [Algebra F E] [Algebra F E'] [Algebra F K]
    (e : E ≃ₐ[F] E') :
    Nat.card (E →ₐ[F] K) = Nat.card (E' →ₐ[F] K) :=
  Nat.card_congr
    { toFun := fun φ => φ.comp e.symm
      invFun := fun φ => φ.comp e
      left_inv := fun φ => by ext x; simp
      right_inv := fun φ => by ext x; simp }

/-- The geometric point count of an algebra is unchanged after extending the
base field, provided the target field is given the compatible scalar tower. -/
@[ega "I 6.4.8" "more general"]
private theorem algHom_card_eq_of_fieldExtension
    (F G E K : Type*) [Field F] [Field G] [CommSemiring E] [Field K]
    [Algebra F G] [Algebra F E] [Algebra F K] [Algebra G K]
    [IsScalarTower F G K] :
    Nat.card (E →ₐ[F] K) =
      Nat.card ((G ⊗[F] E) →ₐ[G] K) :=
  Nat.card_congr (AlgHom.liftEquiv F G E K)

/-- Transport the set of geometric points across compatible changes of all
three algebras. -/
private theorem algHom_card_eq_of_compatible_ringEquivs
    (F G E E' K K' : Type*)
    [CommSemiring F] [CommSemiring G] [CommSemiring E] [CommSemiring E']
    [CommSemiring K] [CommSemiring K']
    [Algebra F E] [Algebra G E'] [Algebra F K] [Algebra G K']
    (eF : F ≃+* G) (eE : E ≃+* E') (eK : K ≃+* K')
    (hE : ∀ a : F, eE (algebraMap F E a) = algebraMap G E' (eF a))
    (hK : ∀ a : F, eK (algebraMap F K a) = algebraMap G K' (eF a)) :
    Nat.card (E →ₐ[F] K) = Nat.card (E' →ₐ[G] K') := by
  let forward (φ : E →ₐ[F] K) : E' →ₐ[G] K' :=
    { toRingHom := eK.toRingHom.comp (φ.toRingHom.comp eE.symm.toRingHom)
      commutes' := by
        intro b
        let a := eF.symm b
        have hab : eF a = b := eF.apply_symm_apply b
        have ha : eE.symm (algebraMap G E' b) = algebraMap F E a := by
          rw [← hab, ← hE a, eE.symm_apply_apply]
        calc
          eK (φ (eE.symm (algebraMap G E' b))) = eK (φ (algebraMap F E a)) := by rw [ha]
          _ = eK (algebraMap F K a) := by rw [AlgHom.commutes]
          _ = algebraMap G K' b := by rw [hK a, eF.apply_symm_apply] }
  let backward (ψ : E' →ₐ[G] K') : E →ₐ[F] K :=
    { toRingHom := eK.symm.toRingHom.comp (ψ.toRingHom.comp eE.toRingHom)
      commutes' := by
        intro a
        calc
          eK.symm (ψ (eE (algebraMap F E a))) =
              eK.symm (ψ (algebraMap G E' (eF a))) := by rw [hE]
          _ = eK.symm (algebraMap G K' (eF a)) := by rw [AlgHom.commutes]
          _ = algebraMap F K a := by rw [← hK a, eK.symm_apply_apply] }
  exact Nat.card_congr
    { toFun := forward
      invFun := backward
      left_inv := by intro φ; ext x; simp [forward, backward]
      right_inv := by intro ψ; ext x; simp [forward, backward] }

/-- The number of geometric points does not depend on which algebraic closure
is used as the target. -/
private theorem algHom_card_eq_of_algClosure
    (F E K K' : Type*) [Field F] [CommSemiring E] [Field K] [Field K']
    [Algebra F E] [Algebra F K] [Algebra F K']
    [IsAlgClosure F K] [IsAlgClosure F K'] :
    Nat.card (E →ₐ[F] K) = Nat.card (E →ₐ[F] K') := by
  let e := IsAlgClosure.equiv F K K'
  exact algHom_card_eq_of_compatible_ringEquivs F F E E K K'
    (RingEquiv.refl F) (RingEquiv.refl E) e (fun _ => rfl) (fun a => e.commutes a)

private theorem algHom_card_tensorProduct_eq_of_compatible_ringEquivs
    (R R' F F' S S' K K' : Type*)
    [CommRing R] [CommRing R'] [CommRing F] [CommRing F']
    [CommRing S] [CommRing S'] [CommRing K] [CommRing K']
    [Algebra R F] [Algebra R' F'] [Algebra R S] [Algebra R' S']
    [Algebra F K] [Algebra F' K']
    (equivR : R ≃+* R') (equivF : F ≃+* F')
    (equivS : S ≃+* S') (equivK : K ≃+* K')
    (hF : ∀ element, equivF (algebraMap R F element) =
      algebraMap R' F' (equivR element))
    (hS : ∀ element, equivS (algebraMap R S element) =
      algebraMap R' S' (equivR element))
    (hK : ∀ element, equivK (algebraMap F K element) =
      algebraMap F' K' (equivF element)) :
    Nat.card ((F ⊗[R] S) →ₐ[F] K) =
      Nat.card ((F' ⊗[R'] S') →ₐ[F'] K') := by
  let : Algebra R K := ((algebraMap F K).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R' K' := ((algebraMap F' K').comp (algebraMap R' F')).toAlgebra
  let : IsScalarTower R' F' K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  calc
    Nat.card ((F ⊗[R] S) →ₐ[F] K) = Nat.card (S →ₐ[R] K) :=
      (Nat.card_congr (AlgHom.liftEquiv R F S K)).symm
    _ = Nat.card (S' →ₐ[R'] K') :=
      algHom_card_eq_of_compatible_ringEquivs R R' S S' K K'
        equivR equivS equivK hS (fun element => by
          change equivK (algebraMap F K (algebraMap R F element)) = _
          rw [hK, hF]
          rfl)
    _ = Nat.card ((F' ⊗[R'] S') →ₐ[F'] K') :=
      Nat.card_congr (AlgHom.liftEquiv R' F' S' K')

private theorem minimalPrime_comap_eq_of_ringEquiv
    {R R' : Type*} [CommRing R] [CommRing R']
    (equiv : R ≃+* R') (prime : Ideal R) (prime' : Ideal R')
    (hprime : prime ∈ minimalPrimes R) (hprime' : prime' ∈ minimalPrimes R')
    (hunique : ∃! ideal : Ideal R, ideal ∈ minimalPrimes R) :
    prime = prime'.comap equiv.toRingHom := by
  have hcomap : prime'.comap equiv.toRingHom ∈ minimalPrimes R := by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := equiv.toRingHom)
      equiv.surjective hprime'
    have hbot : (⊥ : Ideal R').comap equiv.toRingHom = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot]
      exact RingHom.ker_coe_equiv equiv
    rwa [hbot] at h
  obtain ⟨ideal, _, huniq⟩ := hunique
  exact (huniq prime hprime).trans (huniq _ hcomap).symm

private theorem algHom_card_tensorProduct_eq_of_ringEquiv_of_prime
    {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (equivR : R ≃+* R') (equivS : S ≃+* S')
    (hcompat : ∀ element, equivS (algebraMap R S element) =
      algebraMap R' S' (equivR element))
    (prime : Ideal R) (prime' : Ideal R') [prime.IsPrime] [prime'.IsPrime]
    (hprime : prime = prime'.comap equivR.toRingHom)
    (K K' : Type*) [Field K] [Field K']
    [Algebra prime.ResidueField K] [Algebra prime'.ResidueField K']
    [IsAlgClosure prime.ResidueField K] [IsAlgClosure prime'.ResidueField K'] :
    Nat.card ((prime.ResidueField ⊗[R] S) →ₐ[prime.ResidueField] K) =
      Nat.card ((prime'.ResidueField ⊗[R'] S') →ₐ[prime'.ResidueField] K') := by
  let equivF := Ideal.residueFieldRingEquiv prime prime' equivR hprime
  let equivK := IsAlgClosure.equivOfEquiv K K' equivF
  exact algHom_card_tensorProduct_eq_of_compatible_ringEquivs
    R R' prime.ResidueField prime'.ResidueField S S' K K' equivR equivF equivS equivK
    (Ideal.ResidueField.map_algebraMap prime prime' equivR hprime) hcompat
    (IsAlgClosure.equivOfEquiv_algebraMap K K' equivF)

private theorem genericPointCount_eq_of_strictHenselizations
    {R S R₁ R₂ S₁ S₂ : Type u}
    [CommRing R] [CommRing S] [CommRing R₁] [CommRing R₂]
    [CommRing S₁] [CommRing S₂] [IsLocalRing R] [IsLocalRing S]
    [IsLocalRing R₁] [IsLocalRing R₂] [IsLocalRing S₁] [IsLocalRing S₂]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    [Algebra R R₁] [Algebra R R₂] [Algebra S S₁] [Algebra S S₂]
    [Algebra R S₁] [Algebra R S₂] [Algebra R₁ S₁] [Algebra R₂ S₂]
    [IsScalarTower R S S₁] [IsScalarTower R S S₂]
    [IsScalarTower R R₁ S₁] [IsScalarTower R R₂ S₂]
    (κR₁ κR₂ κS₁ κS₂ : Type u)
    [Field κR₁] [Field κR₂] [Field κS₁] [Field κS₂]
    [Algebra (maximalIdeal R).ResidueField κR₁]
    [Algebra (maximalIdeal R).ResidueField κR₂]
    [Algebra (maximalIdeal S).ResidueField κS₁]
    [Algebra (maximalIdeal S).ResidueField κS₂]
    [IsSepClosure (maximalIdeal R).ResidueField κR₁]
    [IsSepClosure (maximalIdeal R).ResidueField κR₂]
    [IsSepClosure (maximalIdeal S).ResidueField κS₁]
    [IsSepClosure (maximalIdeal S).ResidueField κS₂]
    (hR₁ : Stacks.StrictHenselization.IsStrictHenselization R κR₁ R₁)
    (hR₂ : Stacks.StrictHenselization.IsStrictHenselization R κR₂ R₂)
    (hS₁ : Stacks.StrictHenselization.IsStrictHenselization S κS₁ S₁)
    (hS₂ : Stacks.StrictHenselization.IsStrictHenselization S κS₂ S₂)
    (hunibranch : _root_.IsGeometricallyUnibranch R)
    (prime₁ : Ideal R₁) (prime₂ : Ideal R₂) [prime₁.IsPrime] [prime₂.IsPrime]
    (hprime₁ : prime₁ ∈ minimalPrimes R₁) (hprime₂ : prime₂ ∈ minimalPrimes R₂)
    (K₁ K₂ : Type u) [Field K₁] [Field K₂]
    [Algebra prime₁.ResidueField K₁] [Algebra prime₂.ResidueField K₂]
    [IsAlgClosure prime₁.ResidueField K₁] [IsAlgClosure prime₂.ResidueField K₂] :
    Nat.card ((prime₁.ResidueField ⊗[R₁] S₁) →ₐ[prime₁.ResidueField] K₁) =
      Nat.card ((prime₂.ResidueField ⊗[R₂] S₂) →ₐ[prime₂.ResidueField] K₂) := by
  obtain ⟨equivR, equivS, hcompat⟩ := exists_compatible_algEquivs_of_strictHenselizations
    κR₁ κR₂ κS₁ κS₂ hR₁ hR₂ hS₁ hS₂
  have hprime : prime₁ = prime₂.comap equivR.toRingHom :=
    minimalPrime_comap_eq_of_ringEquiv equivR.toRingEquiv prime₁ prime₂ hprime₁ hprime₂
      (existsUnique_minimalPrime_of_strictHenselization R κR₁ R₁ hR₁ hunibranch)
  exact algHom_card_tensorProduct_eq_of_ringEquiv_of_prime equivR.toRingEquiv
    equivS.toRingEquiv hcompat prime₁ prime₂ hprime K₁ K₂

private theorem exists_genericPointCount
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    (hunibranch : _root_.IsGeometricallyUnibranch R) :
    ∃ value : ℕ,
      ∀ (κR : Type u) [Field κR] [Algebra (maximalIdeal R).ResidueField κR]
        [IsSepClosure (maximalIdeal R).ResidueField κR]
        (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
        (_hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
        (κS : Type u) [Field κS] [Algebra (maximalIdeal S).ResidueField κS]
        [IsSepClosure (maximalIdeal S).ResidueField κS]
        (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
        [Algebra Rsh Ssh] [Algebra R Ssh]
        [IsScalarTower R Rsh Ssh] [IsScalarTower R S Ssh]
        (_hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh)
        (prime : Ideal Rsh) [prime.IsPrime] (_hprime : prime ∈ minimalPrimes Rsh)
        (K : Type u) [Field K] [Algebra prime.ResidueField K]
        [IsAlgClosure prime.ResidueField K],
        value = Nat.card ((prime.ResidueField ⊗[Rsh] Ssh) →ₐ[prime.ResidueField] K) := by
  let κR₀ := SeparableClosure (maximalIdeal R).ResidueField
  let κS₀ := SeparableClosure (maximalIdeal S).ResidueField
  obtain ⟨R₀, ringR₀, localR₀, algebraR₀, ⟨hR₀⟩⟩ := exists_strictHenselization R κR₀
  obtain ⟨S₀, ringS₀, localS₀, algebraS₀, ⟨hS₀⟩⟩ := exists_strictHenselization S κS₀
  let := ringR₀
  let := localR₀
  let := algebraR₀
  let := ringS₀
  let := localS₀
  let := algebraS₀
  let : Algebra R S₀ := ((algebraMap S S₀).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S S₀ := .of_algebraMap_eq' rfl
  obtain ⟨hom, _⟩ := exists_localAlgHom_of_strictHenselization κR₀ κS₀ R₀ S₀ hR₀ hS₀
  let : Algebra R₀ S₀ := hom.toRingHom.toAlgebra
  let : IsScalarTower R R₀ S₀ :=
    .of_algebraMap_eq fun element => (hom.commutes element).symm
  obtain ⟨prime₀, hprime₀, _⟩ :=
    existsUnique_minimalPrime_of_strictHenselization R κR₀ R₀ hR₀ hunibranch
  let : prime₀.IsPrime := hprime₀.isPrime
  let K₀ := AlgebraicClosure prime₀.ResidueField
  refine ⟨Nat.card ((prime₀.ResidueField ⊗[R₀] S₀) →ₐ[prime₀.ResidueField] K₀), ?_⟩
  intro κR _ _ _ Rsh _ _ _ hRsh κS _ _ _ Ssh _ _ _ _ _ _ _ hSsh
    prime _ hprime K _ _ _
  exact genericPointCount_eq_of_strictHenselizations κR₀ κR κS₀ κS hR₀ hRsh hS₀ hSsh
    hunibranch prime₀ prime hprime₀ hprime K₀ K

private noncomputable def genericPointCount
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    (hunibranch : _root_.IsGeometricallyUnibranch R) : ℕ :=
  Classical.choose (exists_genericPointCount (S := S) hunibranch)

private theorem genericPointCount_eq
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    (hunibranch : _root_.IsGeometricallyUnibranch R)
    (κR : Type u) [Field κR] [Algebra (maximalIdeal R).ResidueField κR]
    [IsSepClosure (maximalIdeal R).ResidueField κR]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
    (κS : Type u) [Field κS] [Algebra (maximalIdeal S).ResidueField κS]
    [IsSepClosure (maximalIdeal S).ResidueField κS]
    (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
    [Algebra Rsh Ssh] [Algebra R Ssh]
    [IsScalarTower R Rsh Ssh] [IsScalarTower R S Ssh]
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization S κS Ssh)
    (prime : Ideal Rsh) [prime.IsPrime] (hprime : prime ∈ minimalPrimes Rsh)
    (K : Type u) [Field K] [Algebra prime.ResidueField K]
    [IsAlgClosure prime.ResidueField K] :
    genericPointCount (S := S) hunibranch =
      Nat.card ((prime.ResidueField ⊗[Rsh] Ssh) →ₐ[prime.ResidueField] K) :=
  Classical.choose_spec (exists_genericPointCount hunibranch)
    κR Rsh hRsh κS Ssh hSsh prime hprime K

private theorem genericPointCount_eq_of_indEtale
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R R')]
    [IsLocalHom (algebraMap S S')] [IsLocalHom (algebraMap R' S')]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFinite R S]
    [Algebra.EssFiniteType R' S'] [Algebra.QuasiFinite R' S']
    [Algebra.IsSeparable (ResidueField R) (ResidueField R')]
    [Algebra.IsSeparable (ResidueField S) (ResidueField S')]
    (hunibranch : _root_.IsGeometricallyUnibranch R)
    (hunibranch' : _root_.IsGeometricallyUnibranch R')
    (hR : StacksDraft.IndEtale R R') (hS : StacksDraft.IndEtale S S') :
    genericPointCount (S := S) hunibranch = genericPointCount (S := S') hunibranch' := by
  let κR := SeparableClosure (maximalIdeal R').ResidueField
  let κS := SeparableClosure (maximalIdeal S').ResidueField
  obtain ⟨Rsh, ringRsh, localRsh, algebraRsh, ⟨hRsh⟩⟩ := exists_strictHenselization R' κR
  obtain ⟨Ssh, ringSsh, localSsh, algebraSsh, ⟨hSsh⟩⟩ := exists_strictHenselization S' κS
  let := ringRsh
  let := localRsh
  let := algebraRsh
  let := ringSsh
  let := localSsh
  let := algebraSsh
  let : Algebra R' Ssh := ((algebraMap S' Ssh).comp (algebraMap R' S')).toAlgebra
  let : IsScalarTower R' S' Ssh := .of_algebraMap_eq' rfl
  obtain ⟨hom, _⟩ := exists_localAlgHom_of_strictHenselization κR κS Rsh Ssh hRsh hSsh
  let : Algebra Rsh Ssh := hom.toRingHom.toAlgebra
  let : IsScalarTower R' Rsh Ssh :=
    .of_algebraMap_eq fun element => (hom.commutes element).symm
  let : Algebra R Rsh := ((algebraMap R' Rsh).comp (algebraMap R R')).toAlgebra
  let : IsScalarTower R R' Rsh := .of_algebraMap_eq' rfl
  let : Algebra S Ssh := ((algebraMap S' Ssh).comp (algebraMap S S')).toAlgebra
  let : IsScalarTower S S' Ssh := .of_algebraMap_eq' rfl
  let : Algebra R Ssh := ((algebraMap S' Ssh).comp (algebraMap R S')).toAlgebra
  let : IsScalarTower R S' Ssh := .of_algebraMap_eq' rfl
  let : IsScalarTower R S Ssh := IsScalarTower.of_algebraMap_eq fun element => by
    change algebraMap S' Ssh (algebraMap R S' element) =
      algebraMap S' Ssh (algebraMap S S' (algebraMap R S element))
    rw [IsScalarTower.algebraMap_apply R S S']
  let : IsScalarTower R R' Ssh := IsScalarTower.of_algebraMap_eq fun element => by
    change algebraMap S' Ssh (algebraMap R S' element) =
      algebraMap S' Ssh (algebraMap R' S' (algebraMap R R' element))
    rw [IsScalarTower.algebraMap_apply R R' S']
  let : IsScalarTower R Rsh Ssh :=
    IsScalarTower.to₁₃₄ R R' Rsh Ssh
  obtain ⟨algebraκR, sepκR, ⟨hRshR⟩⟩ :=
    exists_isStrictHenselization_of_indEtale_comp κR hR hRsh
  obtain ⟨algebraκS, sepκS, ⟨hSshS⟩⟩ :=
    exists_isStrictHenselization_of_indEtale_comp κS hS hSsh
  let := algebraκR
  let := sepκR
  let := algebraκS
  let := sepκS
  obtain ⟨prime, hprime, _⟩ :=
    existsUnique_minimalPrime_of_strictHenselization R' κR Rsh hRsh hunibranch'
  let : prime.IsPrime := Ideal.IsMinimalPrime.isPrime hprime
  let K := AlgebraicClosure prime.ResidueField
  exact (genericPointCount_eq hunibranch (maximalIdeal Rsh).ResidueField Rsh hRshR
    (maximalIdeal Ssh).ResidueField Ssh hSshS prime hprime K).trans
    (genericPointCount_eq hunibranch' κR Rsh hRsh κS Ssh hSsh prime hprime K).symm

private noncomputable def genericSeparableDegree
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (hY : IsGeometricallyUnibranch Y) (x : X) : ℕ := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  let : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.quasiFiniteAt x).toAlgebra
  exact Classical.choose (exists_genericPointCount (S := X.presheaf.stalk x)
    ((isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).mpr (hY (f x))))

private theorem genericSeparableDegree_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (hY : IsGeometricallyUnibranch Y)
    (x : X)
    (κY : Type u) [Field κY]
    [Algebra (maximalIdeal (Y.presheaf.stalk (f x))).ResidueField κY]
    [IsSepClosure (maximalIdeal (Y.presheaf.stalk (f x))).ResidueField κY]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh]
    [Algebra (Y.presheaf.stalk (f x)) Rsh]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization
      (Y.presheaf.stalk (f x)) κY Rsh)
    (κX : Type u) [Field κX]
    [Algebra (maximalIdeal (X.presheaf.stalk x)).ResidueField κX]
    [IsSepClosure (maximalIdeal (X.presheaf.stalk x)).ResidueField κX]
    (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh]
    [Algebra (X.presheaf.stalk x) Ssh] [Algebra Rsh Ssh]
    [Algebra (Y.presheaf.stalk (f x)) Ssh]
    [IsScalarTower (Y.presheaf.stalk (f x)) Rsh Ssh]
    (hSsh : Stacks.StrictHenselization.IsStrictHenselization
      (X.presheaf.stalk x) κX Ssh)
    (hcomp : (algebraMap (Y.presheaf.stalk (f x)) Ssh) =
      (algebraMap (X.presheaf.stalk x) Ssh).comp (f.stalkMap x).hom)
    (p : Ideal Rsh) [p.IsPrime] (hp : p ∈ minimalPrimes Rsh)
    (Kbar : Type u) [Field Kbar]
    [Algebra p.ResidueField Kbar] [IsAlgClosure p.ResidueField Kbar] :
    genericSeparableDegree f hY x = Nat.card (AlgHom p.ResidueField
      (TensorProduct Rsh p.ResidueField Ssh) Kbar) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  let : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.quasiFiniteAt x).toAlgebra
  let : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Ssh :=
    .of_algebraMap_eq' hcomp
  exact Classical.choose_spec (exists_genericPointCount (S := X.presheaf.stalk x)
    ((isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).mpr (hY (f x))))
    κY Rsh hRsh κX Ssh hSsh p hp Kbar

private theorem algHom_factors_through_eval
    (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (φ : (∀ i, A i) →ₐ[R] K) :
    ∃ i, ∃ ψ : A i →ₐ[R] K, φ = ψ.comp (Pi.evalAlgHom R A i) := by
  let p : PrimeSpectrum (∀ i, A i) :=
    ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime φ.toRingHom⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hker : RingHom.ker (Pi.evalRingHom A i) ≤ RingHom.ker φ.toRingHom := by
    intro a ha
    change a ∈ p.asIdeal
    rw [← hq]
    change a i ∈ q.asIdeal
    have hzero : a i = 0 := ha
    rw [hzero]
    exact q.asIdeal.zero_mem
  have hsurj : Function.Surjective (Pi.evalRingHom A i) :=
    RingHomSurjective.is_surjective
  let ψring : A i →+* K :=
    (Pi.evalRingHom A i).liftOfSurjective hsurj ⟨φ.toRingHom, hker⟩
  have hcomp : ψring.comp (Pi.evalRingHom A i) = φ.toRingHom :=
    RingHom.liftOfSurjective_comp _ _ _
  let ψ : A i →ₐ[R] K :=
    { ψring with
      commutes' := by
        intro r
        have hr := DFunLike.congr_fun hcomp (algebraMap R (∀ i, A i) r)
        simpa using hr.trans (φ.commutes r) }
  exact ⟨i, ψ, AlgHom.ext fun a => (DFunLike.congr_fun hcomp a).symm⟩

private theorem algHom_comp_eval_injective
    (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    {ι : Type*} (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    Function.Injective (fun pair : Σ i, A i →ₐ[R] K =>
      pair.2.comp (Pi.evalAlgHom R A pair.1)) := by
  classical
  rintro ⟨i, φ⟩ ⟨j, ψ⟩ heq
  have hij : i = j := by
    by_contra hne
    have h := AlgHom.congr_fun heq (Pi.single i 1)
    simp [Ne.symm hne] at h
  subst j
  have hφ : φ = ψ := by
    ext a
    have h := AlgHom.congr_fun heq (Pi.single i a)
    simpa using h
  subst ψ
  rfl

private theorem algHom_card_pi
    (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    {ι : Type*} [Fintype ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Finite (A i →ₐ[R] K)] :
    Nat.card ((∀ i, A i) →ₐ[R] K) = ∑ i, Nat.card (A i →ₐ[R] K) := by
  classical
  have hsurj : Function.Surjective (fun pair : Σ i, A i →ₐ[R] K =>
      pair.2.comp (Pi.evalAlgHom R A pair.1)) := by
    intro φ
    obtain ⟨i, ψ, hψ⟩ := algHom_factors_through_eval R K A φ
    exact ⟨⟨i, ψ⟩, hψ.symm⟩
  let e := Equiv.ofBijective _ ⟨algHom_comp_eval_injective R K A, hsurj⟩
  rw [Nat.card_congr e.symm, Nat.card_sigma]

end AlgebraicGeometry
