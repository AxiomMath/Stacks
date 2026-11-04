module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.FiniteStageDescent

/-!
# Tag 09II from Epp's theorem: the final assembly

Part 7 of the development of Stacks Tag 09II from Epp's theorem (Tag 09F9) in
`StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution`. It contains
the two final assembly steps: a solution from formal smoothness over an algebraic extension
(`exists_finite_extension_isSolution_of_formallySmooth_algebraicExtension`), and Tag 09II from
Epp's theorem (`exists_finite_extension_isSolution_of_eppTheorem`).
-/

@[expose] public section

universe uA uB uK uL v uK₁ uL₁ uA₁ uB₁

namespace Stacks.EliminateRamification

open IsLocalRing
open scoped TensorProduct

/-- A field extension of the fraction field `K` of `A` is faithful over `A`. -/
private theorem faithfulSMul_of_isFractionRing_tower
    (A K E : Type*) [CommRing A] [IsDomain A] [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [Algebra A E] [IsScalarTower A K E] :
    FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr (by
  rw [IsScalarTower.algebraMap_eq A K E]
  exact (algebraMap K E).injective.comp (IsFractionRing.injective A K))

/-- An algebraic field extension of `K` is the fraction field of the integral closure of `A`. -/
private theorem isFractionRing_integralClosure_of_tower
    (A K E : Type*) [CommRing A] [IsDomain A] [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [Algebra.IsAlgebraic K E]
    [Algebra A E] [IsScalarTower A K E] : IsFractionRing (integralClosure A E) E := by
  have := faithfulSMul_of_isFractionRing_tower A K E
  have : Algebra.IsAlgebraic A E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := E)).mpr inferInstance
  exact integralClosure.isFractionRing_of_algebraic
    (fun a ha => (FaithfulSMul.algebraMap_injective A E) (by simpa using ha))

/-- The structure map from `A` to the reduced tensor product factors through `E`. -/
private theorem algebraMap_reduction_eq_includeRight
    (A K L E : Type*) [CommRing A] [Field K] [Field L] [Field E]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E] (a : A) :
    algebraMap A (ReducedTensorTower.Reduction (L ⊗[K] E)) a = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) (algebraMap A E a)) := by
  rw [IsScalarTower.algebraMap_apply A K (ReducedTensorTower.Reduction (L ⊗[K] E)),
    IsScalarTower.algebraMap_apply A K E]
  simp only [AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply K (L ⊗[K] E) _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 8000000 in
-- The proof elaborates many compatible algebra and scalar-tower instances on tensor products.
set_option synthInstance.maxHeartbeats 200000 in
private theorem exists_finite_extension_isSolution_of_formallySmooth_algebraicExtension
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (E : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field E]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B] [Algebra K E] [Algebra A E]
    [IsScalarTower A K E] [Algebra.IsAlgebraic K E]
    [IsDedekindDomain (integralClosure A E)]
    [IsNoetherianRing (integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] E)))]
    (fE : integralClosure A E →+* integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] E)))
    (hcomm : ∀ x, (fE x).val = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) x.val))
    (hgeom : letI : Algebra E (L ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyReduced E (ReducedTensorTower.Reduction (L ⊗[K] E)))
    (hsmooth : ∀ (m : Ideal (integralClosure B (ReducedTensorTower.Reduction (L ⊗[K] E))))
      [m.IsMaximal], RingHom.FormallySmoothNAdic.{max uL uK}
        (Localization.localRingHom (m.comap fE) m fE rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime m))) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} := by
  classical
  let R := integralClosure A E
  let T := ReducedTensorTower.Reduction (L ⊗[K] E)
  let C := integralClosure B T
  let algCT : Algebra C T := inferInstance
  let : SMul C T := algCT.toSMul
  let : Algebra E (L ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
  let algET : Algebra E T := inferInstance
  let : SMul E T := algET.toSMul
  let algRE : Algebra R E := inferInstance
  let : SMul R E := algRE.toSMul
  have : Algebra.IsGeometricallyReduced E T := hgeom
  let algRT : Algebra R T := ((algebraMap E T).comp (algebraMap R E)).toAlgebra
  let : SMul R T := algRT.toSMul
  have : IsScalarTower R E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let algRC : Algebra R C := fE.toAlgebra
  let : SMul R C := algRC.toSMul
  have : IsScalarTower R C T := IsScalarTower.of_algebraMap_eq fun x => (hcomm x).symm
  have : IsScalarTower A R C := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.val_injective
    show algebraMap A T a = (fE (algebraMap A R a)).val
    rw [hcomm]
    exact algebraMap_reduction_eq_includeRight A K L E a
  have : FaithfulSMul A E := faithfulSMul_of_isFractionRing_tower A K E
  have : FaithfulSMul A R :=
    (faithfulSMul_iff_algebraMap_injective A R).mpr (by
      intro x y h
      apply FaithfulSMul.algebraMap_injective A E
      exact congrArg Subtype.val h)
  have : IsFractionRing R E := isFractionRing_integralClosure_of_tower A K E
  have : Algebra.EssFiniteType B L := .of_isLocalization L (nonZeroDivisors B)
  have : Algebra.EssFiniteType A L := .comp A B L
  have : Algebra.EssFiniteType K L := .of_comp A K L
  have : Algebra.EssFiniteType E (L ⊗[K] E) :=
    Algebra.EssFiniteType.of_surjective (Algebra.TensorProduct.commRight K E L).toAlgHom
      (Algebra.TensorProduct.commRight K E L).surjective
  have : Algebra.EssFiniteType E T := Algebra.EssFiniteType.of_surjective
    (Ideal.Quotient.mkₐ E (nilradical (L ⊗[K] E))) Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType R E := .of_isLocalization E (nonZeroDivisors R)
  have : Algebra.EssFiniteType R T := .comp R E T
  let S := R ⊗[A] B
  let fS := AlgHom.liftEquiv A R B C (IsScalarTower.toAlgHom A B C)
  let : Algebra S C := fS.toAlgebra
  have : Module.Finite S C :=
    finite_integralClosure_tensorProduct_of_isGeometricallyReduced A B R E T C
  obtain ⟨FC, hFC, hgen⟩ :=
    exists_adjoin_range_eq_top_integralClosure_reducedTensor_finite_stage B K L E S
  have : IsNoetherianRing (L ⊗[K] E) := Algebra.EssFiniteType.isNoetherianRing E _
  obtain ⟨FN, hFN, hnil⟩ := exists_finite_intermediateField_nilradical_map_eq K L E
    (Ideal.fg_of_isNoetherianRing _)
  have : Finite (PrimeSpectrum A) :=
    IsDiscreteValuationRing.finite_primeSpectrum_of_dimensionLEOne A
  have : Finite (PrimeSpectrum B) :=
    IsDiscreteValuationRing.finite_primeSpectrum_of_dimensionLEOne B
  have : Finite (PrimeSpectrum R) := finite_primeSpectrum_of_isIntegral_of_isNoetherianRing A R
  have : Finite (PrimeSpectrum C) := finite_primeSpectrum_of_isIntegral_of_isNoetherianRing B C
  obtain ⟨FA, hFA, hFAspec⟩ :=
    exists_primeSpectrum_bijective_integralClosureMap_finite_stage A K E
  obtain ⟨FB, hFB, hFBspec⟩ :=
    exists_primeSpectrum_bijective_integralClosure_reducedTensor_finite_stage B K L E
  have : Module.Finite K FA := hFA
  have : Module.Finite K FB := hFB
  have : Module.Finite K FC := hFC
  have : Module.Finite K FN := hFN
  obtain ⟨F, hF, hAF, hBF, hCF, hNF⟩ : ∃ F : IntermediateField K E,
      Module.Finite K F ∧ FA ≤ F ∧ FB ≤ F ∧ FC ≤ F ∧ FN ≤ F := by
    refine ⟨(FA ⊔ FB) ⊔ (FC ⊔ FN), inferInstance, ?_, ?_, ?_, ?_⟩
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  have : Module.Finite K F := hF
  obtain ⟨hAspec, hAideal⟩ := hFAspec F inferInstance hAF
  obtain ⟨hBspec, hBideal⟩ := hFBspec F inferInstance hBF
  have hgenF := hgen F inferInstance hCF
  let RF := integralClosure A F
  let TF := ReducedTensorTower.Reduction (L ⊗[K] F)
  let CF := integralClosure B TF
  let algCFTF : Algebra CF TF := inferInstance
  let : SMul CF TF := algCFTF.toSMul
  have : IsDedekindDomain RF :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A K F RF).1
  obtain ⟨hnoethF, fF, hcommF, hsurjF, hresF⟩ :=
    IsDiscreteValuationRing.integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective A
      B K L F
  have := hnoethF
  let a := (F.val.restrictScalars A).mapIntegralClosure
  let b := integralClosureReducedTensorMap B K L F
  have hsquare : fE.comp a.toRingHom = b.toRingHom.comp fF := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    show (fE (a x)).val = (b (fF x)).val
    rw [hcomm]
    show _ = (ReducedTensorTower.reductionMap
      (Algebra.TensorProduct.map (.id L L) F.val)) (fF x).val
    have hx := hcommF x
    change (fF x).val = _ at hx
    rw [hx]
    rfl
  let algRFR : Algebra RF R := a.toAlgebra
  let : SMul RF R := algRFR.toSMul
  let algRFCF : Algebra RF CF := fF.toAlgebra
  let : SMul RF CF := algRFCF.toSMul
  let algRFC : Algebra RF C := (fE.comp a.toRingHom).toAlgebra
  let : SMul RF C := algRFC.toSMul
  have : IsScalarTower RF R C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let bRF : CF →ₐ[RF] C := { __ := b.toRingHom, commutes' := fun x =>
    (DFunLike.congr_fun hsquare x).symm }
  let P := R ⊗[RF] CF
  let algRP : Algebra R P := Algebra.TensorProduct.leftAlgebra
  let algRFP : Algebra RF P := Algebra.TensorProduct.instAlgebra
  let ψ : P →ₐ[R] C := AlgHom.liftEquiv RF R CF C bRF
  let : Algebra F (L ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  have hinjψ : Function.Injective ψ := by
    clear! S
    have hnilF := nilradical_map_eq_of_le_intermediateField K L E FN F hNF hnil
    obtain ⟨e, he⟩ := exists_reducedTensorProductScalarExtensionEquiv K F E L hnilF
    let algRFE : Algebra RF E := ((algebraMap F E).comp (algebraMap RF F)).toAlgebra
    let : SMul RF E := algRFE.toSMul
    have : IsScalarTower RF F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower RF R E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let algFT : Algebra F T := ((algebraMap E T).comp (algebraMap F E)).toAlgebra
    let : SMul F T := algFT.toSMul
    have : IsScalarTower F E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let algRFTF : Algebra RF TF := ((algebraMap F TF).comp (algebraMap RF F)).toAlgebra
    let : SMul RF TF := algRFTF.toSMul
    have : IsScalarTower RF F TF := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower RF CF TF := IsScalarTower.of_algebraMap_eq fun x => (hcommF x).symm
    have : FaithfulSMul A F := faithfulSMul_of_isFractionRing_tower A K F
    have : IsFractionRing RF F := isFractionRing_integralClosure_of_tower A K F
    have : Module.IsTorsionFree RF TF := Module.IsTorsionFree.trans_faithfulSMul RF F TF
    let j := IsScalarTower.toAlgHom RF CF TF
    have : Module.IsTorsionFree RF CF := Function.Injective.moduleIsTorsionFree j
      Subtype.val_injective j.toLinearMap.map_smul
    have : Module.Flat RF CF := inferInstance
    have : Module.IsTorsionFree RF E := Module.IsTorsionFree.trans_faithfulSMul RF F E
    have : Module.Flat RF E := inferInstance
    let jE := algebraMap C T
    let : Algebra R P := algRP
    let : Algebra RF P := algRFP
    have hinj : Function.Injective (jE.comp ψ.toRingHom) :=
      injective_tensorProduct_lift_of_injective_generic RF F R E CF TF T
        (nonZeroDivisors RF) j Subtype.val_injective Subtype.val_injective
        (e.toAlgHom.restrictScalars F) e.injective (jE.comp ψ.toRingHom) (by
          intro r c
          show (fE r).val * (b c).val = e ((r : E) ⊗ₜ[F] c.val)
          rw [hcomm]
          have ht : (r : E) ⊗ₜ[F] c.val = (r : E) • (1 ⊗ₜ[F] c.val) := by
            simp [TensorProduct.smul_tmul']
          have hes : e ((r : E) • (1 ⊗ₜ[F] c.val)) = (r : E) • e (1 ⊗ₜ[F] c.val) :=
            e.toLinearEquiv.map_smul _ _
          rw [ht, hes, he]
          rfl)
    exact fun x y h => hinj (congrArg jE h)
  have hsurjψ : Function.Surjective ψ := by
    apply surjective_of_adjoin_eq_top S C (R ⊗[RF] CF) ψ.toRingHom (Set.range b) hgenF
    · intro s
      induction s using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero ψ⟩
      | add x y hx hy => simpa only [map_add] using ψ.toRingHom.range.add_mem hx hy
      | tmul r c =>
        refine ⟨r ⊗ₜ[RF] algebraMap B CF c, ?_⟩
        show r • b (algebraMap B CF c) = r • algebraMap B C c
        rw [b.commutes]
    · rintro _ ⟨c, rfl⟩
      exact ⟨1 ⊗ₜ[RF] c, by change (1 : R) • b c = b c; rw [one_smul]⟩
  have hbijψ : Function.Bijective ψ := ⟨hinjψ, hsurjψ⟩
  have : FaithfulSMul A F := faithfulSMul_of_isFractionRing_tower A K F
  have : IsScalarTower A RF CF := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.val_injective
    show algebraMap A TF x = (fF (algebraMap A RF x)).val
    have hx := hcommF (algebraMap A RF x)
    change (fF (algebraMap A RF x)).val = _ at hx
    rw [hx]
    exact algebraMap_reduction_eq_includeRight A K L F x
  let D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
      max uL uK, uK, max uL uK} A B K L F :=
    { L₁ := TF
      A₁ := RF
      B₁ := CF
      eL₁ := AlgEquiv.refl
      eL₁_left := fun _ => rfl
      eL₁_right := fun _ => rfl
      ringSquare := hcommF }
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, ?_⟩
  clear! S
  intro q hq
  have : q.IsMaximal := hq
  obtain ⟨m, hm⟩ := hBspec.surjective (⟨q, inferInstance⟩ : PrimeSpectrum CF)
  have hmq : m.asIdeal.comap b.toRingHom = q := congrArg PrimeSpectrum.asIdeal hm
  let algCFC : Algebra CF C := b.toAlgebra
  have : IsScalarTower B CF C := IsScalarTower.of_algebraMap_eq fun x => (b.commutes x).symm
  have hiB : Algebra.IsIntegral CF C := Algebra.IsIntegral.tower_top (R := B)
  have : m.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (R := CF) m.asIdeal (hmq.symm ▸ hq)
  have hbInj : Function.Injective b := by
    intro x y h
    apply Subtype.val_injective
    apply reducedTensorProduct_map_injective K L F.val
    exact congrArg Subtype.val h
  have : IsReduced TF := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  have : IsReduced T := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  have : IsArtinianRing TF := IsDiscreteValuationRing.reducedTensorProduct_isArtinian K L F
  have : IsArtinianRing T := IsDiscreteValuationRing.reducedTensorProduct_isArtinian K L E
  have : FaithfulSMul A RF := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    intro x y h
    apply FaithfulSMul.algebraMap_injective A F
    exact congrArg Subtype.val h)
  obtain ⟨hpF, hqdom, hqdvr, hpdvr, hfInj⟩ :=
    integralClosure_localRingHom_isDiscreteValuationRing_and_injective A B RF L TF q
  obtain ⟨hpE, hmdom, hmdvr, hpEdvr, hfEInj⟩ :=
    integralClosure_localRingHom_isDiscreteValuationRing_and_injective A B R L T m.asIdeal
  have hpSquare : q.comap fF = (m.asIdeal.comap fE).comap a.toRingHom := by
    calc
      q.comap fF = (m.asIdeal.comap b.toRingHom).comap fF :=
        congrArg (fun J : Ideal CF => J.comap fF) hmq.symm
      _ = m.asIdeal.comap (b.toRingHom.comp fF) := Ideal.comap_comap _ _
      _ = m.asIdeal.comap (fE.comp a.toRingHom) :=
        congrArg (fun g : RF →+* C => m.asIdeal.comap g) hsquare.symm
      _ = (m.asIdeal.comap fE).comap a.toRingHom := (Ideal.comap_comap _ _).symm
  have haMax := hAideal (⟨m.asIdeal.comap fE, inferInstance⟩ : PrimeSpectrum R)
  have hbMax := hBideal m
  change (m.asIdeal.comap b.toRingHom).map b.toRingHom = m.asIdeal at hbMax
  rw [hmq] at hbMax
  have haMax' : (q.comap fF).map a.toRingHom = m.asIdeal.comap fE := by
    rwa [hpSquare]
  have hbLocal := localRingHom_injective_of_primeSpectrum_comap_injective b.toRingHom
    hbInj hiB.isIntegral hBspec.injective m.asIdeal
  have hbLocal' := localRingHom_injective_of_eq_comap b.toRingHom q m.asIdeal hmq.symm hbLocal
  have hs : RingHom.FormallySmoothNAdic.{max uK uL}
      (Localization.localRingHom (q.comap fF) q fF rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    formallySmoothNAdic_localRingHom_of_bijective_tensorProduct RF CF R C bRF hbijψ
      (q.comap fF) q (m.asIdeal.comap fE) m.asIdeal rfl rfl hpSquare hmq.symm
      hfInj hfEInj hbLocal' haMax' hbMax (hsmooth m.asIdeal)
  exact formallySmoothNAdic_of_formallySmoothNAdic_sameUniverse _ hfInj hs

set_option synthInstance.maxHeartbeats 200000 in
-- The assembly elaborates many algebra instances over two universe profiles of the construction.
set_option maxHeartbeats 16000000 in
/-- The complete wild-case assembly of Tag 09II from Epp theorem instances at the two
universe profiles used by the construction. -/
theorem exists_finite_extension_isSolution_of_eppTheorem
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B]
    (hEpp : EppTheorem.{uA, uB, uK, uL})
    (hEppLocal : EppTheorem.{uK, max uL uK, uK, max uL uK}) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} := by
  classical
  by_cases hchar : CharZero (IsLocalRing.ResidueField A)
  · let := hchar
    exact exists_finite_extension_isSolution_of_charZero A B K L hEpp
  · by_cases hp : PerfectField (ResidueField A)
    · have := hp
      have : Algebra.EssFiniteType A (ResidueField B) := Algebra.EssFiniteType.comp A B _
      have : Algebra.EssFiniteType (ResidueField A) (ResidueField B) :=
        Algebra.EssFiniteType.of_comp A _ _
      exact exists_finite_extension_isSolution_of_perfectField A B K L hEpp
    obtain ⟨E, hE, hKE, hAE, htower, halg, hDVR, hperfect, hmax⟩ :=
      exists_algebraic_extension_isDiscreteValuationRing_integralClosure A K
    let : Field E := hE
    let : Algebra K E := hKE
    let : Algebra A E := hAE
    have := htower
    have := halg
    have := hDVR
    have := hperfect
    obtain ⟨hnoeth, f, hcomm, hsurj, hresidue⟩ :=
      IsDiscreteValuationRing.integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective
        A B K L E
    have := hnoeth
    have : Finite (PrimeSpectrum B) :=
      IsDiscreteValuationRing.finite_primeSpectrum_of_dimensionLEOne B
    have hspec := finite_primeSpectrum_of_isIntegral_of_isNoetherianRing B
      (integralClosure B ((TensorProduct K L E) ⧸ nilradical (TensorProduct K L E)))
    have : Algebra.EssFiniteType B L := .of_isLocalization L (nonZeroDivisors B)
    have : Algebra.EssFiniteType A L := .comp A B L
    have : Algebra.EssFiniteType K L := .of_comp A K L
    let T := (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)
    let C := integralClosure B T
    have : IsArtinianRing T := IsDiscreteValuationRing.reducedTensorProduct_isArtinian K L E
    have : IsReduced T := (Ideal.isRadical_iff_quotient_reduced _).mp
      (Ideal.radical_isRadical ⊥)
    have hlocal (q : Ideal C) [q.IsMaximal] :
        ∃ (_ : IsDomain (Localization.AtPrime q)),
          IsDiscreteValuationRing (Localization.AtPrime q) :=
      isDiscreteValuationRing_integralClosure_localization B L T q
    have : FaithfulSMul A E := faithfulSMul_of_isFractionRing_tower A K E
    let A' := integralClosure A E
    let algA'C : Algebra A' C := f.toAlgebra
    let : SMul A' C := algA'C.toSMul
    have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.val_injective
      show algebraMap A T a = C.val (f (algebraMap A A' a))
      rw [hcomm]
      exact algebraMap_reduction_eq_includeRight A K L E a
    have hpull (q : Ideal C) [q.IsMaximal] :
        q.comap (algebraMap A' C) = maximalIdeal A' :=
      comap_eq_maximalIdeal_of_integral_tower A B A' C q
    let P := MaximalSpectrum C
    have hdomain (q : P) : IsDomain (Localization.AtPrime q.asIdeal) :=
      (hlocal q.asIdeal).choose
    have hdvr (q : P) : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
      (hlocal q.asIdeal).choose_spec
    let algA'Loc (q : P) : Algebra A' (Localization.AtPrime q.asIdeal) :=
      OreLocalization.instAlgebra (R₀ := A') (R := C) (S := q.asIdeal.primeCompl)
    let algLocF (q : P) : Algebra (Localization.AtPrime q.asIdeal)
        (FractionRing (Localization.AtPrime q.asIdeal)) :=
      OreLocalization.instAlgebra (R₀ := Localization.AtPrime q.asIdeal)
        (R := Localization.AtPrime q.asIdeal) (S := nonZeroDivisors (Localization.AtPrime
          q.asIdeal))
    let algA'F (q : P) : Algebra A' (FractionRing (Localization.AtPrime q.asIdeal)) :=
      OreLocalization.instAlgebra (R₀ := A') (R := Localization.AtPrime q.asIdeal)
        (S := nonZeroDivisors (Localization.AtPrime q.asIdeal))
    let smulA'F (q : P) : SMul A' (FractionRing (Localization.AtPrime q.asIdeal)) :=
      (algA'F q).toSMul
    have hext (q : P) : IsDiscreteValuationRing.IsExtension A' (Localization.AtPrime q.asIdeal) :=
      by
      have : FaithfulSMul B (Localization.AtPrime q.asIdeal) :=
        faithfulSMul_integralClosure_localization B L T q.asIdeal
      have : FaithfulSMul A (Localization.AtPrime q.asIdeal) :=
        (faithfulSMul_iff_algebraMap_injective A _).mpr (by
          rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q.asIdeal)]
          exact (FaithfulSMul.algebraMap_injective B _).comp
            (FaithfulSMul.algebraMap_injective A B))
      have : FaithfulSMul A' (Localization.AtPrime q.asIdeal) :=
        faithfulSMul_of_isIntegral_tower A A' (Localization.AtPrime q.asIdeal)
      have : IsLocalHom (algebraMap A' (Localization.AtPrime q.asIdeal)) :=
        isLocalHom_localization_of_comap_eq_maximalIdeal A' C q.asIdeal (hpull q.asIdeal)
      exact { toFaithfulSMul := inferInstance, toIsLocalHom := inferInstance }
    have hres (q : P) :
        Algebra.EssFiniteType (ResidueField A') q.asIdeal.ResidueField := by
      apply essFiniteType_residueField_of_localization A' C q.asIdeal (hpull q.asIdeal)
      have h := hresidue ⟨q.asIdeal, inferInstance⟩
      exact essFiniteType_residueField_map_of_eq f _ _ q.asIdeal rfl
        (hpull q.asIdeal).symm h
    have : Algebra.IsIntegral L (L ⊗[K] E) := Algebra.IsIntegral.tensorProduct K L E
    have : Algebra.IsIntegral L T :=
      Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ L (nilradical (L ⊗[K] E)))
        Ideal.Quotient.mk_surjective
    have hgeneric (q : P) :
        ∃ (_ : Algebra T (FractionRing (Localization.AtPrime q.asIdeal))),
          (∀ x : C, algebraMap T (FractionRing (Localization.AtPrime q.asIdeal)) x.val =
            algebraMap (Localization.AtPrime q.asIdeal) (FractionRing (Localization.AtPrime
              q.asIdeal))
              (algebraMap C (Localization.AtPrime q.asIdeal) x)) ∧
          IsLocalization (Algebra.algebraMapSubmonoid T q.asIdeal.primeCompl)
            (FractionRing (Localization.AtPrime q.asIdeal)) := by
      have : FaithfulSMul B (Localization.AtPrime q.asIdeal) :=
        faithfulSMul_integralClosure_localization B L T q.asIdeal
      have : IsLocalHom (algebraMap B (Localization.AtPrime q.asIdeal)) :=
        isLocalHom_localization_of_comap_eq_maximalIdeal B C q.asIdeal
          (IsLocalRing.eq_maximalIdeal
            (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal))
      exact exists_isLocalization_fractionRing_atPrime_integralClosure B L T q.asIdeal
    have : IsFractionRing A' E := isFractionRing_integralClosure_of_tower A K E
    have : Finite P := Finite.of_injective
      (fun q : P => (⟨q.asIdeal, q.isMaximal.isPrime⟩ : PrimeSpectrum C))
      (fun _ _ h => MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal h))
    obtain ⟨hEM, hA'EM, E₀, hE₀, hEE₀, hA'E₀, htower₀, hfinite₀, hcommon₀⟩ :=
      exists_finite_extension_localSolutions_of_perfectField A' E C hEppLocal
    have hgenericE (q : P) :
        let : Algebra E (L ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
        let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
        ∃ g : T →ₐ[E] FractionRing (Localization.AtPrime q.asIdeal),
          (∀ x : C, g x.val =
            algebraMap (Localization.AtPrime q.asIdeal) (FractionRing (Localization.AtPrime
              q.asIdeal))
              (algebraMap C (Localization.AtPrime q.asIdeal) x)) ∧
          let := g.toAlgebra
          IsLocalization (Algebra.algebraMapSubmonoid T q.asIdeal.primeCompl)
            (FractionRing (Localization.AtPrime q.asIdeal)) := by
      let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
      let : Algebra E (L ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
      let : Algebra E T := inferInstanceAs
        (Algebra E ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)))
      let : Algebra A' T := ((algebraMap E T).comp (algebraMap A' E)).toAlgebra
      let : SMul A' T := (inferInstance : Algebra A' T).toSMul
      let : SMul A' E := A'.toAlgebra.toSMul
      have : IsScalarTower A' E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsScalarTower A' C T :=
        IsScalarTower.of_algebraMap_eq fun a => (hcomm a).symm
      let : Algebra A' (FractionRing (Localization.AtPrime q.asIdeal)) := algA'F q
      let : SMul A' (FractionRing (Localization.AtPrime q.asIdeal)) := smulA'F q
      have : IsScalarTower A' E (FractionRing (Localization.AtPrime q.asIdeal)) := hA'EM q
      obtain ⟨hTF, hTFcomm, hTFloc⟩ := hgeneric q
      let := hTF
      let g₀ : T →ₐ[A'] FractionRing (Localization.AtPrime q.asIdeal) :=
        { toRingHom := algebraMap T (FractionRing (Localization.AtPrime q.asIdeal))
          commutes' := fun a => by
            show algebraMap T (FractionRing (Localization.AtPrime q.asIdeal))
              (algebraMap A' T a) = _
            rw [IsScalarTower.algebraMap_apply A' C T]
            show algebraMap T (FractionRing (Localization.AtPrime q.asIdeal))
              (algebraMap A' C a).val = _
            rw [hTFcomm]
            congr 1 }
      let g := g₀.extendScalarsOfIsLocalization E (nonZeroDivisors A')
      refine ⟨g, hTFcomm, ?_⟩
      convert! hTFloc using 1
      exact toAlgebra_algebraMap
    let : Field E₀ := hE₀
    let : Algebra E E₀ := hEE₀
    let : Algebra A' E₀ := hA'E₀
    let : SMul A' E₀ := hA'E₀.toSMul
    let : SMul A' E := A'.toAlgebra.toSMul
    have : IsScalarTower A' E E₀ := htower₀
    have : Module.Finite E E₀ := hfinite₀
    let : Algebra K E₀ := ((algebraMap E E₀).comp (algebraMap K E)).toAlgebra
    have : IsScalarTower K E E₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨E₁, hE₁, hE₀E₁, hKE₁, hKE₀E₁, hfinite₁, hgeom₁⟩ :=
      exists_finite_extension_isGeometricallyReduced_reducedTensorProduct K E₀ L
    let : Field E₁ := hE₁
    let : Algebra E₀ E₁ := hE₀E₁
    let : Algebra K E₁ := hKE₁
    have : IsScalarTower K E₀ E₁ := hKE₀E₁
    have : Module.Finite E₀ E₁ := hfinite₁
    let : Algebra E E₁ := ((algebraMap E₀ E₁).comp (algebraMap E E₀)).toAlgebra
    have : IsScalarTower E E₀ E₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower K E E₁ := IsScalarTower.to₁₂₄ K E E₀ E₁
    have : Module.Finite E E₁ := Module.Finite.trans E₀ E₁
    let : Algebra A' E₁ := ((algebraMap E E₁).comp (algebraMap A' E)).toAlgebra
    let : SMul A' E₁ := (inferInstance : Algebra A' E₁).toSMul
    have : IsScalarTower A' E E₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A' E₀ E₁ := IsScalarTower.to₁₃₄ A' E E₀ E₁
    have hcommon (q : P) :
        let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
        let : IsScalarTower A' E (FractionRing (Localization.AtPrime q.asIdeal)) := hA'EM q
        ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL uK, uK,
            max uL uK, uK, max uL uK}
          A' (Localization.AtPrime q.asIdeal) E (FractionRing (Localization.AtPrime q.asIdeal)) E₁,
          D.IsSolution.{uK, max uL uK, uK, max uL uK, uK,
            max uL uK, uK, max uL uK, max uL uK} := by
      let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
      have : IsScalarTower A' E (FractionRing (Localization.AtPrime q.asIdeal)) := hA'EM q
      exact IsDiscreteValuationRing.exists_isSolution_of_tower A' (Localization.AtPrime q.asIdeal)
        E (FractionRing (Localization.AtPrime q.asIdeal)) E₀ E₁ (hcommon₀ q)
    let : Algebra A E₁ := ((algebraMap E E₁).comp (algebraMap A E)).toAlgebra
    have : IsScalarTower A E E₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A K E₁ := IsScalarTower.to₁₂₄ A K E E₁
    have : IsScalarTower A A' E₁ := IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap E E₁ (algebraMap A E a) = algebraMap A' E₁ (algebraMap A A' a)
      exact (IsScalarTower.algebraMap_apply A' E E₁ (algebraMap A A' a)).symm
    let T₁ := (L ⊗[K] E₁) ⧸ nilradical (L ⊗[K] E₁)
    let i : T →ₐ[L] T₁ := ReducedTensorTower.reductionMap
      (Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K E E₁))
    have hgeneric₁ (q : P) :
        let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
        let : Algebra E₁ (L ⊗[K] E₁) := Algebra.TensorProduct.rightAlgebra
        let : Algebra E₁ (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) :=
          Algebra.TensorProduct.rightAlgebra
        ∃ g : T₁ →ₐ[E₁]
            ReducedTensorTower.Reduction (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁),
          (∀ x : C, g (i x.val) = Ideal.Quotient.mk _
            ((algebraMap (Localization.AtPrime q.asIdeal) (FractionRing (Localization.AtPrime
              q.asIdeal))
              (algebraMap C (Localization.AtPrime q.asIdeal) x)) ⊗ₜ[E] (1 : E₁))) ∧
          let := g.toAlgebra
          IsLocalization (q.asIdeal.primeCompl.map (i.toRingHom.comp C.val.toRingHom))
            (ReducedTensorTower.Reduction (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁))
              := by
      let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
      let : Algebra E (L ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
      let : Algebra E₁ (L ⊗[K] E₁) := Algebra.TensorProduct.rightAlgebra
      let : Algebra E₁ (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) :=
        Algebra.TensorProduct.rightAlgebra
      obtain ⟨g₀, hg₀, hloc₀⟩ := hgenericE q
      let g := reducedTensorProductLocalizationMap K E E₁ L
        (FractionRing (Localization.AtPrime q.asIdeal)) g₀
      refine ⟨g, ?_, ?_⟩
      · intro x
        exact (reducedTensorProductLocalizationMap_includeRight K E E₁ L
          (FractionRing (Localization.AtPrime q.asIdeal)) g₀ x.val).trans
            (congrArg (fun z : FractionRing (Localization.AtPrime q.asIdeal) =>
              Ideal.Quotient.mk _ (z ⊗ₜ[E] (1 : E₁))) (hg₀ x))
      · have hloc := isLocalization_reducedTensorProductLocalizationMap K E E₁ L
          (FractionRing (Localization.AtPrime q.asIdeal)) g₀
          (Algebra.algebraMapSubmonoid T q.asIdeal.primeCompl) hloc₀
        convert! hloc using 1
        show q.asIdeal.primeCompl.map (i.toMonoidHom.comp C.val.toMonoidHom) =
          (q.asIdeal.primeCompl.map C.val.toMonoidHom).map i.toMonoidHom
        exact (Submonoid.map_map _ _ _).symm
    have : Algebra.IsAlgebraic K E₁ := Algebra.IsAlgebraic.trans K E E₁
    have : IsDedekindDomain (integralClosure A E₁) :=
      isDedekindDomain_integralClosure_of_integral_base A A' E E₁
    obtain ⟨hnoeth₁, f₁, hcomm₁, hsurj₁, hresidue₁⟩ :=
      IsDiscreteValuationRing.integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective
        A B K L E₁
    have := hnoeth₁
    let C₁ := integralClosure B T₁
    let algCT₁ : Algebra C T₁ := (i.toRingHom.comp C.val.toRingHom).toAlgebra
    let : SMul C T₁ := algCT₁.toSMul
    have : IsScalarTower B C T₁ := IsScalarTower.of_algebraMap_eq fun b =>
      ((i.restrictScalars B).commutes b).symm
    let c₁ : C →ₐ[B] C₁ := IsIntegralClosure.lift B C₁ T₁
    let algCC₁ : Algebra C C₁ := c₁.toAlgebra
    let : SMul C C₁ := algCC₁.toSMul
    have : IsScalarTower B C C₁ :=
      IsScalarTower.of_algebraMap_eq fun b => (c₁.commutes b).symm
    have : Algebra.IsIntegral C C₁ := Algebra.IsIntegral.tower_top (R := B)
    have hsmooth₁ (m : Ideal C₁) [m.IsMaximal] :
        RingHom.FormallySmoothNAdic.{max uL uK, uK, max uL uK}
          (R := Localization.AtPrime (m.comap f₁)) (S := Localization.AtPrime m)
          (Localization.localRingHom (m.comap f₁) m f₁ rfl)
          (IsLocalRing.maximalIdeal (Localization.AtPrime m)) := by
      obtain ⟨q, hq⟩ : ∃ q : P, q.asIdeal = m.comap (algebraMap C C₁) :=
        ⟨⟨m.comap (algebraMap C C₁), Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m⟩, rfl⟩
      let : Algebra E (FractionRing (Localization.AtPrime q.asIdeal)) := hEM q
      have : IsScalarTower A' E (FractionRing (Localization.AtPrime q.asIdeal)) := hA'EM q
      obtain ⟨D, hD⟩ := hcommon q
      let : Algebra E₁ (L ⊗[K] E₁) := Algebra.TensorProduct.rightAlgebra
      let : Algebra E₁ (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) :=
        Algebra.TensorProduct.rightAlgebra
      let Q := ReducedTensorTower.Reduction
        (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁)
      let U := integralClosure (Localization.AtPrime q.asIdeal)
        ((FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) ⧸
          nilradical (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁))
      let algCqQ : Algebra (Localization.AtPrime q.asIdeal) Q := inferInstance
      let algCQ : Algebra C Q :=
        ((algebraMap (Localization.AtPrime q.asIdeal) Q).comp
          (algebraMap C (Localization.AtPrime q.asIdeal))).toAlgebra
      let : SMul C Q := algCQ.toSMul
      have : IsScalarTower C (Localization.AtPrime q.asIdeal) Q :=
        IsScalarTower.of_algebraMap_eq (R := C) (S := Localization.AtPrime q.asIdeal)
          (A := Q) fun _ => rfl
      obtain ⟨G, hG, hGloc⟩ := hgeneric₁ q
      let := G.toAlgebra
      have : IsScalarTower C T₁ Q := IsScalarTower.of_algebraMap_eq fun x => by
        exact (hG x).symm
      have : IsLocalization (Algebra.algebraMapSubmonoid T₁ q.asIdeal.primeCompl) Q := hGloc
      let g : C₁ →ₐ[C] U := integralClosureMapOfIntegralBase B C T₁
        (Localization.AtPrime q.asIdeal) Q
      let := g.toAlgebra
      have hnorm : IsLocalization (Algebra.algebraMapSubmonoid C₁ q.asIdeal.primeCompl) U :=
        isLocalization_integralClosureMapOfIntegralBase B C T₁
          (Localization.AtPrime q.asIdeal) Q q.asIdeal.primeCompl
      have hdisj : Disjoint
          ((Algebra.algebraMapSubmonoid C₁ q.asIdeal.primeCompl) : Set C₁) (m : Set C₁) := by
        apply Set.disjoint_left.mpr
        rintro _ ⟨x, hx, rfl⟩ hxm
        apply hx
        show x ∈ q.asIdeal
        rw [hq]
        exact hxm
      apply formallySmoothNAdic_localRingHom_of_isLocalization
        (R := integralClosure A E₁) (S := C₁) (D := U) f₁
        (Algebra.algebraMapSubmonoid C₁ q.asIdeal.primeCompl) m hdisj
      let n : Ideal (integralClosure (Localization.AtPrime q.asIdeal)
          ((FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) ⧸
            nilradical (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁))) :=
        m.map (algebraMap C₁ U)
      have : n.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint
        (Algebra.algebraMapSubmonoid C₁ q.asIdeal.primeCompl) U m hdisj
      let algA'₁ : Algebra A' (integralClosure A E₁) :=
        (IsIntegralClosure.lift A (integralClosure A E₁) E₁ :
          A' →ₐ[A] integralClosure A E₁).toAlgebra
      let eA := integralClosureEquivOfIntegralBase A A' E₁
      have heA (x : integralClosure A' E₁) : (eA.symm x).val = x.val := by
        have hx := integralClosureEquivOfIntegralBase_apply A A' E₁ (eA.symm x)
        change (eA (eA.symm x)).val = (eA.symm x).val at hx
        simpa only [eA.apply_symm_apply] using hx.symm
      let fq : integralClosure A' E₁ →+* integralClosure (Localization.AtPrime q.asIdeal)
          ((FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) ⧸
            nilradical (FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁)) :=
        (g.toRingHom.comp f₁).comp eA.symm.toRingHom
      have hfq (x : integralClosure A' E₁) : (fq x).val = Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : E₁ →ₐ[E]
            FractionRing (Localization.AtPrime q.asIdeal) ⊗[E] E₁) x.val) := by
        calc
          (fq x).val = G (f₁ (eA.symm x)).val :=
            integralClosureMapOfIntegralBase_apply B C T₁
              (Localization.AtPrime q.asIdeal) Q (f₁ (eA.symm x))
          _ = G (algebraMap E₁ T₁ (eA.symm x).val) :=
            congrArg G (hcomm₁ (eA.symm x))
          _ = algebraMap E₁ Q (eA.symm x).val := G.commutes _
          _ = algebraMap E₁ Q x.val := congrArg (algebraMap E₁ Q) (heA x)
          _ = _ := rfl
      refine formallySmoothNAdic_localRingHom_of_ringEquiv_left fq (g.toRingHom.comp f₁)
        eA.symm.toRingEquiv rfl n ?_
      exact formallySmoothNAdic_integralClosure_of_isSolution
        (A := A') (B := Localization.AtPrime q.asIdeal) (K := E)
        (L := FractionRing (Localization.AtPrime q.asIdeal)) (K₁ := E₁) D hD fq hfq n
    exact exists_finite_extension_isSolution_of_formallySmooth_algebraicExtension
      A B K L E₁ f₁ hcomm₁ hgeom₁ hsmooth₁

end Stacks.EliminateRamification
