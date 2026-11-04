module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AdjoinRootExtensions

/-!
# Abhyankar's lemma: adjoining a root of the uniformizer

Auxiliary results for Abhyankar's lemma: ramification index and residue field of the integral
closure after adjoining a root of the uniformizer, transport of formal smoothness along
equivalences and universe changes, and formal smoothness of the field factors of the tensor
product over the root extension.

## References

* [The Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y z

open scoped TensorProduct

open Polynomial

private theorem ramificationIndex_integralClosure_root_uniformizer
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (n : ℕ) [Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n))]
    [IsDiscreteValuationRing (Stacks.KummerExtension.A1 K π n)]
    [IsExtension A (Stacks.KummerExtension.A1 K π n)]
    (hn : 2 ≤ n) (hπ : Irreducible π) :
    ramificationIndex A (Stacks.KummerExtension.A1 K π n) = n := by
  obtain ⟨m, hm, hl, _, he⟩ := Stacks.KummerExtension.exists_ramificationIdx_eq K π n hn hπ
  have hm' : m = IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π n) :=
    IsLocalRing.eq_maximalIdeal hm
  subst m
  let := hl
  exact he

private theorem residueFieldMap_surjective_integralClosure_root_uniformizer
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (n : ℕ) [Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n))]
    [IsDiscreteValuationRing (Stacks.KummerExtension.A1 K π n)]
    [IsExtension A (Stacks.KummerExtension.A1 K π n)]
    (hn : 2 ≤ n) (hπ : Irreducible π) :
    Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Stacks.KummerExtension.A1 K π n))) := by
  obtain ⟨m, hm, hl, _, hf⟩ := Stacks.KummerExtension.isTotallyRamified_K1 K π n hn hπ
  have hm' : m = IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π n) :=
    IsLocalRing.eq_maximalIdeal hm
  subst m
  let := hl
  replace hf : (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π n)).inertiaDeg A = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π n))]
    simpa using hf
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π n))] at hf
  change Module.finrank (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField (Stacks.KummerExtension.A1 K π n)) = 1 at hf
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf).surjective

private theorem formallySmoothNAdic_of_ulift_test
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal S)
    (h : RingHom.FormallySmoothNAdic.{max u v} φ I) :
    RingHom.FormallySmoothNAdic.{u} φ I := by
  intro T _ J hJ f ψ hcomm hkill
  let e : T ≃+* ULift.{v} T := ULift.ringEquiv.symm
  let J' : Ideal (ULift.{v} T) := J.map e
  let eQ : T ⧸ J ≃+* (ULift.{v} T) ⧸ J' := Ideal.quotientEquiv J J' e rfl
  have hJ' : J' ^ 2 = 0 := by
    rw [← Ideal.map_pow, hJ]
    exact Ideal.map_bot
  have hcomm' : (eQ.toRingHom.comp ψ).comp φ =
      (Ideal.Quotient.mk J').comp (e.toRingHom.comp f) := by
    ext r
    show eQ (ψ (φ r)) = Ideal.Quotient.mk J' (e (f r))
    rw [show ψ (φ r) = Ideal.Quotient.mk J (f r) from RingHom.congr_fun hcomm r]
    exact Ideal.quotientEquiv_mk J J' e rfl (f r)
  have hkill' : ∃ k : ℕ, 1 ≤ k ∧ I ^ k ≤ RingHom.ker (eQ.toRingHom.comp ψ) := by
    obtain ⟨k, hk, hkI⟩ := hkill
    refine ⟨k, hk, fun s hs ↦ ?_⟩
    show eQ (ψ s) = 0
    rw [show ψ s = 0 from hkI hs, map_zero]
  obtain ⟨g, hg, hgf⟩ := h (ULift.{v} T) J' hJ'
    (e.toRingHom.comp f) (eQ.toRingHom.comp ψ) hcomm' hkill'
  refine ⟨e.symm.toRingHom.comp g, ?_, ?_⟩
  · ext s
    apply eQ.injective
    show eQ (Ideal.Quotient.mk J (e.symm (g s))) = eQ (ψ s)
    rw [Ideal.quotientEquiv_mk J J' e rfl, e.apply_symm_apply]
    exact RingHom.congr_fun hg s
  · ext r
    show e.symm (g (φ r)) = f r
    rw [show g (φ r) = e (f r) from RingHom.congr_fun hgf r, e.symm_apply_apply]

private theorem formallySmoothNAdic_of_targetEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (I : Ideal S) (e : S ≃+* T)
    (h : RingHom.FormallySmoothNAdic.{u} (e.toRingHom.comp φ) (I.map e)) :
    RingHom.FormallySmoothNAdic.{u} φ I := by
  intro Q _ J hJ f ψ hcomm hkill
  have hcomm' : (ψ.comp e.symm.toRingHom).comp (e.toRingHom.comp φ) =
      (Ideal.Quotient.mk J).comp f := by
    ext r
    show ψ (e.symm (e (φ r))) = Ideal.Quotient.mk J (f r)
    rw [e.symm_apply_apply]
    exact RingHom.congr_fun hcomm r
  have hkill' : ∃ k : ℕ, 1 ≤ k ∧
      I.map e ^ k ≤ RingHom.ker (ψ.comp e.symm.toRingHom) := by
    obtain ⟨k, hk, hkI⟩ := hkill
    refine ⟨k, hk, ?_⟩
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro s hs
    show ψ (e.symm (e s)) = 0
    rw [e.symm_apply_apply]
    exact hkI hs
  obtain ⟨g, hg, hgf⟩ := h Q J hJ f (ψ.comp e.symm.toRingHom) hcomm' hkill'
  refine ⟨g.comp e.toRingHom, ?_, ?_⟩
  · ext s
    show Ideal.Quotient.mk J (g (e s)) = ψ s
    have hg' : Ideal.Quotient.mk J (g (e s)) = ψ (e.symm (e s)) :=
      RingHom.congr_fun hg (e s)
    simpa only [e.symm_apply_apply] using hg'
  · exact hgf

/-- Formal smoothness for the maximal ideal of a local ring transports along a ring equivalence
of local rings. -/
private theorem formallySmoothNAdic_maximalIdeal_of_ringEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [IsLocalRing S] [IsLocalRing T]
    (φ : R →+* S) (e : S ≃+* T)
    (h : RingHom.FormallySmoothNAdic.{u} (e.toRingHom.comp φ) (IsLocalRing.maximalIdeal T)) :
    RingHom.FormallySmoothNAdic.{u} φ (IsLocalRing.maximalIdeal S) := by
  have : IsLocalHom e.toRingHom := ⟨fun r hr ↦ (isLocalHom_equiv e).map_nonunit r hr⟩
  have hmax : (IsLocalRing.maximalIdeal S).map e.toRingHom = IsLocalRing.maximalIdeal T := by
    rw [← IsLocalRing.maximalIdeal_comap e.toRingHom]
    exact Ideal.map_comap_of_surjective e.toRingHom e.surjective _
  exact formallySmoothNAdic_of_targetEquiv φ _ e (hmax ▸ h)

private theorem isDiscreteValuationRing_of_ringEquiv
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] (e : R ≃+* S) : IsDiscreteValuationRing S := by
  let : IsPrincipalIdealRing S := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  let : IsLocalRing S := RingEquiv.isLocalRing e
  refine IsDiscreteValuationRing.mk ?_
  intro h
  exact IsDiscreteValuationRing.not_isField R
    (MulEquiv.isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h) e.toMulEquiv)

theorem formallySmoothNAdic_of_max_universe
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B)
      (IsLocalRing.maximalIdeal B)) :
    RingHom.FormallySmoothNAdic.{w} (algebraMap A B)
      (IsLocalRing.maximalIdeal B) := by
  let C := ULift.{w} B
  let e : B ≃ₐ[B] C := ULift.algEquiv.symm
  let : IsDomain C := e.symm.injective.isDomain e.symm.toRingHom
  let : IsDiscreteValuationRing C := isDiscreteValuationRing_of_ringEquiv e.toRingEquiv
  let : IsLocalHom (algebraMap B C) := ⟨fun r hr ↦ by
    change IsUnit (e r) at hr
    have hr' : IsUnit (e.symm (e r)) := hr.map e.symm.toRingHom
    simpa only [e.symm_apply_apply] using hr'⟩
  let : IsLocalHom (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    infer_instance
  let : IsExtension B C := ⟨⟩
  let : IsExtension A C := ⟨⟩
  let : Algebra.FormallySmooth B C := Algebra.FormallySmooth.of_equiv e
  have hC : RingHom.FormallySmoothNAdic.{max u v w} (algebraMap A C)
      (IsLocalRing.maximalIdeal C) :=
    formallySmoothNAdic_trans A B C h (formallySmoothNAdic_of_formallySmooth _)
  have hB : RingHom.FormallySmoothNAdic.{max w (max u v)} (algebraMap A B)
      (IsLocalRing.maximalIdeal B) :=
    formallySmoothNAdic_maximalIdeal_of_ringEquiv (algebraMap A B) e.toRingEquiv hC
  exact formallySmoothNAdic_of_ulift_test (algebraMap A B) _ hB

theorem exists_finite_algebra_adjoinRoot_of_eval_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (f : R[X]) (x : S) (hx : f.eval₂ (algebraMap R S) x = 0) :
    ∃ (_ : Algebra (AdjoinRoot f) S) (_ : IsScalarTower R (AdjoinRoot f) S),
      Module.Finite (AdjoinRoot f) S ∧ algebraMap (AdjoinRoot f) S (AdjoinRoot.root f) = x := by
  let φ : AdjoinRoot f →ₐ[R] S := AdjoinRoot.liftAlgHom f (Algebra.ofId R S) x hx
  let : Algebra (AdjoinRoot f) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (AdjoinRoot f) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  refine ⟨inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite R _ _, ?_⟩
  exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId R S) x hx

theorem formallySmoothNAdic_over_root_uniformizer
    (A : Type u) (B : Type v) (K : Type w) (L : Type z)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (π : A) (n : ℕ) [Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n))]
    [IsDiscreteValuationRing (Stacks.KummerExtension.A1 K π n)]
    [IsExtension A (Stacks.KummerExtension.A1 K π n)]
    (E : Type*) (D : Type x) [Field E] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Algebra (integralClosure B E) D] [Algebra B D]
    [IsScalarTower B (integralClosure B E) D]
    [Algebra A D] [Algebra (Stacks.KummerExtension.A1 K π n) D]
    [IsScalarTower A B D] [IsScalarTower A (Stacks.KummerExtension.A1 K π n) D]
    [IsExtension A D] [IsExtension B D]
    [IsExtension (Stacks.KummerExtension.A1 K π n) D]
    (q : Ideal (integralClosure B E)) [q.IsPrime] [IsLocalization.AtPrime D q]
    (hπ : Irreducible π) (hn : 2 ≤ n) (he : ramificationIndex A B = n)
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A)) n ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    (f : L ⊗[K] Stacks.KummerExtension.K1 K π n →ₐ[L] E) (hf : Function.Surjective f) :
    RingHom.FormallySmoothNAdic.{y} (algebraMap (Stacks.KummerExtension.A1 K π n) D)
      (IsLocalRing.maximalIdeal D) := by
  have hn0 : n ≠ 0 := by omega
  have hunitA : IsUnit (n : A) := isUnit_natCast_of_residueChar hn0
    (htame.imp_right And.left)
  have hunitB : IsUnit (n : B) := by
    simpa only [map_natCast] using hunitA.map (algebraMap A B)
  have hs : Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) := by
    rcases htame with h | h
    · exact isSeparableExtension_of_ringChar_eq_zero _ _ h
    · exact h.2
  let := hs
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_prime B
  obtain ⟨b, hb⟩ := (ramificationIndex_characterization A B).2.2.2
    π hπ t ht.irreducible
  rw [he] at hb
  let c : Lˣ := Units.mk0 (algebraMap B L t)
    (by simpa only [map_zero] using (IsFractionRing.injective B L).ne ht.ne_zero)
  have hπL : algebraMap K L (algebraMap A K π) =
      (c : L) ^ n * algebraMap B L (b : B) := by
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      hb, map_mul, map_pow]
    exact mul_comm _ _
  let : Algebra.FormallyEtale B (integralClosure B E) :=
    formallyEtale_integralClosure_of_tensorProduct_adjoinRoot_factor
      (algebraMap A K π) b c hn0 hunitB hπL f hf
  let : Algebra.FormallySmooth (integralClosure B E) D :=
    Algebra.FormallySmooth.of_isLocalization q.primeCompl
  let : Algebra.FormallySmooth B D := Algebra.FormallySmooth.comp B (integralClosure B E) D
  apply formallySmoothNAdic_of_max_universe (Stacks.KummerExtension.A1 K π n) D
  exact formallySmoothNAdic_of_ramificationIndex_eq A B (Stacks.KummerExtension.A1 K π n) D
    (he.trans (ramificationIndex_integralClosure_root_uniformizer K π n hn hπ).symm)
    (residueFieldMap_surjective_integralClosure_root_uniformizer K π n hn hπ)
    (formallySmoothNAdic_of_formallySmooth _)

private theorem exists_integralClosure_localization
    (R Rₘ E : Type*) [CommRing R] [CommRing Rₘ] [Field E]
    [Algebra R Rₘ] [Algebra R E] [Algebra Rₘ E] [IsScalarTower R Rₘ E]
    (M : Submonoid R) [IsLocalization M Rₘ]
    (hM : ∀ m ∈ M, algebraMap R E m ≠ 0) :
    ∃ (_ : Algebra (integralClosure R E) (integralClosure Rₘ E)),
      IsScalarTower (integralClosure R E) (integralClosure Rₘ E) E ∧
      IsScalarTower R (integralClosure R E) (integralClosure Rₘ E) ∧
      IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R E) M)
        (integralClosure Rₘ E) ∧
      ∀ a : integralClosure R E,
        (algebraMap (integralClosure R E) (integralClosure Rₘ E) a : E) = (a : E) := by
  let f : integralClosure R E →+* integralClosure Rₘ E :=
    { toFun := fun a ↦ ⟨a, a.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let : Algebra (integralClosure R E) (integralClosure Rₘ E) := f.toAlgebra
  let : IsScalarTower (integralClosure R E) (integralClosure Rₘ E) E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower R (integralClosure R E) (integralClosure Rₘ E) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid E M) E :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨m, hm, rfl⟩
      exact isUnit_iff_ne_zero.mpr (hM m hm))
  exact ⟨inferInstance, inferInstance, inferInstance,
    IsLocalization.integralClosure (S := E) (Rf := Rₘ) (Sf := E) M, fun _ ↦ rfl⟩

private theorem formallySmoothNAdic_of_sourceEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* T) (I : Ideal T) (e : R ≃+* S)
    (h : RingHom.FormallySmoothNAdic.{u} (φ.comp e.symm.toRingHom) I) :
    RingHom.FormallySmoothNAdic.{u} φ I := by
  intro Q _ J hJ f ψ hcomm hkill
  have hcomm' : ψ.comp (φ.comp e.symm.toRingHom) =
      (Ideal.Quotient.mk J).comp (f.comp e.symm.toRingHom) := by
    rw [← RingHom.comp_assoc, hcomm, RingHom.comp_assoc]
  obtain ⟨g, hg, hgf⟩ := h Q J hJ (f.comp e.symm.toRingHom) ψ hcomm' hkill
  refine ⟨g, hg, ?_⟩
  ext r
  show g (φ r) = f r
  have hr := RingHom.congr_fun hgf (e r)
  change g (φ (e.symm (e r))) = f (e.symm (e r)) at hr
  simpa only [e.symm_apply_apply] using hr

theorem formallySmoothNAdic_of_equiv_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (I : Ideal S) (J : Ideal S')
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : eS.toRingHom.comp φ = ψ.comp eR.toRingHom)
    (hIJ : I.map eS.toRingHom = J)
    (h : RingHom.FormallySmoothNAdic.{u} ψ J) :
    RingHom.FormallySmoothNAdic.{u} φ I := by
  apply formallySmoothNAdic_of_targetEquiv φ I eS
  show RingHom.FormallySmoothNAdic (eS.toRingHom.comp φ) (I.map eS.toRingHom)
  rw [hIJ]
  apply formallySmoothNAdic_of_sourceEquiv _ J eR
  convert h using 1
  rw [hcomm]
  ext r
  show ψ (eR (eR.symm r)) = ψ r
  rw [eR.apply_symm_apply]

private theorem exists_isLocalizationAway_mapIntegralClosure
    {R T E : Type*} [CommRing R] [CommRing T] [Field E]
    [Algebra R T] [Algebra R E] [IsArtinianRing T] [IsReduced T]
    (f : T →ₐ[R] E) (hf : Function.Surjective f) :
    letI := f.mapIntegralClosure.toAlgebra
    ∃ s : integralClosure R T, IsLocalization.Away s (integralClosure R E) := by
  classical
  let := f.mapIntegralClosure.toAlgebra
  let m : MaximalSpectrum T := ⟨RingHom.ker f,
    RingHom.ker_isMaximal_of_surjective f hf⟩
  let d := (IsArtinianRing.equivPi T).restrictScalars R
  let c : T := d.symm (Pi.single m 1)
  have hc : IsIdempotentElem c := by
    apply d.injective
    ext j
    by_cases hj : j = m
    · subst j; simp [c]
    · simp [c, Pi.single_eq_of_ne hj]
  have hi : IsIntegral R c := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num)), ?_⟩
    simpa only [eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, pow_two, sub_eq_zero] using
      (show c * c = c from hc)
  let s : integralClosure R T := ⟨c, hi⟩
  have hs : IsIdempotentElem s := Subtype.ext hc
  refine ⟨s, IsLocalization.away_of_isIdempotentElem_of_mul hs ?_
    (surjective_mapIntegralClosure_of_isArtinianRing f hf)⟩
  intro a b
  show f.mapIntegralClosure a = f.mapIntegralClosure b ↔ s * a = s * b
  have hfm (a b : T) : f a = f b ↔ d a m = d b m := by
    let e := Ideal.quotientKerAlgEquivOfSurjective hf
    show e (Ideal.Quotient.mk (RingHom.ker f) a) =
      e (Ideal.Quotient.mk (RingHom.ker f) b) ↔ _
    exact e.injective.eq_iff
  rw [Subtype.ext_iff, Subtype.ext_iff]
  show f (a : T) = f (b : T) ↔ c * (a : T) = c * (b : T)
  rw [hfm, ← d.injective.eq_iff]
  constructor
  · intro h
    ext j
    by_cases hj : j = m
    · subst j; simpa [c] using h
    · simp [c, Pi.single_eq_of_ne hj]
  · intro h
    simpa [c] using congrFun h m

theorem isLocalHom_localizationAtPrime_of_isIntegral
    (A C D : Type*) [CommRing A] [IsLocalRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra C D] [Algebra A D] [IsScalarTower A C D]
    [Algebra.IsIntegral A C] (p : Ideal C) [p.IsMaximal]
    [IsLocalization.AtPrime D p] [IsLocalRing D] : IsLocalHom (algebraMap A D) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap A D)).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq A C D, ← Ideal.comap_comap]
  show ((IsLocalRing.maximalIdeal D).under C).comap (algebraMap A C) = _
  rw [IsLocalization.AtPrime.under_maximalIdeal D p]
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)

theorem maximalIdeal_ne_bot_of_isIntegral
    (A C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C]
    [Algebra.IsIntegral A C] (p : Ideal C) [p.IsMaximal] : p ≠ ⊥ := by
  intro hp
  have hfield : IsField C := Ring.isField_iff_maximal_bot.mpr (hp ▸ ‹p.IsMaximal›)
  exact IsDiscreteValuationRing.not_isField A
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective A C) hfield)

theorem exists_fractionRing_localizationAtPrime_algebra
    (C E : Type*) [CommRing C] [IsDomain C] [Field E]
    [Algebra C E] [IsFractionRing C E] (p : Ideal C) [p.IsPrime] :
    ∃ (_ : Algebra (Localization.AtPrime p) E),
      IsScalarTower C (Localization.AtPrime p) E ∧
      IsFractionRing (Localization.AtPrime p) E := by
  have hu (s : p.primeCompl) : IsUnit (algebraMap C E s) := by
    apply isUnit_iff_ne_zero.mpr
    exact fun h ↦ s.2 ((IsFractionRing.injective C E (h.trans (map_zero _).symm)) ▸ p.zero_mem)
  let f : Localization.AtPrime p →+* E := IsLocalization.lift hu
  let : Algebra (Localization.AtPrime p) E := f.toAlgebra
  let : IsScalarTower C (Localization.AtPrime p) E :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (IsLocalization.lift_eq hu c).symm
  exact ⟨inferInstance, inferInstance,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ _⟩

set_option maxHeartbeats 800000 in
-- Elaborating the many nested localization and tensor-product algebra structures here is
-- expensive.
set_option synthInstance.maxHeartbeats 80000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The two canonical localizations carry the algebra structures of both field factors.
theorem formallySmoothNAdic_tensorProduct_fieldFactor
    (A : Type u) (B : Type v) (K L K₁ E : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁] [Field E]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K E] [Algebra L E] [Algebra K₁ E] [Algebra B E]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower K L E] [IsScalarTower K K₁ E] [IsScalarTower B L E]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (f : L ⊗[K] K₁ →ₐ[L] E) (hf : Function.Surjective f)
    (hfK₁ : ∀ a : K₁, f (Algebra.TensorProduct.includeRight a) = algebraMap K₁ E a)
    (g : integralClosure A K₁ →+* integralClosure B E)
    (hg : ∀ a : integralClosure A K₁, (g a : E) = algebraMap K₁ E (a : K₁))
    (p : Ideal (integralClosure A K₁)) [p.IsPrime]
    (q : Ideal (integralClosure B E)) [q.IsMaximal] (hpq : q.comap g = p)
    (ψ : Localization.AtPrime p →+* Localization.AtPrime q)
    (hψ : ∀ a, ψ (algebraMap (integralClosure A K₁) _ a) =
      algebraMap (integralClosure B E) _ (g a))
    (hformal : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B)
      (IsLocalRing.maximalIdeal B)) :
    RingHom.FormallySmoothNAdic.{z} ψ
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  let T := L ⊗[K] K₁
  let Q := T ⧸ nilradical T
  let : Algebra K₁ T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower K K₁ T := Algebra.TensorProduct.right_isScalarTower
  let : Algebra K₁ Q := inferInstance
  let : IsScalarTower K K₁ Q := inferInstance
  let : IsScalarTower A K₁ Q := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K Q, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ Q]
  let A₁ := integralClosure A K₁
  let C := integralClosure B Q
  let F := integralClosure B E
  obtain ⟨gQ, hgQ, hgQA⟩ := exists_integralClosure_hom A B K₁ Q
  let : Algebra A₁ C := gQ.toAlgebra
  let : IsScalarTower A A₁ C := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B C]
    exact (hgQA a).symm
  have hfzero : ∀ t ∈ nilradical T, (f.restrictScalars B) t = 0 := by
    intro t ht
    exact (mem_nilradical.mp ht).map f |>.eq_zero
  let fQ : Q →ₐ[B] E := Ideal.Quotient.liftₐ (nilradical T) (f.restrictScalars B) hfzero
  have hfQ : Function.Surjective fQ := by
    intro e
    obtain ⟨t, rfl⟩ := hf e
    exact ⟨Ideal.Quotient.mk _ t, rfl⟩
  have hfQK₁ (a : K₁) : fQ (algebraMap K₁ Q a) = algebraMap K₁ E a := hfK₁ a
  let : IsArtinianRing T := IsArtinianRing.of_finite L T
  let : IsArtinianRing Q := inferInstance
  let : IsReduced Q := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  let α : C →ₐ[B] F := fQ.mapIntegralClosure
  let : Algebra C F := α.toAlgebra
  let : IsScalarTower B C F := IsScalarTower.of_algebraMap_eq fun b ↦ (α.commutes b).symm
  have hα : Function.Surjective α := surjective_mapIntegralClosure_of_isArtinianRing fQ hfQ
  obtain ⟨s, hs⟩ := exists_isLocalizationAway_mapIntegralClosure fQ hfQ
  let : IsLocalization.Away s F := hs
  have hdiag : α.toRingHom.comp gQ = g := by
    ext a
    show fQ (gQ a : Q) = (g a : E)
    rw [hgQ, hfQK₁, hg]
  let q' : Ideal C := q.comap α.toRingHom
  let : q'.IsMaximal := Ideal.comap_isMaximal_of_surjective α.toRingHom hα
  have hp' : q'.comap (algebraMap A₁ C) = p := by
    show (q.comap α.toRingHom).comap gQ = p
    rw [Ideal.comap_comap, hdiag, hpq]
  have hwhole := formallySmooth_localizations_after_finite_fraction_field_extension
    A B K L K₁ Q A₁ C (AlgEquiv.refl) (AlgEquiv.refl) (AlgEquiv.refl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun k ↦ by rw [← IsScalarTower.algebraMap_apply K L Q,
      ← IsScalarTower.algebraMap_apply K K₁ Q]) hgQ hformal
  have hloc := hwhole.2.2 q' inferInstance
  rw [hp'] at hloc
  obtain ⟨_, hq'prime, hp'prime, ⟨hRdom, hRdvr⟩, ⟨hDdom, hDdvr⟩,
    φ, hφinj, hφlocal, hφ, hφformal⟩ := hloc
  let := hRdom
  let := hRdvr
  let := hDdom
  let := hDdvr
  let R := Localization.AtPrime p
  let D' := Localization.AtPrime q'
  let D := Localization.AtPrime q
  let : Algebra R D' := φ.toAlgebra
  let : FaithfulSMul R D' := (faithfulSMul_iff_algebraMap_injective R D').mpr hφinj
  let : IsLocalHom (algebraMap R D') := hφlocal
  let : IsExtension R D' := ⟨⟩
  have hφtest : RingHom.FormallySmoothNAdic.{z} φ (IsLocalRing.maximalIdeal D') :=
    formallySmoothNAdic_of_max_universe R D' hφformal
  let : IsLocalization.AtPrime D q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers s) D q
  let eD : D' ≃ₐ[C] D := IsLocalization.algEquiv q'.primeCompl D' D
  have hcomm : eD.toRingHom.comp φ = ψ := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    show eD (φ (algebraMap A₁ R a)) = ψ (algebraMap A₁ R a)
    rw [hφ, hψ, eD.commutes]
    show algebraMap F D (α (gQ a)) = algebraMap F D (g a)
    exact congrArg (algebraMap F D) (RingHom.congr_fun hdiag a)
  apply formallySmoothNAdic_maximalIdeal_of_ringEquiv ψ eD.symm.toRingEquiv
  convert hφtest using 1
  ext r
  apply eD.injective
  show eD (eD.symm (ψ r)) = eD (φ r)
  rw [eD.apply_symm_apply]
  exact (RingHom.congr_fun hcomm r).symm

private theorem exists_integralClosure_equiv_of_isIntegral
    (A C E : Type*) [CommRing A] [CommRing C] [CommRing E]
    [Algebra A C] [Algebra C E] [Algebra A E] [IsScalarTower A C E]
    [Algebra.IsIntegral A C] :
    ∃ e : integralClosure A E ≃ₐ[A] (integralClosure C E).restrictScalars A,
      ∀ a : integralClosure A E, (e a : E) = (a : E) := by
  let e : integralClosure A E ≃ₐ[A] (integralClosure C E).restrictScalars A :=
    { toFun := fun a ↦ ⟨a, a.2.tower_top⟩
      invFun := fun a ↦ ⟨a, isIntegral_trans (R := A) (a : E) a.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact ⟨e, fun _ ↦ rfl⟩

theorem ramificationIdx_maximalIdeal_localizationAtPrime
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    (p : Ideal C) [p.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ramificationIdx A =
      p.ramificationIdx A := by
  classical
  let R := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal R
  let R' := Localization.AtPrime m
  let : IsLocalization.AtPrime R m := IsLocalization.of_le_isUnit fun r hr ↦ by
    change ¬¬IsUnit r at hr
    exact not_not.mp hr
  let e : R' ≃ₐ[R] R := IsLocalization.algEquiv m.primeCompl R' R
  have hunder : m.under A = p.under A := by
    show m.comap (algebraMap A R) = p.under A
    rw [IsScalarTower.algebraMap_eq A C R, ← Ideal.comap_comap]
    show (m.under C).comap (algebraMap A C) = p.under A
    rw [IsLocalization.AtPrime.under_maximalIdeal R p]
  have hmap : (p.under A).map (algebraMap A R') =
      ((p.under A).map (algebraMap A R)).comap e.toRingHom := by
    have hcomp : e.toRingHom.comp (algebraMap A R') = algebraMap A R := by
      ext a
      show e (algebraMap A R' a) = algebraMap A R a
      rw [IsScalarTower.algebraMap_apply A R R', e.commutes]
      rfl
    rw [← hcomp, ← Ideal.map_map, Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def, hunder]
  show (Module.length R' (R' ⧸ (p.under A).map (algebraMap A R'))).toNat =
    (Module.length R (R ⧸ (p.under A).map (algebraMap A R))).toNat
  rw [Module.length_quotient, Module.length_quotient, hmap,
    Ideal.coheight_comap_of_surjective e.toRingHom e.surjective]

private theorem isLocalization_comap_of_ringEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R T] [Algebra S T] (M : Submonoid S) [IsLocalization M T]
    (e : R ≃+* S) (h : (algebraMap S T).comp e.toRingHom = algebraMap R T) :
    IsLocalization (M.comap e.toMonoidHom) T := by
  have hmap (r : R) : algebraMap R T r = algebraMap S T (e r) :=
    (RingHom.congr_fun h r).symm
  constructor
  constructor
  · intro r
    rw [hmap]
    exact IsLocalization.map_units T ⟨e r, r.2⟩
  · intro t
    obtain ⟨⟨s, m⟩, hm⟩ := IsLocalization.surj M t
    refine ⟨⟨e.symm s, ⟨e.symm m, ?_⟩⟩, ?_⟩
    · show e (e.symm (m : S)) ∈ M
      simpa only [e.apply_symm_apply] using m.2
    · simpa only [hmap, e.apply_symm_apply] using hm
  · intro a b hab
    rw [hmap, hmap] at hab
    obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M T).mp hab
    refine ⟨⟨e.symm m, ?_⟩, ?_⟩
    · show e (e.symm (m : S)) ∈ M
      simpa only [e.apply_symm_apply] using m.2
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hm

private theorem exists_integralClosure_localization_of_isIntegral
    (A C D E : Type*) [CommRing A] [CommRing C] [CommRing D] [Field E]
    [Algebra A C] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
    [Algebra A E] [Algebra C E] [Algebra D E]
    [IsScalarTower A C E] [IsScalarTower A D E] [IsScalarTower C D E]
    [Algebra.IsIntegral A C] (M : Submonoid C) [IsLocalization M D]
    (hM : ∀ m ∈ M, algebraMap C E m ≠ 0) :
    ∃ (_ : Algebra (integralClosure A E) (integralClosure D E)),
      IsScalarTower (integralClosure A E) (integralClosure D E) E ∧
      IsScalarTower A (integralClosure A E) (integralClosure D E) ∧
      (∃ N : Submonoid (integralClosure A E), IsLocalization N (integralClosure D E) ∧
        ∀ n ∈ N, ∃ m ∈ M, (n : E) = algebraMap C E m) ∧
      ∀ a : integralClosure A E,
        (algebraMap (integralClosure A E) (integralClosure D E) a : E) = (a : E) := by
  obtain ⟨e, he⟩ := exists_integralClosure_equiv_of_isIntegral A C E
  obtain ⟨hCD, ht, htC, hloc, hmap⟩ := exists_integralClosure_localization C D E M hM
  let := hCD
  let := ht
  let := htC
  let := hloc
  let f : integralClosure A E →+* integralClosure D E :=
    (algebraMap (integralClosure C E) (integralClosure D E)).comp e.toRingHom
  have hf (a : integralClosure A E) : (f a : E) = (a : E) := (hmap (e a)).trans (he a)
  let : Algebra (integralClosure A E) (integralClosure D E) := f.toAlgebra
  let : IsScalarTower (integralClosure A E) (integralClosure D E) E :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (hf a).symm
  let : IsScalarTower A (integralClosure A E) (integralClosure D E) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply Subtype.ext
      exact (hf (algebraMap A (integralClosure A E) a)).symm
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, hf⟩
  let e' : integralClosure A E ≃+* integralClosure C E := e.toRingEquiv
  refine ⟨(Algebra.algebraMapSubmonoid (integralClosure C E) M).comap e'.toMonoidHom,
    isLocalization_comap_of_ringEquiv _ e' rfl, ?_⟩
  rintro n ⟨m, hm, hmn⟩
  refine ⟨m, hm, ?_⟩
  rw [← he n]
  exact (congrArg Subtype.val hmn).symm.trans
    (IsScalarTower.algebraMap_apply C (integralClosure C E) E m).symm

end

end IsDiscreteValuationRing
