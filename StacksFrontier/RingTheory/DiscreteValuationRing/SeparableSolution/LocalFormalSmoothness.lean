module

public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableSolution.LinearPerturbation

/-!
# Formal smoothness at maximal ideals for solutions

Idempotent kernels of maps of integral closures, local ring maps, formal smoothness at
maximal ideals along a common surjective square, compatible `AdjoinRoot` orders, and
discrete valuation rings at maximal ideals of finite principal ideal rings.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

namespace IsDiscreteValuationRing

open Polynomial IntermediateField
open scoped TensorProduct

private theorem mapIntegralClosure_surjective_of_ker_eq_span_idempotent
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (f : S →ₐ[A] T) (hf : Function.Surjective f)
    {e : S} (he : IsIdempotentElem e) (hker : RingHom.ker f = Ideal.span {e}) :
    Function.Surjective f.mapIntegralClosure := by
  let e₀ : (S ⧸ RingHom.ker f) ≃ₐ[A] T :=
    { __ := f.toRingHom.quotientKerEquivOfSurjective hf
      commutes' := fun a => f.commutes a }
  let e₁ : (S ⧸ Ideal.span {e}) ≃ₐ[A] T :=
    (Ideal.quotientEquivAlgOfEq A hker.symm).trans e₀
  let d := AlgEquiv.prodQuotientOfIsIdempotentElem A he he.one_sub (by simp)
    (by rw [mul_sub, mul_one, he.eq, sub_self])
  intro y
  let z : S := d.symm (e₁.symm y, 0)
  have hz : IsIntegral A z :=
    ((y.property.map e₁.symm).pair (isIntegral_zero (R := A))).map d.symm
  refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  show f z = y.val
  have hd : Ideal.Quotient.mk (Ideal.span {e}) z = e₁.symm y :=
    congrArg Prod.fst (d.apply_symm_apply (e₁.symm y, 0))
  have hcompat : e₁ (Ideal.Quotient.mk (Ideal.span {e}) z) = f z := by
    show e₀ ((Ideal.quotientEquivAlgOfEq A hker.symm) (Ideal.Quotient.mk _ z)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    rfl
  rw [← hcompat, hd, e₁.apply_symm_apply]

theorem mapIntegralClosure_surjective_of_isArtinianRing
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [IsArtinianRing S] [IsReduced S]
    (f : S →ₐ[A] T) (hf : Function.Surjective f) :
    Function.Surjective f.mapIntegralClosure := by
  have : IsSemisimpleRing S := IsArtinianRing.isSemisimpleRing_of_isReduced S
  obtain ⟨e, he, hker⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker f)
  exact mapIntegralClosure_surjective_of_ker_eq_span_idempotent f hf he hker

theorem ker_mapIntegralClosure_eq_span_idempotent
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (f : S →ₐ[A] T)
    {e : S} (he : IsIdempotentElem e) (hker : RingHom.ker f = Ideal.span {e}) :
    ∃ e' : integralClosure A S, IsIdempotentElem e' ∧
      RingHom.ker f.mapIntegralClosure = Ideal.span {e'} := by
  have hei : IsIntegral A e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · exact (Polynomial.degree_X_le).trans_lt (by decide)
    · simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul,
        pow_two, sub_eq_zero] using he.eq
  let e' : integralClosure A S := ⟨e, hei⟩
  have he' : IsIdempotentElem e' := Subtype.ext he.eq
  refine ⟨e', he', le_antisymm ?_ ?_⟩
  · intro x hx
    have hxS : (x : S) ∈ Ideal.span {e} := by
      rw [← hker]
      exact congrArg Subtype.val (show f.mapIntegralClosure x = 0 from hx)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hxS
    have hex : e * (x : S) = x := by
      rw [ha, ← mul_assoc, he.eq]
    exact Ideal.mem_span_singleton.mpr ⟨x, Subtype.ext hex.symm⟩
  · apply Ideal.span_le.mpr
    rintro _ rfl
    apply Subtype.ext
    show f e = 0
    exact (hker.symm ▸ Ideal.subset_span (Set.mem_singleton e) : e ∈ RingHom.ker f)

/-- If `a / s` dies under the localized surjection, some lift `t'` of a unit kills `a`. -/
private theorem exists_lift_notMem_mul_eq_zero_of_localRingHom_mk'_eq_zero
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : Ideal S) [q.IsPrime]
    (a : R) (s : (q.comap f).primeCompl)
    (hz : Localization.localRingHom (q.comap f) q f rfl
      (IsLocalization.mk' (Localization.AtPrime (q.comap f)) a s) = 0) :
    ∃ t' : R, f t' ∉ q ∧ f (t' * a) = 0 := by
  rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨t, ht⟩ := hz
  obtain ⟨t', ht'⟩ := hf t.val
  refine ⟨t', ?_, ?_⟩
  · rw [ht']
    exact t.property
  · rwa [map_mul, ht']

private theorem localRingHom_bijective_of_ker_eq_span_idempotent
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) {e : R}
    (he : IsIdempotentElem e) (hker : RingHom.ker f = Ideal.span {e})
    (q : Ideal S) [q.IsPrime] :
    Function.Bijective (Localization.localRingHom (q.comap f) q f rfl) := by
  refine ⟨?_, localRingHom_surjective_of_surjective f hf q⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (q.comap f).primeCompl z
  obtain ⟨t', ht', hta⟩ :=
    exists_lift_notMem_mul_eq_zero_of_localRingHom_mk'_eq_zero f hf q a s hz
  have ha : t' * a ∈ Ideal.span {e} := by
    rw [← hker]
    exact hta
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hfe : f e = 0 :=
    (hker.symm ▸ Ideal.subset_span (Set.mem_singleton e) : e ∈ RingHom.ker f)
  have hu : (1 - e) * t' ∈ (q.comap f).primeCompl := by
    show f ((1 - e) * t') ∉ q
    simpa only [map_mul, map_sub, map_one, hfe, sub_zero, one_mul] using ht'
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨(1 - e) * t', hu⟩, ?_⟩
  show ((1 - e) * t') * a = 0
  rw [mul_assoc, hb, ← mul_assoc, sub_mul, one_mul, he.eq, sub_self, zero_mul]

private theorem ker_localRingHom_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : Ideal S) [q.IsPrime] :
    RingHom.ker (Localization.localRingHom (q.comap f) q f rfl) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime (q.comap f))) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (q.comap f).primeCompl z
    change Localization.localRingHom (q.comap f) q f rfl
      (IsLocalization.mk' (Localization.AtPrime (q.comap f)) a s) = 0 at hz
    obtain ⟨t', ht', hta⟩ :=
      exists_lift_notMem_mul_eq_zero_of_localRingHom_mk'_eq_zero f hf q a s hz
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨t', ht', hta⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    show Localization.localRingHom (q.comap f) q f rfl (algebraMap _ _ x) = 0
    rw [Localization.localRingHom_to_map, show f x = 0 from hx, map_zero]

private theorem ker_localRingHom_le_maximalIdeal_pow_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : Ideal S) [q.IsPrime]
    (n : ℕ) (hker : RingHom.ker f ≤ q.comap f ^ n) :
    RingHom.ker (Localization.localRingHom (q.comap f) q f rfl) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f)) ^ n := by
  rw [ker_localRingHom_of_surjective f hf q,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal (q.comap f), ← Ideal.map_pow]
  exact Ideal.map_mono hker

private theorem localRingHom_comp_eq_of_square
    {R S R₀ S₀ : Type*} [CommRing R] [CommRing S] [CommRing R₀] [CommRing S₀]
    (f : R →+* S) (f₀ : R₀ →+* S₀) (a : R →+* R₀) (b : S →+* S₀)
    (hsq : b.comp f = f₀.comp a)
    (p : Ideal R) (q : Ideal S) (p₀ : Ideal R₀) (q₀ : Ideal S₀)
    [p.IsPrime] [q.IsPrime] [p₀.IsPrime] [q₀.IsPrime]
    (hpq : p = q.comap f) (hpq₀ : p₀ = q₀.comap f₀)
    (hpa : p = p₀.comap a) (hqb : q = q₀.comap b) :
    (Localization.localRingHom q q₀ b hqb).comp (Localization.localRingHom p q f hpq) =
      (Localization.localRingHom p₀ q₀ f₀ hpq₀).comp (Localization.localRingHom p p₀ a hpa) := by
  apply IsLocalization.ringHom_ext p.primeCompl
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
  exact congrArg (algebraMap S₀ (Localization.AtPrime q₀)) (DFunLike.congr_fun hsq x)

theorem formallySmoothNAdic_atPrime_iff_of_common_surjective_square
    {R : Type u₁} {S : Type v₁} {R' : Type u₂} {S' : Type v₂} {R₀ S₀ : Type*}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [CommRing R₀] [CommRing S₀]
    (f : R →+* S) (f' : R' →+* S') (f₀ : R₀ →+* S₀)
    (a : R →+* R₀) (b : S →+* S₀) (a' : R' →+* R₀) (b' : S' →+* S₀)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (ha' : Function.Surjective a') (hb' : Function.Surjective b')
    (hsq : b.comp f = f₀.comp a) (hsq' : b'.comp f' = f₀.comp a')
    (p : Ideal R) (q : Ideal S) (p' : Ideal R') (q' : Ideal S')
    (p₀ : Ideal R₀) (q₀ : Ideal S₀)
    [p.IsPrime] [q.IsPrime] [p'.IsPrime] [q'.IsPrime] [p₀.IsPrime] [q₀.IsPrime]
    (hpq : p = q.comap f) (hpq' : p' = q'.comap f') (hpq₀ : p₀ = q₀.comap f₀)
    (hpa : p = p₀.comap a) (hqb : q = q₀.comap b)
    (hpa' : p' = p₀.comap a') (hqb' : q' = q₀.comap b')
    [IsDomain (Localization.AtPrime p)] [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    [IsDomain (Localization.AtPrime p')] [IsDiscreteValuationRing (Localization.AtPrime p')]
    [IsDomain (Localization.AtPrime q')] [IsDiscreteValuationRing (Localization.AtPrime q')]
    (hi : Function.Injective (Localization.localRingHom p q f hpq))
    (hi' : Function.Injective (Localization.localRingHom p' q' f' hpq'))
    (hker : RingHom.ker b ≤ q ^ 2) (hker' : RingHom.ker b' ≤ q' ^ 2) :
    RingHom.FormallySmoothNAdic.{max u₁ v₁} (Localization.localRingHom p q f hpq)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ↔
      RingHom.FormallySmoothNAdic.{max u₂ v₂} (Localization.localRingHom p' q' f' hpq')
        (IsLocalRing.maximalIdeal (Localization.AtPrime q')) := by
  let fL := Localization.localRingHom p q f hpq
  let fL' := Localization.localRingHom p' q' f' hpq'
  let fL₀ := Localization.localRingHom p₀ q₀ f₀ hpq₀
  let := fL.toAlgebra
  let := fL'.toAlgebra
  let := fL₀.toAlgebra
  have : FaithfulSMul (Localization.AtPrime p) (Localization.AtPrime q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  have : FaithfulSMul (Localization.AtPrime p') (Localization.AtPrime q') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi'
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    inferInstanceAs (IsLocalHom fL)
  have : IsLocalHom (algebraMap (Localization.AtPrime p') (Localization.AtPrime q')) :=
    inferInstanceAs (IsLocalHom fL')
  have : IsLocalHom (algebraMap (Localization.AtPrime p₀) (Localization.AtPrime q₀)) :=
    inferInstanceAs (IsLocalHom fL₀)
  have : IsExtension (Localization.AtPrime p) (Localization.AtPrime q) := ⟨⟩
  have : IsExtension (Localization.AtPrime p') (Localization.AtPrime q') := ⟨⟩
  apply formallySmoothNAdic_iff_of_common_surjective_square
    (Localization.AtPrime p) (Localization.AtPrime q)
    (Localization.AtPrime p') (Localization.AtPrime q')
    (Localization.AtPrime p₀) (Localization.AtPrime q₀)
    (Localization.localRingHom p p₀ a hpa) (Localization.localRingHom q q₀ b hqb)
    (Localization.localRingHom p' p₀ a' hpa') (Localization.localRingHom q' q₀ b' hqb')
  · cases hpa
    exact localRingHom_surjective_of_surjective a ha p₀
  · subst q
    exact localRingHom_surjective_of_surjective b hb q₀
  · cases hpa'
    exact localRingHom_surjective_of_surjective a' ha' p₀
  · subst q'
    exact localRingHom_surjective_of_surjective b' hb' q₀
  · exact localRingHom_comp_eq_of_square f f₀ a b hsq p q p₀ q₀ hpq hpq₀ hpa hqb
  · exact localRingHom_comp_eq_of_square f' f₀ a' b' hsq' p' q' p₀ q₀ hpq' hpq₀ hpa' hqb'
  · subst q
    exact ker_localRingHom_le_maximalIdeal_pow_of_surjective b hb q₀ 2 hker
  · subst q'
    exact ker_localRingHom_le_maximalIdeal_pow_of_surjective b' hb' q₀ 2 hker'

theorem exists_compatible_adjoinRoot_orders
    (A B K L : Type*)
    (K₁ K₂ : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra K₁ K₂] [Algebra K K₂]
    [Algebra A K₁] [Algebra A K₂]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [IsScalarTower K K₁ K₂] [IsScalarTower A K₁ K₂]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K K₁] [Module.Finite K₁ K₂]
    [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    (p : ℕ) (hp : p.Prime)
    (hsep : Algebra.IsSeparableExtension K L) (hB : IsNagataRing B)
    [CharP K p] (hpi : IsPurelyInseparable K₁ K₂) (hdegree : Module.finrank K₁ K₂ = p) :
    let := D₁.commRingL₁
    let := D₁.commRingA₁
    let := D₁.commRingB₁
    let := D₁.algebraKL₁
    let := D₁.algebraLL₁
    let := D₁.algebraK₁L₁
    let := D₁.algebraBL₁
    let := D₁.algebraAA₁
    let := D₁.algebraA₁K₁
    let := D₁.algebraBB₁
    let := D₁.algebraB₁L₁
    let := D₁.algebraAB₁
    let := D₁.algebraA₁B₁
    let := D₁.isScalarTowerKLL₁
    let := D₁.isScalarTowerKK₁L₁
    let := D₁.isScalarTowerBLL₁
    let := D₁.isScalarTowerAA₁K₁
    let := D₁.isScalarTowerBB₁L₁
    let := D₁.isScalarTowerABB₁
    let := D₁.isScalarTowerAA₁B₁
    let := D₁.isIntegralClosureA₁
    let := D₁.isIntegralClosureB₁
    let := D₂.commRingL₁
    let := D₂.commRingA₁
    let := D₂.commRingB₁
    let := D₂.algebraKL₁
    let := D₂.algebraLL₁
    let := D₂.algebraK₁L₁
    let := D₂.algebraBL₁
    let := D₂.algebraAA₁
    let := D₂.algebraA₁K₁
    let := D₂.algebraBB₁
    let := D₂.algebraB₁L₁
    let := D₂.algebraAB₁
    let := D₂.algebraA₁B₁
    let := D₂.isScalarTowerKLL₁
    let := D₂.isScalarTowerKK₁L₁
    let := D₂.isScalarTowerBLL₁
    let := D₂.isScalarTowerAA₁K₁
    let := D₂.isScalarTowerBB₁L₁
    let := D₂.isScalarTowerABB₁
    let := D₂.isScalarTowerAA₁B₁
    let := D₂.isIntegralClosureA₁
    let := D₂.isIntegralClosureB₁
    ∃ (c : D₁.A₁),
      let P : D₁.A₁[X] := X ^ p - C c
      let φ : D₁.A₁ →+* D₁.B₁ := algebraMap D₁.A₁ D₁.B₁
      ∃ (a₂ : AdjoinRoot P →+* D₂.A₁)
      (b₂ : AdjoinRoot (P.map φ) →+* D₂.B₁),
      (∀ r : A, a₂ (AdjoinRoot.of _ (algebraMap A D₁.A₁ r)) = algebraMap A D₂.A₁ r) ∧
      (∀ r : B, b₂ (AdjoinRoot.of _ (algebraMap B D₁.B₁ r)) = algebraMap B D₂.B₁ r) ∧
      Function.Injective a₂ ∧ Function.Injective b₂ ∧
      (letI := a₂.toAlgebra; Module.Finite (AdjoinRoot P) D₂.A₁) ∧
      (letI := b₂.toAlgebra;
        Module.Finite (AdjoinRoot (P.map φ)) D₂.B₁) ∧
      (algebraMap D₂.A₁ D₂.B₁).comp a₂ = b₂.comp
        (AdjoinRoot.map φ P
          (P.map φ) dvd_rfl) ∧
      (∀ r : A, IsLocalization.Away r K →
        letI := a₂.toAlgebra
        LocalizationEq (AdjoinRoot P) D₂.A₁
          (AdjoinRoot.of _ (algebraMap A D₁.A₁ r))) ∧
      (∀ r : B, IsLocalization.Away r L →
        letI := b₂.toAlgebra
        LocalizationEq (AdjoinRoot (P.map φ)) D₂.B₁
          (AdjoinRoot.of _ (algebraMap B D₁.B₁ r))) := by
  let := D₁.commRingL₁
  let := D₁.commRingA₁
  let := D₁.commRingB₁
  let := D₁.algebraKL₁
  let := D₁.algebraLL₁
  let := D₁.algebraK₁L₁
  let := D₁.algebraBL₁
  let := D₁.algebraAA₁
  let := D₁.algebraA₁K₁
  let := D₁.algebraBB₁
  let := D₁.algebraB₁L₁
  let := D₁.algebraAB₁
  let := D₁.algebraA₁B₁
  let := D₁.isScalarTowerKLL₁
  let := D₁.isScalarTowerKK₁L₁
  let := D₁.isScalarTowerBLL₁
  let := D₁.isScalarTowerAA₁K₁
  let := D₁.isScalarTowerBB₁L₁
  let := D₁.isScalarTowerABB₁
  let := D₁.isScalarTowerAA₁B₁
  let := D₁.isIntegralClosureA₁
  let := D₁.isIntegralClosureB₁
  let := D₂.commRingL₁
  let := D₂.commRingA₁
  let := D₂.commRingB₁
  let := D₂.algebraKL₁
  let := D₂.algebraLL₁
  let := D₂.algebraK₁L₁
  let := D₂.algebraBL₁
  let := D₂.algebraAA₁
  let := D₂.algebraA₁K₁
  let := D₂.algebraBB₁
  let := D₂.algebraB₁L₁
  let := D₂.algebraAB₁
  let := D₂.algebraA₁B₁
  let := D₂.isScalarTowerKLL₁
  let := D₂.isScalarTowerKK₁L₁
  let := D₂.isScalarTowerBLL₁
  let := D₂.isScalarTowerAA₁K₁
  let := D₂.isScalarTowerBB₁L₁
  let := D₂.isScalarTowerABB₁
  let := D₂.isScalarTowerAA₁B₁
  let := D₂.isIntegralClosureA₁
  let := D₂.isIntegralClosureB₁
  dsimp only
  let := hpi
  have : Module.Finite A D₂.A₁ := integralClosureBaseChange_finite_left A B K L K₂ D₂ hsep hB
  obtain ⟨c, a₁₂, a₂, hcoefA, hcompA, hiA, hmin, hgen, hfinA⟩ :=
    exists_injective_finite_adjoinRoot_integralClosure A K K₁ K₂ D₁.A₁ D₂.A₁ p hp hdegree
  obtain ⟨b₁₂, b₂, hcompB, hcoefB, hrootB, hiB, hfinB, hlocB⟩ :=
    exists_injective_finite_adjoinRoot_baseChange A B K L K₁ K₂ D₁ D₂ p hp hsep hB
      c (a₂ (AdjoinRoot.root _)) hmin hgen
  have hA (y : D₁.A₁) : a₂ (AdjoinRoot.of _ y) = a₁₂ y := DFunLike.congr_fun hcompA y
  have hB' (y : D₁.B₁) : b₂ (AdjoinRoot.of _ y) = b₁₂ y := DFunLike.congr_fun hcompB y
  refine ⟨c, a₂, b₂, ?_, ?_, hiA, hiB, hfinA, hfinB, ?_, ?_, hlocB⟩
  · intro r
    rw [hA, a₁₂.commutes]
  · intro r
    rw [hB', b₁₂.commutes]
  · apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro y
      show algebraMap D₂.A₁ D₂.B₁ (a₂ (AdjoinRoot.of _ y)) =
        b₂ (AdjoinRoot.map (algebraMap D₁.A₁ D₁.B₁) _ _ dvd_rfl (AdjoinRoot.of _ y))
      rw [AdjoinRoot.map_of, hA, hB']
      exact (hcoefB y (a₁₂ y) (hcoefA y)).symm
    · show algebraMap D₂.A₁ D₂.B₁ (a₂ (AdjoinRoot.root _)) =
        b₂ (AdjoinRoot.map (algebraMap D₁.A₁ D₁.B₁) _ _ dvd_rfl (AdjoinRoot.root _))
      rw [AdjoinRoot.map_root, hrootB]
  · intro r hloc
    let := hloc
    let := a₁₂.toRingHom.toAlgebra
    let : Algebra D₁.A₁ K₂ := ((algebraMap K₁ K₂).comp (algebraMap D₁.A₁ K₁)).toAlgebra
    have : IsScalarTower D₁.A₁ K₁ K₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower D₁.A₁ D₂.A₁ K₂ :=
      IsScalarTower.of_algebraMap_eq fun y => (hcoefA y).symm
    have : IsLocalization.Away (algebraMap A D₁.A₁ r) K₁ :=
      isLocalization_away_of_isIntegralClosure A K K₁ D₁.A₁ r
    let f : AdjoinRoot (X ^ p - C c) →ₐ[D₁.A₁] D₂.A₁ :=
      { __ := a₂
        commutes' := hA }
    exact localizationEq_of_adjoinRoot_minpoly D₁.A₁ K₁ K₂ D₂.A₁
      (algebraMap A D₁.A₁ r) (X ^ p - C c) f
      (IsIntegralClosure.algebraMap_injective D₂.A₁ A K₂)
      (IsIntegral.of_finite K₁ _) hgen
      (by
        show minpoly K₁ (algebraMap D₂.A₁ K₂ (a₂ (AdjoinRoot.root (X ^ p - C c)))) = _
        simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C] using hmin)

private theorem exists_algebra_isLocalization_away_of_localizationEq
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (r : R) [IsLocalization.Away r T]
    (hinj : Function.Injective (algebraMap R S)) (hloc : LocalizationEq R S r)
    (hreg : algebraMap R S r ∈ nonZeroDivisors S) :
    ∃ (_ : Algebra S T), IsScalarTower R S T ∧
      IsLocalization.Away (algebraMap R S r) T ∧ Function.Injective (algebraMap S T) := by
  let U := Localization.Away (algebraMap R S r)
  have : IsLocalization.Away r U :=
    isLocalization_away_of_localizationEq R S U r hinj hloc
  let e := IsLocalization.algEquiv (Submonoid.powers r) U T
  let : Algebra S T := (e.toRingHom.comp (algebraMap S U)).toAlgebra
  have htower : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap R T x = e (algebraMap S U (algebraMap R S x))
    rw [← IsScalarTower.algebraMap_apply]
    exact (e.commutes x).symm
  let eS : U ≃ₐ[S] T := { __ := e.toRingEquiv, commutes' := fun _ => rfl }
  have hlocT : IsLocalization.Away (algebraMap R S r) T :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap R S r)) eS
  exact ⟨inferInstance, htower, hlocT,
    e.injective.comp (IsLocalization.injective U (Submonoid.powers_le.mpr hreg))⟩

theorem ringHom_ext_of_localizationEq
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (r : R) (hloc : LocalizationEq R S r) (f g : S →+* T)
    (hreg : f (algebraMap R S r) ∈ nonZeroDivisors T)
    (hcomp : f.comp (algebraMap R S) = g.comp (algebraMap R S)) : f = g := by
  apply RingHom.ext
  intro x
  obtain ⟨n, y, hy⟩ := hloc x
  have hr : f (algebraMap R S r) = g (algebraMap R S r) := DFunLike.congr_fun hcomp r
  have h : f (algebraMap R S r) ^ n * f x = f (algebraMap R S r) ^ n * g x := by
    calc
      _ = f (algebraMap R S y) := by rw [← map_pow, ← map_mul, hy]
      _ = g (algebraMap R S y) := DFunLike.congr_fun hcomp y
      _ = _ := by rw [← hy, map_mul, map_pow, ← hr]
  exact (isRegular_iff_mem_nonZeroDivisors.mpr (pow_mem hreg n)).left h

private theorem isLocalization_away_pow_iff
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (r : R) (n : ℕ) (hn : 0 < n) :
    IsLocalization.Away (r ^ n) T ↔ IsLocalization.Away r T := by
  apply IsLocalization.iff_of_le_of_exists_dvd
  · rintro x ⟨m, rfl⟩
    exact ⟨n * m, pow_mul _ _ _⟩
  · rintro x ⟨m, rfl⟩
    refine ⟨(r ^ n) ^ m, ⟨m, rfl⟩, ?_⟩
    rw [← pow_mul]
    exact pow_dvd_pow r (Nat.le_mul_of_pos_left _ hn)

/-- Elements of the zero ideal's Jacobson radical map into the maximal ideal of each localization at
a maximal ideal. -/
private theorem algebraMap_mem_maximalIdeal_of_mem_jacobson_bot
    {R : Type*} [CommRing R] {x : R} (hx : x ∈ (⊥ : Ideal R).jacobson)
    (m : Ideal R) [m.IsMaximal] :
    algebraMap R (Localization.AtPrime m) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ m]
  simpa only [Ideal.jacobson_eq_self_of_isMaximal] using
    Ideal.jacobson_mono (bot_le : (⊥ : Ideal R) ≤ m) hx

private theorem isDiscreteValuationRing_atMaximal_of_isPrincipal_quotient_square
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ (⊥ : Ideal R).jacobson) (hxreg : x ∈ nonZeroDivisors R)
    (m : Ideal R) [m.IsMaximal]
    (hprincipal : (m.map (Ideal.Quotient.mk (Ideal.span {x ^ 2}))).IsPrincipal) :
    ∃ (_ : IsDomain (Localization.AtPrime m)), IsDiscreteValuationRing (Localization.AtPrime m) :=
      by
  have : IsDedekindDomain (Localization.AtPrime m) :=
    isDedekindDomain_atMaximal_of_isPrincipal_quotient_square hx hxreg m hprincipal
  have hm : (IsLocalRing.maximalIdeal (Localization.AtPrime m)).IsPrincipal := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m]
    exact (isPrincipal_maximal_of_isPrincipal_quotient_square hx m hprincipal).map_ringHom _
  have : IsPrincipalIdealRing (Localization.AtPrime m) :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime m)).out 5 1 |>.mp hm
  refine ⟨inferInstance, { not_a_field' := ?_ }⟩
  intro hzero
  have hxm' := algebraMap_mem_maximalIdeal_of_mem_jacobson_bot hx m
  rw [hzero, Ideal.mem_bot] at hxm'
  exact nonZeroDivisors.ne_zero
    (IsLocalization.nonZeroDivisors_le_comap m.primeCompl (Localization.AtPrime m) hxreg) hxm'

theorem exists_isIntegralClosure_of_localizationEq_of_quotient_equiv
    {A R S T C : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [CommRing S] [CommRing T] [CommRing C] [IsPrincipalIdealRing C]
    [Algebra A R] [Algebra A S] [Algebra A T] [Algebra R S] [Algebra R T]
    [IsScalarTower A R S] [IsScalarTower A R T] [Module.Finite A S]
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A)
    [IsLocalization.Away (algebraMap A R π ^ 2) T]
    (hinj : Function.Injective (algebraMap R S))
    (hloc : LocalizationEq R S (algebraMap A R π ^ 2))
    (hreg : algebraMap A S π ^ 2 ∈ nonZeroDivisors S)
    (I : Ideal C) (e : (C ⧸ I) ≃+* (S ⧸ Ideal.span {algebraMap A S π ^ 2})) :
    ∃ (_ : Algebra S T), IsScalarTower R S T ∧ IsScalarTower A S T ∧
      IsLocalization.Away (algebraMap A S π) T ∧ IsIntegralClosure S A T ∧
      (∀ (m : Ideal S) [m.IsMaximal],
        ∃ (_ : IsDomain (Localization.AtPrime m)),
          IsDiscreteValuationRing (Localization.AtPrime m)) := by
  obtain ⟨alg, htower, hlocT, hi⟩ := exists_algebra_isLocalization_away_of_localizationEq
    (T := T) (algebraMap A R π ^ 2) hinj hloc (by
      simpa only [map_pow, ← IsScalarTower.algebraMap_apply] using hreg)
  let := alg
  let := htower
  have htowerA : IsScalarTower A S T := IsScalarTower.to₁₃₄ A R S T
  have hlocT' : IsLocalization.Away (algebraMap A S π ^ 2) T := by
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply] using hlocT
  have hlocT'' : IsLocalization.Away (algebraMap A S π) T :=
    (isLocalization_away_pow_iff _ 2 (by decide)).mp hlocT'
  have hreg' : algebraMap A S π ∈ nonZeroDivisors S :=
    isRegular_iff_mem_nonZeroDivisors.mp
      ((IsRegular.pow_iff (by decide : 0 < 2)).mp (isRegular_iff_mem_nonZeroDivisors.mpr hreg))
  have : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  have hx : algebraMap A S π ∈ (⊥ : Ideal S).jacobson :=
    map_maximalIdeal_le_jacobson_of_isIntegral A S (Ideal.mem_map_of_mem _ hπ)
  have : IsIntegralClosure S A T := isIntegralClosure_of_quotient_equiv hx hreg' I e
  refine ⟨alg, htower, htowerA, hlocT'', inferInstance, ?_⟩
  have : IsPrincipalIdealRing (C ⧸ I) :=
    IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsPrincipalIdealRing (S ⧸ Ideal.span {algebraMap A S π ^ 2}) :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  intro m hm
  exact isDiscreteValuationRing_atMaximal_of_isPrincipal_quotient_square hx hreg' m
    (IsPrincipalIdealRing.principal _)

private theorem tensorAdjoinRootAlgEquiv_symm_of
    {K L F : Type*} [CommRing K] [CommRing L] [CommRing F]
    [Algebra K L] [Algebra K F] (P : F[X]) (z : L ⊗[K] F) :
    (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) P _ rfl).symm
        (AdjoinRoot.of _ z) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F (AdjoinRoot P)) z := by
  apply (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) P _ rfl).injective
  rw [AlgEquiv.apply_symm_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l x =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (IsScalarTower.toAlgHom L (L ⊗[K] F)
        (AdjoinRoot (P.map (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)))
          (l ⊗ₜ[K] x) = _
      rw [← mul_one l, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul]
      rw [← TensorProduct.smul_tmul', map_smul]
      congr 1
      exact (AdjoinRoot.tensorAlgEquiv_of (R := K) (T := L) P _ rfl).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isReduced_adjoinRoot_of_separable
    {F : Type*} [Field F] {P : F[X]} (hP : P.Separable) : IsReduced (AdjoinRoot P) := by
  apply (Ideal.isRadical_iff_quotient_reduced (Ideal.span {P})).mp
  exact isRadical_iff_span_singleton.mp hP.squarefree.isRadical

theorem exists_isLocalization_away_tensor_adjoinRoot
    {R K L F : Type*} [CommRing R] [CommRing K] [CommRing L] [CommRing F]
    [Algebra K L] [Algebra K F] (i : R →+* L ⊗[K] F)
    (P : R[X]) (Q : F[X])
    (hPQ : P.map i = Q.map (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
    (r : R) (hloc : letI := i.toAlgebra; IsLocalization.Away r (L ⊗[K] F)) :
    ∃ h : AdjoinRoot P →+* L ⊗[K] AdjoinRoot Q,
      (∀ x, h (AdjoinRoot.of P x) =
        Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F (AdjoinRoot Q)) (i x))
          ∧
      h (AdjoinRoot.root P) = 1 ⊗ₜ[K] AdjoinRoot.root Q ∧
      (letI := h.toAlgebra; IsLocalization.Away (AdjoinRoot.of P r) (L ⊗[K] AdjoinRoot Q)) := by
  let ψ : L ⊗[K] F →ₐ[L] L ⊗[K] AdjoinRoot Q :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K F (AdjoinRoot Q))
  let := i.toAlgebra
  let := ψ.toRingHom.toAlgebra
  let : Algebra R (L ⊗[K] AdjoinRoot Q) := (ψ.toRingHom.comp i).toAlgebra
  have : IsScalarTower R (L ⊗[K] F) (L ⊗[K] AdjoinRoot Q) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization.Away r (L ⊗[K] F) := hloc
  let e₀ : AdjoinRoot (Q.map (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
      ≃ₐ[L ⊗[K] F] L ⊗[K] AdjoinRoot Q :=
    { __ := (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) Q _ rfl).symm.toRingEquiv
      commutes' := fun x => tensorAdjoinRootAlgEquiv_symm_of Q x }
  let e : AdjoinRoot (P.map i) ≃ₐ[L ⊗[K] F] L ⊗[K] AdjoinRoot Q :=
    (Ideal.quotientEquivAlgOfEq (L ⊗[K] F)
      (congrArg (fun p : (L ⊗[K] F)[X] => Ideal.span {p}) hPQ)).trans e₀
  let f₀ : AdjoinRoot P →ₐ[R] AdjoinRoot (P.map i) :=
    { __ := AdjoinRoot.map i P (P.map i) dvd_rfl
      commutes' := fun x => AdjoinRoot.map_of i P (P.map i) dvd_rfl x }
  let f := (e.restrictScalars R).toAlgHom.comp f₀
  have hroot : e (AdjoinRoot.root (P.map i)) = f (AdjoinRoot.root P) := by
    simp only [f, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply]
    show _ = e (AdjoinRoot.map i P (P.map i) dvd_rfl (AdjoinRoot.root P))
    rw [AdjoinRoot.map_root]
  refine ⟨f.toRingHom, fun x => f.commutes x, ?_, ?_⟩
  · show f (AdjoinRoot.root P) = _
    rw [← hroot]
    show e₀ ((Ideal.quotientEquivAlgOfEq (L ⊗[K] F)
      (congrArg (fun p : (L ⊗[K] F)[X] => Ideal.span {p}) hPQ)) (Ideal.Quotient.mk _ X)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    apply (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) Q _ rfl).injective
    show (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) Q _ rfl)
      ((AdjoinRoot.tensorAlgEquiv (R := K) (T := L) Q _ rfl).symm (AdjoinRoot.root _)) = _
    rw [AlgEquiv.apply_symm_apply, AdjoinRoot.tensorAlgEquiv_root]
  · exact isLocalization_away_of_adjoinRoot_equiv R (L ⊗[K] F)
      (L ⊗[K] AdjoinRoot Q) r P f e hroot

private theorem injective_of_nonzero_mem_maximalIdeal
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] (f : R →+* S) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hfx : f x ≠ 0) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  by_contra hker
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hm : (RingHom.ker f).IsMaximal := (show (RingHom.ker f).IsPrime from inferInstance).isMaximal
    hker
  have heq : RingHom.ker f = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  exact hfx (show x ∈ RingHom.ker f from heq.symm ▸ hx)

theorem formallySmoothNAdic_atMaximal_of_common_surjective_square
    {R : Type u₁} {S : Type v₁} {R' : Type u₂} {S' : Type v₂} {R₀ S₀ : Type*}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [CommRing R₀] [CommRing S₀]
    (f : R →+* S) (f' : R' →+* S') (f₀ : R₀ →+* S₀)
    (a : R →+* R₀) (b : S →+* S₀) (a' : R' →+* R₀) (b' : S' →+* S₀)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (ha' : Function.Surjective a') (hb' : Function.Surjective b')
    (hsq : b.comp f = f₀.comp a) (hsq' : b'.comp f' = f₀.comp a')
    (hmax : ∀ (q : Ideal S) [q.IsMaximal], (q.comap f).IsMaximal)
    (hmax' : ∀ (q : Ideal S') [q.IsMaximal], (q.comap f').IsMaximal)
    (hR : ∀ (p : Ideal R) [p.IsMaximal], ∃ (_ : IsDomain (Localization.AtPrime p)),
      IsDiscreteValuationRing (Localization.AtPrime p))
    (hS : ∀ (q : Ideal S) [q.IsMaximal], ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q))
    (hR' : ∀ (p : Ideal R') [p.IsMaximal], ∃ (_ : IsDomain (Localization.AtPrime p)),
      IsDiscreteValuationRing (Localization.AtPrime p))
    (hS' : ∀ (q : Ideal S') [q.IsMaximal], ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q))
    (hi : ∀ (q : Ideal S) (hq : q.IsMaximal), letI := hq.isPrime
      Function.Injective (Localization.localRingHom (q.comap f) q f rfl))
    (hi' : ∀ (q : Ideal S') (hq : q.IsMaximal), letI := hq.isPrime
      Function.Injective (Localization.localRingHom (q.comap f') q f' rfl))
    (hker : ∀ (q : Ideal S) [q.IsMaximal], RingHom.ker b ≤ q ^ 2)
    (hker' : ∀ (q : Ideal S') [q.IsMaximal], RingHom.ker b' ≤ q ^ 2)
    (hsource : ∀ (q : Ideal S) (hq : q.IsMaximal), letI := hq.isPrime
      RingHom.FormallySmoothNAdic.{max u₁ v₁} (Localization.localRingHom (q.comap f) q f rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))) :
    ∀ (q' : Ideal S') (hq' : q'.IsMaximal), letI := hq'.isPrime
      RingHom.FormallySmoothNAdic.{max u₂ v₂} (Localization.localRingHom (q'.comap f') q' f' rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q')) := by
  intro q' hq'
  let := hq'
  let q₀ := q'.map b'
  have hkq' : RingHom.ker b' ≤ q' := (hker' q').trans (Ideal.pow_le_self (by decide))
  have : q₀.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hb' hkq'
  have hqb' : q' = q₀.comap b' := by
    show q' = (q'.map b').comap b'
    rw [Ideal.comap_map_of_surjective b' hb', ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkq']
  let q := q₀.comap b
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective b hb
  let p := q.comap f
  have hp : p.IsMaximal := hmax q
  let p' := q'.comap f'
  have hp' : p'.IsMaximal := hmax' q'
  let p₀ := q₀.comap f₀
  have hpa : p = p₀.comap a := by
    show (q₀.comap b).comap f = (q₀.comap f₀).comap a
    rw [Ideal.comap_comap, Ideal.comap_comap, hsq]
  have hpa' : p' = p₀.comap a' := by
    show q'.comap f' = (q₀.comap f₀).comap a'
    rw [hqb', Ideal.comap_comap, Ideal.comap_comap, hsq']
  obtain ⟨dR, vR⟩ := hR p
  obtain ⟨dS, vS⟩ := hS q
  obtain ⟨dR', vR'⟩ := hR' p'
  obtain ⟨dS', vS'⟩ := hS' q'
  let := dR
  let := vR
  let := dS
  let := vS
  let := dR'
  let := vR'
  let := dS'
  let := vS'
  exact (formallySmoothNAdic_atPrime_iff_of_common_surjective_square
    f f' f₀ a b a' b' ha hb ha' hb' hsq hsq' p q p' q' p₀ q₀
    rfl rfl rfl hpa rfl hpa' hqb' (hi q hq) (hi' q' hq')
    (hker q) (hker' q')).mp (hsource q hq)

theorem isMaximal_comap_of_finite_local_bases
    (A B R S : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A R] [Algebra B S] [Algebra A S] [Algebra R S]
    [IsScalarTower A B S] [IsScalarTower A R S]
    [Module.Finite A R] [Module.Finite B S]
    (q : Ideal S) [q.IsMaximal] : (q.comap (algebraMap R S)).IsMaximal := by
  have hqB : (q.comap (algebraMap B S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) q
  have hqBeq : q.comap (algebraMap B S) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal hqB
  have hqA : q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A := by
    rw [IsScalarTower.algebraMap_eq A B S, ← Ideal.comap_comap, hqBeq,
      IsLocalRing.maximalIdeal_comap]
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A)
  have heq : (q.comap (algebraMap R S)).comap (algebraMap A R) = IsLocalRing.maximalIdeal A := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hqA]
  rw [heq]
  infer_instance

theorem isDiscreteValuationRing_atMaximal_of_finite_of_isPrincipalIdealRing
    (A R : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [Algebra A R] [Module.Finite A R] [IsPrincipalIdealRing R]
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A)
    (hreg : algebraMap A R x ∈ nonZeroDivisors R)
    (m : Ideal R) [m.IsMaximal] :
    ∃ (_ : IsDomain (Localization.AtPrime m)), IsDiscreteValuationRing (Localization.AtPrime m) :=
      by
  have : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  have hjac : algebraMap A R x ∈ (⊥ : Ideal R).jacobson :=
    map_maximalIdeal_le_jacobson_of_isIntegral A R (Ideal.mem_map_of_mem _ hx)
  exact isDiscreteValuationRing_atMaximal_of_isPrincipal_quotient_square hjac hreg m
    ((IsPrincipalIdealRing.principal m).map_ringHom _)

theorem localRingHom_injective_of_finite_of_nonZeroDivisor
    (A R S : Type*) [CommRing A] [IsLocalRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    [Module.Finite A R] (q : Ideal S) [q.IsPrime]
    [(q.comap (algebraMap R S)).IsMaximal]
    [IsDomain (Localization.AtPrime (q.comap (algebraMap R S)))]
    [IsDiscreteValuationRing (Localization.AtPrime (q.comap (algebraMap R S)))]
    [IsDomain (Localization.AtPrime q)]
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A)
    (hreg : algebraMap A S x ∈ nonZeroDivisors S) :
    Function.Injective (Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl)
      := by
  let p := q.comap (algebraMap R S)
  apply injective_of_nonzero_mem_maximalIdeal (x := algebraMap R (Localization.AtPrime p)
    (algebraMap A R x))
  · exact algebraMap_mem_maximalIdeal_of_mem_jacobson_bot
      (map_maximalIdeal_le_jacobson_of_isIntegral A R (Ideal.mem_map_of_mem _ hx)) p
  · rw [Localization.localRingHom_to_map]
    show algebraMap S (Localization.AtPrime q) (algebraMap R S (algebraMap A R x)) ≠ 0
    rw [← IsScalarTower.algebraMap_apply A R S]
    exact nonZeroDivisors.ne_zero (IsLocalization.nonZeroDivisors_le_comap q.primeCompl
      (Localization.AtPrime q) hreg)

end IsDiscreteValuationRing
