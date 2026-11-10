module

public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableSolution.LocalCriteria

/-!
# `AdjoinRoot` orders in integral closures of solutions

Orders `A[x]/(P)` inside integral closures of discrete valuation rings, comparisons of
`AdjoinRoot` with tensor products, and localisations away from a uniformiser of the
integral closures of a solution.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open Polynomial IntermediateField
open scoped TensorProduct

private theorem localizationEq_of_isLocalization_away
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (f : R) [IsLocalization.Away f T]
    (hinj : Function.Injective (algebraMap S T)) : LocalizationEq R S f := by
  intro x
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f (algebraMap S T x)
  refine ⟨n, r, hinj ?_⟩
  rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, mul_comm]
  exact hr

theorem isLocalization_away_of_localizationEq
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (f : R) [IsLocalization.Away (algebraMap R S f) T]
    (hinj : Function.Injective (algebraMap R S)) (hloc : LocalizationEq R S f) :
    IsLocalization.Away f T := by
  have hf : IsUnit (algebraMap R T f) := by
    rw [IsScalarTower.algebraMap_apply R S T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R S f) (S := T)
  apply IsLocalization.Away.mk f hf
  · intro x
    obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (algebraMap R S f) x
    obtain ⟨m, r, hr⟩ := hloc s
    refine ⟨n + m, r, ?_⟩
    rw [pow_add, ← mul_assoc, IsScalarTower.algebraMap_apply R S T, hs]
    rw [← map_pow, ← map_mul, mul_comm s, hr, ← IsScalarTower.algebraMap_apply]
  · intro x y hxy
    rw [IsScalarTower.algebraMap_apply R S T,
      IsScalarTower.algebraMap_apply R S T] at hxy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R S f)) T).mp hxy
    refine ⟨n, hinj ?_⟩
    simpa only [map_mul, map_pow] using hn

/-- If `AdjoinRoot P → S` is compatible with the structure maps from `B`, finiteness of `S`
over `B` gives finiteness of `S` over `AdjoinRoot P`. -/
private theorem finite_adjoinRoot_of_comp_eq
    {B R S : Type*} [CommRing B] [CommRing R] [CommRing S] [Algebra B R] [Algebra B S]
    [Module.Finite B S] {P : R[X]} (h : AdjoinRoot P →+* S)
    (hc : ∀ r, h (AdjoinRoot.of P (algebraMap B R r)) = algebraMap B S r) :
    letI := h.toAlgebra
    Module.Finite (AdjoinRoot P) S := by
  let := h.toAlgebra
  have : IsScalarTower B (AdjoinRoot P) S := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Module.Finite.of_restrictScalars_finite B (AdjoinRoot P) S

private theorem adjoinRoot_algHom_injective_of_minpoly_eq_map
    {R F E : Type*} [CommRing R] [Field F] [CommRing E]
    [Algebra R F] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    {p : R[X]} (hp : p.Monic) (hi : Function.Injective (algebraMap R F))
    (φ : AdjoinRoot p →ₐ[R] E)
    (hmin : minpoly F (φ (AdjoinRoot.root p)) = p.map (algebraMap R F)) :
    Function.Injective φ := by
  apply (injective_iff_map_eq_zero φ).mpr
  intro x hx
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  apply AdjoinRoot.mk_eq_zero.mpr
  apply (Polynomial.map_dvd_map (algebraMap R F) hi hp).mp
  rw [← hmin]
  apply minpoly.dvd F
  simpa only [aeval_map_algebraMap, aeval_algHom_apply, AdjoinRoot.aeval_eq] using hx

theorem exists_injective_finite_adjoinRoot_integralClosure
    (A K K₁ K₂ A₁ A₂ : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field K₁] [Field K₂] [CommRing A₁] [CommRing A₂]
    [Algebra A K] [Algebra K K₁] [Algebra K₁ K₂] [Algebra K K₂]
    [Algebra A K₁] [Algebra A K₂]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [IsScalarTower K K₁ K₂] [IsScalarTower A K₁ K₂] [IsFractionRing A K]
    [Module.Finite K K₁] [Module.Finite K₁ K₂]
    [Algebra A A₁] [Algebra A₁ K₁] [IsScalarTower A A₁ K₁] [IsIntegralClosure A₁ A K₁]
    [Algebra A A₂] [Algebra A₂ K₂] [IsScalarTower A A₂ K₂] [IsIntegralClosure A₂ A K₂]
    [Module.Finite A A₂]
    (p : ℕ) (hp : p.Prime) [CharP K p] [IsPurelyInseparable K₁ K₂]
    (hdegree : Module.finrank K₁ K₂ = p) :
    ∃ (c : A₁) (a₁₂ : A₁ →ₐ[A] A₂) (a₂ : AdjoinRoot (X ^ p - C c) →+* A₂),
      (∀ x, algebraMap A₂ K₂ (a₁₂ x) = algebraMap K₁ K₂ (algebraMap A₁ K₁ x)) ∧
      a₂.comp (AdjoinRoot.of _) = a₁₂.toRingHom ∧ Function.Injective a₂ ∧
      minpoly K₁ (algebraMap A₂ K₂ (a₂ (AdjoinRoot.root _))) =
        X ^ p - C (algebraMap A₁ K₁ c) ∧
      K₁⟮algebraMap A₂ K₂ (a₂ (AdjoinRoot.root _))⟯ = ⊤ ∧
      (letI := a₂.toAlgebra; Module.Finite (AdjoinRoot (X ^ p - C c)) A₂) := by
  have : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
  have : CharP K₁ p := charP_of_injective_algebraMap (algebraMap K K₁).injective p
  obtain ⟨α, a, hgen, hminpoly⟩ :=
    exists_minpoly_eq_X_pow_sub_C_of_finrank_eq_prime K₁ K₂ p hp hdegree
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have : IsLocalization.Away π K := isLocalization_away_of_isFractionRing A K hπ
  obtain ⟨n, hβint⟩ := exists_pow_smul_isIntegral (F := K) π
    (IsIntegral.of_finite K α)
  let β : K₂ := π ^ n • α
  have hπ₁ : algebraMap A K₁ π ≠ 0 := by
    intro hz
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    apply (algebraMap K K₁).injective
    simpa only [map_zero, ← IsScalarTower.algebraMap_apply] using hz
  have hβeq : β = α * algebraMap K₁ K₂ ((algebraMap A K₁ π) ^ n) := by
    simp only [β, Algebra.smul_def, ← map_pow, ← IsScalarTower.algebraMap_apply]
    ring
  have hβgen : K₁⟮β⟯ = ⊤ := by
    rw [hβeq, adjoin_simple_mul_algebraMap α _ (pow_ne_zero n hπ₁)]
    exact hgen
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a₁, hβminpoly⟩ := minpoly_eq_X_pow_sub_C_of_adjoin_eq_top
    K₁ K₂ p hdegree β hβgen
  have ha₁ : IsIntegral A a₁ :=
    isIntegral_of_minpoly_eq_X_pow_sub_C p hβint hβminpoly
  let c₁ : A₁ := IsIntegralClosure.mk' A₁ a₁ ha₁
  let β₂ : A₂ := IsIntegralClosure.mk' A₂ β hβint
  have hc₁ : algebraMap A₁ K₁ c₁ = a₁ :=
    IsIntegralClosure.algebraMap_mk' A₁ a₁ ha₁
  have hβ₂ : algebraMap A₂ K₂ β₂ = β :=
    IsIntegralClosure.algebraMap_mk' A₂ β hβint
  let eA₁ := IsIntegralClosure.equiv A A₁ K₁ (integralClosure A K₁)
  let eA₂ := IsIntegralClosure.equiv A A₂ K₂ (integralClosure A K₂)
  let a₁₂ : A₁ →ₐ[A] A₂ := eA₂.symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom A K₁ K₂).mapIntegralClosure.comp eA₁.toAlgHom)
  have ha₁₂ (x : A₁) :
      algebraMap A₂ K₂ (a₁₂ x) = algebraMap K₁ K₂ (algebraMap A₁ K₁ x) := by
    have he₂ := IsIntegralClosure.algebraMap_equiv A A₂ K₂ (integralClosure A K₂) (a₁₂ x)
    rw [← he₂]
    change (eA₂ (eA₂.symm ((IsScalarTower.toAlgHom A K₁ K₂).mapIntegralClosure (eA₁ x))) : K₂) = _
    rw [eA₂.apply_symm_apply, AlgHom.coe_mapIntegralClosure]
    exact congrArg (algebraMap K₁ K₂)
      (IsIntegralClosure.algebraMap_equiv A A₁ K₁ (integralClosure A K₁) x)
  have hβpow : β ^ p = algebraMap K₁ K₂ a₁ := by
    have h := minpoly.aeval K₁ β
    rw [hβminpoly] at h
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h
  have hβ₂pow : β₂ ^ p = a₁₂ c₁ := by
    apply IsIntegralClosure.algebraMap_injective A₂ A K₂
    rw [map_pow, hβ₂, ha₁₂, hc₁, hβpow]
  let P₂ : A₁[X] := X ^ p - C c₁
  let a₂ : AdjoinRoot P₂ →+* A₂ :=
    AdjoinRoot.lift a₁₂.toRingHom β₂ (by
      simp only [P₂, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
      change β₂ ^ p = a₁₂ c₁
      exact hβ₂pow)
  let : Algebra A₁ K₂ := ((algebraMap K₁ K₂).comp (algebraMap A₁ K₁)).toAlgebra
  have : IsScalarTower A₁ K₁ K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ : AdjoinRoot P₂ →ₐ[A₁] K₂ :=
    { __ := (algebraMap A₂ K₂).comp a₂
      commutes' := fun r => by
        change algebraMap A₂ K₂ (a₂ (AdjoinRoot.of P₂ r)) = _
        rw [AdjoinRoot.lift_of]
        exact ha₁₂ r }
  have hroot : algebraMap A₂ K₂ (a₂ (AdjoinRoot.root P₂)) = β := by
    rw [AdjoinRoot.lift_root, hβ₂]
  have hP₂ : P₂.Monic := by
    simpa only [P₂, map_zero, zero_mul, sub_zero] using
      monic_X_pow_sub_C_mul_X_sub_C p hp.one_lt c₁ 0
  have hiφ : Function.Injective φ :=
    adjoinRoot_algHom_injective_of_minpoly_eq_map hP₂
      (IsIntegralClosure.algebraMap_injective A₁ A K₁) φ (by
        change minpoly K₁ (algebraMap A₂ K₂ (a₂ (AdjoinRoot.root P₂))) = _
        rw [hroot, hβminpoly]
        simp only [P₂, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C, hc₁])
  refine ⟨c₁, a₁₂, a₂, ha₁₂, ?_, Function.Injective.of_comp hiφ, ?_, ?_,
    finite_adjoinRoot_of_comp_eq (B := A) a₂ fun r => ?_⟩
  · ext x
    change a₂ (AdjoinRoot.of P₂ x) = a₁₂ x
    exact AdjoinRoot.lift_of _
  · rw [hroot, hβminpoly, hc₁]
  · rw [hroot]
    exact hβgen
  · rw [AdjoinRoot.lift_of]
    exact a₁₂.commutes r

private theorem adjoinRoot_map_injective_of_monic
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    {P : R[X]} (hP : P.Monic) :
    Function.Injective (AdjoinRoot.map f P (P.map f) dvd_rfl) := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    intro x y _
    have : Subsingleton (AdjoinRoot P) := AdjoinRoot.mk_surjective.subsingleton
    exact Subsingleton.elim x y
  | inr h =>
  have : Nontrivial S := ⟨⟨0, 1, fun h => zero_ne_one (hf (by simpa using h))⟩⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  have hmk : AdjoinRoot.mk P q = AdjoinRoot.mk P (q %ₘ P) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨q /ₘ P, by rw [sub_eq_iff_eq_add, add_comm, modByMonic_add_div q P]⟩
  rw [hmk] at hx ⊢
  have hmap : AdjoinRoot.map f P (P.map f) dvd_rfl (AdjoinRoot.mk P (q %ₘ P)) =
      AdjoinRoot.mk (P.map f) ((q %ₘ P).map f) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def,
      ← eval₂_map, eval₂_map, AdjoinRoot.algebraMap_eq, eval₂_map]
  rw [hmap, AdjoinRoot.mk_eq_zero] at hx
  have hPm : (P.map f).Monic := hP.map f
  have hdeg : ((q %ₘ P).map f).degree < (P.map f).degree := by
    rw [degree_map_eq_of_injective hf, degree_map_eq_of_injective hf]
    exact degree_modByMonic_lt q hP
  have h0 : (q %ₘ P).map f = 0 := by
    rw [← (modByMonic_eq_self_iff hPm).mpr hdeg]
    exact (modByMonic_eq_zero_iff_dvd hPm).mpr hx
  have : q %ₘ P = 0 := by
    simpa using (Polynomial.map_injective f hf) (h0.trans (Polynomial.map_zero f).symm)
  rw [this, map_zero]

private noncomputable def adjoinRootAlgEquivOfAdjoinEqTop
    (F E : Type*) [Field F] [Field E] [Algebra F E] {β : E} (hβ : IsIntegral F β)
    (hgen : F⟮β⟯ = ⊤) : AdjoinRoot (minpoly F β) ≃ₐ[F] E :=
  (adjoinRootEquivAdjoin F hβ).trans ((equivOfEq hgen).trans topEquiv)

private theorem adjoinRootAlgEquivOfAdjoinEqTop_root
    (F E : Type*) [Field F] [Field E] [Algebra F E] {β : E} (hβ : IsIntegral F β)
    (hgen : F⟮β⟯ = ⊤) :
    adjoinRootAlgEquivOfAdjoinEqTop F E hβ hgen (AdjoinRoot.root _) = β := by
  simp [adjoinRootAlgEquivOfAdjoinEqTop, adjoinRootEquivAdjoin_apply_root]

private noncomputable def tensorAdjoinRootAlgEquiv
    (K L F E : Type*) [Field K] [CommRing L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {β : E} (hβ : IsIntegral F β) (hgen : F⟮β⟯ = ⊤) :
    AdjoinRoot ((minpoly F β).map
        (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom) ≃ₐ[L] L ⊗[K] E :=
  (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) (minpoly F β) _ rfl).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl
      ((adjoinRootAlgEquivOfAdjoinEqTop F E hβ hgen).restrictScalars K))

private theorem tensorAdjoinRootAlgEquiv_root
    (K L F E : Type*) [Field K] [CommRing L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {β : E} (hβ : IsIntegral F β) (hgen : F⟮β⟯ = ⊤) :
    tensorAdjoinRootAlgEquiv K L F E hβ hgen (AdjoinRoot.root _) = 1 ⊗ₜ β := by
  rw [tensorAdjoinRootAlgEquiv, AlgEquiv.trans_apply,
    show (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) (minpoly F β) _ rfl).symm
      (AdjoinRoot.root _) = 1 ⊗ₜ AdjoinRoot.root _ from by
        rw [AlgEquiv.symm_apply_eq, AdjoinRoot.tensorAlgEquiv_root]]
  simp [adjoinRootAlgEquivOfAdjoinEqTop_root]

private theorem tensorAdjoinRootAlgEquiv_of
    (K L F E : Type*) [Field K] [CommRing L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {β : E} (hβ : IsIntegral F β) (hgen : F⟮β⟯ = ⊤) (x : L ⊗[K] F) :
    tensorAdjoinRootAlgEquiv K L F E hβ hgen (AdjoinRoot.of _ x) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) x := by
  let φ₁ : L ⊗[K] F →ₐ[L] L ⊗[K] E :=
    (tensorAdjoinRootAlgEquiv K L F E hβ hgen).toAlgHom.comp
      (IsScalarTower.toAlgHom L (L ⊗[K] F) (AdjoinRoot ((minpoly F β).map
        (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)))
  let φ₂ : L ⊗[K] F →ₐ[L] L ⊗[K] E :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K F E)
  have : φ₁ = φ₂ := by
    apply Algebra.TensorProduct.ext (AlgHom.ext fun l => by
      simp only [φ₁, φ₂, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      rw [← mul_one l, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul,
        Algebra.TensorProduct.one_def.symm, map_one, map_one]
      rfl)
    apply AlgHom.ext
    intro f
    have h : (algebraMap (L ⊗[K] F) (AdjoinRoot ((minpoly F β).map
        (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom))) (1 ⊗ₜ f) =
        AdjoinRoot.tensorAlgEquiv (R := K) (T := L) (minpoly F β) _ rfl
          (1 ⊗ₜ AdjoinRoot.of _ f) := by
      rw [AdjoinRoot.tensorAlgEquiv_of]; rfl
    simp only [φ₁, φ₂, AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeRight_apply, h, AlgEquiv.coe_toAlgHom]
    rw [tensorAdjoinRootAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    simp only [adjoinRootAlgEquivOfAdjoinEqTop, Algebra.TensorProduct.congr_apply,
      AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [← AdjoinRoot.algebraMap_eq]
    congr 1
    exact ((adjoinRootEquivAdjoin F hβ).trans ((equivOfEq hgen).trans topEquiv)).commutes f
  exact DFunLike.congr_fun this x

private theorem adjoinRoot_lift_injective_of_tensor_comparison
    {R S K L F E : Type*} [CommRing R] [CommRing S]
    [Field K] [CommRing L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E] {β : E} (hβ : IsIntegral F β)
    (hgen : F⟮β⟯ = ⊤) (i : R →+* L ⊗[K] F)
    (hi : Function.Injective i) (P : R[X]) (hP : P.Monic)
    (hPmap : P.map i = (minpoly F β).map
      (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
    (h : AdjoinRoot P →+* S) (j : S →+* L ⊗[K] E)
    (hc : ∀ r, j (h (AdjoinRoot.of P r)) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) (i r))
    (hr : j (h (AdjoinRoot.root P)) = 1 ⊗ₜ β) : Function.Injective h := by
  let Q := (minpoly F β).map
    (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom
  let m : AdjoinRoot P →+* AdjoinRoot Q := AdjoinRoot.map i P Q
    (by rw [hPmap])
  have hm : Function.Injective m := by
    have aux (Q' : (L ⊗[K] F)[X]) (he : P.map i = Q') :
        Function.Injective (AdjoinRoot.map i P Q' (he ▸ dvd_rfl)) := by
      subst Q'
      exact adjoinRoot_map_injective_of_monic i hi hP
    exact aux Q hPmap
  let e := tensorAdjoinRootAlgEquiv K L F E hβ hgen
  have heq : j.comp h = e.toRingHom.comp m := by
    apply AdjoinRoot.ringHom_ext
    · ext r
      change j (h (AdjoinRoot.of P r)) = e (m (AdjoinRoot.of P r))
      rw [AdjoinRoot.map_of, tensorAdjoinRootAlgEquiv_of]
      exact hc r
    · change j (h (AdjoinRoot.root P)) = e (m (AdjoinRoot.root P))
      rw [AdjoinRoot.map_root, tensorAdjoinRootAlgEquiv_root]
      exact hr
  exact Function.Injective.of_comp (show Function.Injective (j.comp h) from
    heq ▸ e.injective.comp hm)

theorem integralClosureBaseChange_finite_right
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hB : IsNagataRing B) :
    let := D.commRingB₁
    let := D.algebraBB₁
    Module.Finite B D.B₁ := by
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let eA := IsIntegralClosure.equiv A D.A₁ F (integralClosure A F)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  have heA (x : D.A₁) : (eA x : F) = algebraMap D.A₁ F x :=
    IsIntegralClosure.algebraMap_equiv A D.A₁ F (integralClosure A F) x
  have heB (x : D.B₁) : (eB x : D.L₁) = algebraMap D.B₁ D.L₁ x :=
    IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x
  have h := integralClosures_after_finite_fraction_field_extension
    A B K L F D.L₁ D.A₁ D.B₁ D.eL₁ eA eB D.eL₁_left D.eL₁_right heB
    (fun x => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    (fun x => by rw [heA]; exact D.ringSquare x)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfinB⟩ := h
  exact hfinB hB

private theorem exists_injective_finite_adjoinRoot_map_integralClosure
    (B K L F E : Type*) [CommRing B] [Field K] [CommRing L] [Field F] [Field E]
    [Algebra B L] [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [Module.Finite B (integralClosure B (L ⊗[K] E))]
    {β : E} (hβ : IsIntegral F β) (hgen : F⟮β⟯ = ⊤)
    (P : (integralClosure B (L ⊗[K] F))[X]) (hP : P.Monic)
    (hPmap : P.map (integralClosure B (L ⊗[K] F)).val.toRingHom =
      (minpoly F β).map
        (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
    (hβB : IsIntegral B (1 ⊗ₜ[K] β : L ⊗[K] E)) :
    ∃ h : AdjoinRoot P →+* integralClosure B (L ⊗[K] E),
      (∀ r, (h (AdjoinRoot.of P r) : L ⊗[K] E) =
        Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) r) ∧
      (h (AdjoinRoot.root P) : L ⊗[K] E) = 1 ⊗ₜ[K] β ∧ Function.Injective h ∧
      (letI := h.toAlgebra; Module.Finite (AdjoinRoot P) (integralClosure B (L ⊗[K] E))) := by
  let ψ : L ⊗[K] F →ₐ[B] L ⊗[K] E :=
    (Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K F E)).restrictScalars B
  let φ := ψ.mapIntegralClosure
  let βB : integralClosure B (L ⊗[K] E) := ⟨1 ⊗ₜ[K] β, hβB⟩
  let e := tensorAdjoinRootAlgEquiv K L F E hβ hgen
  have hzero : eval₂ φ.toRingHom βB P = 0 := by
    apply Subtype.ext
    change (integralClosure B (L ⊗[K] E)).val.toRingHom (eval₂ φ.toRingHom βB P) = 0
    rw [hom_eval₂]
    change eval₂ ((ψ.toRingHom).comp (integralClosure B (L ⊗[K] F)).val.toRingHom)
      (1 ⊗ₜ[K] β) P = 0
    rw [← eval₂_map, hPmap]
    rw [← tensorAdjoinRootAlgEquiv_root K L F E hβ hgen]
    have hcoeff : ψ.toRingHom = e.toRingHom.comp (AdjoinRoot.of _) := by
      apply RingHom.ext
      intro x
      exact (tensorAdjoinRootAlgEquiv_of K L F E hβ hgen x).symm
    rw [hcoeff]
    change eval₂ (e.toRingHom.comp (AdjoinRoot.of _))
      (e.toRingHom (AdjoinRoot.root _)) _ = 0
    rw [← hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  let h := AdjoinRoot.lift φ.toRingHom βB hzero
  have hc (r) : (h (AdjoinRoot.of P r) : L ⊗[K] E) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) r := by
    rw [AdjoinRoot.lift_of]
    rfl
  have hr : (h (AdjoinRoot.root P) : L ⊗[K] E) = 1 ⊗ₜ[K] β := by
    rw [AdjoinRoot.lift_root]
  have hi : Function.Injective h := adjoinRoot_lift_injective_of_tensor_comparison
    hβ hgen (integralClosure B (L ⊗[K] F)).val.toRingHom Subtype.val_injective P hP hPmap
    h (integralClosure B (L ⊗[K] E)).val.toRingHom hc hr
  exact ⟨h, hc, hr, hi, finite_adjoinRoot_of_comp_eq h fun b => by
    rw [AdjoinRoot.lift_of]
    exact φ.commutes b⟩

noncomputable def integralClosureBaseChangeTensorEquiv
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hred : IsReduced (L ⊗[K] F)) :
    let := D.commRingL₁
    let := D.algebraLL₁
    D.L₁ ≃ₐ[L] L ⊗[K] F := by
  let := D.commRingL₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.isScalarTowerKLL₁
  let q : ((L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)) ≃ₐ[K] L ⊗[K] F :=
    (Ideal.quotientEquivAlgOfEq K (nilradical_eq_zero _)).trans (AlgEquiv.quotientBot K _)
  let e := D.eL₁.trans q
  exact { __ := e.toRingEquiv
          commutes' := fun l => by
            change q (D.eL₁ (algebraMap L D.L₁ l)) = algebraMap L (L ⊗[K] F) l
            rw [D.eL₁_left]
            simp only [q, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
              AlgEquiv.quotientBot_mk]
            rfl }

theorem integralClosureBaseChangeTensorEquiv_right
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hred : IsReduced (L ⊗[K] F)) (x : F) :
    let := D.commRingL₁
    let := D.algebraLL₁
    let := D.algebraK₁L₁
    integralClosureBaseChangeTensorEquiv A B K L F D hred (algebraMap F D.L₁ x) =
      (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F) x := by
  let := D.commRingL₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  change (AlgEquiv.quotientBot K _) ((Ideal.quotientEquivAlgOfEq K (nilradical_eq_zero _))
    (D.eL₁ (algebraMap F D.L₁ x))) = _
  rw [D.eL₁_right, Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]

noncomputable def integralClosureBaseChangeRightEquiv
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hred : IsReduced (L ⊗[K] F)) :
    let := D.commRingB₁
    let := D.algebraBB₁
    D.B₁ ≃ₐ[B] integralClosure B (L ⊗[K] F) := by
  let := D.commRingL₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraBL₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerBB₁L₁
  let := D.isIntegralClosureB₁
  exact (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)).trans
    ((integralClosureBaseChangeTensorEquiv A B K L F D hred).restrictScalars B).mapIntegralClosure

theorem integralClosureBaseChangeRightEquiv_apply
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hred : IsReduced (L ⊗[K] F)) (x : D.B₁) :
    let := D.commRingL₁
    let := D.commRingB₁
    let := D.algebraLL₁
    let := D.algebraBB₁
    let := D.algebraB₁L₁
    (integralClosureBaseChangeRightEquiv A B K L F D hred x : L ⊗[K] F) =
      integralClosureBaseChangeTensorEquiv A B K L F D hred (algebraMap D.B₁ D.L₁ x) := by
  let := D.commRingL₁
  let := D.commRingB₁
  let := D.algebraBL₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.isScalarTowerBB₁L₁
  let := D.isIntegralClosureB₁
  change integralClosureBaseChangeTensorEquiv A B K L F D hred
    ((IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x : integralClosure B D.L₁) :
      D.L₁) = _
  exact congrArg (integralClosureBaseChangeTensorEquiv A B K L F D hred)
    (IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x)

theorem isLocalization_away_adjoinRoot_map
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (π : R) [IsLocalization.Away π S] (P : R[X]) :
    letI := (AdjoinRoot.map (algebraMap R S) P (P.map (algebraMap R S)) dvd_rfl).toAlgebra
    IsLocalization.Away (AdjoinRoot.of P π) (AdjoinRoot (P.map (algebraMap R S))) := by
  let Q := P.map (algebraMap R S)
  let f := AdjoinRoot.map (algebraMap R S) P Q dvd_rfl
  let := f.toAlgebra
  let : Algebra (AdjoinRoot P) (S ⊗[R] AdjoinRoot P) := Algebra.TensorProduct.rightAlgebra
  let e₀ := AdjoinRoot.tensorAlgEquiv (R := R) (T := S) P _ rfl
  let r : (S ⊗[R] R) ≃ₐ[S] S := Algebra.TensorProduct.rid R S S
  have hmap : (P.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom).map
      r.toRingHom = Q := by
    rw [Polynomial.map_map]
    congr 1
    apply RingHom.ext
    intro x
    simp [r, Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]
  let e₁ := AdjoinRoot.mapAlgEquiv r
    (P.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom) Q
    (by
      change Associated ((P.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R]
        R).toRingHom).map r.toRingHom) Q
      rw [hmap])
  let e := e₀.trans e₁
  have heof (x : R) : e (1 ⊗ₜ[R] AdjoinRoot.of P x) = AdjoinRoot.of Q (algebraMap R S x) := by
    change e₁ (e₀ (1 ⊗ₜ[R] AdjoinRoot.of P x)) = _
    rw [AdjoinRoot.tensorAlgEquiv_of]
    change AdjoinRoot.map r.toRingHom _ Q hmap.symm.dvd (AdjoinRoot.of _ (1 ⊗ₜ[R] x)) = _
    rw [AdjoinRoot.map_of]
    congr 1
    simp [r, Algebra.smul_def]
  have heroot : e (1 ⊗ₜ[R] AdjoinRoot.root P) = AdjoinRoot.root Q := by
    change e₁ (e₀ (1 ⊗ₜ[R] AdjoinRoot.root P)) = _
    rw [AdjoinRoot.tensorAlgEquiv_root]
    exact AdjoinRoot.map_root r.toRingHom _ Q hmap.symm.dvd
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : AdjoinRoot P →ₐ[R] S ⊗[R] AdjoinRoot P).toRingHom = f :=
        by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro x
      change e (1 ⊗ₜ[R] AdjoinRoot.of P x) = f (AdjoinRoot.of P x)
      rw [heof, AdjoinRoot.map_of]
    · change e (1 ⊗ₜ[R] AdjoinRoot.root P) = f (AdjoinRoot.root P)
      rw [heroot, AdjoinRoot.map_root]
  let e' : S ⊗[R] AdjoinRoot P ≃ₐ[AdjoinRoot P] AdjoinRoot Q :=
    { __ := e.toRingEquiv
      commutes' := fun x => DFunLike.congr_fun he x }
  have : IsLocalization.Away (AdjoinRoot.of P π) (S ⊗[R] AdjoinRoot P) :=
    IsLocalization.Away.tensorRight π S
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (AdjoinRoot.of P π)) e'

theorem isLocalization_away_of_adjoinRoot_equiv
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (π : R) [IsLocalization.Away π S] (P : R[X])
    (φ : AdjoinRoot P →ₐ[R] T)
    (e : AdjoinRoot (P.map (algebraMap R S)) ≃ₐ[S] T)
    (he : e (AdjoinRoot.root _) = φ (AdjoinRoot.root P)) :
    letI := φ.toRingHom.toAlgebra
    IsLocalization.Away (AdjoinRoot.of P π) T := by
  let m := AdjoinRoot.map (algebraMap R S) P (P.map (algebraMap R S)) dvd_rfl
  let := m.toAlgebra
  let := φ.toRingHom.toAlgebra
  have hcomp : e.toRingHom.comp m = φ.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      change e (m (AdjoinRoot.of P r)) = φ (AdjoinRoot.of P r)
      rw [AdjoinRoot.map_of]
      change e (algebraMap S _ (algebraMap R S r)) = φ (algebraMap R _ r)
      rw [e.commutes, φ.commutes, ← IsScalarTower.algebraMap_apply]
    · change e (m (AdjoinRoot.root P)) = φ (AdjoinRoot.root P)
      rw [AdjoinRoot.map_root]
      exact he
  let e' : AdjoinRoot (P.map (algebraMap R S)) ≃ₐ[AdjoinRoot P] T :=
    { __ := e.toRingEquiv
      commutes' := fun x => DFunLike.congr_fun hcomp x }
  have : IsLocalization.Away (AdjoinRoot.of P π) (AdjoinRoot (P.map (algebraMap R S))) :=
    isLocalization_away_adjoinRoot_map R S π P
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (AdjoinRoot.of P π)) e'

theorem localizationEq_of_adjoinRoot_minpoly
    (R F E C : Type*) [CommRing R] [Field F] [Field E] [CommRing C]
    [Algebra R F] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    [Algebra R C] [Algebra C E] [IsScalarTower R C E]
    (π : R) [IsLocalization.Away π F] (P : R[X])
    (f : AdjoinRoot P →ₐ[R] C) (hi : Function.Injective (algebraMap C E))
    (hβ : IsIntegral F (algebraMap C E (f (AdjoinRoot.root P))))
    (hgen : F⟮algebraMap C E (f (AdjoinRoot.root P))⟯ = ⊤)
    (hmin : minpoly F (algebraMap C E (f (AdjoinRoot.root P))) =
      P.map (algebraMap R F)) :
    letI := f.toRingHom.toAlgebra
    LocalizationEq (AdjoinRoot P) C (AdjoinRoot.of P π) := by
  let φ := (IsScalarTower.toAlgHom R C E).comp f
  let e₀ := adjoinRootAlgEquivOfAdjoinEqTop F E hβ hgen
  let e : AdjoinRoot (P.map (algebraMap R F)) ≃ₐ[F] E :=
    (Ideal.quotientEquivAlgOfEq F (congrArg (fun p : F[X] => Ideal.span {p}) hmin.symm)).trans e₀
  have he : e (AdjoinRoot.root _) = φ (AdjoinRoot.root P) := by
    change e₀ ((Ideal.quotientEquivAlgOfEq F
      (congrArg (fun p : F[X] => Ideal.span {p}) hmin.symm)) (Ideal.Quotient.mk _ X)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact adjoinRootAlgEquivOfAdjoinEqTop_root F E hβ hgen
  let := f.toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower (AdjoinRoot P) C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization.Away (AdjoinRoot.of P π) E :=
    isLocalization_away_of_adjoinRoot_equiv R F E π P φ e he
  exact localizationEq_of_isLocalization_away (AdjoinRoot P) C E (AdjoinRoot.of P π) hi

private theorem localizationEq_of_tensor_adjoinRoot_comparison
    {R S K L F E : Type*} [CommRing R] [CommRing S]
    [Field K] [CommRing L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E] {β : E} (hβ : IsIntegral F β)
    (hgen : F⟮β⟯ = ⊤) (i : R →+* L ⊗[K] F)
    (P : R[X])
    (hPmap : P.map i = (minpoly F β).map
      (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
    (h : AdjoinRoot P →+* S) (j : S →+* L ⊗[K] E) (hj : Function.Injective j)
    (hc : ∀ r, j (h (AdjoinRoot.of P r)) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) (i r))
    (hr : j (h (AdjoinRoot.root P)) = 1 ⊗ₜ β)
    (r : R) (hloc : letI := i.toAlgebra; IsLocalization.Away r (L ⊗[K] F)) :
    letI := h.toAlgebra
    LocalizationEq (AdjoinRoot P) S (AdjoinRoot.of P r) := by
  let ψ : L ⊗[K] F →ₐ[L] L ⊗[K] E :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K F E)
  let := i.toAlgebra
  let : Algebra R S := (h.comp (AdjoinRoot.of P)).toAlgebra
  let := j.toAlgebra
  let : Algebra R (L ⊗[K] E) := (j.comp (h.comp (AdjoinRoot.of P))).toAlgebra
  let := ψ.toRingHom.toAlgebra
  have : IsScalarTower R S (L ⊗[K] E) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (L ⊗[K] F) (L ⊗[K] E) := IsScalarTower.of_algebraMap_eq hc
  have : IsLocalization.Away r (L ⊗[K] F) := hloc
  let f : AdjoinRoot P →ₐ[R] L ⊗[K] E :=
    { __ := j.comp h
      commutes' := fun _ => rfl }
  let e₀ : AdjoinRoot ((minpoly F β).map
      (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom) ≃ₐ[L ⊗[K] F] L ⊗[K] E :=
    { __ := (tensorAdjoinRootAlgEquiv K L F E hβ hgen).toRingEquiv
      commutes' := fun x => tensorAdjoinRootAlgEquiv_of K L F E hβ hgen x }
  let e : AdjoinRoot (P.map i) ≃ₐ[L ⊗[K] F] L ⊗[K] E :=
    (Ideal.quotientEquivAlgOfEq (L ⊗[K] F)
      (congrArg (fun p : (L ⊗[K] F)[X] => Ideal.span {p}) hPmap)).trans e₀
  have he : e (AdjoinRoot.root _) = f (AdjoinRoot.root P) := by
    change e₀ ((Ideal.quotientEquivAlgOfEq (L ⊗[K] F)
      (congrArg (fun p : (L ⊗[K] F)[X] => Ideal.span {p}) hPmap)) (Ideal.Quotient.mk _ X)) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact (tensorAdjoinRootAlgEquiv_root K L F E hβ hgen).trans hr.symm
  let := h.toAlgebra
  let := f.toRingHom.toAlgebra
  have : IsScalarTower (AdjoinRoot P) S (L ⊗[K] E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization.Away (AdjoinRoot.of P r) (L ⊗[K] E) :=
    isLocalization_away_of_adjoinRoot_equiv R (L ⊗[K] F) (L ⊗[K] E) r P f e he
  exact localizationEq_of_isLocalization_away (AdjoinRoot P) S (L ⊗[K] E)
    (AdjoinRoot.of P r) hj

theorem isLocalization_away_of_integralClosure_equiv
    (A F T R : Type*) [CommRing A] [CommRing F] [CommRing T] [CommRing R]
    [Algebra A F] [Algebra A T] [Algebra F T] [IsScalarTower A F T]
    [Algebra A R] [Algebra.IsIntegral F T]
    (e : R ≃ₐ[A] integralClosure A T) (r : A) [IsLocalization.Away r F] :
    letI := ((integralClosure A T).val.toRingHom.comp e.toRingHom).toAlgebra
    IsLocalization.Away (algebraMap A R r) T := by
  let := ((integralClosure A T).val.toRingHom.comp e.toRingHom).toAlgebra
  have : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A T a = (e (algebraMap A R a) : T)
    rw [e.commutes]
    rfl
  have : IsIntegralClosure R A T :=
    { algebraMap_injective := Subtype.val_injective.comp e.injective
      isIntegral_iff := fun {x} => by
        constructor
        · intro hx
          exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
        · rintro ⟨y, rfl⟩
          exact (e y).property }
  exact isLocalization_away_of_isIntegralClosure A F T R r

private theorem localizationEq_of_tensor_adjoinRoot_integralClosure_equiv
    {B K L F E R S : Type*} [CommRing B] [Field K] [CommRing L] [Field F] [Field E]
    [CommRing R] [CommRing S] [Algebra B R] [Algebra B S]
    [Algebra B L] [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E] [Module.Finite K F]
    (eR : R ≃ₐ[B] integralClosure B (L ⊗[K] F))
    (eS : S ≃ₐ[B] integralClosure B (L ⊗[K] E))
    {β : E} (hβ : IsIntegral F β) (hgen : F⟮β⟯ = ⊤) (P : R[X])
    (hPmap : P.map ((integralClosure B (L ⊗[K] F)).val.toRingHom.comp eR.toRingHom) =
      (minpoly F β).map
        (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
    (h : AdjoinRoot P →+* S)
    (hc : ∀ x, (eS (h (AdjoinRoot.of P x)) : L ⊗[K] E) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) (eR x))
    (hr : (eS (h (AdjoinRoot.root P)) : L ⊗[K] E) = 1 ⊗ₜ[K] β)
    (r : B) [IsLocalization.Away r L] :
    letI := h.toAlgebra
    LocalizationEq (AdjoinRoot P) S (AdjoinRoot.of P (algebraMap B R r)) :=
  localizationEq_of_tensor_adjoinRoot_comparison hβ hgen
    ((integralClosure B (L ⊗[K] F)).val.toRingHom.comp eR.toRingHom) P hPmap h
    ((integralClosure B (L ⊗[K] E)).val.toRingHom.comp eS.toRingHom)
    (Subtype.val_injective.comp eS.injective) hc hr (algebraMap B R r)
    (isLocalization_away_of_integralClosure_equiv B L (L ⊗[K] F) R eR r)

theorem exists_injective_finite_adjoinRoot_of_integralClosure_equiv
    (B K L F E R S : Type*) [CommRing B] [Field K] [CommRing L] [Field F] [Field E]
    [CommRing R] [CommRing S] [Algebra B R] [Algebra B S]
    [Algebra B L] [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E] [Module.Finite K F] [Module.Finite B S]
    (eR : R ≃ₐ[B] integralClosure B (L ⊗[K] F))
    (eS : S ≃ₐ[B] integralClosure B (L ⊗[K] E))
    {β : E} (hβ : IsIntegral F β) (hgen : F⟮β⟯ = ⊤)
    (P : R[X]) (hP : P.Monic)
    (hPmap : P.map ((integralClosure B (L ⊗[K] F)).val.toRingHom.comp eR.toRingHom) =
      (minpoly F β).map
        (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).toRingHom)
    (hβB : IsIntegral B (1 ⊗ₜ[K] β : L ⊗[K] E)) :
    ∃ (b : R →ₐ[B] S) (h : AdjoinRoot P →+* S),
      h.comp (AdjoinRoot.of P) = b.toRingHom ∧
      (∀ r, (eS (b r) : L ⊗[K] E) =
        Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) (eR r)) ∧
      (eS (h (AdjoinRoot.root P)) : L ⊗[K] E) = 1 ⊗ₜ[K] β ∧ Function.Injective h ∧
      (letI := h.toAlgebra; Module.Finite (AdjoinRoot P) S) ∧
      ∀ r : B, IsLocalization.Away r L →
        letI := h.toAlgebra
        LocalizationEq (AdjoinRoot P) S (AdjoinRoot.of P (algebraMap B R r)) := by
  have : Module.Finite B (integralClosure B (L ⊗[K] E)) :=
    Module.Finite.equiv eS.toLinearEquiv
  let Q := P.map eR.toRingHom
  obtain ⟨h₀, hc₀, hr₀, hi₀, hfin₀⟩ :=
    exists_injective_finite_adjoinRoot_map_integralClosure B K L F E hβ hgen Q
      (hP.map eR.toRingHom) (by simpa only [Q, Polynomial.map_map] using hPmap) hβB
  let eP := AdjoinRoot.mapAlgEquiv eR P Q (Associated.refl _)
  let h := eS.symm.toRingHom.comp (h₀.comp eP.toRingHom)
  let ψ : L ⊗[K] F →ₐ[B] L ⊗[K] E :=
    (Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K F E)).restrictScalars B
  let b : R →ₐ[B] S := eS.symm.toAlgHom.comp (ψ.mapIntegralClosure.comp eR.toAlgHom)
  have hc (r : R) : h (AdjoinRoot.of P r) = b r := by
    apply eS.injective
    apply Subtype.val_injective
    change (eS (eS.symm (h₀ (eP (AdjoinRoot.of P r)))) : L ⊗[K] E) = _
    rw [eS.apply_symm_apply]
    change (h₀ (AdjoinRoot.map eR.toRingHom P Q dvd_rfl (AdjoinRoot.of P r)) : L ⊗[K] E) = _
    rw [AdjoinRoot.map_of, hc₀]
    change _ = (eS (eS.symm (ψ.mapIntegralClosure (eR r))) : L ⊗[K] E)
    rw [eS.apply_symm_apply]
    rfl
  have hb (r : R) : (eS (b r) : L ⊗[K] E) =
      Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K F E) (eR r) := by
    change (eS (eS.symm (ψ.mapIntegralClosure (eR r))) : L ⊗[K] E) = _
    rw [eS.apply_symm_apply]
    rfl
  have hr : (eS (h (AdjoinRoot.root P)) : L ⊗[K] E) = 1 ⊗ₜ[K] β := by
    change (eS (eS.symm (h₀ (eP (AdjoinRoot.root P)))) : L ⊗[K] E) = _
    rw [eS.apply_symm_apply]
    change (h₀ (AdjoinRoot.map eR.toRingHom P Q dvd_rfl (AdjoinRoot.root P)) : L ⊗[K] E) = _
    rw [AdjoinRoot.map_root, hr₀]
  refine ⟨b, h, RingHom.ext hc, hb, hr,
    eS.symm.injective.comp (hi₀.comp eP.injective),
    finite_adjoinRoot_of_comp_eq h fun r => by rw [hc, b.commutes], ?_⟩
  intro r hloc
  let := hloc
  exact localizationEq_of_tensor_adjoinRoot_integralClosure_equiv eR eS hβ hgen P hPmap h
    (fun x => (congrArg (fun y : S => (eS y : L ⊗[K] E)) (hc x)).trans (hb x)) hr r

end IsDiscreteValuationRing
