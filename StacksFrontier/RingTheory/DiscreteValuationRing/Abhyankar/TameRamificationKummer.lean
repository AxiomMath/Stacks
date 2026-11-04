module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AbhyankarLemma

/-!
# Tame ramification via Kummer extensions

Tame ramification of a finite separable extension `L / K` is characterized by the existence of a
Kummer extension `K[π^(1/e)]` of exponent prime to the residue characteristic over which `L`
embeds into an unramified extension.

## Main results

* `IsDiscreteValuationRing.isTamelyRamifiedWithRespectTo_tfae_hasUnramifiedKummerOverfield`:
  three equivalent characterizations of tame ramification.

## Implementation notes

The rings `A[π^(1/n)]` and fields `K[π^(1/n)]` are the canonical Kummer models of Tag 09EV.

## References

* [The Stacks Project, Tag 0EXW](https://stacks.math.columbia.edu/tag/0EXW)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y z v' w'

open Polynomial

open scoped TensorProduct

section Kummer

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (π : A)

private theorem bij_K1_one (hπ : Irreducible π) :
    letI : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π 1)) :=
      ⟨Stacks.KummerExtension.kummerPoly_irreducible K π 1 le_rfl hπ⟩
    Function.Bijective (algebraMap K (Stacks.KummerExtension.K1 K π 1)) := by
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π 1)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π 1 le_rfl hπ⟩
  have hf : Stacks.KummerExtension.kummerPoly K π 1 ≠ 0 := (Fact.out : Irreducible _).ne_zero
  rw [Algebra.bijective_algebraMap_iff, ← Subalgebra.finrank_eq_one_iff,
    (Subalgebra.topEquiv).toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hf).finrank,
    AdjoinRoot.powerBasis_dim, Stacks.KummerExtension.kummerPoly, pow_one, natDegree_X_sub_C]

private theorem bij_A1_one (hπ : Irreducible π) :
    letI : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π 1)) :=
      ⟨Stacks.KummerExtension.kummerPoly_irreducible K π 1 le_rfl hπ⟩
    Function.Bijective (algebraMap A (Stacks.KummerExtension.A1 K π 1)) := by
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π 1)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π 1 le_rfl hπ⟩
  have hb := bij_K1_one K π hπ
  have hAK1 : Function.Injective (algebraMap A (Stacks.KummerExtension.K1 K π 1)) := by
    rw [IsScalarTower.algebraMap_eq A K (Stacks.KummerExtension.K1 K π 1)]
    exact hb.1.comp (IsFractionRing.injective A K)
  refine ⟨fun x y hxy => hAK1 (congrArg Subtype.val hxy), fun x => ?_⟩
  obtain ⟨y, hy⟩ := hb.2 x.1
  let φ : K →ₐ[A] Stacks.KummerExtension.K1 K π 1 := IsScalarTower.toAlgHom A K _
  have hyint : IsIntegral A y := by
    rw [← isIntegral_algHom_iff φ hb.1]
    show IsIntegral A (algebraMap K _ y)
    rw [hy]; exact x.2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyint
  refine ⟨a, Subtype.ext ?_⟩
  show algebraMap A (Stacks.KummerExtension.K1 K π 1) a = x.1
  rw [IsScalarTower.algebraMap_apply A K, ha, hy]

end Kummer

open IsLocalRing in
private theorem tame_of_unram {R K M : Type*} [CommRing R] [IsLocalRing R] [Field K] [Field M]
    [Algebra R K] [Algebra R M] [Algebra K M] [IsScalarTower R K M]
    [Module.Finite K M] [Algebra.IsSeparable K M]
    (h : ∀ m : Ideal (integralClosure R M), m.IsMaximal →
      ∀ _ : m.LiesOver (IsLocalRing.maximalIdeal R),
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal R) m = 1 ∧
          @Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ m) _ _
            (Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal R))) :
    Stacks.KummerExtension.IsTamelyRamified R K M := by
  intro m hm hlies
  obtain ⟨h1, h2⟩ := h m hm hlies
  exact ⟨h2, Or.inr (h1 ▸ Nat.coprime_one_right _)⟩

private theorem coprime_of_isUnit {A : Type*} [CommRing A] [IsLocalRing A] {e : ℕ}
    (he : IsUnit (e : IsLocalRing.ResidueField A)) :
    ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A)) e := by
  show ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A)) e
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField A)
      (ringChar (IsLocalRing.ResidueField A)) with hp | hp
  · right
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    rw [(ringChar.spec (IsLocalRing.ResidueField A) e).mpr hdvd] at he
    exact not_isUnit_zero he
  · exact Or.inl hp

open IsLocalRing in
private theorem exists_common_exponent
    (A : Type*) (K : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (htame : IsTamelyRamifiedWithRespectTo A K L) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : ResidueField A) ∧
      ∀ m : Ideal (integralClosure A L), m.IsMaximal → m.LiesOver (IsLocalRing.maximalIdeal A) →
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m ∣ e₀ := by
  classical
  let B := integralClosure A L
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraMap_injective_of_field_isFractionRing A B K L)
  have hpne : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  let S : Set (Ideal B) := {m | m.IsMaximal ∧ m.LiesOver (IsLocalRing.maximalIdeal A)}
  have hS : S.Finite := (IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal A) B).subset
    fun m hm => ⟨hm.1.isPrime, hm.2⟩
  refine ⟨∏ m ∈ hS.toFinset, Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m, ?_, ?_, ?_⟩
  · refine Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun m hm => ?_)
    obtain ⟨hmax, hlies⟩ := hS.mem_toFinset.mp hm
    have := hmax.isPrime
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m hpne
  · rw [Nat.cast_prod, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
    obtain ⟨hmax, hlies⟩ := hS.mem_toFinset.mp hm
    have := hmax.isPrime
    have hne := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m hpne
    obtain ⟨-, hchar⟩ := htame m hmax hlies
    intro h0
    have hdvd := (ringChar.spec (ResidueField A) _).mp h0
    change ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A)) _ at hchar
    change ringChar (A ⧸ IsLocalRing.maximalIdeal A) ∣ _ at hdvd
    rcases hchar with h | h
    · rw [h, zero_dvd_iff] at hdvd
      exact hne hdvd
    · have h1 : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 1 :=
        Nat.Coprime.eq_one_of_dvd h hdvd
      have : CharP (A ⧸ IsLocalRing.maximalIdeal A) 1 := h1 ▸ ringChar.charP _
      have := CharP.CharOne.subsingleton (R := A ⧸ IsLocalRing.maximalIdeal A)
      exact zero_ne_one (Subsingleton.elim (0 : A ⧸ IsLocalRing.maximalIdeal A) 1)
  · intro m hmax hlies
    exact Finset.dvd_prod_of_mem _ (hS.mem_toFinset.mpr ⟨hmax, hlies⟩)

open IsLocalRing Stacks.KummerExtension in
private theorem tame_of_has
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (π : A) (hπ : Irreducible π) (e : ℕ)
    (h : HasUnramifiedKummerOverfield A K L π hπ e) :
    IsTamelyRamifiedWithRespectTo A K L := by
  obtain ⟨he, hu, L', _, _, _, _, _, _, _, _, _, _, hcompat, ⟨ι⟩, hunr⟩ := h
  let : Fact (Irreducible (kummerPoly K π e)) := ⟨kummerPoly_irreducible K π e he hπ⟩
  have hAK1L' : ∀ a : A, algebraMap A L' a =
      algebraMap (A1 K π e) L' (algebraMap A (A1 K π e) a) := by
    intro a
    rw [hcompat, IsScalarTower.algebraMap_apply A (K1 K π e) L']
    rfl
  have hsepK1 : Algebra.IsSeparable K (K1 K π e) := by
    rcases Nat.lt_or_ge e 2 with h2 | h2
    · obtain rfl : e = 1 := by omega
      exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl K)
        (RingEquiv.ofBijective _ (bij_K1_one K π hπ)) (by ext; simp)
    · exact isSeparable_K1 K π e h2 hπ (coprime_of_isUnit hu)
  let : IsScalarTower A K L' := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A (K1 K π e) L',
      IsScalarTower.algebraMap_apply A K (K1 K π e),
      ← IsScalarTower.algebraMap_apply K (K1 K π e) L']
  let : Module.Finite K L' := Module.Finite.trans (K1 K π e) L'
  let : Algebra.IsSeparable K L' := Algebra.IsSeparable.trans K (K1 K π e) L'
  have htame' : Stacks.KummerExtension.IsTamelyRamified A K L' := by
    rcases Nat.lt_or_ge e 2 with h2 | h2
    · obtain rfl : e = 1 := by omega
      let σ : A ≃+* A1 K π 1 := RingEquiv.ofBijective _ (bij_A1_one K π hπ)
      refine tame_of_unram (unram_transport σ.symm (fun r => ?_) hunr)
      obtain ⟨a, rfl⟩ := σ.surjective r
      rw [RingEquiv.symm_apply_apply, hAK1L']
      rfl
    · let : IsFractionRing (integralClosure A (K1 K π e)) (K1 K π e) :=
        integralClosure.isFractionRing_of_finite_extension K (K1 K π e)
      refine isTamelyRamified_tower A K (K1 K π e) L'
        (Stacks.KummerExtension.isTamelyRamified_K1 K π e h2 hπ (coprime_of_isUnit hu)) ?_
      intro m hm
      let : m.IsPrime := hm.isPrime
      let : Algebra (Localization.AtPrime m) (K1 K π e) :=
        IsLocalization.localizationAlgebraOfSubmonoidLe _ _ m.primeCompl
          (nonZeroDivisors (integralClosure A (K1 K π e))) m.primeCompl_le_nonZeroDivisors
      let : Algebra (Localization.AtPrime m) L' :=
        ((algebraMap (K1 K π e) L').comp
          (algebraMap (Localization.AtPrime m) (K1 K π e))).toAlgebra
      let : IsScalarTower (Localization.AtPrime m) (K1 K π e) L' :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hmeq : m = IsLocalRing.maximalIdeal (A1 K π e) := IsLocalRing.eq_maximalIdeal hm
      have hunits : m.primeCompl ≤ IsUnit.submonoid (A1 K π e) := by
        intro x hx
        have hx' : x ∉ IsLocalRing.maximalIdeal (A1 K π e) := hmeq ▸ hx
        exact IsLocalRing.notMem_maximalIdeal.mp hx'
      let σ : A1 K π e ≃+* Localization.AtPrime m :=
        (IsLocalization.atUnits (A1 K π e) m.primeCompl hunits).toRingEquiv
      have htower := IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime m) (K1 K π e) m.primeCompl
          (nonZeroDivisors (integralClosure A (K1 K π e))) m.primeCompl_le_nonZeroDivisors
      refine tame_of_unram (unram_transport σ (fun r => ?_) hunr)
      show algebraMap (K1 K π e) L' (algebraMap (Localization.AtPrime m) (K1 K π e)
        (algebraMap (A1 K π e) (Localization.AtPrime m) r)) = _
      rw [hcompat]
      congr 1
      exact (IsScalarTower.algebraMap_apply (A1 K π e) (Localization.AtPrime m) (K1 K π e) r).symm
  let : Algebra L L' := ι.toRingHom.toAlgebra
  let : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun k => (ι.commutes k).symm
  let : IsScalarTower A L L' := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K L', IsScalarTower.algebraMap_apply A K L]
    exact (ι.commutes _).symm
  let : Module.Finite L L' := Module.Finite.of_restrictScalars_finite K L L'
  let : Algebra.IsSeparable L L' := Algebra.isSeparable_tower_top_of_isSeparable K L L'
  exact isTamelyRamified_of_isTamelyRamified_tower A K L L' htame'

private theorem overfield_implies_tame
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (π : A) (hπ : Irreducible π) :
    (∃ e : ℕ, HasUnramifiedKummerOverfield A K L π hπ e) →
      IsTamelyRamifiedWithRespectTo A K L := by
  rintro ⟨e, h⟩
  exact tame_of_has A K L π hπ e h

private theorem formallySmoothNAdic_of_equiv
    {R : Type v} {S : Type w} {R' : Type v'} {S' : Type w'}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing S] [IsLocalRing S']
    (a : R' ≃+* R) (b : S ≃+* S') (φ : R →+* S) (φ' : R' →+* S')
    (hc : b.toRingHom.comp (φ.comp a.toRingHom) = φ')
    (h : RingHom.FormallySmoothNAdic.{u} φ (IsLocalRing.maximalIdeal S)) :
    RingHom.FormallySmoothNAdic.{u} φ' (IsLocalRing.maximalIdeal S') := by
  intro T _ J hJ f q hq hn
  have hq' : (q.comp b.toRingHom).comp φ =
      (Ideal.Quotient.mk J).comp (f.comp a.symm.toRingHom) := by
    ext r
    have h := RingHom.congr_fun hq (a.symm r)
    have hc' := RingHom.congr_fun hc (a.symm r)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at hc'
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ← hc'] using h
  have hn' : ∃ k : ℕ, 1 ≤ k ∧
      IsLocalRing.maximalIdeal S ^ k ≤ RingHom.ker (q.comp b.toRingHom) := by
    obtain ⟨k, hk, hn⟩ := hn
    refine ⟨k, hk, ?_⟩
    show IsLocalRing.maximalIdeal S ^ k ≤ (RingHom.ker q).comap b.toRingHom
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    have hmax : (IsLocalRing.maximalIdeal S).map b.toRingHom =
        IsLocalRing.maximalIdeal S' := IsLocalRing.map_ringEquiv_maximalIdeal b
    rwa [hmax]
  obtain ⟨g, hg, hgf⟩ := h T J hJ (f.comp a.symm.toRingHom) (q.comp b.toRingHom) hq' hn'
  refine ⟨g.comp b.symm.toRingHom, ?_, ?_⟩
  · ext s
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
      using RingHom.congr_fun hg (b.symm s)
  · ext r
    have hc' := RingHom.congr_fun hc r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hc'
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← hc',
      RingEquiv.symm_apply_apply] using RingHom.congr_fun hgf (a r)

-- Abhyankar for a specified quotient of the tensor product.
private theorem formallySmooth_tensor_factor
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (F : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field F]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K F]
    [Algebra A F] [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K F]
    (E : Type (max u v w x y)) [Field E]
    [Algebra K E] [Algebra L E] [Algebra F E] [Algebra B E]
    [IsScalarTower K L E] [IsScalarTower K F E] [IsScalarTower B L E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ f : F, t (1 ⊗ₜ[K] f) = algebraMap F E f)
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A)) (ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    (f : integralClosure A F →+* integralClosure B E)
    (hf : ∀ z : integralClosure A F, (f z : E) = algebraMap F E (z : F))
    (p : Ideal (integralClosure A F)) [p.IsMaximal]
    (hp : ramificationIndex A B ∣ p.ramificationIdx A)
    (q : Ideal (integralClosure B E)) [q.IsMaximal] (hq : q.comap f = p) :
    ∃ φ : Localization.AtPrime p →+* Localization.AtPrime q,
      Function.Injective φ ∧ IsLocalHom φ ∧
        (∀ z : integralClosure A F, φ (algebraMap _ _ z) = algebraMap _ _ (f z)) ∧
        RingHom.FormallySmoothNAdic.{max u v w x y} φ
          (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  classical
  obtain ⟨n, H, hfield, hK, hL, hF, hB, hKL, hKF, hfin, d, hn, hdL, hdF, hdB, hloc⟩ :=
    formallySmooth_localizations_of_ramificationIndex_dvd A B K L F htame
  have hnil : ∀ z ∈ nilradical (L ⊗[K] F), t z = 0 := by
    intro z hz
    have : (RingHom.ker t).IsPrime := RingHom.ker_isPrime t
    exact nilradical_le_prime (RingHom.ker t) hz
  let t₀ := Ideal.Quotient.liftₐ (nilradical (L ⊗[K] F)) t hnil
  have ht₀ : Function.Surjective t₀ := by
    intro e
    obtain ⟨z, rfl⟩ := ht e
    exact ⟨Ideal.Quotient.mk _ z, rfl⟩
  obtain ⟨i, g, hg⟩ := exists_algEquiv_of_surjective_pi K H E
    (t₀.comp d.symm.toAlgHom) (ht₀.comp d.symm.surjective)
  have hg' (z : L ⊗[K] F) : g (d (Ideal.Quotient.mk _ z) i) = t z := by
    have h := AlgHom.congr_fun hg (d (Ideal.Quotient.mk _ z))
    show g (d (Ideal.Quotient.mk _ z) i) = t₀ (Ideal.Quotient.mk _ z)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
      Pi.evalAlgHom_apply] using h
  have hgL (l : L) : g (algebraMap L (H i) l) = algebraMap L E l := by
    rw [← hdL i l]
    exact (hg' (l ⊗ₜ[K] 1)).trans (htL l)
  have hgF (a : F) : g (algebraMap F (H i) a) = algebraMap F E a := by
    rw [← hdF i a]
    exact (hg' (1 ⊗ₜ[K] a)).trans (htF a)
  let gB : H i ≃ₐ[B] E :=
    { g.toRingEquiv with
      commutes' := fun b => by
        show g (algebraMap B (H i) b) = algebraMap B E b
        rw [hdB i b, hgL, ← IsScalarTower.algebraMap_apply B L E] }
  let c : integralClosure B (H i) ≃ₐ[B] integralClosure B E := gB.mapIntegralClosure
  obtain ⟨fᵢ, hfᵢ, hfᵢA, hformal⟩ := hloc i
  have hcf (z : integralClosure A F) : c (fᵢ z) = f z := by
    apply Subtype.ext
    show g (fᵢ z : H i) = (f z : E)
    rw [hfᵢ, hgF, hf]
  let qᵢ := q.comap c.toRingHom
  have : qᵢ.IsMaximal := Ideal.comap_isMaximal_of_surjective _ c.surjective
  have hqᵢ : qᵢ.comap fᵢ = p := by
    rw [← hq]
    show q.comap (c.toRingHom.comp fᵢ) = q.comap f
    congr 1
    exact RingHom.ext hcf
  obtain ⟨_, _, _, _, φ, hφinj, hφlocal, hφcomp, hφformal⟩ :=
    hformal p inferInstance hp qᵢ inferInstance hqᵢ
  let b : Localization.AtPrime qᵢ ≃+* Localization.AtPrime q :=
    Localization.localRingEquiv qᵢ q c.toRingEquiv rfl
  let φ' := b.toRingHom.comp φ
  have : IsLocalHom φ := hφlocal
  have : IsLocalHom b.toRingHom := IsLocalHom.of_surjective _ b.surjective
  refine ⟨φ', b.injective.comp hφinj, RingHom.isLocalHom_comp b.toRingHom φ, ?_, ?_⟩
  · intro z
    show b (φ (algebraMap _ _ z)) = _
    rw [hφcomp]
    show Localization.localRingHom qᵢ q c.toRingHom rfl
      (algebraMap _ _ (fᵢ z)) = _
    rw [Localization.localRingHom_to_map]
    show algebraMap _ _ (c (fᵢ z)) = algebraMap _ _ (f z)
    rw [hcf]
  · exact formallySmoothNAdic_of_equiv (RingEquiv.refl _) b φ φ' rfl hφformal

private noncomputable def quotientEquivResidue
    (A C T : Type*) [CommRing A] [CommRing C] [CommRing T]
    [Algebra A C] [Algebra C T] [Algebra A T] [IsScalarTower A C T]
    (n : Ideal C) [n.IsMaximal] [IsLocalization.AtPrime T n] [IsLocalRing T] :
    (C ⧸ n) ≃ₐ[A] IsLocalRing.ResidueField T :=
  { IsLocalization.AtPrime.equivQuotMaximalIdeal n T with
    commutes' := fun a => by
      change Ideal.Quotient.mk _ (algebraMap C T (algebraMap A C a)) =
        Ideal.Quotient.mk _ (algebraMap A T a)
      rw [← IsScalarTower.algebraMap_apply A C T] }

private theorem finite_residue_of_localization
    (A C T : Type*) [CommRing A] [CommRing C] [CommRing T]
    [Algebra A C] [Algebra C T] [Algebra A T] [IsScalarTower A C T]
    [Module.Finite A C]
    (n : Ideal C) [n.IsMaximal] [IsLocalization.AtPrime T n] [IsLocalRing T] :
    Module.Finite A (IsLocalRing.ResidueField T) :=
  Module.Finite.equiv (quotientEquivResidue A C T n).toLinearEquiv

private theorem formallyUnramified_of_formallySmooth_localization
    (A : Type u) (C : Type v) (T : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A C] [Algebra C T] [Algebra A T] [IsScalarTower A C T]
    [Module.Finite A C] [IsExtension A T]
    (n : Ideal C) [n.IsMaximal] [IsLocalization.AtPrime T n]
    (h : RingHom.FormallySmoothNAdic.{max u w} (algebraMap A T)
      (IsLocalRing.maximalIdeal T)) : Algebra.FormallyUnramified A T := by
  have : Algebra.EssFiniteType C T := .of_isLocalization T n.primeCompl
  have : Algebra.EssFiniteType A T := .comp A C T
  have : Module.Finite A (IsLocalRing.ResidueField T) := finite_residue_of_localization A C T n
  have : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField T) :=
    Module.Finite.of_restrictScalars_finite A _ _
  obtain ⟨he, hs⟩ :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A T).mp h
  have := hs
  have : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField T) :=
    isSeparable_of_isSeparableExtension _ _
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  obtain ⟨_, hpow, _, _⟩ := ramificationIndex_characterization A T
  change ramificationIndex A T = 1 at he
  simpa only [he, pow_one] using hpow

theorem isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable
    (A : Type u) (C : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDedekindDomain C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] (n : Ideal C) [n.IsMaximal]
    [n.LiesOver (IsLocalRing.maximalIdeal A)] :
    Algebra.IsUnramifiedAt A n ↔
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) n = 1 ∧
      @Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ n) _ _
        (Ideal.Quotient.algebraOfLiesOver n (IsLocalRing.maximalIdeal A)) := by
  let p := IsLocalRing.maximalIdeal A
  let _ := Localization.AtPrime.algebraOfLiesOver p n
  have hn : n ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) n
  rw [Algebra.isUnramifiedAt_iff_map_eq A p n,
    Algebra.isSeparable_residueField_iff,
    Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hn (Ideal.map_le_of_le_comap
      (Ideal.over_def n p).le)]
  exact and_comm

private theorem isLocalHom_localization
    (A B T : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra B T] [Algebra A T] [IsScalarTower A B T]
    (m : Ideal B) [m.IsPrime] [m.LiesOver (IsLocalRing.maximalIdeal A)]
    [IsLocalization.AtPrime T m] [IsLocalRing T] :
    IsLocalHom (algebraMap A T) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap A T)).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq A B T, ← Ideal.comap_comap]
  show ((IsLocalRing.maximalIdeal T).under B).under A = _
  rw [IsLocalization.AtPrime.under_maximalIdeal T m,
    ← Ideal.over_def m (IsLocalRing.maximalIdeal A)]

private theorem tame_localization
    (A B T : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Algebra A B] [Algebra B T] [Algebra A T]
    [IsScalarTower A B T] [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsExtension A T]
    (m : Ideal B) [m.IsMaximal] [m.LiesOver (IsLocalRing.maximalIdeal A)]
    [IsLocalization.AtPrime T m]
    (hs : @Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ m) _ _
      (Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A)))
    (hc : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A))
        (Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m)) :
    (ramificationIndex A T =
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m) ∧
    (ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A)) (ramificationIndex A T) ∧
        Algebra.IsSeparableExtension
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField T)) := by
  have he : ramificationIndex A T =
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m := by
    rw [ramificationIndex_eq_ramificationIdx A T,
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field A)]
    exact ramificationIdx_atPrime A B T m
  refine ⟨he, ?_⟩
  rcases hc with hc | hc
  · exact Or.inl hc
  right
  refine ⟨he ▸ hc, ?_⟩
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let : Algebra (IsLocalRing.ResidueField A) (B ⧸ m) :=
    Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A)
  have : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ m) :=
    .of_algebraMap_eq fun _ => rfl
  have : Algebra.IsSeparable (IsLocalRing.ResidueField A) (B ⧸ m) := hs
  let e : (B ⧸ m) ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField T :=
    (quotientEquivResidue A B T m).extendScalarsOfSurjective
      (show Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) from
        IsLocalRing.residue_surjective)
  have : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField T) :=
    Algebra.IsSeparable.of_algHom _ (B ⧸ m) e.symm.toAlgHom
  exact isSeparableExtension_of_isSeparable _ _

-- Match the build's instance-synthesis depth when this proof is validated directly.
set_option maxSynthPendingDepth 3 in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- Elaborating the many nested localization and tensor-product algebra structures here is
-- expensive.
set_option synthInstance.maxHeartbeats 200000 in
-- The normalization square requires searching several compatible scalar towers.
private theorem isUnramified_tensor_factor
    (A : Type u) (K : Type v) (L : Type w) (F : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [Module.Finite K F] [Algebra.IsSeparable K F]
    [IsDiscreteValuationRing (integralClosure A F)]
    [IsFractionRing (integralClosure A F) F]
    (E : Type (max u v w x)) [Field E]
    [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Algebra A E] [IsScalarTower A K E] [IsScalarTower A F E]
    [Algebra L E] [IsScalarTower K L E] [IsScalarTower A L E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ f : F, t (1 ⊗ₜ[K] f) = algebraMap F E f)
    (htame : IsTamelyRamifiedWithRespectTo A K L)
    (hdiv : ∀ m : Ideal (integralClosure A L), m.IsMaximal →
      m.LiesOver (IsLocalRing.maximalIdeal A) →
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m ∣
        (IsLocalRing.maximalIdeal (integralClosure A F)).ramificationIdx A) :
    IsUnramifiedWithRespectTo (integralClosure A F) F E := by
  classical
  let B := integralClosure A L
  let C := integralClosure A E
  let A₁ := integralClosure A F
  have : Module.Finite K E := Module.Finite.trans F E
  have : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K F E
  have : Module.Finite L E := Module.Finite.of_restrictScalars_finite K L E
  have : Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable K L E
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A K E
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : IsFractionRing A₁ F := integralClosure.isFractionRing_of_finite_extension K F
  let bc : B →ₐ[A] C := (IsScalarTower.toAlgHom A L E).mapIntegralClosure
  let : Algebra B C := bc.toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq fun a => (bc.commutes a).symm
  have : IsScalarTower B C E := .of_algebraMap_eq fun _ => rfl
  let ac : A₁ →ₐ[A] C := (IsScalarTower.toAlgHom A F E).mapIntegralClosure
  let : Algebra A₁ C := ac.toAlgebra
  have : IsScalarTower A A₁ C := .of_algebraMap_eq fun a => (ac.commutes a).symm
  have : IsScalarTower A₁ C E := .of_algebraMap_eq fun _ => rfl
  have : IsIntegralClosure C B E := IsIntegralClosure.tower_top (R := A)
  have : IsIntegralClosure C A₁ E := IsIntegralClosure.tower_top (R := A)
  have hA₁C : Function.Injective (algebraMap A₁ C) :=
    algebraMap_injective_of_field_isFractionRing A₁ C F E
  have : FaithfulSMul A₁ C := (faithfulSMul_iff_algebraMap_injective A₁ C).mpr hA₁C
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  have : Module.Finite A₁ C := Module.Finite.of_restrictScalars_finite A A₁ C
  have hAinj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraMap_injective_of_field_isFractionRing A B K L)
  have hlocal (n : Ideal C) (hn : n.IsMaximal) :
      Algebra.FormallyUnramified A₁ (Localization.AtPrime n) := by
    have := hn
    let m := n.under B
    have : m.IsMaximal := Ideal.IsMaximal.under B n
    have : m.LiesOver (IsLocalRing.maximalIdeal A) :=
      (Ideal.liesOver_iff _ _).mpr
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A m)).symm
    have : n.LiesOver (IsLocalRing.maximalIdeal A₁) :=
      (Ideal.liesOver_iff _ _).mpr
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A₁ n)).symm
    have hm0 : m ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field A) m
    let R := Localization.AtPrime m
    let : Algebra R L := IsLocalization.localizationAlgebraOfSubmonoidLe _ _
      m.primeCompl (nonZeroDivisors B) m.primeCompl_le_nonZeroDivisors
    have : IsScalarTower B R L :=
      IsLocalization.localization_isScalarTower_of_submonoid_le R L m.primeCompl
        (nonZeroDivisors B) m.primeCompl_le_nonZeroDivisors
    have : IsScalarTower A R L := IsScalarTower.to₁₃₄ A B R L
    have : IsFractionRing R L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl R L
    have : IsDiscreteValuationRing R :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 R
    have : IsLocalHom (algebraMap A R) := isLocalHom_localization A B R m
    have : FaithfulSMul A R := FaithfulSMul.of_field_isFractionRing A R K L
    have : IsExtension A R := ⟨⟩
    let : Algebra R E := ((algebraMap L E).comp (algebraMap R L)).toAlgebra
    have : IsScalarTower R L E := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower B R E := IsScalarTower.to₁₂₄ B R L E
    have : IsScalarTower A R E := IsScalarTower.to₁₂₄ A R L E
    obtain ⟨hindex, hRtame⟩ := tame_localization A B R m
      (htame m inferInstance inferInstance).1 (htame m inferInstance inferInstance).2
    let D := integralClosure R E
    have hsub : C ≤ Subalgebra.restrictScalars A D := fun z hz => hz.tower_top
    let cd : C →ₐ[A] D := Subalgebra.inclusion hsub
    let : Algebra C D := cd.toAlgebra
    have : IsScalarTower C D E := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A C D := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower B C D := .of_algebraMap_eq fun b => by
      apply FaithfulSMul.algebraMap_injective D E
      rw [← IsScalarTower.algebraMap_apply C D E, ← IsScalarTower.algebraMap_apply B C E]
      exact (IsScalarTower.algebraMap_apply B D E b).symm
    have : IsLocalization (Algebra.algebraMapSubmonoid E m.primeCompl) E :=
      IsLocalization.self (by
        rintro z ⟨b, hb, rfl⟩
        apply isUnit_iff_ne_zero.mpr
        have hb0 : b ≠ 0 := fun h => hb (h ▸ m.zero_mem)
        simpa only [map_zero] using (FaithfulSMul.algebraMap_injective B E).ne hb0)
    have : IsLocalization (Algebra.algebraMapSubmonoid C m.primeCompl) D :=
      isLocalization_integralClosure B R E C m.primeCompl
    let q := n.map (algebraMap C D)
    have hdisj : Disjoint (Algebra.algebraMapSubmonoid C m.primeCompl : Set C) (n : Set C) := by
      rw [Set.disjoint_left]
      rintro z ⟨b, hb, rfl⟩ hz
      exact hb hz
    have : q.IsMaximal :=
      IsLocalization.isMaximal_of_isMaximal_disjoint _ D n hdisj
    have hqn : q.under C = n :=
      IsLocalization.under_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid C m.primeCompl) D inferInstance hdisj
    let f : A₁ →+* D := (cd.comp ac).toRingHom
    have hf (z : A₁) : (f z : E) = algebraMap F E (z : F) := rfl
    have hqp : q.comap f = IsLocalRing.maximalIdeal A₁ := by
      show (q.under C).under A₁ = _
      rw [hqn, ← Ideal.over_def n (IsLocalRing.maximalIdeal A₁)]
    have hdivR : ramificationIndex A R ∣
        (IsLocalRing.maximalIdeal A₁).ramificationIdx A := by
      rw [hindex]
      exact hdiv m inferInstance inferInstance
    obtain ⟨φ, hφinj, hφlocal, hφcomp, hφformal⟩ :=
      formallySmooth_tensor_factor A R K L F E t ht htL htF hRtame f hf
        (IsLocalRing.maximalIdeal A₁) hdivR q hqp
    let T := Localization.AtPrime n
    let U := Localization.AtPrime q
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C
        (Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A₁) n) T
    let : Algebra A₁ D := f.toAlgebra
    have : IsScalarTower A₁ C D := .of_algebraMap_eq fun _ => rfl
    have : IsLocalization.AtPrime U n := by
      have hh := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid C m.primeCompl) U q
      change IsLocalization (q.under C).primeCompl U at hh
      simpa only [hqn] using hh
    let b : U ≃ₐ[C] T := IsLocalization.algEquiv n.primeCompl U T
    let a : A₁ ≃ₐ[A₁] Localization.AtPrime (IsLocalRing.maximalIdeal A₁) :=
      IsLocalization.atUnits A₁ (IsLocalRing.maximalIdeal A₁).primeCompl
        (fun z hz => IsLocalRing.notMem_maximalIdeal.mp hz)
    have hcomp : b.toRingEquiv.toRingHom.comp (φ.comp a.toRingEquiv.toRingHom) =
        algebraMap A₁ T := by
      apply RingHom.ext
      intro z
      show b (φ (algebraMap A₁ _ z)) = algebraMap A₁ T z
      rw [hφcomp]
      show b (algebraMap C U (ac z)) = _
      rw [b.commutes]
      rfl
    have hformal : RingHom.FormallySmoothNAdic.{max u v w x} (algebraMap A₁ T)
        (IsLocalRing.maximalIdeal T) :=
      formallySmoothNAdic_of_equiv
        (R := Localization.AtPrime (IsLocalRing.maximalIdeal A₁)) (S := U)
        (R' := A₁) (S' := T) a.toRingEquiv b.toRingEquiv φ _ hcomp hφformal
    have : IsLocalHom (algebraMap A₁ T) := isLocalHom_localization A₁ C T n
    have : FaithfulSMul A₁ T := (faithfulSMul_iff_algebraMap_injective A₁ T).mpr (by
      rw [IsScalarTower.algebraMap_eq A₁ C T]
      exact (IsLocalization.injective T n.primeCompl_le_nonZeroDivisors).comp hA₁C)
    have : IsExtension A₁ T := ⟨⟩
    exact formallyUnramified_of_formallySmooth_localization A₁ C T n hformal
  have : Algebra.FormallyUnramified A₁ C := by
    apply Algebra.formallyUnramified_iff_forall.mpr
    intro p
    obtain ⟨n, hn, hpn⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    have := hn
    have : Algebra.IsUnramifiedAt A₁ n := hlocal n hn
    exact Algebra.isOpen_unramifiedLocus.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes p ⟨n, hn.isPrime⟩).mp hpn) this
  have : Algebra.FormallyUnramified A₁ (integralClosure A₁ E) :=
    Algebra.FormallyUnramified.of_equiv (IsIntegralClosure.equiv A₁ C E (integralClosure A₁ E))
  have : IsDedekindDomain (integralClosure A₁ E) := integralClosure.isDedekindDomain A₁ F E
  have : Module.Finite A₁ (integralClosure A₁ E) := IsIntegralClosure.finite A₁ F E _
  have : Module.IsTorsionFree A₁ (integralClosure A₁ E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap_injective_of_field_isFractionRing A₁ _ F E)
  intro n hn hlo
  have := hn
  have := hlo
  exact (isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable A₁ _ n).mp inferInstance

private theorem tame_has_overfields
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (π : A) (hπ : Irreducible π) :
    IsTamelyRamifiedWithRespectTo A K L →
      ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : IsLocalRing.ResidueField A) ∧
        ∀ d : ℕ, 1 ≤ d → IsUnit (d : IsLocalRing.ResidueField A) →
          HasUnramifiedKummerOverfield A K L π hπ (d * e₀) := by
  intro htame
  obtain ⟨e₀, he₀, hu₀, hdiv₀⟩ := exists_common_exponent A K L htame
  obtain ⟨e₁, he₁, hu₁, hmul⟩ := exists_large_unit_multiple (IsLocalRing.ResidueField A) e₀ he₀ hu₀
  refine ⟨e₁, by omega, hu₁, ?_⟩
  intro d hd hu
  let e := d * e₁
  have he : 2 ≤ e := by dsimp [e]; nlinarith
  have heu : IsUnit (e : IsLocalRing.ResidueField A) := by
    simpa only [e, Nat.cast_mul] using hu.mul hu₁
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π e)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π e (by omega) hπ⟩
  let F := Stacks.KummerExtension.K1 K π e
  let A₁ := Stacks.KummerExtension.A1 K π e
  have : Algebra.IsSeparable K F :=
    Stacks.KummerExtension.isSeparable_K1 K π e he hπ (coprime_of_isUnit heu)
  have : IsDiscreteValuationRing A₁ := Stacks.KummerExtension.isDiscreteValuationRing_A1 K π e he hπ
  have : IsFractionRing A₁ F := integralClosure.isFractionRing_of_finite_extension K F
  obtain ⟨E, hfield, hFE, hfin, hsep, q, hq⟩ :=
    exists_separable_tensor_factor.{v, w, v, u} K L F
  let : Algebra K E := ((algebraMap F E).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F E := .of_algebraMap_eq fun _ => rfl
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K E := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A F E := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply A K F]
    rfl
  let j : L →ₐ[K] E := (q.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let : Algebra L E := j.toAlgebra
  have : IsScalarTower K L E := .of_algebraMap_eq fun a => (j.commutes a).symm
  have : IsScalarTower A L E := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply A K L]
    exact (j.commutes _).symm
  let t : (L ⊗[K] F) →ₐ[K] E :=
    (q.restrictScalars K).comp (Algebra.TensorProduct.comm K L F).toAlgHom
  have ht : Function.Surjective t := hq.comp (Algebra.TensorProduct.comm K L F).surjective
  have htL (l : L) : t (l ⊗ₜ[K] 1) = algebraMap L E l := by
    show q (1 ⊗ₜ[K] l) = j l
    rfl
  have htF (f : F) : t (1 ⊗ₜ[K] f) = algebraMap F E f := by
    show q (f ⊗ₜ[K] 1) = algebraMap F E f
    exact q.commutes f
  have hr : (IsLocalRing.maximalIdeal A₁).ramificationIdx A = e := by
    obtain ⟨m, hm, hlo, _, hr⟩ := Stacks.KummerExtension.exists_ramificationIdx_eq K π e he hπ
    have hm' : m = IsLocalRing.maximalIdeal A₁ := IsLocalRing.eq_maximalIdeal hm
    subst m
    have := hlo
    have : Module.IsTorsionFree A A₁ := Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap_injective_of_field_isFractionRing A A₁ K F)
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field A)]
    exact hr
  have hunram : IsUnramifiedWithRespectTo A₁ F E :=
    isUnramified_tensor_factor A K L F E t ht htL htF htame (by
      intro m hm hlo
      rw [hr]
      exact (hdiv₀ m hm hlo).trans (hmul.trans (dvd_mul_left e₁ d)))
  refine ⟨by omega, heu, E, hfield, hFE, inferInstance, inferInstance,
    inferInstance, inferInstance, hfin, hsep, inferInstance, inferInstance, ?_, ⟨j⟩, hunram⟩
  intro x
  rfl

/-- A finite separable extension of the fraction field of a discrete valuation ring is tamely
ramified if and only if it embeds into an unramified extension after some Kummer base change;
equivalently, such an unramified overfield exists after every prime-to-residue-characteristic
multiple of one fixed exponent. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWithRespectTo_tfae_hasUnramifiedKummerOverfield
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (π : A) (hπ : Irreducible π) :
    List.TFAE
      [ IsTamelyRamifiedWithRespectTo A K L,
        ∃ e : ℕ, HasUnramifiedKummerOverfield A K L π hπ e,
        ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : IsLocalRing.ResidueField A) ∧
          ∀ d : ℕ, 1 ≤ d → IsUnit (d : IsLocalRing.ResidueField A) →
            HasUnramifiedKummerOverfield A K L π hπ (d * e₀) ] := by
  tfae_have 1 → 3
  | h => tame_has_overfields A K L π hπ h
  tfae_have 3 → 2
  | h => by
    obtain ⟨e₀, he₀, hu, h⟩ := h
    refine ⟨e₀, ?_⟩
    simpa using h 1 (by simp) (by simp)
  tfae_have 2 → 1
  | h => overfield_implies_tame A K L π hπ h
  tfae_finish

end

end IsDiscreteValuationRing
