module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Surjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.RingTheory.Nagata.IntegralClosure
public import StacksFrontier.RingTheory.IntegralClosure.Pi

/-!
# Integral closures after a finite extension of fraction fields

Let `A → B` be an extension of discrete valuation rings, with fraction fields `K ⊆ L`, and let
`K₁/K` be finite.  This file records the structure of the integral closures after passing from
`K` to `K₁`.  Writing `L₁ = (L ⊗[K] K₁)_red` for the reduced tensor product and `A₁ ⊆ K₁`,
`B₁ ⊆ L₁` for the integral closures of `A` and `B`: the ring `L₁` is a nonempty finite product
of finite extensions of `L`, the ring `A₁` is a Dedekind domain, the ring `B₁` is a finite
product of Dedekind domains, the induced map on spectra is surjective, and the expected local,
henselian, inseparable, separable, and Nagata consequences hold.

## Main definitions

* `IsDiscreteValuationRing.IsNonemptyFiniteProductOfFiniteFieldExtensions` and
  `IsDiscreteValuationRing.IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions` express a
  decomposition as a nonempty finite product of finite (separable) field extensions.
* `IsDiscreteValuationRing.IsFiniteProductOfDedekindDomains` and
  `IsDiscreteValuationRing.IsFiniteProductOfDiscreteValuationRings` express the corresponding
  ring decompositions.

## Main results

* `IsDiscreteValuationRing.integralClosures_after_finite_fraction_field_extension` gives all the
  properties of the two integral closures and the reduced tensor product.

## Implementation notes

The reduction of `L ⊗[K] K₁` is represented by its quotient by the nilradical.  Product
statements are expressed by explicit finite product decompositions, retaining the individual
field-extension and domain properties.

When `B` is henselian or complete, each field factor of `L₁` has a discrete valuation ring as
its integral closure.  Several such factors may lie over the same maximal ideal of `A₁`.

## References

* [Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
-/

@[expose] public section

open scoped TensorProduct

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁ uR

namespace IsDiscreteValuationRing

/-- A ring is a nonempty finite product of finite field extensions of `K`. -/
abbrev IsNonemptyFiniteProductOfFiniteFieldExtensions
    (K : Type uK) (R : Type uR) [Field K] [CommRing R] [Algebra K R] : Prop :=
  ∃ (n : ℕ) (E : Fin n → Type (max uK uR)) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i)) (_ : ∀ i, Module.Finite K (E i)),
    0 < n ∧ Nonempty (R ≃ₐ[K] ∀ i, E i)

/-- A ring is a finite product of Dedekind domains. -/
abbrev IsFiniteProductOfDedekindDomains (R : Type uR) [CommRing R] : Prop :=
  ∃ (n : ℕ) (D : Fin n → Type uR) (_ : ∀ i, CommRing (D i))
      (_ : ∀ i, IsDedekindDomain (D i)),
    0 < n ∧ Nonempty (R ≃+* ∀ i, D i)

/-- A ring is a finite product of discrete valuation rings. -/
abbrev IsFiniteProductOfDiscreteValuationRings (R : Type uR) [CommRing R] : Prop :=
  ∃ (n : ℕ) (D : Fin n → Type uR) (_ : ∀ i, CommRing (D i))
      (_ : ∀ i, IsDomain (D i)) (_ : ∀ i, IsDiscreteValuationRing (D i)),
    0 < n ∧ Nonempty (R ≃+* ∀ i, D i)

/-- A ring is a nonempty finite product of finite separable field extensions of `K`. -/
abbrev IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions
    (K : Type uK) (R : Type uR) [Field K] [CommRing R] [Algebra K R] : Prop :=
  ∃ (n : ℕ) (E : Fin n → Type (max uK uR)) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i)) (_ : ∀ i, Module.Finite K (E i))
      (_ : ∀ i, Algebra.IsSeparable K (E i)),
    0 < n ∧ Nonempty (R ≃ₐ[K] ∀ i, E i)

/-- A reduced finite algebra over a field is the product of its quotients by finitely many
maximal ideals, indexed by `Fin n`, with `n` positive when the algebra is nontrivial. -/
private theorem exists_algEquiv_pi_quotient_of_finite
    (F R : Type*) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R] :
    ∃ (n : ℕ) (I : Fin n → Ideal R) (_ : ∀ i, (I i).IsMaximal),
      (Nontrivial R → 0 < n) ∧ Nonempty (R ≃ₐ[F] ∀ i, R ⧸ I i) := by
  classical
  have : IsArtinianRing R := IsArtinianRing.of_finite F R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let e := (Fintype.equivFin (MaximalSpectrum R)).symm
  exact ⟨_, fun i => (e i).asIdeal, fun i => inferInstance,
    fun _ => Fintype.card_pos_iff.mpr inferInstance,
    ⟨((IsArtinianRing.equivPi R).restrictScalars F).trans
      (AlgEquiv.piCongrLeft F (fun I : MaximalSpectrum R => R ⧸ I.asIdeal) e).symm⟩⟩

/-- For a reduced finite `L`-algebra `S`: the integral closure of `B` in `S` is the product
of the integral closures in the quotients of `S` by finitely many maximal ideals. -/
private theorem exists_algEquiv_pi_integralClosure
    (B L S C : Type*) [CommRing B] [Field L] [CommRing S] [CommRing C]
    [Algebra B L] [Algebra L S] [Algebra B S] [IsScalarTower B L S]
    [Module.Finite L S] [IsReduced S] [Algebra B C] (eC : C ≃ₐ[B] integralClosure B S) :
    ∃ (n : ℕ) (I : Fin n → Ideal S) (_ : ∀ i, (I i).IsMaximal), (Nontrivial S → 0 < n) ∧
      Nonempty (C ≃ₐ[B] ∀ i, integralClosure B (S ⧸ I i)) := by
  obtain ⟨n, I, hI, hn, ⟨d⟩⟩ := exists_algEquiv_pi_quotient_of_finite L S
  exact ⟨n, I, hI, hn, ⟨(eC.trans (d.restrictScalars B).mapIntegralClosure).trans
    (integralClosurePiEquiv B _)⟩⟩

/-- A reduced finite algebra over a field is a nonempty finite product of finite field
extensions, indexed by its maximal ideals. -/
private theorem isNonemptyFiniteProductOfFiniteFieldExtensions_of_finite_of_isReduced
    (F : Type uL) (R : Type uR) [Field F] [CommRing R]
    [Algebra F R] [Module.Finite F R] [Nontrivial R] [IsReduced R] :
    IsNonemptyFiniteProductOfFiniteFieldExtensions F R := by
  obtain ⟨n, I, hI, hn, ⟨e⟩⟩ := exists_algEquiv_pi_quotient_of_finite F R
  let : ∀ i, Field (R ⧸ I i) := fun i => Ideal.Quotient.field (I i)
  exact ⟨n, fun i => ULift.{uL} (R ⧸ I i), fun i => inferInstance, fun i => inferInstance,
    fun i => inferInstance, hn inferInstance,
    ⟨e.trans (AlgEquiv.piCongrRight fun _ => ULift.algEquiv.symm)⟩⟩

private theorem isDedekindDomain_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
    (e : R ≃+* S) : IsDedekindDomain R := by
  have : IsDomain R := e.toMulEquiv.isDomain _
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e.symm
  have : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  exact (isDedekindDomain_iff R (FractionRing R)).2
    ⟨inferInstance, inferInstance, inferInstance,
      (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance⟩

private theorem isDedekindDomain_integralClosure_equiv
    (A : Type uA) (K : Type uK) (K₁ : Type uK₁) (A₁ : Type uA₁)
    [CommRing A] [Field K] [Field K₁] [CommRing A₁]
    [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K] [IsFractionRing A K]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁] [Module.Finite K K₁]
    [Algebra A A₁] (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁) : IsDedekindDomain A₁ := by
  have : IsDedekindDomain (integralClosure A K₁) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      A K K₁ (integralClosure A K₁)).1
  exact isDedekindDomain_of_ringEquiv eA₁.toRingEquiv

private theorem isFiniteProductOfDedekindDomains_of_equiv
    {R : Type*} [CommRing R] {n : ℕ} (hn : 0 < n) (D : Fin n → Type*)
    [∀ i, CommRing (D i)] [∀ i, IsDedekindDomain (D i)]
    (e : R ≃+* ∀ i, D i) : IsFiniteProductOfDedekindDomains R := by
  classical
  let f (i : Fin n) : R →+* D i := (Pi.evalRingHom D i).comp e.toRingHom
  have hf (i) : Function.Surjective (f i) := by
    intro x
    exact ⟨e.symm (Pi.single i x), by simp [f]⟩
  let q (i : Fin n) : (R ⧸ RingHom.ker (f i)) ≃+* D i :=
    RingHom.quotientKerEquivOfSurjective (hf i)
  have (i : Fin n) : IsDedekindDomain (R ⧸ RingHom.ker (f i)) :=
    isDedekindDomain_of_ringEquiv (q i)
  exact ⟨n, (fun i => R ⧸ RingHom.ker (f i)), inferInstance, this, hn,
    ⟨e.trans (RingEquiv.piCongrRight fun i => (q i).symm)⟩⟩

private theorem isFiniteProductOfDedekindDomains_integralClosure
    (B L S C : Type*) [CommRing B] [Field L] [CommRing S] [CommRing C]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra B L] [IsFractionRing B L]
    [Algebra L S] [Algebra B S] [IsScalarTower B L S]
    [Module.Finite L S] [IsReduced S] [Nontrivial S] [Algebra B C]
    (eC : C ≃ₐ[B] integralClosure B S) : IsFiniteProductOfDedekindDomains C := by
  obtain ⟨n, I, hI, hn, ⟨e⟩⟩ := exists_algEquiv_pi_integralClosure B L S C eC
  let : ∀ i, Field (S ⧸ I i) := fun i => Ideal.Quotient.field (I i)
  have : ∀ i, IsDedekindDomain (integralClosure B (S ⧸ I i)) := fun i =>
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      B L (S ⧸ I i) (integralClosure B (S ⧸ I i))).1
  exact isFiniteProductOfDedekindDomains_of_equiv (hn inferInstance)
    (fun i => integralClosure B (S ⧸ I i)) e.toRingEquiv

private theorem henselianLocalRing_of_henselianRing
    (R : Type*) [CommRing R] [IsLocalRing R] [HenselianRing R (IsLocalRing.maximalIdeal R)] :
    HenselianLocalRing R where
  is_henselian f hf a ha hd := HenselianRing.is_henselian f hf a ha
    (hd.map (Ideal.Quotient.mk _))

@[sga "6 X 7.13.3"]
private theorem isDiscreteValuationRing_integralClosure_of_henselianLocalRing
    (A K K₁ C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianLocalRing A] [Field K] [Field K₁] [Algebra A K] [IsFractionRing A K]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁] [Module.Finite K K₁]
    [CommRing C] [Algebra A C] (e : C ≃ₐ[A] integralClosure A K₁) :
    ∃ _ : IsDomain C, IsDiscreteValuationRing C := by
  have : IsDedekindDomain (integralClosure A K₁) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      A K K₁ (integralClosure A K₁)).1
  have : IsLocalRing (integralClosure A K₁) :=
    Stacks.DiscreteValuationRing.Ramification.isLocalRing_of_isIntegral_of_henselianLocalRing A _
  have : FaithfulSMul A K₁ := (faithfulSMul_iff_algebraMap_injective A K₁).mpr (by
    rw [IsScalarTower.algebraMap_eq A K K₁]
    exact (algebraMap K K₁).injective.comp (IsFractionRing.injective A K))
  have : FaithfulSMul A (integralClosure A K₁) :=
    (faithfulSMul_iff_algebraMap_injective A _).mpr fun x y h =>
      FaithfulSMul.algebraMap_injective A K₁ (congrArg Subtype.val h)
  have : IsDiscreteValuationRing (integralClosure A K₁) :=
    Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_of_isIntegral A _
  have : IsDomain C := e.toMulEquiv.isDomain _
  exact ⟨this, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm⟩

private theorem finite_maximalSpectrum_of_isIntegral_of_quasiFinite
    (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Algebra.QuasiFinite R S] : Finite (MaximalSpectrum S) := by
  have := (Algebra.QuasiFinite.finite_primesOver (S := S)
    (IsLocalRing.maximalIdeal R)).to_subtype
  let f : MaximalSpectrum S → (IsLocalRing.maximalIdeal R).primesOver S := fun q =>
    ⟨q.asIdeal, inferInstance, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩⟩
  exact Finite.of_injective f fun x y h => MaximalSpectrum.ext (congrArg Subtype.val h)

private theorem isFiniteProductOfDiscreteValuationRings_of_equiv
    {R : Type*} [CommRing R] {n : ℕ} (hn : 0 < n) (D : Fin n → Type*)
    [∀ i, CommRing (D i)] [∀ i, IsDomain (D i)] [∀ i, IsDiscreteValuationRing (D i)]
    (e : R ≃+* ∀ i, D i) : IsFiniteProductOfDiscreteValuationRings R := by
  classical
  let f (i : Fin n) : R →+* D i := (Pi.evalRingHom D i).comp e.toRingHom
  have hf (i) : Function.Surjective (f i) := fun x => ⟨e.symm (Pi.single i x), by simp [f]⟩
  let q (i : Fin n) : (R ⧸ RingHom.ker (f i)) ≃+* D i :=
    RingHom.quotientKerEquivOfSurjective (hf i)
  have hdom (i : Fin n) : IsDomain (R ⧸ RingHom.ker (f i)) :=
    (q i).toMulEquiv.isDomain _
  have hdvr (i : Fin n) : IsDiscreteValuationRing (R ⧸ RingHom.ker (f i)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (q i).symm
  exact ⟨n, (fun i => R ⧸ RingHom.ker (f i)), inferInstance, hdom, hdvr, hn,
    ⟨e.trans (RingEquiv.piCongrRight fun i => (q i).symm)⟩⟩

private theorem isFiniteProductOfDiscreteValuationRings_integralClosure
    (B L S C : Type*) [CommRing B] [Field L] [CommRing S] [CommRing C]
    [IsDomain B] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra B L] [IsFractionRing B L]
    [Algebra L S] [Algebra B S] [IsScalarTower B L S]
    [Module.Finite L S] [IsReduced S] [Nontrivial S] [Algebra B C]
    (eC : C ≃ₐ[B] integralClosure B S) : IsFiniteProductOfDiscreteValuationRings C := by
  obtain ⟨n, I, hI, hn, ⟨e⟩⟩ := exists_algEquiv_pi_integralClosure B L S C eC
  let : ∀ i, Field (S ⧸ I i) := fun i => Ideal.Quotient.field (I i)
  have : ∀ i, IsDiscreteValuationRing (integralClosure B (S ⧸ I i)) := fun i =>
    (isDiscreteValuationRing_integralClosure_of_henselianLocalRing
      B L (S ⧸ I i) (integralClosure B (S ⧸ I i)) AlgEquiv.refl).2
  exact isFiniteProductOfDiscreteValuationRings_of_equiv (hn inferInstance)
    (fun i => integralClosure B (S ⧸ I i)) e.toRingEquiv

private theorem isNonemptyFiniteProductOfFiniteSeparableFieldExtensions_of_formallyEtale
    (F : Type uL) (R : Type uR) [Field F] [CommRing R]
    [Algebra F R] [Module.Finite F R] [Nontrivial R] [IsReduced R]
    [Algebra.FormallyEtale F R] :
    IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions F R := by
  obtain ⟨n, I, hI, hn, ⟨e⟩⟩ := exists_algEquiv_pi_quotient_of_finite F R
  let : ∀ i, Field (R ⧸ I i) := fun i => Ideal.Quotient.field (I i)
  have hsep : ∀ i, Algebra.IsSeparable F (ULift.{uL} (R ⧸ I i)) := fun i =>
    AlgEquiv.Algebra.isSeparable (ULift.algEquiv (R := F) (A := R ⧸ I i)).symm
  exact ⟨n, fun i => ULift.{uL} (R ⧸ I i), fun i => inferInstance, fun i => inferInstance,
    fun i => inferInstance, hsep, hn inferInstance,
    ⟨e.trans (AlgEquiv.piCongrRight fun _ => ULift.algEquiv.symm)⟩⟩

private theorem finite_integralClosure_of_formallyEtale
    (B L S C : Type*) [CommRing B] [Field L] [CommRing S] [CommRing C]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra B L] [IsFractionRing B L]
    [Algebra L S] [Algebra B S] [IsScalarTower B L S]
    [Module.Finite L S] [IsReduced S] [Algebra.FormallyEtale L S] [Algebra B C]
    (eC : C ≃ₐ[B] integralClosure B S) : Module.Finite B C := by
  obtain ⟨n, I, hI, -, ⟨e⟩⟩ := exists_algEquiv_pi_integralClosure B L S C eC
  let : ∀ i, Field (S ⧸ I i) := fun i => Ideal.Quotient.field (I i)
  have hsep : ∀ i, Algebra.IsSeparable L (S ⧸ I i) := fun i => inferInstance
  have hfin : ∀ i, Module.Finite B (integralClosure B (S ⧸ I i)) := fun i =>
    IsIntegralClosure.finite B L (S ⧸ I i) _
  exact Module.Finite.equiv e.symm.toLinearEquiv

private theorem finite_integralClosure_of_isNagataRing
    (R : Type uA) (K S C : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [CommRing S] [CommRing C]
    [Algebra K S] [Algebra R S] [IsScalarTower R K S]
    [Module.Finite K S] [IsReduced S] [Algebra R C]
    (eC : C ≃ₐ[R] integralClosure R S) (hR : IsNagataRing R) : Module.Finite R C := by
  have : IsNoetherianRing R := hR.1
  have : Small.{uA} K := small_of_injective (FractionRing.algEquiv R K).symm.injective
  have : Small.{uA} S := Module.Finite.small K S
  let e : Shrink.{uA} S ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.EssFiniteType R K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  have : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R K S
  have : Algebra.EssFiniteType R (Shrink.{uA} S) :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mpr inferInstance
  have : IsReduced (Shrink.{uA} S) := isReduced_of_injective e e.injective
  have : Module.Finite R (integralClosure R (Shrink.{uA} S)) :=
    IsIntegralClosure.finite_of_essFiniteType_of_isReduced (S := Shrink.{uA} S) hR.2
  exact Module.Finite.equiv (e.mapIntegralClosure.trans eC.symm).toLinearEquiv

private theorem isLocalRing_of_isIntegral_of_pow_mem_range
    (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hpow : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap R S).range) :
    IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, ?_⟩
  intro p hp
  let := hp
  let := hq
  have hpc : p.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal p)
  have hqc : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q)
  ext x
  obtain ⟨n, hn, r, hr⟩ := hpow x
  rw [← hp.isPrime.pow_mem_iff_mem n hn, ← hq.isPrime.pow_mem_iff_mem n hn, ← hr]
  change r ∈ p.comap (algebraMap R S) ↔ r ∈ q.comap (algebraMap R S)
  rw [hpc, hqc]

private theorem isDiscreteValuationRing_integralClosure_of_isPurelyInseparable
    (A K E C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E] [Module.Finite K E]
    [IsPurelyInseparable K E] [CommRing C] [Algebra A C]
    (e : C ≃ₐ[A] integralClosure A E) : ∃ _ : IsDomain C, IsDiscreteValuationRing C := by
  have : IsDedekindDomain (integralClosure A E) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      A K E (integralClosure A E)).1
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have : IsLocalRing (integralClosure A E) :=
    isLocalRing_of_isIntegral_of_pow_mem_range A _ fun x => by
      obtain ⟨n, k, hk⟩ := IsPurelyInseparable.pow_mem K p (x : E)
      have hkint : IsIntegral A k :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K E)
          (algebraMap K E).injective).mp (by simpa [hk] using x.2.pow (p ^ n))
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkint
      refine ⟨p ^ n, pow_pos (expChar_pos K p) _, a, ?_⟩
      apply Subtype.ext
      change algebraMap A E a = (x : E) ^ p ^ n
      rw [IsScalarTower.algebraMap_apply A K E, ha, hk]
  have : FaithfulSMul A (integralClosure A E) :=
    (faithfulSMul_iff_algebraMap_injective A _).mpr fun x y h =>
      IsFractionRing.injective A K ((algebraMap K E).injective (by
        simpa [← IsScalarTower.algebraMap_apply A K E] using congrArg Subtype.val h))
  have : IsDiscreteValuationRing (integralClosure A E) :=
    Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_of_isIntegral A _
  have : IsDomain C := e.toMulEquiv.isDomain _
  exact ⟨this, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm⟩

private theorem tensorProduct_pow_mem_range
    (K L E : Type*) [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [IsPurelyInseparable K E] (p : ℕ) [ExpChar K p] :
    ∀ z : L ⊗[K] E, ∃ n : ℕ, z ^ p ^ n ∈ (algebraMap L (L ⊗[K] E)).range := by
  have : ExpChar (L ⊗[K] E) p :=
    expChar_of_injective_algebraMap (algebraMap K (L ⊗[K] E)).injective p
  have key (l : L) (c : K) :
      (l ⊗ₜ[K] (algebraMap K E c) : L ⊗[K] E) = (algebraMap K L c * l) ⊗ₜ[K] 1 := by
    rw [Algebra.algebraMap_eq_smul_one (R := K) (A := E),
      Algebra.algebraMap_eq_smul_one (R := K) (A := L), TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    congr 1
    rw [smul_mul_assoc, one_mul]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul l m =>
      obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K p m
      refine ⟨n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, ← hc, key]
      exact ⟨algebraMap K L c * l ^ p ^ n, rfl⟩
  | add x y hx hy =>
      obtain ⟨a, ea, ha⟩ := hx
      obtain ⟨b, eb, hb⟩ := hy
      refine ⟨max a b, ?_⟩
      rw [add_pow_expChar_pow x y p (max a b)]
      have hxx : x ^ p ^ max a b ∈ (algebraMap L (L ⊗[K] E)).range := by
        rw [← Nat.add_sub_cancel' (le_max_left a b), pow_add, pow_mul]
        exact pow_mem (RingHom.mem_range.mpr ⟨ea, ha⟩) _
      have hyy : y ^ p ^ max a b ∈ (algebraMap L (L ⊗[K] E)).range := by
        rw [← Nat.add_sub_cancel' (le_max_right a b), pow_add, pow_mul]
        exact pow_mem (RingHom.mem_range.mpr ⟨eb, hb⟩) _
      exact Subring.add_mem _ hxx hyy

private theorem isField_of_pow_mem_range
    (F R : Type*) [Field F] [CommRing R] [Nontrivial R] [IsReduced R] [Algebra F R]
    (hpow : ∀ x : R, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap F R).range) : IsField R where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    obtain ⟨n, hn, a, ha⟩ := hpow x
    have ha0 : a ≠ 0 := fun ha0 => hx (IsNilpotent.eq_zero ⟨n, by simpa [ha0] using ha.symm⟩)
    refine ⟨x ^ (n - 1) * algebraMap F R a⁻¹, ?_⟩
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, ← ha, ← map_mul,
      mul_inv_cancel₀ ha0, map_one]

/-- If `x` is a nonzero nonunit of a discrete valuation ring `R`, then the fraction field `K`
of `R` is the localization of `R` away from `x`. -/
theorem isLocalization_away_of_ne_zero_of_not_isUnit
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : x ≠ 0) (hxu : ¬ IsUnit x) : IsLocalization.Away x K := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hxm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hm : 0 < m := Nat.pos_of_ne_zero fun hm0 => hxu (by simp [hxm, hm0])
  have hπx : π ∣ x := by
    rw [hxm]
    exact dvd_mul_of_dvd_right (dvd_pow_self π (Nat.ne_of_gt hm)) _
  apply (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers x)
    (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · rintro y ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hx)
  · intro y hy
    obtain ⟨n, v, hyv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hy) hπ
    refine ⟨x ^ n, ⟨n, rfl⟩, ?_⟩
    obtain ⟨z, hz⟩ := hπx
    refine ⟨↑v⁻¹ * z ^ n, ?_⟩
    rw [hz, hyv, mul_pow]
    calc
      π ^ n * z ^ n = (π ^ n * z ^ n) * (↑v * ↑v⁻¹) := by simp
      _ = ↑v * π ^ n * (↑v⁻¹ * z ^ n) := by ring

private theorem integralClosures_isDedekindDomain_and_finiteness
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (L₁ : Type uL₁) (A₁ : Type uA₁) (B₁ : Type uB₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [CommRing L₁] [CommRing A₁] [CommRing B₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A K] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁] [Algebra K L₁] [Algebra B L₁] [Algebra L L₁]
    [Algebra A A₁] [Algebra B B₁]
    [IsScalarTower A K K₁] [IsScalarTower K L L₁] [IsScalarTower B L L₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
    (eA₁ : A₁ ≃ₐ[A] integralClosure A K₁)
    (eB₁ : B₁ ≃ₐ[B] integralClosure B L₁)
    (eL₁_left : ∀ x : L,
      eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x)) :
    IsNonemptyFiniteProductOfFiniteFieldExtensions L L₁ ∧
      IsDedekindDomain A₁ ∧ IsFiniteProductOfDedekindDomains B₁ ∧
      Finite (MaximalSpectrum A₁) ∧ Nonempty (MaximalSpectrum A₁) ∧
      (HenselianLocalRing A → ∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
      (IsAdicComplete (IsLocalRing.maximalIdeal A) A →
        ∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
      (HenselianLocalRing B → IsFiniteProductOfDiscreteValuationRings B₁) ∧
      (IsAdicComplete (IsLocalRing.maximalIdeal B) B →
        IsFiniteProductOfDiscreteValuationRings B₁) ∧
      (IsPurelyInseparable K K₁ →
        (∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
        (∃ _ : IsDomain B₁, IsDiscreteValuationRing B₁)) ∧
      (Algebra.IsSeparable K K₁ →
        IsReduced (L ⊗[K] K₁) ∧
        IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions L L₁ ∧
        Module.Finite A A₁ ∧ Module.Finite B B₁) ∧
      (IsNagataRing A → Module.Finite A A₁) ∧
      (IsNagataRing B → Module.Finite B B₁) := by
  classical
  let T := L ⊗[K] K₁
  let Q := T ⧸ nilradical T
  let e : L₁ ≃ₐ[L] Q :=
    { eL₁.toRingEquiv with commutes' := eL₁_left }
  have : Nontrivial T := inferInstance
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (by
    simp [nilradical, Ideal.radical_eq_top])
  have : IsReduced Q := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : Nontrivial L₁ := e.toEquiv.nontrivial
  have : IsReduced L₁ := isReduced_of_injective e e.injective
  have : Module.Finite L Q := inferInstance
  have : Module.Finite L L₁ := Module.Finite.equiv e.symm.toLinearEquiv
  have hA : IsDedekindDomain A₁ := isDedekindDomain_integralClosure_equiv A K K₁ A₁ eA₁
  have hB := isFiniteProductOfDedekindDomains_integralClosure B L L₁ B₁ eB₁
  have : Nontrivial A₁ := eA₁.toEquiv.nontrivial
  have : Algebra.IsIntegral A A₁ := ⟨fun x =>
    (isIntegral_algHom_iff eA₁.toAlgHom eA₁.injective).mp (Algebra.IsIntegral.isIntegral (eA₁ x))⟩
  have : Algebra.QuasiFinite A (integralClosure A K₁) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      A K K₁ (integralClosure A K₁)).2.2
  have : Algebra.QuasiFinite A A₁ :=
    Algebra.QuasiFinite.of_surjective_algHom eA₁.symm.toAlgHom eA₁.symm.surjective
  have hFA : Finite (MaximalSpectrum A₁) :=
    finite_maximalSpectrum_of_isIntegral_of_quasiFinite A A₁
  have hHA : HenselianLocalRing A → ∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁ := fun _ =>
    isDiscreteValuationRing_integralClosure_of_henselianLocalRing A K K₁ A₁ eA₁
  have hHB : HenselianLocalRing B → IsFiniteProductOfDiscreteValuationRings B₁ := fun _ =>
    isFiniteProductOfDiscreteValuationRings_integralClosure B L L₁ B₁ eB₁
  have hsep : Algebra.IsSeparable K K₁ →
      IsReduced (L ⊗[K] K₁) ∧
      IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions L L₁ ∧
      Module.Finite A A₁ ∧ Module.Finite B B₁ := by
    intro
    have : Algebra.FormallyEtale K K₁ := Algebra.FormallyEtale.of_isSeparable K K₁
    have : Algebra.FormallyEtale L T := inferInstance
    have : IsReduced T := Algebra.FormallyUnramified.isReduced_of_field L T
    have : Algebra.FormallyUnramified L Q := inferInstance
    have : Algebra.FormallyEtale L Q :=
      Algebra.FormallyEtale.of_formallyUnramified_of_field L Q
    have : Algebra.FormallyEtale L L₁ := Algebra.FormallyEtale.of_equiv e.symm
    have : Module.Finite A (integralClosure A K₁) := IsIntegralClosure.finite A K K₁ _
    exact ⟨inferInstance,
      isNonemptyFiniteProductOfFiniteSeparableFieldExtensions_of_formallyEtale L L₁,
      Module.Finite.equiv eA₁.symm.toLinearEquiv,
      finite_integralClosure_of_formallyEtale B L L₁ B₁ eB₁⟩
  have hpi : IsPurelyInseparable K K₁ →
      (∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
      (∃ _ : IsDomain B₁, IsDiscreteValuationRing B₁) := by
    intro
    obtain ⟨p, hp⟩ := ExpChar.exists K
    have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
    have hpow : ∀ z : L₁, ∃ n : ℕ, z ^ p ^ n ∈ (algebraMap L L₁).range := by
      intro z
      obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (eL₁ z)
      obtain ⟨n, a, ha⟩ := tensorProduct_pow_mem_range K L K₁ p t
      refine ⟨n, a, eL₁.injective ?_⟩
      rw [eL₁_left, map_pow, ← ht]
      change Ideal.Quotient.mk _ (algebraMap L T a) = (Ideal.Quotient.mk _ t) ^ p ^ n
      rw [← map_pow, ha]
    let : Field L₁ := (isField_of_pow_mem_range L L₁ fun z => by
      obtain ⟨n, a, ha⟩ := hpow z
      exact ⟨p ^ n, pow_pos (expChar_pos K p) _, a, ha⟩).toField
    have : IsPurelyInseparable L L₁ := (isPurelyInseparable_iff_pow_mem L p).mpr hpow
    exact ⟨isDiscreteValuationRing_integralClosure_of_isPurelyInseparable A K K₁ A₁ eA₁,
      isDiscreteValuationRing_integralClosure_of_isPurelyInseparable B L L₁ B₁ eB₁⟩
  exact ⟨isNonemptyFiniteProductOfFiniteFieldExtensions_of_finite_of_isReduced L L₁,
    hA, hB, hFA, inferInstance,
    hHA, fun _ => hHA (henselianLocalRing_of_henselianRing A),
    hHB, fun _ => hHB (henselianLocalRing_of_henselianRing B), hpi, hsep,
    fun h => finite_integralClosure_of_isNagataRing A K K₁ A₁ eA₁ h,
    fun h => finite_integralClosure_of_isNagataRing B L L₁ B₁ eB₁ h⟩

/-- A one-dimensional domain with finitely many maximal ideals has finite spectrum. -/
theorem finite_primeSpectrum_of_dimensionLEOne
    (R : Type*) [CommRing R] [IsDomain R] [Ring.DimensionLEOne R]
    [Finite (MaximalSpectrum R)] : Finite (PrimeSpectrum R) := by
  classical
  let f : PrimeSpectrum R → Option (MaximalSpectrum R) := fun p =>
    if h : p.asIdeal = ⊥ then none else some ⟨p.asIdeal, p.isPrime.isMaximal h⟩
  apply Finite.of_injective f
  intro p q h
  by_cases hp : p.asIdeal = ⊥ <;> by_cases hq : q.asIdeal = ⊥
  · exact PrimeSpectrum.ext (hp.trans hq.symm)
  · simp [f, hp, hq] at h
  · simp [f, hp, hq] at h
  · have he := Option.some.inj (show some (⟨p.asIdeal, p.isPrime.isMaximal hp⟩ :
        MaximalSpectrum R) = some ⟨q.asIdeal, q.isPrime.isMaximal hq⟩ by simpa [f, hp, hq] using h)
    exact PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal he)

private theorem isDedekindDomain_atPrime_of_pi
    (R : Type uR) [CommRing R] {n : ℕ} (D : Fin n → Type uR)
    [∀ i, CommRing (D i)] [∀ i, IsDedekindDomain (D i)]
    (e : R ≃+* ∀ i, D i) (q : Ideal R) [q.IsPrime] :
    IsDedekindDomain (Localization.AtPrime q) := by
  classical
  obtain ⟨⟨i, p⟩, hp⟩ := (PrimeSpectrum.sigmaToPi_bijective D).surjective
    (PrimeSpectrum.comap e.symm.toRingHom ⟨q, inferInstance⟩)
  let f : R →+* D i := (Pi.evalRingHom D i).comp e.toRingHom
  have hf : Function.Surjective f := fun x => ⟨e.symm (Pi.single i x), by simp [f]⟩
  have hq : q = p.asIdeal.comap f := by
    have he := congrArg (fun x : PrimeSpectrum (∀ i, D i) =>
      (PrimeSpectrum.comap e.toRingHom x).asIdeal) hp
    simpa [f, PrimeSpectrum.sigmaToPi_apply, Ideal.comap_comap] using he.symm
  let g := Localization.localRingHom q p.asIdeal f hq
  have hg : Function.Bijective g := by
    refine ⟨?_, by subst q; exact RingHom.surjective_localRingHom_of_surjective f hf p.asIdeal⟩
    refine IsLocalization.injective_of_map_algebraMap_zero (M := q.primeCompl)
      (Localization.AtPrime q) g ?_
    intro x hx
    rw [Localization.localRingHom_to_map] at hx
    have hx0 : f x = 0 := (IsLocalization.injective (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl_le_nonZeroDivisors)
      (by simpa using hx)
    apply (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).mpr
    refine ⟨⟨e.symm (Pi.single i 1), ?_⟩, ?_⟩
    · change e.symm (Pi.single i 1) ∉ q
      rw [hq]
      change f (e.symm (Pi.single i 1)) ∉ p.asIdeal
      simpa [f] using p.isPrime.one_notMem
    · apply e.injective
      ext j
      by_cases hj : j = i
      · subst j
        simpa [f] using hx0
      · simp [Pi.single_eq_of_ne hj]
  exact isDedekindDomain_of_ringEquiv (RingEquiv.ofBijective g hg)

private theorem finite_primeSpectrum_integralClosure
    (B L S C : Type*) [CommRing B] [Field L] [CommRing S] [CommRing C]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra B L] [IsFractionRing B L]
    [Algebra L S] [Algebra B S] [IsScalarTower B L S]
    [Module.Finite L S] [IsReduced S] [Algebra B C]
    (eC : C ≃ₐ[B] integralClosure B S) : Finite (PrimeSpectrum C) := by
  obtain ⟨n, I, hI, -, ⟨e⟩⟩ := exists_algEquiv_pi_integralClosure B L S C eC
  let : ∀ i, Field (S ⧸ I i) := fun i => Ideal.Quotient.field (I i)
  have hD : ∀ i, IsDedekindDomain (integralClosure B (S ⧸ I i)) := fun i =>
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      B L (S ⧸ I i) (integralClosure B (S ⧸ I i))).1
  have hQ : ∀ i, Algebra.QuasiFinite B (integralClosure B (S ⧸ I i)) := fun i =>
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      B L (S ⧸ I i) (integralClosure B (S ⧸ I i))).2.2
  have hF : ∀ i, Finite (MaximalSpectrum (integralClosure B (S ⧸ I i))) := fun i =>
    finite_maximalSpectrum_of_isIntegral_of_quasiFinite B _
  have hP : ∀ i, Finite (PrimeSpectrum (integralClosure B (S ⧸ I i))) := fun i =>
    finite_primeSpectrum_of_dimensionLEOne _
  have : Finite (PrimeSpectrum (∀ i, integralClosure B (S ⧸ I i))) :=
    Finite.of_surjective _ (PrimeSpectrum.sigmaToPi_bijective _).surjective
  exact Finite.of_equiv _ (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).toEquiv.symm

private theorem exists_tensorProduct_localization
    (A B K L E C : Type*) [CommRing A] [CommRing B] [Field K] [Field L] [Field E]
    [CommRing C] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K E] [Algebra A E] [Algebra A C]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K E]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K E]
    (eC : C ≃ₐ[A] integralClosure A E) (π : A) (hπ : π ≠ 0) (hπu : ¬ IsUnit π) :
    ∃ e : Localization.Away (algebraMap A (B ⊗[A] C) π) ≃+* (L ⊗[K] E),
      (∀ b : B, e (algebraMap (B ⊗[A] C) _
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C) b)) =
        (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] E) (algebraMap B L b)) ∧
      (∀ c : C, e (algebraMap (B ⊗[A] C) _
        ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c)) =
        (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) (eC c).1) := by
  let a : C →ₐ[A] E := (integralClosure A E).val.comp eC.toAlgHom
  let : Algebra C E := a.toAlgebra
  have : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  have : IsIntegralClosure C A E :=
    { algebraMap_injective := Subtype.val_injective.comp eC.injective
      isIntegral_iff := by
        intro x
        exact ⟨fun hx => ⟨eC.symm ⟨x, hx⟩, by
          change (eC (eC.symm ⟨x, hx⟩)).1 = x
          rw [eC.apply_symm_apply]⟩,
          by rintro ⟨c, rfl⟩; exact (eC c).2⟩ }
  have : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization A K E C
  have : Algebra.IsPushout A C K E :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K C E
  have : Algebra.IsPushout A K C E := Algebra.IsPushout.symm inferInstance
  have : IsLocalization.Away (algebraMap A B π) L :=
    isLocalization_away_of_ne_zero_of_not_isUnit B L
      (by simpa using (FaithfulSMul.algebraMap_injective A B).ne hπ)
      (fun h => hπu (isUnit_of_map_unit (algebraMap A B) π h))
  let V := L ⊗[A] C
  let T := B ⊗[A] C
  let f : T →ₐ[A] V := Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B L) (AlgHom.id A C)
  let : Algebra T V := f.toAlgebra
  have : IsScalarTower B T V := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have hloc := IsLocalization.tensorProduct_tensorProduct A C
    (Submonoid.powers (algebraMap A B π)) L (by
      ext x
      change algebraMap B L 1 ⊗ₜ[A] x = 1 ⊗ₜ[A] x
      rw [map_one])
  have : IsLocalization.Away (algebraMap A T π) V := by
    change IsLocalization (Submonoid.powers (algebraMap A T π)) V
    convert hloc using 1
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    congr 1
  let e₁ := (IsLocalization.algEquiv (Submonoid.powers (algebraMap A T π))
    (Localization.Away (algebraMap A T π)) V).toRingEquiv
  let e₂ : V ≃ₐ[L] L ⊗[K] E :=
    (Algebra.TensorProduct.cancelBaseChange A K L L C).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
        (Algebra.IsPushout.equiv A K C E))
  refine ⟨e₁.trans e₂.toRingEquiv, ?_, ?_⟩
  · intro b
    change e₂ (e₁ (algebraMap T _ (b ⊗ₜ[A] 1))) = _
    rw [show e₁ (algebraMap T _ _) = algebraMap T V _ from
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap A T π))
        (Localization.Away (algebraMap A T π)) V).commutes _]
    change e₂ (algebraMap B L b ⊗ₜ[A] 1) = _
    change (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
      (Algebra.IsPushout.equiv A K C E))
        ((Algebra.TensorProduct.cancelBaseChange A K L L C).symm
          (algebraMap B L b ⊗ₜ[A] 1)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul A K L L C]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, Algebra.IsPushout.equiv_tmul,
      map_one, mul_one]
    rfl
  · intro c
    change e₂ (e₁ (algebraMap T _ (1 ⊗ₜ[A] c))) = _
    rw [show e₁ (algebraMap T _ _) = algebraMap T V _ from
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap A T π))
        (Localization.Away (algebraMap A T π)) V).commutes _]
    change e₂ (algebraMap B L 1 ⊗ₜ[A] c) = _
    rw [map_one]
    change (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
      (Algebra.IsPushout.equiv A K C E))
        ((Algebra.TensorProduct.cancelBaseChange A K L L C).symm (1 ⊗ₜ[A] c)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul A K L L C]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, Algebra.IsPushout.equiv_tmul,
      map_one, one_mul]
    rfl

private theorem isRegular_of_injective_of_isUnit
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {r : R} (hr : IsUnit (f r)) : IsRegular r := by
  apply (Commute.isRegular_iff (fun x => Commute.all r x)).mpr
  intro x y h
  apply hf
  apply hr.mul_left_cancel
  simpa only [← map_mul] using congrArg f h

private theorem isRegular_algebraMap_of_isTorsionFree
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.IsTorsionFree R S] {r : R} (hr : IsRegular r) :
    IsRegular (algebraMap R S r) :=
  (Commute.isRegular_iff fun x => Commute.all _ x).mpr fun _ _ h =>
    hr.smul_right_injective S (by simpa only [Algebra.smul_def] using h)

private theorem injective_localization_comp_of_isRegular
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hreg : ∀ r, r ≠ 0 → IsRegular (f r)) (q : Ideal S) [q.IsPrime] :
    Function.Injective ((algebraMap S (Localization.AtPrime q)).comp f) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  by_contra h
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl
    (Localization.AtPrime q) (f x)).mp hx
  have hs0 : (s : S) = 0 := (hreg x h).right (by simpa using hs)
  exact s.2 (hs0 ▸ q.zero_mem)

private theorem isDiscreteValuationRing_atPrime_of_isDedekindDomain
    (R : Type*) [CommRing R] (q : Ideal R) [q.IsPrime]
    [IsDedekindDomain (Localization.AtPrime q)]
    {r : R} (hr : r ∈ q) (hreg : IsRegular r) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hne : algebraMap R (Localization.AtPrime q) r ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ r).mp h
    have hs0 : (s : R) = 0 := hreg.right (by simpa using hs)
    exact s.2 (hs0 ▸ q.zero_mem)
  have hnunit : ¬ IsUnit (algebraMap R (Localization.AtPrime q) r) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q]
    exact not_not_intro hr
  have hnf : ¬ IsField (Localization.AtPrime q) := by
    intro h
    let := h.toField
    exact hnunit (isUnit_iff_ne_zero.mpr hne)
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 3 1).mp
    (show IsDedekindDomain _ from inferInstance)

/-- The integral closures attached to a finite extension `K₁/K` and an extension of discrete
valuation rings `A → B` have the product, spectral, local, henselian, inseparable, separable,
and Nagata properties listed in Stacks Project, Tag 09EM. -/
@[stacks 09EM]
theorem integralClosures_after_finite_fraction_field_extension
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
    (eB₁_coe : ∀ x : B₁, ((eB₁ x : integralClosure B L₁) : L₁) = algebraMap B₁ L₁ x)
    (hfieldSquare : ∀ x : K, algebraMap L L₁ (algebraMap K L x) =
      algebraMap K₁ L₁ (algebraMap K K₁ x))
    (hringSquare : ∀ x : A₁, algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ ((eA₁ x : integralClosure A K₁) : K₁)) :
    IsNonemptyFiniteProductOfFiniteFieldExtensions L L₁ ∧
      IsDedekindDomain A₁ ∧
      IsFiniteProductOfDedekindDomains B₁ ∧
      (∃ π : A,
        IsLocalRing.maximalIdeal A = Ideal.span {π} ∧
        IsRegular (algebraMap A (B ⊗[A] A₁) π) ∧
        (∃ e : Localization.Away (algebraMap A (B ⊗[A] A₁) π) ≃+* (L ⊗[K] K₁),
          (∀ b : B, e (algebraMap (B ⊗[A] A₁) _
              ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) b)) =
            (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) (algebraMap B L b)) ∧
          (∀ a : A₁, e (algebraMap (B ⊗[A] A₁) _
              ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a)) =
            (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
              ((eA₁ a : integralClosure A K₁) : K₁))) ∧
        ∃ g : (B ⊗[A] A₁) →+* B₁,
          g.IsIntegral ∧ RingHom.ker g ≤ nilradical (B ⊗[A] A₁) ∧
          Function.Surjective (PrimeSpectrum.comap g) ∧
          (∀ b : B, g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) b) =
            algebraMap B B₁ b) ∧
          (∀ a : A₁, g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a) =
            algebraMap A₁ B₁ a)) ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap A₁ B₁)) ∧
      Finite (MaximalSpectrum A₁) ∧
      Nonempty (MaximalSpectrum A₁) ∧
      (∀ p : MaximalSpectrum A₁,
        Finite {q : MaximalSpectrum B₁ //
          q.asIdeal.comap (algebraMap A₁ B₁) = p.asIdeal} ∧
        Nonempty {q : MaximalSpectrum B₁ //
          q.asIdeal.comap (algebraMap A₁ B₁) = p.asIdeal}) ∧
      (∀ p : Ideal A₁, p.IsMaximal →
        ∃ q : Ideal B₁, q.IsMaximal ∧ q.comap (algebraMap A₁ B₁) = p) ∧
      (∀ q : Ideal B₁, q.IsMaximal →
        (q.comap (algebraMap A₁ B₁)).IsMaximal ∧
        ∃ (_ : q.IsPrime) (_ : (q.comap (algebraMap A₁ B₁)).IsPrime),
          (∃ _ : IsDomain (Localization (q.comap (algebraMap A₁ B₁)).primeCompl),
            IsDiscreteValuationRing (Localization (q.comap (algebraMap A₁ B₁)).primeCompl)) ∧
          (∃ _ : IsDomain (Localization q.primeCompl),
            IsDiscreteValuationRing (Localization q.primeCompl)) ∧
          ∃ φ : Localization (q.comap (algebraMap A₁ B₁)).primeCompl →+*
              Localization q.primeCompl,
            Function.Injective φ ∧ IsLocalHom φ ∧
              ∀ x : A₁, φ (algebraMap A₁ _ x) = algebraMap B₁ _ (algebraMap A₁ B₁ x)) ∧
      (HenselianLocalRing A → ∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
      (IsAdicComplete (IsLocalRing.maximalIdeal A) A →
        ∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
      (HenselianLocalRing B →
        IsFiniteProductOfDiscreteValuationRings B₁) ∧
      (IsAdicComplete (IsLocalRing.maximalIdeal B) B →
        IsFiniteProductOfDiscreteValuationRings B₁) ∧
      (IsPurelyInseparable K K₁ →
        (∃ _ : IsDomain A₁, IsDiscreteValuationRing A₁) ∧
        (∃ _ : IsDomain B₁, IsDiscreteValuationRing B₁)) ∧
      (Algebra.IsSeparable K K₁ →
        IsReduced (L ⊗[K] K₁) ∧
        IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions L L₁ ∧
        Module.Finite A A₁ ∧ Module.Finite B B₁) ∧
      (IsNagataRing A → Module.Finite A A₁) ∧
      (IsNagataRing B → Module.Finite B B₁) := by
  classical
  -- The commuting square of fields is also a consequence of the two scalar towers through `L₁`.
  have := hfieldSquare
  obtain ⟨hfields, hA, hB, hFA, hNA, hHA, hCA, hHB, hCB, hPI, hSep, hNagA, hNagB⟩ :=
    integralClosures_isDedekindDomain_and_finiteness A B K L K₁ L₁ A₁ B₁
      eL₁ eA₁ eB₁ eL₁_left
  have hBT : Function.Injective (algebraMap B₁ L₁) := fun x y h =>
    eB₁.injective (Subtype.ext (by simpa only [eB₁_coe] using h))
  have : Nontrivial ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by simp [nilradical, Ideal.radical_eq_top])
  have : Nontrivial L₁ := eL₁.toEquiv.nontrivial
  have hreg (a : A₁) (ha : a ≠ 0) : IsRegular (algebraMap A₁ B₁ a) := by
    apply isRegular_of_injective_of_isUnit (algebraMap B₁ L₁) hBT
    rw [hringSquare]
    refine IsUnit.map (algebraMap K₁ L₁) (isUnit_iff_ne_zero.mpr fun h => ha (eA₁.injective ?_))
    exact Subtype.ext (by simpa using h)
  have : FaithfulSMul A K₁ := (faithfulSMul_iff_algebraMap_injective A K₁).mpr (by
    rw [IsScalarTower.algebraMap_eq A K K₁]
    exact (algebraMap K K₁).injective.comp (IsFractionRing.injective A K))
  have : FaithfulSMul A A₁ := (faithfulSMul_iff_algebraMap_injective A A₁).mpr (by
    intro x y h
    apply FaithfulSMul.algebraMap_injective A K₁
    simpa using congrArg (fun a : A₁ => (eA₁ a).1) h)
  have : Algebra.IsIntegral B B₁ := ⟨fun x =>
    (isIntegral_algHom_iff eB₁.toAlgHom eB₁.injective).mp (Algebra.IsIntegral.isIntegral (eB₁ x))⟩
  have : Module.IsTorsionFree A₁ B₁ := Module.IsTorsionFree.of_smul_eq_zero (by
    intro a b h
    exact or_iff_not_imp_left.mpr fun ha => (hreg a ha).left (by simpa [Algebra.smul_def] using h))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmπ : IsLocalRing.maximalIdeal A = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπA : algebraMap A A₁ π ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective A A₁).ne hπ.ne_zero
  have hmax (q : Ideal B₁) [q.IsMaximal] :
      (q.comap (algebraMap A₁ B₁)).IsMaximal ∧ algebraMap A A₁ π ∈ q.comap (algebraMap A₁ B₁) := by
    have hqB : q.comap (algebraMap B B₁) = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q)
    have hqA : q.comap (algebraMap A B₁) = IsLocalRing.maximalIdeal A := by
      rw [IsScalarTower.algebraMap_eq A B B₁, ← Ideal.comap_comap, hqB,
        IsLocalRing.maximalIdeal_comap]
    have hmem : algebraMap A A₁ π ∈ q.comap (algebraMap A₁ B₁) := by
      change algebraMap A₁ B₁ (algebraMap A A₁ π) ∈ q
      rw [← IsScalarTower.algebraMap_apply A A₁ B₁]
      change π ∈ q.comap (algebraMap A B₁)
      rw [hqA, hmπ]
      exact Ideal.subset_span (Set.mem_singleton π)
    exact ⟨(q.comap_isPrime _).isMaximal (fun h => hπA (by simpa [h] using hmem)), hmem⟩
  let T := B ⊗[A] A₁
  let U := L ⊗[K] K₁
  have : Module.Flat A T := inferInstance
  have hπT : IsRegular (algebraMap A T π) :=
    isRegular_algebraMap_of_isTorsionFree (isRegular_iff_ne_zero.mpr hπ.ne_zero)
  obtain ⟨e, heB, heA⟩ := exists_tensorProduct_localization A B K L K₁ A₁ eA₁ π
    hπ.ne_zero hπ.not_isUnit
  let c : T →+* U := e.toRingHom.comp (algebraMap T _)
  have hc : Function.Injective c := e.injective.comp (IsLocalization.injectiveₛ
    (M := Submonoid.powers (algebraMap A T π))
    (Localization.Away (algebraMap A T π)) (by
    rintro _ ⟨n, rfl⟩
    exact hπT.pow n))
  let g : T →ₐ[A] B₁ := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom A B B₁) (IsScalarTower.toAlgHom A A₁ B₁) (fun _ _ => Commute.all _ _)
  have hgB (b : B) : g (b ⊗ₜ[A] 1) = algebraMap B B₁ b := by
    change algebraMap B B₁ b * algebraMap A₁ B₁ 1 = _
    rw [map_one, mul_one]
  have hgA (a : A₁) : g (1 ⊗ₜ[A] a) = algebraMap A₁ B₁ a := by
    change algebraMap B B₁ 1 * algebraMap A₁ B₁ a = _
    rw [map_one, one_mul]
  have hg : g.toRingHom.IsIntegral := by
    apply RingHom.IsIntegral.tower_top
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] T).toRingHom
    convert (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral B B₁)) using 1
    ext b
    exact hgB b
  have hcg : (Ideal.Quotient.mk (nilradical U)).comp c =
      eL₁.toRingHom.comp ((algebraMap B₁ L₁).comp g.toRingHom) := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext b
      change Ideal.Quotient.mk _ (c (b ⊗ₜ[A] 1)) =
        eL₁ (algebraMap B₁ L₁ (g (b ⊗ₜ[A] 1)))
      calc
        _ = Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeLeft : L →ₐ[K] U)
            (algebraMap B L b)) := congrArg (Ideal.Quotient.mk _) (heB b)
        _ = _ := by
          rw [hgB, ← IsScalarTower.algebraMap_apply B B₁ L₁,
            IsScalarTower.algebraMap_apply B L L₁, eL₁_left]
    · ext a
      change Ideal.Quotient.mk _ (c (1 ⊗ₜ[A] a)) =
        eL₁ (algebraMap B₁ L₁ (g (1 ⊗ₜ[A] a)))
      calc
        _ = Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] U)
            (eA₁ a).1) := congrArg (Ideal.Quotient.mk _) (heA a)
        _ = _ := by rw [hgA, hringSquare, eL₁_right]
  have hker : RingHom.ker g.toRingHom ≤ nilradical T := by
    intro x hx
    have hz : Ideal.Quotient.mk (nilradical U) (c x) = 0 := by
      have := DFunLike.congr_fun hcg x
      change g x = 0 at hx
      change Ideal.Quotient.mk _ (c x) = eL₁ (algebraMap B₁ L₁ (g x)) at this
      simpa only [hx, map_zero] using this
    have hn : IsNilpotent (c x) := mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    exact mem_nilradical.mpr ((IsNilpotent.map_iff hc).mp hn)
  have hgs : Function.Surjective (PrimeSpectrum.comap g.toRingHom) := by
    let : Algebra T B₁ := g.toAlgebra
    have : Algebra.IsIntegral T B₁ := ⟨hg⟩
    intro p
    obtain ⟨q, _, hq, heq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B₁)
      p.asIdeal ⊥ (hker.trans (nilradical_le_prime p.asIdeal))
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext heq⟩
  have hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap A₁ B₁)) := by
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hs : Function.Surjective (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] T).toRingHom) := by
      let d := Algebra.TensorProduct.comm A B A₁
      have he : d.toRingHom.comp
          (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] T).toRingHom =
          algebraMap A₁ (A₁ ⊗[A] B) := by ext; simp [d]
      have hs' : Function.Surjective (PrimeSpectrum.comap (algebraMap A₁ (A₁ ⊗[A] B))) :=
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
      rw [← he, PrimeSpectrum.comap_comp] at hs'
      exact Function.Surjective.of_comp hs'
    have he : g.toRingHom.comp (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] T).toRingHom =
        algebraMap A₁ B₁ := by
      ext x
      exact hgA x
    rw [← he, PrimeSpectrum.comap_comp]
    exact hs.comp hgs
  have hlift (p : Ideal A₁) (hp : p.IsMaximal) :
      ∃ q : Ideal B₁, q.IsMaximal ∧ q.comap (algebraMap A₁ B₁) = p := by
    obtain ⟨q, heq⟩ := hspec ⟨p, hp.isPrime⟩
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
    refine ⟨m, hm, ?_⟩
    have := congrArg PrimeSpectrum.asIdeal heq
    exact (hp.eq_of_le ((hmax m).1.ne_top) (by
      change q.asIdeal.comap (algebraMap A₁ B₁) = p at this
      rw [← this]
      exact Ideal.comap_mono hqm)).symm
  have : IsReduced ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : IsReduced L₁ := isReduced_of_injective eL₁ eL₁.injective
  let eL : L₁ ≃ₐ[L] (U ⧸ nilradical U) := { eL₁.toRingEquiv with commutes' := eL₁_left }
  have : Module.Finite L L₁ := Module.Finite.equiv eL.symm.toLinearEquiv
  have : Finite (PrimeSpectrum B₁) := finite_primeSpectrum_integralClosure B L L₁ B₁ eB₁
  have : Finite (MaximalSpectrum B₁) := Finite.of_injective MaximalSpectrum.toPrimeSpectrum
    (fun _ _ h => MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal h))
  refine ⟨hfields, hA, hB, ⟨π, hmπ, hπT, ⟨e, heB, heA⟩,
    g.toRingHom, hg, hker, hgs, hgB, hgA⟩, hspec, hFA, hNA, ?_, hlift, ?_,
    hHA, hCA, hHB, hCB, hPI, hSep, hNagA, hNagB⟩
  · intro p
    obtain ⟨q, hq, heq⟩ := hlift p.asIdeal p.isMaximal
    exact ⟨inferInstance, ⟨⟨⟨q, hq⟩, heq⟩⟩⟩
  · intro q hq
    let p := q.comap (algebraMap A₁ B₁)
    obtain ⟨hp, hm⟩ := hmax q
    have : IsDedekindDomain (Localization.AtPrime q) := by
      obtain ⟨n, D, hD, hDed, _, ⟨d⟩⟩ := hB
      exact isDedekindDomain_atPrime_of_pi B₁ D d q
    have hdq : IsDiscreteValuationRing (Localization.AtPrime q) :=
      isDiscreteValuationRing_atPrime_of_isDedekindDomain B₁ q hm (hreg _ hπA)
    have hdp : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A₁ (P := p)
        (fun h => hπA (by
          have hm' : algebraMap A A₁ π ∈ p := hm
          rwa [h, Ideal.mem_bot] at hm')) _
    let φ := Localization.localRingHom p q (algebraMap A₁ B₁) rfl
    have hφ : Function.Injective φ := by
      apply IsLocalization.injective_of_map_algebraMap_zero (M := p.primeCompl)
        (Localization.AtPrime p) φ
      intro x hx
      rw [Localization.localRingHom_to_map] at hx
      have hx0 := injective_localization_comp_of_isRegular (algebraMap A₁ B₁) hreg q
        (show ((algebraMap B₁ (Localization.AtPrime q)).comp (algebraMap A₁ B₁)) x =
          ((algebraMap B₁ (Localization.AtPrime q)).comp (algebraMap A₁ B₁)) 0 by simpa using hx)
      simp [hx0]
    exact ⟨hp, inferInstance, inferInstance, ⟨inferInstance, hdp⟩, ⟨inferInstance, hdq⟩,
      φ, hφ, inferInstance, fun x => Localization.localRingHom_to_map p q _ rfl x⟩

end IsDiscreteValuationRing
