module

public import Mathlib
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Flat
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.CompleteIntersection.BaseChange
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Etale.Height
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Permanence of local properties under étale maps

Let `A → B` be an étale ring map and `𝔮 ⊂ B` a prime lying over `𝔭 ⊂ A`. Then `A_𝔭` is
Noetherian, resp. regular, if and only if `B_𝔮` is; the Noetherian statement holds more generally
for flat ring maps of finite type. An étale algebra over a Dedekind domain is a finite product of
Dedekind domains, and its localization at a maximal ideal with nonzero contraction to the base
is a discrete valuation ring.

## Main results

* `isNoetherianRing_localization_iff_of_flat_of_finiteType`: for a flat finite type map, `A_𝔭` is
  Noetherian if and only if `B_𝔮` is.
* `isNoetherianRing_localization_iff_of_etale`: the same for an étale map.
* `isRegularLocalRing_localization_iff_of_etale`: for an étale map, `A_𝔭` is regular if and only
  if `B_𝔮` is.
* `exists_ringEquiv_pi_isDedekindDomain_and_isDiscreteValuationRing_atPrime_of_etale`: an étale
  algebra over a Dedekind domain is a finite product of Dedekind domains, and its localizations
  at maximal ideals with nonzero contraction are discrete valuation rings.
* `not_isDiscreteValuationRing_localization_of_etale_of_comap_eq_bot`: at a prime lying over
  `(0)` the localization of an étale algebra is not a discrete valuation ring.
* `not_forall_isDiscreteValuationRing_localization_rat`: for the étale map `ℚ → ℚ` the
  localization at the maximal ideal `(0)` is not a discrete valuation ring.

## References

* [Stacks Project, Tag 0AGY](https://stacks.math.columbia.edu/tag/0AGY)
* [Stacks Project, Tag 0AGZ](https://stacks.math.columbia.edu/tag/0AGZ)
* [Stacks Project, Tag 0AH0](https://stacks.math.columbia.edu/tag/0AH0)
* [Stacks Project, Tag 0AP2](https://stacks.math.columbia.edu/tag/0AP2)
-/

@[expose] public section

/-! ### Noetherian local rings -/

section

section

public section

/-- For a flat finite type map, the local rings at primes lying over one another are Noetherian
simultaneously. -/
@[stacks 0AGZ]
public theorem isNoetherianRing_localization_iff_of_flat_of_finiteType
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    IsNoetherianRing (Localization.AtPrime p) ↔
      IsNoetherianRing (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType A (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp A B (Localization.AtPrime q)
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp A _ _
  refine ⟨fun _ ↦ Algebra.EssFiniteType.isNoetherianRing (Localization.AtPrime p) _,
    fun _ ↦ ?_⟩
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (A := Localization.AtPrime q)
    (isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid (Localization.AtPrime p) (Localization.AtPrime q)
        (Localization.AtPrime q)).symm.toLinearEquiv)

end

end

section

@[expose] public section

/-- For an étale map, the local rings at primes lying over one another are Noetherian
simultaneously. -/
@[stacks 0AGY "Lemma 0AGZ of the section: for an étale ring map `A → B` and a prime `𝔮 ⊂ B`
lying over `𝔭 ⊂ A`, `A_𝔭` is Noetherian if and only if `B_𝔮` is."]
public lemma isNoetherianRing_localization_iff_of_etale
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    IsNoetherianRing (Localization.AtPrime p) ↔
      IsNoetherianRing (Localization.AtPrime q) :=
  isNoetherianRing_localization_iff_of_flat_of_finiteType p q

end

end

end

/-! ### Regular local rings -/

section

section

open IsLocalRing
open scoped TensorProduct

/-- For an étale map, the local rings at primes lying over one another have the same dimension. -/
private lemma ringKrullDim_localization_eq_of_etale
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    ringKrullDim (Localization.AtPrime p) = ringKrullDim (Localization.AtPrime q) :=
  RingHom.Etale.ringKrullDim_localization_atPrime_eq (f := algebraMap A B)
    (RingHom.etale_algebraMap.mpr inferInstance) p q (q.over_def p)

/-- Local rings at corresponding primes under an étale ring map are regular simultaneously. -/
@[stacks 0AH0]
public theorem isRegularLocalRing_localization_iff_of_etale
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    IsRegularLocalRing (Localization.AtPrime p) ↔
      IsRegularLocalRing (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hdim := ringKrullDim_localization_eq_of_etale p q
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp A _ _
  constructor
  · intro hreg
    have : IsNoetherianRing (Localization.AtPrime p) := hreg.toIsNoetherian
    have : IsNoetherianRing (Localization.AtPrime q) :=
      isNoetherianRing_localization_iff_of_etale p q |>.mp inferInstance
    rw [isRegularLocalRing_iff,
      ← Algebra.FormallyUnramified.map_maximalIdeal (R := Localization.AtPrime p),
      Stacks.CompleteIntersection.BaseChange.spanFinrank_map_of_flat_of_isLocalHom _
        (IsNoetherian.noetherian _), hreg.spanFinrank_maximalIdeal, hdim]
  · intro hreg
    have : IsNoetherianRing (Localization.AtPrime q) := hreg.toIsNoetherian
    have : IsNoetherianRing (Localization.AtPrime p) :=
      isNoetherianRing_localization_iff_of_etale p q |>.mpr inferInstance
    rw [isRegularLocalRing_iff,
      ← Stacks.CompleteIntersection.BaseChange.spanFinrank_map_of_flat_of_isLocalHom
        (A' := Localization.AtPrime q) (maximalIdeal (Localization.AtPrime p))
        (IsNoetherian.noetherian _),
      Algebra.FormallyUnramified.map_maximalIdeal,
      hreg.spanFinrank_maximalIdeal, ← hdim]

attribute [stacks 0AGY "Lemma 0AH0 of the section: for an étale ring map `A → B` and a prime
`𝔮 ⊂ B` lying over `𝔭 ⊂ A`, `A_𝔭` is regular if and only if `B_𝔮` is."]
  isRegularLocalRing_localization_iff_of_etale

end

end

/-! ### Étale algebras over Dedekind domains -/

section

section

universe u v

private lemma normal_of_regular_of_ringKrullDim_le_one (R : Type*) [CommRing R]
    [IsRegularLocalRing R] (hR : ringKrullDim R ≤ 1) :
    IsDomain R ∧ IsIntegrallyClosed R := by
  have hdom : IsDomain R := IsRegularLocalRing.isDomain R
  have hmle : (IsLocalRing.maximalIdeal R).height ≤ 1 := by
    exact_mod_cast (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans_le hR
  by_cases hzero : (IsLocalRing.maximalIdeal R).height = 0
  · have hdim : ringKrullDim R = 0 := by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hzero]
      rfl
    have hspan : Submodule.spanFinrank (IsLocalRing.maximalIdeal R) = 0 := by
      exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
    have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr
      ((Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hspan)
    let := hfield.toField
    exact ⟨inferInstance, inferInstance⟩
  · have hm : (IsLocalRing.maximalIdeal R).height = 1 :=
      le_antisymm hmle (Order.one_le_iff_ne_zero.mpr hzero)
    have hdim : ringKrullDim R = 1 := by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm]
      rfl
    have hregular : IsRegularLocalRing R ∧ ringKrullDim R = 1 := ⟨inferInstance, hdim⟩
    obtain ⟨_, hdvr⟩ := ((isDiscreteValuationRing_tfae R).out 3 1).mp hregular
    exact ⟨hdom, inferInstance⟩

private lemma normal_localization_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [IsDedekindDomain A] (q : Ideal B) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let p := q.comap (algebraMap A B)
  let : p.IsPrime := q.comap_isPrime (algebraMap A B)
  let : q.LiesOver p := ⟨rfl⟩
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    (isRegularLocalRing_localization_iff_of_etale p q).mp inferInstance
  apply normal_of_regular_of_ringKrullDim_le_one
  rw [← ringKrullDim_localization_eq_of_etale p q]
  exact Ring.krullDimLE_iff.mp inferInstance

private lemma finite_product_of_dedekind_domains
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [IsDedekindDomain A] :
    ∃ (n : ℕ) (D : Fin n → Type v) (_ : ∀ i, CommRing (D i)),
      (∀ i, IsDedekindDomain (D i)) ∧ Nonempty (B ≃+* ∀ i, D i) := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hnormal : ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
    fun q _ ↦ normal_localization_of_etale (A := A) (B := B) q
  have : IsReduced B := isReduced_ofLocalizationMaximal B fun q hq ↦ by
    have : q.IsPrime := hq.isPrime
    have : IsDomain (Localization.AtPrime q) := (hnormal q).1
    infer_instance
  have hBdim : ringKrullDim B ≤ 1 := (ringKrullDim_le_iff_height_le 1).mpr fun {q} hq ↦ by
    have : q.IsPrime := hq
    have : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      ← ringKrullDim_localization_eq_of_etale (q.comap (algebraMap A B)) q]
    exact Ring.krullDimLE_iff.mp inferInstance
  have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr hBdim
  obtain ⟨n, D, hcomm, hdom, hic, ⟨e⟩⟩ := ((isIntegrallyClosed_tfae_of_finite_minimalPrimes
    (minimalPrimes.finite_of_isNoetherianRing B)).out 1 3).mp hnormal
  let : ∀ i, CommRing (D i) := hcomm
  have hprodNoeth : IsNoetherianRing (∀ i, D i) := isNoetherianRing_of_ringEquiv B e
  have hded : ∀ i, IsDedekindDomain (D i) := fun i ↦ by
    have : IsDomain (D i) := hdom i
    have : IsIntegrallyClosed (D i) := hic i
    have : IsNoetherianRing (D i) :=
      isNoetherianRing_of_surjective (∀ i, D i) (D i) (Pi.evalRingHom D i)
        (Function.surjective_eval i)
    have hdim : ringKrullDim (D i) ≤ 1 :=
      (ringKrullDim_le_of_surjective (Pi.evalRingHom D i) (Function.surjective_eval i)).trans
        ((ringKrullDim_eq_of_ringEquiv e).symm.le.trans hBdim)
    have : Ring.KrullDimLE 1 (D i) := Ring.krullDimLE_iff.mpr hdim
    have : Ring.DimensionLEOne (D i) := ⟨fun hp hprime ↦ hprime.isMaximal_of_ne_bot hp⟩
    exact (isDedekindDomain_iff (A := D i) (FractionRing (D i))).mpr
      ⟨hdom i, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing (D i))).mp (hic i)⟩
  exact ⟨n, D, hcomm, hded, ⟨e⟩⟩

private lemma isDiscreteValuationRing_localization_of_etale_of_comap_ne_bot
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [IsDedekindDomain A] (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap A B) ≠ ⊥) :
    ∃ _ : IsDomain (Localization.AtPrime q),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  let p := q.comap (algebraMap A B)
  let : p.IsPrime := q.comap_isPrime (algebraMap A B)
  let : q.LiesOver p := ⟨rfl⟩
  have hpDvr : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq _
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [← ringKrullDim_localization_eq_of_etale p q]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  exact ((isDiscreteValuationRing_tfae (Localization.AtPrime q)).out 3 1).mp
    (⟨(isRegularLocalRing_localization_iff_of_etale p q).mp inferInstance, hdim⟩ :
      IsRegularLocalRing _ ∧ _)

/-- An étale algebra over a Dedekind domain is a finite product of Dedekind domains, and its
localizations at maximal ideals with nonzero contraction to the base are discrete valuation
rings. -/
@[stacks 0AP2]
public theorem exists_ringEquiv_pi_isDedekindDomain_and_isDiscreteValuationRing_atPrime_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [IsDedekindDomain A] :
    (∃ (n : ℕ) (D : Fin n → Type v) (_ : ∀ i, CommRing (D i)),
      (∀ i, IsDedekindDomain (D i)) ∧ Nonempty (B ≃+* ∀ i, D i)) ∧
      ∀ q : MaximalSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ ⊥ →
        ∃ _ : IsDomain (Localization.AtPrime q.asIdeal),
          IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
  ⟨finite_product_of_dedekind_domains (A := A) (B := B),
    fun q ↦ isDiscreteValuationRing_localization_of_etale_of_comap_ne_bot (A := A) q.asIdeal⟩

attribute [stacks 0AGY "Lemma 0AP2 of the section, its localization clause in corrected form: an
étale algebra `B` over a Dedekind domain `A` is a finite product of Dedekind domains, and `B_𝔮` is
a discrete valuation ring for every maximal ideal `𝔮 ⊂ B` with `𝔮 ∩ A ≠ (0)`. As written the
clause asserts this for every maximal ideal, which is false: at a prime over `(0)` the local ring
has dimension `0` by Lemma 07QP, see
`not_isDiscreteValuationRing_localization_of_etale_of_comap_eq_bot` and the instance
`not_forall_isDiscreteValuationRing_localization_rat` for the étale map `ℚ → ℚ`. The source's
proof, through Lemmas 07QP, 0AH0 and Algebra 00PD, establishes the corrected clause."]
  exists_ringEquiv_pi_isDedekindDomain_and_isDiscreteValuationRing_atPrime_of_etale

/-- For an étale ring map `A → B` and a prime `𝔮` of `B` lying over the zero ideal of `A`, the
local ring `B_𝔮` is not a discrete valuation ring. -/
theorem not_isDiscreteValuationRing_localization_of_etale_of_comap_eq_bot
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] (hq : q.comap (algebraMap A B) = ⊥) :
    ¬ ∃ _ : IsDomain (Localization.AtPrime q),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  rintro ⟨_, _⟩
  have : Nontrivial A := not_subsingleton_iff_nontrivial.mp fun _ ↦
    (q.comap_isPrime (algebraMap A B)).ne_top (Subsingleton.elim _ _)
  have : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  have h1 := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime q)
  rw [← ringKrullDim_localization_eq_of_etale (q.comap (algebraMap A B)) q,
    IsLocalization.AtPrime.ringKrullDim_eq_height (q.comap (algebraMap A B))
      (Localization.AtPrime (q.comap (algebraMap A B))), hq, Ideal.height_bot] at h1
  exact absurd h1 (by decide)

/-- For the étale map `ℚ → ℚ` from the Dedekind domain `ℚ`, the localization of `ℚ` at its
maximal ideal `(0)` is not a discrete valuation ring. -/
theorem not_forall_isDiscreteValuationRing_localization_rat :
    ¬ ∀ q : MaximalSpectrum ℚ, ∃ _ : IsDomain (Localization.AtPrime q.asIdeal),
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := fun h ↦
  not_isDiscreteValuationRing_localization_of_etale_of_comap_eq_bot (A := ℚ)
    (⊥ : Ideal ℚ) (Ideal.comap_bot_of_injective _ (algebraMap ℚ ℚ).injective)
    (h ⟨⊥, Ideal.bot_isMaximal⟩)

end

end

end
