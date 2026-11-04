module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength

/-!
# Local contributions to a multiplicity

For an element `x` of a Noetherian local ring and a finite module `M`, each point `q` of the
support of `M` contributes the order of vanishing of `x` on `R ⧸ q` times the length of the
localization of `M` at `q`. This file collects the behaviour of that contribution: it is
additive on short exact sequences, invariant under isomorphism, and its restricted sum over the
nonclosed points of the support is a finite sum.

## Main definitions

* `AlgebraicGeometry.localOrderTerm` is the contribution of a single point.

## Main results

* `AlgebraicGeometry.localOrderFinsum_add_of_exact` — additivity of the restricted sum.
* `AlgebraicGeometry.localOrderFinsum_congr` — invariance of the restricted sum.
* `AlgebraicGeometry.localized_length_quotientPrime_eq_one` — the localization of `R ⧸ q` at `q`
  has length one.

## Implementation notes

Orders of vanishing and module lengths take values in `ℕ∞`; their finite values are mapped to
integers with `ENat.toNat`, so that the contribution is an integer and the sums are integer
sums. The sum over the nonclosed points is a restricted `finsum`, which is finite because such
a support has finitely many nonclosed points.

## References

* [Stacks Project, Tag 02QF](https://stacks.math.columbia.edu/tag/02QF)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-- Localizing at a point turns a short exact sequence of modules into an additive relation
between the lengths of the localizations. -/
private lemma localized_length_add_of_exact
    {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (q : PrimeSpectrum R) (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl B) =
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl A) +
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl C) :=
  Module.length_eq_add_of_exact
    (LocalizedModule.map q.asIdeal.primeCompl f)
    (LocalizedModule.map q.asIdeal.primeCompl g)
    (LocalizedModule.map_injective _ _ hf)
    (LocalizedModule.map_surjective _ _ hg)
    (LocalizedModule.map_exact _ _ _ hfg)

/-- Isomorphic modules have localizations of equal length. -/
private lemma localized_length_eq_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (q : PrimeSpectrum R) (e : M ≃ₗ[R] N) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) =
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl N) :=
  (LinearEquiv.ofBijective (LocalizedModule.map q.asIdeal.primeCompl e.toLinearMap)
    ⟨LocalizedModule.map_injective _ _ e.injective,
      LocalizedModule.map_surjective _ _ e.surjective⟩).length_eq

/-- Outside the support, the localization of a module is zero, hence of length zero. -/
private lemma localized_length_eq_zero_of_not_mem_support
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : PrimeSpectrum R) (hq : q ∉ Module.support R M) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) = 0 := by
  have : Subsingleton (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.notMem_support_iff.mp hq
  exact Module.length_eq_zero

/-- The localization of `R ⧸ q` at the prime `q` is a simple module. -/
private theorem isSimpleModule_localizedModule_quotient
    {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] :
    IsSimpleModule (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ q)) := by
  have e := IsLocalizedModule.linearEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl (R ⧸ q))
    (Submodule.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)) q)
  have hmax : Submodule.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)) q
      = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.localized'_eq_map, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have hsimple : IsSimpleModule (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  exact IsSimpleModule.congr
    ((LinearEquiv.extendScalarsOfIsLocalization q.primeCompl (Localization.AtPrime q) e).trans
      (Submodule.quotEquivOfEq _ _ hmax))

/-- The localization of `R ⧸ q` at the point `q` has length one. -/
public lemma localized_length_quotientPrime_eq_one
    {R : Type*} [CommRing R] (q : PrimeSpectrum R) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (R ⧸ q.asIdeal)) = 1 := by
  let : q.asIdeal.IsPrime := q.isPrime
  have := isSimpleModule_localizedModule_quotient q.asIdeal
  exact Module.length_eq_one _ _

/-- At a nonclosed point, a finite module whose support has dimension at most one localizes
to a module of finite length. -/
private lemma localized_length_ne_top_of_dim_le_one
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.supportDim R M ≤ 1) (q : PrimeSpectrum R)
    (hne : q ≠ IsLocalRing.closedPoint R) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := by
  by_cases hq : q ∈ Module.support R M
  · exact localized_length_ne_top q
      (minimal_of_mem_support_ne_closed hM q hq hne)
  · rw [localized_length_eq_zero_of_not_mem_support q hq]
    exact ENat.zero_ne_top

/-- The contribution of a point to the multiplicity of multiplication by `x`: the order of
vanishing of `x` on the residue ring of the point times the length of the localization there. -/
public noncomputable abbrev localOrderTerm
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (q : PrimeSpectrum R) : ℤ :=
  ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x)).toNat : ℤ) *
    ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ)

/-- The local contribution at a nonclosed point is additive on a short exact sequence. -/
private lemma localOrderTerm_add_of_exact
    {R A B C : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] [Module.Finite R C]
    (x : R) (q : PrimeSpectrum R) (hne : q ≠ IsLocalRing.closedPoint R)
    (hA : Module.supportDim R A ≤ 1) (hC : Module.supportDim R C ≤ 1)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    localOrderTerm (M := B) x q =
      localOrderTerm (M := A) x q + localOrderTerm (M := C) x q := by
  unfold localOrderTerm
  rw [localized_length_add_of_exact q f g hf hg hfg,
    ENat.toNat_add (localized_length_ne_top_of_dim_le_one hA q hne)
      (localized_length_ne_top_of_dim_le_one hC q hne)]
  push_cast
  ring

/-- The restricted sum of the local contributions over the nonclosed points of the support of a
submodule is a finite sum over the nonclosed points of an ambient module. -/
private lemma localOrderFinsum_eq_sum_of_support_subset
    {R A B : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    (x : R) (hB : Module.supportDim R B ≤ 1)
    (h : Module.support R A ⊆ Module.support R B) :
    (∑ᶠ q ∈ {q : PrimeSpectrum R |
        q ∈ Module.support R A ∧ q ≠ IsLocalRing.closedPoint R},
      localOrderTerm (M := A) x q) =
      ∑ q ∈ (finite_nonclosed_support hB).toFinset,
        localOrderTerm (M := A) x q := by
  apply finsum_mem_eq_sum_of_inter_support_eq
  rw [(finite_nonclosed_support hB).coe_toFinset]
  ext q
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
  constructor
  · exact fun ⟨⟨hq, hne⟩, ht⟩ ↦ ⟨⟨h hq, hne⟩, ht⟩
  · rintro ⟨⟨_, hne⟩, ht⟩
    refine ⟨⟨?_, hne⟩, ht⟩
    by_contra hn
    exact ht (by simp [localOrderTerm, localized_length_eq_zero_of_not_mem_support q hn])

/-- The restricted sum of the local contributions over the nonclosed points of the support is
additive on a short exact sequence. -/
public lemma localOrderFinsum_add_of_exact
    {R A B C : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] [Module.Finite R C]
    (x : R) (hB : Module.supportDim R B ≤ 1)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    (∑ᶠ q ∈ {q : PrimeSpectrum R |
        q ∈ Module.support R B ∧ q ≠ IsLocalRing.closedPoint R},
      localOrderTerm (M := B) x q) =
      (∑ᶠ q ∈ {q : PrimeSpectrum R |
          q ∈ Module.support R A ∧ q ≠ IsLocalRing.closedPoint R},
        localOrderTerm (M := A) x q) +
      (∑ᶠ q ∈ {q : PrimeSpectrum R |
          q ∈ Module.support R C ∧ q ≠ IsLocalRing.closedPoint R},
        localOrderTerm (M := C) x q) := by
  let s := finite_nonclosed_support hB
  have hA : Module.supportDim R A ≤ 1 :=
    (Module.supportDim_le_of_injective f hf).trans hB
  have hC : Module.supportDim R C ≤ 1 :=
    (Module.supportDim_le_of_surjective g hg).trans hB
  rw [finsum_mem_eq_finite_toFinset_sum _ s,
    localOrderFinsum_eq_sum_of_support_subset x hB (Module.support_subset_of_injective f hf),
    localOrderFinsum_eq_sum_of_support_subset x hB (Module.support_subset_of_surjective g hg),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q hq ↦
    localOrderTerm_add_of_exact x q (s.mem_toFinset.mp hq).2 hA hC f g hf hg hfg

/-- Isomorphic modules have the same restricted sum of local contributions. -/
public lemma localOrderFinsum_congr
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : R) (e : M ≃ₗ[R] N) :
    (∑ᶠ q ∈ {q : PrimeSpectrum R |
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
      localOrderTerm (M := M) x q) =
      (∑ᶠ q ∈ {q : PrimeSpectrum R |
          q ∈ Module.support R N ∧ q ≠ IsLocalRing.closedPoint R},
        localOrderTerm (M := N) x q) := by
  apply finsum_mem_congr
  · simp only [e.support_eq]
  · intro q _
    unfold localOrderTerm
    rw [localized_length_eq_of_linearEquiv q e]

end AlgebraicGeometry
