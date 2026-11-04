module

public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantFromProZero
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthTwo
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit
public import StacksFrontier.RingTheory.LocalCohomology.SupportedAugmentation
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cokernel of an embedding into a module of depth at least two along `T`

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset stable under specialization. Let
`0 → M₁ → M₂ → M₃ → 0` be a short exact sequence of `A`-modules with `M₂` finite, such that
`M₃` vanishes at every prime outside `T` and `depth((M₂)_𝔭) ≥ 2` at every prime `𝔭 ∈ T`. Then
the connecting map of local cohomology identifies `M₃` with `H¹_T(M₁)`:

`M₃ ≅ H⁰_T(M₃) ⟶ H¹_T(M₁)`

is an isomorphism, and naturally so in the short exact sequence. This is the computation behind
"the cokernel of `ℱ' → ℱ''` is `H¹_{T'}(ℱ')`" in the proof of [Stacks, Tag 0EJF].

The two ingredients are the following.

* `H⁰_T(M₂) = H¹_T(M₂) = 0`. Local cohomology with support in `T` is the filtered colimit of
  local cohomology with the closed supports `V(J) ⊆ T` ([Stacks, Tag 0EF1],
  `Stacks.LocalCohomology.colimitClosedSupportComparison_isIso`), so it suffices to kill
  `H⁰_{V(J)}(M₂)` and `H¹_{V(J)}(M₂)`. By the depth hypothesis no associated prime of `M₂` contains
  `J`, so prime avoidance gives `f ∈ J` regular on `M₂`; and no associated prime of `M₂/fM₂`
  contains `J` either, because at such a prime `𝔭` the module `(M₂/fM₂)_𝔭 = (M₂)_𝔭/f(M₂)_𝔭` would
  have depth `0` while [Stacks, Tag 090R] gives it depth `depth((M₂)_𝔭) - 1 ≥ 1`. So there is
  `g ∈ J` regular on `M₂/fM₂`, and `H⁰_{V(J)}(M₂) = H¹_{V(J)}(M₂) = 0` by
  `Stacks.LocalCohomology.isZero_localCohomology_one_of_isSMulRegular`.
* `H⁰_T(M₃) = M₃`. The module `M₃` is supported in `T`, so the augmentation
  `RΓ_T(M₃) ⟶ M₃` is an isomorphism
  (`Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset`).

The long exact sequence `H⁰_T(M₂) → H⁰_T(M₃) → H¹_T(M₁) → H¹_T(M₂)` then makes the connecting map
an isomorphism.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyZeroAugmentation` — the augmentation `H⁰_T(M) ⟶ M`,
  natural in `M`.
* `Stacks.LocalCohomology.cokernelIsoLocalCohomologyOne` — the isomorphism `M₃ ≅ H¹_T(M₁)`.
* `Stacks.LocalCohomology.cokernelNatIsoLocalCohomologyOne` — the same isomorphism for a diagram
  of short exact sequences, natural in the diagram.

## Main results

* `Stacks.LocalCohomology.exists_mem_isSMulRegular_of_forall_not_le` — prime avoidance against
  the associated primes produces a nonzerodivisor in an ideal contained in none of them.
* `Stacks.LocalCohomology.isZero_localCohomology_le_one_of_forall_two_le_depth` — `H⁰_T(N)` and
  `H¹_T(N)` vanish for a finite module of depth at least two at every prime of `T`.
* `Stacks.LocalCohomology.isIso_localCohomologyZeroAugmentation_of_support_subset` — `H⁰_T(M) = M`
  for a module supported in `T`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-! ### Nonzerodivisors from the depth at the primes of `T` -/

/-- **Prime avoidance against the associated primes.** If an ideal `J` is contained in no
associated prime of a finite module `M` over a Noetherian ring, then `J` contains a nonzerodivisor
on `M`. -/
theorem exists_mem_isSMulRegular_of_forall_not_le {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] (J : Ideal A) (h : ∀ p ∈ associatedPrimes A M, ¬ J ≤ p) :
    ∃ x ∈ J, IsSMulRegular M x := by
  by_contra! hcon
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact hcon 0 J.zero_mem (fun a b _ => Subsingleton.elim a b)
  have hsub : (J : Set A) ⊆ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hcon
  obtain ⟨Ia, hIa⟩ := associatedPrimes.nonempty A M
  obtain ⟨p, hp, hJp⟩ := (Ideal.subset_union_prime_finite (f := id) (associatedPrimes.finite A M)
    Ia Ia (fun I hI _ _ => IsAssociatedPrime.isPrime hI)).mp hsub
  exact h p hp hJp

/-- At positive depth over a Noetherian local ring, the maximal ideal is not an associated prime:
it contains a nonzerodivisor. -/
private theorem maximalIdeal_notMem_associatedPrimes_of_one_le_depth {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hdepth : 1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) M) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R M := fun hass => by
  obtain ⟨r, hr, hreg⟩ := (Module.one_le_depth_iff_exists_isSMulRegular _).mp hdepth
  have hmem : r ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) := Set.mem_biUnion hass hr
  rw [biUnion_associatedPrimes_eq_compl_regular] at hmem
  exact hmem hreg

/-- A prime at which a finite module has positive depth is not an associated prime of it: the
maximal ideal of the localization would be associated to the localized module, but it contains
a nonzerodivisor on it. -/
theorem notMem_associatedPrimes_of_one_le_depth {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] (p : PrimeSpectrum A)
    (hdepth : 1 ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M)) :
    p.asIdeal ∉ associatedPrimes A M := by
  intro hp
  exact maximalIdeal_notMem_associatedPrimes_of_one_le_depth hdepth
    (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp)

omit [IsNoetherianRing A] in
/-- Localizing `M/fM` at a prime gives the quotient of the localized module by the image of
`f`, as a submodule of the localized module: the localization of `f M` is `f M_𝔭`. -/
theorem localized_smul_top_eq (p : Submonoid A) {M : Type*} [AddCommGroup M] [Module A M]
    (f : A) :
    (f • (⊤ : Submodule A M)).localized p =
      (algebraMap A (Localization p) f) •
        (⊤ : Submodule (Localization p) (LocalizedModule p M)) := by
  change (f • (⊤ : Submodule A M)).localized' (Localization p) p
    (LocalizedModule.mkLinearMap p M) = _
  rw [← Submodule.ideal_span_singleton_smul f (⊤ : Submodule A M),
    ← Submodule.ideal_span_singleton_smul (algebraMap A (Localization p) f)
      (⊤ : Submodule (Localization p) (LocalizedModule p M)),
    Submodule.localized'_smul, Submodule.localized'_span]
  simp only [Set.image_singleton, Submodule.localized'_top]
  rfl

/-- If `f ∈ 𝔭` is a nonzerodivisor on a finite module `M` with `depth(M_𝔭) ≥ 2`, then `𝔭` is not
an associated prime of `M/fM`: by [Stacks, Tag 090R] the module `(M/fM)_𝔭 = M_𝔭/fM_𝔭` has depth
`depth(M_𝔭) - 1 ≥ 1`. -/
theorem notMem_associatedPrimes_quotSMulTop_of_two_le_depth {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] (p : PrimeSpectrum A) {f : A} (hf : f ∈ p.asIdeal)
    (hreg : IsSMulRegular M f)
    (hdepth : 2 ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M)) :
    p.asIdeal ∉ associatedPrimes A (QuotSMulTop f M) := by
  set R := Localization.AtPrime p.asIdeal
  set Mp := LocalizedModule p.asIdeal.primeCompl M
  set f' : R := algebraMap A R f
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing p.asIdeal.primeCompl R ‹_›
  have hf' : f' ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R p.asIdeal f).mpr hf
  have hreg' : IsSMulRegular Mp f' :=
    hreg.of_isLocalizedModule R p.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M)
  have h090R := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal R) Mp).1 f' hf' hreg'
  have hQ : 1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) (QuotSMulTop f' Mp) := by
    by_contra hlt
    rw [Order.lt_one_iff.mp (not_le.mp hlt), zero_add] at h090R
    rw [← h090R] at hdepth
    exact absurd hdepth (by decide)
  -- The localization of `M/fM` is `M_𝔭 ⧸ (fM)_𝔭`, which is `M_𝔭/fM_𝔭`.
  set N := f • (⊤ : Submodule A M)
  let e : (Mp ⧸ N.localized p.asIdeal.primeCompl) ≃ₗ[R] QuotSMulTop f' Mp :=
    Submodule.quotEquivOfEq _ _ (localized_smul_top_eq p.asIdeal.primeCompl f)
  have hQ' : 1 ≤ Module.depth R (IsLocalRing.maximalIdeal R)
      (Mp ⧸ N.localized p.asIdeal.primeCompl) := by
    rwa [Module.depth_eq_depth_of_linearEquiv _ e]
  intro hp
  refine maximalIdeal_notMem_associatedPrimes_of_one_le_depth hQ'
    (Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      p.asIdeal.primeCompl (N.toLocalizedQuotient p.asIdeal.primeCompl) _ ?_)
  rwa [show Ideal.comap (algebraMap A R) (IsLocalRing.maximalIdeal R) = p.asIdeal from
    Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)]

/-! ### Vanishing of `H⁰_T` and `H¹_T` -/

/-- For a closed subset `V(J)` of `T`, a finite module of depth at least two at every prime of
`T` has `H⁰_{V(J)} = H¹_{V(J)} = 0`. -/
theorem isZero_localCohomology_zeroLocus_le_one_of_forall_two_le_depth
    (T : Set (PrimeSpectrum A)) (J : Ideal A) (hJ : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T)
    (N : ModuleCat.{max u v} A) [Module.Finite A N]
    (hdepth : ∀ p : PrimeSpectrum A, p ∈ T →
      2 ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl N))
    (i : ℤ) (hi : i ≤ 1) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (J : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i) := by
  obtain ⟨f, hfJ, hf⟩ := exists_mem_isSMulRegular_of_forall_not_le J fun p hp hJp =>
    notMem_associatedPrimes_of_one_le_depth (M := N) ⟨p, hp.isPrime⟩
      (le_trans (by decide) (hdepth _ (hJ hJp))) hp
  obtain ⟨g, hgJ, hg⟩ := exists_mem_isSMulRegular_of_forall_not_le (M := QuotSMulTop f N) J
    fun p hp hJp =>
      notMem_associatedPrimes_quotSMulTop_of_two_le_depth (M := N) ⟨p, hp.isPrime⟩ (hJp hfJ) hf
        (hdepth _ (hJ hJp)) hp
  rcases lt_or_ge i 0 with hneg | hpos
  · exact isZero_localCohomologyWithSupportIn_of_neg.{u, v} _ N i hneg
  · interval_cases i
    · exact isZero_localCohomology_zero_of_isSMulRegular.{u, v} J hfJ N hf
    · exact isZero_localCohomology_one_of_isSMulRegular.{u, v} J hfJ hgJ N hf hg

/-- **Depth at least two along `T` kills `H⁰_T` and `H¹_T`.** Let `T ⊆ Spec(A)` be stable under
specialization and `N` a finite `A`-module with `depth(N_𝔭) ≥ 2` for every `𝔭 ∈ T`. Then
`H^i_T(N) = 0` for `i ≤ 1`.

Local cohomology with support in `T` is the filtered colimit of local cohomology with the closed
supports `V(J) ⊆ T`, each of which vanishes in these degrees. -/
@[sga "2 XII 1.5" "special case"]
theorem isZero_localCohomology_le_one_of_forall_two_le_depth (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (N : ModuleCat.{max u v} A) [Module.Finite A N]
    (hdepth : ∀ p : PrimeSpectrum A, p ∈ T →
      2 ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl N))
    (i : ℤ) (hi : i ≤ 1) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N
  have := colimitClosedSupportComparison_isIso.{u, v} A T hT i
  refine IsZero.of_iso ?_ (asIso ((colimitClosedSupportComparison.{u, v} A T i).app K)).symm
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun J => (isZero_localCohomology_zeroLocus_le_one_of_forall_two_le_depth T
    (OrderDual.ofDual J).1 (OrderDual.ofDual J).2 N hdepth i hi).eq_of_src _ _

/-! ### Degree zero on modules supported in `T` -/

/-- The augmentation `H⁰_T(M) ⟶ M`: degree-zero cohomology of the augmentation `RΓ_T ⟶ id`
evaluated at `M` placed in degree zero. -/
def localCohomologyZeroAugmentation (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) :
    localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 0 ⟶ M :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
      ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) 0).hom.app M

omit [IsNoetherianRing A] in
/-- The augmentation `H⁰_T(M) ⟶ M` is natural in `M`. -/
@[reassoc]
theorem localCohomologyZeroAugmentation_naturality (T : Set (PrimeSpectrum A))
    {M N : ModuleCat.{max u v} A} (φ : M ⟶ N) :
    localCohomologyMap.{u, v} A T 0 φ ≫ localCohomologyZeroAugmentation.{u, v} T N =
      localCohomologyZeroAugmentation.{u, v} T M ≫ φ := by
  have h1 := (derivedSectionsWithSupportInAugmentation.{u, v} A T).naturality
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map φ)
  have h2 := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max u v} A) 0).hom.naturality φ
  dsimp only [localCohomologyZeroAugmentation, localCohomologyMap]
  simp only [Functor.id_map] at h1
  simp only [Functor.comp_map, Functor.id_map] at h2
  rw [← Category.assoc, ← Functor.map_comp, h1, Functor.map_comp, Category.assoc, h2,
    Category.assoc]

/-- **`H⁰_T(M) = M` for a module supported in `T`**, when `T` is stable under specialization:
the augmentation `RΓ_T(M) ⟶ M` is an isomorphism at an object with `T`-supported cohomology. -/
theorem isIso_localCohomologyZeroAugmentation_of_support_subset (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (M : ModuleCat.{max u v} A)
    (hM : Module.support A M ⊆ T) :
    IsIso (localCohomologyZeroAugmentation.{u, v} T M) := by
  have hsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ⊆ T := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · exact (le_of_eq ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} A) 0).app M).toLinearEquiv.support_eq).trans hM
    · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) :=
        ModuleCat.subsingleton_of_isZero ((lt_or_gt_of_ne hi).elim
          (fun hlt => DerivedCategory.isZero_of_isGE _ 0 i hlt)
          (fun hgt => DerivedCategory.isZero_of_isLE _ 0 i hgt))
      rw [Module.support_eq_empty]
      exact Set.empty_subset _
  have := isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset.{u, v} A T hT
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 0 hsupp
  dsimp only [localCohomologyZeroAugmentation]
  infer_instance

/-! ### The cokernel as `H¹_T` -/

variable {S : ShortComplex (ModuleCat.{max u v} A)}

/-- The hypotheses on a short exact sequence `0 → M₁ → M₂ → M₃ → 0` under which the connecting
map identifies `M₃` with `H¹_T(M₁)`: `M₂` is finite, `M₃` vanishes at the primes outside `T`, and
`(M₂)_𝔭` has depth at least two at the primes `𝔭 ∈ T`. -/
structure IsDepthTwoEmbedding (T : Set (PrimeSpectrum A))
    (S : ShortComplex (ModuleCat.{max u v} A)) : Prop where
  /-- The middle term is finite. -/
  finite : Module.Finite A S.X₂
  /-- The third term vanishes at every prime outside `T`. -/
  supp : ∀ p : PrimeSpectrum A, p ∉ T →
    Subsingleton (LocalizedModule p.asIdeal.primeCompl S.X₃)
  /-- The middle term has depth at least two at every prime of `T`. -/
  depth : ∀ p : PrimeSpectrum A, p ∈ T →
    2 ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl S.X₂)

omit [IsNoetherianRing A] in
/-- The third term of a sequence as in `IsDepthTwoEmbedding` is supported in `T`. -/
theorem IsDepthTwoEmbedding.support_subset {T : Set (PrimeSpectrum A)}
    (h : IsDepthTwoEmbedding.{u, v} T S) : Module.support A S.X₃ ⊆ T := by
  intro p hp
  by_contra hpT
  have := Module.mem_support_iff.mp hp
  exact not_subsingleton _ (h.supp p hpT)

/-- The connecting map `H⁰_T(M₃) ⟶ H¹_T(M₁)` is an isomorphism under the hypotheses of
`IsDepthTwoEmbedding`. -/
theorem isIso_localCohomologyδ_zero_one (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hS : S.ShortExact) (h : IsDepthTwoEmbedding.{u, v} T S) :
    IsIso (localCohomologyδ.{u, v} T hS 0 1 (by norm_num)) := by
  have := h.finite
  have : Mono (localCohomologyδ.{u, v} T hS 0 1 (by norm_num)) :=
    (localCohomology_exact₃.{u, v} T hS 0 1 (by norm_num)).mono_g
      ((isZero_localCohomology_le_one_of_forall_two_le_depth.{u, v} T hT S.X₂ h.depth 0
        (by norm_num)).eq_of_src _ _)
  have : Epi (localCohomologyδ.{u, v} T hS 0 1 (by norm_num)) :=
    (localCohomology_exact₁.{u, v} T hS 0 1 (by norm_num)).epi_f
      ((isZero_localCohomology_le_one_of_forall_two_le_depth.{u, v} T hT S.X₂ h.depth 1
        le_rfl).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **The cokernel of an embedding into a module of depth at least two along `T` is `H¹_T`.**
Let `T` be stable under specialization and `0 → M₁ → M₂ → M₃ → 0` short exact with `M₂` finite,
`M₃` vanishing outside `T` and `depth((M₂)_𝔭) ≥ 2` for `𝔭 ∈ T`. Then the inverse of the
augmentation `H⁰_T(M₃) ⟶ M₃` followed by the connecting map is an isomorphism `M₃ ≅ H¹_T(M₁)`. -/
def cokernelIsoLocalCohomologyOne (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hS : S.ShortExact) (h : IsDepthTwoEmbedding.{u, v} T S) :
    S.X₃ ≅ localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj S.X₁) 1 :=
  have := isIso_localCohomologyZeroAugmentation_of_support_subset.{u, v} T hT S.X₃
    h.support_subset
  have := isIso_localCohomologyδ_zero_one.{u, v} T hT hS h
  (asIso (localCohomologyZeroAugmentation.{u, v} T S.X₃)).symm ≪≫
    asIso (localCohomologyδ.{u, v} T hS 0 1 (by norm_num))

/-- The isomorphism `M₃ ≅ H¹_T(M₁)` is the inverse of the augmentation followed by the
connecting map. -/
theorem cokernelIsoLocalCohomologyOne_hom (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hS : S.ShortExact) (h : IsDepthTwoEmbedding.{u, v} T S) :
    (cokernelIsoLocalCohomologyOne.{u, v} T hT hS h).hom =
      haveI := isIso_localCohomologyZeroAugmentation_of_support_subset.{u, v} T hT S.X₃
        h.support_subset
      CategoryTheory.inv (localCohomologyZeroAugmentation.{u, v} T S.X₃) ≫
        localCohomologyδ.{u, v} T hS 0 1 (by norm_num) := rfl

/-- **Naturality of the identification of the cokernel with `H¹_T`.** For a diagram `S` of short
exact sequences satisfying the hypotheses of `IsDepthTwoEmbedding` termwise, the isomorphisms
`cokernelIsoLocalCohomologyOne` form a natural isomorphism from the diagram of third terms to the
diagram of `H¹_T` of the first terms. -/
def cokernelNatIsoLocalCohomologyOne {C : Type*} [Category C] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (S : C ⥤ ShortComplex (ModuleCat.{max u v} A))
    (hS : ∀ c, (S.obj c).ShortExact) (h : ∀ c, IsDepthTwoEmbedding.{u, v} T (S.obj c)) :
    S ⋙ ShortComplex.π₃ ≅
      S ⋙ ShortComplex.π₁ ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T 1 :=
  NatIso.ofComponents (fun c => cokernelIsoLocalCohomologyOne.{u, v} T hT (hS c) (h c))
    (fun {c c'} φ => by
      have := isIso_localCohomologyZeroAugmentation_of_support_subset.{u, v} T hT (S.obj c).X₃
        (h c).support_subset
      have := isIso_localCohomologyZeroAugmentation_of_support_subset.{u, v} T hT (S.obj c').X₃
        (h c').support_subset
      change (S.map φ).τ₃ ≫ (cokernelIsoLocalCohomologyOne.{u, v} T hT (hS c') (h c')).hom =
        (cokernelIsoLocalCohomologyOne.{u, v} T hT (hS c) (h c)).hom ≫
          localCohomologyMap.{u, v} A T 1 (S.map φ).τ₁
      rw [cokernelIsoLocalCohomologyOne_hom, cokernelIsoLocalCohomologyOne_hom,
        Category.assoc, ← localCohomologyδ_naturality.{u, v} T (hS c) (hS c') (S.map φ),
        ← Category.assoc, ← Category.assoc]
      congr 1
      rw [IsIso.eq_inv_comp, ← Category.assoc,
        ← localCohomologyZeroAugmentation_naturality.{u, v} T (S.map φ).τ₃,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id])

end Stacks.LocalCohomology

end
