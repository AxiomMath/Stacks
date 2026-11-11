module

public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Removing the embedded associated primes from a finite module

Let `R` be a Noetherian ring and `M` a finite `R`-module. Among the submodules of `M` whose
support is nowhere dense in `Supp(M)` there is a largest one, namely the submodule

`K = {m ∈ M | m ↦ 0 in M_𝔮 for every minimal point 𝔮 of Supp(M)}`,

and the quotient `M' = M / K` is `M` with its embedded associated primes removed.

The proof rests on one observation: a submodule `N ⊆ M` has nowhere dense support in `Supp(M)`
exactly when `N_𝔮 = 0` for every minimal point `𝔮` of `Supp(M)`. Indeed `Supp(N)` is closed in
`Supp(M)`; if it misses every minimal point it can contain no nonempty open, since every point
of `Supp(M)` is a specialization of a minimal one and an open set containing a specialization
contains the point specialized; and if it contains a minimal point `𝔮` then it contains
`V(𝔮) ∩ Supp(M)`, which is a neighbourhood of `𝔮` in `Supp(M)` because `Supp(M)` has only
finitely many minimal points. With that, `K` is visibly the largest such submodule, and the
three properties of `M'` follow by chasing elements: killing `K` changes nothing at the minimal
points of `Supp(M)`, so `Supp(M') = Supp(M)`; an associated prime `Ann(m̄)` of `M'` is trapped
inside a minimal point of `Supp(M)` and hence equal to it; and if `f` lies in every embedded
associated prime of `M` then `f` is nilpotent on `K`, because a prime minimal over `Ann(m)` for
`m ∈ K` is an associated prime of `M` which, by Stacks 02CE, is not a minimal one — and a
submodule on which `f` is nilpotent disappears from `M_f`.

## Main results

* `Stacks.AssociatedPrimes.EmbeddedRemoval.solution`: the statement of Stacks 02M6,
  `Module.exists_isGreatest_isNowhereDense_support`.

## Implementation notes

The largest submodule is constructed as an intersection of kernels of the localization maps
`M → M_𝔮`, one for each minimal point `𝔮` of `Supp(M)`, which makes it a submodule by
construction; the description in the source, `{m | Supp(R m) ⊆ ⋃ V(𝔭ᵢ)}` with `𝔭ᵢ` the embedded
associated primes, is the same set, since `Supp(R m)` is the union of `V(p)` over the associated
primes `p` of `R m`, all of which are associated primes of `M`.

Stacks 02CE enters exactly once, in the third part, to know that a prime which is minimal among
the associated primes of `M` is a minimal point of `Supp(M)`.

## References

* [StacksProject 02M6](https://stacks.math.columbia.edu/tag/02M6)
-/

namespace Stacks.AssociatedPrimes.EmbeddedRemoval

open PrimeSpectrum

section ZeroLocus

variable {R : Type*} [CommRing R]

/-- The primes minimal in the closed set `V(I)` are exactly the primes minimal over `I`. -/
private lemma minimal_mem_zeroLocus_iff {I : Ideal R} {q : PrimeSpectrum R} :
    Minimal (· ∈ zeroLocus (I : Set R)) q ↔ q.asIdeal ∈ I.minimalPrimes := by
  simp only [Ideal.minimalPrimes, Minimal, mem_zeroLocus, ← SetLike.coe_subset_coe,
    ← asIdeal_le_asIdeal]
  exact ⟨fun h ↦ ⟨⟨q.isPrime, h.1⟩, fun J hJ hJq ↦ h.2 (y := ⟨J, hJ.1⟩) hJ.2 hJq⟩,
    fun h ↦ ⟨h.1.2, fun y hy hyq ↦ h.2 ⟨y.isPrime, hy⟩ hyq⟩⟩

end ZeroLocus

section Vanishing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

private lemma notMem_support_submodule_iff (N : Submodule R M) (q : PrimeSpectrum R) :
    q ∉ Module.support R ↥N ↔ ∀ x ∈ N, ∃ r ∉ q.asIdeal, r • x = 0 := by
  rw [Module.notMem_support_iff']
  simp [Subtype.forall, ← Submodule.coe_eq_zero]

/-- The class of `m` in `M ⧸ N` is killed by `r` exactly when `r • m` lies in `N`. -/
private lemma smul_mkQ_eq_zero_iff {N : Submodule R M} {r : R} {m : M} :
    r • N.mkQ m = 0 ↔ r • m ∈ N := by
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- If every element of `N` is killed by an element of `S`, then `S⁻¹N = 0`, so localizing the
exact sequence `0 → N → M → M ⧸ N → 0` at `S` identifies `S⁻¹M` with `S⁻¹(M ⧸ N)`. -/
private lemma bijective_map_mkQ (S : Submonoid R) (N : Submodule R M)
    (h : ∀ x ∈ N, ∃ r ∈ S, r • x = 0) :
    Function.Bijective (LocalizedModule.map S N.mkQ) := by
  have : Subsingleton (LocalizedModule S ↥N) :=
    (IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S ↥N)).mpr fun x ↦ by
      obtain ⟨r, hr, hrx⟩ := h x x.2
      exact ⟨r, hr, Subtype.ext (by simpa using hrx)⟩
  refine ⟨?_, LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _)⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := (LocalizedModule.map_exact S N.subtype N.mkQ
    (LinearMap.exact_subtype_mkQ N) z).mp hz
  simp [Subsingleton.elim y 0]

/-- The submodule of elements of `M` which vanish in `M_𝔮` for every prime `𝔮` minimal in the
support of `M`. For `R` Noetherian and `M` finite this is the largest submodule of `M` whose
support is nowhere dense in `Supp(M)`. -/
private noncomputable def vanishingAtMinimalSupport (R : Type*) [CommRing R] (M : Type*)
    [AddCommGroup M] [Module R M] : Submodule R M :=
  ⨅ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
    LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)

private lemma mem_vanishingAtMinimalSupport_iff {x : M} :
    x ∈ vanishingAtMinimalSupport R M ↔ ∀ q : PrimeSpectrum R,
      Minimal (· ∈ Module.support R M) q → ∃ r ∉ q.asIdeal, r • x = 0 := by
  simp only [vanishingAtMinimalSupport, Submodule.mem_iInf, Set.mem_ofPred_eq,
    LocalizedModule.mem_ker_mkLinearMap_iff, Ideal.mem_primeCompl_iff]

/-- A submodule of `M` is contained in `K` exactly when its support misses every minimal point
of `Supp(M)`. -/
private lemma le_vanishingAtMinimalSupport_iff (N : Submodule R M) :
    N ≤ vanishingAtMinimalSupport R M ↔ ∀ q : PrimeSpectrum R,
      Minimal (· ∈ Module.support R M) q → q ∉ Module.support R ↥N := by
  simp only [IsConcreteLE.le_iff, mem_vanishingAtMinimalSupport_iff, notMem_support_submodule_iff]
  exact ⟨fun h q hq x hx ↦ h hx q hq, fun h x hx q hq ↦ h q hq x hx⟩

/-- The support of `K` misses every minimal point of `Supp(M)`. -/
private lemma notMem_support_vanishingAtMinimalSupport {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) :
    q ∉ Module.support R ↥(vanishingAtMinimalSupport R M) :=
  (le_vanishingAtMinimalSupport_iff _).mp le_rfl q hq

/-- `K` is saturated at every minimal point `𝔮` of `Supp(M)`: an element of `M` whose class in
`M ⧸ K` is killed by some `r ∉ 𝔮` is itself killed by an element outside `𝔮`. -/
private lemma exists_smul_eq_zero_of_smul_mkQ_eq_zero {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) {m : M} {r : R} (hr : r ∉ q.asIdeal)
    (hrm : r • (vanishingAtMinimalSupport R M).mkQ m = 0) : ∃ u ∉ q.asIdeal, u • m = 0 := by
  rw [smul_mkQ_eq_zero_iff, mem_vanishingAtMinimalSupport_iff] at hrm
  obtain ⟨u, hu, hum⟩ := hrm q hq
  exact ⟨u * r, fun h ↦ (q.isPrime.mem_or_mem h).elim hu hr, by rw [mul_smul]; exact hum⟩

end Vanishing

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsNoetherianRing R] in
/-- For `M` finite, the primes minimal in `Supp(M)` are the primes minimal over `Ann(M)`. -/
private lemma minimal_mem_support_iff {q : PrimeSpectrum R} :
    Minimal (· ∈ Module.support R M) q ↔ q.asIdeal ∈ (Module.annihilator R M).minimalPrimes := by
  rw [Module.support_eq_zeroLocus]
  exact minimal_mem_zeroLocus_iff

private lemma finite_setOf_minimal_mem_support :
    {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q}.Finite :=
  Set.Finite.subset (Set.Finite.preimage (f := PrimeSpectrum.asIdeal)
    (fun _ _ _ _ h ↦ PrimeSpectrum.ext h)
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Module.annihilator R M)))
    fun _ hq ↦ minimal_mem_support_iff.mp hq

omit [IsNoetherianRing R] in
/-- Every point of the support of a finite module is a specialization of a minimal one. -/
private lemma exists_minimal_le_of_mem_support {p : PrimeSpectrum R}
    (hp : p ∈ Module.support R M) :
    ∃ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q ∧ q ≤ p := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_minimalPrimes_le (J := p.asIdeal) (Module.mem_support_iff_of_finite.mp hp)
  exact ⟨⟨q, hq.isPrime⟩, minimal_mem_support_iff.mpr hq, (asIdeal_le_asIdeal _ _).mp hqp⟩

/-- A minimal point `𝔮` of `Supp(M)` is an interior point of `V(𝔮) ∩ Supp(M)`: as `Supp(M)` has
only finitely many minimal points, the complement of the closures of the others is an open
neighbourhood of `𝔮` in `Supp(M)`, and it is contained in `V(𝔮)` because every point of
`Supp(M)` specializes some minimal one. -/
private lemma mem_interior_preimage_zeroLocus_of_minimal {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) :
    (⟨q, hq.prop⟩ : ↥(Module.support R M)) ∈
      interior (Subtype.val ⁻¹' zeroLocus (q.asIdeal : Set R)) := by
  set W := ⋃ q' ∈ {q' : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q'} \ {q},
    zeroLocus (q'.asIdeal : Set R) with hWdef
  have hW : IsClosed W := (finite_setOf_minimal_mem_support.sdiff).isClosed_biUnion
    fun i _ ↦ isClosed_zeroLocus _
  refine mem_interior.mpr ⟨Subtype.val ⁻¹' Wᶜ, ?_,
    hW.isOpen_compl.preimage continuous_subtype_val, ?_⟩
  · rintro ⟨y, hy⟩ hyW
    obtain ⟨q', hq', hq'y⟩ := exists_minimal_le_of_mem_support hy
    obtain rfl : q' = q := by
      by_contra hne
      refine hyW ?_
      rw [hWdef, Set.mem_iUnion₂]
      exact ⟨q', ⟨hq', hne⟩, (asIdeal_le_asIdeal _ _).mpr hq'y⟩
    exact (asIdeal_le_asIdeal _ _).mpr hq'y
  · simp only [Set.mem_preimage, Set.mem_compl_iff, hWdef, Set.mem_iUnion₂, not_exists]
    rintro q' ⟨hq', hne⟩ hmem
    have hmemle : q' ≤ q := (asIdeal_le_asIdeal _ _).mp hmem
    exact hne (le_antisymm hmemle (hq.le_of_le hq'.prop hmemle))

/-- A submodule of a finite module over a Noetherian ring has nowhere dense support in `Supp(M)`
if and only if its support contains no minimal point of `Supp(M)`. -/
private lemma isNowhereDense_support_iff (N : Submodule R M) :
    IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥N : Set ↥(Module.support R M)) ↔
      ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q → q ∉ Module.support R ↥N := by
  rw [(Module.isClosed_support.preimage
      (continuous_subtype_val (p := (· ∈ Module.support R M)))).isNowhereDense_iff,
    Set.eq_empty_iff_forall_notMem]
  refine ⟨fun hint q hq hqN ↦ hint ⟨q, hq.prop⟩ (interior_mono
    (Set.preimage_mono fun y hy ↦ Module.mem_support_mono ((asIdeal_le_asIdeal _ _).mp hy) hqN)
    (mem_interior_preimage_zeroLocus_of_minimal hq)), fun h y hy ↦ ?_⟩
  obtain ⟨U, hUsub, hUopen, hyU⟩ := mem_interior.mp hy
  obtain ⟨V, hVopen, hVU⟩ := isOpen_induced_iff.mp hUopen
  obtain ⟨q, hqmin, hqle⟩ := exists_minimal_le_of_mem_support y.2
  have hqV : q ∈ V := ((PrimeSpectrum.le_iff_specializes q y.1).mp hqle).mem_open hVopen
    (by rw [← hVU] at hyU; exact hyU)
  exact h q hqmin (hUsub (show (⟨q, hqmin.prop⟩ : ↥(Module.support R M)) ∈ U by
    rw [← hVU]; exact hqV))

/-- `K` is the largest submodule of `M` whose support is nowhere dense in `Supp(M)`. -/
private lemma isGreatest_isNowhereDense_support :
    IsGreatest {N : Submodule R M |
        IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥N : Set ↥(Module.support R M))}
      (vanishingAtMinimalSupport R M) :=
  ⟨(isNowhereDense_support_iff _).mpr fun _ ↦ notMem_support_vanishingAtMinimalSupport,
    fun N hN ↦ (le_vanishingAtMinimalSupport_iff N).mpr ((isNowhereDense_support_iff N).mp hN)⟩

omit [IsNoetherianRing R] in
/-- Killing `K` changes nothing at the minimal points of `Supp(M)`, hence nothing in the
support. -/
private lemma support_quotient_vanishingAtMinimalSupport :
    Module.support R (M ⧸ vanishingAtMinimalSupport R M) = Module.support R M := by
  refine Set.Subset.antisymm
    (Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)) fun p hp ↦ ?_
  obtain ⟨q, hqmin, hqle⟩ := exists_minimal_le_of_mem_support hp
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hqmin.prop
  refine Module.mem_support_mono hqle (Module.mem_support_iff'.mpr
    ⟨(vanishingAtMinimalSupport R M).mkQ m, fun r hr hrm ↦ ?_⟩)
  obtain ⟨u, hu, hum⟩ := exists_smul_eq_zero_of_smul_mkQ_eq_zero hqmin hr hrm
  exact hm u hu hum

omit [IsNoetherianRing R] in
/-- An associated prime of `M ⧸ K` is a point of `Supp(M)`. -/
private lemma mem_support_of_mem_associatedPrimes_quotient {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ vanishingAtMinimalSupport R M)) :
    (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  rw [← support_quotient_vanishingAtMinimalSupport]
  exact Module.mem_support_iff_of_finite.mpr
    (le_of_eq_of_le Submodule.annihilator_top.symm hp.annihilator_le)

/-- Every associated prime of `M ⧸ K` is a minimal point of `Supp(M)`. If `p = Ann(m̄)` then
`m ∉ K`, so `m` survives at some minimal point `𝔮` of `Supp(M)`; every `a ∈ p` sends `m` into
`K` and hence lies in `𝔮` by saturation, so `p ≤ 𝔮`; and `p` is itself a point of `Supp(M)`, so
minimality of `𝔮` forces `p = 𝔮`. -/
private lemma minimal_mem_support_of_mem_associatedPrimes_quotient {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ vanishingAtMinimalSupport R M)) :
    Minimal (· ∈ Module.support R M) (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
  obtain ⟨-, y, hy⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨m, rfl⟩ := (vanishingAtMinimalSupport R M).mkQ_surjective y
  have hmK : m ∉ vanishingAtMinimalSupport R M := fun hmem ↦ hp.isPrime.ne_top
    (hy.trans (eq_top_iff.mpr fun r _ ↦ Submodule.mem_colon_singleton.mpr
      ((Submodule.mem_bot R).mpr (smul_mkQ_eq_zero_iff.mpr (Submodule.smul_mem _ r hmem)))))
  rw [mem_vanishingAtMinimalSupport_iff] at hmK
  push Not at hmK
  obtain ⟨q, hqmin, hq⟩ := hmK
  have hple : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ≤ q := by
    refine (asIdeal_le_asIdeal _ _).mp fun a ha ↦ ?_
    by_contra hane
    obtain ⟨u, hu, hum⟩ := exists_smul_eq_zero_of_smul_mkQ_eq_zero hqmin hane
      ((Submodule.mem_bot R).mp (Submodule.mem_colon_singleton.mp (hy.le ha)))
    exact hq u hu hum
  obtain rfl : q = (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
    (hqmin.le_of_le (mem_support_of_mem_associatedPrimes_quotient hp) hple).antisymm hple
  exact hqmin

/-- `M ⧸ K` has no embedded associated primes: its associated primes are minimal points of
`Supp(M)`, and no point of `Supp(M)` lies below a minimal one without equalling it. -/
private lemma minimal_mem_associatedPrimes_quotient {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ vanishingAtMinimalSupport R M)) :
    Minimal (· ∈ associatedPrimes R (M ⧸ vanishingAtMinimalSupport R M)) p :=
  ⟨hp, fun _ hp' hle ↦ (asIdeal_le_asIdeal _ _).mpr
    ((minimal_mem_support_of_mem_associatedPrimes_quotient hp).le_of_le
      (mem_support_of_mem_associatedPrimes_quotient hp') ((asIdeal_le_asIdeal _ _).mpr hle))⟩

/-- For `x ∈ K`, every prime `p` minimal over `Ann(x)` is an *embedded* associated prime of `M`:
it is an associated prime of the submodule `R x ⊆ M`, hence of `M`, and it is not minimal among
those, since by Stacks 02CE a minimal one is a minimal point of `Supp(M)`, where `x` dies. -/
private lemma mem_associatedPrimes_and_not_minimal_of_mem_minimalPrimes_annihilator
    {x : M} (hx : x ∈ vanishingAtMinimalSupport R M) {p : Ideal R}
    (hp : p ∈ (Submodule.span R {x}).annihilator.minimalPrimes) :
    p ∈ associatedPrimes R M ∧ ¬ Minimal (· ∈ associatedPrimes R M) p := by
  refine ⟨associatedPrimes.subset_of_injective (f := (Submodule.span R {x}).subtype)
    Subtype.val_injective
    (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ hp),
    fun hmin ↦ ?_⟩
  have hq : Minimal (· ∈ Module.support R M) (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
    (Set.ext_iff.mp Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes _).mpr
      ⟨hmin.prop, fun y hy hyle ↦ (asIdeal_le_asIdeal _ _).mp
        (hmin.le_of_le hy ((asIdeal_le_asIdeal _ _).mpr hyle))⟩
  obtain ⟨r, hr, hrx⟩ := mem_vanishingAtMinimalSupport_iff.mp hx _ hq
  exact hr (hp.1.2 ((Submodule.mem_annihilator_span_singleton x r).mpr hrx))

/-- An element `f` of every embedded associated prime of `M` is nilpotent on `K`: it lies in
every prime minimal over `Ann(x)` for `x ∈ K`, hence in the radical of `Ann(x)`. -/
private lemma exists_pow_smul_eq_zero_of_mem_vanishingAtMinimalSupport {f : R}
    (hf : ∀ p ∈ associatedPrimes R M, ¬ Minimal (· ∈ associatedPrimes R M) p → f ∈ p)
    {x : M} (hx : x ∈ vanishingAtMinimalSupport R M) : ∃ n : ℕ, f ^ n • x = 0 := by
  have hrad : f ∈ (Submodule.span R {x}).annihilator.radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro p hp
    obtain ⟨hass, hemb⟩ :=
      mem_associatedPrimes_and_not_minimal_of_mem_minimalPrimes_annihilator hx hp
    exact hf p hass hemb
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  exact ⟨n, (Submodule.mem_annihilator_span_singleton x (f ^ n)).mp hn⟩

end Noetherian

/-- **Stacks 02M6.** Let `R` be a Noetherian ring and `M` a finite `R`-module. The set of
`R`-submodules `K ⊆ M` whose support is nowhere dense in `Supp(M)` has a largest element `K`,
and the quotient `M' = M / K` satisfies: (1) `Supp(M) = Supp(M')`; (2) every associated prime
of `M'` is minimal among the associated primes of `M'`; (3) for every `f ∈ R` lying in all
embedded associated primes of `M`, the localization of `M → M'` at the powers of `f` is
bijective. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ K : Submodule R M,
      IsGreatest {K : Submodule R M |
          IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥K : Set ↥(Module.support R M))} K ∧
        Module.support R (M ⧸ K) = Module.support R M ∧
        (∀ p ∈ associatedPrimes R (M ⧸ K),
          Minimal (· ∈ associatedPrimes R (M ⧸ K)) p) ∧
        ∀ f : R, (∀ p ∈ associatedPrimes R M, ¬ Minimal (· ∈ associatedPrimes R M) p → f ∈ p) →
          Function.Bijective (LocalizedModule.map (Submonoid.powers f) K.mkQ) :=
  ⟨vanishingAtMinimalSupport R M, isGreatest_isNowhereDense_support,
    support_quotient_vanishingAtMinimalSupport,
    fun _ hp ↦ minimal_mem_associatedPrimes_quotient hp,
    fun f hf ↦ bijective_map_mkQ _ _ fun _ hx ↦
      have ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_mem_vanishingAtMinimalSupport hf hx
      ⟨f ^ n, pow_mem (Submonoid.mem_powers f) n, hn⟩⟩

end Stacks.AssociatedPrimes.EmbeddedRemoval

/-!
# Removing embedded associated primes from a finite module

Let `R` be a Noetherian ring and `M` a finite `R`-module. Among the `R`-submodules `K ⊆ M`
whose support is nowhere dense in `Supp(M)` there is a largest one, and the quotient
`M' = M / K` is `M` with its embedded associated primes removed: `Supp(M') = Supp(M)`, every
associated prime of `M'` is minimal among the associated primes of `M'`, and `M` and `M'` agree
after inverting any `f ∈ R` which lies in every embedded associated prime of `M`.

Writing `𝔮₁, …, 𝔮_t` for the minimal primes of `Supp(M)` and `𝔭₁, …, 𝔭_s` for the embedded
associated primes of `M`, the largest such submodule is
`K = {m ∈ M | Supp(R m) ⊆ V(𝔭₁) ∪ ⋯ ∪ V(𝔭_s)}`: a submodule of `M` has nowhere dense support
exactly when it vanishes at each generic point `𝔮_j`, and for `m ∈ M` this happens precisely
when the associated primes of `R m`, which are associated primes of `M`, are all embedded.

## Main results

* `Module.exists_isGreatest_isNowhereDense_support`: the submodules of `M` with nowhere dense
  support have a largest element `K`, and `M ⧸ K` has the same support as `M`, has no embedded
  associated primes, and is reached from `M` by a map which becomes bijective after inverting
  any element of every embedded associated prime of `M`.

## Implementation notes

The source asserts that the set of submodules with nowhere dense support has a *maximal*
element; its proof gives the stronger `IsGreatest`, which is what is stated here. This is not
decoration: `IsGreatest` pins `K` uniquely, and the quotient `M'` of the source's subsequent
lemmas ("the quotient constructed in Lemma 02M6") is only well defined because of it.

"`Supp(K)` is nowhere dense in `Supp(M)`" is a statement about the subspace `Supp(M)` of
`Spec(R)`, not about `Spec(R)`: it is rendered as `IsNowhereDense` applied to the preimage of
`Supp(K)` in the topological space `↥(Module.support R M)`. The ambient reading would be false
to the source — it would admit `K = M` whenever `Supp(M)` has empty interior in `Spec(R)`, and
the greatest element would be `M` itself.

Embedded associated primes (Definition 02M5: an associated prime that is not minimal among the
associated primes) are spelled out with `Minimal`, as `p ∈ associatedPrimes R M` together with
`¬ Minimal (· ∈ associatedPrimes R M) p`, there being no such predicate in Mathlib or in this
library yet; "`M'` has no embedded associated primes" is therefore the statement that every
associated prime of `M'` is `Minimal` among them.

Every hypothesis is used: `IsNoetherianRing R` and `Module.Finite R M` are what make the
associated primes of `M` finite in number and the supports closed, hence what produce the
largest element at all, and both occur in each of the three conclusions through `K`. The
scalars are the source's throughout: `K` is an `R`-submodule and `M ⧸ K` the `R`-module
quotient, while part (3) is a statement over `R_f = Localization (Submonoid.powers f)`, the
map there being `Localization (Submonoid.powers f)`-linear as `M_f ≅ M'_f` is in the source.
Part (3) pins the canonical map rather than asserting an abstract isomorphism: it says that the
localization `LocalizedModule.map (Submonoid.powers f) K.mkQ` of the quotient map `M → M ⧸ K`
is bijective. The instantiation is not degenerate: for `R = k[x, y]` and `M = R / (x², x y)`
one has `Supp(M) = V(x)` and `associatedPrimes R M = {(x), (x, y)}` with `(x, y)` embedded, and
the theorem returns `K = (x) / (x², x y) ≅ R / (x, y)`, nonzero, with `M ⧸ K ≅ R / (x)`.

## References

* [StackProject 02M6](https://stacks.math.columbia.edu/tag/02M6)

## Tags

associated prime, embedded prime, support, nowhere dense

-/

namespace Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Let `R` be a Noetherian ring and `M` a finite `R`-module. The set of `R`-submodules
`K ⊆ M` whose support is nowhere dense in `Supp(M)` has a largest element `K`, and the
quotient `M' = M / K` satisfies: (1) `Supp(M) = Supp(M')`; (2) every associated prime of `M'`
is minimal among the associated primes of `M'`, that is, `M'` has no embedded associated
primes; (3) for every `f ∈ R` lying in all embedded associated primes of `M`, the localization
of `M → M'` at the powers of `f` is bijective, so `M_f ≅ M'_f`. -/
@[stacks 02M6]
public theorem exists_isGreatest_isNowhereDense_support :
    ∃ K : Submodule R M,
      IsGreatest {K : Submodule R M |
          IsNowhereDense (Subtype.val ⁻¹' support R ↥K : Set ↥(support R M))} K ∧
        support R (M ⧸ K) = support R M ∧
        (∀ p ∈ associatedPrimes R (M ⧸ K), Minimal (· ∈ associatedPrimes R (M ⧸ K)) p) ∧
        ∀ f : R, (∀ p ∈ associatedPrimes R M, ¬ Minimal (· ∈ associatedPrimes R M) p → f ∈ p) →
          Function.Bijective (LocalizedModule.map (Submonoid.powers f) K.mkQ) :=
    by apply Stacks.AssociatedPrimes.EmbeddedRemoval.solution

end Module

/-!
# Removing embedded associated primes commutes with localization

Let `R` be a Noetherian ring, `M` a finite `R`-module, and `K ⊆ M` the largest submodule whose
support is nowhere dense in `Supp(M)`, as produced by Stacks 02M6. This file proves that for any
submonoid `p ⊆ R` the localized submodule `Kₚ ⊆ Mₚ` is again the largest submodule of `Mₚ` with
nowhere dense support; since `(M ⧸ K)ₚ = Mₚ ⧸ Kₚ`, that is the statement `(M')_f = (M_f)'` of
Stacks 02M7.

Both sides are read through the same criterion, valid over any Noetherian ring and any finite
module: a submodule has nowhere dense support exactly when its support contains no minimal point
of the ambient support. What has to be compared is therefore the minimal points on the two sides,
and the localization map `Spec(Rₚ) → Spec(R)` does that: it reflects the order, its image is the
lower set of primes disjoint from `p`, and `Supp(Mₚ)` is the preimage of `Supp(M)` along it, so it
matches the minimal points of `Supp(Mₚ)` with those minimal points of `Supp(M)` which are
disjoint from `p`.

That `Kₚ` has nowhere dense support is then immediate. For the converse — every `L ⊆ Mₚ` with
nowhere dense support lies in `Kₚ` — it suffices, for `m ∈ M` with `g m ∈ L`, to produce `t ∈ p`
with `t • m ∈ K`, and for that it suffices that `t • m` die at every minimal point `𝔮` of
`Supp(M)`. A minimal point disjoint from `p` is a minimal point of `Supp(Mₚ)`, where `L` already
dies. A minimal point meeting `p`, say in `f`, contributes because `f` is nilpotent on `M` near
`𝔮`: as `𝔮` is minimal over `Ann(M)`, some `r ∉ 𝔮` has `r f ^ n ∈ Ann(M)`. Multiplying the
finitely many witnesses together gives a single `t ∈ p`.

## Main results

* `Stacks.AssociatedPrimes.EmbeddedLocalized.solution`: the statement of Stacks 02M7,
  `Module.isGreatest_isNowhereDense_support_localized'`.

## Implementation notes

The criterion "nowhere dense support iff missing the minimal points of `Supp(M)`",
`Stacks.AssociatedPrimes.EmbeddedLocalized.isNowhereDense_support_iff`, is a general fact about
finite modules over Noetherian rings rather than a step of either tag, and so is the resulting
criterion for membership in the greatest such submodule,
`Stacks.AssociatedPrimes.EmbeddedLocalized.mem_of_forall_exists_smul_eq_zero`.

The comparison of supports along a localization,
`Stacks.AssociatedPrimes.EmbeddedLocalized.support_eq_preimage_support`, holds for an arbitrary
localization of an arbitrary module: neither finiteness nor Noetherianness enters, since one
direction clears a denominator and the other transports an annihilator along `g`. Reading
minimality of a point of `Supp(Mₚ)` off that equality is pure order theory,
`Stacks.AssociatedPrimes.EmbeddedLocalized.minimal_comp_iff`: a map which reflects the order and
whose range is a lower set detects minimality in a preimage.

The nilpotence used at a minimal point meeting `p` is isolated at the level of ideals,
`Stacks.AssociatedPrimes.EmbeddedLocalized.exists_mul_pow_mem_of_mem_minimalPrimes`: an element of
a prime `𝔮` minimal over `I` is nilpotent modulo `I` after inverting something outside `𝔮`.

## References

* [StacksProject 02M7](https://stacks.math.columbia.edu/tag/02M7)
-/

namespace Stacks.AssociatedPrimes.EmbeddedLocalized

open PrimeSpectrum

section Order

/-- Minimality passes through a map which reflects the order and whose range is a lower set: such
a map matches the minimal points of a preimage `f ⁻¹' t` with the minimal points of `t` lying in
its range. -/
private lemma minimal_comp_iff {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) (hr : IsLowerSet (Set.range f)) {t : Set β} {a : α} :
    Minimal (fun x ↦ f x ∈ t) a ↔ Minimal (· ∈ t) (f a) := by
  refine ⟨fun h ↦ ⟨h.prop, fun y hy hle ↦ ?_⟩, fun h ↦ ⟨h.prop, fun y hy hle ↦
    (hf _ _).mp (h.le_of_le hy ((hf _ _).mpr hle))⟩⟩
  obtain ⟨b, rfl⟩ := hr hle (Set.mem_range_self a)
  exact (hf _ _).mpr (h.le_of_le hy ((hf _ _).mp hle))

end Order

section MinimalPrimes

variable {R : Type*} [CommRing R]

/-- The primes minimal in the closed set `V(I)` are exactly the primes minimal over `I`. -/
private alias minimal_mem_zeroLocus_iff :=
    Stacks.AssociatedPrimes.EmbeddedRemoval.minimal_mem_zeroLocus_iff

/-- An element `f` of a prime `q` minimal over an ideal `I` is nilpotent modulo `I` locally at
`q`: some `f ^ n`, multiplied by an element outside `q`, lies in `I`. Indeed the radical of
`I R_q` is `q R_q`, so `f` is nilpotent there, and clearing the denominator gives the witness. -/
private lemma exists_mul_pow_mem_of_mem_minimalPrimes {I q : Ideal R} (hq : q ∈ I.minimalPrimes)
    {f : R} (hf : f ∈ q) : ∃ (n : ℕ) (r : R), r ∉ q ∧ r * f ^ n ∈ I := by
  have : q.IsPrime := hq.1.1
  have hmem : algebraMap R (Localization.AtPrime q) f ∈
      (I.map (algebraMap R (Localization.AtPrime q))).radical := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (A := Localization.AtPrime q) q I hq]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨n, hn⟩ := hmem
  rw [← map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl] at hn
  exact ⟨n, hn.choose, hn.choose_spec.1, hn.choose_spec.2⟩

end MinimalPrimes

section Support

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A prime misses the support of a submodule exactly when every element of the submodule is
killed by something outside the prime. -/
private alias notMem_support_submodule_iff :=
    Stacks.AssociatedPrimes.EmbeddedRemoval.notMem_support_submodule_iff

/-- A prime misses the support of a cyclic module exactly when it misses the annihilator of the
generator. -/
private lemma notMem_support_span_singleton_iff (x : M) (q : PrimeSpectrum R) :
    q ∉ Module.support R ↥(Submodule.span R {x}) ↔ ∃ r ∉ q.asIdeal, r • x = 0 := by
  rw [notMem_support_submodule_iff]
  refine ⟨fun h ↦ h x (Submodule.mem_span_singleton_self x), fun ⟨r, hr, hrx⟩ y hy ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  exact ⟨r, hr, by rw [smul_comm, hrx, smul_zero]⟩

end Support

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For `M` finite, the primes minimal in `Supp(M)` are the primes minimal over `Ann(M)`. -/
private alias minimal_mem_support_iff :=
    Stacks.AssociatedPrimes.EmbeddedRemoval.minimal_mem_support_iff

private alias finite_setOf_minimal_mem_support :=
    Stacks.AssociatedPrimes.EmbeddedRemoval.finite_setOf_minimal_mem_support

omit [IsNoetherianRing R] in
/-- Every point of the support of a finite module is a specialization of a minimal one. -/
private lemma exists_minimal_le_of_mem_support {q : PrimeSpectrum R}
    (hq : q ∈ Module.support R M) :
    ∃ q' : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q' ∧ q' ≤ q :=
  Stacks.AssociatedPrimes.EmbeddedRemoval.exists_minimal_le_of_mem_support hq

/-- A minimal point `𝔮` of `Supp(M)` is an interior point of `V(𝔮) ∩ Supp(M)`: as `Supp(M)` has
only finitely many minimal points, the complement of the closures of the others is an open
neighbourhood of `𝔮` in `Supp(M)`, and it is contained in `V(𝔮)` because every point of `Supp(M)`
specializes some minimal one. -/
private alias mem_interior_preimage_zeroLocus_of_minimal :=
    Stacks.AssociatedPrimes.EmbeddedRemoval.mem_interior_preimage_zeroLocus_of_minimal

/-- A submodule of a finite module over a Noetherian ring has nowhere dense support in `Supp(M)`
if and only if its support contains no minimal point of `Supp(M)`. -/
private alias isNowhereDense_support_iff :=
    Stacks.AssociatedPrimes.EmbeddedRemoval.isNowhereDense_support_iff

/-- Membership in the greatest submodule with nowhere dense support is pointwise: an element
which dies at every minimal point of `Supp(M)` lies in it, because the submodule it generates
then has nowhere dense support. -/
private lemma mem_of_forall_exists_smul_eq_zero {K : Submodule R M}
    (hK : IsGreatest {K : Submodule R M |
        IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥K : Set ↥(Module.support R M))} K)
    {m : M} (h : ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q →
      ∃ r ∉ q.asIdeal, r • m = 0) : m ∈ K :=
  hK.2 ((isNowhereDense_support_iff _).mpr fun q hq ↦
      (notMem_support_span_singleton_iff m q).mpr (h q hq))
    (Submodule.mem_span_singleton_self m)

omit [IsNoetherianRing R] in
/-- An element `f` of a prime `𝔮` minimal in `Supp(M)` is nilpotent on `M` near `𝔮`: some power
of it, multiplied by an element outside `𝔮`, kills `M`.

This is the local finiteness of length at a generic point of the support, in the form the
localization argument uses: it is what makes the minimal points of `Supp(M)` meeting `p`
invisible after localizing at `p`. -/
private lemma exists_pow_mul_smul_eq_zero_of_minimal {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) {f : R} (hf : f ∈ q.asIdeal) (m : M) :
    ∃ (n : ℕ) (r : R), r ∉ q.asIdeal ∧ (f ^ n * r) • m = 0 := by
  obtain ⟨n, r, hr, hrf⟩ :=
    exists_mul_pow_mem_of_mem_minimalPrimes (minimal_mem_support_iff.mp hq) hf
  exact ⟨n, r, hr, by rw [mul_comm]; exact Module.mem_annihilator.mp hrf m⟩

end Noetherian

section Localization

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {Rₚ : Type*} [CommRing Rₚ] [Algebra R Rₚ]
  {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
  (p : Submonoid R) [IsLocalization p Rₚ]

include p in
/-- The map `Spec(Rₚ) → Spec(R)` reflects the order. -/
private lemma comap_le_comap_iff {Q Q' : PrimeSpectrum Rₚ} :
    comap (algebraMap R Rₚ) Q ≤ comap (algebraMap R Rₚ) Q' ↔ Q ≤ Q' := by
  rw [← asIdeal_le_asIdeal, ← asIdeal_le_asIdeal, comap_asIdeal, comap_asIdeal]
  exact IsLocalization.under_le_under_iff p Rₚ

include p in
/-- The image of `Spec(Rₚ) → Spec(R)`, the set of primes disjoint from `p`, is a lower set. -/
private lemma isLowerSet_range_comap :
    IsLowerSet (Set.range (comap (algebraMap R Rₚ))) := by
  rw [PrimeSpectrum.localization_comap_range Rₚ p]
  exact fun _ _ hle hq ↦ hq.mono_right ((asIdeal_le_asIdeal _ _).mpr hle)

variable (g : M →ₗ[R] Mₚ) [IsLocalizedModule p g]

/-- Every element of `Mₚ` is a fraction `mk' g m s`. -/
private lemma exists_mk'_eq (x : Mₚ) : ∃ (m : M) (s : p), IsLocalizedModule.mk' g m s = x := by
  obtain ⟨⟨m, s⟩, hx⟩ := IsLocalizedModule.mk'_surjective p g x
  exact ⟨m, s, hx⟩

omit [IsLocalization p Rₚ] in
/-- A submodule of `Mₚ` containing `mk' g m s` contains `g m`, since `s` acts invertibly. -/
private lemma mem_of_mk'_mem {L : Submodule Rₚ Mₚ} {m : M} {s : p}
    (h : IsLocalizedModule.mk' g m s ∈ L) : g m ∈ L := by
  have h := L.smul_mem (algebraMap R Rₚ (s : R)) h
  rwa [algebraMap_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel'] at h

/-- If an element outside a prime `Q` of `Rₚ` kills `g m`, then `m` is killed by a product of an
element of `p` and an element outside the pullback of `Q`. -/
private lemma exists_mem_mul_smul_eq_zero {Q : PrimeSpectrum Rₚ} {a : Rₚ} (ha : a ∉ Q.asIdeal)
    {m : M} (h : a • g m = 0) :
    ∃ v ∈ p, ∃ r ∉ (comap (algebraMap R Rₚ) Q).asIdeal, (v * r) • m = 0 := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p a
  have hru : algebraMap R Rₚ r ∉ Q.asIdeal := by
    rw [← IsLocalization.mk'_spec' Rₚ r s]
    exact fun hc ↦ ha ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units Rₚ s)).mp hc)
  have hg : g (r • m) = 0 := by
    rw [map_smul, ← algebraMap_smul Rₚ, ← IsLocalization.mk'_spec' Rₚ r s, mul_smul, h, smul_zero]
  obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_zero_iff p g).mp hg
  exact ⟨u, u.2, r, by simpa using hru, by simpa [mul_smul, Submonoid.smul_def] using hu⟩

include p g in
/-- The support of a localization of `M` is the preimage of the support of `M` under the induced
map of prime spectra. -/
private lemma support_eq_preimage_support :
    Module.support Rₚ Mₚ = comap (algebraMap R Rₚ) ⁻¹' Module.support R M := by
  ext Q
  rw [Set.mem_preimage, ← not_iff_not, Module.notMem_support_iff', Module.notMem_support_iff']
  refine ⟨fun h m ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨a, ha, hax⟩ := h (g m)
    obtain ⟨v, hv, r, hr, hvr⟩ := exists_mem_mul_smul_eq_zero p g ha hax
    refine ⟨v * r, fun hc ↦ ((comap (algebraMap R Rₚ) Q).isPrime.mem_or_mem hc).elim ?_ hr, hvr⟩
    exact fun h ↦ Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.map_units Rₚ ⟨v, hv⟩))
  · obtain ⟨m, s, rfl⟩ := exists_mk'_eq p g x
    obtain ⟨r, hr, hrm⟩ := h m
    refine ⟨algebraMap R Rₚ r, by simpa using hr, ?_⟩
    rw [algebraMap_smul Rₚ, ← IsLocalizedModule.mk'_smul, hrm, IsLocalizedModule.mk'_zero]

include p g in
/-- The minimal points of `Supp(Mₚ)` are exactly the points lying over minimal points of
`Supp(M)`: minimality transports along `Spec(Rₚ) → Spec(R)`, which reflects the order and has
lower-set range, and `Supp(Mₚ)` is the preimage of `Supp(M)`. -/
private lemma minimal_mem_support_comap_iff (Q : PrimeSpectrum Rₚ) :
    Minimal (· ∈ Module.support Rₚ Mₚ) Q ↔
      Minimal (· ∈ Module.support R M) (comap (algebraMap R Rₚ) Q) := by
  rw [support_eq_preimage_support p g]
  exact minimal_comp_iff (fun _ _ ↦ comap_le_comap_iff p) (isLowerSet_range_comap p)

section Descent

variable [IsNoetherianRing R] [Module.Finite R M]

omit [IsNoetherianRing R] in
/-- **The descent step.** Let `L ⊆ Mₚ` be a submodule whose support misses every minimal point of
`Supp(Mₚ)`, and let `m ∈ M` have `g m ∈ L`. Then at every minimal point `𝔮` of `Supp(M)` the
element `m` is killed by an element of `p` times an element outside `𝔮`.

This is the mathematical content of Stacks 02M7: the two kinds of minimal point of `Supp(M)`
contribute for different reasons. One disjoint from `p` survives in `Spec(Rₚ)`, where it is a
minimal point of `Supp(Mₚ)` and `L` — hence `g m` — already dies; one meeting `p` in some `f`
contributes `f ^ n`, because `f` is nilpotent on `M` near `𝔮`. -/
private lemma exists_mem_mul_smul_eq_zero_of_minimal {L : Submodule Rₚ Mₚ}
    (hL : ∀ Q : PrimeSpectrum Rₚ, Minimal (· ∈ Module.support Rₚ Mₚ) Q →
      Q ∉ Module.support Rₚ ↥L)
    {m : M} (hm : g m ∈ L) {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) :
    ∃ v ∈ p, ∃ r ∉ q.asIdeal, (v * r) • m = 0 := by
  by_cases hd : Disjoint (p : Set R) (q.asIdeal : Set R)
  · obtain ⟨Q, rfl⟩ : q ∈ Set.range (comap (algebraMap R Rₚ)) := by
      rw [PrimeSpectrum.localization_comap_range Rₚ p]; exact hd
    obtain ⟨a, ha, hag⟩ := (notMem_support_submodule_iff L Q).mp
      (hL Q ((minimal_mem_support_comap_iff p g Q).mpr hq)) (g m) hm
    exact exists_mem_mul_smul_eq_zero p g ha hag
  · obtain ⟨f, hfp, hfq⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨n, r, hr, hrf⟩ := exists_pow_mul_smul_eq_zero_of_minimal hq hfq m
    exact ⟨f ^ n, pow_mem hfp n, r, hr, hrf⟩

/-- Multiplying the witnesses of the descent step over the finitely many minimal points of
`Supp(M)` produces a single `t ∈ p` with `t • m ∈ K`. -/
private lemma exists_mem_smul_mem {K : Submodule R M}
    (hK : IsGreatest {K : Submodule R M |
        IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥K : Set ↥(Module.support R M))} K)
    {L : Submodule Rₚ Mₚ}
    (hL : ∀ Q : PrimeSpectrum Rₚ, Minimal (· ∈ Module.support Rₚ Mₚ) Q →
      Q ∉ Module.support Rₚ ↥L)
    {m : M} (hm : g m ∈ L) : ∃ t ∈ p, t • m ∈ K := by
  have hfin := finite_setOf_minimal_mem_support (R := R) (M := M)
  have key : ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q →
      ∃ v ∈ p, ∃ r ∉ q.asIdeal, (v * r) • m = 0 :=
    fun _ hq ↦ exists_mem_mul_smul_eq_zero_of_minimal p g hL hm hq
  choose! v hv r hr hvr using key
  refine ⟨∏ q ∈ hfin.toFinset, v q,
    Submonoid.prod_mem _ fun q hq ↦ hv q (hfin.mem_toFinset.mp hq),
    mem_of_forall_exists_smul_eq_zero hK fun q hq ↦ ⟨r q, hr q hq, ?_⟩⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem v (hfin.mem_toFinset.mpr hq)
  rw [smul_smul, hc]
  calc (r q * (v q * c)) • m = c • ((v q * r q) • m) := by rw [smul_smul]; congr 1; ring
    _ = 0 := by rw [hvr q hq, smul_zero]

end Descent

end Localization

/-- **Stacks 02M7.** Let `R` be a Noetherian ring, `M` a finite `R`-module, and `K ⊆ M` the
greatest submodule whose support is nowhere dense in `Supp(M)`. For any submonoid `p ⊆ R` the
localized submodule `Kₚ ⊆ Mₚ` is the greatest `Rₚ`-submodule of `Mₚ` whose support is nowhere
dense in `Supp(Mₚ)`; since `(M ⧸ K)ₚ = Mₚ ⧸ Kₚ`, this is the equality `(M')_f = (M_f)'`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {Rₚ : Type*} [CommRing Rₚ] [Algebra R Rₚ]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (p : Submonoid R) [IsLocalization p Rₚ] (g : M →ₗ[R] Mₚ) [IsLocalizedModule p g]
    {K : Submodule R M}
    (hK : IsGreatest {K : Submodule R M |
        IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥K : Set ↥(Module.support R M))} K) :
    IsGreatest {L : Submodule Rₚ Mₚ |
        IsNowhereDense (Subtype.val ⁻¹' Module.support Rₚ ↥L : Set ↥(Module.support Rₚ Mₚ))}
      (K.localized' Rₚ p g) := by
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p Rₚ ‹_›
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p g
  refine ⟨(isNowhereDense_support_iff _).mpr fun Q hQ ↦ ?_, fun L hL x hx ↦ ?_⟩
  · -- `Kₚ` misses every minimal point of `Supp(Mₚ)`, because `K` misses every minimal point of
    -- `Supp(M)` and the two sets of minimal points correspond.
    rw [support_eq_preimage_support p (K.toLocalized' Rₚ p g), Set.mem_preimage]
    exact (isNowhereDense_support_iff K).mp hK.1 _ ((minimal_mem_support_comap_iff p g Q).mp hQ)
  · obtain ⟨m, s, rfl⟩ := exists_mk'_eq p g x
    obtain ⟨t, htp, htm⟩ := exists_mem_smul_mem p g hK ((isNowhereDense_support_iff L).mp hL)
      (mem_of_mk'_mem p g hx)
    exact ⟨t • m, htm, ⟨t, htp⟩ * s, by
      rw [show t • m = (⟨t, htp⟩ : p) • m from rfl, IsLocalizedModule.mk'_cancel_left]⟩

end Stacks.AssociatedPrimes.EmbeddedLocalized

/-!
# Removing embedded associated primes commutes with localization

Let `R` be a Noetherian ring and `M` a finite `R`-module. Lemma 02M6 produces the largest
`R`-submodule `K ⊆ M` whose support is nowhere dense in `Supp(M)`, and with it the quotient
`M' = M ⧸ K`, which is `M` with its embedded associated primes removed. This file records that
the construction is compatible with localization: if `Mₚ` is the localization of `M` at a
multiplicative subset `p ⊆ R`, then the localization `Kₚ ⊆ Mₚ` of `K` is again the largest
`Rₚ`-submodule of `Mₚ` with nowhere dense support, so `(M')ₚ = (Mₚ)'`.

The reason is that `K` is the set of `m ∈ M` whose support meets no irreducible component of
`Supp(M)`, i.e. the kernel of `M → ∏ⱼ M_{𝔮ⱼ}` for `𝔮₁, …, 𝔮_t` the minimal primes of `Supp(M)`.
Localizing at `p` kills exactly those factors with `𝔮ⱼ ∩ p ≠ ∅` — `M_{𝔮ⱼ}` is finite with
support `{𝔮ⱼ}`, so its localization at `p` has empty support — and the surviving `𝔮ⱼ` are
precisely the minimal primes of `Supp(Mₚ)`. Equivalently, on associated primes: `Ass(Mₚ)` is
`Ass(M)` intersected with `Spec(Rₚ)`, and an associated prime of `Mₚ` is embedded exactly when
it is embedded in `M`, since a strictly smaller associated prime is again disjoint from `p`.

## Main results

* `Module.isGreatest_isNowhereDense_support_localized'`: the localization
  `Submodule.localized'` of the greatest submodule with nowhere dense support is the greatest
  submodule of the localized module with nowhere dense support.

## Implementation notes

The source states the conclusion as an equality of quotients, `(M')_f = (M_f)'`. That
`(M ⧸ K)ₚ = Mₚ ⧸ Kₚ`, compatibly with the maps out of `Mₚ`, is already Mathlib's
`IsLocalizedModule.toLocalizedQuotient'`; the whole content of the lemma is therefore the
identification of the *submodules*, which is what is stated here. Phrasing it as `IsGreatest`
of `K.localized' Rₚ p g` both pins the map (the quotient `(Mₚ)'` is the quotient by exactly the
localized submodule, not merely isomorphic to `(M')ₚ`) and yields the equality `L = Kₚ` for any
other `L` satisfying 02M6 for `Mₚ`, greatest elements being unique.

The source localizes at the powers of a single `f ∈ R`; the statement here localizes at an
arbitrary submonoid `p ⊆ R`, which the argument above needs no more than, and it is phrased
over an abstract localization `Rₚ` of `R` and `Mₚ` of `M` rather than over
`Localization (Submonoid.powers f)` and `LocalizedModule (Submonoid.powers f) M`, so that no
user has to undo a choice of model. Taking `p = Submonoid.powers f`, `Rₚ = Localization p` and
`g = LocalizedModule.mkLinearMap p M` recovers the source's statement.

The set of submodules with nowhere dense support is spelled exactly as in 02M6: nowhere density
is read in the subspace `Supp(M)` of `Spec(R)`, not in `Spec(R)`, so `hK` matches the conclusion
of `Module.exists_isGreatest_isNowhereDense_support` verbatim.

Faithfulness. (1) Every hypothesis is used: `IsNoetherianRing R` and `Module.Finite R M` are
what make `Supp` closed and the associated primes finite, hence what make nowhere density of
`Supp(L)` equivalent to `L` vanishing at the generic points on both sides; `hK` is what names
the `K` of 02M6, without which no submodule of `Mₚ` is singled out. (2) The scalars are the
source's: `K` is an `R`-submodule of `M` and the conclusion is about `Rₚ`-submodules of `Mₚ`,
`K.localized' Rₚ p g` being the `Rₚ`-span of the image of `K`, exactly the `Kₚ` of the source.
(3) The canonical map is pinned: the localization map `g : M →ₗ[R] Mₚ` is a parameter and the
distinguished submodule of `Mₚ` is its image's span, so `(Mₚ)'` is `Mₚ ⧸ Kₚ` on the nose.
(4) The instantiation is not degenerate: for `R = k[x, y]` and `M = R ⧸ (x², x y)` one has
`Supp(M) = V(x)`, `Ass(M) = {(x), (x, y)}` with `(x, y)` embedded, and `K = (x) ⧸ (x², x y) ≅
R ⧸ (x, y) ≠ 0`; localizing at `p = Ideal.primeCompl (x, y)` keeps both `Kₚ ≠ 0` and
`Supp(Mₚ)` one-dimensional, so the conclusion asserts that a nonzero submodule is the greatest
one. (Localizing instead at `Submonoid.powers y` gives `Kₚ = 0`, as 02M6(3) predicts, and at
`Submonoid.powers x` gives `Mₚ = 0`; the general-submonoid form is what makes the nonzero
witness available at all.)

## References

* [StackProject 02M7](https://stacks.math.columbia.edu/tag/02M7)

## Tags

associated prime, embedded prime, support, nowhere dense, localization

-/

namespace Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  {Rₚ : Type*} [CommRing Rₚ] [Algebra R Rₚ]
  {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]

/-- Let `R` be a Noetherian ring, `M` a finite `R`-module, and let `K ⊆ M` be the largest
`R`-submodule whose support is nowhere dense in `Supp(M)`, as produced by
`Module.exists_isGreatest_isNowhereDense_support`. Let `Rₚ` be the localization of `R` at a
submonoid `p` and `g : M →ₗ[R] Mₚ` the localization of `M` at `p`. Then the localized submodule
`Kₚ ⊆ Mₚ` is the largest `Rₚ`-submodule of `Mₚ` whose support is nowhere dense in `Supp(Mₚ)`.
Since `(M ⧸ K)ₚ = Mₚ ⧸ Kₚ`, this says that removing the embedded associated primes commutes
with localization: `(M')ₚ = (Mₚ)'`. -/
@[stacks 02M7]
public theorem isGreatest_isNowhereDense_support_localized' (p : Submonoid R)
    [IsLocalization p Rₚ] (g : M →ₗ[R] Mₚ) [IsLocalizedModule p g] {K : Submodule R M}
    (hK : IsGreatest {K : Submodule R M |
        IsNowhereDense (Subtype.val ⁻¹' support R ↥K : Set ↥(support R M))} K) :
    IsGreatest {L : Submodule Rₚ Mₚ |
        IsNowhereDense (Subtype.val ⁻¹' support Rₚ ↥L : Set ↥(support Rₚ Mₚ))}
      (K.localized' Rₚ p g) := by apply Stacks.AssociatedPrimes.EmbeddedLocalized.solution ;
                                    assumption

end Module

end

/-!
# Quotienting by the annihilator kills embedded primes

All rings are commutative. For a ring `R` and an `R`-module `M`, the set of
associated primes of `M` is `associatedPrimes R M`, where `IsAssociatedPrime I M`
says that `I` is prime and is the radical of the annihilator of some `x : M`.

A prime `𝔭` is an *embedded associated prime of `M`* when it is an associated prime
of `M` that is not minimal among them, that is, when `𝔮 ⊊ 𝔭` for some associated
prime `𝔮`. Equivalently, `M` has no embedded associated prime exactly when `𝔮 ≤ 𝔭`
implies `𝔮 = 𝔭` for all `𝔭, 𝔮 ∈ associatedPrimes R M`. The *embedded primes of a
ring* `R` are the embedded associated primes of `R` as a module over itself. The
*annihilator ideal* of `M` is `{x : R | ∀ m : M, x • m = 0}`, that is,
`Module.annihilator R M`.

The main result: let `R` be a Noetherian commutative ring and `M` a finite
`R`-module with no embedded associated prime, and let `I` be the annihilator of `M`.
Then the ring `R ⧸ I`, viewed as a module over itself, has no embedded prime.
-/

@[expose] public section

/-- A prime `𝔭` is an *embedded associated prime of `M`* in the sense of Mathlib's
`associatedPrimes` if it lies in `associatedPrimes R M` and is not minimal there, i.e. there is
some `𝔮 ∈ associatedPrimes R M` with `𝔮 ⊊ 𝔭`.

Mathlib's `associatedPrimes` asks that a prime be the *radical* of the annihilator of an
element, whereas Stacks 00LA asks that it be *exactly* the annihilator of an element. The two
agree over a Noetherian ring, and so do the two notions of embedded associated prime
(`isEmbeddedAssociatedPrimeStacks_iff_isEmbeddedAssociatedPrime`); over a general ring they
differ. Stacks 02M5 itself is `IsEmbeddedAssociatedPrimeStacks`. -/
def IsEmbeddedAssociatedPrime
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (𝔭 : Ideal R) : Prop :=
  𝔭 ∈ associatedPrimes R M ∧ ∃ 𝔮 ∈ associatedPrimes R M, 𝔮 < 𝔭

/-- `M` *has no embedded associated primes* iff every associated prime of `M` is
minimal among the associated primes of `M`: for all `𝔭, 𝔮 ∈ associatedPrimes R M`,
if `𝔮 ≤ 𝔭` then `𝔮 = 𝔭`. -/
@[ega "IV 3.2.2" "partial"]
def HasNoEmbeddedAssociatedPrimes
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃𝔭⦄, 𝔭 ∈ associatedPrimes R M → ∀ ⦃𝔮⦄, 𝔮 ∈ associatedPrimes R M → 𝔮 ≤ 𝔭 → 𝔮 = 𝔭

/-- Correctness statement linking the two formulations of Definition 1:
`M` has no embedded associated primes iff no prime is an embedded associated
prime of `M`. -/
theorem hasNoEmbeddedAssociatedPrimes_iff
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    HasNoEmbeddedAssociatedPrimes R M ↔ ∀ 𝔭, ¬ IsEmbeddedAssociatedPrime R M 𝔭 := by
  refine ⟨fun h 𝔭 ⟨hp, 𝔮, hq, hlt⟩ ↦ hlt.ne (h hp hq hlt.le), fun h 𝔭 hp 𝔮 hq hle ↦ ?_⟩
  by_contra hne
  exact h 𝔭 ⟨hp, 𝔮, hq, lt_of_le_of_ne hle hne⟩

/-- **Stacks 02M5 (1).** Let `R` be a ring and `M` an `R`-module. A prime `𝔭` is an
*embedded associated prime of `M`* if it is an associated prime of `M` (Stacks 00LA: `𝔭` is
exactly the annihilator of some element of `M`) which is not minimal among the associated
primes of `M`. -/
@[stacks 02M5 "(1) embedded associated primes of a module"]
def IsEmbeddedAssociatedPrimeStacks
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (𝔭 : Ideal R) : Prop :=
  𝔭 ∈ assStacks R M ∧ ¬ Minimal (· ∈ assStacks R M) 𝔭

/-- **Stacks 02M5 (2).** The *embedded primes of a ring* `R` are the embedded associated
primes of `R` regarded as a module over itself. -/
@[stacks 02M5 "(2) embedded primes of a ring"]
def IsEmbeddedPrimeStacks (R : Type*) [CommRing R] (𝔭 : Ideal R) : Prop :=
  IsEmbeddedAssociatedPrimeStacks R R 𝔭

/-- An associated prime is embedded exactly when some associated prime lies strictly
below it. -/
theorem isEmbeddedAssociatedPrimeStacks_iff
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (𝔭 : Ideal R) :
    IsEmbeddedAssociatedPrimeStacks R M 𝔭 ↔
      𝔭 ∈ assStacks R M ∧ ∃ 𝔮 ∈ assStacks R M, 𝔮 < 𝔭 := by
  refine and_congr_right fun hp => ?_
  simp only [Minimal, hp, true_and, not_forall, exists_prop]
  exact ⟨fun ⟨𝔮, hq, hle, hne⟩ => ⟨𝔮, hq, lt_of_le_not_ge hle hne⟩,
    fun ⟨𝔮, hq, hlt⟩ => ⟨𝔮, hq, hlt.le, hlt.not_ge⟩⟩

/-- Over a Noetherian ring the Stacks notion of embedded associated prime agrees with the
one built on Mathlib's `associatedPrimes`, because the two notions of associated prime
agree there. -/
theorem isEmbeddedAssociatedPrimeStacks_iff_isEmbeddedAssociatedPrime
    (R M : Type*) [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    (𝔭 : Ideal R) :
    IsEmbeddedAssociatedPrimeStacks R M 𝔭 ↔ IsEmbeddedAssociatedPrime R M 𝔭 := by
  have key : assStacks R M = associatedPrimes R M := by
    ext q
    change IsAssociatedPrimeStacks R M q ↔ IsAssociatedPrime q M
    rw [isAssociatedPrime_iff]
    refine and_congr_right fun _ => exists_congr fun m => ?_
    rw [Submodule.colon_span, eq_comm]
  rw [isEmbeddedAssociatedPrimeStacks_iff, key]
  rfl

/-- The colon of `⊥` against the singleton `{f}`, for a tuple `f : ι → M`, is the infimum
over `i` of the colons of `⊥` against `{f i}`. -/
theorem bot_colon_singleton_pi_eq_inf {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] (f : ι → M) :
    (⊥ : Submodule R (ι → M)).colon {f}
      = Finset.univ.inf (fun i => (⊥ : Submodule R M).colon {f i}) := by
  ext r
  simp [Submodule.mem_colon_singleton, Submodule.mem_finsetInf, funext_iff]

/-- **Sub-lemma A.** An associated prime of the finite product module `ι → M` is an
associated prime of `M`. -/
theorem IsAssociatedPrime.of_pi {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] {p : Ideal R}
    (h : IsAssociatedPrime p (ι → M)) : IsAssociatedPrime p M := by
  let := Fintype.ofFinite ι
  obtain ⟨hp, f, hf⟩ := h
  rw [bot_colon_singleton_pi_eq_inf] at hf
  obtain ⟨i, _, hi⟩ := hp.inf_le'.mp (hf ▸ Ideal.le_radical)
  refine ⟨hp, f i, le_antisymm ?_ ?_⟩
  · rw [hf]
    exact Ideal.radical_mono (Finset.inf_le (Finset.mem_univ i))
  · rw [← hp.radical]
    exact Ideal.radical_mono hi

-- This is the rho `restrict` helper_02m8, repaired to thread the `.radical` through the
-- contraction (the rho version forgot the `.radical`).
/-- **Sub-lemma B.** If `P` is an associated prime of `R ⧸ I` regarded as a module over
`R ⧸ I`, then its contraction `comap (algebraMap R (R ⧸ I)) P` is an associated prime of
`R ⧸ I` regarded as a module over `R`. -/
theorem IsAssociatedPrime.comap_algebraMap_quotient {R : Type*} [CommRing R] {I : Ideal R}
    {P : Ideal (R ⧸ I)} (h : IsAssociatedPrime P (R ⧸ I)) :
    IsAssociatedPrime (Ideal.comap (algebraMap R (R ⧸ I)) P) (R ⧸ I) := by
  obtain ⟨hPrime, x, hx⟩ := h
  refine ⟨Ideal.comap_isPrime _ P, x, ?_⟩
  rw [hx, Ideal.comap_radical]
  congr 1

/-- The kernel of `r ↦ r • s` for a generating family `s` of `M` is the annihilator of `M`. -/
theorem ker_toSpanSingleton_eq_annihilator {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} {s : Fin n → M} (hs : Submodule.span R (Set.range s) = ⊤) :
    LinearMap.ker (LinearMap.toSpanSingleton R (Fin n → M) s) = Module.annihilator R M := by
  ext r
  simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Module.mem_annihilator]
  refine ⟨fun h m ↦ ?_, fun h ↦ funext fun i ↦ by simpa using h (s i)⟩
  induction (hs ▸ Submodule.mem_top : m ∈ Submodule.span R (Set.range s)) using
    Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using congrFun h i
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

/-- **Theorem (Stacks Tag 02M8).** Let `R` be a Noetherian commutative ring and
`M` a finite `R`-module having no embedded associated primes. Let `I` be the
annihilator of `M`. Then `R ⧸ I`, viewed as a module over itself, has no embedded
associated primes (i.e. the ring `R ⧸ I` has no embedded primes, in the sense of
`HasNoEmbeddedAssociatedPrimes`). -/
@[stacks 02M8]
theorem hasNoEmbeddedAssociatedPrimes_quotient_annihilator
    (R M : Type*) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasNoEmbeddedAssociatedPrimes R M) :
    HasNoEmbeddedAssociatedPrimes (R ⧸ Module.annihilator R M) (R ⧸ Module.annihilator R M) := by
  -- Build an injection `R ⧸ Module.annihilator R M ↪ (Fin n → M)`.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let g : R →ₗ[R] (Fin n → M) := LinearMap.toSpanSingleton R (Fin n → M) s
  have hker : LinearMap.ker g = Module.annihilator R M := ker_toSpanSingleton_eq_annihilator hs
  -- The induced map on the quotient, and its injectivity.
  have hle : (Module.annihilator R M : Submodule R R) ≤ LinearMap.ker g := hker.ge
  set f : (R ⧸ Module.annihilator R M) →ₗ[R] (Fin n → M) :=
    Submodule.liftQ (Module.annihilator R M : Submodule R R) g hle
  have hfinj : Function.Injective f :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ g hle hker.le)
  -- From an associated prime of `R ⧸ I` (as `R`-module), get an associated prime of `M`.
  have key : ∀ p : Ideal R, IsAssociatedPrime p (R ⧸ Module.annihilator R M) →
      IsAssociatedPrime p M := fun _ hp ↦ (hp.map_of_injective f hfinj).of_pi
  -- Now assemble the main argument.
  intro P hP Q hQ hQP
  rw [AssociatedPrimes.mem_iff] at hP hQ
  -- Comap to `R`.
  exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    (hM (AssociatedPrimes.mem_iff.mpr (key _ hP.comap_algebraMap_quotient))
      (AssociatedPrimes.mem_iff.mpr (key _ hQ.comap_algebraMap_quotient))
      (Ideal.comap_mono hQP))

end
