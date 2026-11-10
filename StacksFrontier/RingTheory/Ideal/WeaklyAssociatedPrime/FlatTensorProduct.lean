module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weakly associated primes of a tensor product with a flat module

Let `R → S` be a ring map, let `N` be an `S`-module which is flat as an `R`-module and let `M`
be an arbitrary `R`-module.  The tensor product `N ⊗[R] M` is again an `S`-module, through the
left factor, and this file compares its weakly associated primes with those of `M`:  a prime of
`S` weakly associated to `N ⊗[R] M` contracts to a prime of `R` weakly associated to `M`, as
soon as `M` has only finitely many weakly associated primes.

The same contraction statement is also proved with the finiteness hypothesis on `WeakAss_R(M)`
replaced by finite generation of the contracted prime.

In the local situation, that is after `R` has been localized at `p` and `S` at `q`, the residue
field `κ(p)` is `R / 𝔪_R`, so the fibre ring of [Stacks, Tag 05IG] is the quotient `S / 𝔪_R S`,
the fibre module is `N / 𝔪_R N`, and `q-bar` is the maximal ideal of `S / 𝔪_R S`. There, if the
maximal ideal of `S` is weakly associated to `N ⊗[R] M`, it is associated to `N / 𝔪_R N`.

## Main results

* `Module.Flat.exists_finset_tmul_of_smul_eq_zero`:  an element of `N ⊗[R] M` annihilated by a
  scalar `r` is a finite sum of tensors whose right-hand factors are annihilated by `r`.
* `Stacks.WeaklyAssociatedPrimes.finite_weaklyAssociatedPrimes_localizedModule`:  finiteness of
  the weakly associated primes passes to a localization.
* `Stacks.WeaklyAssociatedPrimes.exists_smul_pow_eq_zero_localizedModule_of_tensorProduct`:  with
  no finiteness hypothesis, the maximal ideal of `R_p` consists of scalars a power of which
  annihilates a nonzero element of `M_p`.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct`:  the contraction
  of a prime weakly associated to `N ⊗[R] M` is weakly associated to `M`.
* `Stacks.WeaklyAssociatedPrimes.weaklyAssociatedPrimes_tensorProduct_subset`:  the same
  statement as an inclusion of sets of primes.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct_of_fg`:  the same
  contraction statement with no finiteness hypothesis on `WeakAss_R(M)`, for a finitely
  generated contracted prime.
* `isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct`, in
  `Stacks.WeaklyAssociatedPrimes`:  the fibre clause of [Stacks, Tag 05IG] in the local
  situation.
* `isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_closedFibre`, in
  `Stacks.WeaklyAssociatedPrimes`:  the two together, that is the implication `⟹` of
  [Stacks, Tag 05IG] in the local situation.

## Implementation notes

The tensor product is written `N ⊗[R] M` with the flat module on the left, because the `S`-module
structure that `Mathlib` puts on a tensor product comes from the left factor and because
`Module.Flat.lTensor_exact` is stated for `N ⊗[R] -`.  Stacks writes the same module as
`M ⊗_R N`.

The conclusion of `Module.Flat.exists_finset_tmul_of_smul_eq_zero` is phrased with a
`Finset (N × M)` rather than with an indexed family, so that no universe is introduced beyond
those of `N` and `M`.

Associated primes of the closed fibre are taken in the strict sense of [Stacks, Tag 00LA],
`IsAssociatedPrimeStacks`. The closed fibre of `N` is spelled `N ⧸ 𝔪_R S • ⊤`.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 0547](https://stacks.math.columbia.edu/tag/0547)
* [Stacks Project, Tag 0566](https://stacks.math.columbia.edu/tag/0566)
* [Stacks Project, Tag 05C9](https://stacks.math.columbia.edu/tag/05C9)
* [Stacks Project, Tag 05DE](https://stacks.math.columbia.edu/tag/05DE)
* [Stacks Project, Tag 05DF](https://stacks.math.columbia.edu/tag/05DF)
-/

@[expose] public section

open TensorProduct

universe u v w t

/-- An element of `N ⊗[R] M` annihilated by a scalar `r : R`, with `N` flat over `R`, is a
finite sum of tensors `n ⊗ₜ m` in which every right-hand factor is annihilated by `r`. -/
theorem Module.Flat.exists_finset_tmul_of_smul_eq_zero {R : Type u} [CommRing R]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    {M : Type t} [AddCommGroup M] [Module R M] (r : R) (z : N ⊗[R] M) (hz : r • z = 0) :
    ∃ T : Finset (N × M), (∀ x ∈ T, r • x.2 = 0) ∧ z = ∑ x ∈ T, x.1 ⊗ₜ[R] x.2 := by
  classical
  set f : M →ₗ[R] M := LinearMap.lsmul R M r with hf
  have hex : Function.Exact (LinearMap.lTensor N (LinearMap.ker f).subtype)
      (LinearMap.lTensor N f) :=
    Module.Flat.lTensor_exact N (LinearMap.exact_subtype_ker_map f)
  have hzk : LinearMap.lTensor N f z = 0 := by
    have hlt : LinearMap.lTensor N f = LinearMap.lsmul R (N ⊗[R] M) r := by
      ext n m
      simp [hf, TensorProduct.tmul_smul]
    rw [hlt]
    simpa using hz
  obtain ⟨y, hy⟩ := (hex z).mp hzk
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset y
  have hinj : ∀ a ∈ T, ∀ b ∈ T, (a.1, (a.2 : M)) = (b.1, (b.2 : M)) → a = b := by
    rintro ⟨n₁, k₁⟩ - ⟨n₂, k₂⟩ - hab
    simp only [Prod.mk.injEq, Subtype.coe_inj] at hab
    simp [hab.1, hab.2]
  refine ⟨T.image fun x => (x.1, (x.2 : M)), ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨n, k⟩, -, rfl⟩ := Finset.mem_image.mp hx
    exact LinearMap.mem_ker.mp k.2
  · rw [← hy, hT, map_sum, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun x _ => by simp

namespace Stacks.WeaklyAssociatedPrimes

/-- The two spellings of the set of weakly associated primes — as a set of ideals and as a set
of points of the prime spectrum — are finite together. -/
theorem finite_weakAss_iff {R : Type u} [CommRing R] {M : Type t} [AddCommGroup M]
    [Module R M] : (weakAss R M).Finite ↔ (weaklyAssociatedPrimes R M).Finite := by
  refine ⟨fun h => (h.image PrimeSpectrum.asIdeal).subset ?_, fun h => ?_⟩
  · intro I hI
    exact ⟨⟨I, hI.isPrime R M⟩, hI, rfl⟩
  · exact h.preimage (f := PrimeSpectrum.asIdeal) fun _ _ _ _ he => PrimeSpectrum.ext he

/-- Finiteness of the set of weakly associated primes passes to a localization:  if `M` has
finitely many weakly associated primes over `R`, then `T⁻¹M` has finitely many over `T⁻¹R`. -/
theorem finite_weaklyAssociatedPrimes_localizedModule {R : Type u} [CommRing R]
    {M : Type t} [AddCommGroup M] [Module R M] (T : Submonoid R)
    (h : (weaklyAssociatedPrimes R M).Finite) :
    (weaklyAssociatedPrimes (Localization T) (LocalizedModule T M)).Finite := by
  rw [← finite_weakAss_iff] at h ⊢
  refine Set.Finite.of_finite_image (h.subset ?_)
    (PrimeSpectrum.localization_comap_injective (Localization T) T).injOn
  rw [weakAss_localizedModule_eq_image T (M := M) |>.symm,
    ← weakAss_inter_image_eq_weakAss_localizedModule T (M := M)]
  exact fun p hp => hp.1

/-- The scalars that annihilate a nonzero element of the localization `M_p` form a set covering
the maximal ideal of `R_p`;  if moreover `M_p` has finitely many weakly associated primes, that
maximal ideal is itself weakly associated to `M_p`. -/
private theorem isWeaklyAssociatedPrime_maximalIdeal_of_forall_exists_smul_pow_eq_zero
    {A : Type u} [CommRing A] [IsLocalRing A] {P : Type t} [AddCommGroup P] [Module A P]
    (hfin : (weaklyAssociatedPrimes A P).Finite)
    (hzd : ∀ c ∈ IsLocalRing.maximalIdeal A, ∃ (n : ℕ) (x : P), x ≠ 0 ∧ c ^ n • x = 0) :
    IsWeaklyAssociatedPrime A P (IsLocalRing.maximalIdeal A) := by
  classical
  have hcov : ∀ c ∈ IsLocalRing.maximalIdeal A, ∃ I ∈ weaklyAssociatedPrimes A P, c ∈ I := by
    intro c hc
    obtain ⟨n, x, hx, hcx⟩ := hzd c hc
    have hne : (A ∙ x).annihilator ≠ ⊤ := fun htop => hx <| by
      have hone : (1 : A) ∈ (A ∙ x).annihilator := htop ▸ Submodule.mem_top
      simpa using (Submodule.mem_annihilator_span_singleton x 1).mp hone
    obtain ⟨⟨I, hI⟩⟩ := Ideal.nonempty_minimalPrimes hne
    refine ⟨I, ⟨x, hI⟩, hI.left.left.mem_of_pow_mem n ?_⟩
    exact hI.left.right ((Submodule.mem_annihilator_span_singleton x _).mpr hcx)
  set F : Finset (Ideal A) := hfin.toFinset with hF
  have hsub : (IsLocalRing.maximalIdeal A : Set A) ⊆ ⋃ I ∈ (F : Set (Ideal A)), (I : Set A) := by
    intro c hc
    obtain ⟨I, hI, hcI⟩ := hcov c hc
    exact Set.mem_biUnion (by rw [hF]; simpa using hI) hcI
  have hprime : ∀ I ∈ F, I ≠ ⊥ → I ≠ ⊥ → I.IsPrime := by
    intro I hI _ _
    have hIw : I ∈ weaklyAssociatedPrimes A P := by rw [hF] at hI; simpa using hI
    exact hIw.isPrime A P
  obtain ⟨I, hIF, hle⟩ := (Ideal.subset_union_prime (⊥ : Ideal A) ⊥ hprime).mp hsub
  have hIw : I ∈ weaklyAssociatedPrimes A P := by rw [hF] at hIF; simpa using hIF
  exact le_antisymm (IsLocalRing.le_maximalIdeal (hIw.isPrime A P).ne_top) hle ▸ hIw

/-- If `q` is minimal over the annihilator of `z` and `x` has image in `q`, then some power of `x`
kills `y • z` for a `y ∉ q`. -/
private theorem exists_notMem_pow_smul_smul_eq_zero
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {A : Type w} [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
    {q : Ideal S} {z : A} (hq : q ∈ (Submodule.span S {z}).annihilator.minimalPrimes) {x : R}
    (hx : algebraMap R S x ∈ q) : ∃ y ∉ q, ∃ n : ℕ, x ^ n • y • z = 0 := by
  obtain ⟨y, hy, n, hyn⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hq hx
  refine ⟨y, hy, n, ?_⟩
  rw [← algebraMap_smul S, smul_smul, map_pow, mul_comm]
  exact (Submodule.mem_annihilator_span_singleton z _).mp hyn

/-- If `q` is minimal over the annihilator of `z`, `y ∉ q` and `a` is not in the contraction of
`q`, then `a • y • z ≠ 0`. -/
private theorem smul_smul_ne_zero_of_notMem_comap
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {A : Type w} [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
    {q : Ideal S} {z : A} (hq : q ∈ (Submodule.span S {z}).annihilator.minimalPrimes) {y : S}
    (hy : y ∉ q) {a : R} (ha : a ∉ q.comap (algebraMap R S)) : a • y • z ≠ 0 := by
  intro h
  have h0 : (algebraMap R S a * y) • z = 0 := by rwa [mul_smul, algebraMap_smul]
  have hqp : q.IsPrime := hq.left.left
  exact (hqp.mem_or_mem (hq.left.right
    ((Submodule.mem_annihilator_span_singleton z _).mpr h0))).elim ha hy

/-- If each `m x`, `x ∈ T`, is killed by some scalar outside a prime `p`, then a single scalar
outside `p` kills all of them. -/
private theorem exists_notMem_forall_smul_eq_zero
    {R : Type u} [CommRing R] {A : Type w} [AddCommGroup A] [Module R A] {ι : Type*}
    (p : Ideal R) [p.IsPrime] (T : Finset ι) (m : ι → A)
    (h : ∀ x ∈ T, ∃ a ∉ p, a • m x = 0) : ∃ a ∉ p, ∀ x ∈ T, a • m x = 0 := by
  classical
  choose! a ha hax using h
  refine ⟨∏ x ∈ T, a x, fun hmem => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx, hxp⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact ha x hx hxp
  · obtain ⟨c, hc⟩ : a x ∣ ∏ x' ∈ T, a x' := Finset.dvd_prod_of_mem a hx
    rw [hc, mul_comm, mul_smul, hax x hx, smul_zero]

/-- For a prime `q` of `S` weakly associated to `N ⊗[R] M` with contraction `p`, every element
of `p` has a power annihilating a nonzero element of the localization `M_p`. -/
private theorem exists_smul_pow_eq_zero_localizedModule_of_mem
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] {M : Type t} [AddCommGroup M] [Module R M]
    {q : Ideal S} {z : N ⊗[R] M}
    (hq : q ∈ (Submodule.span S {z}).annihilator.minimalPrimes)
    (p : Ideal R) [p.IsPrime] (hpq : q.comap (algebraMap R S) = p) {r : R} (hr : r ∈ p) :
    ∃ (n : ℕ) (x : LocalizedModule.AtPrime p M), x ≠ 0 ∧ (r ^ n) • x = 0 := by
  classical
  obtain ⟨y, hy, n, hrz'⟩ := exists_notMem_pow_smul_smul_eq_zero hq
    (x := r) (Ideal.mem_comap.mp (hpq ▸ hr))
  have hkey := fun a (ha : a ∉ p) => smul_smul_ne_zero_of_notMem_comap hq hy (hpq ▸ ha)
  obtain ⟨T, hT0, hTsum⟩ := Module.Flat.exists_finset_tmul_of_smul_eq_zero (r ^ n) _ hrz'
  by_cases hall : ∀ x ∈ T,
      (LocalizedModule.mk x.2 (1 : p.primeCompl) : LocalizedModule.AtPrime p M) = 0
  · exfalso
    obtain ⟨a, ha, hax⟩ := exists_notMem_forall_smul_eq_zero p T (fun x => x.2) fun x hx => by
      obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl M)).mp
        (show LocalizedModule.mkLinearMap p.primeCompl M x.2 = 0 from hall x hx)
      exact ⟨s, s.2, hs⟩
    refine hkey a ha ?_
    rw [hTsum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hax x hx, TensorProduct.tmul_zero]
  · push Not at hall
    obtain ⟨x, hx, hxne⟩ := hall
    refine ⟨n, LocalizedModule.mk x.2 (1 : p.primeCompl), hxne, ?_⟩
    rw [LocalizedModule.smul'_mk, hT0 x hx, LocalizedModule.zero_mk]

/-- **Every element of the maximal ideal of `R_p` annihilates, up to a power, a nonzero element
of `M_p`**, for `p` the contraction of a prime `q` of `S` weakly associated to `N ⊗[R] M` and `N`
flat over `R`. -/
theorem exists_smul_pow_eq_zero_localizedModule_of_tensorProduct
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] {M : Type t} [AddCommGroup M] [Module R M]
    {q : Ideal S} (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q)
    (p : Ideal R) [p.IsPrime] (hpq : q.comap (algebraMap R S) = p)
    {c : Localization.AtPrime p} (hc : c ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    ∃ (n : ℕ) (x : LocalizedModule.AtPrime p M), x ≠ 0 ∧ c ^ n • x = 0 := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
  have hr : r ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff _ p r s).mp hc
  obtain ⟨n, x, hx, hrx⟩ := exists_smul_pow_eq_zero_localizedModule_of_mem hz p hpq hr
  refine ⟨n, x, hx, ?_⟩
  change IsLocalization.mk' (Localization.AtPrime p) r s ^ n • x = 0
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_pow, mul_comm, mul_smul, ← map_pow,
    algebraMap_smul, hrx, smul_zero]

/-- **The contraction of a weakly associated prime of a flat base change.**  Let `R → S` be a
ring map, let `N` be an `S`-module which is flat as an `R`-module and let `M` be an `R`-module
with only finitely many weakly associated primes.  Then the contraction to `R` of a prime of `S`
weakly associated to `N ⊗[R] M` is weakly associated to `M`. -/
theorem isWeaklyAssociatedPrime_comap_tensorProduct
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] {M : Type t} [AddCommGroup M] [Module R M]
    (hfin : (weaklyAssociatedPrimes R M).Finite) {q : Ideal S}
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) := by
  classical
  have hqp : q.IsPrime := hq.isPrime S (N ⊗[R] M)
  set p : Ideal R := q.comap (algebraMap R S) with hp
  have : p.IsPrime := hp ▸ Ideal.comap_isPrime (algebraMap R S) q
  have hloc : IsWeaklyAssociatedPrime (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
    isWeaklyAssociatedPrime_maximalIdeal_of_forall_exists_smul_pow_eq_zero
      (finite_weaklyAssociatedPrimes_localizedModule p.primeCompl hfin)
      fun _ hc => exists_smul_pow_eq_zero_localizedModule_of_tensorProduct hq p hp.symm hc
  exact (weaklyAssociated_iff_localization (M := M) p).mpr hloc

/-- **The contraction of a weakly associated prime of a flat base change**, as an inclusion of
sets of primes:  contraction along `R → S` carries `WeakAss_S(N ⊗_R M)` into `WeakAss_R(M)`,
when `N` is flat over `R` and `M` has finitely many weakly associated primes. -/
theorem weaklyAssociatedPrimes_tensorProduct_subset
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] {M : Type t} [AddCommGroup M] [Module R M]
    (hfin : (weaklyAssociatedPrimes R M).Finite) :
    Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S (N ⊗[R] M) ⊆
      weaklyAssociatedPrimes R M := by
  rintro I ⟨q, hq, rfl⟩
  exact isWeaklyAssociatedPrime_comap_tensorProduct hfin hq

/-- **The contraction of a weakly associated prime of a flat base change, for a finitely
generated prime.**  Let `R → S` be a ring map, let `N` be an `S`-module which is flat as an
`R`-module and let `M` be an `R`-module.  If a prime `q` of `S` is weakly associated to
`N ⊗[R] M` and its contraction `p` is finitely generated — for instance if `R` is Noetherian —
then `p` is weakly associated to `M`. -/
@[ega "IV 3.3.8" "special case"]
theorem isWeaklyAssociatedPrime_comap_tensorProduct_of_fg
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] {M : Type t} [AddCommGroup M] [Module R M]
    {q : Ideal S} (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q)
    (hfg : (q.comap (algebraMap R S)).FG) :
    IsWeaklyAssociatedPrime R M (q.comap (algebraMap R S)) := by
  classical
  obtain ⟨z, hz⟩ := hq
  have hqp : q.IsPrime := hz.left.left
  set p : Ideal R := q.comap (algebraMap R S) with hp
  have hpp : p.IsPrime := hp ▸ Ideal.comap_isPrime (algebraMap R S) q
  obtain ⟨s, hs⟩ := hfg
  have hmemp : ∀ f ∈ s, algebraMap R S f ∈ q := fun f hf =>
    Ideal.mem_comap.mp (hp ▸ hs ▸ Ideal.subset_span (Finset.mem_coe.mpr hf))
  choose! Y hYq k hk using fun f (hf : f ∈ s) =>
    exists_notMem_pow_smul_smul_eq_zero hz (x := f) (hmemp f hf)
  set y : S := ∏ f ∈ s, Y f with hy
  have hyq : y ∉ q := fun hmem => by
    obtain ⟨f, hf, hfq⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hYq f hf hfq
  have hkill : ∀ f ∈ s, (f ^ k f) • y • z = 0 := by
    intro f hf
    obtain ⟨c, hc⟩ : Y f ∣ y := Finset.dvd_prod_of_mem Y hf
    rw [hc, mul_comm, mul_smul, smul_comm, hk f hf, smul_zero]
  have hkey := fun a (ha : a ∉ p) => smul_smul_ne_zero_of_notMem_comap hz hyq ha
  set φ : M →ₗ[R] ({f // f ∈ s} → M) :=
    LinearMap.pi fun i => LinearMap.lsmul R M ((i : R) ^ k (i : R)) with hφ
  have hcomp : ∀ (x : N ⊗[R] M) (i : {f // f ∈ s}),
      TensorProduct.piRightHom R R N (fun _ : {f // f ∈ s} => M)
        (LinearMap.lTensor N φ x) i = ((i : R) ^ k (i : R)) • x := by
    intro x i
    induction x with
    | tmul a m => simp [hφ, TensorProduct.smul_tmul']
    | add x₁ x₂ h₁ h₂ => simp [h₁, h₂, smul_add]
  have hzφ : LinearMap.lTensor N φ (y • z) = 0 := by
    refine (TensorProduct.piRight R R N (fun _ : {f // f ∈ s} => M)).injective ?_
    rw [map_zero]
    funext i
    rw [TensorProduct.piRight_apply, hcomp, Pi.zero_apply]
    exact hkill (i : R) i.2
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact N (LinearMap.exact_subtype_ker_map φ) (y • z)).mp hzφ
  obtain ⟨U, hU⟩ := TensorProduct.exists_finset w
  have hex : ∃ x ∈ U, (R ∙ ((x.2 : LinearMap.ker φ) : M)).annihilator ≤ p := by
    by_contra hall
    push Not at hall
    obtain ⟨a, ha, hax⟩ := exists_notMem_forall_smul_eq_zero p U (fun x => x.2) fun x hx => by
      obtain ⟨a, ha, hane⟩ := Set.not_subset.mp (hall x hx)
      exact ⟨a, hane, Subtype.ext ((Submodule.mem_annihilator_span_singleton _ a).mp ha)⟩
    refine hkey a ha ?_
    rw [← hw, ← map_smul, hU, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [← TensorProduct.tmul_smul, hax x hx, TensorProduct.tmul_zero, map_zero]
  obtain ⟨x, hxU, hxle⟩ := hex
  refine ⟨((x.2 : LinearMap.ker φ) : M), minimalPrimes_of_radical_condition _ p hpp hxle ?_⟩
  have hker : ∀ i : {g // g ∈ s},
      ((i : R) ^ k (i : R)) • ((x.2 : LinearMap.ker φ) : M) = 0 := by
    intro i
    have h0 : φ ((x.2 : LinearMap.ker φ) : M) = 0 := LinearMap.mem_ker.mp x.2.2
    simpa [hφ] using congrFun h0 i
  have hrad : p ≤ (R ∙ ((x.2 : LinearMap.ker φ) : M)).annihilator.radical := by
    rw [← hs, Ideal.span_le]
    intro f hf
    exact ⟨k f, (Submodule.mem_annihilator_span_singleton _ _).mpr (hker ⟨f, hf⟩)⟩
  intro f hf
  obtain ⟨n, hn⟩ := hrad hf
  exact ⟨1, fun hone => hpp.ne_top (Ideal.eq_top_of_isUnit_mem p hone isUnit_one), n,
    by simpa using hn⟩

section ClosedFibre

open IsLocalRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {M : Type t} [AddCommGroup M] [Module R M]

/-- A scalar acting injectively on the closed fibre of `N` is not a zerodivisor on
`N ⊗[R] M`. -/
private theorem injective_smul_of_mem_nonZeroSMulDivisors
    [Module.FinitePresentation S N] [Module.Flat R N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    {c : S} (hc : c ∈ nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))) :
    Function.Injective fun x : N ⊗[R] M => c • x := by
  have h := Stacks.UniversalInjectivity.universallyInjectivePoly_lsmul_of_nonZeroSMulDivisors
    (N := N) hS ⟨c, hc⟩ M
  intro x y hxy
  exact h ((AlgebraTensorModule.smul_eq_lsmul_rTensor _ x).symm.trans
    (hxy.trans (AlgebraTensorModule.smul_eq_lsmul_rTensor _ y)))

/-- **The fibre clause of [Stacks, Tag 05IG], in the local situation.**  Let `R → S` be a local
homomorphism of local rings which is essentially of finite presentation, let `N` be an `S`-module
finitely presented over `S` and flat over `R`, and let `M` be an `R`-module.  If the maximal
ideal of `S` is weakly associated to `N ⊗[R] M`, then it is an associated prime — in the strict
sense of Stacks Tag 00LA — of the closed fibre `N / 𝔪_R N`.

This is the implication `𝔮 ∈ WeakAss_S(M ⊗_R N) ⟹ 𝔮-bar ∈ Ass_{S-bar}(N-bar)` of Tag 05IG, read
after localizing `R` at `𝔭` and `S` at `𝔮`:  the residue field `κ(𝔭)` is then `R / 𝔪_R`, so the
fibre ring `S ⊗_R κ(𝔭)` is the quotient `S / 𝔪_R S` and the fibre module is `N / 𝔪_R N`, and
`𝔮-bar` is the maximal ideal of `S / 𝔪_R S`. -/
theorem isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct
    [Module.FinitePresentation S N] [Module.Flat R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    [Module.Finite (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) (maximalIdeal S)) :
    IsAssociatedPrimeStacks S
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))
      (maximalIdeal S) := by
  classical
  set I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R) with hI
  set H := N ⧸ (I • (⊤ : Submodule S N)) with hH
  by_contra hcon
  have hndisj : ¬ Disjoint ((nonZeroSMulDivisors S H : Submonoid S) : Set S)
      ((maximalIdeal S : Ideal S) : Set S) := by
    intro hdisj
    obtain ⟨P, hP, hle⟩ :=
      (Stacks.UniversalInjectivity.localization_disjoint_iff_exists_assStacks
        (A := S) (M := H) I (maximalIdeal S)).mp hdisj
    exact hcon ((maximalIdeal.isMaximal S).eq_of_le hP.1.ne_top hle ▸ hP)
  obtain ⟨a, hareg, ham⟩ := Set.not_disjoint_iff.mp hndisj
  obtain ⟨z, hz⟩ := hq
  obtain ⟨y, hy, n, hzero⟩ := exists_notMem_pow_smul_smul_eq_zero hz (x := a) ham
  refine absurd (hz.left.right ?_) hy
  refine (Submodule.mem_annihilator_span_singleton z y).mpr ?_
  refine injective_smul_of_mem_nonZeroSMulDivisors (M := M) hS (pow_mem hareg n) ?_
  simpa using hzero

/-- **The implication `⟹` of [Stacks, Tag 05IG], in the local situation and for a finitely
generated maximal ideal.**  If the maximal ideal of `S` is weakly associated to `N ⊗[R] M`, then
the maximal ideal of `R` is weakly associated to `M` and the maximal ideal of `S` is associated
to the closed fibre `N / 𝔪_R N`. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_closedFibre
    [Module.FinitePresentation S N] [Module.Flat R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    [Module.Finite (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (hfg : (maximalIdeal R).FG)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) (maximalIdeal S)) :
    IsWeaklyAssociatedPrime R M (maximalIdeal R) ∧
      IsAssociatedPrimeStacks S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))
        (maximalIdeal S) := by
  refine ⟨?_,
    isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct hS hq⟩
  have h := isWeaklyAssociatedPrime_comap_tensorProduct_of_fg hq
    (by rwa [IsLocalRing.maximalIdeal_comap])
  rwa [IsLocalRing.maximalIdeal_comap] at h

end ClosedFibre

end Stacks.WeaklyAssociatedPrimes

end
