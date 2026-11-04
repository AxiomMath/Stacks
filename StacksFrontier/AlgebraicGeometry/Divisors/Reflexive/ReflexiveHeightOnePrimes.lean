module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexiveSectionSupportHeight

/-!
# The height one primes cut out by a section of a reflexive module

Let `A` be a Noetherian normal domain, let `M` be a finite reflexive `A`-module of rank one, let
`s ∈ M` be nonzero, and let `𝔭₁, …, 𝔭_r` be the height one primes of `A` in the support of
`M ⧸ A·s`. On `Spec(A)`, the open `U` of [Stacks, Tag 0EBN], the locus where `s` induces an
isomorphism `𝒪_{X, x} → ℱ_x` for `X = Spec(A)` and `ℱ = M^~`, is the set of primes `𝔭` at which
`A_𝔭 → M_𝔭`, `a ↦ a·s`, is bijective. This file proves the first display of [Stacks, Tag 0EBQ],

`U = Spec(A) \ (V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r))`,

as the conjunction of

1. `U = Spec(A) \ Supp(M ⧸ A·s)`, which holds for any nonzero section of a torsion free module over
   a domain;
2. `Supp(M ⧸ A·s) = V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)`, the affine case of [Stacks, Tag 0EBP].

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.toSpanSingletonAtPrime`: the map `A_𝔭 → M_𝔭`,
  `a ↦ a·s`.
* `Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.sectionIsomorphismPrimes`: the set of primes
  at which that map is bijective, i.e. the open `U` of [Stacks, Tag 0EBN] read on `Spec(A)`.
* `Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.heightOneSupport`: the primes `𝔭₁, …, 𝔭_r`,
  namely the height one primes in the support of `M ⧸ A·s`.
* `Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.heightOneSupportZeroLocus`: the closed set
  `V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)`.

## Main results

* `mem_sectionIsomorphismPrimes_iff`: a prime lies in `U` if and only if it is outside the support
  of `M ⧸ A·s`.
* `sectionIsomorphismPrimes_eq_compl_support`: assertion (1).
* `heightOneSupportZeroLocus_subset_support`: the inclusion `V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r) ⊆ Supp(M ⧸ A·s)`.
* `rank_quotient_span_singleton_eq_zero`, `bot_notMem_support_quotient`: for `M` torsion free of
  rank one, a nonzero `s` spans the generic fibre of `M`.
* `support_subset_heightOneSupportZeroLocus`: the inclusion `Supp(M ⧸ A·s) ⊆ V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)`.
* `sectionIsomorphismPrimes_eq_compl_heightOneSupportZeroLocus`:
  `U = Spec(A) \ (V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r))`.

## References

* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBP](https://stacks.math.columbia.edu/tag/0EBP)
-/

@[expose] public section

universe u v

namespace Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-! ### The locus where a section generates -/

/-- Multiplication by a section `s ∈ M`: the map `A_𝔭 → M_𝔭`, `a ↦ a·s`. -/
def toSpanSingletonAtPrime (s : M) (p : PrimeSpectrum A) :
    Localization.AtPrime p.asIdeal →ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M :=
  LinearMap.toSpanSingleton _ _ (LocalizedModule.mk s 1)

/-- The set of primes `𝔭` of `A` at which `s : A_𝔭 → M_𝔭` is an isomorphism. This is the open `U`
of [Stacks, Tag 0EBN] read on the affine scheme `Spec(A)`. -/
def sectionIsomorphismPrimes (A : Type u) [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (s : M) : Set (PrimeSpectrum A) :=
  {p | Function.Bijective (toSpanSingletonAtPrime s p)}

/-- A prime avoids the support of `M ⧸ A·s` exactly when every element of `M` is carried into `A·s`
by a scalar outside the prime. -/
theorem notMem_support_quotient_iff (s : M) (p : PrimeSpectrum A) :
    p ∉ Module.support A (M ⧸ (A ∙ s)) ↔ ∀ m : M, ∃ r ∉ p.asIdeal, r • m ∈ A ∙ s := by
  rw [Module.notMem_support_iff, Submodule.subsingleton_iff_forall_exists_smul_mem
    p.asIdeal.primeCompl (A ∙ s) (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _)]
  exact forall_congr' fun m =>
    ⟨fun ⟨t, ht⟩ => ⟨t, t.2, ht⟩, fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, h⟩⟩

/-- The map `A_𝔭 → M_𝔭`, `a ↦ a·s`, sends `a / r` to `(a • s) / r`. -/
private theorem toSpanSingletonAtPrime_mk (s : M) (p : PrimeSpectrum A) (a : A)
    (r : p.asIdeal.primeCompl) :
    toSpanSingletonAtPrime s p (Localization.mk a r) = LocalizedModule.mk (a • s) r := by
  rw [toSpanSingletonAtPrime, LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk,
    mul_one]

/-- The map `A_𝔭 → M_𝔭`, `a ↦ a·s`, is surjective if and only if every element of `M` is carried
into `A·s` by a scalar outside `𝔭`. -/
theorem surjective_toSpanSingletonAtPrime_iff (s : M) (p : PrimeSpectrum A) :
    Function.Surjective (toSpanSingletonAtPrime s p) ↔
      ∀ m : M, ∃ r ∉ p.asIdeal, r • m ∈ A ∙ s := by
  refine ⟨fun hsurj m => ?_, fun h y => ?_⟩
  · obtain ⟨x, hx⟩ := hsurj (LocalizedModule.mk m 1)
    induction x using Localization.induction_on with
    | H ar =>
      obtain ⟨a, r⟩ := ar
      rw [toSpanSingletonAtPrime_mk, LocalizedModule.mk_eq] at hx
      obtain ⟨u, hu⟩ := hx
      simp only [Submonoid.smul_def, one_smul, ← mul_smul] at hu
      exact ⟨(u : A) * (r : A), p.asIdeal.primeCompl.mul_mem u.2 r.2,
        Submodule.mem_span_singleton.2 ⟨(u : A) * a, hu⟩⟩
  · induction y using LocalizedModule.induction_on with
    | _ m t =>
      obtain ⟨r, hr, hrm⟩ := h m
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hrm
      refine ⟨Localization.mk a (⟨r, hr⟩ * t), ?_⟩
      rw [toSpanSingletonAtPrime_mk, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]
      rw [mul_smul, ha, ← mul_smul, mul_comm (t : A) r]

/-- For a nonzero section of a torsion free module over a domain, `A_𝔭 → M_𝔭`, `a ↦ a·s`, is
injective. -/
theorem injective_toSpanSingletonAtPrime [IsDomain A] [Module.IsTorsionFree A M] {s : M}
    (hs : s ≠ 0) (p : PrimeSpectrum A) :
    Function.Injective (toSpanSingletonAtPrime s p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Localization.induction_on with
  | H ar =>
    obtain ⟨a, r⟩ := ar
    rw [toSpanSingletonAtPrime_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hx
    obtain ⟨u, hu⟩ := hx
    simp only [Submonoid.smul_def, one_smul, smul_zero, ← mul_smul] at hu
    have hua : (u : A) * a = 0 := by
      by_contra hne
      exact hs (smul_right_injective M hne (by simpa using hu))
    rw [(mul_eq_zero.1 hua).resolve_left fun h => u.2 (h ▸ p.asIdeal.zero_mem),
      Localization.mk_zero]

/-- A prime lies in the locus where a nonzero section of a torsion free module over a domain is an
isomorphism exactly when it avoids the support of `M ⧸ A·s`. -/
theorem mem_sectionIsomorphismPrimes_iff [IsDomain A] [Module.IsTorsionFree A M] {s : M}
    (hs : s ≠ 0) (p : PrimeSpectrum A) :
    p ∈ sectionIsomorphismPrimes A s ↔ p ∉ Module.support A (M ⧸ (A ∙ s)) := by
  rw [notMem_support_quotient_iff, ← surjective_toSpanSingletonAtPrime_iff]
  exact ⟨And.right, fun h => ⟨injective_toSpanSingletonAtPrime hs p, h⟩⟩

/-! ### The height one primes in the support -/

/-- The primes `𝔭₁, …, 𝔭_r` of [Stacks, Tag 0EBQ]: the height one primes of `A` in the support of
`M ⧸ A·s`. -/
def heightOneSupport (A : Type u) [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (s : M) : Set (PrimeSpectrum A) :=
  {p | p.asIdeal.height = 1 ∧ p ∈ Module.support A (M ⧸ (A ∙ s))}

/-- The closed set `V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)` of [Stacks, Tag 0EBQ]. -/
def heightOneSupportZeroLocus (A : Type u) [CommRing A] {M : Type v} [AddCommGroup M]
    [Module A M] (s : M) : Set (PrimeSpectrum A) :=
  ⋃ p ∈ heightOneSupport A s, PrimeSpectrum.zeroLocus (p.asIdeal : Set A)

/-- `V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)` is contained in the support of `M ⧸ A·s`. -/
theorem heightOneSupportZeroLocus_subset_support (A : Type u) [CommRing A] {M : Type v}
    [AddCommGroup M] [Module A M] (s : M) :
    heightOneSupportZeroLocus A s ⊆ Module.support A (M ⧸ (A ∙ s)) :=
  Set.iUnion₂_subset fun _ hp _ hq =>
    Module.mem_support_mono ((PrimeSpectrum.mem_zeroLocus _ _).1 hq) hp.2

/-- For `A` a Noetherian normal domain, `M` a finite reflexive `A`-module and `s ∈ M` nonzero, the
set of primes at which `s : A_𝔭 → M_𝔭` is an isomorphism is the complement of the support of
`M ⧸ A·s`. -/
@[stacks 0EBQ "the open U of Lemma 31.30.3, on Spec(A), identified with the complement of the
support of M/As; the identification of that support with V(p_1) ∪ … ∪ V(p_r) is Lemma 31.30.4
(Tag 0EBP)"]
theorem sectionIsomorphismPrimes_eq_compl_support [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] [Module.IsReflexive A M] {s : M} (hs : s ≠ 0) :
    sectionIsomorphismPrimes A s = (Module.support A (M ⧸ (A ∙ s)))ᶜ :=
  Set.ext fun p => mem_sectionIsomorphismPrimes_iff hs p

/-! ### The rank one hypothesis -/

/-- For a torsion free module of rank one over a domain, a nonzero element spans the generic fibre:
the quotient `M ⧸ A·s` has rank zero. -/
theorem rank_quotient_span_singleton_eq_zero [IsDomain A] [Module.IsTorsionFree A M]
    (hrank : Module.rank A M = 1) {s : M} (hs : s ≠ 0) :
    Module.rank A (M ⧸ (A ∙ s)) = 0 := by
  have hspan : Module.rank A (A ∙ s) = 1 := by
    have h := (LinearEquiv.toSpanNonzeroSingleton A M s hs).lift_rank_eq
    rw [CommSemiring.rank_self, Cardinal.lift_one] at h
    exact Cardinal.lift_eq_one.mp h.symm
  have hrn := rank_quotient_add_rank_of_isDomain (R := A) (M := M) (A ∙ s)
  rw [hspan, hrank] at hrn
  exact Cardinal.add_one_inj.1 (hrn.trans (zero_add 1).symm)

/-- For a torsion free module `M` of rank one over a domain and `s ∈ M` nonzero, the zero ideal is
outside the support of `M ⧸ A·s`. -/
theorem bot_notMem_support_quotient [IsDomain A] [Module.IsTorsionFree A M]
    (hrank : Module.rank A M = 1) {s : M} (hs : s ≠ 0) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ (A ∙ s)) := by
  rw [notMem_support_quotient_iff]
  intro m
  obtain ⟨a, ha, hax⟩ := rank_eq_zero_iff.mp
    (rank_quotient_span_singleton_eq_zero hrank hs) ((A ∙ s).mkQ m)
  refine ⟨a, by simpa using ha, ?_⟩
  rwa [← Submodule.ker_mkQ (A ∙ s), LinearMap.mem_ker, map_smul]

/-- For `A` a Noetherian normal domain, `M` a finite reflexive `A`-module of rank one and `s ∈ M`
nonzero, the support of `M ⧸ A·s` is contained in `V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)`. -/
theorem support_subset_heightOneSupportZeroLocus [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] [Module.IsReflexive A M]
    (hrank : Module.rank A M = 1) {s : M} (hs : s ≠ 0) :
    Module.support A (M ⧸ (A ∙ s)) ⊆ heightOneSupportZeroLocus A s := by
  intro q hq
  obtain ⟨p, hple, hpsupp, hpq⟩ :=
    Stacks.AlgebraicGeometry.ReflexiveSectionSupport.exists_le_of_mem_support (M := M) hs hq
  have hpne : p.asIdeal ≠ ⊥ := fun h => bot_notMem_support_quotient hrank hs
    ((PrimeSpectrum.ext h : p = ⟨⊥, Ideal.isPrime_bot⟩) ▸ hpsupp)
  have hone : 1 ≤ p.asIdeal.height :=
    Order.one_le_iff_ne_zero.mpr fun h0 => hpne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  exact Set.mem_biUnion (show p ∈ heightOneSupport A s from ⟨le_antisymm hple hone, hpsupp⟩)
    ((PrimeSpectrum.mem_zeroLocus _ _).2 hpq)

/-- For `A` a Noetherian normal domain, `M` a finite reflexive `A`-module of rank one and `s ∈ M`
nonzero, `U = Spec(A) \ (V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r))`, where `U` is the set of primes at which
`s : A_𝔭 → M_𝔭` is an isomorphism and `𝔭₁, …, 𝔭_r` are the height one primes of `A` in the support
of `M ⧸ A·s`. -/
@[stacks 0EBQ "the first display, U = Spec(A) \\ (V(p_1) ∪ … ∪ V(p_r)), unconditionally; the
colimit Γ(U, O_U) = colim M^[n] is AlgebraicGeometry.objective_0EBQ of
Divisors/Reflexive/ReflexiveColimitSections.lean"]
theorem sectionIsomorphismPrimes_eq_compl_heightOneSupportZeroLocus [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [Module.Finite A M] [Module.IsReflexive A M]
    (hrank : Module.rank A M = 1) {s : M} (hs : s ≠ 0) :
    sectionIsomorphismPrimes A s = (heightOneSupportZeroLocus A s)ᶜ := by
  rw [sectionIsomorphismPrimes_eq_compl_support hs,
    (support_subset_heightOneSupportZeroLocus hrank hs).antisymm
      (heightOneSupportZeroLocus_subset_support A s)]

end Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes

end
