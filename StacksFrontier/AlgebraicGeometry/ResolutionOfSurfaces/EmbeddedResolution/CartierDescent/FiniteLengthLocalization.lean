module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# A power of `t` kills a vector that dies in every localization away from `t`

Let `B` be a commutative ring, `N` a `B`-module, `t : B` and `v : N`. Suppose `v` dies in the
localization `N_𝔭` for every prime `𝔭` of `B` avoiding `t`. Then `t ^ k • v = 0` for some `k`.

This is the "compatibility on the overlap of two charts" step of [Stacks, Tag 0AGT]: two sections
of a residual quotient agreeing at every point of the support that lies in the overlap of the two
charts differ by a vector dying in every localization at a prime of the overlap, hence by a vector
a power of the overlap parameter kills; so the two sections agree over the overlap.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_pow_smul_eq_zero_of_localizedModule_eq_zero` —
  the annihilation criterion: if `v` dies in `N_𝔭` for every prime `𝔭` with `t ∉ 𝔭`, then
  `t ^ k • v = 0` for some `k`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_pow_smul_mem_of_forall_localization` — the
  form consumers use: for `b : B` and an ideal `K` of `B`, if `b` lies in `K · B_𝔭` for every
  prime `𝔭` containing `K` and avoiding `t`, then `t ^ k * b ∈ K` for some `k`.

## Implementation notes

**No finiteness hypothesis is needed, and none is imposed** — in particular neither
`IsArtinian B N` on the module nor `IsArtinianRing (B ⧸ K)` on the quotient, which is how the
consumer in [Stacks, Tag 0AGT] meets these statements. The reason is that the hypothesis is
equivalent to a statement about one ideal. Vanishing of `v` in `N_𝔭` says exactly that some scalar
outside `𝔭` annihilates `v` (`IsLocalizedModule.eq_zero_iff`), i.e. that the annihilator `I` of `v`
is *not* contained in `𝔭`. So the hypothesis reads: every prime containing `I` contains `t`. That
is `t ∈ I.radical` (`Ideal.radical_eq_sInf`), i.e. `t ^ k • v = 0` for some `k`
(`Ideal.mem_radical_iff`) — the Zariski-topology statement that the support of a vector is closed
and the complement of `V(t)` misses it.

The route through finiteness — decompose the Artinian `N` as the product of its localizations at
the finitely many primes of its support, and observe that `t` is nilpotent on each factor whose
prime contains `t` — proves the same thing with more hypotheses, so it is not taken. The statements
below therefore apply verbatim where an Artinian hypothesis is available, and also where it is not;
a consumer that has `[IsArtinian B N]` in scope simply does not pass it.

In item two the hypothesis is only required at the primes *containing* `K`, which is what the
consumer can check: at a prime `𝔭` not containing `K` an element of `K ∖ 𝔭` already annihilates all
of `B ⧸ K`, so the localization of `B ⧸ K` there vanishes for free.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public section

universe u v

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {B : Type u} [CommRing B]

/-- Multiplication by `s` kills the class of `b` in `B ⧸ K` exactly when `s * b ∈ K`. -/
private theorem smul_quotient_mk_eq_zero_iff (K : Ideal B) (s b : B) :
    s • (Ideal.Quotient.mk K b) = 0 ↔ s * b ∈ K := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]

/-- **A vector dying in every localization away from `t` is killed by a power of `t`.** If the
image of `v : N` in `N_𝔭` vanishes for every prime `𝔭` of `B` with `t ∉ 𝔭`, then `t ^ k • v = 0`
for some `k`.

Vanishing in `N_𝔭` says that some scalar outside `𝔭` annihilates `v`, so the hypothesis says that
no prime avoiding `t` contains the annihilator `I` of `v`; equivalently every prime containing `I`
contains `t`, which is `t ∈ I.radical`. No finiteness of `N` is involved: this is the statement
that the support of `v` is a closed subset of `Spec B` disjoint from the basic open of `t`. -/
theorem exists_pow_smul_eq_zero_of_localizedModule_eq_zero (N : Type v) [AddCommGroup N]
    [Module B N] (t : B) (v : N)
    (h : ∀ p : PrimeSpectrum B, t ∉ p.asIdeal →
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) v = 0) :
    ∃ k : ℕ, t ^ k • v = 0 := by
  have ht : t ∈ (B ∙ v).annihilator.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun {J} hJ => ?_
    obtain ⟨hJle, hJp⟩ := hJ
    by_contra htJ
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff
      (⟨J, hJp⟩ : PrimeSpectrum B).asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ N)).mp (h ⟨J, hJp⟩ htJ)
    exact Ideal.mem_primeCompl_iff.mp s.2
      (hJle ((Submodule.mem_annihilator_span_singleton v _).mpr hs))
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp ht
  exact ⟨k, (Submodule.mem_annihilator_span_singleton v _).mp hk⟩

/-- **The form consumers use.** Let `K` be an ideal of `B` and `t b : B`. If the image of `b` in
`B_𝔭` lies in the extension `K · B_𝔭` for every prime `𝔭` of `B` containing `K` and avoiding `t`,
then `t ^ k * b ∈ K` for some `k`.

This is the previous statement for `N := B ⧸ K` and `v :=` the class of `b`. Membership of `b` in
`K · B_𝔭` is exactly vanishing of that class in `(B ⧸ K)_𝔭`
(`IsLocalization.algebraMap_mem_map_algebraMap_iff`), and at a prime not containing `K` the
localization of `B ⧸ K` vanishes because an element of `K ∖ 𝔭` annihilates it — so nothing need be
checked there. -/
theorem exists_pow_smul_mem_of_forall_localization (K : Ideal B) (t b : B)
    (h : ∀ p : PrimeSpectrum B, K ≤ p.asIdeal → t ∉ p.asIdeal →
      (algebraMap B (Localization.AtPrime p.asIdeal)) b ∈
        Ideal.map (algebraMap B (Localization.AtPrime p.asIdeal)) K) :
    ∃ k : ℕ, t ^ k * b ∈ K := by
  have key : ∀ p : PrimeSpectrum B, t ∉ p.asIdeal →
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (B ⧸ K))
        (Ideal.Quotient.mk K b) = 0 := by
    intro p htp
    rw [IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl]
    by_cases hKp : K ≤ p.asIdeal
    · obtain ⟨m, hm, hmb⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) K b).mp (h p hKp htp)
      exact ⟨⟨m, hm⟩, (smul_quotient_mk_eq_zero_iff K m b).mpr hmb⟩
    · obtain ⟨s, hsK, hsp⟩ := SetLike.not_le_iff_exists.mp hKp
      exact ⟨⟨s, Ideal.mem_primeCompl_iff.mpr hsp⟩,
        (smul_quotient_mk_eq_zero_iff K s b).mpr (K.mul_mem_right b hsK)⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_localizedModule_eq_zero (B ⧸ K) t
    (Ideal.Quotient.mk K b) key
  exact ⟨k, (smul_quotient_mk_eq_zero_iff K _ b).mp hk⟩

end Stacks.ResolutionOfSurfaces.CartierDescent

end
