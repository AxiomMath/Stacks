module

public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support

@[expose] public section

/-!
# A minimal prime over `𝔭 + (x)` is an associated prime of `M/xⁿM`

Proof of `exists_mem_associatedPrimes_quotSMulTop_pow_of_mem_minimalPrimes` (Stacks 0CN5): for a
Noetherian ring `R`, a finite `R`-module `M` and `x : R`, if `𝔭 ∈ Ass(M)` and `𝔮` is a minimal
prime over `𝔭 + (x)`, then `𝔮 ∈ Ass(M/xⁿM)` for some `n ≥ 1`.

The source's route is followed. Write `𝔭 = Ann(m)` for some `m : M`, so that the cyclic submodule
`N = R·m` is a copy of `R/𝔭` inside `M`, and let the Artin–Rees lemma supply an `n > 0` with
`xⁿM ∩ N ⊆ xN`. The image `m̄` of `m` in `M/xⁿM` then has annihilator `J` squeezed between
`𝔭 + (xⁿ)` and `𝔭 + (x)`: the lower bound because `𝔭` kills `m` while `xⁿ` kills the whole
quotient, the upper bound because `a • m ∈ xⁿM` forces `a • m ∈ xN`, that is `a ∈ 𝔭 + (x)`. Since
`R·m̄` is cyclic, hence finite, `Supp(R·m̄) = V(J)`, and the squeeze says exactly that `𝔮` is
minimal in `V(J)`: it contains `J` because `J ⊆ 𝔭 + (x) ⊆ 𝔮`, and a prime below `𝔮` containing
`J` contains `𝔭` and `xⁿ`, hence `𝔭 + (x)`, hence `𝔮`. So `𝔮 ∈ Ass(R·m̄)` by Stacks 05BV, and
`Ass` is monotone along the inclusion `R·m̄ ↪ M/xⁿM`.

## Main results

* `Stacks.AssociatedPrimes.PowerQuotient.solution`: Stacks 0CN5, `𝔮 ∈ Ass(M/xⁿM)` for some `n ≥ 1`.

## Implementation notes

The three auxiliary results are stated under the weakest hypotheses they need, and for an
arbitrary submodule or module rather than for the cyclic one at hand.

`exists_pos_smul_pow_top_inf_le_smul` is the form of the Artin–Rees lemma the source uses,
`∃ n > 0, xⁿM ∩ N ⊆ xN`, obtained from Mathlib's `Ideal.exists_pow_inf_eq_pow_smul` at the
exponent `k + 1`, where `k` is the stability index: there the intersection is
`(x)¹ • ((x)ᵏM ∩ N)`, which lies in `xN`.

`annihilator_span_singleton_mkQ_le_sup` is the upper bound `Ann(m̄) ⊆ 𝔭 + (x)`, stated for the
quotient by an arbitrary submodule `N'` satisfying `N' ∩ R·m ⊆ x·(R·m)`; only that inclusion and
`Ann(m) ⊆ 𝔭` are used, so neither `R` Noetherian nor `M` finite appears.

`mem_associatedPrimes_of_annihilator_span_singleton_squeeze` applies Stacks 05BV, and
is where the geometry happens: an element `y` of any module whose annihilator lies between
`𝔭 + (xⁿ)` and `𝔭 + (x)` produces every minimal prime over `𝔭 + (x)` as an associated prime.
Minimality in the support is transported to `Ideal R` through `Module.mem_support_iff_of_finite`
rather than through `Module.support_eq_zeroLocus`, because `Submodule.annihilator` is by
definition `Module.annihilator R ↥N`, so both halves of `Minimal` become inequalities of ideals
with no `zeroLocus` bookkeeping.

## References

* [StacksProject 0CN5](https://stacks.math.columbia.edu/tag/0CN5)

-/

namespace Stacks.AssociatedPrimes.PowerQuotient

open Submodule

open scoped Pointwise

/-- **Artin–Rees, in the form used by Stacks 0CN5.** For a finite module `M` over a Noetherian
ring, an element `x : R` and a submodule `N ⊆ M`, there is an `n > 0` with `xⁿM ∩ N ⊆ xN`. -/
private theorem exists_pos_smul_pow_top_inf_le_smul {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R)
    (N : Submodule R M) :
    ∃ n : ℕ, 0 < n ∧ (x ^ n) • (⊤ : Submodule R M) ⊓ N ≤ x • N := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {x}) (M := M) N
  refine ⟨k + 1, k.succ_pos, ?_⟩
  calc (x ^ (k + 1)) • (⊤ : Submodule R M) ⊓ N
      = (Ideal.span {x} : Ideal R) ^ (k + 1) • (⊤ : Submodule R M) ⊓ N := by
        rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    _ = Ideal.span {x} • ((Ideal.span {x} : Ideal R) ^ k • (⊤ : Submodule R M) ⊓ N) := by
        rw [hk (k + 1) k.le_succ, Nat.add_sub_cancel_left, pow_one]
    _ ≤ Ideal.span {x} • N := Submodule.smul_mono le_rfl inf_le_right
    _ = x • N := Submodule.ideal_span_singleton_smul x N

/-- If `Ann(m) ⊆ 𝔭` and `N' ∩ R·m ⊆ x·(R·m)`, then the annihilator of the image of `m` in `M/N'`
is contained in `𝔭 + (x)`: an `a` killing that image has `a • m ∈ N' ∩ R·m`, hence
`a • m = x • (c • m)`, and then `a - xc` kills `m`. -/
private theorem annihilator_span_singleton_mkQ_le_sup {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {p : Ideal R} {x : R} {m : M} {N' : Submodule R M}
    (hpm : (Submodule.span R {m}).annihilator ≤ p)
    (hN' : N' ⊓ Submodule.span R {m} ≤ x • Submodule.span R {m}) :
    (Submodule.span R {N'.mkQ m}).annihilator ≤ p + Ideal.span {x} := by
  intro a ha
  rw [Submodule.mem_annihilator_span_singleton] at ha
  have hmemN' : a • m ∈ N' := by
    rwa [← Submodule.ker_mkQ N', LinearMap.mem_ker, map_smul]
  have hmem := hN' ⟨hmemN', Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m)⟩
  obtain ⟨s, hs, hxs⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have hsub : a - x * c ∈ p :=
    hpm (Submodule.mem_annihilator_span_singleton _ _ |>.mpr
      (by rw [sub_smul, ← smul_smul, hxs, sub_self]))
  have hx : x * c ∈ Ideal.span {x} := Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c x⟩
  simpa [Ideal.add_eq_sup] using Submodule.add_mem_sup hsub hx

/-- If the annihilator of a single element `y` of an `R`-module `N` lies between `𝔭 + (xⁿ)` and
`𝔭 + (x)`, then every minimal prime `𝔮` over `𝔭 + (x)` is an associated prime of `N`.

Indeed `R·y` is finite, so its support is `V(Ann(y))`, and the two bounds say precisely that `𝔮`
is minimal in that support: Stacks 05BV then puts `𝔮` in `Ass(R·y) ⊆ Ass(N)`. -/
private theorem mem_associatedPrimes_of_annihilator_span_singleton_squeeze {R N : Type*}
    [CommRing R] [IsNoetherianRing R] [AddCommGroup N] [Module R N] {p q : Ideal R} {x : R}
    {n : ℕ} (y : N) (hq : q ∈ (p + Ideal.span {x}).minimalPrimes)
    (hp : p ≤ (Submodule.span R {y}).annihilator)
    (hxn : x ^ n ∈ (Submodule.span R {y}).annihilator)
    (hle : (Submodule.span R {y}).annihilator ≤ p + Ideal.span {x}) :
    q ∈ associatedPrimes R N := by
  have : Module.Finite R ↥(Submodule.span R {y}) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span_singleton y)
  have hmin : Minimal (· ∈ Module.support R ↥(Submodule.span R {y}))
      (⟨q, hq.isPrime⟩ : PrimeSpectrum R) := by
    refine ⟨Module.mem_support_iff_of_finite.mpr (hle.trans hq.le), fun P hP hPq => ?_⟩
    have hPJ := Module.mem_support_iff_of_finite.mp hP
    refine hq.2 ⟨P.2, ?_⟩ hPq
    rw [Ideal.add_eq_sup, sup_le_iff]
    exact ⟨hp.trans hPJ,
      (Ideal.span_singleton_le_iff_mem _).mpr (P.2.mem_of_pow_mem n (hPJ hxn))⟩
  exact associatedPrimes.subset_of_injective (f := (Submodule.span R {y}).subtype)
    (Submodule.injective_subtype _) (Module.mem_associatedPrimes_of_minimal_mem_support hmin)

/-- **Stacks 0CN5.** Let `R` be a Noetherian ring, `M` a finite `R`-module and `x : R`. If `𝔭` is
an associated prime of `M` and `𝔮` is a minimal prime over `𝔭 + (x)`, then `𝔮` is an associated
prime of `M/xⁿM` for some `n ≥ 1`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) {p q : Ideal R}
    (hp : p ∈ associatedPrimes R M) (hq : q ∈ (p + Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 0 < n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) := by
  obtain ⟨-, m, hm⟩ := isAssociatedPrime_iff.mp hp
  rw [Submodule.bot_colon'] at hm
  obtain ⟨n, hn, hAR⟩ := exists_pos_smul_pow_top_inf_le_smul x (Submodule.span R {m})
  refine ⟨n, hn, mem_associatedPrimes_of_annihilator_span_singleton_squeeze (n := n)
    (((x ^ n) • (⊤ : Submodule R M)).mkQ m) hq ?_ ?_
    (annihilator_span_singleton_mkQ_le_sup hm.ge hAR)⟩
  · intro a ha
    rw [Submodule.mem_annihilator_span_singleton, ← map_smul,
      (Submodule.mem_annihilator_span_singleton _ _).mp (hm.le ha), map_zero]
  · rw [Submodule.mem_annihilator_span_singleton, ← map_smul, ← LinearMap.mem_ker,
      Submodule.ker_mkQ]
    exact Submodule.smul_mem_pointwise_smul m (x ^ n) ⊤ Submodule.mem_top

end Stacks.AssociatedPrimes.PowerQuotient

/-!
# A minimal prime over `𝔭 + (x)` is an associated prime of `M/xⁿM`

Let `R` be a Noetherian ring, `M` a finite `R`-module, `x ∈ R`, let `𝔭` be an associated prime
of `M` and let `𝔮` be a minimal prime over `𝔭 + (x)`. Then

`𝔮 ∈ Ass(M/xⁿM)` for some `n ≥ 1`.

The source's route. Choose a submodule `N ⊆ M` with `N ≅ R/𝔭`, which is what `𝔭 ∈ Ass(M)`
provides. By the Artin–Rees lemma there is an `n > 0` with `N ∩ xⁿM ⊆ xN`. Let `N̄ ⊆ M/xⁿM` be
the image of `N`. Since `Ass` of a submodule is contained in `Ass` of the ambient module it
suffices to see `𝔮 ∈ Ass(N̄)`. The choice of `n` gives a surjection
`N̄ → N/xN = R/(𝔭 + (x))`, whence `𝔮 ∈ Supp(N̄)`; and `N̄` is annihilated by both `𝔭` and `xⁿ`,
so every prime of `Supp(N̄)` contains `𝔭 + (x)` and therefore `𝔮` is minimal in `Supp(N̄)`. A
minimal prime of the support of a finite module is an associated prime, so `𝔮 ∈ Ass(N̄)`.

## Main results

* `exists_mem_associatedPrimes_quotSMulTop_pow_of_mem_minimalPrimes`: the statement above.

## Implementation notes

The source states the case of a Noetherian *local* ring `(R, 𝔪)` with `x ∈ 𝔪`; both
restrictions are dropped, which weakens nothing. Locality is used nowhere in the source's proof
— Artin–Rees, `Ass` of a submodule, and "a minimal prime of the support is associated" all hold
over any Noetherian ring — and `x ∈ 𝔪` carries no information that `𝔮 ∈ minimalPrimes (𝔭 + (x))`
does not already carry: if `x` is a unit then `𝔭 + (x) = ⊤` and `⊤` has no minimal primes, since
a prime containing `⊤` would equal `⊤`, so the hypothesis is vacuous exactly where `x ∉ 𝔪`
allows it to be.

`Ass` is Mathlib's `associatedPrimes R`, `M/xⁿM` is `QuotSMulTop (x ^ n) M`, i.e.
`M ⧸ xⁿ • (⊤ : Submodule R M)`, and "minimal over `𝔭 + (x)`" is
`𝔮 ∈ (𝔭 + Ideal.span {x}).minimalPrimes`, which already supplies `𝔮.IsPrime` and
`𝔭 + (x) ≤ 𝔮`; the additive spelling of the ideal is the source's.

Faithfulness. (1) No hypothesis is dead. `Module.Finite R M` fails without: over `R = ℤ` with
`M = ℤ[1/2]`, `𝔭 = (0) ∈ Ass(M)`, `x = 2` and `𝔮 = (2)` minimal over `(0) + (2)`, one has
`2ⁿM = M` for all `n`, so `M/2ⁿM = 0` and `Ass(M/2ⁿM) = ∅`. `IsNoetherianRing R` is consumed
twice, by Artin–Rees and by "a minimal prime of the support is an associated prime"; without it
even `Ass(M) ≠ ∅` for `M ≠ 0` fails. `𝔭 ∈ Ass(M)` fails without: over `R = M = ℤ` take
`𝔭 = (3) ∉ Ass(ℤ) = {(0)}` and `x = 0`, so that `𝔮 = (3)` is minimal over `(3) + (0)` while
`Ass(ℤ/0ⁿℤ) = Ass(ℤ) = {(0)}`. Minimality of `𝔮`, rather than `𝔭 + (x) ≤ 𝔮` with `𝔮` prime,
fails without: over `R = M = k[u, v]` take `𝔭 = (0)`, `x = u` and `𝔮 = (u, v)`, and
`Ass(R/uⁿR) = {(u)}`. (2) The scalars and base are the source's: `M` and every `M/xⁿM` are
`R`-modules, `x` and both primes live in `R`, and `Ass` is taken over `R` throughout; no
localization at `𝔮` or completion intervenes, even though the source's `R` is local.
(3) The source names no canonical map; what it names is the module `M/xⁿM`, and the conclusion
pins it as `QuotSMulTop (x ^ n) M` for the `n` produced, and pins the associated prime to be
`𝔮` on the nose rather than asserting that some prime over `𝔭 + (x)` is associated.
(4) The instantiation is not degenerate: `R = M = ℤ`, `𝔭 = (0) ∈ Ass(ℤ)`, `x = 2`, `𝔮 = (2)`,
which is minimal over `(0) + (2) = (2)`, and `n = 1` works since `Ass(ℤ/2ℤ) = {(2)}`. The
requirement `0 < n` is not decoration: `x ^ 0 = 1` makes `M/x⁰M = 0`, whose set of associated
primes is empty, so the conclusion is false for `n = 0` in every instance.

## References

* [StacksProject 0CN5](https://stacks.math.columbia.edu/tag/0CN5)

## Tags

associated prime, minimal prime, Artin-Rees, Noetherian ring
-/

@[expose] public section

/-- **A minimal prime over `𝔭 + (x)` is an associated prime of `M/xⁿM`.** Let `R` be a
Noetherian ring, `M` a finite `R`-module and `x ∈ R`. If `𝔭` is an associated prime of `M` and
`𝔮` is a minimal prime over `𝔭 + (x)`, then `𝔮` is an associated prime of `M/xⁿM` for some
`n ≥ 1`.

The source states this for `x` in the maximal ideal of a Noetherian local ring; neither
restriction is used, and `x ∉ 𝔪` makes `𝔭 + (x) = ⊤`, which has no minimal primes. -/
@[stacks 0CN5 "Stated over an arbitrary Noetherian ring for an arbitrary `x`: the source's \
  locality is unused, and `x ∈ 𝔪` is implied to the extent it matters by `𝔮` being a minimal \
  prime over `𝔭 + (x)`."]
public theorem exists_mem_associatedPrimes_quotSMulTop_pow_of_mem_minimalPrimes {R : Type*}
    [CommRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R) {p q : Ideal R} (hp : p ∈ associatedPrimes R M)
    (hq : q ∈ (p + Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 0 < n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) :=
  Stacks.AssociatedPrimes.PowerQuotient.solution x hp hq

end
