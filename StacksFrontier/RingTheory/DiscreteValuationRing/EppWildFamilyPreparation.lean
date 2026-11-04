module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier

/-!
# Uniform wild preparation of a family of degree-`p` layers over one orbit extension

The equal-characteristic degree-`p` endgame of Epp's theorem solves *one* Artin--Schreier
presentation over a totally ramified orbit extension.  The all-factor route to Tag 09F9 needs it
run at **every** conjugate factor of a reduced base change at once, over one extension fixed
before any factor is examined.  The obstruction to doing otherwise is not that the factors are
exotic — they may well be isomorphic as fields, and nothing below assumes they are not — but that
there is no *canonical algebra-compatible transport* between their packages: the factors are
distinct quotients of one reduced tensor product, carrying no base-algebra map from one to another
along which a weak solution could be pushed, so a solution obtained at one factor says nothing
about the next.  And a solution cannot be repaired after the fact either: the per-factor endgames
adjoin roots of a uniformizer and are therefore totally ramified rather than étale, so a common
overfield of individually chosen extensions is not reachable from any one of them by the étale
square along which weak solutions do ascend
(`IsWeakSolution.of_finiteEtale_square`).

This file supplies the two halves of that quantifier exchange which are about *preparation*:

* `exists_prepared_wild_laurent_of_charP` **produces**, from a single degree-`p` layer and a
  supplied uniformizer of the base, a collision-free Laurent presentation together with the
  intrinsic wild/tame split of its coefficients and a terminal Frobenius depth at each wild
  position — with **no residue hypothesis whatsoever**;
* `exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_wild_laurent` **consumes** a
  finite family of such packages, over rings `B i` and fields `L i` that vary with the member, and
  returns one orbit extension of `K` with a weak solution at every member over it.

## Why the split is against the perfect core, and never against the full range

The wild set of a member is `J i`, the set of coefficient positions whose coefficient lies
**outside** `perfectCore (κ_{B i}) p`.  It is *not* the full range `Finset.range (n i)`, and the
difference is not cosmetic.

The separation hypothesis that makes the scaled-pole maximum unique — no scaled pole of one wild
position equals the plain pole gap of another — is supplied by
`exists_artinSchreier_laurent_presentation_without_related_poles`, which delivers it **only at the
positions where the classifying predicate fails**, because that is the only place its
collision-removal step can act: removing a collision replaces one coefficient by `0`, which is in
the perfect core, and so decreases the wild count.  Demanded at every position of
`Finset.range (n i)` the same hypothesis is a constraint on the pole order alone: taking `r = 1`
and the position `k = n i - 1` it forces `p > n i`.  So a full-range formulation is satisfiable
only for pole orders below the residue characteristic, and it additionally asks for a terminal —
non-`p`-th-power — root at every position, which fails at once at any position whose coefficient
is `0`, since the only `p ^ m`-th root of `0` is `0 = 0 ^ p`.  Nothing with a zero Laurent
coefficient satisfies it.

What replaces the full-range demand is the following, and it is the reason a single rank serves
the whole range:

* at a position in `J i` the root is the terminal one and its depth is that position's own
  Frobenius depth, both returned by `exists_pow_eq_and_not_pow_of_notMem_perfectCore` with no
  hypothesis at all;
* at a position outside `J i` the coefficient is in the perfect core, hence a `p ^ m`-th power for
  **every** `m`, so its root may be taken at the one shared rank `R`.  Its scaled pole is then
  `(n i - k) * p ^ (R - R) = n i - k ≤ n i`;
* and `exists_shared_orbit_parameters` returns, at every wild position, a scaled pole *strictly
  greater than* `n i`.

So the maximum over `J i` dominates every tame position automatically, and is therefore the
maximum over the full range — which is what the terminal theorem asks for.  That is
`scaledPole_package_of_uniform_depth`, and it is the one-member bookkeeping of
`exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport_of_uniformizer` lifted
off its own extension so that a family can share one.

## What is and is not assumed

Nothing here assumes completeness, an algebraically closed residue field, a perfect base residue
field, separable closedness, or Epp's condition.  The classification is intrinsic to each member's
own residue field, which is exactly what lets the wild data be *produced* rather than demanded:
membership in `perfectCore (κ_{B i}) p` is a property of `κ_{B i}` alone, so the split, the
terminal depths, and hence the shared rank are all determined before any base residue field is
interrogated.

No member is distinguished.  Every quantifier runs over all members, each member's weak solution
is derived from its own data, and no member's solution is transported to another.

## What remains

Two things, both recorded precisely at the relevant declaration:

1. `J i` must be **nonempty** — some coefficient outside the perfect core.  When `J i = ∅` every
   coefficient of the minimal presentation is in the perfect core and the endgame is a different
   one: the constant-numerator branch, which produces an Artin--Schreier extension of `K` itself
   and needs the *base* residue field, i.e. Epp's condition.  That branch is not treated here.
2. The layer must be genuinely ramified, which `exists_prepared_wild_laurent_of_charP` takes as
   the hypothesis that no Artin--Schreier parameter of the layer is integral over `B`.  The
   complementary case is `IsWeaklyUnramified B C` — Tag 09F0 clause (A) — whose proof uses
   declarations private to
   `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier` and so is not restated here.

  Neither theorem below is tagged: there is still no
unconditional Tag 09F9.

## References

* [The Stacks Project, Tag 09F1](https://stacks.math.columbia.edu/tag/09F1)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

universe uA uB uC uK uL uM

namespace IsDiscreteValuationRing

/-- A function agreeing with `f` on a finset `J` and with `g` off it. -/
private theorem exists_eq_on_of_mem_and_notMem {α : Sort*} (J : Finset ℕ) (f g : ℕ → α) :
    ∃ h : ℕ → α, (∀ k ∈ J, h k = f k) ∧ ∀ k, k ∉ J → h k = g k := by
  classical
  exact ⟨fun k => if k ∈ J then f k else g k, fun k hk => ite_eq_left hk,
    fun k hk => ite_eq_right hk⟩

/-- **The wild maximum is the maximum: scaled poles under the uniform depth function.**

`d` is the depth function that agrees with each wild position's own terminal depth on `J` and is
the shared rank `R` everywhere else.  Given the unique-maximum package that
`exists_shared_orbit_parameters` returns over `J` — in particular `hpolegt`, which puts every wild
scaled pole strictly above `n` — the four clauses the terminal degree-`p` theorem consumes hold
over the **full** range `Finset.range n`.

The tame positions are handled by the exponent collapsing: `R - d k = 0` there, so the scaled pole
is the plain gap `n - k ≤ n`, which `hpolegt` at `j` dominates.  This is the only place the shared
rank is used as a *value* rather than as a bound, and it is why the rank has to be one number for
the whole family rather than chosen per member.  It is computed *from* the members' coefficient
data, as a bound over all of them; what it may not be is a different number for each. -/
private theorem scaledPole_package_of_uniform_depth
    (p n R : ℕ) (J : Finset ℕ) (depth d : ℕ → ℕ) (j : ℕ) (hj : j ∈ J)
    (hdJ : ∀ k ∈ J, d k = depth k) (hdoff : ∀ k, k ∉ J → d k = R)
    (hdepthlt : ∀ k ∈ J, depth k + 1 < R)
    (hpolegt : ∀ k ∈ J, n < (n - k) * p ^ (R - depth k))
    (hpolemax : ∀ k ∈ J, k ≠ j → (n - k) * p ^ (R - depth k) < (n - j) * p ^ (R - depth j))
    (hpoledvd : p ∣ (n - j) * p ^ (R - depth j)) :
    (∀ k ∈ Finset.range n, d k ≤ R) ∧
      0 < (n - j) * p ^ (R - d j) ∧
      p ∣ (n - j) * p ^ (R - d j) ∧
      ∀ k ∈ Finset.range n, k ≠ j →
        (n - k) * p ^ (R - d k) < (n - j) * p ^ (R - d j) := by
  have hdj : d j = depth j := hdJ j hj
  refine ⟨fun k _ => ?_, ?_, ?_, fun k hk hne => ?_⟩
  · by_cases hkJ : k ∈ J
    · have := hdepthlt k hkJ
      rw [hdJ k hkJ]
      omega
    · exact (hdoff k hkJ).le
  · rw [hdj]
    exact (Nat.zero_le n).trans_lt (hpolegt j hj)
  · rw [hdj]
    exact hpoledvd
  · rw [hdj]
    by_cases hkJ : k ∈ J
    · rw [hdJ k hkJ]
      exact hpolemax k hkJ hne
    · rw [hdoff k hkJ, Nat.sub_self, pow_zero, mul_one]
      exact (Nat.sub_le n k).trans_lt (hpolegt j hj)

/-- **Wild preparation of a single degree-`p` layer, with no residue hypothesis.**

For a weakly unramified extension `A ⊆ B` of discrete valuation rings in equal characteristic `p`
and a degree-`p` Galois extension `M / L` of the fraction field of `B`, this produces, over a
*supplied* uniformizer `π` of `A`:

* an Artin--Schreier presentation `z ^ p - z = ξ` of `M / L` of minimal pole order `n > 0`, whose
  Laurent expansion in `π` has **no two wild pole indices related by a power of `p`**;
* the residue lifting datum `lift`, `liftMod` that the expansion is written in;
* the wild set `J`, the positions whose coefficient lies outside `perfectCore (κ_B) p`, each
  carrying a terminal root `wildRoot k` of depth `depth k` — a root that is not itself a `p`-th
  power;
* and, off `J`, the statement that the coefficient is a `p ^ m`-th power for **every** `m`.

Everything returned is intrinsic to `B` and `L`.  The base residue field `κ_A` is never
interrogated: the classification is by membership in `perfectCore (κ_B) p`, whose finiteness of
depth costs nothing (`exists_pow_eq_and_not_pow_of_notMem_perfectCore`), and the perfect-core
positions are described by the elementary root property rather than by a base element.  That is
what makes this a *producer*: under Epp's condition a deep root of a perfect-core coefficient is
separable algebraic over `κ_A` but need not lie in the image of `κ_A`, so any formulation that
asked for the roots downstairs would have to be assumed rather than proved.

The lifting datum is returned in full — `lift` together with `liftMod` and both of their defining
equations — and not only as the set-theoretic section `lift`.  The truncated ring homomorphism is
what turns an equality of residues into a congruence modulo `π ^ n`, so
`exists_isWeakSolution_of_prepared_mixed_laurent_orbitExtension` takes it as an input; a package
carrying only `lift` cannot be fed to it.

**The hypothesis `hram`** says the layer admits no integral Artin--Schreier parameter, which is
exactly what makes the minimal pole order positive.  In the complementary case the layer's own
valuation ring is weakly unramified over `B` (Tag 09F0 clause (A)) and no extension is needed at
all; that implication rests on declarations private to `ArtinSchreier.lean` and is therefore not
restated here.  Note that the valuation ring of `M` does not appear in this statement at all: the
preparation is a statement about `B`, `L` and `M` only.

**What this does not settle.**  Nothing here says `J` is nonempty.  If it is empty, every
coefficient is in the perfect core and the endgame is the constant-numerator branch, which produces
an Artin--Schreier extension of `K` itself and genuinely needs `κ_A` — that is where Epp's
condition enters, and it is not treated in this file. -/
theorem exists_prepared_wild_laurent_of_charP
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B L] [Algebra K L] [Algebra L M]
    [IsExtension A B] [IsFractionRing B L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hweak : IsWeaklyUnramified A B)
    (π : A) (hπ : Irreducible π)
    (hram : ∀ (η : L) (w : M), w ^ p - w = algebraMap L M η →
      Algebra.adjoin L {w} = ⊤ → η ∉ (algebraMap B L).range) :
    ∃ (n : ℕ) (ξ : L) (z : M) (lift : IsLocalRing.ResidueField B → B)
      (liftMod : IsLocalRing.ResidueField B →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ n)
      (coeff : ℕ → IsLocalRing.ResidueField B) (b : B) (J : Finset ℕ) (depth : ℕ → ℕ)
      (wildRoot : ℕ → IsLocalRing.ResidueField B),
      0 < n ∧ z ^ p - z = algebraMap L M ξ ∧ Algebra.adjoin L {z} = ⊤ ∧
        (∀ x, IsLocalRing.residue B (lift x) = x) ∧
        (∀ x, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (lift x) = liftMod x) ∧
        ξ = (∑ i ∈ Finset.range n, algebraMap B L (lift (coeff i)) *
            (algebraMap B L (algebraMap A B π))⁻¹ ^ (n - i)) + algebraMap B L b ∧
        (∀ (m : ℕ) (η : L) (w : M),
          w ^ p - w = algebraMap L M η → Algebra.adjoin L {w} = ⊤ →
          algebraMap B L (algebraMap A B π) ^ m * η ∈ (algebraMap B L).range → n ≤ m) ∧
        (∀ k ∈ J, k < n) ∧
        (∀ k ∈ J, wildRoot k ^ (p ^ depth k) = coeff k) ∧
        (∀ k ∈ J, ¬∃ y : IsLocalRing.ResidueField B, wildRoot k = y ^ p) ∧
        (∀ k ∈ Finset.range n, k ∉ J →
          ∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ m) = coeff k) ∧
        ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → ∀ r : ℕ, n - k' ≠ (n - k) * p ^ r := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hπB : Irreducible (algebraMap A B π) :=
    irreducible_algebraMap_of_isWeaklyUnramified hweak hπ
  obtain ⟨n, ξ, z, hz, hgen, hn, hmin⟩ :=
    exists_artinSchreier_presentation_minimal_poleOrder B L M p hπB
      (exists_artinSchreier_presentation_of_charP K L M p hp hdegree)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by simpa only [h, pow_zero, one_mul] using hn) (hram ξ z hz hgen)
    · exact h
  have : CharP B p := (algebraMap B L).charP (IsFractionRing.injective B L) p
  have : CharP (IsLocalRing.ResidueField B) p :=
    (CharP.charP_iff_prime_eq_zero (R := IsLocalRing.ResidueField B) hp).mpr
      (by rw [← map_natCast (IsLocalRing.residue B), CharP.cast_eq_zero B p, map_zero])
  obtain ⟨σ, hσ, s, hs⟩ := exists_residueField_lift_mod_pow (B := B) p n hnpos
  have htB : algebraMap B L (algebraMap A B π) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B L).ne hπB.ne_zero
  obtain ⟨coeff, b, hexp⟩ := exists_laurent_expansion hπB σ hσ n ξ hn
  have hP : (0 : IsLocalRing.ResidueField B) ∈ perfectCore (IsLocalRing.ResidueField B) p :=
    mem_perfectCore_iff.mpr fun m => ⟨0, zero_pow (pow_pos hp.pos m).ne'⟩
  have hI : (IsLocalRing.maximalIdeal B) ^ n ≤ Ideal.span {algebraMap A B π ^ n} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπB, Ideal.span_singleton_pow]
  obtain ⟨ξ', z', coeff', b', hz', hgen', hexp', hsep⟩ :=
    exists_artinSchreier_laurent_presentation_without_related_poles p (algebraMap A B π) htB n
      ((IsLocalRing.maximalIdeal B) ^ n) hI σ s hs
      (fun x => x ∈ perfectCore (IsLocalRing.ResidueField B) p) hP ξ z coeff b hz hgen hexp
  obtain ⟨J, hJmem⟩ : ∃ J : Finset ℕ, ∀ k, k ∈ J ↔
      (k ∈ Finset.range n ∧ coeff' k ∉ perfectCore (IsLocalRing.ResidueField B) p) :=
    ⟨(Finset.range n).filter fun i =>
      coeff' i ∉ perfectCore (IsLocalRing.ResidueField B) p, fun k => Finset.mem_filter⟩
  choose! depth wildRoot hwild using fun k (hk : k ∈ J) =>
    exists_pow_eq_and_not_pow_of_notMem_perfectCore p ((hJmem k).mp hk).2
  refine ⟨n, ξ', z', σ, s, coeff', b', J, depth, wildRoot, hnpos, hz', hgen', hσ, hs, hexp', hmin,
    fun k hk => Finset.mem_range.mp ((hJmem k).mp hk).1,
    fun k hk => (hwild k hk).1, fun k hk ⟨y, hy⟩ => (hwild k hk).2 ⟨y, hy.symm⟩,
    fun k hk hkJ m => ?_, fun k hk k' hk' hne r => ?_⟩
  · have hPk : coeff' k ∈ perfectCore (IsLocalRing.ResidueField B) p := by
      by_contra hc
      exact hkJ ((hJmem k).mpr ⟨hk, hc⟩)
    exact mem_perfectCore_iff.mp hPk m
  · exact hsep k ((hJmem k).mp hk).1 ((hJmem k).mp hk).2 k' ((hJmem k').mp hk').1
      ((hJmem k').mp hk').2 hne r

/-- **A prepared wild family is solved over one orbit extension, quantified outside the family.**

Each member `i` of a finite family carries its own discrete valuation ring `B i`, weakly unramified
over the common base `A`, its own fraction field `L i`, and its own degree-`p` Artin--Schreier
layer `M i / L i` with a Laurent presentation of pole order `n i` in the **common** uniformizer
`pi` of `A`.  The coefficients are split by the member's own wild set `J i`, on which terminal
roots of prescribed depths are supplied, and off which the coefficients are `p ^ m`-th powers for
every `m`.  The conclusion is a single finite Galois extension `E / K`, totally ramified with
respect to `A` and of degree exactly `p ^ rank`, together with a weak solution at **every** member
over that same `E`.

The quantifier order is the whole content.  `E` is built once, from a depth clearing every
member's pole order and a rank at which every member's unique-maximum package holds, both selected
from the family as a whole by `exists_shared_orbit_parameters`; the rank cannot be left to a
member, since `Module.finrank K E = p ^ rank` pins the degree exactly and one extension cannot
realise two ranks.  The terminal theorem
`exists_isWeakSolution_of_prepared_mixed_laurent_orbitExtension` is then re-run at each member
against that prescribed `E`.  Each member keeps its own pole order, its own depths, its own
maximising position and its own rings; only the extension is shared.

**Where the shared rank is spent.**  At a wild position the root and the depth are the member's
own.  At every other position the coefficient is in the perfect core, so a root exists at the
shared rank itself, and the scaled pole collapses to the plain gap `n i - k ≤ n i`, which
`exists_shared_orbit_parameters` puts strictly below the wild maximum.  Hence the maximum over
`J i` is the maximum over the full range, which is `scaledPole_package_of_uniform_depth`.  This is
why the split must be against the perfect core: over the full range the separation hypothesis
would force `p > n i` and the terminality demand would fail at every zero coefficient.

**The rings vary with the member and must be allowed to.**  In the application to Tag 09F9 the
member is a conjugate factor of a reduced tensor product and `B i` is the intermediate weakly
unramified layer inside that factor, which differs from factor to factor; a formulation with a
single `B` cannot be applied there.

This is a re-derivation at every member, not a transport.  No member's weak solution is used to
obtain another's, no member is distinguished, and nothing is enlarged after the fact: `E` does not
depend on which member is asking.  No completeness and no algebraically closed, perfect, or
separably closed residue field is assumed anywhere, and Epp's condition is not used.

What a caller still owes is nonemptiness of each `J i` — some coefficient outside the perfect
core.  `exists_prepared_wild_laurent_of_charP` produces every other hypothesis unconditionally. -/
theorem exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_wild_laurent
    (A : Type uA) (K : Type uK) {ι : Type*} [Finite ι]
    (B : ι → Type uB) (C : ι → Type uC) (L : ι → Type uL) (M : ι → Type uM)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    (pi : A) (hpi : Irreducible pi)
    (xi : ∀ i, L i) (z : ∀ i, M i)
    (hz : ∀ i, z i ^ p - z i = algebraMap (L i) (M i) (xi i))
    (hgen : ∀ i, Algebra.adjoin (L i) {z i} = ⊤)
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (lift : ∀ i, IsLocalRing.ResidueField (B i) → B i)
    (hlift : ∀ i, ∀ x, IsLocalRing.residue (B i) (lift i x) = x)
    (liftMod : ∀ i, IsLocalRing.ResidueField (B i) →+*
      B i ⧸ (IsLocalRing.maximalIdeal (B i)) ^ (n i))
    (hliftMod : ∀ i, ∀ x,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (B i)) ^ (n i)) (lift i x) = liftMod i x)
    (coeff : ∀ i, ℕ → IsLocalRing.ResidueField (B i)) (b : ∀ i, B i)
    (hexp : ∀ i, xi i = (∑ k ∈ Finset.range (n i),
        algebraMap (B i) (L i) (lift i (coeff i k)) *
          (algebraMap (B i) (L i) (algebraMap A (B i) pi))⁻¹ ^ (n i - k)) +
      algebraMap (B i) (L i) (b i))
    (J : ι → Finset ℕ) (hJ : ∀ i, (J i).Nonempty) (hJn : ∀ i, ∀ k ∈ J i, k < n i)
    (depth : ι → ℕ → ℕ) (wildRoot : ∀ i, ℕ → IsLocalRing.ResidueField (B i))
    (hwildPow : ∀ i, ∀ k ∈ J i, wildRoot i k ^ (p ^ depth i k) = coeff i k)
    (hwildTerminal : ∀ i, ∀ k ∈ J i,
      ¬∃ y : IsLocalRing.ResidueField (B i), wildRoot i k = y ^ p)
    (htame : ∀ i, ∀ k ∈ Finset.range (n i), k ∉ J i →
      ∀ m : ℕ, ∃ y : IsLocalRing.ResidueField (B i), y ^ (p ^ m) = coeff i k)
    (hsep : ∀ i, ∀ k ∈ J i, ∀ k' ∈ J i, k ≠ k' →
      ∀ r : ℕ, n i - k' ≠ (n i - k) * p ^ r) :
    ∃ (E : Type uK) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Module.Finite K E) (_ : IsGalois K E),
      IsTotallyRamifiedWithRespectTo A K E ∧ ∃ rank : ℕ,
        Module.finrank K E = p ^ rank ∧
          ∀ i, ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
            max uM uK, uK, max uM uK} A (C i) K (M i) E, D.IsWeakSolution := by
  classical
  obtain ⟨N, R, hN1, hNn, hpkg⟩ :=
    exists_shared_orbit_parameters p hp n J hJ hJn depth hsep
  obtain ⟨E, hEfield, hEalgK, hEalgA, hEtower, hEfin, hEgal, htot, hdeg,
    V, hVfin, alpha, hcard, halpha, hV, hprod⟩ :=
    exists_isGalois_totallyRamified_orbitExtension_forall_depth A K p hp pi hpi N R hN1
  let := hEfield
  let := hEalgK
  let := hEalgA
  let := hEtower
  let := hEfin
  let := hEgal
  let := hVfin
  refine ⟨E, hEfield, hEalgK, hEalgA, hEtower, hEfin, hEgal, htot, R, hdeg, fun i => ?_⟩
  obtain ⟨j, hjJ, hdepthlt, hpolegt, hpolemax, hpoledvd⟩ := hpkg i
  -- The root at a tame position is taken at the shared rank, inside the member's own residue
  -- field: a perfect-core coefficient has `p ^ m`-th roots for every `m`, in particular for `R`.
  choose! tameRoot htameRoot using fun k (hk : k ∈ Finset.range (n i) ∧ k ∉ J i) =>
    htame i k hk.1 hk.2 R
  obtain ⟨d, hdJ, hdoff⟩ := exists_eq_on_of_mem_and_notMem (J i) (depth i) fun _ => R
  obtain ⟨root, hrootJ, hrootoff⟩ := exists_eq_on_of_mem_and_notMem (J i) (wildRoot i) tameRoot
  have hpow : ∀ k ∈ Finset.range (n i), root k ^ (p ^ d k) = coeff i k := by
    intro k hk
    by_cases hkJ : k ∈ J i
    · rw [hrootJ k hkJ, hdJ k hkJ]
      exact hwildPow i k hkJ
    · rw [hrootoff k hkJ, hdoff k hkJ]
      exact htameRoot k ⟨hk, hkJ⟩
  obtain ⟨hdle, hpolePos, hpoleDvd, hpoleMax⟩ :=
    scaledPole_package_of_uniform_depth p (n i) R (J i) (depth i) d j hjJ hdJ hdoff
      hdepthlt hpolegt hpolemax hpoledvd
  refine exists_isWeakSolution_of_prepared_mixed_laurent_orbitExtension
    A (B i) (C i) K (L i) (M i) E p hp (hweak i) (xi i) (z i) (hz i) (hgen i) pi hpi
    (n i) (hn i) (lift i) (hlift i) (liftMod i) (hliftMod i) (coeff i) root (b i) (hexp i)
    R d hdle hpow j (Finset.mem_range.mpr (hJn i j hjJ)) ?_ hpolePos hpoleDvd hpoleMax
    htot hdeg V alpha hcard halpha (hV (n i + 1) (hNn i)) hprod
  rw [hrootJ j hjJ]
  exact hwildTerminal i j hjJ

/-- **Equal-characteristic degree-`p`, reduced to the constant-numerator branch.**

For one Galois degree-`p` layer, either a finite weak solution already exists, or there is a
positive minimal Laurent presentation all of whose coefficients lie in the perfect core of the
intermediate residue field.  The hypothesis excludes an integral Artin--Schreier parameter, so
the first alternative is the nonempty-wild-support branch; the second is exactly the finite
constant-numerator datum that residue absorption must solve. -/
theorem exists_finite_extension_isWeakSolution_or_constant_laurent_of_charP
    (A B C K L M : Type uK)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hweak : IsWeaklyUnramified A B)
    (hram : ∀ (η : L) (w : M), w ^ p - w = algebraMap L M η →
      Algebra.adjoin L {w} = ⊤ → η ∉ (algebraMap B L).range) :
    (∃ (E : Type uK) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
        (_ : IsScalarTower A K E) (_ : Module.Finite K E),
        ∃ D : IntegralClosureBaseChange.{uK, uK, uK, uK, uK, uK, uK, uK}
          A C K M E, D.IsWeakSolution) ∨
      ∃ (π : A) (n : ℕ) (ξ : L) (z : M)
        (lift : IsLocalRing.ResidueField B → B)
        (liftMod : IsLocalRing.ResidueField B →+*
          B ⧸ (IsLocalRing.maximalIdeal B) ^ n)
        (coeff : ℕ → IsLocalRing.ResidueField B) (b : B),
        Irreducible π ∧ 0 < n ∧
        z ^ p - z = algebraMap L M ξ ∧ Algebra.adjoin L {z} = ⊤ ∧
        (∀ x, IsLocalRing.residue B (lift x) = x) ∧
        (∀ x, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (lift x) = liftMod x) ∧
        ξ = (∑ i ∈ Finset.range n, algebraMap B L (lift (coeff i)) *
            (algebraMap B L (algebraMap A B π))⁻¹ ^ (n - i)) + algebraMap B L b ∧
        (∀ (m : ℕ) (η : L) (w : M),
          w ^ p - w = algebraMap L M η → Algebra.adjoin L {w} = ⊤ →
          algebraMap A L π ^ m * η ∈ (algebraMap B L).range → n ≤ m) ∧
        ∀ k ∈ Finset.range n, ∀ m : ℕ,
          ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ m) = coeff k := by
  classical
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, ξ, z, lift, liftMod, coeff, b, J, depth, wildRoot,
      hn, hz, hgen, hlift, hliftMod, hexp, hmin, hJn, hwildPow,
      hwildTerminal, htame, hsep⟩ :=
    exists_prepared_wild_laurent_of_charP A B K L M p hp hdegree hweak π hπ hram
  by_cases hJ : J.Nonempty
  · obtain ⟨E, hE, hKE, hAE, htower, hfin, hgal, htot, rank, hdeg, hsol⟩ :=
      exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_wild_laurent
        A K (fun _ : Unit => B) (fun _ : Unit => C) (fun _ : Unit => L)
        (fun _ : Unit => M) p hp (fun _ => hweak) π hπ (fun _ => ξ) (fun _ => z)
        (fun _ => hz) (fun _ => hgen) (fun _ => n) (fun _ => hn)
        (fun _ => lift) (fun _ => hlift) (fun _ => liftMod) (fun _ => hliftMod)
        (fun _ => coeff) (fun _ => b) (fun _ => hexp) (fun _ => J) (fun _ => hJ)
        (fun _ => hJn) (fun _ => depth) (fun _ => wildRoot) (fun _ => hwildPow)
        (fun _ => hwildTerminal) (fun _ => htame) (fun _ => hsep)
    exact Or.inl ⟨E, hE, hKE, hAE, htower, hfin, hsol ()⟩
  · have hJ0 : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    refine Or.inr ⟨π, n, ξ, z, lift, liftMod, coeff, b, hπ, hn, hz, hgen,
      hlift, hliftMod, hexp, ?_, ?_⟩
    · intro m η w hw hwgen hmem
      apply hmin m η w hw hwgen
      simpa only [← IsScalarTower.algebraMap_apply A B L] using hmem
    · intro k hk m
      exact htame k hk (by simp [hJ0]) m

end IsDiscreteValuationRing

end
