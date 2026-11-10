module

public import StacksFrontier.FieldTheory.PerfectCore

/-!
# Epp's complete degree-`p` case, as corrected by Kuhlmann

The Stacks Project's route to Epp's theorem on elimination of wild ramification (Tag 09F9) goes
through Tag 09ET, whose weak-solution clause is false; see
`StacksFrontier/RingTheory/DiscreteValuationRing/EppConditionalDescent.lean` for the exact sentence
of the published argument that fails.  The alternative taken here is a
**Route 2**: prove Epp's theorem over the *original* residue fields, following Epp's own paper
rather than the separable-closure reduction.

This file is the groundwork for the step of Route 2 that needs the most care, namely Epp's
**complete degree-`p` case** — his Theorem (1.3) — because that is the one step of Epp's paper
that is known to have a gap, and the gap was closed by Kuhlmann.  What is here is a study of the
corrected argument, a dependency-ordered decomposition of it into Lean-ready statements, and the
bottom layers of that decomposition, proved.  The complete case itself is **not** proved here and
nothing below claims it; the deferred steps are marked `NOT PROVED` in the decomposition and
appear nowhere as unproved declarations.

**Warning to anyone reading the decomposition below as a work list.** Those markers describe the
tree as it was when this file was written and have gone stale. (E8) is proved, and the
surjectivity half of (E9) is proved; both are cited at their entries. Check the tree before
trusting a `NOT PROVED`, and update the entry when you find it wrong.

## Epp's Theorem (1.3)

Kuhlmann quotes it as follows.  All discrete valuation rings are assumed *complete*.

> **Theorem (1.3).** Let `S` be a `p`-cyclic extension of `S₀` where `S₀` is a weakly unramified
> extension of `R` such that `𝔏 ^ (p ^ ∞) = 𝔎`, where `𝔏` and `𝔎` are the residue fields of `S₀`
> and `R` respectively.  There exists a finite extension `T` of `R` such that `T S` is weakly
> unramified over `T`.

Three things about the hypotheses are worth recording, because they are what make this the right
target for Route 2.

* `𝔏 ^ (p ^ ∞)` is the **perfect core** of `𝔏`, which is `perfectCore 𝔏 p` in this repository
  (`StacksFrontier/FieldTheory/PerfectCore.lean`).  So the hypothesis is
  `perfectCore 𝔏 p = ⊥`-relative-to-`𝔎`, i.e. the perfect core upstairs has *already been
  absorbed into the base*.  This is strictly stronger than Epp's global hypothesis — condition
  (2) of his paper, which this repository calls `Stacks.EppTheorem.EppCondition` — that the largest
  perfect subfield of `κ_S` be separable algebraic over `κ_R`.
* The step that converts the global hypothesis into Theorem (1.3)'s hypothesis is precisely the
  **finite unramified base change** already built in
  `StacksFrontier/RingTheory/DiscreteValuationRing/EppUnramifiedBaseChange.lean`:
  `Stacks.EppTheorem.exists_isWeaklyUnramified_residueField_algEquiv_perfectCore` produces a finite
  weakly unramified `A₁ / A` with `κ_{A₁} ≅ perfectCore κ_B p`.  Route 2's opening move and
  Theorem (1.3)'s hypothesis fit together exactly.
* Theorem (1.3) is an **inductive step**, not Epp's theorem: it handles one `p`-cyclic layer over
  a weakly unramified base.  Assembling the layers is separate work and is not analysed here.

`p`-cyclic means cyclic Galois of degree `p` on fraction fields; weakly unramified means
ramification index one, which is `IsDiscreteValuationRing.IsWeaklyUnramified` in
`StacksFrontier/RingTheory/DiscreteValuationRing/Solution.lean`.

## Epp's proof of the equal-characteristic case, and its gap

Kuhlmann's correction concerns the **equal characteristic `p ≠ 0`** case only; the mixed
characteristic case of (1.3) is not at issue.  The argument, as Kuhlmann sketches it:

1. By the structure theorems, `R = 𝔎[[π]]` and `S₀ = 𝔏[[π]]` with `π` a local parameter of `R`
   (a local parameter of `S₀` too, since `S₀ / R` is weakly unramified).
2. `X ^ p - X` is additive and surjective on the maximal ideal of `S₀`, so Artin–Schreier theory
   puts the `p`-cyclic extension `S / S₀` in the normal form

   `z ^ p - z = a₋ₙ π ^ (-N) + ⋯ + a₋₁ π ^ (-1) + a₀`, with all `aᵢ ∈ 𝔏`.  **(1)**

   (Kuhlmann's text prints `aᵢ ∈ 𝔎` here; that is a typo — the very next definitions split the
   indices according to whether `a₋ₘ` lies in `𝔎`, and the second bullet of (2) below places
   `c₋ₘ ∈ 𝔏 ∖ 𝔏 ^ p`.  The coefficients are residues of `S₀`, hence in `𝔏`.)
3. `N = 0` is trivial, so assume `N ≠ 0`, and split `{1, …, N}` into

   `I = {m | a₋ₘ ∈ 𝔎, a₋ₘ ≠ 0}` (*tame*) and `J = {m | a₋ₘ ∉ 𝔎, a₋ₘ ≠ 0}` (*wild*).

   The case `J = ∅` is handled separately; assume `J ≠ ∅`.
4. The goal is a `d ∈ 𝔎[[t]]`, where `t ^ (p ^ k) = π`, such that after `z ↦ z - d` — which adds
   `d - d ^ p` to the right-hand side — the defining equation of `𝔎[[t]] S` over `𝔎[[t]]` reads
   `z ^ p - z = c t ^ (-n) + ⋯` with `p ∣ n` and `c ∉ 𝔏 ^ p`.  Epp shows that this makes
   `𝔎[[t]] S` weakly unramified over `𝔎[[t]]`, so `T = 𝔎[[t]]` works.
5. Such a substitution replaces a `p`-th power `d ^ p` on the right-hand side by its `p`-th root
   `d`.  Iterating, Epp removes the coefficients lying in `𝔏 ^ p ∖ 𝔎`.  He chooses `ν ≥ 1` with
   `min_{m ∈ J} m p ^ ν > max_{m ∈ I} m`, sets `ν_m := max {i | a₋ₘ ∈ 𝔏 ^ (p ^ i)}` — finite for
   `m ∈ J` exactly because `𝔏 ^ (p ^ ∞) = 𝔎` and `a₋ₘ ∉ 𝔎` — puts `μ := max {ν_m | m ∈ J}`, and
   takes `t` with `t ^ (p ^ (ν + μ)) = π`.  The substitutions then yield

   `z ^ p - z = ∑_{m ∈ J} c₋ₘ t ^ (-m p ^ (ν + μ - ν_m)) + ∑_{s ∈ I} c₋ₛ t ^ (-s) + a₀`  **(2)**

   where `c₋ₛ ∈ 𝔎` is the `p ^ (ν + μ)`-th root of `a₋ₛ` (`𝔎` is perfect), `c₋ₘ ∈ 𝔏 ∖ 𝔏 ^ p` is
   the `p ^ (ν_m)`-th root of `a₋ₘ`, every wild exponent is divisible by `p` (as `ν ≥ 1` and
   `μ ≥ ν_m`), and every tame exponent is strictly smaller in absolute value than every wild one
   (as `s < m p ^ ν`).

**The false step.** Epp then claims that in (2) the term of most negative exponent has
coefficient outside `𝔏 ^ p`.  Kuhlmann: *"This is not necessarily true. It would hold if the
exponents `-m p ^ (ν + μ - ν_m)` were distinct, for distinct `m`. But this could be false since
we know nothing about the `ν_m`."*

## Kuhlmann's Example

Take

`z ^ p - z = a₋ₘ₀ π ^ (-m₀) + a₋ₘ₁ π ^ (-m₁) + ⋯`,
`m₀ = m₁ p`, `a₋ₘ₀ = c₀ ^ p`, `a₋ₘ₁ = c₁ - c₀`, with `c₀ ∈ 𝔏 ∖ 𝔏 ^ p` and `c₁ ∈ 𝔏 ^ p`.

Then `a₋ₘ₀ ∉ 𝔎`, `a₋ₘ₁ ∉ 𝔏 ^ p`, `ν_{m₁} = 0`, `ν_{m₀} = 1`, and
`a₋ₘ₁ + a₋ₘ₀ ^ (1/p) = a₋ₘ₁ + c₀ = c₁ ∈ 𝔏 ^ p`.  In the notation of (2) the two wild exponents
collide, `-m₀ p ^ (ν + μ - ν_{m₀}) = -m₁ p ^ (ν + μ - ν_{m₁})`, and the coefficients recombine,
`c₋ₘ₀ + c₋ₘ₁ = c₁ ∈ 𝔏 ^ p`.  Choosing `c₁ ∈ 𝔎` makes the recombined coefficient lie in `𝔎`, so
that exponent "switches" from `J` to `I`.

## Kuhlmann's correction

*"However, whenever such a recombination happens and we start over with the new equation (2), the
new set `J` will be smaller than the original set `J`.  So the gap in Epp's proof can be closed by
repeating his transformations until his assertion is satisfied or the set `J` is empty."*

So the fix is a **termination argument**: the loop `(1) ↦ (2) ↦ (2) ↦ ⋯` has the strictly
decreasing measure `#J`, and its exit condition is "Epp's assertion holds, or `J = ∅`".  No
hypothesis of Theorem (1.3) changes; only its proof.

Kuhlmann adds one correction to a *conclusion*.  `J` can genuinely become empty: with `c₁ = 0`
and `z ^ p - z = a₋ₘ₀ π ^ (-m₀) + a₋ₘ₁ π ^ (-m₁) + a₀`, the transformation leads to
`z ^ p - z = a₀`.  Hence even when `J ≠ ∅` in (1), the residue extension of `T S / T` may come
out **Artin–Schreier**, i.e. separable, and not purely inseparable as Epp concludes in that case.
Anything downstream that uses the finer form of Epp's conclusion, rather than just weak
unramifiedness, must therefore be re-derived.

## Decomposition into Lean-ready statements

Dependency order, bottom-up.  `F` plays the role of `𝔏` throughout and `perfectCore F p` the role
of `𝔎`, so that Theorem (1.3)'s hypothesis `𝔏 ^ (p ^ ∞) = 𝔎` is *definitionally* satisfied by
this naming rather than being an extra assumption.

**(K1) The Frobenius tower.** `frobeniusPowRange F p n : Subfield F` is `F ^ (p ^ n)`; the tower
is antitone and its intersection is the perfect core.
`theorem mem_frobeniusPowRange {n : ℕ} {x : F} : x ∈ frobeniusPowRange F p n ↔ ∃ y, y ^ p ^ n = x`
Depends on: `perfectCore` (already in `StacksFrontier/FieldTheory/PerfectCore.lean`).  **PROVED
HERE** — `frobeniusPowRange`, `mem_frobeniusPowRange`, `mem_frobeniusPowRange_zero`,
`frobeniusPowRange_antitone`, `mem_perfectCore_iff_forall_mem_frobeniusPowRange`,
`perfectCore_le_frobeniusPowRange`.  Not previously in the repository.

**(K2) Finiteness of `ν_m`.** The set of stages containing a given element is bounded above as
soon as the element is outside the perfect core.  This is the one place Theorem (1.3)'s hypothesis
is used in the bookkeeping, and it is the reason `ν_m` exists at all.
`theorem bddAbove_setOf_mem_frobeniusPowRange (hx : x ∉ perfectCore F p) :
  BddAbove {n : ℕ | x ∈ frobeniusPowRange F p n}`
Depends on: (K1).  **PROVED HERE.**

**(K3) Kuhlmann's `ν_m`.** `frobeniusDepth F p x`, with its characterisation as the unique `n`
with `x ∈ F ^ (p ^ n) ∖ F ^ (p ^ (n + 1))` — Kuhlmann's parenthetical "recall that
`a₋ₘ ∈ 𝔏 ^ (p ^ ν_m) ∖ 𝔏 ^ (p ^ (ν_m + 1))`".
`theorem frobeniusDepth_eq_iff (hx : x ∉ perfectCore F p) {n : ℕ} :
  frobeniusDepth F p x = n ↔
    x ∈ frobeniusPowRange F p n ∧ x ∉ frobeniusPowRange F p (n + 1)`
Depends on: (K2).  **PROVED HERE**, with `frobeniusDepth_eq_zero_iff`.

**(K4) Frobenius reflects the perfect core.** `x ^ p ∈ perfectCore F p → x ∈ perfectCore F p`,
needed to see that `a₋ₘ₀ = c₀ ^ p` is wild in Kuhlmann's Example.
`theorem pow_notMem_perfectCore (hx : x ∉ perfectCore F p) : x ^ p ∉ perfectCore F p`
Depends on: nothing beyond `perfectCore`.  **PROVED HERE.**

**(K5) The tame/wild splitting and Epp's bookkeeping.** `Stacks.EppTheorem.PolePart F p` bundles
the coefficient family `a₋ₘ` with Epp's `I` and `J`; `depth` is `ν_m`, `maxDepth` is `μ`, and
`Stacks.EppTheorem.eppExponent p ν μ d m = m * p ^ (ν + μ - d)` is the exponent of (2).  The four
  bullets
after (2), in Lean:
`theorem PolePart.dvd_exponent (hν : 1 ≤ ν) (hm : m ∈ s.wild) :
  p ∣ eppExponent p ν s.maxDepth (s.depth m) m`
`theorem PolePart.exists_nu (hp : 1 < p) (hJ : s.wild.Nonempty) :
  ∃ ν, 1 ≤ ν ∧ ∀ m ∈ s.wild, ∀ t ∈ s.tame, t < eppExponent p ν s.maxDepth (s.depth m) m`
Depends on: (K3).  **PROVED HERE**, with `dvd_eppExponent`, `lt_eppExponent`,
`exists_one_le_forall_lt_mul_pow`, `exists_one_le_forall_mem_lt`, `PolePart.lt_exponent`, and the
`ν_m`-level facts `PolePart.coeff_mem_frobeniusPowRange_depth` and
`PolePart.coeff_notMem_frobeniusPowRange_depth_succ`.

**(K6) The collision, and that Epp's assertion really fails.** Kuhlmann's Example, formalised as
far as it is field theory and arithmetic: the exponents coincide, the coefficients recombine into
`F ^ p`, and the configuration exists over any field with a non-`p`-th-power.
`theorem eppExponent_collision (h : 1 ≤ ν + μ) :
  eppExponent p ν μ 1 (m₁ * p) = eppExponent p ν μ 0 m₁`
`theorem frobeniusDepth_sub_eq_zero (hc₀ : c₀ ∉ frobeniusPowRange F p 1)
  (hc₁ : c₁ ∈ frobeniusPowRange F p 1) : frobeniusDepth F p (c₁ - c₀) = 0`
`theorem frobeniusDepth_pow_eq_one (hc₀ : c₀ ∉ frobeniusPowRange F p 1) :
  frobeniusDepth F p (c₀ ^ p) = 1`
Depends on: (K3), (K4).  **PROVED HERE**, with `sub_notMem_frobeniusPowRange_one`,
`pow_notMem_frobeniusPowRange_two`, `eq_of_pow_eq_pow_self`,
`add_sub_cancel_mem_frobeniusPowRange_one` and `exists_kuhlmann_example`.  This is the certificate
that the step Epp asserts is genuinely false, in the same spirit as the certificate for Tag 09ET
in `EppConditionalDescent.lean`.

**(K7) The correction itself.** A collision makes the exponent map of (2) non-injective on `J`,
which strictly shrinks the index set; and a strictly shrinking `Finset` measure makes the loop
terminate.
`theorem not_injOn_eppExponent (hp : 1 < p) (hm₁ : 1 ≤ m₁) (hνμ : 1 ≤ ν + μ)
  (hd₀ : d (m₁ * p) = 1) (hd₁ : d m₁ = 0) (h₀ : m₁ * p ∈ J) (h₁ : m₁ ∈ J) :
  ¬ Set.InjOn (fun m => eppExponent p ν μ (d m) m) ↑J`
`theorem card_image_lt_card_of_not_injOn (h : ¬ Set.InjOn f ↑J) :
  (J.image f).card < J.card`
`theorem exists_iterate_good_or_wild_eq_empty
  (hstep : ∀ x, ¬ Good x → (wild x).Nonempty → (wild (step x)).card < (wild x).card) (x : α) :
  ∃ n, Good (step^[n] x) ∨ wild (step^[n] x) = ∅`
Depends on: (K5), (K6).  **PROVED HERE**, with
`exists_iterate_good_or_wild_eq_empty_of_ssubset`, which is the shape in which Kuhlmann phrases
the decrease.  `Good` is instantiated by `Stacks.EppTheorem.IsEppReduced`, also defined here.

**(E8) The equal-characteristic structure theorem.** `R ≅ 𝔎[[π]]` and `S₀ ≅ 𝔏[[π]]` for a weakly
unramified extension of complete discrete valuation rings of equal characteristic `p`.
`theorem exists_powerSeriesAlgEquiv (R : Type*) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  (hchar : ringChar R = p) :
  Nonempty (R ≃+* PowerSeries (IsLocalRing.ResidueField R))`
Depends on: nothing in this file.  **PROVED**, in
`StacksFrontier/RingTheory/DiscreteValuationRing/EqualCharacteristicStructure.lean`:
`Stacks.EppTheorem.exists_powerSeriesRingEquiv_of_irreducible` gives `R ≃+* 𝔎[[X]]` sending `X` to
a prescribed uniformizer and splitting the residue map, `exists_powerSeriesRingEquiv` and
`exists_powerSeriesRingEquiv_of_ringChar` are the unparameterised forms, and
`exists_powerSeriesRingEquiv_common_uniformizer` is exactly the weakly unramified pair on **one
common uniformizer** that (E9) needs.
`StacksFrontier/RingTheory/DiscreteValuationRing/EppCohenReduction.lean` covers the *mixed*
characteristic Cohen reduction, steps (a) and (c), with step (b) blocked by a `DiscreteTopology`
mismatch in this tree's Tag 07NJ.

**(E9) The Artin–Schreier normal form (1).** Surjectivity of `X ^ p - X` on the maximal ideal of
`𝔏[[π]]` (the geometric series `-∑ₖ w ^ (p ^ k)` converges there), and hence a generator of a
`p`-cyclic extension whose defining element is a pole part plus a constant.
`theorem exists_artinSchreier_polePart :
  ∃ (N : ℕ) (a : ℕ → 𝔏) (z : L), IsGenerator z ∧ z ^ p - z = polePart a N`
Depends on: (E8).  **The surjectivity half is PROVED**, in
`StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreierSurjective.lean`:
`exists_pow_sub_self_eq_of_mem_maximalIdeal` and `pow_sub_self_surjOn_maximalIdeal`, by Hensel
rather than by summing `-∑ₖ w ^ (p ^ k)`.  What is still owed is the *normal form* — turning a
`p`-cyclic extension into a generator whose parameter is a pole part plus a constant.  Note before
starting it that `ArtinSchreier.lean` already has Laurent-presentation machinery
(`exists_artinSchreier_presentation_minimal_poleOrder`, `exists_laurent_expansion`,
`exists_artinSchreier_laurent_presentation_without_related_poles`), so the remaining gap may be
narrower than a fresh development.

**(E10) The substitution step.** For `d` in the coefficient ring, `z ↦ z - d` adds `d - d ^ p` to
the right-hand side; iterating over `m ∈ J` in decreasing order of `ν_m` transforms (1) into (2),
replacing each `a₋ₘ` by its `p ^ (ν_m)`-th root at exponent `m p ^ (ν + μ - ν_m)`.
`theorem exists_step (s : PolePart F p) (hJ : s.wild.Nonempty) :
  ∃ s' : PolePart F p, IsEppReduced F p s'.coeff n ∨ s'.wild ⊂ s.wild`
Depends on: (E9), (K5).  **NOT PROVED.**  This is the analytic heart of the loop, and the only
step where (K7)'s abstract `step` becomes concrete.

**(E11) Epp's weak-unramifiedness criterion.** If the equation over `T = 𝔎[[t]]` is
`z ^ p - z = c t ^ (-n) + ⋯` with `p ∣ n` and `c ∉ 𝔏 ^ p`, then `T S / T` is weakly unramified
(substitute `z = y t ^ (-n/p)`: modulo the maximal ideal `ȳ ^ p = c̄`, and `X ^ p - c` is
irreducible over `𝔏`, so the residue degree is already `p` and `e = 1`).
`theorem isWeaklyUnramified_of_isEppReduced (h : IsEppReduced F p c n) :
  IsDiscreteValuationRing.IsWeaklyUnramified T (T S)`
Depends on: (E8), `IsEppReduced`.  **PROVED**, in
`StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier.lean`:
`IsDiscreteValuationRing.isWeaklyUnramified_of_artinSchreier_residue_not_pow` is exactly this
criterion — from `z ^ p - z = algebraMap L M ξ` with
`ξ = (algebraMap B L π)⁻¹ ^ n * algebraMap B L a`, `0 < n`, `p ∣ n` and `residue B a` not a
`p`-th power, it concludes `IsWeaklyUnramified B C`.  Its
three hypotheses `hpn`, `hn` and `ha` are the three conjuncts of `IsEppReduced` other than the
trailing vanishing condition, so a consumer holding `IsEppReduced F p c n` supplies it directly.
(This entry previously read "NOT PROVED".)

**(E12) The `J = ∅` branch, and Kuhlmann's corrected conclusion.** When `J = ∅` the equation is
defined over the perfect field `𝔎`, and after `t ^ (p ^ k) = π` the substitutions reduce it to
`z ^ p - z = a₀`, which is weakly unramified with *separable* — Artin–Schreier — residue
extension.  Kuhlmann's observation is that this branch is reachable even from `J ≠ ∅`, so the
disjunction in (K7) is not cosmetic and the conclusion of (E12) is what must be quoted, not
Epp's "purely inseparable".
Depends on: (E8), (E11).  **NOT PROVED** as a standalone statement — but see the note below:
the theorem (E9)–(E12) were jointly building toward is itself already proved by a different route.

**The whole of (E9)–(E12) is subsumed.**  What this chain was assembling is the *equal-
characteristic degree-`p` case* of Epp's theorem, and that case is proved in
`StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier.lean` as
`IsDiscreteValuationRing.exists_isGalois_totallyRamified_isWeakSolution_of_charP`, tagged
`@[stacks 09F1]`, with no algebraic closedness, no Kuhlmann loop, and no appeal to the refuted
Tag 09ET.  Two strictly more general forms sit beneath it:
`..._of_charP_of_perfectCore_le`, which needs only perfectness of `κ_A` plus
`perfectCore κ_B p ⊆ image κ_A`, and `..._of_charP_of_finiteSupport_of_uniformizer`, which takes
*no* residue hypothesis at all and instead returns a finite set `S ⊆ κ_B` and a depth `N` with the
requirement as an antecedent.  That last form is the live one: its antecedent is what a consumer
must discharge from `Stacks.EppTheorem.EppCondition`, and because the uniformizer is an input, `S`
  and `N`
are invariant under replacing `A` by a finite weakly unramified `A₁ ⊆ B`.

So the route to the equal-characteristic case does not run through Kuhlmann's pole-part loop at
all; it runs through the intrinsic perfect-core classification of the Laurent coefficients.  The
value of (K1)–(K7) below is unchanged — they are the certificate that Epp's own step is false —
but (E9)–(E13) should not be read as a work plan.  Anyone picking this up should start from
`..._of_charP_of_finiteSupport_of_uniformizer` and
`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`, whose
  composition is
blocked only by `S` and `N` being existentially bound rather than exposed.

**(E13) Theorem (1.3).** Assemble (E8)–(E12) through (K7).
`theorem exists_finite_isWeaklyUnramified (R S₀ S : Type*) [...] [IsExtension R S₀]
  (hwu : IsDiscreteValuationRing.IsWeaklyUnramified R S₀)
  (hcore : perfectCore (ResidueField S₀) p = ⊥-relative-to-(ResidueField R))
  (hcyc : IsPCyclic S₀ S) :
  ∃ (T : Type*) [...], Module.Finite R T ∧
    IsDiscreteValuationRing.IsWeaklyUnramified T (normalizedJoin S T)`
Depends on: all of the above.  **NOT PROVED.**  The normalised-join package is Tag 09EN's
`IsDiscreteValuationRing.IntegralClosureBaseChange` in
`StacksFrontier/RingTheory/DiscreteValuationRing/Solution.lean`; it has no general constructor yet,
so the shape of the conclusion should be revisited once one exists.

## What is proved here

(K1)–(K7): the Frobenius tower, the well-definedness and characterisation of Kuhlmann's `ν_m`,
the fact that Frobenius does not move elements into the perfect core, Epp's tame/wild splitting
with all four bullets of equation (2), Kuhlmann's Example as a certificate that Epp's assertion
is false, and Kuhlmann's correction itself in the form of the collision, the strict decrease of
the index set, and the termination of the loop.

(E8)–(E13) are not proved and are not stated as theorems.  `IsEppReduced` is the only `Prop` this
file defines for a deferred step, and it is a definition, not a claim.

Also proved here, and belonging to a *different* recursion: `solves_of_prescribed` and
`forall_solves_of_prescribed`.  Kuhlmann's loop (K7) terminates the transformations *within* one
degree-`p` layer; those two terminate the descent *across* layers, for a whole finite family of
towers at once, which is what the all-factor route to Tag 09F9 needs and what Tag 09F8's pointwise
`normalTowerSolvable` does not provide.  They are abstract in the same way (K7) is — no ring
theory, the shared base extension left opaque — and they take that extension as a **parameter**,
which is what removes the need to amalgamate separately chosen extensions.  See the section
docstring.

Also proved here: `exists_iterate_good_or_pole_eq_zero`, the termination statement for the
pole-order reduction, beside the `Finset`-measure loop lemma it is the sibling of.

The all-perfect-core (constant-numerator) lemmas that used to live here have moved to
`StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync`, because finishing them needs
the truncated lifting datum of
`StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier`, which this file deliberately
does not import.

## References

* [Epp, *Eliminating wild ramification*, Invent. Math. **19** (1973) 235–249][epp1973]
* Franz-Viktor Kuhlmann, *A correction to Epp's paper "Elimination of wild ramification"*,
  Invent. Math. **153** (2004) 679–681;
  [arXiv:1003.5687](https://arxiv.org/abs/1003.5687).  All quotations above are from this note.
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
-/

@[expose] public section

/-! ### The subfields `F ^ (p ^ n)` and the depth `ν_x` -/

variable (F : Type*) [Field F] (p : ℕ) [ExpChar F p]

/-- The subfield `F ^ (p ^ n)` of `p ^ n`-th powers of `F`, as the range of the `n`-fold
Frobenius endomorphism. -/
def frobeniusPowRange (n : ℕ) : Subfield F := (iterateFrobenius F p n).fieldRange

variable {F p}

/-- Membership in `F ^ (p ^ n)` is being a `p ^ n`-th power. -/
theorem mem_frobeniusPowRange {n : ℕ} {x : F} :
    x ∈ frobeniusPowRange F p n ↔ ∃ y : F, y ^ p ^ n = x := by
  simp only [frobeniusPowRange, RingHom.mem_fieldRange, iterateFrobenius_def]

/-- `F ^ (p ^ 0) = F`. -/
theorem mem_frobeniusPowRange_zero (x : F) : x ∈ frobeniusPowRange F p 0 :=
  mem_frobeniusPowRange.mpr ⟨x, by simp⟩

/-- The tower `F ⊇ F ^ p ⊇ F ^ (p ^ 2) ⊇ ⋯` is decreasing. -/
theorem frobeniusPowRange_antitone : Antitone (frobeniusPowRange F p) := by
  refine antitone_nat_of_succ_le fun n => ?_
  intro x hx
  obtain ⟨y, hy⟩ := mem_frobeniusPowRange.mp hx
  refine mem_frobeniusPowRange.mpr ⟨y ^ p, ?_⟩
  rw [← pow_mul, ← pow_succ']
  exact hy

/-- The perfect core is the intersection of the tower `F ^ (p ^ n)`. -/
theorem mem_perfectCore_iff_forall_mem_frobeniusPowRange {x : F} :
    x ∈ perfectCore F p ↔ ∀ n : ℕ, x ∈ frobeniusPowRange F p n := by
  simp only [perfectCore, frobeniusPowRange, Subfield.mem_iInf]

/-- The perfect core sits inside every stage of the Frobenius tower. -/
theorem perfectCore_le_frobeniusPowRange (n : ℕ) :
    perfectCore F p ≤ frobeniusPowRange F p n :=
  fun _ hx => mem_perfectCore_iff_forall_mem_frobeniusPowRange.mp hx n

/-- An element outside the perfect core lies in only finitely many stages of the Frobenius
tower.  This is the finiteness that makes Kuhlmann's `ν_m` well defined. -/
theorem bddAbove_setOf_mem_frobeniusPowRange {x : F} (hx : x ∉ perfectCore F p) :
    BddAbove {n : ℕ | x ∈ frobeniusPowRange F p n} := by
  have hne : ¬ ∀ n : ℕ, x ∈ frobeniusPowRange F p n := fun h =>
    hx (mem_perfectCore_iff_forall_mem_frobeniusPowRange.mpr h)
  obtain ⟨n₀, hn₀⟩ := not_forall.mp hne
  refine ⟨n₀, fun n hn => ?_⟩
  by_contra hlt
  exact hn₀ (frobeniusPowRange_antitone (le_of_lt (not_le.mp hlt)) hn)

/-- Taking `p`-th powers does not move an element into the perfect core. -/
theorem pow_notMem_perfectCore {x : F} (hx : x ∉ perfectCore F p) :
    x ^ p ∉ perfectCore F p := by
  intro h
  refine hx (mem_perfectCore_iff.mpr fun n => ?_)
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp h (n + 1)
  have hinj : (y ^ p ^ n) ^ p = x ^ p := by rw [← pow_mul, ← pow_succ]; exact hy
  exact ⟨y, frobenius_inj F p (by simpa [frobenius_def] using hinj)⟩

/-- **Kuhlmann's `ν_x`**: the greatest `n` with `x ∈ F ^ (p ^ n)`.

Kuhlmann writes `ν_m := max {i | a₋ₘ ∈ 𝔏 ^ (p ^ i)}` and notes that it is finite for every
`m ∈ J`, precisely because `𝔏 ^ (p ^ ∞) = 𝔎` and `a₋ₘ ∉ 𝔎`.  The junk value at an element of
the perfect core is `0`; every lemma below carries the hypothesis `x ∉ perfectCore F p`. -/
noncomputable def frobeniusDepth (F : Type*) [Field F] (p : ℕ) [ExpChar F p] (x : F) : ℕ :=
  sSup {n : ℕ | x ∈ frobeniusPowRange F p n}

/-- `x` is a `p ^ (ν_x)`-th power. -/
theorem mem_frobeniusPowRange_frobeniusDepth {x : F} (hx : x ∉ perfectCore F p) :
    x ∈ frobeniusPowRange F p (frobeniusDepth F p x) :=
  Nat.sSup_mem ⟨0, mem_frobeniusPowRange_zero x⟩ (bddAbove_setOf_mem_frobeniusPowRange hx)

/-- `x` is not a `p ^ (ν_x + 1)`-th power. -/
theorem notMem_frobeniusPowRange_frobeniusDepth_succ {x : F} (hx : x ∉ perfectCore F p) :
    x ∉ frobeniusPowRange F p (frobeniusDepth F p x + 1) := by
  intro h
  have h2 : frobeniusDepth F p x + 1 ≤ frobeniusDepth F p x :=
    le_csSup (bddAbove_setOf_mem_frobeniusPowRange hx) h
  omega

/-- Kuhlmann's characterisation of `ν_m`: it is the unique `n` with
`a₋ₘ ∈ 𝔏 ^ (p ^ n) ∖ 𝔏 ^ (p ^ (n + 1))`. -/
theorem frobeniusDepth_eq_iff {x : F} (hx : x ∉ perfectCore F p) {n : ℕ} :
    frobeniusDepth F p x = n ↔
      x ∈ frobeniusPowRange F p n ∧ x ∉ frobeniusPowRange F p (n + 1) := by
  refine ⟨fun h => h ▸ ⟨mem_frobeniusPowRange_frobeniusDepth hx,
    notMem_frobeniusPowRange_frobeniusDepth_succ hx⟩, fun h => ?_⟩
  have hle : n ≤ frobeniusDepth F p x :=
    le_csSup (bddAbove_setOf_mem_frobeniusPowRange hx) h.1
  have hge : frobeniusDepth F p x ≤ n := by
    by_contra hc
    exact h.2 (frobeniusPowRange_antitone (by omega : n + 1 ≤ frobeniusDepth F p x)
      (mem_frobeniusPowRange_frobeniusDepth hx))
  omega

/-- `ν_x = 0` exactly when `x` is not a `p`-th power. -/
theorem frobeniusDepth_eq_zero_iff {x : F} (hx : x ∉ perfectCore F p) :
    frobeniusDepth F p x = 0 ↔ x ∉ frobeniusPowRange F p 1 := by
  rw [frobeniusDepth_eq_iff hx, zero_add, and_iff_right (mem_frobeniusPowRange_zero x)]

namespace Stacks.EppTheorem

/-! ### Kuhlmann's termination argument -/

section Loop

variable {α ι : Type*} (wild : α → Finset ι) (step : α → α) (Good : α → Prop)

/-- Iterating a step that strictly decreases a positive `ℕ`-valued measure reaches a `Good` state
or measure zero. -/
private theorem exists_iterate_good_or_measure_eq_zero (measure : α → ℕ)
    (hstep : ∀ x, ¬ Good x → 0 < measure x → measure (step x) < measure x) (x : α) :
    ∃ m : ℕ, Good (step^[m] x) ∨ measure (step^[m] x) = 0 := by
  suffices H : ∀ k : ℕ, ∀ y : α, measure y ≤ k →
      ∃ m : ℕ, Good (step^[m] y) ∨ measure (step^[m] y) = 0 from H (measure x) x le_rfl
  intro k
  induction k with
  | zero =>
    intro y hy
    exact ⟨0, Or.inr (by simpa using Nat.le_zero.mp hy)⟩
  | succ k ih =>
    intro y hy
    by_cases hg : Good y
    · exact ⟨0, Or.inl (by simpa using hg)⟩
    by_cases he : measure y = 0
    · exact ⟨0, Or.inr (by simpa using he)⟩
    have hlt := hstep y hg (Nat.pos_of_ne_zero he)
    obtain ⟨m, hm⟩ := ih (step y) (by omega)
    exact ⟨m + 1, by rwa [Function.iterate_succ_apply]⟩

/-- **Kuhlmann's correction to Epp, as a termination statement.**

Epp's proof performs a substitution `z ↦ z - d` and then *asserts* that the resulting equation is
in reduced form (`Good`).  It need not be, because two wild exponents can collide and their
coefficients recombine.  Kuhlmann's observation is that each such recombination makes the wild set
`J` strictly smaller, so iterating the substitution reaches a state that is either reduced or has
empty wild set.  That is exactly this lemma, with `wild = J` and `Good` = Epp's assertion. -/
theorem exists_iterate_good_or_wild_eq_empty
    (hstep : ∀ x, ¬ Good x → (wild x).Nonempty → (wild (step x)).card < (wild x).card) (x : α) :
    ∃ n : ℕ, Good (step^[n] x) ∨ wild (step^[n] x) = ∅ := by
  obtain ⟨n, hn⟩ := exists_iterate_good_or_measure_eq_zero step Good (fun y => (wild y).card)
    (fun y hg h0 => hstep y hg (Finset.card_pos.mp h0)) x
  exact ⟨n, hn.imp_right Finset.card_eq_zero.mp⟩

/-- The form in which Kuhlmann states the decrease: "the new set `J` will be smaller than the
original set `J`". -/
theorem exists_iterate_good_or_wild_eq_empty_of_ssubset
    (hstep : ∀ x, ¬ Good x → (wild x).Nonempty → wild (step x) ⊂ wild x) (x : α) :
    ∃ n : ℕ, Good (step^[n] x) ∨ wild (step^[n] x) = ∅ :=
  exists_iterate_good_or_wild_eq_empty wild step Good
    (fun y hg hne => Finset.card_lt_card (hstep y hg hne)) x

/-- **The pole-order reduction terminates.**

The `ℕ`-measure sibling of `exists_iterate_good_or_wild_eq_empty`: iterating a step that strictly
decreases a natural-number measure, as long as the measure is positive and the exit condition has
not been met, reaches a state that is either `Good` or has measure zero.

This is the termination statement for Epp's reduction of the Artin--Schreier pole order, where
`pole` is that order, `step` is one substitution `z ↦ z - d`, and `Good` is the reduced form.  It
is proved the same way as the `Finset`-measure version above and is not new mathematics; it is kept
separate because a pole order is a natural number, and routing it through a `Finset` in order to
reuse that lemma would add a conversion at every call site for no gain.

Note what this does **not** say: that the reduction is one-shot.  An upstream claim that minimality
makes the iteration unnecessary has been disproved, so the iteration is genuinely required and a
consumer must supply the decreasing step. -/
theorem exists_iterate_good_or_pole_eq_zero (pole : α → ℕ)
    (hstep : ∀ x, ¬ Good x → 0 < pole x → pole (step x) < pole x) (x : α) :
    ∃ m : ℕ, Good (step^[m] x) ∨ pole (step^[m] x) = 0 :=
  exists_iterate_good_or_measure_eq_zero step Good pole hstep x

end Loop

/-! ### The finite-family layer recursion, abstractly

`exists_iterate_good_or_wild_eq_empty` above terminates Epp's transformations *within* one
degree-`p` layer.  Assembling the layers of an arbitrary finite extension needs a second,
independent descent, and for the all-factor route to Tag 09F9 it must produce **one** base
extension serving a whole finite family of towers: that is the quantifier order
`Stacks.EppTheorem.FactorSolutions` requires, and Tag 09F8's `normalTowerSolvable` (private,
`EppAlgClosedResidue.lean`) does not provide it — its conclusion is `∃ K₁, ∃ D`, so the recursion
at `EppAlgClosedResidue.lean:4470-4500` invokes it once per conjugate factor and reconciles the
resulting fields with `exists_finite_extension_isWeakSolution_of_factor_solutions`.  That
amalgamation is what `[IsAlgClosed κ_A]` and the two `IsAdicComplete` hypotheses pay for, and it
is unavailable here: weak solutions do not survive arbitrary finite enlargement of the base, and a
common overfield of totally ramified extensions may not be assumed to preserve total ramification.

The lemma below is that descent, and the discipline that makes it work is that the shared resource
is **prescribed**: it is a parameter `r`, not something a sub-problem chooses.

That is not a presentational detail, it is the whole difficulty.  Quantifying the resource
existentially per sub-family, partitioning the family into its terminal and non-terminal parts,
solving each separately, and then combining the two resources by a hypothesis `hmerge` does not
work.  **Such a hypothesis is the forbidden amalgamation.**  Combining two
independently chosen resources into one is exactly the step the route rules out, and it is no
weaker for having two inputs rather than many: the many-input form follows from the two-input form
by induction on the family.  So that route proves a true implication from a hypothesis that
cannot be discharged.

With `r` prescribed there is nothing to combine.  Terminal members are *checked* against the given
`r` by `hterminal` instead of being solved over a field of their own, non-terminal members are
reduced to lower-degree ones by `hsplit` against the same `r`, and the family conclusion
`∀ i, Solves r (f i)` is then immediate from the per-member statement — the sharing is carried
entirely by `r` being quantified *outside* the family rather than once per member.  The existential
is introduced exactly once, by whatever constructs `r`, and in the intended instantiation that is
`IsDiscreteValuationRing.exists_isGalois_totallyRamified_orbitExtension_forall_depth`, whose
parameters come from `exists_shared_orbit_parameters` as bounds over the whole family.

The Kummer-root construction
`Stacks.EppTheorem.exists_sharedExtension_kummerRoot_forall_depth` does not serve here:
  in
equal characteristic an exact `p ^ r`-th root of `π` generates a purely inseparable extension,
while every prescribed solver downstream demands `[Algebra.IsSeparable K E]`.

This is the discipline the prescribed-extension results in the tree already follow —
`IsDiscreteValuationRing.isWeakSolution_of_tame_of_ramificationIndex_dvd`,
`Stacks.EppTheorem.factorSolutions_of_tame`,
`IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`,
`IsDiscreteValuationRing.exists_baseChanged_laurent_reduction` and
`IsDiscreteValuationRing.exists_isWeakSolution_of_baseChanged_artinSchreier_residue` all take the
extension as input — and the reason the shared degree-`p` family solver must be stated the same
way. -/

section SharedFamily

variable {μ R : Type*} (deg : μ → ℕ) (Solves : R → μ → Prop) (Terminal : μ → Prop)

/-- **The finite-family layer descent, against a prescribed shared resource.**

Read `μ` as the towers to be solved, `R` as the candidate base extensions, `Solves r m` as "`r` is
a weak solution for member `m`", `deg m` as the degree of `m`'s top extension, and `Terminal m` as
"`m` is a single prime-degree layer".  The resource `r` is a **parameter**: every hypothesis and
the conclusion speak about that one `r`.

* `hterminal` is the terminal case: a prime-degree layer is solved by the prescribed `r`.  This is
  the shared degree-`p` solver, and stating it against a given `r` rather than letting it produce
  one is what keeps the family statement reachable.
* `hsplit` is the intermediate-field case: a non-terminal member is reduced to finitely many
  members of strictly smaller degree, all over the same `r`.

There is deliberately **no** hypothesis combining resources.  See the section docstring: such a
hypothesis is the amalgamation the all-factor route forbids, and with `r` prescribed it is not
needed — which is the point of stating the descent this way.

Because `r` is fixed, the descent is per member and the family statement is free: for any index
family `f : ι → μ` one gets `∀ i, Solves r (f i)` by applying this at each `f i`, with the single
`r` shared across all of them.  That is the shape `Stacks.EppTheorem.FactorSolutions` asks for.

Proved by strong induction on `deg m`. -/
theorem solves_of_prescribed (r : R)
    (hterminal : ∀ m, Terminal m → Solves r m)
    (hsplit : ∀ m, ¬ Terminal m →
      ∃ t : Finset μ, (∀ m' ∈ t, deg m' < deg m) ∧ ((∀ m' ∈ t, Solves r m') → Solves r m))
    (m : μ) : Solves r m := by
  suffices H : ∀ k : ℕ, ∀ m : μ, deg m ≤ k → Solves r m from H (deg m) m le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hm
    by_cases h : Terminal m
    · exact hterminal m h
    obtain ⟨t, htdeg, htimp⟩ := hsplit m h
    exact htimp fun m' hm' => ih (deg m') (lt_of_lt_of_le (htdeg m' hm') hm) m' le_rfl

/-- The family form of `solves_of_prescribed`: one prescribed resource serves every member of an
arbitrary index family at once.

This is the conclusion shape the all-factor route consumes — `∃ r` outside `∀ i`, with the
existential introduced by whatever constructs `r` and never inside the descent. -/
theorem forall_solves_of_prescribed {ι : Sort*} (r : R) (f : ι → μ)
    (hterminal : ∀ m, Terminal m → Solves r m)
    (hsplit : ∀ m, ¬ Terminal m →
      ∃ t : Finset μ, (∀ m' ∈ t, deg m' < deg m) ∧ ((∀ m' ∈ t, Solves r m') → Solves r m)) :
    ∀ i, Solves r (f i) :=
  fun i => solves_of_prescribed deg Solves Terminal r hterminal hsplit (f i)

end SharedFamily

/-! ### The outer induction: a family whose members split into families

`solves_of_prescribed` recurses one member at a time.  That is enough when a member's reduction
produces members drawn from a lattice fixed in advance, and it is *not* enough for the layer
assembly, where reducing a member produces the conjugate factors of its top layer — objects
generated by the reduction rather than given beforehand.  A path-indexed member type, indexing a
member by the sequence of factor choices made to reach it, would handle this, but it is far more
than is needed.

What is needed instead is to quantify over the **index type**.  A step takes a family
`f : ι → μ` and returns, for each `i`, finitely many members `g i : Fin (m i) → μ`; the new family
is the flattening, indexed by `Σ i, Fin (m i)`.  Since `ι : Type u` and `Fin _ : Type 0`, that
sigma type is again in `Type u`, so the statement is closed under its own step and one universe
suffices. The members are still generated, but they never have to be *named*: they are whatever the
step returned, and the induction only needs their degrees.

**The measure has to be the maximum, not the sum.** Each new member has strictly smaller degree
than the member it came from, but a member may split into many, so the sum of the degrees can
*increase* — degree `3` splitting into ten factors of degree `2` takes the sum from `3` to `20`.
The maximum always drops, because every new degree is `< deg (f i) ≤ max`. Below, the maximum
appears in the induction-friendly form of a uniform bound `k` with `∀ i, deg (f i) ≤ k`, which also
avoids needing any `Finset.sup` machinery inside the proof.

**Mixed families are handled by splitting the index type, and that is not the retracted
amalgamation.** The step is applied to the subtype of non-terminal indices, with terminal members
discharged by `hterminal`. Partitioning an index set is harmless precisely because the resource is
baked into `Solves` rather than chosen per part: there is one resource throughout, so there is
nothing to merge. The retracted `hmerge` combined two *independently chosen* resources, which is a
different operation and the one the route forbids. -/

section FamilyDescent

universe u

variable {μ : Type u} (deg : μ → ℕ) (Solves : μ → Prop)

/-- **The outer induction of the layer assembly: a prescribed resource that solves the terminal
members and survives one family splitting step solves every member of every finite family.**

`Solves` carries the prescribed resource, as in the ring-theoretic instantiations — see the
`LayerDescent` section of `EppSharedFactorSync.lean` for why the resource belongs in the ambient
context rather than ranging over a type.

* `hterminal` is the shared degree-`p` solver: a member of degree at most one is solved by the
  prescribed resource.  Degree-one members are *carried* here, never solved separately.
* `hstep` is one family step: a family all of whose members are non-terminal is replaced by the
  flattened family of their reductions, of strictly smaller degree, and solving all of those solves
  the original family.  It is stated on a family rather than on a member because the ring-theoretic
  step consumes the whole factor family at once.

The conclusion quantifies over every finite index type in `Type u`, which is what makes the step
applicable to its own output. -/
theorem forall_solves_of_family_descent
    (hterminal : ∀ m : μ, deg m ≤ 1 → Solves m)
    (hstep : ∀ (ι : Type u) [Finite ι] (f : ι → μ), (∀ i, 1 < deg (f i)) →
      ∃ (m : ι → ℕ) (g : (i : ι) → Fin (m i) → μ),
        (∀ i j, deg (g i j) < deg (f i)) ∧
        ((∀ i j, Solves (g i j)) → ∀ i, Solves (f i)))
    (ι : Type u) [Finite ι] (f : ι → μ) : ∀ i, Solves (f i) := by
  suffices H : ∀ k : ℕ, ∀ (ι : Type u) [Finite ι] (f : ι → μ),
      (∀ i, deg (f i) ≤ k) → ∀ i, Solves (f i) by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact fun i => (hι.false i).elim
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => deg (f i)
      exact H (deg (f i₀)) ι f hi₀
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ι _ f hf i
    by_cases h1 : deg (f i) ≤ 1
    · exact hterminal _ h1
    obtain ⟨m, g, hdeg, himp⟩ :=
      hstep {i : ι // 1 < deg (f i)} (fun p => f p.1) fun p => p.2
    have hnew : ∀ q : (p : {i : ι // 1 < deg (f i)}) × Fin (m p), deg (g q.1 q.2) ≤ k - 1 := by
      intro q
      have h₁ := hdeg q.1 q.2
      have h₂ := hf q.1.1
      omega
    have hk : 2 ≤ k := by have := hf i; omega
    have hsol := ih (k - 1) (by omega) ((p : {i : ι // 1 < deg (f i)}) × Fin (m p))
      (fun q => g q.1 q.2) hnew
    exact himp (fun p j => hsol ⟨p, j⟩) ⟨i, by omega⟩

end FamilyDescent


/-! ### Epp's exponent bookkeeping -/

/-- The exponent Epp's substitution attaches to a wild index `m` with `ν_m = d`, namely the `n`
in `t ^ (-n)` for `n = m * p ^ (ν + μ - d)`. -/
def eppExponent (p ν μ d m : ℕ) : ℕ := m * p ^ (ν + μ - d)

/-- **Epp's third bullet**: `p ∣ m * p ^ (ν + μ - ν_m)`, since `ν ≥ 1` and `μ ≥ ν_m`. -/
theorem dvd_eppExponent {p ν μ d : ℕ} (hν : 1 ≤ ν) (hd : d ≤ μ) (m : ℕ) :
    p ∣ eppExponent p ν μ d m :=
  (dvd_pow_self p (by omega : ν + μ - d ≠ 0)).mul_left m

/-- **Epp's fourth bullet**: a tame exponent `s` is strictly less than every wild exponent,
because `s < m * p ^ ν` by the choice of `ν`. -/
theorem lt_eppExponent {p ν μ d : ℕ} (hp : 1 ≤ p) (hd : d ≤ μ) {s m : ℕ}
    (hs : s < m * p ^ ν) : s < eppExponent p ν μ d m :=
  lt_of_lt_of_le hs (Nat.mul_le_mul_left m (Nat.pow_le_pow_right hp (by omega)))

/-- **Epp's choice of `ν`**, for a single wild index: there is a `ν ≥ 1` with `s < m * p ^ ν` for
every `s` in a given finite set of tame indices. -/
theorem exists_one_le_forall_lt_mul_pow {p : ℕ} (hp : 1 < p) (I : Finset ℕ) {m : ℕ}
    (hm : 1 ≤ m) : ∃ ν : ℕ, 1 ≤ ν ∧ ∀ s ∈ I, s < m * p ^ ν := by
  refine ⟨I.sup id + 1, Nat.le_add_left 1 _, fun s hs => ?_⟩
  have h1 : s ≤ I.sup id := Finset.le_sup (f := id) hs
  have h2 : I.sup id + 1 < p ^ (I.sup id + 1) := Nat.lt_pow_self hp
  exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left _ hm)

/-- **Epp's choice of `ν`**: `min_{m ∈ J} m * p ^ ν > max_{s ∈ I} s`. -/
theorem exists_one_le_forall_mem_lt {p : ℕ} (hp : 1 < p) (I J : Finset ℕ) (hJ : J.Nonempty)
    (hJ1 : ∀ m ∈ J, 1 ≤ m) : ∃ ν : ℕ, 1 ≤ ν ∧ ∀ m ∈ J, ∀ s ∈ I, s < m * p ^ ν := by
  obtain ⟨ν, hν1, hν⟩ := exists_one_le_forall_lt_mul_pow hp I (hJ1 _ (J.min'_mem hJ))
  exact ⟨ν, hν1, fun m hm s hs =>
    lt_of_lt_of_le (hν s hs) (Nat.mul_le_mul_right _ (J.min'_le m hm))⟩

/-- **The exponent collision of Kuhlmann's Example**: when `m₀ = m₁ * p`, `ν_{m₀} = 1` and
`ν_{m₁} = 0`, the two wild exponents of equation (2) coincide.  This is what defeats Epp's claim
that the most negative exponent has a single coefficient. -/
theorem eppExponent_collision {p ν μ m₁ : ℕ} (h : 1 ≤ ν + μ) :
    eppExponent p ν μ 1 (m₁ * p) = eppExponent p ν μ 0 m₁ := by
  have hsub : ν + μ - 1 + 1 = ν + μ := by omega
  rw [eppExponent, eppExponent, Nat.sub_zero, mul_assoc, ← pow_succ', hsub]

/-- **Kuhlmann's decrease, in its combinatorial form.**  Equation (2) is indexed not by the
original wild indices `m ∈ J` but by the exponents `m * p ^ (ν + μ - ν_m)` they produce.  As soon
as two distinct wild indices produce the same exponent, that index set is strictly smaller —
which is Kuhlmann's "the new set `J` will be smaller than the original set `J`", and hence the
decrease hypothesis of `exists_iterate_good_or_wild_eq_empty`. -/
theorem card_image_lt_card_of_not_injOn {J : Finset ℕ} {f : ℕ → ℕ}
    (h : ¬ Set.InjOn f ↑J) : (J.image f).card < J.card :=
  lt_of_le_of_ne Finset.card_image_le fun he => h (Finset.card_image_iff.mp he)

/-- **The collision of Kuhlmann's Example makes the exponent map non-injective.**

With `m₀ = m₁ * p`, `ν_{m₀} = 1` and `ν_{m₁} = 0`, the two distinct wild indices `m₁` and
`m₁ * p` are sent to the same exponent of equation (2).  Combined with
`card_image_lt_card_of_not_injOn` this is precisely the strict decrease Kuhlmann's correction
relies on. -/
theorem not_injOn_eppExponent {p ν μ m₁ : ℕ} (hp : 1 < p) (hm₁ : 1 ≤ m₁) (hνμ : 1 ≤ ν + μ)
    {d : ℕ → ℕ} (hd₀ : d (m₁ * p) = 1) (hd₁ : d m₁ = 0) {J : Finset ℕ}
    (h₀ : m₁ * p ∈ J) (h₁ : m₁ ∈ J) :
    ¬ Set.InjOn (fun m => eppExponent p ν μ (d m) m) ↑J := by
  intro hinj
  have hval : eppExponent p ν μ (d (m₁ * p)) (m₁ * p) = eppExponent p ν μ (d m₁) m₁ := by
    rw [hd₀, hd₁]; exact eppExponent_collision hνμ
  have := hinj (Finset.mem_coe.mpr h₀) (Finset.mem_coe.mpr h₁) hval
  have hne : m₁ * p ≠ m₁ := by
    have h2 : m₁ * 2 ≤ m₁ * p := Nat.mul_le_mul_left m₁ (show 2 ≤ p from hp)
    omega
  exact hne this

/-! ### Kuhlmann's Example: Epp's assertion is genuinely false -/

section Example

variable {F : Type*} [Field F] {p : ℕ} [ExpChar F p] {c₀ c₁ : F}

/-- In Kuhlmann's Example, `a₋ₘ₁ = c₁ - c₀` is not a `p`-th power. -/
theorem sub_notMem_frobeniusPowRange_one (hc₀ : c₀ ∉ frobeniusPowRange F p 1)
    (hc₁ : c₁ ∈ frobeniusPowRange F p 1) : c₁ - c₀ ∉ frobeniusPowRange F p 1 := fun h =>
  hc₀ (by simpa using sub_mem hc₁ h)

/-- In Kuhlmann's Example, `ν_{m₁} = 0`. -/
theorem frobeniusDepth_sub_eq_zero (hc₀ : c₀ ∉ frobeniusPowRange F p 1)
    (hc₁ : c₁ ∈ frobeniusPowRange F p 1) : frobeniusDepth F p (c₁ - c₀) = 0 := by
  have h := sub_notMem_frobeniusPowRange_one hc₀ hc₁
  exact (frobeniusDepth_eq_zero_iff fun hm => h (perfectCore_le_frobeniusPowRange 1 hm)).mpr h

/-- In Kuhlmann's Example, `a₋ₘ₀ = c₀ ^ p` is not a `p ^ 2`-th power. -/
theorem pow_notMem_frobeniusPowRange_two (hc₀ : c₀ ∉ frobeniusPowRange F p 1) :
    c₀ ^ p ∉ frobeniusPowRange F p 2 := by
  intro h
  obtain ⟨y, hy⟩ := mem_frobeniusPowRange.mp h
  refine hc₀ (mem_frobeniusPowRange.mpr ⟨y, frobenius_inj F p ?_⟩)
  change (y ^ p ^ 1) ^ p = c₀ ^ p
  rw [← pow_mul, ← hy]
  ring

/-- In Kuhlmann's Example, `ν_{m₀} = 1`. -/
theorem frobeniusDepth_pow_eq_one (hc₀ : c₀ ∉ frobeniusPowRange F p 1) :
    frobeniusDepth F p (c₀ ^ p) = 1 := by
  have hcore : c₀ ∉ perfectCore F p := fun hm => hc₀ (perfectCore_le_frobeniusPowRange 1 hm)
  refine (frobeniusDepth_eq_iff (pow_notMem_perfectCore hcore)).mpr ⟨?_, ?_⟩
  · exact mem_frobeniusPowRange.mpr ⟨c₀, by rw [pow_one]⟩
  · exact pow_notMem_frobeniusPowRange_two hc₀

/-- In Kuhlmann's Example, the `p ^ (ν_{m₀})`-th root of `a₋ₘ₀ = c₀ ^ p` is `c₀`. -/
theorem eq_of_pow_eq_pow_self {y : F} (hy : y ^ p ^ frobeniusDepth F p (c₀ ^ p) = c₀ ^ p)
    (hc₀ : c₀ ∉ frobeniusPowRange F p 1) : y = c₀ := by
  rw [frobeniusDepth_pow_eq_one hc₀, pow_one] at hy
  exact frobenius_inj F p (by simpa [frobenius_def] using hy)

/-- **The recombination**: in Kuhlmann's Example the two colliding coefficients of equation (2)
are `c₋ₘ₀ = c₀` and `c₋ₘ₁ = c₁ - c₀`, and their sum is `c₁`, which *is* a `p`-th power.  Epp's
claim that the coefficient of the most negative exponent is not a `p`-th power therefore fails. -/
theorem add_sub_cancel_mem_frobeniusPowRange_one (hc₁ : c₁ ∈ frobeniusPowRange F p 1) :
    c₁ - c₀ + c₀ ∈ frobeniusPowRange F p 1 := by
  rwa [sub_add_cancel]

/-- Kuhlmann's Example is not vacuous: over any field with a non-`p`-th-power, the configuration
`c₀ ∉ F ^ p`, `c₁ ∈ F ^ p` exists, with `c₁ = 0` the case in which the wild set empties out. -/
theorem exists_kuhlmann_example (hc₀ : c₀ ∉ frobeniusPowRange F p 1) :
    ∃ c₁ : F, c₁ ∈ frobeniusPowRange F p 1 ∧
      frobeniusDepth F p (c₁ - c₀) = 0 ∧ frobeniusDepth F p (c₀ ^ p) = 1 ∧
      c₁ - c₀ + c₀ ∈ frobeniusPowRange F p 1 :=
  ⟨0, zero_mem _, frobeniusDepth_sub_eq_zero hc₀ (zero_mem _),
    frobeniusDepth_pow_eq_one hc₀, add_sub_cancel_mem_frobeniusPowRange_one (zero_mem _)⟩

end Example

/-! ### Epp's pole part and its tame/wild splitting -/

/-- The pole part of an Artin–Schreier normal form, together with Epp's splitting of its
exponents into the tame set `I` and the wild set `J`.

`coeff m` is Epp's `a₋ₘ`, the coefficient of `π ^ (-m)`; the tame indices are those whose
coefficient lies in the base residue field `𝔎 = perfectCore F p`, the wild ones those whose
coefficient does not. -/
structure PolePart (F : Type*) [Field F] (p : ℕ) [ExpChar F p] where
  /-- Epp's `a₋ₘ`. -/
  coeff : ℕ → F
  /-- Epp's `I`, the tame exponents. -/
  tame : Finset ℕ
  /-- Epp's `J`, the wild exponents. -/
  wild : Finset ℕ
  /-- `I = {m | a₋ₘ ∈ 𝔎, a₋ₘ ≠ 0}`. -/
  mem_tame_iff : ∀ m, m ∈ tame ↔ 1 ≤ m ∧ coeff m ≠ 0 ∧ coeff m ∈ perfectCore F p
  /-- `J = {m | a₋ₘ ∉ 𝔎, a₋ₘ ≠ 0}`. -/
  mem_wild_iff : ∀ m, m ∈ wild ↔ 1 ≤ m ∧ coeff m ≠ 0 ∧ coeff m ∉ perfectCore F p

namespace PolePart

variable {F : Type*} [Field F] {p : ℕ} [ExpChar F p] (s : PolePart F p)

/-- Kuhlmann's `ν_m` for a wild index `m` of the pole part. -/
noncomputable def depth (m : ℕ) : ℕ := frobeniusDepth F p (s.coeff m)

/-- Epp's `μ = max {ν_m | m ∈ J}`. -/
noncomputable def maxDepth : ℕ := s.wild.sup s.depth

/-- A wild coefficient lies outside the base residue field, so its depth is finite. -/
theorem coeff_notMem_perfectCore {m : ℕ} (hm : m ∈ s.wild) :
    s.coeff m ∉ perfectCore F p := ((s.mem_wild_iff m).mp hm).2.2

/-- Wild indices are positive. -/
theorem one_le_of_mem_wild {m : ℕ} (hm : m ∈ s.wild) : 1 ≤ m := ((s.mem_wild_iff m).mp hm).1

/-- Tame indices are positive. -/
theorem one_le_of_mem_tame {m : ℕ} (hm : m ∈ s.tame) : 1 ≤ m := ((s.mem_tame_iff m).mp hm).1

/-- `ν_m ≤ μ` for every wild index. -/
theorem depth_le_maxDepth {m : ℕ} (hm : m ∈ s.wild) : s.depth m ≤ s.maxDepth :=
  Finset.le_sup hm

/-- Kuhlmann's `a₋ₘ ∈ 𝔏 ^ (p ^ ν_m)`. -/
theorem coeff_mem_frobeniusPowRange_depth {m : ℕ} (hm : m ∈ s.wild) :
    s.coeff m ∈ frobeniusPowRange F p (s.depth m) :=
  mem_frobeniusPowRange_frobeniusDepth (s.coeff_notMem_perfectCore hm)

/-- Kuhlmann's `a₋ₘ ∉ 𝔏 ^ (p ^ (ν_m + 1))`; equivalently, the `p ^ (ν_m)`-th root `c₋ₘ` of
`a₋ₘ` lies in `𝔏 ∖ 𝔏 ^ p`, which is the second bullet of equation (2). -/
theorem coeff_notMem_frobeniusPowRange_depth_succ {m : ℕ} (hm : m ∈ s.wild) :
    s.coeff m ∉ frobeniusPowRange F p (s.depth m + 1) :=
  notMem_frobeniusPowRange_frobeniusDepth_succ (s.coeff_notMem_perfectCore hm)

/-- **Epp's third bullet**, on the pole part: every wild exponent of equation (2) is divisible
by `p`. -/
theorem dvd_exponent {ν : ℕ} (hν : 1 ≤ ν) {m : ℕ} (hm : m ∈ s.wild) :
    p ∣ eppExponent p ν s.maxDepth (s.depth m) m :=
  dvd_eppExponent hν (s.depth_le_maxDepth hm) m

/-- **Epp's fourth bullet**, on the pole part: every tame exponent of equation (2) is strictly
smaller than every wild one. -/
theorem lt_exponent {ν : ℕ} (hp : 1 ≤ p) {m t : ℕ} (hm : m ∈ s.wild)
    (ht : t < m * p ^ ν) : t < eppExponent p ν s.maxDepth (s.depth m) m :=
  lt_eppExponent hp (s.depth_le_maxDepth hm) ht

/-- **Epp's choice of `ν`**, on the pole part: a `ν ≥ 1` for which every tame exponent of
equation (2) is strictly smaller than every wild one. -/
theorem exists_nu (hp : 1 < p) (hJ : s.wild.Nonempty) :
    ∃ ν : ℕ, 1 ≤ ν ∧ ∀ m ∈ s.wild, ∀ t ∈ s.tame,
      t < eppExponent p ν s.maxDepth (s.depth m) m := by
  obtain ⟨ν, hν1, hν⟩ :=
    exists_one_le_forall_mem_lt hp s.tame s.wild hJ fun m hm => s.one_le_of_mem_wild hm
  exact ⟨ν, hν1, fun m hm t ht => s.lt_exponent hp.le hm (hν m hm t ht)⟩

end PolePart

/-! ### The reduced form Epp's substitution aims at -/

/-- Epp's target normal form, and the `Good` predicate of the iteration: the transformed equation
`z ^ p - z = ∑ c m * t ^ (-m)` has a unique most negative exponent `n`, that exponent is
divisible by `p`, and its coefficient is not a `p`-th power.

This is the hypothesis under which Epp proves that `𝔎[[t]] S` is weakly unramified over
`𝔎[[t]]`.  It is **not** proved here that the iteration reaches it; that is the deferred step
`(E10)`, the substitution step, of the decomposition in the module docstring.

(The decomposition
runs `(K1)`–`(K7)` then `(E8)`–`(E13)`.  `(K7)` *is* proved — it is the abstract termination,
`exists_iterate_good_or_wild_eq_empty`, giving "either `Good` holds or `J` is empty".  What is
deferred is the *concrete* instantiation of its abstract `step`, which is `(E10)`.) -/
def IsEppReduced (F : Type*) [Field F] (p : ℕ) [ExpChar F p] (c : ℕ → F) (n : ℕ) : Prop :=
  0 < n ∧ p ∣ n ∧ c n ∉ frobeniusPowRange F p 1 ∧ ∀ m : ℕ, n < m → c m = 0

end Stacks.EppTheorem
