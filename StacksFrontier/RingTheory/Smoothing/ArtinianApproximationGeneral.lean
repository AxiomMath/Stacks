module

public import StacksFrontier.RingTheory.Smoothing.PositiveCharacteristicResolution

/-!
# Stacks 07FT in full generality

Stacks 07FT: let `k` be a field of characteristic `p > 0`, let `Λ` be a Noetherian geometrically
regular `k`-algebra, let `𝔮` be a prime of `Λ`, let `n ≥ 1` and let `E` be a finite subset of
`Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮`. Then there are `m ≥ 0` and a `k`-algebra map `φ : k[y_1, …, y_m] → Λ` such
that, with `𝔭 = φ^{-1}(𝔮)`, the induced local map `k[y_1, …, y_m]_𝔭 → Λ_𝔮` is flat with
`𝔭Λ_𝔮 = 𝔮Λ_𝔮`, and the induced map `k[y_1, …, y_m]_𝔭/𝔭^n → Λ̄` factors through a local Artinian
subring `D ⊇ E` of `Λ̄` by an essentially smooth map followed by a flat one.

This file does nothing but transport
`Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem_of_charP` — the three
clauses of Stacks 07FH in the generality of that tag, proved in
`StacksFrontier/RingTheory/Smoothing/InseparableResidueField.lean` — into the predicate
`Stacks.Smoothing.HasArtinianApproximationData` in which the proof of Stacks 07FJ carries 07FT as
a hypothesis.

The gap that made 07FT conditional in this repository was the λ-choice of the proof of Stacks
07FH, which the source asserts without argument and which is false for a general member of the
directed family of Stacks 07FG. **The repair is due to Brian Nugent**; it is described in the
module docstring of `StacksFrontier/RingTheory/Smoothing/InseparableResidueField.lean` and
implemented in `Stacks.Smoothing.exists_global_stage_primePowerQuotient`.

## Main results

* `Stacks.Smoothing.artinianApproximationDataAt_of_charP`: the conclusion of Stacks 07FT at one
  `(k, Λ, 𝔮, n, E)`, with no hypothesis on `κ(𝔮)`.
* `Stacks.Smoothing.hasArtinianApproximationData`: Stacks 07FT in full generality — the
  predicate `Stacks.Smoothing.HasArtinianApproximationData`, proved.

## References

* [Stacks Project, Tag 07FT](https://stacks.math.columbia.edu/tag/07FT)
* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.Smoothing

universe u

/-- **The conclusion of Stacks 07FT at one `(k, Λ, 𝔮, n, E)`, unconditionally.** The hypothesis
`Algebra.EssFiniteType k κ(𝔮)` of `Stacks.Smoothing.artinianApproximationDataAt_of_essFiniteType`
is removed: clauses (2) and (3) of Stacks 07FH are available in the generality of that tag, by
Brian Nugent's repair of its λ-choice.

The acceptance of
`Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem_of_charP` here is the check
that `Stacks.Smoothing.ArtinianApproximationDataAt` is that theorem's conclusion verbatim. -/
theorem artinianApproximationDataAt_of_charP (k Λ : Type u) [Field k] [CommRing Λ]
    [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ)
    [𝔮.IsPrime] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ} (hn : 1 ≤ n)
    (E : Finset (primePowerQuotient 𝔮 n)) : ArtinianApproximationDataAt k Λ 𝔮 n E :=
  exists_mvPolynomial_localArtinianFactorization_mem_of_charP 𝔮 p hn E

/-- **Stacks 07FT in full generality**, the predicate
`Stacks.Smoothing.HasArtinianApproximationData` proved: for every field `k` of characteristic
`p > 0`, every Noetherian geometrically regular `k`-algebra `Λ`, every prime `𝔮` of `Λ`, every
`n ≥ 1` and every finite subset `E` of `Λ_𝔮/𝔮^nΛ_𝔮`, the Artinian approximation data exist.

This was item (9) of the proof of Stacks 07FJ, carried as a hypothesis there and in
`Stacks.Smoothing.TwistedQuotientResolution`. The λ-choice of Stacks 07FH, on which it turns, is
not justified by the source's text; **the repair implemented here is due to Brian Nugent**. -/
@[stacks 07FT "The lemma in full generality: for every field k of characteristic p > 0, every
Noetherian geometrically regular k-algebra Λ, every prime 𝔮 of Λ, every n ≥ 1 and every finite
subset E of Λ_𝔮/𝔮^nΛ_𝔮, there are m and a k-algebra map φ : k[y_1, …, y_m] → Λ such that, with
𝔭 = φ⁻¹(𝔮), the induced local map k[y]_𝔭 → Λ_𝔮 is flat with 𝔭Λ_𝔮 = 𝔮Λ_𝔮, and the induced map
k[y]_𝔭/𝔭^n → Λ_𝔮/𝔮^nΛ_𝔮 factors through a local Artinian subring D containing E by an
essentially smooth map followed by a flat one. The three clauses of Stacks 07FH that this
consumes are proved in
`Stacks.Smoothing.exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat_of_charP`; the
λ-choice of the source's proof of 07FH is not justified by its text and is false for a general
member of the directed family of 07FG, and the repair is due to Brian Nugent."]
theorem hasArtinianApproximationData : HasArtinianApproximationData.{u} := by
  intro k Λ _ _ _ _ _ 𝔮 _ p _ _ n hn E
  exact artinianApproximationDataAt_of_charP k Λ 𝔮 p hn E

end Stacks.Smoothing
