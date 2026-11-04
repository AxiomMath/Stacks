module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing

/-!
# A multiple of a closed point is an effective Cartier divisor

Let `X` be a locally Noetherian integral scheme and `x` a closed point whose local ring
`𝒪_{X,x}` is a discrete valuation ring. Then the reduced point is an effective Cartier divisor —
items (4) and (5) of [Stacks, Tag 0B8Y] — and so is its `n`-fold multiple `n·x`, by the remark
following [Stacks, Tag 01WT]. This file makes that composition an **instance**, the form in which
the statements of `StacksFrontier/AlgebraicGeometry/Divisors/CanonicalSectionNonvanishing.lean`
take it: `[Stacks.Divisors.IsEffectiveCartierDivisor (vanishingIdeal {x} ^ n)]`.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_pow`: **`n·x` is an effective
  Cartier divisor**, as an instance, for every `n` including `n = 0`.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_canonicalSections_of_isDiscreteValuationRing`:
  the inner claim of [Stacks, Tag 0A27] with the effective-Cartier hypothesis gone, replaced by
  `𝒪_{X,x}` being a discrete valuation ring.

## Implementation notes

The proof is the composition `isEffectiveCartierDivisor_pow` applied to
`isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hx`. Its first factor is
stated at classes on `X` alone rather than at `IsCurve k f`, since `k` and `f` do not occur in the
conclusion and an instance cannot carry them.

**`IsIntegral X` is not decoration.** `IsDiscreteValuationRing (X.presheaf.stalk x)` takes
`IsDomain (X.presheaf.stalk x)` as an instance argument, and the only route to it is Mathlib's
`instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x)`. Without `IsIntegral X` in
scope the *binder* `[IsDiscreteValuationRing (X.presheaf.stalk x)]` fails to elaborate, so this
is a hypothesis of the statement and not of the proof.

**Every `n`, including zero.** `Stacks.Divisors.isEffectiveCartierDivisor_pow` covers `n = 0`,
where `𝓘 ^ 0 = ⊤` is the empty divisor, so the instance is unconditional in `n`. The hypothesis
`0 < n` that the nonvanishing statements carry belongs to `Stacks.Divisors.supportSet_pow` —
at `n = 0` the support is empty and `X_{1_{0·x}}` is all of `X`, not `X ∖ {x}` — and not to
effectivity.

**`IsLocallyNoetherian X` in the last theorem.** The section binder
`s : (invertibleSheaf (vanishingIdeal {x} ^ n)).sections` needs the effective-Cartier instance
when the binder is elaborated, so `IsLocallyNoetherian X` is an instance binder even though
`hc : IsCurve k f` implies it: `LocallyOfFiniteType.isLocallyNoetherian` is a theorem about `f`,
not an instance.

## References

* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Stacks.ProjectiveSpaceSections

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **A multiple of a closed point with a discrete valuation ring at it is an effective Cartier
divisor.**  Items (4) and (5) of [Stacks, Tag 0B8Y] followed by the remark after
[Stacks, Tag 01WT], as an instance, for every `n` — at `n = 0` the divisor is empty. -/
instance isEffectiveCartierDivisor_vanishingIdeal_pow [IsLocallyNoetherian X] [IsIntegral X]
    {x : X} (hx : IsClosed ({x} : Set X))
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (n : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n) :=
  Stacks.Divisors.isEffectiveCartierDivisor_pow
    (isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hx) n

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X : Scheme.{u}} {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}

/-- **The inner claim of [Stacks, Tag 0A27] with no effective-Cartier hypothesis.**  Let `X` be a
proper curve over `k`, locally Noetherian and integral, let `x` be a closed point at which
`𝒪_{X,x}` is a discrete valuation ring, and let `s₀, …, s_m` be global sections of `𝒪_X(n·x)`
whose nonvanishing loci cover `X`, one of which is the canonical section `1_{n·x}`. Then
`X ∖ {x}` is affine.

This is `isAffineOpen_compl_singleton_of_canonicalSections` with its instance binder discharged
by `AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_pow`. -/
theorem isAffineOpen_compl_singleton_of_canonicalSections_of_isDiscreteValuationRing
    [IsLocallyNoetherian X] [IsIntegral X]
    (hf : IsProper f) (hc : IsCurve k f) {x : X} (hx : IsClosed ({x} : Set X))
    {n : ℕ} (hn : 0 < n) [IsDiscreteValuationRing (X.presheaf.stalk x)] {m : ℕ}
    (s : Fin (m + 1) →
      (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)).sections)
    (hs : (⨆ i, nonvanishingChart
        (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
        (s i)) = ⊤)
    (i₀ : Fin (m + 1))
    (h0 : s i₀ = canonicalSections
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
  isAffineOpen_compl_singleton_of_canonicalSections hf hc hx hn s hs i₀ h0

end Stacks.Divisors

end
