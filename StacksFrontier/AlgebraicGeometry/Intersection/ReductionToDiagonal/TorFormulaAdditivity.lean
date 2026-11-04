module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Additivity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct

/-!
# Additivity of the cycle-product side of the Tor formula

The proof of Tag 0B0W compares, for coherent `𝒪_X`-modules `ℱ` and `𝒢` on a nonsingular
variety `X`, the two cycles

`RHS(ℱ, 𝒢) = [ℱ]_r · [𝒢]_s`  and  `LHS(ℱ, 𝒢) = ∑ (-1)^p [Tor_p^{𝒪_X}(ℱ, 𝒢)]_{r + s - dim X}`,

and its first step is that both are additive in either variable along a short exact sequence of
coherent sheaves. This file proves that for the cycle-product side `RHS`: the source's reason is
that `[-]_r` is additive (Chow Homology, Lemma 42.10.4, Tag 02QZ) and that the product of cycles
is bilinear, and both of those are available here.

The statement is proved for the bilinear extension `cycleIntersectionProduct` of an arbitrary
rule `prod` assigning a cycle to a pair of closed subvarieties, so it applies verbatim to the
Tor-formula product of Section 43.14 and hence to the `α · β` of Tag 0B08; that instance is
spelled out as `torFormulaCycleIntersectionProduct_coherentSheafCycle_add_left` and its
right-hand companion.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.coherentSheafCycle_add` — Tag 02QZ as an equality of
  cycles rather than of elements of the cycle group.
* `Stacks.Intersection.ReductionToDiagonal.cycleIntersectionProduct_coherentSheafCycle_add_left`
  and `…_add_right` — `RHS(ℱ₂, 𝒢) = RHS(ℱ₁, 𝒢) + RHS(ℱ₃, 𝒢)` and the variant in the second
  variable, for an arbitrary product of closed subvarieties.
* `torFormulaCycleIntersectionProduct_coherentSheafCycle_add_left` and `…_add_right`, in the
  same namespace — the same for the product of Tag 0B08.

## Implementation notes

The source's hypothesis that the three sheaves of the short exact sequence are supported inside
`Supp ℱ` enters, as everywhere in this library, as the three delta-dimension bounds that
`Stacks.Chow.coherentSheafCycle` needs in order to form a `k`-cycle at all; the support
condition is what supplies them in the source, and they are the hypotheses `h₁`, `h₂`, `h₃`
here.

Bilinearity of `cycleIntersectionProduct` needs each cycle to have finitely many components.
That is automatic on a quasi-compact scheme, in particular on a variety, by
`AlgebraicGeometry.TorFormula.finite_support_of_compactSpace`, so `X` is assumed compact rather
than the finiteness being carried as three further hypotheses.

The other half of the source's step, additivity of `LHS` along the long exact sequence of `Tor`
sheaves, is not proved here but elsewhere: it is
`Stacks.Intersection.ReductionToDiagonal.intersectionProductCycle_add_left` in
`StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorSideAdditivity`, resting on
the long exact sequence of `Tor` sheaves of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorLongExactSequence`.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Lemma 42.10.4 (Tag 02QZ)](https://stacks.math.columbia.edu/tag/02QZ)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

variable {X : Scheme.{u}}

/-- **Stacks 02QZ, as an equality of cycles.** The cycle of a coherent sheaf is additive along a
short exact sequence of coherent sheaves whose supports all have delta-dimension at most `k`.
This is `Stacks.Chow.cycleAssociatedToCoherentSheaf_add` read in `AlgebraicCycle X ℤ` instead of
in the group of `k`-cycles. -/
theorem coherentSheafCycle_add (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent] (k : ℤ)
    (h₁ : schemeDeltaDimension C ((reducedSupport E.X₁).subschemeι ≫ f) ≤ (k : EInt))
    (h₂ : schemeDeltaDimension C ((reducedSupport E.X₂).subschemeι ≫ f) ≤ (k : EInt))
    (h₃ : schemeDeltaDimension C ((reducedSupport E.X₃).subschemeι ≫ f) ≤ (k : EInt)) :
    coherentSheafCycle C f E.X₂ k h₂ =
      coherentSheafCycle C f E.X₁ k h₁ + coherentSheafCycle C f E.X₃ k h₃ :=
  congrArg Subtype.val (cycleAssociatedToCoherentSheaf_add C f E hE k h₁ h₂ h₃)

/-- **The first additivity of the proof of Stacks 0B0W, in the first variable.** For a short
exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of coherent sheaves whose supports all have
delta-dimension at most `r`, and any cycle `β`,

`[ℱ₂]_r · β = [ℱ₁]_r · β + [ℱ₃]_r · β`.

The source's reason is exactly this: additivity of `[-]_r` (Tag 02QZ) together with bilinearity
of the product of cycles. -/
theorem cycleIntersectionProduct_coherentSheafCycle_add_left [CompactSpace X]
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (prod : X → X → AlgebraicCycle X ℤ)
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent] (r : ℤ)
    (h₁ : schemeDeltaDimension C ((reducedSupport E.X₁).subschemeι ≫ f) ≤ (r : EInt))
    (h₂ : schemeDeltaDimension C ((reducedSupport E.X₂).subschemeι ≫ f) ≤ (r : EInt))
    (h₃ : schemeDeltaDimension C ((reducedSupport E.X₃).subschemeι ≫ f) ≤ (r : EInt))
    (β : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod (coherentSheafCycle C f E.X₂ r h₂) β =
      cycleIntersectionProduct prod (coherentSheafCycle C f E.X₁ r h₁) β +
        cycleIntersectionProduct prod (coherentSheafCycle C f E.X₃ r h₃) β := by
  rw [coherentSheafCycle_add C f E hE r h₁ h₂ h₃]
  exact cycleIntersectionProduct_add_left prod (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _) (finite_support_of_compactSpace _)

/-- **The first additivity of the proof of Stacks 0B0W, in the second variable.** For a short
exact sequence `0 → 𝒢₁ → 𝒢₂ → 𝒢₃ → 0` of coherent sheaves whose supports all have
delta-dimension at most `s`, and any cycle `α`,

`α · [𝒢₂]_s = α · [𝒢₁]_s + α · [𝒢₃]_s`. -/
theorem cycleIntersectionProduct_coherentSheafCycle_add_right [CompactSpace X]
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (prod : X → X → AlgebraicCycle X ℤ)
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent] (s : ℤ)
    (h₁ : schemeDeltaDimension C ((reducedSupport E.X₁).subschemeι ≫ f) ≤ (s : EInt))
    (h₂ : schemeDeltaDimension C ((reducedSupport E.X₂).subschemeι ≫ f) ≤ (s : EInt))
    (h₃ : schemeDeltaDimension C ((reducedSupport E.X₃).subschemeι ≫ f) ≤ (s : EInt))
    (α : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod α (coherentSheafCycle C f E.X₂ s h₂) =
      cycleIntersectionProduct prod α (coherentSheafCycle C f E.X₁ s h₁) +
        cycleIntersectionProduct prod α (coherentSheafCycle C f E.X₃ s h₃) := by
  rw [coherentSheafCycle_add C f E hE s h₁ h₂ h₃]
  exact cycleIntersectionProduct_add_right prod (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _) (finite_support_of_compactSpace _)

/-- **Additivity of `[ℱ]_r · β` for the product of Stacks 0B08**, the instance of
`cycleIntersectionProduct_coherentSheafCycle_add_left` at the Tor-formula product of
Section 43.14. -/
theorem torFormulaCycleIntersectionProduct_coherentSheafCycle_add_left [CompactSpace X]
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (n : ℤ)
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent] (r : ℤ)
    (h₁ : schemeDeltaDimension C ((reducedSupport E.X₁).subschemeι ≫ f) ≤ (r : EInt))
    (h₂ : schemeDeltaDimension C ((reducedSupport E.X₂).subschemeι ≫ f) ≤ (r : EInt))
    (h₃ : schemeDeltaDimension C ((reducedSupport E.X₃).subschemeι ≫ f) ≤ (r : EInt))
    (β : AlgebraicCycle X ℤ) :
    torFormulaCycleIntersectionProduct C f hX n (coherentSheafCycle C f E.X₂ r h₂) β =
      torFormulaCycleIntersectionProduct C f hX n (coherentSheafCycle C f E.X₁ r h₁) β +
        torFormulaCycleIntersectionProduct C f hX n (coherentSheafCycle C f E.X₃ r h₃) β :=
  cycleIntersectionProduct_coherentSheafCycle_add_left C f _ E hE r h₁ h₂ h₃ β

/-- **Additivity of `α · [𝒢]_s` for the product of Stacks 0B08**, the instance of
`cycleIntersectionProduct_coherentSheafCycle_add_right` at the Tor-formula product of
Section 43.14. -/
theorem torFormulaCycleIntersectionProduct_coherentSheafCycle_add_right [CompactSpace X]
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (n : ℤ)
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent] (s : ℤ)
    (h₁ : schemeDeltaDimension C ((reducedSupport E.X₁).subschemeι ≫ f) ≤ (s : EInt))
    (h₂ : schemeDeltaDimension C ((reducedSupport E.X₂).subschemeι ≫ f) ≤ (s : EInt))
    (h₃ : schemeDeltaDimension C ((reducedSupport E.X₃).subschemeι ≫ f) ≤ (s : EInt))
    (α : AlgebraicCycle X ℤ) :
    torFormulaCycleIntersectionProduct C f hX n α (coherentSheafCycle C f E.X₂ s h₂) =
      torFormulaCycleIntersectionProduct C f hX n α (coherentSheafCycle C f E.X₁ s h₁) +
        torFormulaCycleIntersectionProduct C f hX n α (coherentSheafCycle C f E.X₃ s h₃) :=
  cycleIntersectionProduct_coherentSheafCycle_add_right C f _ E hE s h₁ h₂ h₃ α

end Stacks.Intersection.ReductionToDiagonal

end
