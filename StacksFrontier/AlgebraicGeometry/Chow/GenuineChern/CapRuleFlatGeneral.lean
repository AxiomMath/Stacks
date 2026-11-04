module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat

/-!
# The Chern class cap products commute with flat pullback, with no factorization hypothesis

`Stacks.Chow.GenuineChern.chernCap_flatPullback_heq` states [Stacks, Tag 02U8] for the cap
products of [Stacks, Tag 02U6] with the factorization of flat pullback through rational
equivalence, in the two degrees involved, taken as hypotheses. That factorization holds in every
degree (`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`), so the identity
holds with no hypothesis beyond the source's: this is the statement here.

## Main results

* `Stacks.Chow.GenuineChern.chernCap_flatPullback_heq_general` — Stacks 02U8 for the cap
  products, for a flat morphism over a base and a module identified with a pullback.

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- **Stacks 02U8 for the cap products of Stacks 02U6, in every rank.** For `f : Y ⟶ X` flat of
relative dimension `d` over the base, `ℰ` of rank `r` on `X` and `ℰ' ≅ f^*ℰ`,

  `c_j(ℰ') ∩ f^*α = f^*(c_j(ℰ) ∩ α)`,

as a heterogeneous equality: the two sides lie in `A_{(k+d)-j}(Y)` and `A_{(k-j)+d}(Y)`. The flat
pullbacks are those of `Stacks.Chow.flatPullbackChow`, through the factorization through rational
equivalence that holds in every degree. -/
@[stacks 02U8 "Stated for a module on Y identified with the pullback of E, as a heterogeneous \
equality between the Chow groups of the two equal degrees (k + d) - j and (k - j) + d."]
theorem chernCap_flatPullback_heq_general {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback f).obj E) (k : ℤ) (j : Fin (r + 1))
    (α : chowGroup C sX k) :
    chernCap C r sY E' (k + d) j (flatPullbackChow C sY sX f hf d hd k
        (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd k) α) ≍
      flatPullbackChow C sY sX f hf d hd (k - (j : ℤ))
        (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd _)
        (chernCap C r sX E k j α) :=
  chernCap_flatPullback_heq C sX sY f hf d hd E r E' eE k j
    (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd k)
    (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd _) α

end Stacks.Chow.GenuineChern

end
