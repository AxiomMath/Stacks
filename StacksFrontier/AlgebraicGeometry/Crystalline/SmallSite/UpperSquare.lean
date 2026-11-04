module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureMorphism

/-!
# The upper square of the diagram of [Stacks, Tag 07IM]

Fix a global crystalline situation `(p, (S, I, γ), X)` with `p` locally nilpotent on the closed
fibre `S₀ = V(I)`, so that `Cris(S₀/S)` is available and `f : X ⟶ S₀` induces the top arrow
`f_cris : (X/S)_cris ⟶ (S₀/S)_cris` of the diagram, [Stacks, Tag 07IK].  This file proves that
the *upper square*

```
(X/S)_cris  --f_cris-->  (S₀/S)_cris
    |                        |
 u_{X/S}                  u_{S₀/S}
    v                        v
 Sh(X_Zar)  --f_small-->  Sh(S₀_Zar)
```

of [Stacks, Tag 07IM] commutes up to an invertible 2-morphism.

The square is a square of morphisms of *topoi*, not of ringed topoi: `u_{X/S}` of
[Stacks, Tag 07IL] is the morphism of topoi of a cocontinuous functor and carries no ring
structure, as in the big crystalline analogue
`Crystalline.GlobalCrystallineSituation.comparisonSquare` of [Stacks, Tag 07IE].  The
2-isomorphism is stated between the direct image functors.

## Main results

* `Crystalline.GlobalCrystallineSituation.closedFiberCrisUpperSquare` — the upper square of
  [Stacks, Tag 07IM] as an invertible 2-morphism of topoi.

## References

* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IE](https://stacks.math.columbia.edu/tag/07IE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StacksZariskiSite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})
  (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
    IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))

/-- **The upper square of the diagram of [Stacks, Tag 07IM].**  For `f : X ⟶ S₀` the structure
morphism of `X` over `S`, the direct image of `u_{S₀/S} ∘ f_cris` is isomorphic to that of
`f_small ∘ u_{X/S}`. -/
@[stacks 07IM "the upper square of the diagram: u_{S₀/S} ∘ f_cris is isomorphic to \
f_small ∘ u_{X/S}, for f : X ⟶ S₀ the structure morphism"]
def closedFiberCrisUpperSquare :
    ((zariskiToposMorphism (closedFiberSituation S hlocnil)).comp
        (closedFiberCrisMorphism S hlocnil)).pushforward ≅
      ((opensMapMorphismOfTopoi S.toClosedFiber.base).comp
        (zariskiToposMorphism S)).pushforward :=
  SmallSite.crisZariskiSquareCoeff S (closedFiberSituation S hlocnil) (𝟙 S.S) S.toClosedFiber
    (closedFiberSituation_comm S hlocnil) (Type (u + 1))

end Crystalline.GlobalCrystallineSituation

end
