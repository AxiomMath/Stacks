module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.FinitePushforwardInputs

/-!
# Property (0EZ7) for the fppf–étale comparison situation

Let `B` be a big fppf site and `(Sch/S)_étale` the étale site on the same category of schemes.
This file proves property (0EZ7) of Situation 0EZ3 for the data of Stacks 0F0H: for a finite
morphism `f : X ⟶ Y` the higher direct images `R^if_*` of the relocalization carry `𝒜'_X` into
`𝒜'_Y`. As in the source (Stacks 0DDJ (4)), `f_*` is exact for `f` finite, so `R^if_*` vanishes
for `i > 0`, and `f_*π_X⁻¹F = π_Y⁻¹f_{small,*}F` in degree zero.

## Main results

* `AlgebraicGeometry.fppfEtaleWeakSerre_rightDerived_of_finite`: property (0EZ7).

## References

* [Stacks Project, Tag 0F0H](https://stacks.math.columbia.edu/tag/0F0H)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}}

/-- **Property (0EZ7) of Situation 0EZ3 in Stacks 0F0H.** For a finite morphism `f : X ⟶ Y` and
`F` in `𝒜'_X`, every higher direct image `R^if_*F` of the relocalization lies in `𝒜'_Y`
(Stacks 0DDJ (4)). -/
theorem fppfEtaleWeakSerre_rightDerived_of_finite ⦃X Y : B.Schemes⦄ (f : X ⟶ Y)
    (hf : fppfEtaleFinite B f)
    (F : Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1})
    (hF : fppfEtaleWeakSerre B X F) (i : ℕ) :
    fppfEtaleWeakSerre B Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).rightDerived i).obj F) :=
  have := fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite f hf
  fppfEtaleWeakSerre_rightDerived_of_exact f
    (fppfEtaleWeakSerre_overMapPushforward_of_finite f hf) F hF i

end AlgebraicGeometry
