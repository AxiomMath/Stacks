module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenVersalityFlatInterface
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelCompatibleKCb

/-!
# Openness of versality for `Coh_{X/B}` with `X → B` flat, from the ideal maps

In Situation Stacks 08KB assume that `S` is locally Noetherian, `S = B` (so that `Y` is final)
and `f : X → B` is flat. Of the two remaining inputs of the second proof of Stacks 08WA (see
`isOpenVersality_coherentCFG_of_isFlat_of_tangentLiftDifferencePullback`), the naturality of the
difference from the trivial lift along `Spec A[N] ⟶ Spec A[M]` holds
(`tangentLiftDifferencePullback_of_testRelativeIdealSquareCompatible`), so openness of versality
follows from the ideal-square compatibility of `relativeSquareIdealMap` alone.

## Main results

* `isOpenVersality_coherentCFG_of_isFlat_of_relativeIdealSquareCompatibleOfIdealMaps`: if `X → B`
  is flat and `relativeSquareIdealMap` is ideal-square compatible, then `Coh_{X/B}` satisfies
  openness of versality.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **Openness of versality for `Coh_{X/B}` with `X → B` flat** (Stacks 08WA, through Stacks
0CYF): if `S` is locally Noetherian, `Y` is final, `f : X → B` is flat, and `λ` is ideal-square
compatible for all affine first order thickenings from their ideal maps, then `Coh_{X/B}`
satisfies openness of versality. -/
theorem isOpenVersality_coherentCFG_of_isFlat_of_relativeIdealSquareCompatibleOfIdealMaps
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] (hY : IsTerminal D.Y)
    (hflat : IsFlat B S hS D.f.hom) (H : RelativeIdealSquareCompatibleOfIdealMaps D) :
    HasOpenVersality ((coherentCFG D).val.p ⋙ Over.post B.inclusion) :=
  D.isOpenVersality_coherentCFG_of_isFlat_of_tangentLiftDifferencePullback hY hflat H
    (fun _ _ _ _ _ hx _ _ _ f _ hH =>
      tangentLiftDifferencePullback_of_testRelativeIdealSquareCompatible hY hx hflat f hH)

end AlgebraicGeometry.Space.CoherentSituation

end
