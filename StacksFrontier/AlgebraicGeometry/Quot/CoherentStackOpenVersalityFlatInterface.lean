module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackTestRelativeIdealSquare

/-!
# Openness of versality for `Coh_{X/B}` with `X → B` flat

Let `S` be locally Noetherian, `S = B` (so that `Y` is final) and `f : X → B` flat. This file
proves openness of versality for `𝒳 = Coh_{X/B}`, taking two inputs as hypotheses:

* the ideal-square compatibility of
  `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` from the ideal maps for all
  affine first order thickenings
  (`AlgebraicGeometry.Space.CoherentSituation.RelativeIdealSquareCompatibleOfIdealMaps`);
* the naturality of the difference from the trivial lift along `Spec A[N] ⟶ Spec A[M]`
  (`AlgebraicGeometry.Space.CoherentSituation.TangentLiftDifferencePullback`) for a surjection
  `M ⟶ N` of modules, given the ideal-square compatibility at `Spec A[N] ⟶ Spec A[M]`.

## Main results

* `CoherentSituation.isOpenVersality_coherentCFG_of_isFlat_of_tangentLiftDifferencePullback`:
  given these two inputs, `Coh_{X/B}` satisfies openness of versality.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **Openness of versality for `Coh_{X/B}` with `X → B` flat**, given as hypotheses the
ideal-square compatibility of `λ` from the ideal maps for all affine first order thickenings, and
the naturality of the difference from the trivial lift along `Spec A[N] ⟶ Spec A[M]` for every
surjection `M ⟶ N` of modules over a chart, the latter given the ideal-square compatibility at
`Spec A[N] ⟶ Spec A[M]`. -/
theorem isOpenVersality_coherentCFG_of_isFlat_of_tangentLiftDifferencePullback
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] (hY : IsTerminal D.Y)
    (hflat : IsFlat B S hS D.f.hom) (H : RelativeIdealSquareCompatibleOfIdealMaps D)
    (hdiff : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
      {M N : SiteModule A B} (f : M ⟶ N), Function.Surjective f.hom →
      D.TestRelativeIdealSquareCompatible hY hflat hx
        (squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS) (hA := hA) f) →
      TangentLiftDifferencePullback hY hx hflat f) :
    HasOpenVersality ((coherentCFG D).val.p ⋙ Over.post B.inclusion) :=
  isOpenVersality_coherentCFG_of_isFlat_of_idealMaps hY hflat H
    (fun A _ toS hA x hx _ _ _ f hf hH t =>
      chartTangentEquiv_map_of_tangentLiftDifferencePullback hY hx hflat
        D.satisfiesRSStar_coherentCFG f (hdiff A toS hA x hx f hf hH) t)

end AlgebraicGeometry.Space.CoherentSituation

end
