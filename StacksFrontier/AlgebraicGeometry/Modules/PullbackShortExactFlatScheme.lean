module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroupPullback
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation

/-!
# Pullback of a short exact sequence with finite locally free quotient

Let `f : X ⟶ Y` be a morphism of schemes and let `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact
sequence of `𝒪_Y`-modules whose final term `ℱ₃` is finite locally free. Then
`0 ⟶ f^*ℱ₁ ⟶ f^*ℱ₂ ⟶ f^*ℱ₃ ⟶ 0` is short exact. This is Stacks 0G6R,
`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFlat`, applied to a finite locally
free quotient, which is flat.

`f` is **not** assumed flat.

## Main results

* `AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree`: the pullback
  along any morphism of a short exact sequence with finite locally free final term is short exact.

## References

* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A short exact sequence of `𝒪_Y`-modules whose final term is finite locally free pulls back
along an *arbitrary* morphism of schemes to a short exact sequence. -/
theorem shortExact_map_pullback_of_finiteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    (s : ShortComplex Y.Modules) (hs : s.ShortExact)
    (h₃ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) s.X₃) :
    (s.map (Scheme.Modules.pullback f)).ShortExact :=
  let := h₃
  shortExact_map_pullback_of_isFlat f s hs (isFlat_of_isFiniteLocallyFree s.X₃)

end AlgebraicGeometry.Scheme.Modules

end
