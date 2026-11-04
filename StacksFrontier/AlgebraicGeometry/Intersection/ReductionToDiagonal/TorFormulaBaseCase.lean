module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct

/-!
# The Tor formula on two closed subvarieties

The dévissage in the proof of Tag 0B0W reduces the Tor formula

`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dim X}`

to the case `ℱ = 𝒪_V`, `𝒢 = 𝒪_W` of the structure sheaves of two closed subvarieties, and the
source then says of the case `dim V = r`, `dim W = s` that "this equality is the definition of
`V · W`". This file proves that case against this library's definition of `V · W`, which is
indeed the Tor formula (`AlgebraicGeometry.TorFormula.intersectionProductCycle`, Tag 0AZR).

The content is not the Tor formula itself but the two identifications the source leaves
implicit: that `[𝒪_V]_r` is the prime cycle `[V]`, so that the bilinear extension of Tag 0B08
has a single contributing summand; and that the single summand it leaves is the alternating sum
of Tag 0AZR at that pair of points, which is where the delta-dimension bound enters.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.coherentSheafCycle_structureSheafAt` — `[𝒪_V]_r` is
  the prime cycle of the generic point of `V`, for `V` the reduced closure of a point of
  delta-dimension `r`.
* `Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_structureSheafAt` —
  the Tor formula on two closed subvarieties of delta-dimensions `r` and `s`.

## Implementation notes

Closed subvarieties are their generic points throughout, as cycles are: `V` is
`Stacks.Chow.integralComponentAt x`, the reduced induced structure on the closure of `x`, and
`𝒪_V` is `AlgebraicGeometry.TorFormula.structureSheafAt x`, its structure sheaf pushed forward
to `X`. Phrasing the statement at the point rather than at a chosen integral closed subscheme
is what lets it be applied directly to a pair of components of two cycles, and it loses
nothing: every integral closed subscheme is the reduced closure of its own generic point
(`Stacks.Chow.integralComponentAt_genericPointOf`).

The hypothesis is that the delta-dimension of `V` is exactly `r`, not at most `r`. That is what
the source's `dim V = r` says, and it is what makes the cycle the prime cycle rather than zero;
the complementary case `dim V < r`, where `[𝒪_V]_r = 0` and the alternating sum has to be shown
to vanish, is the hard half of the dévissage and is treated elsewhere, in
`StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaDeficient`.

The delta-dimension bounds that `Stacks.Chow.coherentSheafCycle` and
`AlgebraicGeometry.TorFormula.intersectionProductCycle` take as arguments are propositions, so
proof irrelevance makes the value independent of which proof is supplied; the statements below
therefore quantify over them rather than fixing the ones derived here.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

variable {X : Scheme.{u}}

/-- **`[𝒪_V]_r = [V]`.** For `V` the reduced closure of a point `x` of delta-dimension `r`, the
cycle of the structure sheaf of `V` is the prime cycle of `x` with coefficient one.

This is Tag 02QY, which identifies `[𝒪_V]_r` with the fundamental cycle `[V]_r`, followed by
Tag 02QU, which computes the fundamental cycle of an integral closed subscheme of
delta-dimension `r` as that prime cycle. -/
theorem coherentSheafCycle_structureSheafAt [DecidableEq X] (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (x : X) (r : ℤ)
    (hx : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ f) = (r : EInt))
    (hb : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      schemeDeltaDimension C ((reducedSupport (structureSheafAt x)).subschemeι ≫ f)
        ≤ (r : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    coherentSheafCycle C f (structureSheafAt x) r hb =
      Function.locallyFinsuppWithin.single x 1 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hint : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hgen : genericPointOf (integralComponentAt x) hint = x :=
    genericPointOf_integralComponentAt x
  -- `[𝒪_V]_r` is the fundamental cycle `[V]_r`, by Tag 02QY.
  have h02QY := cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C f
    (integralComponentAt x).subschemeι r (le_of_eq hx)
  apply Function.locallyFinsuppWithin.ext
  intro z
  have hval : coherentSheafCycle C f (structureSheafAt x) r hb z =
      (cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι r).1 z := by
    rw [h02QY]; rfl
  rw [hval]
  rcases eq_or_ne z x with heq | hz
  · -- At the generic point both coefficients are one, by Tag 02QU.
    have h1 := cycleAssociatedToClosedSubscheme_integral_apply C f (integralComponentAt x) hint hx
    rw [hgen] at h1
    rw [heq, h1]
    simp [Function.locallyFinsuppWithin.single_apply]
  · -- Away from it the fundamental cycle of an integral closed subscheme vanishes.
    have h0 := cycleAssociatedToClosedSubscheme_integral_apply_of_ne C f
      (integralComponentAt x) hint r
      (show z ≠ genericPointOf (integralComponentAt x) hint by rw [hgen]; exact hz)
    rw [h0]
    simp [Function.locallyFinsuppWithin.single_apply, hz]

/-- **The Tor formula on two closed subvarieties of the expected dimensions, the easy case of the
dévissage of Stacks 0B0W.** Let `V` and `W` be the reduced closures of two points `x` and `y` of
a regular scheme, of delta-dimensions exactly `r` and `s`, and suppose the `Tor` sheaves of their
structure sheaves have supports of delta-dimension at most `n`. Then

`[𝒪_V]_r · [𝒪_W]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(𝒪_V, 𝒪_W)]_n`.

This is the case the source disposes of by saying "this equality is the definition of `V · W`":
both sides are the alternating sum of Tag 0AZR, the left after the bilinear extension of Tag
0B08 has been evaluated at the one pair of components that contributes. -/
theorem torFormulaCycleIntersectionProduct_structureSheafAt [DecidableEq X]
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (x y : X) (r s n : ℤ)
    (hx : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ f) = (r : EInt))
    (hy : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ f) = (s : EInt))
    (hbd : TorSupportBound C f hX n x y)
    (hbx : schemeDeltaDimension C ((reducedSupport (structureSheafAt x)).subschemeι ≫ f)
      ≤ (r : EInt))
    (hby : schemeDeltaDimension C ((reducedSupport (structureSheafAt y)).subschemeι ≫ f)
      ≤ (s : EInt)) :
    torFormulaCycleIntersectionProduct C f hX n
        (coherentSheafCycle C f (structureSheafAt x) r hbx)
        (coherentSheafCycle C f (structureSheafAt y) s hby) =
      intersectionProductCycle C f hX (structureSheafAt x) (structureSheafAt y)
        (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) n hbd := by
  rw [torFormulaCycleIntersectionProduct,
    coherentSheafCycle_structureSheafAt C f x r hx hbx,
    coherentSheafCycle_structureSheafAt C f y s hy hby,
    cycleIntersectionProduct_single_single, one_mul, one_smul,
    torFormulaSubvarietyProductTotal_eq_of_bound C f hX n hbd]
  rfl

end Stacks.Intersection.ReductionToDiagonal

end
