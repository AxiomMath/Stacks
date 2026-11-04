module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct

/-!
# Perfectness of the convolution kernel over a Noetherian base

Let `f : X ⟶ S`, `g : Y ⟶ S`, `h : Z ⟶ S`. If `X ×_S Z` is Noetherian and the middle morphism
`g` is flat, proper and of finite presentation, then the convolution
`R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*M)` of [Stacks, Tag 0FYS] of a perfect `K` on
`X ×_S Y` and a perfect `M` on `Y ×_S Z` is perfect on `X ×_S Z`: `pr_{13}` is a base change of
`g`, hence a perfect proper morphism, and [Stacks, Tag 0B6G] applies.

## Main results

* `AlgebraicGeometry.isPerfect_fourierMukaiConvolution_of_isNoetherian` — the convolution of two
  perfect kernels is perfect when `X ×_S Z` is Noetherian and `g` is flat, proper and of finite
  presentation.

## Implementation notes

This is the Noetherian case of the perfectness clause (3) of the category of
[Stacks, Tag 0G0F], whose source reference is [Stacks, Tag 0B91]. The general case is not proved
here and no `@[stacks 0G0F]` attribute is attached.

## References

* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Perfect

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- **`pr_{13}` is a base change of the middle morphism `g`**, so it inherits every property of
morphisms stable under base change. -/
theorem fourierMukaiPr13_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hg : P g) : P (fourierMukaiPr13 f g h) := by
  have hfst : P (pullback.fst f g) := P.of_isPullback (IsPullback.of_hasPullback f g).flip hg
  exact P.of_isPullback (isPullback_fourierMukaiPr12_fourierMukaiPr13 f g h) hfst

/-- The derived tensor product of two perfect complexes on a scheme is perfect, [Stacks, Tag 09J5],
in the spelling `AlgebraicGeometry.dtenR` that the convolution kernel is built with. -/
theorem isPerfect_dtenR {W : Scheme.{u}} (A B : DerivedCategory W.Modules)
    (hA : IsPerfect (X := W.toRingedSpace) A) (hB : IsPerfect (X := W.toRingedSpace) B) :
    IsPerfect (X := W.toRingedSpace) ((dtenR W B).obj A) :=
  RingedSpace.isPerfect_canonicalDerivedTensorProduct _ A B hA hB

/-- **[Stacks, Tag 0B6G]** in the spelling `AlgebraicGeometry.dpush` of the derived direct image
that the convolution kernel is built with: for `p : V ⟶ W` flat, of finite presentation (hence
perfect) and proper, with `W` Noetherian, the derived direct image of a perfect complex is
perfect. -/
theorem isPerfect_dpush_of_perfect_of_isProper {V W : Scheme.{u}} (p : V ⟶ W) [IsNoetherian W]
    [Flat p] [LocallyOfFinitePresentation p] [IsProper p] (E : DerivedCategory V.Modules)
    (hE : IsPerfect (X := V.toRingedSpace) E) :
    IsPerfect (X := W.toRingedSpace) ((dpush p).obj E) :=
  Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect p E hE

/-- **The convolution of two perfect kernels is perfect over a Noetherian base.** If
`X ×_S Z` is Noetherian and `g : Y ⟶ S` is flat, proper and of finite presentation, then for
perfect `K` on `X ×_S Y` and `M` on `Y ×_S Z` the convolution
`R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*M)` of [Stacks, Tag 0FYS] is perfect on `X ×_S Z`.

The two pullbacks are perfect by [Stacks, Tag 09UA], their derived tensor product by
[Stacks, Tag 09J5], and `pr_{13}`, a base change of `g`, is flat of finite presentation (hence
perfect) and proper, so [Stacks, Tag 0B6G] applies. -/
theorem isPerfect_fourierMukaiConvolution_of_isNoetherian [IsNoetherian (pullback f h)]
    [Flat g] [IsProper g] [LocallyOfFinitePresentation g]
    {K : DerivedCategory (pullback f g).Modules}
    (hK : IsPerfect (X := (pullback f g).toRingedSpace) K)
    {M : DerivedCategory (pullback g h).Modules}
    (hM : IsPerfect (X := (pullback g h).toRingedSpace) M) :
    IsPerfect (X := (pullback f h).toRingedSpace) (fourierMukaiConvolution f g h K M) := by
  have i1 : Flat (fourierMukaiPr13 f g h) :=
    fourierMukaiPr13_of_isPullback f g h @Flat inferInstance
  have i2 : IsProper (fourierMukaiPr13 f g h) :=
    fourierMukaiPr13_of_isPullback f g h @IsProper inferInstance
  have i3 : LocallyOfFinitePresentation (fourierMukaiPr13 f g h) :=
    fourierMukaiPr13_of_isPullback f g h @LocallyOfFinitePresentation inferInstance
  exact isPerfect_dpush_of_perfect_of_isProper (fourierMukaiPr13 f g h) _
    (isPerfect_dtenR _ _ (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K hK)
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ M hM))

end Perfect

end AlgebraicGeometry

end
