module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorGenerator
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# The normed ratio of two elementary tensors of generators

Let `f : X ⟶ Y` be a morphism of schemes carrying a norm `N` of degree `d` on functions
(`Stacks.Norm.MorphismNorm`, Tag 0BD1), let `L` and `M` be `𝒪_X`-modules, and let `V` be an
open of `Y` over which both are trivialized upstairs, by generators `s, s'` of `L` and `t, t'` of
`M` on `f⁻¹V`. The normed transition unit of the two elementary tensors `s ⊗ t` and `s' ⊗ t'` of
`L ⊗_{𝒪_X} M` is then the product of the normed transition units of the factors.

This is the form in which the multiplicativity of
`Stacks.SheafOfModules.generatorRatioUnit_tmulGenerator` enters the norm construction of
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY): the cocycle
`Stacks.Divisors.normTransitionCocycle` is built from `Stacks.Divisors.normGeneratorRatio`, so
the transition cocycle of a tensor product is the pointwise product of the two transition
cocycles.

## Main results

* `Stacks.Divisors.normGeneratorRatio_tmulGenerator`: **the normed ratio is multiplicative across
  a tensor product.**

## Implementation notes

The proof is `Stacks.SheafOfModules.generatorRatioUnit_tmulGenerator` followed by
multiplicativity of `Stacks.Divisors.normUnitsMap`, which is a monoid homomorphism; no property of
the norm beyond that is used, and in particular no trivializing cover of the target is needed.

No `@[stacks]` attribute is placed. This is an ingredient of Tag 0BCY, not a clause of it; the
additivity clause and the pullback--power clause of that tag additionally need an identification
of a module carrying chart generators with the glue of their ratio cocycle.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules
open scoped TensorProduct

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-- **The normed ratio of two elementary tensors of generators is the product of the normed
ratios of the factors.** -/
theorem normGeneratorRatio_tmulGenerator (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    (L M : X.Modules) (V : Y.Opens)
    (s s' : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V))
    (t t' : GeneratorSections X.toRingedSpace M (f ⁻¹ᵁ V)) :
    normGeneratorRatio f N.toMorphismNormMap
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))) V
        (tmulGenerator s t) (tmulGenerator s' t') =
      normGeneratorRatio f N.toMorphismNormMap L V s s' *
        normGeneratorRatio f N.toMorphismNormMap M V t t' :=
  (congrArg (normUnitsMap f N.toMorphismNormMap V)
    (generatorRatioUnit_tmulGenerator (X := X.toRingedSpace) s s' t t')).trans
    (map_mul (normUnitsMap f N.toMorphismNormMap V) _ _)

end Stacks.Divisors

end
