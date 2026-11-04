module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveMorFunctorsEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveMorFunctorsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceHilbertModelsBounded

/-!
# The diagonal of `Curves` is representable by algebraic spaces (towards Stacks 0D53)

Stacks 0D53 says that the diagonal of the stack of curves is representable by algebraic spaces.
The source deduces it from Stacks 0D1F, whose input is the algebraicity of Hilbert functors of
algebraic spaces (Stacks 0D01, through Artin's criterion for the stack of coherent sheaves). The
proof assembled here avoids that: families of curves are H-projective étale locally on the base,
so only the Hilbert functors of projective spaces over affine schemes are needed.

All names below are in the namespace `AlgebraicGeometry.C1590Private`.

* Criterion (2) of Stacks 045G reduces the diagonal to the algebraicity of the `Isom` functors of
  families of curves
  (`hasRepresentableDiagonal_curvesFiberedCategory_of_curveIsomFunctorsAlgebraic`), and
  `Isom_U(F, G)` is open in `Mor_U(F, G)` (Stacks 0DPP,
  `curveIsomFunctorsAlgebraic_of_curveMorFunctorsAlgebraic`).
* `Mor_U(F, G)` is glued from affine étale neighbourhoods over which both families are
  H-projective (`curveMorFunctorsAlgebraic_of_projectiveMorFunctorsBounded`).
* Over such a neighbourhood it is an open subspace of the Hilbert functor of `F ×_U G`, which is a
  closed subspace of the Hilbert functor of a projective space (Stacks 0D1B and 0DPF,
  `projectiveMorFunctorsBounded_of_projectiveSpaceHilbertModelsBounded`).

* The Hilbert functors of the projective spaces `ℙⁿ_U ⟶ U` have algebraic models with atlases
  of bounded size (`projectiveSpaceHilbertModelsBounded`), built from the projective Quot schemes
  `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` by base change.

## Main results

* `hasRepresentableDiagonal_curvesFiberedCategory_of_projectiveSpaceHilbertModelsBounded`: the
  diagonal of `Curves` is representable by algebraic spaces once the Hilbert functors of the
  projective spaces over affine objects of the site have algebraic models with atlases of bounded
  size (`ProjectiveSpaceHilbertModelsBounded`).
* `hasRepresentableDiagonal_curvesFiberedCategory`: the diagonal of `Curves` is representable by
  algebraic spaces.

## Implementation notes

Nothing here carries a `stacks` attribute: the statement is used as a helper towards other
tags.

## References

* [Stacks Project, Tag 0D53](https://stacks.math.columbia.edu/tag/0D53)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0D53, from the Hilbert functors of projective spaces.** If, for every `n`, the
Hilbert functors of `ℙⁿ_U ⟶ U` over affine objects `U` of the big fppf site over `Spec ℤ` have
algebraic models whose atlases are bounded in terms of the size of `U`, then the diagonal of the
stack of curves is representable by algebraic spaces. -/
theorem hasRepresentableDiagonal_curvesFiberedCategory_of_projectiveSpaceHilbertModelsBounded
    (hD : ProjectiveSpaceHilbertModelsBounded B hZ) :
    Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ) :=
  hasRepresentableDiagonal_curvesFiberedCategory_of_curveIsomFunctorsAlgebraic B hZ
    (curveIsomFunctorsAlgebraic_of_curveMorFunctorsAlgebraic B hZ
      (curveMorFunctorsAlgebraic_of_projectiveMorFunctorsBounded B hZ
        (projectiveMorFunctorsBounded_of_projectiveSpaceHilbertModelsBounded B hZ hD)))

/-- **Stacks 0D53.** The diagonal of the stack of curves is representable by algebraic spaces. -/
theorem hasRepresentableDiagonal_curvesFiberedCategory :
    Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ) :=
  hasRepresentableDiagonal_curvesFiberedCategory_of_projectiveSpaceHilbertModelsBounded B hZ
    (projectiveSpaceHilbertModelsBounded B hZ)

end AlgebraicGeometry.C1590Private

end
