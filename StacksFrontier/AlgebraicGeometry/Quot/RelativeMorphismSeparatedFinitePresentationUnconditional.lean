module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismSeparatedFinitePresentation

/-!
# `Mor_B(Y, X) ⟶ B` is separated and locally of finite presentation (Stacks 0DPN)

Let `B` be an algebraic space and `Y, X` algebraic spaces over `B` with `Y ⟶ B` flat, proper and
of finite presentation and `X ⟶ B` separated and of finite presentation. Stacks 0DPN asserts that
`Mor_B(Y, X) ⟶ B` is separated and locally of finite presentation.

The separation clause is the source's argument: the diagonal is a closed immersion by Stacks 0DPM
(`AlgebraicGeometry.Space.isSeparated_relativeHomProjection`). For the second clause the source
cites Stacks 0D1C; here it is
`isLocallyOfFinitePresentation_relativeHomProjection_of_isFinitePresentation`, which reads local
finite presentation off the functor of points (Stacks 04AK) and needs neither the algebraicity of
`Mor_B(Y, X)` nor the flatness and properness of `Y ⟶ B`. So the statement below drops the
hypothesis `hilb` (algebraic models of the Hilbert functors) of
`AlgebraicGeometry.Space.isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection`.

In this development `Y ⟶ B` is `z : Z ⟶ Q` and `X ⟶ B` is `x : X ⟶ Q`.

## Main results

* `isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection_unconditional`:
  **Stacks 0DPN.** For `z` flat, proper and of finite presentation and `x` separated and of finite
  presentation, the projection `Mor_Q(Z, X) ⟶ Q` is separated and locally of finite presentation.

## References

* [Stacks Project, Tag 0DPN](https://stacks.math.columbia.edu/tag/0DPN)
* [Stacks Project, Tag 0DPM](https://stacks.math.columbia.edu/tag/0DPM)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- **Stacks 0DPN.** Let `Q` be an algebraic space, `z : Z ⟶ Q` flat, proper and of finite
presentation and `x : X ⟶ Q` separated and of finite presentation, all algebraic spaces over `S`.
Then the projection `Mor_Q(Z, X) ⟶ Q` of the relative morphism functor is separated (its diagonal
is a closed immersion, Stacks 0DPM) and locally of finite presentation. -/
@[stacks 0DPN]
theorem isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection_unconditional
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z) :
    IsSeparated B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) ∧
      IsLocallyOfFinitePresentation B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  ⟨isSeparated_relativeHomProjection hZ hX hQ hsep hxfp hfp hflat hproper,
    isLocallyOfFinitePresentation_relativeHomProjection_of_isFinitePresentation z x hZ hX hQ hfp
      hxfp.1⟩

end AlgebraicGeometry.Space

end
