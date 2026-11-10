module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismDiagonal

/-!
# `Mor_B(Y, X) ⟶ B` is separated and locally of finite presentation (Stacks 0DPN)

Let `B` be an algebraic space and `Y, X` algebraic spaces over `B` with `Y ⟶ B` flat, proper and
of finite presentation and `X ⟶ B` separated and of finite presentation. Stacks 0DPN asserts that
`Mor_B(Y, X) ⟶ B` is separated and locally of finite presentation: its diagonal is a closed
immersion (Stacks 0DPM, `AlgebraicGeometry.Space.isSeparated_relativeHomProjection`), and it is
locally of finite presentation by Stacks 0D1C
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_relativeHomProjection`).

## Main results

* `AlgebraicGeometry.Space.isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection`:
  `Mor_B(Y, X) ⟶ B` is separated and locally of finite presentation.

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

/-- For `z : Z ⟶ Q` flat, proper and of finite presentation and `x : X ⟶ Q` separated and of
finite presentation, the projection `Mor_Q(Z, X) ⟶ Q` is separated and locally of finite
presentation (Stacks 0DPN). -/
theorem isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z) :
    IsSeparated B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) ∧
      IsLocallyOfFinitePresentation B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  ⟨isSeparated_relativeHomProjection hZ hX hQ hsep hxfp hfp hflat hproper,
    isLocallyOfFinitePresentation_relativeHomProjection z x hZ hX hQ hxfp hsep hfp hflat hproper⟩

end AlgebraicGeometry.Space

end
