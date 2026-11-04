module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation

/-!
# Local finite type of a 1-morphism out of a reduced locally Noetherian one-point stack

Let `𝒴` be an algebraic stack over `S` which is reduced, locally Noetherian and has exactly one
point — condition (1) of **Stacks 06MP** — and let `i : 𝒴 ⟶ 𝒳` be a 1-morphism. This module
proves that `i` is locally of finite type as soon as *some* 1-morphism `z` to `𝒴` from the
algebraic stack of the spectrum of a field has `z ≫ i` locally of finite type. This is a step of
the proof of **Stacks 06G3**, where `𝒴` is the residual gerbe of `𝒳` at a finite type point.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_fieldSpectrumCover_comp`: the statement
  above.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06U8](https://stacks.math.columbia.edu/tag/06U8)
* [Stacks Project, Tag 06U9](https://stacks.math.columbia.edu/tag/06U9)
* [Stacks Project, Tag 0DQJ](https://stacks.math.columbia.edu/tag/0DQJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local finite type descends along a field-spectrum cover of a reduced locally Noetherian
one-point algebraic stack.** Let `𝒴` be an algebraic stack over `S` which is reduced with exactly
one point and locally Noetherian, let `i : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S`,
and let `z` be a 1-morphism to `𝒴` from the algebraic stack of the spectrum of a field. If
`z ≫ i` is locally of finite type then so is `i`. -/
theorem isLocallyOfFiniteType_of_fieldSpectrumCover_comp
    {𝒴 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒴 ⟶ 𝒳)
    (hred : IsReducedWithUniquePoint B S hS 𝒴)
    (hnoeth : IsLocallyNoetherianStack B S hS 𝒴)
    (F : FieldSpectrum B S hS) (z : schemeStack.{u, w} B S hS F.base ⟶ 𝒴)
    (hzi : AlgebraicStacks.IsLocallyOfFiniteType B S hS (z ≫ i)) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS i := by
  have hzlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS z :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS z hnoeth
      (AlgebraicStacks.isLocallyOfFiniteType_of_comp B S hS z i hzi)
  have hzflat : AlgebraicStacks.IsFlat B S hS z :=
    isFlat_of_isReducedWithUniquePoint.{u, w} B S hS 𝒴 hred F z
  have hzsurj : IsSurjective B S hS z := by
    obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F
    exact fun y => ⟨p, hred.2.2.allEq _ y⟩
  have hzrep : IsRepresentableByAlgebraicSpaces B S hS z.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base) z.hom
  exact AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf B S hS z i hzi hzrep hzsurj hzflat
    hzlfp

end AlgebraicGeometry.Stack

end
