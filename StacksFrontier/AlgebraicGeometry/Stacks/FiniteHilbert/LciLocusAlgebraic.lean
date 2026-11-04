module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusInherited
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.RelativeAlgebraicity
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.RelativeAlgebraicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FiniteCoverAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack

/-!
# The local complete intersection locus is an algebraic stack

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
with `𝒳` representable by an algebraic space and `F` representable by algebraic spaces,
surjective, flat and locally of finite presentation, and let `d` be a positive natural number.
This file proves that the local complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` of **Stacks 06CJ**
is an algebraic stack, and that `𝒴` is an algebraic stack as soon as the 1-morphism
`ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is representable by algebraic spaces, surjective and smooth.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_lciFiniteHilbertCategory`: the locus is an algebraic
  stack.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_lciFiniteHilbertCoveringMorphism`: if the
  1-morphism from the locus to `𝒴` is representable by algebraic spaces, surjective and smooth,
  then `𝒴` is an algebraic stack.

## References

* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 06CI](https://stacks.math.columbia.edu/tag/06CI)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- **The local complete intersection locus of a flat presentation is an algebraic stack.**  For
a positive degree `d` and a 1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in groupoids over the big fppf site
of `S` with `𝒳` representable by an algebraic space and `F` representable by algebraic spaces,
surjective, flat and locally of finite presentation, the locus `ℋ_{d,lci}(𝒳/𝒴)` of Stacks 06CJ
is an algebraic stack. -/
theorem isAlgebraicStack_lciFiniteHilbertCategory (hd : 0 < d)
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    IsAlgebraicStack.{u, w} B S hS
      (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hflat := fun U y hy P hP he => (hFprops U y hy P hP he).2.1
  have hlfp := fun U y hy P hP he => (hFprops U y hy P hP he).2.2
  have h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids :=
    isFiberedInGroupoids_lciFiniteHilbertCategory
      (FiniteHilbert.hasOpenLciLocus hF hflat hlfp)
  exact isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces.{u, w} B S hS
    (𝒳 := lciFiniteHilbertFibered h) (𝒴 := finiteHilbertFibered B S hS d 𝒳 𝒴 F)
    (Bicategory.InducedBicategory.mkHom
      (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)))
    (isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion_of_flat hF hflat hlfp)
    (isAlgebraicStack_finiteHilbertFibered.{u, w} hd h𝒴 h𝒳 hF hFprops)

/-- **A covering 1-morphism out of the local complete intersection locus.**  Under the
hypotheses on `F` of `isAlgebraicStack_lciFiniteHilbertCategory`, if the 1-morphism
`ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴`, bundled using the witness `h` that the locus is fibred in groupoids, is
representable by algebraic spaces and relatively surjective and smooth, then `𝒴` is an algebraic
stack. -/
theorem isAlgebraicStack_of_lciFiniteHilbertCoveringMorphism (hd : 0 < d)
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F))
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids)
    (hq : IsRepresentableByAlgebraicSpaces B S hS (lciFiniteHilbertToTargetFibered h).hom)
    (hqP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
      (lciFiniteHilbertToTargetFibered h) hq) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.toBasedCategory :=
  isAlgebraicStack_of_lciFiniteHilbertCover.{u, w} h
    (isAlgebraicStack_lciFiniteHilbertCategory.{u, w} hd h𝒴 h𝒳 hF hFprops) h𝒴
    (hasRepresentableDiagonal_targetCFG_of_flatPresentation h𝒴 h𝒳 hF hFprops) hq hqP

end AlgebraicGeometry.Stack

end
