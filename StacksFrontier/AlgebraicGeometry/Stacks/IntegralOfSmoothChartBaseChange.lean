module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorTotalSpaceAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralFiniteMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableOfFlatCoverBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone

/-!
# A 1-morphism whose base change along a smooth cover is integral

Let `ν : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` and let `g : W ⟶ 𝒳` be a surjective
smooth 1-morphism from an algebraic space. If some 2-fibre product `W ×_𝒳 𝒳'` is (the stack of)
an algebraic space `V` whose projection to `W` is (induced by) an integral morphism `V ⟶ W` of
algebraic spaces, then `ν` is integral in the sense of Stacks 0CHU: it is representable by
algebraic spaces (Stacks 04ZP) and integral in the sense of Stacks 04XB (Stacks 06TY).

This is the step "as `U^ν → U` is integral, we see that `ν` is integral" of the proof of
Stacks 0GMJ, for an arbitrary 1-morphism.

## Main results

* `isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_smoothChart`: representability of `ν`.
* `isIntegralHom_of_isTwoFibreProduct_smoothChart`: integrality of `ν`.

## References

* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06TY](https://stacks.math.columbia.edu/tag/06TY)
* [Stacks Project, Tag 0CHU](https://stacks.math.columbia.edu/tag/0CHU)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (ν : 𝒳' ⟶ 𝒳)
  {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
  (hV : IsAlgebraicSpace B S hS V)
  (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒳) (h : V ⟶ W)
  (a : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳')
  (θ : (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
      algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≫ g ≅
    a ≫ ν)

/-- The 2-commutative square with apex the stack of `V`, its projection to the stack of `W`
induced by `h : V ⟶ W`, and its projection to `𝒳'` the given `a`. -/
def smoothChartSquare : Bicategory.TwoCommSq g ν where
  pt := algebraicSpaceStack.{u, w} B S hS V hV
  fst := Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1
  snd := a
  iso := θ

/-- **A 1-morphism whose base change along a surjective smooth 1-morphism from an algebraic space
is an algebraic space is representable by algebraic spaces.** This is Stacks 04ZP, the
implication (2) ⟹ (1), a smooth morphism being flat and locally of finite presentation. -/
theorem isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_smoothChart
    (hSurj : IsSurjective B S hS g) (hSmooth : AlgebraicStacks.IsSmooth B S hS g)
    (hQ : Bicategory.IsTwoFibreProduct (smoothChartSquare B S hS ν hW hV g h a θ)) :
    IsRepresentableByAlgebraicSpaces B S hS ν.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_pt B S hS ν g
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW) hSurj
    (isFlat_of_isSmooth B S hS g hSmooth)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS g hSmooth)
    _ hQ (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)

/-- **A 1-morphism whose base change along a surjective smooth 1-morphism from an algebraic space
is an integral morphism of algebraic spaces is integral** (Stacks 0CHU, part (1)).

Representability is `isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_smoothChart`.
Integrality in the sense of Stacks 04XB descends from the projection `V ⟶ W` by Stacks 06TY; that
projection is the 1-morphism of Stacks 0458 attached to `h`, which is integral in the sense of
Stacks 04XB by Stacks 045A, because every base change of `h` along a scheme-valued point is
integral (Stacks 03ZS). -/
theorem isIntegralHom_of_isTwoFibreProduct_smoothChart
    (hSurj : IsSurjective B S hS g) (hSmooth : AlgebraicStacks.IsSmooth B S hS g)
    (hQ : Bicategory.IsTwoFibreProduct (smoothChartSquare B S hS ν hW hV g h a θ))
    (hh : Space.IsIntegralHom B S hS h) :
    AlgebraicStacks.IsIntegralHom B S hS ν := by
  have hν := isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_smoothChart B S hS ν hW hV g h
    a θ hSurj hSmooth hQ
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW) g.hom
  have hrep := Space.isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hV hW h
  have hprop : Space.HasProperty B S hS (Space.integralMorphismProperty B S hS) h hrep :=
    Space.hasProperty_of_space_hom' (Space.integralMorphismProperty B S hS) hV hW h hh
  have hrel := (holdsOnEverySchemePoint_iff_hasRelativeProperty B S hS
    (Space.integralMorphismProperty B S hS) h hrep).1 hprop
  refine ⟨hν, (hasRelativeProperty_iff_of_fppfCover B S hS (Space.integralMorphismProperty B S hS)
    ν g hν hg hSurj (isFlat_of_isSmooth B S hS g hSmooth)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS g hSmooth) _ hQ).2 ⟨_, hrel⟩⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
