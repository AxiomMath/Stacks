module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRelativeDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative

/-!
# Relative descent for a 1-morphism of algebraic stacks locally of finite type

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is locally of finite type.
Its relative diagonal `Δ_f` and the diagonal `Δ_{Δ_f}` of that are representable by algebraic
spaces (**Stacks 04XS**) and locally of finite presentation (**Stacks 0CMG**, applied twice), so
both are limit preserving on objects by **Stacks 06CX**. Hence `f` satisfies relative descent of
morphisms and of equalities, `AlgebraicGeometry.Stack.RelativeDescentHom` and
`AlgebraicGeometry.Stack.RelativeDescentEq`, along every cofiltered limit of affine schemes over
`S`.

## Main results

All in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isLimitPreservingOnObjects_of_isRepresentable_of_isLocallyOfFinitePresentation`: a 1-morphism
  of algebraic stacks representable by algebraic spaces and locally of finite presentation is
  limit preserving on objects.
* `isLimitPreservingOnObjects_relativeDiagonal` and
  `isLimitPreservingOnObjects_relativeDiagonal_relativeDiagonal`: the two diagonals of a
  1-morphism locally of finite type are limit preserving on objects.
* `relativeDescentHom_of_isLocallyOfFiniteType` and
  `relativeDescentEq_of_isLocallyOfFiniteType`.

## Implementation notes

Stacks 06CX is stated for the relative property of Stacks 03YK, while local finite presentation
of a 1-morphism of algebraic stacks is the universal smooth-diagram test of Stacks 06Q2; for a
1-morphism representable by algebraic spaces the two are equated by
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_relative`.

Index categories are taken in the universe of the schemes, the size at which Stacks 06CX is
available.

## References

* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CMG](https://stacks.math.columbia.edu/tag/0CMG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable 1-morphism of algebraic stacks locally of finite presentation is limit
preserving on objects.** Local finite presentation in the sense of Stacks 06Q2 is the relative
property of Stacks 03YK for a 1-morphism representable by algebraic spaces, which is the
hypothesis of Stacks 06CX. -/
theorem isLimitPreservingOnObjects_of_isRepresentable_of_isLocallyOfFinitePresentation
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val 𝒴.val g.hom := by
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳.val 𝒴.val
    g.hom hrep).mpr ?_
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS
    (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒳.property 𝒴.property g.hom hrep).mp hg

/-- **The relative diagonal of a 1-morphism of algebraic stacks locally of finite type is limit
preserving on objects.** It is representable by algebraic spaces by Stacks 04XS and locally of
finite presentation by Stacks 0CMG. -/
theorem isLimitPreservingOnObjects_relativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val
      (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳.val 𝒴.val 𝒳.val f.hom f.hom)
      (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom) :=
  isLimitPreservingOnObjects_of_isRepresentable_of_isLocallyOfFinitePresentation B S hS
    (relativeDiagonal B S hS f)
    (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf)

/-- **The second diagonal of a 1-morphism of algebraic stacks locally of finite type is limit
preserving on objects.** The relative diagonal is locally of finite presentation by Stacks 0CMG,
hence locally of finite type, so Stacks 0CMG applies to it in turn, and its diagonal is
representable by algebraic spaces by Stacks 04XS. -/
theorem isLimitPreservingOnObjects_relativeDiagonal_relativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val
      (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳.val
        (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳.val 𝒴.val 𝒳.val f.hom f.hom) 𝒳.val
        (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom)
        (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom))
      (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳.val
        (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳.val 𝒴.val 𝒳.val f.hom f.hom)
        (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom)) :=
  isLimitPreservingOnObjects_of_isRepresentable_of_isLocallyOfFinitePresentation B S hS
    (relativeDiagonal B S hS (relativeDiagonal B S hS f))
    (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS _)
    (isLocallyOfFinitePresentation_relativeDiagonal B S hS _
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf)))

/-- **Relative descent of morphisms for a 1-morphism of algebraic stacks locally of finite
type**, along every cofiltered limit of affine schemes over `S`. -/
theorem relativeDescentHom_of_isLocallyOfFiniteType
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Stack.RelativeDescentHom.{u, u, u, u, u} B S hS f.hom D c :=
  Stack.relativeDescentHom_of_isLimitPreservingOnObjects_diagonal.{u, u, u, u, u} B S hS f.hom
    (isLimitPreservingOnObjects_relativeDiagonal B S hS f hf) D c hc

/-- **Relative descent of equalities for a 1-morphism of algebraic stacks locally of finite
type**, along every cofiltered limit of affine schemes over `S`. -/
theorem relativeDescentEq_of_isLocallyOfFiniteType
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Stack.RelativeDescentEq.{u, u, u, u, u} B S hS f.hom D c :=
  Stack.relativeDescentEq_of_isLimitPreservingOnObjects_diagonal_diagonal.{u, u, u, u, u} B S hS
    f.hom
    (isLimitPreservingOnObjects_relativeDiagonal_relativeDiagonal B S hS f hf) D c hc

end AlgebraicGeometry.Stack.AlgebraicStacks

end
