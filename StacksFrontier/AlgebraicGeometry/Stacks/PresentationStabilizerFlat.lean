module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquareAlgebraicStacks
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The stabilizer of a presentation is flat when the inertia is

Let `𝒳` be an algebraic stack over `S` whose inertia projection `ℐ_𝒳 ⟶ 𝒳` is flat and locally of
finite presentation, and let `[U/R] ⟶ 𝒳` be a presentation with stabilizer group algebraic space
`G/U`. Then

    G ⟶ U

is a flat, locally finitely presented morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isFlat_algebraicSpaceStackMap_iff`: a morphism of algebraic spaces over
  `S` is flat exactly when the 1-morphism of algebraic stacks it induces is.
* `AlgebraicGeometry.Stack.isFlat_presentationStabilizer` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_presentationStabilizer`: the structure
  morphism `G ⟶ U` of the stabilizer of a presentation is flat, resp. locally of finite
  presentation, as soon as the inertia projection of `𝒳` is.

## References

* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces over `S` is flat exactly when the 1-morphism of algebraic
stacks it induces is. -/
theorem isFlat_algebraicSpaceStackMap_iff
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G) :
    AlgebraicStacks.IsFlat B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsFlat B S hS g := by
  refine Iff.trans (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _) ?_
  refine Iff.trans (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS T hT)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS G hG) T G hT hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _) ?_
  rw [representingMap_associatedMap B S hS T G g]

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : GroupoidPresentation B S hS 𝒳.val.val)

/-- The 1-morphism `𝒮_G ⟶ 𝒮_U` of the inertia–presentation square is the 1-morphism of algebraic
stacks attached to the structure morphism `G ⟶ U` of the stabilizer. -/
theorem presentationStabilizerProjectionAlgebraicStacks_eq :
    presentationStabilizerProjectionAlgebraicStacks B S hS P =
      algebraicSpaceStackMap.{u, w} B S hS
        (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property
        P.groupoid.objects.property
        (GroupoidInAlgebraicSpaces.stabilizer P.groupoid).hom :=
  (rfl)

/-- The swapped inertia–presentation square is a 2-fibre product of algebraic stacks. -/
private noncomputable def isTwoFibreProduct_swap_inertiaPresentationSquare :
    Bicategory.IsTwoFibreProduct (inertiaPresentationSquareAlgebraicStacks B S hS P).swap :=
  Bicategory.isTwoFibreProduct_swap
    (isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks B S hS P)

/-- If the inertia projection `ℐ_𝒳 ⟶ 𝒳` of an algebraic stack `𝒳` over `S` is flat, then for
every presentation `[U/R] ⟶ 𝒳` the structure morphism `G ⟶ U` of the stabilizer group algebraic
space of the presenting groupoid is a flat morphism of algebraic spaces. -/
@[stacks 06QJ "the implication (2) implies (1): flatness of the stabilizer of a presentation"]
theorem isFlat_presentationStabilizer
    (hflat : AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    Space.IsFlat B S hS (GroupoidInAlgebraicSpaces.stabilizer P.groupoid).hom :=
  (isFlat_algebraicSpaceStackMap_iff.{u, w} B S hS
    (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property
    P.groupoid.objects.property
    (GroupoidInAlgebraicSpaces.stabilizer P.groupoid).hom).1
    (AlgebraicStacks.isFlat_baseChange B S hS _ _ _
      (isTwoFibreProduct_swap_inertiaPresentationSquare B S hS P) hflat)

/-- If the inertia projection `ℐ_𝒳 ⟶ 𝒳` of an algebraic stack `𝒳` over `S` is locally of finite
presentation, then for every presentation `[U/R] ⟶ 𝒳` the structure morphism `G ⟶ U` of the
stabilizer group algebraic space of the presenting groupoid is locally of finite presentation. -/
@[stacks 06QJ "the implication (2) implies (1): local finite presentation of the stabilizer of a \
presentation"]
theorem isLocallyOfFinitePresentation_presentationStabilizer
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    Space.IsLocallyOfFinitePresentation B S hS
      (GroupoidInAlgebraicSpaces.stabilizer P.groupoid).hom :=
  (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS
    (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property
    P.groupoid.objects.property
    (GroupoidInAlgebraicSpaces.stabilizer P.groupoid).hom).1
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS _ _ _
      (isTwoFibreProduct_swap_inertiaPresentationSquare B S hS P) hlfp)

end AlgebraicGeometry.Stack

end
