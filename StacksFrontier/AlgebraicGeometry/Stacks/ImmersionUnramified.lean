module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedImmersionAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd

/-!
# An immersion of algebraic stacks is unramified (Stacks 0CIX)

An immersion of algebraic stacks over `S` (Stacks 04YL, part (3)) is unramified in the sense of
Stacks 0CIT: it is Deligne–Mumford, and in every étale-smooth diagram over it the top horizontal
morphism of algebraic spaces is unramified.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isUnramified_of_isImmersion`: **Stacks 0CIX**.

## Implementation notes

`AlgebraicGeometry.Stack.IsUnramified` (Stacks 0CIT) asks for the *universal* étale-smooth
diagram test, which Stacks 0CIF identifies with the existential one only for a property of
morphisms of algebraic spaces that is étale-smooth local on the source and target — Stacks 0CG3
at unramifiedness, which this library does not have. The universal test is reached here without
that identification, by factoring each diagram's top horizontal morphism: it is the comparison
to the canonical 2-fibre product of the diagram's cospan followed by that product's first
projection. The first projection induces a base change of the immersion along an algebraic
space, so it is unramified by Stacks 04XC applied to the relative property of Stacks 03YK that
Stacks 06CQ gives the immersion; the comparison is étale, hence unramified by Stacks 06CR; and
unramifiedness is stable under composition by Stacks 03ZI.

## References

* [Stacks Project, Tag 03ZI](https://stacks.math.columbia.edu/tag/03ZI)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 06CQ](https://stacks.math.columbia.edu/tag/06CQ)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIX](https://stacks.math.columbia.edu/tag/0CIX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CIX.** An immersion of algebraic stacks over `S`, in the sense of Stacks 04YL,
part (3), is unramified in the sense of Stacks 0CIT. -/
@[stacks 0CIX]
theorem isUnramified_of_isImmersion (j : 𝒵 ⟶ 𝒳) (hj : IsImmersion B S hS j) :
    Stack.IsUnramified B S hS j := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsUnramified B S hS g.hom
  let : P.IsStableUnderBaseChange := Space.isUnramified_isStableUnderBaseChange B S hS
  let : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrel : Stack.HasRelativeProperty B S hS P j.hom hj.1 := fun U y hy F hF hrep =>
    Space.isUnramified_of_isImmersion B S hS
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
      (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) (hj.2 U y hy F hF hrep)
  refine ⟨isDM_of_isImmersion B S hS j hj, ?_⟩
  intro U V hU hV a b h η _hbsm hcompar
  -- the canonical 2-fibre product of the diagram's cospan, and the comparison to it
  have hQ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom j.hom
  have hket := hcompar
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom) hQ
    (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom j.hom
      (diagramCone B S hS j.hom a.hom b.hom h η))
  -- the apex of that product is representable by an algebraic space, by Stacks 0300
  obtain ⟨T, hT, ⟨eT₀⟩⟩ := Stack.isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (fibredCategory B S hS V) 𝒵.val b.hom.hom j.hom.hom hj.1
    (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  let eT : StacksRepresentableCFG.EquivalenceOver
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom).pt.val.p
    (presheafOfCategories (T ⋙ typeToCat)).p := eT₀
  -- the first projection is a base change of the immersion along an algebraic space
  have hfst : Space.IsUnramified B S hS
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom).pt
        (fibredCategory B S hS V) T V eT (StacksRepresentableCFG.EquivalenceOver.refl _)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom).fst) :=
    Stack.prop_representingMap_of_hasRelativeProperty B S hS P j.hom hj.1 hrel
      (fibredCategory B S hS V) b.hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom) hQ
      T V hT hV eT (StacksRepresentableCFG.EquivalenceOver.refl _)
  -- the comparison is étale, hence unramified
  have hkrep : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom j.hom
        (diagramCone B S hS j.hom a.hom b.hom h η)).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) ⟨T, hT, ⟨eT⟩⟩
  have hcmp : Space.IsUnramified B S hS
      (representingMap B S hS (fibredCategory B S hS U)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom j.hom).pt U T
        (StacksRepresentableCFG.EquivalenceOver.refl _) eT
        (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom j.hom
          (diagramCone B S hS j.hom a.hom b.hom h η)).hom) :=
    Space.isUnramified_of_isEtale B S hS
      (Stack.isEtale_representingMap_of_isRelativelyEtale B S hS _ hkrep U T hU hT
        (StacksRepresentableCFG.EquivalenceOver.refl _) eT hket)
  -- the top horizontal morphism of the diagram is the composite of the two
  exact Stack.representingMap_preHom_comp_fst B S hS j.hom a.hom b.hom h η _ _ T eT ▸
    Space.isUnramified_comp B S hS hU hT hV _ _ hcmp hfst

end AlgebraicGeometry.Stack.AlgebraicStacks

end
