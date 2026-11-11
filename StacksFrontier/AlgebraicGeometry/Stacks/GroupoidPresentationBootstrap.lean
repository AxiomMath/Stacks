module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth

/-!
# Bootstrapping algebraic stacks (Stacks 06DC)

An fppf stack in groupoids over a scheme `S` of a big fppf site whose diagonal is representable
by algebraic spaces and which receives a 1-morphism from an algebraic stack that is representable
by algebraic spaces, surjective and smooth is itself an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover`: the assembly —
  an algebraic cover transports the scheme atlas.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation`: the assembly step of the proof
  of **Stacks 06DC**, taking the diagonal and the smooth surjective cover as inputs. The theorem
  itself, with both inputs proved, is `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`.

## Implementation notes

The three nontrivial clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` are produced as
follows. The family-indexed stack condition of **Stacks 02ZI** is recovered from the
sieve-indexed one of **Stacks 026F** by `CategoryTheory.Functor.IsStack.isStackInGroupoids`, the
implication 026F ⟹ 02ZI of **Stacks 02ZJ**, so only the latter has to be assumed. The diagonal
clause is assumed. The scheme atlas is the atlas of the covering algebraic stack composed with
the covering 1-morphism: its representability by algebraic spaces is **Stacks 0301** and its
relative surjectivity-and-smoothness is **Stacks 045B** at the meet of
`AlgebraicGeometry.Space.surjectiveMorphismProperty` and
`AlgebraicGeometry.Space.smoothMorphismProperty`, whose three instance hypotheses are assembled
from those of the two factors (**Stacks 03MG**, **Stacks 03MH**, **Stacks 03ZD**, **Stacks
03ZE**, **Stacks 041Q** and **Stacks 0429**).

The assembly `isAlgebraicStack_of_flatPresentation` takes two inputs of the proof of Stacks
06DC as arguments.

* `hdiagonal`, representability of the diagonal of `𝒴` by algebraic spaces, which the source
  gets from **Stacks 05XW** applied to `F`; the library proves it as
  `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_flatPresentation`.
* `hcover`, the existence of an algebraic stack with a 1-morphism to `𝒴` that is representable
  by algebraic spaces, surjective and smooth, which the source gets by taking
  `∐_{d ≥ 1} 𝓗_{d, lci}(𝒳/𝒴)` — the locally-complete-intersection locus of the relative Hilbert
  stack of `F` (**Stacks 06CI**, **Stacks 06CL**, **Stacks 06CH**, **Stacks 06D9**, **Stacks
  06DA**). The library carries out that construction in
  `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`, which proves Stacks 06DC outright.

Hypothesis (2) of the source — that `F` is surjective, flat and locally of finite presentation —
is written out longhand rather than as `AlgebraicGeometry.Stack.HasRelativeProperty` at a meet of
three morphism properties, because flatness and local finite presentation of morphisms of
algebraic spaces are not packaged as `CategoryTheory.MorphismProperty`s in the library, so the
instance arguments of Stacks 03YK cannot be discharged for them and a statement using it would
not elaborate. The longhand is the condition of Stacks 03YK spelled out, exactly as the atlas
clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` spells out surjectivity and smoothness.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
* [Stacks Project, Tag 06CI](https://stacks.math.columbia.edu/tag/06CI)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An fppf stack in groupoids over `S` whose diagonal is representable by algebraic spaces and
which receives a 1-morphism from an algebraic stack that is representable by algebraic spaces,
surjective and smooth is an algebraic stack.

The scheme atlas is the atlas of the covering algebraic stack followed by the covering
1-morphism; representability of the composite is **Stacks 0301** and its relative
surjectivity-and-smoothness is **Stacks 045B**. -/
theorem isAlgebraicStack_of_smoothSurjectiveAlgebraicCover
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (q : 𝒲 ⟶ 𝒴)
    (h𝒲 : IsAlgebraicStack.{u, w} B S hS 𝒲.val)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiagonal : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴))
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom)
    (hqP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS) q hq) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val := by
  obtain ⟨hfib, ⟨-, -⟩, -, U, a, ha, hAtlas⟩ := h𝒲
  have ha' : IsRepresentableByAlgebraicSpaces B S hS
      (Bicategory.InducedBicategory.mkHom
        (X := schemeFibredCategory B S hS U) (Y := 𝒲) a).hom := ha
  have hcomp : IsRepresentableByAlgebraicSpaces B S hS
      (Bicategory.InducedBicategory.mkHom
        (X := schemeFibredCategory B S hS U) (Y := 𝒲) a ≫ q).hom :=
    isRepresentableByAlgebraicSpaces_comp_basedFunctor B S hS a q.hom ha hq
  refine ⟨𝒴.2, ⟨hstack, hstack.isStackInGroupoids 𝒴.2⟩, hdiagonal, U,
    BasedFunctor.comp a q.hom, hcomp, ?_⟩
  exact hasRelativeProperty_comp.{u, u, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
    (Bicategory.InducedBicategory.mkHom
      (X := schemeFibredCategory B S hS U) (Y := 𝒲) a) q ha' hq hAtlas hqP

/-- **The assembly step of Stacks 06DC.** Let `F : 𝒳 ⟶ 𝒴` be a
1-morphism of stacks in groupoids over the big fppf site of `S`. If `𝒳` is representable by an
algebraic space and `F` is representable by algebraic spaces, surjective, flat and locally of
finite presentation, then `𝒴` is an algebraic stack.

This version takes as arguments representability of the diagonal of `𝒴`, which the source gets
from Stacks 05XW, and a smooth surjective cover of `𝒴` by an algebraic stack, which the source
gets from the locally-complete-intersection locus of the relative Hilbert stack of `F`. Stacks
06DC with both proved is `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`. -/
theorem isAlgebraicStack_of_flatPresentation
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒳 ⟶ 𝒴)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (_h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (_hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (_hFprops : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor F))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom
       Space.IsSurjective B S hS g ∧ Space.IsFlat B S hS g ∧
         Space.IsLocallyOfFinitePresentation B S hS g))
    (hdiagonal : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴))
    (hcover : ∃ (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (q : 𝒲 ⟶ 𝒴) (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom),
      IsAlgebraicStack.{u, w} B S hS 𝒲.val ∧
        HasRelativeProperty.{u, u, u + 1, u} B S hS
          (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
          q hq) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val := by
  obtain ⟨𝒲, q, hq, h𝒲, hqP⟩ := hcover
  exact isAlgebraicStack_of_smoothSurjectiveAlgebraicCover.{u, w} B S hS q h𝒲 hstack hdiagonal
    hq hqP

end AlgebraicGeometry.Stack

end
