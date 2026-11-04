module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperTFAE
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedQuasiSeparatedAlgebraicStack

/-!
# Two more implications among the four conditions of Stacks 04YS

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` which is representable by algebraic spaces. Stacks 04YS asserts the
equivalence of

1. `f` is separated,
2. `Δ_f` is a closed immersion,
3. `Δ_f` is proper, and
4. `Δ_f` is universally closed,

all four in the relative sense of Properties of Stacks, Section 04XB. The implication (3) ⇒ (4)
is `AlgebraicGeometry.Stack.universallyClosed_of_isProper`. This file adds (2) ⇒ (3), and
(4) ⇒ (2) under the hypothesis that the represented base changes of `Δ_f` are locally of finite
type.

## Main results

* `AlgebraicGeometry.Stack.isProper_relativeDiagonal_of_isClosedImmersion`: **the implication
  (2) ⇒ (3) of Stacks 04YS**, for the relative diagonal of a 1-morphism of categories fibred in
  groupoids, and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isClosedImmersion_relativeDiagonal`:
  the same implication read between the two conditions as the source states them, part (2) of
  Stacks 04YL on the relative diagonal and the separatedness condition of Stacks 04YW.
* `AlgebraicGeometry.Stack.isClosedImmersion_relativeDiagonal_of_universallyClosed`: **the
  implication (4) ⇒ (2) of Stacks 04YS**, conditional on the represented base changes of `Δ_f`
  being locally of finite type.

## Implementation notes

The four conditions of Stacks 04YS are quantified clause by clause over the same data — a
scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` and an algebraic space representing the base change of
`Δ_f` along it — so an implication between them which holds for morphisms of algebraic spaces
holds pointwise for them.

The locally-of-finite-type hypothesis of (4) ⇒ (2) is part (2) of Stacks 04XS; for a 1-morphism
representable by algebraic spaces it is
`AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal`, and the equivalence of
the four conditions, which carries the tag 04YS, is
`AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_tfae`.

## References

* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The implication (2) ⇒ (3) of Stacks 04YS.** If the relative diagonal of a 1-morphism of
algebraic stacks over `S` is a closed immersion in the relative sense of Stacks 04XB, then it is
proper in that sense. -/
theorem isProper_relativeDiagonal_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (h : IsClosedImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) :
    IsProper B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  fun U y hy F hF he =>
    Space.isProper_of_isClosedImmersion B S hS
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
      (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) _ (h U y hy F hF he)

/-- **The implication (4) ⇒ (2) of Stacks 04YS, conditional on part (2) of Stacks 04XS.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is representable by algebraic
spaces and assume that every algebraic space representing a base change of its relative diagonal
along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has structural morphism all of whose
represented base changes are locally of finite type. If the relative diagonal is universally
closed in the relative sense of Stacks 04XB, then it is a closed immersion in that sense. -/
theorem isClosedImmersion_relativeDiagonal_of_universallyClosed (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hLFT : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
        = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
          (CatFiberedInGroupoids.homFunctor
            (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (h : UniversallyClosed B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) :
    IsClosedImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  fun U y hy F hF he => Space.isClosedImmersion_of_mono_of_charts B S hS _
    (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF
      (subsingleton_representing_of_relativeDiagonal B S hS 𝒳.val 𝒴.val f.hom hf U y hy F he))
    (hLFT U y hy F hF he)
    (Space.presheaf_universallyClosed_of_universallyClosed B S hS
      (hLFT U y hy F hF he).1 (h U y hy F hF he))

namespace AlgebraicStacks

/-- **The implication (2) ⇒ (3) of Stacks 04YS, between the two conditions as the source states
them.** If the relative diagonal of a 1-morphism `f` of algebraic stacks over `S` is a closed
immersion of algebraic stacks — part (2) of Stacks 04YL — then `f` is separated in the sense of
Stacks 04YW, that is, its relative diagonal is proper in the relative sense of Stacks 04XB. -/
theorem isSeparated_of_isClosedImmersion_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (h : Stack.AlgebraicStacks.IsClosedImmersion B S hS
      (Bicategory.InducedBicategory.mkHom
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :
          𝒳 ⟶ relativeDiagonalTargetStack B S hS 𝒳 𝒴 f)) :
    Stack.AlgebraicStacks.IsSeparated B S hS f :=
  isProper_relativeDiagonal_of_isClosedImmersion B S hS f h.2

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
