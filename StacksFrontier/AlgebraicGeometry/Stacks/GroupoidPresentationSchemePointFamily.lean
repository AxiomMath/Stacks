module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatPresentationRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.GluedChartSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap

/-!
# Stacks 06DC from a family of scheme-valued points

**Stacks 06DC** derives algebraicity of `𝒴` from a 1-morphism `F : 𝒳 ⟶ 𝒴` with `𝒳` representable
by an algebraic space and `F` representable by algebraic spaces, surjective, flat and locally of
finite presentation. The source's proof draws two things from that presentation: representability
of the diagonal of `𝒴`, which is **Stacks 05XW**, and a cover of `𝒴`, which it builds out of the
locally-complete-intersection locus of the relative Hilbert stack of `F`.

This file reads the second input as a *family of scheme-valued points* of `𝒴` rather than as a
1-morphism from an algebraic stack, which is what the route of
`StacksFrontier.AlgebraicGeometry.Stacks.GluedChartSchemePoint` consumes: the coproduct of the
objects of the site underlying the members is again an object of the site, the family glues into
one scheme-valued point out of it, and the three conditions "on objects" of that point make `𝒴`
algebraic. All three are read on the family: surjectivity on objects off one member, limit
preservation and formal smoothness on objects off every member.

Forming the coproduct of the *site objects* is what distinguishes this from the source's own
assembly, which takes the coproduct of the loci as *categories* and then has to stackify it: the
sigma category of a family of stacks is not a stack, and its algebraicity is false as stated,
because its fibre over an object covered by the empty sieve has one object per index while the
fibre of a stack there is contractible.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation_of_jointlySurjective_family`:
  clauses (1) and (2) of Stacks 06DC together with the family of scheme-valued points, the family
  being *jointly* surjective on objects — which is the form in which the source's cover is
  surjective, the degree of the locus varying with the field object.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation_of_schemePointFamily`: the same
  at a family one of whose members is surjective on objects.

## Implementation notes

Representability of the diagonal is produced, not assumed:
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_flatPresentation` is Stacks 05XW. Clause
(1) and the flatness and local finite presentation of clause (2) enter only through it, exactly as
in `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation`.

The family's hypotheses are spelled out longhand, as they are there, because the conditions on
objects are not packaged as `CategoryTheory.MorphismProperty`s.

## References

* [Stacks Project, Tag 04YD](https://stacks.math.columbia.edu/tag/04YD)
* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clauses (1) and (2) of Stacks 06DC, with the cover read as a jointly surjective family of
scheme-valued points.** Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over
the big fppf site of `S` with `𝒴` a stack for the fppf topology, `𝒳` representable by an
algebraic space and `F` representable by algebraic spaces, surjective, flat and locally of finite
presentation. Let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be a family of scheme-valued points of `𝒴`
indexed by a type of cardinality below the cofinality of the site's size cutoff which is jointly
surjective on objects, and let every member be limit preserving on objects and formally smooth on
objects. Then `𝒴` is an algebraic stack.

Representability of the diagonal of `𝒴` is **Stacks 05XW**,
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_flatPresentation`, applied to the
presentation; the family is then consumed by
`AlgebraicGeometry.Stack.isAlgebraicStack_of_jointlySurjective_forall_onObjects`, which glues it
into one scheme-valued point of `𝒴` out of the coproduct of the `Z i` and asks nothing of that
point.

Joint surjectivity is the form in which the source's cover is surjective: the degree of the
finite locally free subscheme produced over a field object varies with the field object
(`AlgebraicGeometry.Stack.FiniteHilbert.ExistsLciQuintupleOverField`), so the loci
`𝓗_{d, lci}(𝒳/𝒴)` cover `𝒴` jointly and no single one of them covers it. -/
theorem isAlgebraicStack_of_flatPresentation_of_jointlySurjective_family
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒳 ⟶ 𝒴)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hFprops : ∀ (V : BigFppfOver B S hS)
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
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hsurj : IsJointlySurjectiveOnObjects B S hS
      (fun i => (schemeFibredCategory B S hS (Z i)).val.p) 𝒴.val.p
      (fun i => CatFiberedInGroupoids.homFunctor (f i)))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i))
    (hlim : ∀ i, BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_jointlySurjective_forall_onObjects.{u, w} B S hS hstack
    (hasRepresentableDiagonal_of_flatPresentation.{u, u + 1, u + 1} B S hS F hstack h𝒳 hF
      (fun V y hy G hG h => (hFprops V y hy G hG h).1)
      (fun V y hy G hG h => (hFprops V y hy G hG h).2.1)
      (fun V y hy G hG h => (hFprops V y hy G hG h).2.2))
    hI Z f hsurj hlim hsm

/-- **Clauses (1) and (2) of Stacks 06DC, with the cover read as a family of scheme-valued points
one of which is surjective on objects.** This is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation_of_jointlySurjective_family` at a
family one of whose members is surjective on objects, which is jointly surjective on objects by
`AlgebraicGeometry.Stack.isJointlySurjectiveOnObjects_of_member`. -/
theorem isAlgebraicStack_of_flatPresentation_of_schemePointFamily
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒳 ⟶ 𝒴)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hFprops : ∀ (V : BigFppfOver B S hS)
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
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴) (i₀ : I)
    (hsurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS (Z i₀)).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor (f i₀)))
    (hsm : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i))
    (hlim : ∀ i, BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_flatPresentation_of_jointlySurjective_family.{u, w} B S hS F hstack h𝒳 hF
    hFprops hI Z f (isJointlySurjectiveOnObjects_of_member B S hS _ _ _ i₀ hsurj) hsm hlim

end AlgebraicGeometry.Stack

end
