module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# Algebraic stacks presented by a smooth groupoid in algebraic spaces

Let `S` be a scheme contained in a big fppf site. From a smooth groupoid in algebraic spaces
`G = (U, R, s, t, c)` over an algebraic space over `S` this file builds the construction the section
**Stacks 04TJ** is about: the quotient stack `[U/R]` of Stacks 044Q together with its algebraicity,
bundled as a single object. Algebraicity is Stacks 04TK
(`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`).
The bundling is not into the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP:
that is built on `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, whereas a quotient
stack is a stackification and so has hom sets one universe up.

The étale criterion for an algebraic stack (Stacks 076V), whose proof passes through the
quotient stack of a smooth groupoid, is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale_of_smoothAtlas` in
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleStackCriterion`.

## Main definitions

* `AlgebraicGeometry.Stack.LargeAlgebraicStack`: an algebraic stack over `S` at the universes a
  quotient stack lives at.
* `AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack`: **Stacks 04TJ**.

## Main results

* `AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack_val`: its underlying category over the
  site is the quotient stack.
* `AlgebraicGeometry.Stack.isStackInGroupoids_quotientStack_of_isSmooth`: the stack clause and
  the diagonal clause of Stacks 026O for the quotient stack of a smooth groupoid, which are the
  section's Lemma 94.17.1 and the stack clause of Stacks 044Q.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale`: algebraicity of an étale
  stack presented by a given groupoid in algebraic spaces.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04TJ](https://stacks.math.columbia.edu/tag/04TJ)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-! ### The algebraic stack associated to a smooth groupoid -/

section SmoothGroupoid

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}

/-- An algebraic stack over `S` at the universes the quotient stack of a groupoid in algebraic
spaces lives at: a category fibred in groupoids over the big fppf site of `S` together with the
proof that it is an algebraic stack in the sense of Stacks 026O.

The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP is this subtype at the
object and morphism universes `u` and `u + 1`; a quotient stack is a stackification, so its hom
sets are not small and it lives one universe up. -/
abbrev LargeAlgebraicStack (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :=
  { 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) //
    IsAlgebraicStack.{u, w} C S hS 𝒳.val }

/-- **Stacks 04TJ.** The algebraic stack associated to a smooth groupoid in algebraic spaces
`G = (U, R, s, t, c)` over an algebraic space over `S`: the quotient stack `[U/R]` of Stacks
044Q, fibred in groupoids over the big fppf site of `S`, together with the proof that it is an
algebraic stack over `S`.

The underlying category over the site is the quotient stack on the nose
(`AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack_val`); the algebraicity component is
Stacks 04TK. -/
@[stacks 04TJ "the section's construction: the algebraic stack associated to a smooth groupoid \
in algebraic spaces, as one object bundling the quotient stack with its algebraicity. The \
quotient stack and its fibredness in groupoids are Stacks 044Q; algebraicity is Stacks 04TK"]
noncomputable def smoothGroupoidAlgebraicStack
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    LargeAlgebraicStack.{u, w} C S hS :=
  ⟨CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G),
    isAlgebraicStack_quotientStack_of_isSmooth.{u, w} hG⟩

/-- The category over the site underlying the algebraic stack of a smooth groupoid is the
quotient stack of Stacks 044Q. -/
theorem smoothGroupoidAlgebraicStack_val
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (smoothGroupoidAlgebraicStack.{u, w} hG).val.val = quotientStack G :=
  rfl

/-- The quotient stack of a smooth groupoid in algebraic spaces is a stack in groupoids for the
fppf topology, and its diagonal is representable by algebraic spaces: the two clauses of Stacks
026O that the section's Lemma 94.17.1 and the stack clause of Stacks 044Q supply, read off the
algebraic stack of `AlgebraicGeometry.Stack.smoothGroupoidAlgebraicStack`. -/
theorem isStackInGroupoids_quotientStack_of_isSmooth
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    (quotientStack G).p.IsStackInGroupoids.{w} (BigFppfOver.topology C S hS) ∧
      ∃ h : (quotientStack G).p.IsFiberedInGroupoids,
        IsRepresentableByAlgebraicSpaces C S hS
          (diagonalBasedFunctor C S hS (CatFiberedInGroupoids.mk (quotientStack G) h)) := by
  obtain ⟨h, hst, hd, -⟩ := isAlgebraicStack_quotientStack_of_isSmooth.{u, w} hG
  exact ⟨hst.2, h, hd⟩

end SmoothGroupoid

/-! ### The étale criterion for an algebraic stack -/

section EtaleCriterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale stack in groupoids `𝒳` over the big fppf site of `S`, with diagonal representable by
algebraic spaces and a surjective smooth scheme atlas `f : (Sch/U) ⟶ 𝒳`, is an algebraic stack,
given in addition a groupoid in algebraic spaces `G` whose arrow space represents the
self-intersection of `f` (`_eR`), whose object space is the space `U` represents (`_hobjects`), and
whose quotient stack is equivalent to `𝒳` over the site (`e`). The fppf stack clause is transported
from the quotient stack (Stacks 044Q) along `e` (Stacks 042W).

The extra data are not needed: Stacks 076V, with exactly the source's hypotheses, is
`AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale_of_smoothAtlas`, which
constructs the self-intersection groupoid itself (Stacks 04T4 (1) is
`AlgebraicGeometry.Stack.SelfIntersection.isRepresentableByAlgebraicSpace_relation`). -/
theorem isAlgebraicStack_of_isStackInGroupoids_etale
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (hstack : 𝒳.p.IsStackInGroupoids.{w} ((etaleTopology B).over (B.obj hS)))
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor B S hS (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids)))
    (U : BigFppfOver B S hS)
    (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳)
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfprop : ∀ (V : BigFppfOver B S hS)
        (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
        (_hy : y ⋙ 𝒳.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let g := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g))
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (_eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS U)
        (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids) f).val.p
      (presheafOfCategories (G.arrows.obj ⋙ typeToCat)).p)
    (_hobjects : G.objects = Space.representedAlgebraicSpace B S hS U)
    (e : BasedCategory.Equivalence (quotientStack G) 𝒳) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  have hX : 𝒳.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence e (BigFppfOver.topology B S hS)).mp
      (isStack_quotientStack G)
  exact ⟨hstack.isFiberedInGroupoids,
    ⟨hX, hX.isStackInGroupoids hstack.isFiberedInGroupoids⟩, hdiag, U, f, hfrep, hfprop⟩

end EtaleCriterion

end AlgebraicGeometry.Stack

end
