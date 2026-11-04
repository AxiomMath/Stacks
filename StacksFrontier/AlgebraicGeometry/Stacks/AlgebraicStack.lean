module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid

/-!
# Algebraic stacks (Stacks 026O, 03YP)

An *algebraic stack* over a scheme `S` contained in a big fppf site is a category fibred in
groupoids over the big fppf site of `S` which is a stack for the fppf topology, whose
diagonal is representable by algebraic spaces, and which has a presentation by a scheme: a
1-morphism from the category represented by a scheme over `S`, representable by algebraic spaces,
which is surjective and smooth. Algebraic stacks over `S` form a full sub-2-category of the
2-category of categories fibred in groupoids over the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.Stack.IsAlgebraicStack`: **Stacks 026O**.
* `AlgebraicGeometry.Stack.AlgebraicStacks`: **Stacks 03YP**, the 2-category of algebraic stacks
  over `S`.

## Main results

* `AlgebraicGeometry.Stack.isStackInGroupoids_of_isAlgebraicStack`: the family-indexed rendering
  of the stack condition for an algebraic stack, i.e. the second conjunct of its stack clause.

## Implementation notes

The first clause of the definition supplies the fibred-in-groupoids structure that the diagonal
and the atlas are formed with, so it is existentially quantified ahead of the other three; the
remaining clauses are stated for the bundled `CategoryTheory.CatFiberedInGroupoids` it produces.
The diagonal is `AlgebraicGeometry.Stack.diagonalBasedFunctor`, i.e. the 1-morphism to the 2-fibre
self-product over the identity, so the second clause is condition (1) of Stacks 045G
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff`).

Surjectivity and smoothness of the presentation are the relative-property condition of Stacks 03YK
written out for those two properties together: they are tested on every algebraic space
representing the base change of the presentation along a scheme-valued point of the stack, read as
a morphism of algebraic spaces over `S` by `AlgebraicGeometry.algebraicSpaceMap`. Passing from an
algebraic space over the scheme-valued point `V` to one over `S` is the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG; only that functor is needed, not
the full equivalence, which is why the definition is available although Stacks 03I5 part (1) is
not.

The stack clause is the conjunction of the sieve-indexed `CategoryTheory.Functor.IsStack` of
Stacks 026F with the family-indexed `CategoryTheory.Functor.IsStackInGroupoids` of Stacks 02ZI at
the descent universe `w`. The second conjunct follows from the first by
`CategoryTheory.Functor.IsStack.isStackInGroupoids` (the implication 026F ⟹ 02ZI of Stacks 02ZJ)
applied to the fibred-in-groupoids witness the definition already quantifies over, so the
predicate does not depend on `w`; it is retained because Lean admits no unused universe
parameter, and dropping `w` would change the universe signature of this definition and of
`AlgebraicGeometry.Stack.AlgebraicStacks`, so that every statement written at a free descent
universe would stop elaborating. The sieve-indexed conjunct is the one a consumer wants: it is
what `CategoryTheory.Functor.IsStackInSetoids` contains, and the converse implication
`CategoryTheory.Functor.isStack_of_isStackInGroupoids` is available only at the index universe
`max u₁ v₁`, which over the big fppf site is `u + 1`.

The object and morphism universes of the total category of the stack are independent of those of
the site, and 1-morphisms are `CategoryTheory.BasedFunctor`s, so the presenting scheme retains the
universes of the site. The universe arguments of
`AlgebraicGeometry.Stack.IsAlgebraicStack` are, in order, the scheme universe, the descent
universe of the second conjunct of the stack condition, and then the stack's morphism and object
universes.

Both definitions are abbreviations: the three defining clauses and the presentation data of
`IsAlgebraicStack` are directly available to a downstream statement, and the induced-bicategory
API of `AlgebraicGeometry.Stack.AlgebraicStacks` applies to its 1-morphisms and 2-morphisms
without unfolding.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

/-- **Stacks 026O.** A category over the big fppf site of `S` is an *algebraic stack* when it is
fibred in groupoids, is a stack for the fppf topology, has a diagonal representable
by algebraic spaces, and has a presentation by a scheme: a 1-morphism from the category
represented by a scheme `U` over `S`, representable by algebraic spaces, which is surjective and
smooth in the sense that every algebraic space representing its base change along a scheme-valued
point of the stack has surjective and smooth structural morphism.

The stack clause is a conjunction of the two renderings of Stacks 02ZJ, the sieve-indexed
`CategoryTheory.Functor.IsStack` of Stacks 026F and the family-indexed
`CategoryTheory.Functor.IsStackInGroupoids` of Stacks 02ZI at the descent universe `w`. The
second conjunct is a consequence of the first — see the implementation notes. -/
@[stacks 026O]
abbrev IsAlgebraicStack.{u, w, v, t}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) : Prop :=
  ∃ (h𝒳 : 𝒳.p.IsFiberedInGroupoids),
    let 𝒳' := CatFiberedInGroupoids.mk 𝒳 h𝒳
    (𝒳.p.IsStack (BigFppfOver.topology B S hS) ∧
        𝒳.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS)) ∧
    IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳') ∧
      ∃ (U : BigFppfOver B S hS)
        (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳'.val),
        IsRepresentableByAlgebraicSpaces B S hS f ∧
          ∀ (V : BigFppfOver B S hS)
            (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
            (_hy : y ⋙ 𝒳.p = Over.map V.hom)
            (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
            (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (TwoFibreProductOver.fst (Over.map V.hom)
                (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
              (presheafOfCategories (F ⋙ typeToCat)).p) →
              (let g := (algebraicSpaceMap B S hS V
                ((spacesOverSmallerBaseFunctor
                  B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
               Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)

/-- **Stacks 03YP.** The 2-category of algebraic stacks over `S`: the full sub-2-category of the
2-category of categories fibred in groupoids over the big fppf site of `S` whose objects are the
algebraic stacks. Its 1-morphisms and 2-morphisms are those of the ambient 2-category, with no
further condition. -/
@[stacks 03YP]
abbrev AlgebraicStacks.{u, w}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  Bicategory.InducedBicategory
    (CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (Subtype.val (p := fun 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS) ↦ IsAlgebraicStack.{u, w} B S hS 𝒳.val))

/-- **The family-indexed stack condition of Stacks 02ZI for an algebraic stack**, at the descent
universe `w` of the predicate: the second conjunct of the stack clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`.

This is the form in which the stack clause was stated before the sieve-indexed conjunct was
added, kept available as a lemma so that no consumer loses a statement. -/
theorem isStackInGroupoids_of_isAlgebraicStack.{u, w, v, t}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    𝒳.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS) := by
  obtain ⟨-, hst, -⟩ := h𝒳
  exact hst.2

end AlgebraicGeometry.Stack

end
