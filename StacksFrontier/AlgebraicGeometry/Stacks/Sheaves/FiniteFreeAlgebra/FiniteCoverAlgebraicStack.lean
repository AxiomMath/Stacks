module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.AbsoluteOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationIsomSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationQuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FiniteCoverStructureConstants

/-!
# `ℋ_d` is an algebraic stack

Let `S` be a scheme of a big fppf site and let `d` be a positive integer. The category `ℋ_d` of
degree-`d` finite locally free covers over the big fppf site over `S` is an algebraic stack over
`S`, which is the second assertion of Stacks 05YQ. So is the quotient stack `[X/G]` of the
conjugation action of the unit-fixing subgroup `G ⊆ GL_d` on the scheme `X` of structure
constants.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_conjugationQuotientStack`: the quotient stack `[X/G]`
  of Stacks 05YQ is an algebraic stack over `S`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_finiteCoverFibered`: **the second assertion of
  Stacks 05YQ — `ℋ_d` is an algebraic stack over `S`.**

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- **The quotient stack `[X/G]` of Stacks 05YQ is an algebraic stack over `S`.** Here `G ⊆ GL_d`
is the unit-fixing subgroup, acting by conjugation on the scheme `X` of structure constants of
free `d`-dimensional algebras. -/
theorem isAlgebraicStack_conjugationQuotientStack :
    IsAlgebraicStack.{u, w} 𝒞 S hS
      (Space.structureConstantsQuotientStack 𝒞 S hS d (Space.terminalSpace 𝒞 S hS)) :=
  FiniteFreeAlgebra.isAlgebraicStack_quotientStack_of_ffaIso
    (FiniteFreeAlgebra.conjugationGroupoidInSpaces 𝒞 S hS d
      (FiniteFreeAlgebra.isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
      (FiniteFreeAlgebra.isAlgebraicSpace_conjugationObject 𝒞 S hS d))
    (FiniteFreeAlgebra.conjugationGroupoidIso 𝒞 S hS d)
    (Space.isSmooth_groupoidOfAction (Space.terminalSpace 𝒞 S hS)
      (Space.groupOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
        (Space.unitFixingPointsOnSite 𝒞 S hS d))
      (Space.objectOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
        (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)))
      (FiniteFreeAlgebra.isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
      (FiniteFreeAlgebra.isAlgebraicSpace_conjugationObject 𝒞 S hS d)
      (Space.isSmooth_groupOverStar_unitFixing 𝒞 S hS d (Space.terminalSpace 𝒞 S hS)))

/-- The category `ℋ_d` of degree-`d` finite locally free covers over the big fppf site over `S`
is an algebraic stack over `S`. -/
@[stacks 05YQ "the second assertion: `ℋ_d` is an algebraic stack over `S`, transported along \
the equivalence of the first assertion from the quotient stack `[X/G]` of the conjugation \
action, which is an algebraic stack by Stacks 04TK"]
theorem isAlgebraicStack_finiteCoverFibered :
    IsAlgebraicStack.{u, w} 𝒞 S hS (finiteCoverFibered 𝒞 S hS d).val := by
  obtain ⟨heq⟩ :=
    FiniteFreeAlgebra.nonempty_isEquivalenceOver_finiteCover_conjugationQuotient 𝒞 S hS d
  refine isAlgebraicStack_of_equivalenceOver 𝒞 S hS
    ((StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver ?_ heq).trans
      (Functor.equivalenceOver_uliftHom
        (finiteCoverProjection (B := 𝒞) (S := S) (hS := hS) (d := d))).symm)
    (isAlgebraicStack_conjugationQuotientStack 𝒞 S hS d)
  exact Functor.Stackification.extend_comp_eq _ _ _ _ _ _

end AlgebraicGeometry.Stack

end
