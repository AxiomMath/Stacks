module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmoothOfAlgebraic

/-!
# The structure morphism `Complexes_{X/B} ⟶ B` as a 1-morphism of algebraic stacks (towards 0DPX)

Let `f : X ⟶ B` be a proper, flat, finitely presented morphism of algebraic spaces over a scheme
`S` (Situation 0DLE), and suppose `Complexes_{X/B}` is an algebraic stack (Stacks 0DLN). Stacks
0DPX says that the structure morphism `Complexes_{X/B} ⟶ B` is quasi-separated and locally of
finite presentation.

The 2-category of algebraic stacks of Stacks 03YP is formed at the universes of the site, while
the hom types of `Complexes_{X/B}` lie one universe up, so `Complexes_{X/B}` enters it through its
small model (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`), and `B` through its category
of elements (Stacks 0458). The structure morphism between them is the projection
`Complexes_{X/B} ⟶ 𝒮_B` of Remark 0DLI composed with the two comparisons, exactly as for the
Picard stack (`AlgebraicGeometry.Space.picardStructureMorphism`).

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.complexesCFG`: `Complexes_{X/B}` as a category
  fibred in groupoids (Stacks 0DLF).
* `AlgebraicGeometry.Space.ComplexesSituation.complexesToBaseCFG`: the projection
  `Complexes_{X/B} ⟶ 𝒮_B` of Remark 0DLI as a 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesAlgebraicStack`: the small model of
  `Complexes_{X/B}`, given its algebraicity.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesStructureMorphism`: the structure morphism
  `Complexes_{X/B} ⟶ B` as a 1-morphism of algebraic stacks.

## References

* [Stacks Project, Tag 0DPX](https://stacks.math.columbia.edu/tag/0DPX)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`Complexes_{X/B}` as a category fibred in groupoids** over the big fppf site of `S`
(Stacks 0DLF). -/
abbrev complexesCFG (D : ComplexesSituation B S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (complexesBasedCategory D) (complexesFunctor_isFiberedInGroupoids D)

/-- **The projection `Complexes_{X/B} ⟶ 𝒮_B` of Remark 0DLI**, `(T, g, E) ↦ (T, g)`, as a
1-morphism of categories fibred in groupoids. -/
abbrev complexesToBaseCFG (D : ComplexesSituation B S hS) : complexesCFG D ⟶ baseCFG D.Y :=
  Bicategory.InducedBicategory.mkHom (complexesToBase D)

/-- **`Complexes_{X/B}` as an object of the 2-category of algebraic stacks**, given that it is an
algebraic stack (Stacks 0DLN): its small model. -/
abbrev complexesAlgebraicStack (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D)) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  Stack.AlgebraicStacks.smallModel B S hS _ h

/-- **The structure morphism `Complexes_{X/B} ⟶ B` as a 1-morphism of algebraic stacks**: the
projection `Complexes_{X/B} ⟶ 𝒮_B` of Remark 0DLI, read on the small model of `Complexes_{X/B}`
and on the category of elements of `B`. -/
def complexesStructureMorphism (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D)) :
    complexesAlgebraicStack D h ⟶ baseAlgebraicStack.{u, w} D.Y :=
  Bicategory.InducedBicategory.mkHom
    ((shrinkHomsComparison (complexesCFG D) h).conj (complexesToBaseCFG D)
      (testSchemesToElementsComparison D.Y))

end AlgebraicGeometry.Space.ComplexesSituation

end
