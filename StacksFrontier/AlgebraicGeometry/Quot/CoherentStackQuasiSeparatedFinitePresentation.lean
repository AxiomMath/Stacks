module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDiagonalAffineFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackToBaseLimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.ShrinkHomsLimitPreserving

/-!
# The stack of coherent sheaves is quasi-separated and locally of finite presentation (Stacks 0DLZ)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is of
finite presentation, the standing data of Stacks 08KB, and let `Coh_{X/B} ⟶ B` be the projection
which forgets the module. **Stacks 0DLZ**: this morphism is quasi-separated and locally of finite
presentation.

## Main results

* `CoherentSituation.isFiberedQuasiSeparated_and_isLocallyOfFinitePresentation_toBaseCFG`: the
  projection `Coh_{X/B} ⟶ B` is quasi-separated and locally of finite presentation.

## Implementation notes

The morphisms of `Coh_{X/B}` are morphisms of sheaves of modules, so its total category has hom
types one universe above those of the site; it is not an object of the 2-category
`AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP, whose total categories have their hom
types in the universe of the site. The two properties are therefore stated as follows, in forms
which agree with Stacks 04YW and Stacks 06Q2 on algebraic stacks.

* Quasi-separatedness is `AlgebraicGeometry.Stack.IsFiberedQuasiSeparated`: the relative
  diagonal is representable by algebraic spaces, quasi-compact and quasi-separated in the sense of
  Properties of Stacks, Section 04XB. For a 1-morphism of algebraic stacks this is Stacks 04YW
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_isFiberedQuasiSeparated`).
* Local finite presentation is part (1) of Stacks 06Q2, the universal smooth-diagram test of
  Stacks 06FM at local finite presentation of morphisms of algebraic spaces
  (`AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram`), applied to the 1-morphism of small
  models `AlgebraicGeometry.Stack.smallHomsModelMap` induced by the projection: `Coh_{X/B}` and
  `𝒮_B` are locally small, and their small models are equivalent to them over the site. For an
  algebraic stack the small model is the one through which it is an object of
  `AlgebraicGeometry.Stack.AlgebraicStacks`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`), and the test is then
  `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`.

The source assumes `f` separated as well, for the algebraicity of `Coh_{X/B}`; the statement
here does not need it.

## References

* [Stacks Project, Tag 0DLZ](https://stacks.math.columbia.edu/tag/0DLZ)
* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The category `𝒮_Y` of test schemes over `Y` is locally small** at the universe of the site:
its morphisms are those of the test schemes over `Y`, lifted along `CategoryTheory.ULiftHom`. -/
theorem locallySmall_baseCFG (Y : AlgebraicSpaces B S hS) :
    LocallySmall.{u} (baseCFG Y).val.obj where
  hom_small _ _ := inferInstanceAs (Small.{u} (ULift _))

namespace CoherentSituation

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation. Then the morphism
`Coh_{X/B} ⟶ B` is quasi-separated and locally of finite presentation.

Quasi-separatedness is `AlgebraicGeometry.Stack.IsFiberedQuasiSeparated`, Stacks 04YW for a
1-morphism of categories fibred in groupoids; local finite presentation is part (1) of Stacks 06Q2
for the induced 1-morphism of small models (`AlgebraicGeometry.Stack.smallHomsModelMap`), the
hom types of `Coh_{X/B}` lying one universe above those of the site. See the implementation notes
of the file. -/
@[stacks 0DLZ "quasi-separated as Stacks 04YW for a 1-morphism of categories fibred in groupoids; \
locally of finite presentation as Stacks 06Q2 (1) for the small models, Coh_{X/B} having its hom \
types one universe above the site"]
theorem isFiberedQuasiSeparated_and_isLocallyOfFinitePresentation_toBaseCFG
    (D : CoherentSituation B S hS) :
    Stack.IsFiberedQuasiSeparated.{u, u + 1, u + 1} B S hS D.toBaseCFG ∧
      letI := locallySmall_coherentCFG D
      letI := locallySmall_baseCFG D.Y
      Stack.HasPropertyOnEverySmoothDiagram B S hS
        (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
        (Stack.smallHomsModelMap D.toBaseCFG) := by
  let := locallySmall_coherentCFG D
  let := locallySmall_baseCFG D.Y
  exact ⟨D.isFiberedQuasiSeparated_toBaseCFG,
    Stack.hasPropertyOnEverySmoothDiagram_smallHomsModelMap_of_isLimitPreservingOnObjects _
      D.isLimitPreservingOnObjects_toBaseCFG⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
