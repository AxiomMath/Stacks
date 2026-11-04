module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesIsomFinitePresentationProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicStackProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStructureMorphismQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesToBaseLimitPreservingOnObjects

/-!
# `Complexes_{X/B} → B` is quasi-separated and locally of finite presentation (Stacks 0DPX)

In Situation 0DLE (`f : X ⟶ B` proper, flat and of finite presentation), the morphism
`Complexes_{X/B} → B` is quasi-separated and locally of finite presentation. Both properties belong
to 1-morphisms of algebraic stacks, so the statement is made at the structure morphism
`AlgebraicGeometry.Space.ComplexesSituation.complexesStructureMorphism D h`, which needs `h`, the
algebraicity of `Complexes_{X/B}` (Stacks 0DLN), to be formed at all; it is Stacks 0DLN,
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_proved`. Both properties
also hold for any algebraicity witness `h`.

## Main results

* `isQuasiSeparated_complexesStructureMorphism`: quasi-separatedness, given `h`.
* `isQuasiSeparated_and_isLocallyOfFinitePresentation_complexesStructureMorphism`: the two
  properties for any algebraicity witness `h`.
* `isQuasiSeparated_and_isLocallyOfFinitePresentation_complexesAlgebraicStack`: the two properties
  for the algebraic stack of Stacks 0DLN.

## References

* [Stacks Project, Tag 0DPX](https://stacks.math.columbia.edu/tag/0DPX)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If `Complexes_{X/B}` is an algebraic stack (witnessed by `h`), the structure morphism
`Complexes_{X/B} → B` is quasi-separated. -/
theorem isQuasiSeparated_complexesStructureMorphism (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D)) :
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS (complexesStructureMorphism D h) :=
  isQuasiSeparated_complexesStructureMorphism_of_isom D h
    (fun A E' h₁ h₂ => isFinitePresentationAlgebraicSpaceOver_complexesIsom_proved A E' h₁ h₂)

/-- In Situation 0DLE (`f : X ⟶ B` proper, flat and of finite presentation), if `Complexes_{X/B}`
is an algebraic stack (witnessed by `h`), the morphism `Complexes_{X/B} → B` is quasi-separated and
locally of finite presentation. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_complexesStructureMorphism
    (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D)) :
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS (complexesStructureMorphism D h) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (complexesStructureMorphism D h) :=
  ⟨isQuasiSeparated_complexesStructureMorphism D h,
    isLocallyOfFinitePresentation_complexesStructureMorphism D h⟩

/-- In Situation 0DLE (`f : X ⟶ B` proper, flat and of finite presentation), the morphism
`Complexes_{X/B} → B` is quasi-separated and locally of finite presentation. Here `Complexes_{X/B}`
is the algebraic stack given by `isAlgebraicStack_complexes_proved`, taken through its small model,
and `B` is the algebraic stack of its category of elements. -/
@[stacks 0DPX]
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_complexesAlgebraicStack
    (D : ComplexesSituation B S hS) :
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS
        (complexesStructureMorphism D (isAlgebraicStack_complexes_proved.{u, w} hS D)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (complexesStructureMorphism D (isAlgebraicStack_complexes_proved.{u, w} hS D)) :=
  isQuasiSeparated_and_isLocallyOfFinitePresentation_complexesStructureMorphism D
    (isAlgebraicStack_complexes_proved hS D)

end AlgebraicGeometry.Space.ComplexesSituation

end
