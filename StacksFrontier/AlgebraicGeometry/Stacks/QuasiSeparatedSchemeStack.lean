module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented

/-!
# A scheme with quasi-separated underlying space is quasi-separated over the base

For `T` an object of the big fppf category of `S` whose underlying scheme is quasi-separated — in
particular for an affine `T` — the stack `T` represents is quasi-separated over `S` in the sense
of Stacks 050D part (4), with no hypothesis on `S`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack`: the stack represented by an object
  of the site whose underlying scheme is a quasi-separated topological space is quasi-separated
  over `S`.
* `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine`: the same for an object
  with affine underlying scheme, affine schemes being quasi-separated.

## References

* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stack represented by an object `T` of the site whose underlying scheme is a
quasi-separated topological space is quasi-separated over `S`, in the sense of Stacks 050D
part (4). There is no hypothesis on `S`. -/
theorem isQuasiSeparatedOver_schemeStack (T : BigFppfOver B S hS)
    (hT : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiSeparatedOver.{u, w} B S hS (schemeStack.{u, w} B S hS T) := by
  have hrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
    (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property
    ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T,
      ⟨PresheafOfCategories.sliceElementsEquivalenceOver T⟩⟩
    (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)).hom
  have hstep : IsQuasiSeparated.{u, u, u + 1} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)).hom := by
    refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.quasiSeparatedProperty B S hS)
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)).hom hrep
      (yoneda.obj T) (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
      (isAlgebraicSpace_yoneda B S hS T)
      (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))
      (PresheafOfCategories.sliceElementsEquivalenceOver T)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)).2 ?_
    have hk : representingMap B S hS (schemeStack.{u, w} B S hS T).val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (yoneda.obj T) (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
        (PresheafOfCategories.sliceElementsEquivalenceOver T)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)).hom =
        yoneda.map (Over.mkIdTerminal.from T) :=
      (Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _
    rw [hk]
    have := hT
    exact (Space.isQuasiSeparated_yoneda_map_iff B S hS (Over.mkIdTerminal.from T)).2
      inferInstance
  refine (AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S hS
    (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)) hrep).2 ?_
  exact (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS
    (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)) hrep).2 hstep

/-- The stack represented by an object of the site with affine underlying scheme is
quasi-separated over `S`. -/
theorem isQuasiSeparatedOver_schemeStack_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiSeparatedOver.{u, w} B S hS (schemeStack.{u, w} B S hS T) :=
  isQuasiSeparatedOver_schemeStack.{u, w} B S hS T (have := hT; inferInstance)

end AlgebraicGeometry.Stack

end
