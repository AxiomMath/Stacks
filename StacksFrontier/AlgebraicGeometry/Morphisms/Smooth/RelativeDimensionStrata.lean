module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import
  StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimensionOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness

/-!
# A smooth morphism is smooth of relative dimension `d` over its `d`-dimensional locus

For a smooth morphism `g : P ⟶ Y`, the canonical open and closed loci of relative dimension `d`
of [Stacks, Tag 02NM] (`AlgebraicGeometry.relativeDimensionOpen`; the fibres of a smooth morphism
are Cohen–Macaulay) are those on which `g` is smooth of relative dimension `d`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {P Y : Scheme.{u}} (g : P ⟶ Y) [Smooth g]

/-- **A smooth morphism is smooth of relative dimension `d` on its `d`-dimensional locus.** -/
theorem smoothOfRelativeDimension_relativeDimensionOpen (d : ℕ) :
    SmoothOfRelativeDimension d
      ((relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) d).ι ≫ g) := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ d fun x => ?_
  rw [fiberDimensionAt_eq_of_open_square
    (relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) d).ι g
    ((relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) d).ι ≫ g) (𝟙 Y)
    (Category.comp_id _).symm x,
    relativeDimensionFunction_apply g (isCohenMacaulay_fiber_of_smooth g)]
  exact congrArg (fun k : ℕ => (k : WithBot ℕ∞))
    ((mem_relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) d x.1).1 x.2)

end AlgebraicGeometry
