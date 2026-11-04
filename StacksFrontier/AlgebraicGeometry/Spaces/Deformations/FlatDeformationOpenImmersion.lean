module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion

/-!
# Open immersions under a flat deformation of algebraic spaces (Stacks 0CGX, part (4))

Let `AlgebraicGeometry.Space.FlatDeformationDiagram` be a flat deformation `f' : X' → Y'` over
`B'` of a morphism `f : X → Y` of algebraic spaces over `B`. Then `f` is an open immersion
exactly when `f'` is.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_iff_of_flatDeformationDiagram`: `f` is an open
  immersion if and only if `f'` is.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being an open immersion is invariant under a flat deformation of algebraic spaces: `f` is an
open immersion if and only if `f'` is. -/
@[stacks 0CGX "part (4): open immersion"]
theorem isOpenImmersion_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsOpenImmersion B S hS D.f.hom ↔ IsOpenImmersion B S hS D.f'.hom := by
  refine ⟨fun hf ↦ ?_, fun hf' ↦ ?_⟩
  · exact isOpenImmersion_of_isEtale_of_universallyInjective B S hS D.X'.property
      D.Y'.property D.f'.hom
      ((isEtale_iff_of_flatDeformationDiagram B S hS D).mp
        (isEtale_of_isOpenImmersion B S hS hf))
      ((universallyInjective_iff_of_flatDeformationDiagram B S hS D).mp
        (universallyInjective_of_mono B S hS D.f.hom (mono_of_isOpenImmersion B S hS D.f.hom hf)))
  · exact isOpenImmersion_of_isPullback B S hS
      (D.isPullback_X.of_bot D.comm_f D.isPullback_Y) hf'

end AlgebraicGeometry.Space

end
