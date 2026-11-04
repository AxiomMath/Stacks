module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Separated
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological

/-!
# Properties of a flat deformation diagram that only depend on the thickenings

Quasi-compactness, universal closedness, (quasi-)separatedness, surjectivity, universal
injectivity and universal openness of the morphism between the special fibres of a flat
deformation diagram agree with the same properties of its ambient deformation.

Each of these properties depends only on the underlying topology of the morphism after base
change, and the two inclusions of a flat deformation diagram are thickenings, hence universal
homeomorphisms. The equivalences are therefore instances of the corresponding statements for an
arbitrary morphism of thickenings (Tag 09ZV), applied to the commutative square formed by the two
inclusions and the two horizontal morphisms; the flatness, finiteness and cartesian hypotheses of
the diagram are not used.

## Main definitions

* `Stacks.Thickenings.FlatDeformationDiagram.arrowHom`: the square of a flat deformation diagram,
  as a morphism in the arrow category from the source inclusion to the target inclusion.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.quasiCompact_iff`
* `Stacks.Thickenings.FlatDeformationDiagram.universallyClosed_iff`
* `Stacks.Thickenings.FlatDeformationDiagram.separated_and_quasiSeparated_iff`
* `Stacks.Thickenings.FlatDeformationDiagram.surjective_iff`
* `Stacks.Thickenings.FlatDeformationDiagram.universallyInjective_iff`
* `Stacks.Thickenings.FlatDeformationDiagram.universallyOpen_iff`

## References

* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings.FlatDeformationDiagram

variable (D : FlatDeformationDiagram.{u})

/-- The commutative square of a flat deformation diagram, as a morphism in the arrow category from
the source inclusion to the target inclusion, with left component `f` and right component
`f'`. -/
abbrev arrowHom : Arrow.mk D.iX ⟶ Arrow.mk D.iY :=
  Arrow.homMk D.f D.f' D.comm_f.symm

/-- Quasi-compactness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "quasi_compact"]
theorem quasiCompact_iff : QuasiCompact D.f ↔ QuasiCompact D.f' :=
  quasiCompact_left_iff_right D.arrowHom D.iX_thickening D.iY_thickening

/-- Universal closedness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "universally_closed"]
theorem universallyClosed_iff : UniversallyClosed D.f ↔ UniversallyClosed D.f' :=
  universallyClosed_left_iff_right D.arrowHom D.iX_thickening D.iY_thickening

/-- Separatedness and quasi-separatedness are each invariant under a flat deformation
diagram. -/
@[stacks 0CF4 "separated"]
theorem separated_and_quasiSeparated_iff :
    (IsSeparated D.f ↔ IsSeparated D.f') ∧ (QuasiSeparated D.f ↔ QuasiSeparated D.f') :=
  ⟨isSeparated_left_iff_right D.iX_thickening D.iY_thickening D.arrowHom,
    quasiSeparated_left_iff_right D.arrowHom D.iX_thickening D.iY_thickening⟩

/-- Surjectivity is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "surjective"]
theorem surjective_iff : Surjective D.f ↔ Surjective D.f' :=
  surjective_left_iff_right D.iX_thickening D.iY_thickening D.arrowHom

/-- Universal injectivity is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "universally_injective"]
theorem universallyInjective_iff : UniversallyInjective D.f ↔ UniversallyInjective D.f' :=
  universallyInjective_left_iff_right D.iX_thickening D.iY_thickening D.arrowHom

/-- Universal openness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "universally_open"]
theorem universallyOpen_iff : UniversallyOpen D.f ↔ UniversallyOpen D.f' :=
  universallyOpen_left_iff_right D.iX_thickening D.iY_thickening D.arrowHom

end Stacks.Thickenings.FlatDeformationDiagram

end
