module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentations
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsCofibered

/-!
# Continuity of a representation and the `A`-`G`-module condition

The objects of the category `ℱ` of Stacks 0D3K are triples `(A, M, ρ)` with `ρ : Γ → GL_A(M)`
continuous for the discrete topology on `GL_A(M)`. The footnote of that example records that
an alternative would have been to ask that `M`, with the action of `Γ` given by `ρ`, be an
`A`-`Γ`-module in the sense of Stacks 04JP, and that for a finite `A`-module the two
requirements agree.

This file proves that equivalence, between the condition cutting out
`Deformation.Examples.FiniteProjectiveRepresentation.continuousObjects` and the condition
defining `Stacks.GroupCohomology.ofRepresentation`.

## Main results

* `Deformation.Examples.isContinuousRepresentation_iff_isContinuous`: for a finite module over
  a commutative ring, a representation is continuous into the discrete general linear group if
  and only if the associated action makes the module an `A`-`Γ`-module of Stacks 04JP.

## Implementation notes

The `A`-`Γ`-module condition of Stacks 04JP is `CategoryTheory.Action.IsContinuous` of
`Stacks.GroupCohomology.actionOfRepresentation`, which is the object the Stacks 04JP
declarations are stated about; it is formed with the scoped forgetful functor giving a module
the discrete topology, so the scope `Stacks.DiscreteModuleTopology` is opened here.

Both conditions are reduced to openness of the stabilizer of every element, the left one by
`Deformation.Examples.continuous_representation_iff_continuousSMul` — which is where
finiteness of the module is used — and the right one by
`Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff`.

## References

* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

open scoped Stacks.DiscreteModuleTopology

universe u v w

/-- **The footnote of Stacks 0D3K.** For a finite module over a commutative ring, a
representation of a topological group is continuous into the general linear group with the
discrete topology exactly when the module, with the action given by the representation, is an
`A`-`Γ`-module in the sense of Stacks 04JP. -/
@[stacks 0D3K "continuity_equivalence"]
public theorem isContinuousRepresentation_iff_isContinuous
    {R : Type u} [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ρ : Representation R Γ M) :
    IsContinuousRepresentation ρ ↔
      (Stacks.GroupCohomology.actionOfRepresentation R Γ M ρ).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
  let : TopologicalSpace M := ⊥
  let : MulAction Γ M := MulAction.compHom M ρ.asGroupHom
  let : DiscreteTopology M := discreteTopology_bot _
  refine (continuous_representation_iff_continuousSMul R M Γ ρ.asGroupHom).trans ?_
  exact continuousSMul_iff_stabilizer_isOpen

end Deformation.Examples
