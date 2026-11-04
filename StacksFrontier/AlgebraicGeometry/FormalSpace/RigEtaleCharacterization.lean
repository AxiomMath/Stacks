module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic

/-!
# Characterising rig-étale morphisms of formal algebraic spaces on affine charts

Rig-étaleness of a morphism of formal algebraic spaces over a scheme `S` is a condition on its
affine charts, and the local-property machinery of **Stacks 0ANG** which tests such conditions
takes a property of arrows of a class of topological rings. This file reads rig-étaleness of a
homomorphism in that shape.

That Definition 0AQM *is* the chart-tested condition of Stacks 0ANG for the class of Noetherian
adic topological rings and rig-étaleness is
`AlgebraicGeometry.FormalSpace.isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability`, and **Stacks 0GCZ**, the
equivalence of Definition 0AQM with that condition and with its two covering forms, is
`AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian'` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts`.

## Main definitions

* `TopologicalRing.IsRigEtaleHom`: rig-étaleness of an arrow of `WAdm^{Noeth}`, in the shape
  in which the local-property machinery of Stacks 0ANG takes a property of arrows.

## References

* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- Rig-étaleness of a homomorphism of topological rings, read as a property of arrows of
`WAdm^{Noeth}`. This is the shape in which the local-property machinery of Stacks 0ANG takes a
property of arrows: the Noetherian and linear-topology instances that Definition 0GCV needs
are quantified over inside `RingHom.IsRigEtaleArrow`, since the chart-tested condition
supplies them as hypotheses rather than as instances. -/
abbrev IsRigEtaleHom {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    (φ : R₁ →+* R₂) : Prop :=
  RingHom.IsRigEtaleArrow φ

end TopologicalRing

end
