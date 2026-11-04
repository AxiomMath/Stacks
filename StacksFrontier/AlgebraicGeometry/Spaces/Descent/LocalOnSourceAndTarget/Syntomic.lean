module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.SmoothCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.SyntomicFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SyntomicSourceLocalityTransfer

/-!
# Syntomicity is smooth local on the source and target (Stacks 06FC)

Syntomicity of a morphism of algebraic spaces over a scheme `S` is smooth local on the
source-and-target in the sense of
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget` (**Stacks 06F8**). This is the
syntomic item of the list of **Stacks 06FC**.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_isSmoothLocalOnSourceAndTarget`: **Stacks 06FC**, the
  syntomic case.

## Implementation notes

What this module proves is the passage from the two localities of syntomicity to smooth
locality on the source-and-target: the smooth precoverage of **Stacks 03YH** is contained in
both the syntomic one (**Stacks 0DFB**) and the fpqc one (**Stacks 0DFQ**), so
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` and its target analogue turn the two
localities into the two hypotheses of the criterion
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget` (**Stacks 06FB**), and the
postcomposition hypothesis of that criterion follows from
`AlgebraicGeometry.Space.isSyntomic_comp` (**Stacks 03Z8**) together with
`AlgebraicGeometry.Space.isSyntomic_of_isSmooth`, a smooth morphism being syntomic.

Source locality for the syntomic precoverage is
`AlgebraicGeometry.Space.syntomic_isLocalAtSource_syntomic` (**Stacks 06F0**) and target
locality for the fpqc precoverage is
`AlgebraicGeometry.Space.syntomic_isLocalAtTarget_fpqc` (**Stacks 0428**); both are imported
instances.

## References

* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06FC**, the syntomic case. Syntomicity of morphisms of algebraic spaces over `S`
is smooth local on the source-and-target.

The source locality hypothesis of Stacks 06FB comes from the syntomic one, Stacks 06F0, along
`AlgebraicGeometry.Space.Topology.precoverage_smooth_le_syntomic`; the target locality one
comes from the fpqc one, Stacks 0428, along
`AlgebraicGeometry.Space.Topology.precoverage_smooth_le_fpqc`; and the postcomposition
hypothesis is composition of syntomic morphisms (Stacks 03Z8) applied to the fact that a
smooth morphism is syntomic. -/
@[stacks 06FC "syntomic"]
theorem isSyntomic_isSmoothLocalOnSourceAndTarget :
    IsSmoothLocalOnSourceAndTarget B S hS (fun _ _ f => IsSyntomic B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsSyntomic B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .syntomic B S hS) :=
    syntomic_isLocalAtSource_syntomic B S hS
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le (Topology.precoverage_smooth_le_syntomic B S hS)
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    syntomic_isLocalAtTarget_fpqc B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Topology.precoverage_smooth_le_fpqc B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    fun hX hY hZ f g hf hg =>
      isSyntomic_comp B S hS hX hY hZ f g hf (isSyntomic_of_isSmooth B S hS g hg)

end AlgebraicGeometry.Space

end
