module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.SmoothCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSourceLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat

/-!
# Universal openness is smooth local on the source and target (Stacks 06FC)

A morphism of algebraic spaces over a scheme `S` being universally open (**Stacks 03Z2**,
part (2)) is a property which is smooth local on the source-and-target in the sense of
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget` (**Stacks 06F8**). This is the
universally open item of the list of **Stacks 06FC**.

## Main results

* `AlgebraicGeometry.Space.universallyOpen_isSmoothLocalOnSourceAndTarget`: **Stacks 06FC**,
  the universally-open case.

## Implementation notes

The two localities that **Stacks 06FC** cites for this item are exactly the two the criterion
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget` (**Stacks 06FB**) consumes, after
restriction along a containment of precoverages: universal openness is local on the source for
the fppf topology (**Stacks 06EY**, Lemma 74.16.4) and local on the target for the fpqc
topology (**Stacks 041P**, Lemma 74.11.4), while the smooth precoverage of **Stacks 03YH** is
contained in the fppf one (**Stacks 0DFC**) and in the fpqc one (**Stacks 0DFQ**). So
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` and its target analogue produce the two
smooth-topology hypotheses.

The postcomposition hypothesis of the criterion is composition of universally open morphisms
(**Stacks 03Z4**) applied to the fact that a smooth morphism of algebraic spaces is universally
open. The latter is not a single tag here: it is **Stacks 042S**, a flat morphism locally of
finite presentation being universally open, applied to a smooth morphism being flat
(**Stacks 04TA**) and locally of finite presentation (**Stacks 04AJ**).

## References

* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A smooth morphism of algebraic spaces over `S` is universally open: it is flat
(**Stacks 04TA**) and locally of finite presentation (**Stacks 04AJ**), and such a morphism is
universally open by **Stacks 042S**. -/
theorem universallyOpen_of_isSmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    UniversallyOpen B S hS f :=
  universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS hX hY f
    (isFlat_of_isSmooth B S hS f hf)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS hf)

/-- **Stacks 06FC**, the universally-open case. Being universally open is, for morphisms of
algebraic spaces over `S`, smooth local on the source-and-target.

The source locality hypothesis of Stacks 06FB comes from the fppf one, Stacks 06EY, along
`AlgebraicGeometry.Space.Topology.precoverage_smooth_le_fppf`; the target locality one comes
from the fpqc one, Stacks 041P, along
`AlgebraicGeometry.Space.Topology.precoverage_smooth_le_fpqc`; and the postcomposition
hypothesis is composition of universally open morphisms (Stacks 03Z4) applied to
`AlgebraicGeometry.Space.universallyOpen_of_isSmooth`. -/
@[stacks 06FC "universally open"]
theorem universallyOpen_isSmoothLocalOnSourceAndTarget :
    IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ f => UniversallyOpen B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => UniversallyOpen B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .fppf B S hS) :=
    universallyOpen_isLocalAtSource_fppf B S hS
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le (Topology.precoverage_smooth_le_fppf B S hS)
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    universallyOpen_isLocalAtTarget_fpqc B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Topology.precoverage_smooth_le_fpqc B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    fun hX hY hZ f g hf hg =>
      universallyOpen_comp B S hS hX hY hZ f g hf
        (universallyOpen_of_isSmooth B S hS hY hZ g hg)

end AlgebraicGeometry.Space

end
