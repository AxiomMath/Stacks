module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcTargetLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget

/-!
# The list of properties étale-smooth local on the source-and-target (Stacks 0CG3)

Let `S` be a scheme contained in a big fppf site `B`. Étaleness, local quasi-finiteness and
unramifiedness of morphisms of algebraic spaces over `S` are étale-smooth local on the
source-and-target in the sense of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget` (**Stacks 0CFZ**). These are the
three enumerated entries of the list of **Stacks 0CG3**.

## Main results

* `AlgebraicGeometry.Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget`: étaleness is
  étale-smooth local on the source-and-target.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_isEtaleSmoothLocalOnSourceAndTarget`: local
  quasi-finiteness is étale-smooth local on the source-and-target.
* `AlgebraicGeometry.Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget`: unramifiedness is
  étale-smooth local on the source-and-target.

## Implementation notes

The list of Stacks 0CG3 ends with the entry "add more here as needed" and with the observation
that any property of **Stacks 06FC** is a fortiori an example; neither is a claim about a
specific property, so neither has a carrier here and each attribute is suffixed with the entry
it states rather than left bare.

The index type of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage`, and the criterion
`AlgebraicGeometry.Space.isEtaleSmoothLocalOnSourceAndTarget_of_local` (Stacks 0CG2) consumes
the locality hypotheses at `Type (u + 1)`, so the locality instances are supplied at that
instantiation.

## References

* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CG2](https://stacks.math.columbia.edu/tag/0CG2)
-/


@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étaleness of morphisms of algebraic spaces over `S` is étale-smooth local on the
source-and-target. -/
@[stacks 0CG3 "étale"]
theorem isEtale_isEtaleSmoothLocalOnSourceAndTarget :
    IsEtaleSmoothLocalOnSourceAndTarget B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsEtale B S hS f.hom) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ f => IsEtale B S hS f.hom
  let : P.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    isEtale_isLocalAtSource_etale.{u, u + 1} B S hS
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isEtale_isLocalAtTarget_fpqc.{u, u + 1} B S hS
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Topology.precoverage_smooth_le_fpqc.{u, u + 1} B S hS)
  let : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
      IsOpenImmersion B S hS f.hom) :=
    ⟨fun i hi _ hf => isEtale_comp B S hS hf
      (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hi))⟩
  exact isEtaleSmoothLocalOnSourceAndTarget_of_local B S hS P

/-- Local quasi-finiteness of morphisms of algebraic spaces over `S` is étale-smooth local on
the source-and-target. -/
@[stacks 0CG3 "locally quasi-finite"]
theorem isLocallyQuasiFinite_isEtaleSmoothLocalOnSourceAndTarget :
    IsEtaleSmoothLocalOnSourceAndTarget B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsLocallyQuasiFinite B S hS f.hom) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ f => IsLocallyQuasiFinite B S hS f.hom
  let : P.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    isLocallyQuasiFinite_isLocalAtSource_etale.{u, u + 1} B S hS
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isLocallyQuasiFinite_isLocalAtTarget_fpqc.{u, u + 1} B S hS
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Topology.precoverage_smooth_le_fpqc.{u, u + 1} B S hS)
  let : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
      IsOpenImmersion B S hS f.hom) :=
    ⟨fun {X Y Z} i hi f hf => isLocallyQuasiFinite_comp B S hS X.property Y.property Z.property
      f.hom i.hom hf (isLocallyQuasiFinite_of_isImmersion B S hS i.hom
        (isImmersion_of_isOpenImmersion B S hS hi))⟩
  exact isEtaleSmoothLocalOnSourceAndTarget_of_local B S hS P

/-- Unramifiedness of morphisms of algebraic spaces over `S` is étale-smooth local on the
source-and-target. -/
@[stacks 0CG3 "unramified"]
theorem isUnramified_isEtaleSmoothLocalOnSourceAndTarget :
    IsEtaleSmoothLocalOnSourceAndTarget B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsUnramified B S hS f.hom) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ f => IsUnramified B S hS f.hom
  let : P.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    unramified_isLocalAtSource_etale.{u, u + 1} B S hS
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isUnramified_isLocalAtTarget_fpqc.{u, u + 1} B S hS
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Topology.precoverage_smooth_le_fpqc.{u, u + 1} B S hS)
  let : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
      IsOpenImmersion B S hS f.hom) :=
    ⟨fun {X Y Z} i hi f hf => isUnramified_comp B S hS X.property Y.property Z.property
      f.hom i.hom hf (isUnramified_of_isImmersion B S hS Y.property Z.property
        (isImmersion_of_isOpenImmersion B S hS hi))⟩
  exact isEtaleSmoothLocalOnSourceAndTarget_of_local B S hS P

end AlgebraicGeometry.Space

end
