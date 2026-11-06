module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingTensorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTensorToSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Čech vanishing at an affine chart for a cartesian module, at a free module universe

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
affine étale chart of `F` and let `G` be an `𝒪_F`-module whose sections live at an arbitrary
universe `max u m` and which is cartesian on affine charts.  This file proves that the higher
Čech cohomology of the abelian presheaf underlying `G` vanishes on every finite affine covering
family of `W`.

It is `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite` with the
module universe freed.  That statement is pinned to `Modules.{u, u}` because it discharges its
coefficient hypothesis through
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite`, which
produces an `Mᵃ` for a module `M` on the chart's *scheme* and hence has its sections at the
universe `u` of the schemes.  Here the coefficient hypothesis is discharged instead by the
comparison `Γ(-, 𝒪) ⊗_R G(W) ⟶ G` of
`AlgebraicGeometry.Space.SmallEtale.tensorToChartSections`, which is built from a bare module
and is free in that universe.

## What the two inputs are

* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_overTensorPresheafIso`, the
  transport of [Stacks, Tag 03FJ] to the small étale site of an algebraic space with the
  ambient coefficient presheaf of a bare module;
* `AlgebraicGeometry.Space.SmallEtale.isIso_tensorToChartSectionsApp`, which says the comparison
  is invertible at the objects of the slice with affine underlying scheme — exactly the
  pointwise form that transport asks for, and exactly what
  `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` provides.

Nothing else is owed, and in particular no isomorphism of presheaves on the whole slice is
claimed: the comparison is not one, see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartTensorToSections.lean`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_isCartesianOnAffineCharts`:
  **the Čech vanishing**, for a module cartesian on affine charts, at a free module universe.
* `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite_freeModuleUniverse`:
  the same for a quasi-coherent module, its cartesianness being the forward implication of
  Descent, Proposition 03DX (2) at a free module universe.

## Implementation notes

**No `@[stacks]` attribute is claimed**, for the reason the statements this composes give:
[Stacks, Tag 03FJ] is stated for the three cases of [Stacks, Tag 03FI], all three of which are
registered elsewhere in this tree, and the small étale site of an algebraic space is not one of
them.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), part (2)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite

universe m u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The Čech cohomology of an `𝒪_F`-module cartesian on affine charts vanishes in positive
degrees on a finite affine covering family of an affine étale chart**, with the module sections
at an arbitrary universe `max u m`.

This is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_overTensorPresheafIso` with
its coefficient comparison supplied by
`AlgebraicGeometry.Space.SmallEtale.tensorToChartSections`, whose invertibility at the affine
objects of the slice is `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` and nothing more.

The coefficient module of the transport is `G(W)` itself, read as a bare module over the
coordinate ring of the chart's scheme. -/
theorem isZero_cechCohomology_succ_of_isCartesianOnAffineCharts
    (W : SmallEtale B S hS F) (G : Modules.{u, max u m} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{max u m} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ topology B S hS F W) (p : ℕ) (hp : 0 < p) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (cechCohomology E (chartAbelianPresheaf.{m} B S hS F hF G) p) :=
  isZero_cechCohomology_succ_of_overTensorPresheafIso B S hS F W hW E hfin haff hcov
    ((chartAbelianPresheaf.{m} B S hS F hF G).obj (op W))
    (chartAbelianPresheaf.{m} B S hS F hF G) (tensorToChartSections B S hS F hF W G)
    (fun Z hZ ↦ isIso_tensorToChartSectionsApp B S hS F hF W G hG hW (op Z) hZ) p hp

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The Čech cohomology of a quasi-coherent `𝒪_X`-module vanishes in positive degrees on a
finite affine covering family of an affine étale chart**, with the module sections at an
arbitrary universe `max u m`.

This is `AlgebraicGeometry.Space.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`, which is
stated at the module universe `u` of the schemes, with the module universe freed: it is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_isCartesianOnAffineCharts` with
its cartesianness hypothesis discharged by the forward implication of Descent, Proposition 03DX
(2), `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse`. -/
theorem isZero_cechCohomology_succ_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : Modules.{u, max u m} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS F) (hW : IsAffineChart B S hS F W)
    (E : PreZeroHypercover.{max u m} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffineChart B S hS F (E.X i))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W) (p : ℕ) (hp : 0 < p) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (Stacks.CechSite.cechCohomology E
      ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{max u m}).obj
        ((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M))
      p) :=
  SmallEtale.isZero_cechCohomology_succ_of_isCartesianOnAffineCharts B S hS F hF W M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse B S hS F hF M hM) hW E hfin
    haff hcov p hp

end AlgebraicGeometry.Space

end
