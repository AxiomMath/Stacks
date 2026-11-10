module

public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FinitelyPresentedOver.Biproduct
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ColimitReindex
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01PJ in the shape the descent files consume

[Stacks Project, Tag 01PJ] — a quasi-coherent module on a quasi-compact quasi-separated scheme is
the colimit of a filtered diagram of finitely presented modules — is proved as
`AlgebraicGeometry.exists_filtered_diagram_of_isFinitePresentation` in
`StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit`.  The same statement is
also named, as a `Prop`, in `StacksFrontier/AlgebraicGeometry/ModuleLimits/ColimitReindex.lean` by
`Stacks.AlgebraicGeometry.ModuleLimits.QcohFilteredColimitFinitePresentation`, where it is the one
hypothesis left of the general quasi-compact quasi-separated case of [Stacks Project, Tag 01ZR]
(1).  This module states the theorem in that shape.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.qcohFilteredColimitFinitePresentation_of_extension`:
  [Stacks Project, Tag 01PJ] in the shape `QcohFilteredColimitFinitePresentation` names it, which
  is what `StacksFrontier/AlgebraicGeometry/ModuleLimits/ColimitReindex.lean` and
  `StacksFrontier/AlgebraicGeometry/ModuleLimits/LocalDescentRefine.lean`
  consume as the hypothesis `hfilt`.  Composing it with
  `exists_isFinitePresentation_pullback_iso_of_filteredColim'` discharges the residue of
  [Stacks Project, Tag 01ZR] (1).

## References

* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- **[Stacks Project, Tag 01PJ]** in the shape
`Stacks.AlgebraicGeometry.ModuleLimits.QcohFilteredColimitFinitePresentation` names it.

This is the form `StacksFrontier/AlgebraicGeometry/ModuleLimits/ColimitReindex.lean` and
`StacksFrontier/AlgebraicGeometry/ModuleLimits/LocalDescentRefine.lean` consume as the hypothesis
`hfilt`, so composing this with `exists_isFinitePresentation_pullback_iso_of_filteredColim'`
discharges the residue of
[Stacks Project, Tag 01ZR] (1). -/
theorem qcohFilteredColimitFinitePresentation_of_extension :
    QcohFilteredColimitFinitePresentation.{u} := by
  intro Z _ _ N hN
  have : N.IsQuasicoherent := hN
  exact _root_.AlgebraicGeometry.exists_filtered_diagram_of_isFinitePresentation Z N

end Stacks.AlgebraicGeometry.ModuleLimits

end
