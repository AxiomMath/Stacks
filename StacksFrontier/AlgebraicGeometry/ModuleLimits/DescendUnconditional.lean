module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FilteredColimitFP
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules as directed colimits of finitely presented modules

A quasi-coherent module on a quasi-compact quasi-separated scheme is the colimit of a directed
system of modules of finite presentation [Stacks Project, Tag 01PK]. This module declares
nothing: it imports the filtered-colimit hypothesis of that statement, proved in
`StacksFrontier.AlgebraicGeometry.ModuleLimits.FilteredColimitFP`, together with
`StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine`, for the files that use both.
The colimit statement with its filtered-colimit hypothesis is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_directed_colimit_of_isFinitePresentation_of_filtered`
in `StacksFrontier.AlgebraicGeometry.ModuleLimits.ColimitReindex`.

## References

* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

end Stacks.AlgebraicGeometry.ModuleLimits

end
