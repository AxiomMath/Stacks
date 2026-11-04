module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Coherent.FiniteTypeSubobjectLimits.FilteredColimit

/-!
# Quasi-coherent modules as directed colimits of finitely presented modules

[Stacks Project, Tag 01PK] — a quasi-coherent module on a quasi-compact, quasi-separated scheme
is the colimit of a system of finitely presented modules indexed by a nonempty directed partially
ordered set — is `AlgebraicGeometry.exists_directed_system_of_isFinitePresentation` in
`StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit`.  This module stated a
second copy of that theorem, with the same binders, the same conclusion and the same proof; it
now only re-exports the surviving one, so the modules downstream of it keep the name they were
written against.

## References

* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/
