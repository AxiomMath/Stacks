module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness of the flat locus

For a morphism of schemes locally of finite presentation and a finitely presented
quasi-coherent module on its source, the locus where the module is flat over the target is
open; this is `AlgebraicGeometry.isOpen_setOf_flatOverAt`, **Stacks 0399**, proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus`.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
-/
