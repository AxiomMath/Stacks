module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat complexes of modules on a ringed site

A cochain complex `K` of sheaves of modules on a ringed site is *K-flat* when the total
complex of `F ⊗ K` is acyclic for every acyclic cochain complex `F`. This is Stacks 06YN,
and it is the same condition as Stacks 06Y9 states for a site with a sheaf of commutative
rings: the definition makes no use of a structure sheaf beyond the sheaf of rings over which
the modules live, and for a ringed site `X` the relevant sheaf of rings is `X.O` with
commutativity forgotten, which is exactly what `Stacks.SheafOfModules.IsKFlat` takes as its
coefficient data. This file records that the library's predicate is the content of 06YN rather
than introducing a second copy of it.

## Main definitions

* `Stacks.SheafOfModules.IsKFlat` (in `StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs`): the
  complex tensors every acyclic complex to an acyclic complex.

## Implementation notes

The tensor product used is `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of the
sectionwise tensor product, and the total complex with its Koszul-sign differential is
`Stacks.SheafOfModules.Tensor.tensorComplex`; acyclicity is Mathlib's `HomologicalComplex.Acyclic`.
The site, the sheaf of rings and the module sections keep independent universes.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public section

add_to_stacks 06YN Stacks.SheafOfModules.IsKFlat

end
