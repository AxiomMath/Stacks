module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Equivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Standard simplices are contractible

For every `[m]`, the simplicial set `Δ[m] : n ↦ Mor_Δ([n], [m])` is homotopy equivalent to a
point, the standard zero-simplex `Δ[0]`: every morphism `Δ[m] ⟶ Δ[0]` is a homotopy equivalence,
`SSet.stdSimplex.homotopyEquivalences_hom_obj₀`.

## References

* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
-/

@[expose] public section

add_to_stacks 08QD "simplex_contractible" SSet.stdSimplex.homotopyEquivalences_hom_obj₀
