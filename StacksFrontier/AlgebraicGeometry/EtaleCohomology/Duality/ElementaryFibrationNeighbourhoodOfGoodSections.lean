module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationNeighbourhood
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.PointwiseAssembly

/-!
# Elementary fibration neighbourhoods from good sections

`Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood k` (SGA 4, Exposé XI,
Proposition 3.3, pointwise) follows from the existence of good sections through a point of a
normal projective compactification
(`AlgebraicGeometry.GoodNeighbourhood.ExistsGoodSections`) together with the incidence
construction (`AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections`). The reduction is
`AlgebraicGeometry.GoodNeighbourhood.exists_elementaryFibrationNeighbourhood_of_goodSections`;
this file only states it as the proposition.

## Main results

* `Stacks.EtaleCohomology.existsElementaryFibrationNeighbourhood_of_goodSections`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Elementary fibration neighbourhoods from good sections and the incidence construction**
(SGA 4, Exposé XI, Proposition 3.3). -/
theorem existsElementaryFibrationNeighbourhood_of_goodSections (k : Type u) [Field k]
    (hgs : GoodNeighbourhood.ExistsGoodSections k)
    (hinc : GoodNeighbourhood.IncidenceFromGoodSections k) :
    ExistsElementaryFibrationNeighbourhood k :=
  fun X p d _ _ hd x hx =>
    GoodNeighbourhood.exists_elementaryFibrationNeighbourhood_of_goodSections k hgs hinc X p d hd
      x hx

end Stacks.EtaleCohomology

end
