module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationNeighbourhoodOfGoodSections
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodSectionsExist
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.IncidenceAssembly

/-!
# Elementary fibration neighbourhoods exist

Over an algebraically closed field `k`, every closed point of a smooth irreducible scheme of
relative dimension `d ≥ 1` over `k` has an open neighbourhood which is an elementary fibration
over an irreducible affine scheme smooth of relative dimension `d - 1` (SGA 4, Exposé XI,
Proposition 3.3, pointwise): `Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood k`.
It follows from the existence of good sections through a point of a normal projective
compactification (`AlgebraicGeometry.GoodNeighbourhood.existsGoodSections`, the Bertini part) and
the incidence construction (`AlgebraicGeometry.GoodNeighbourhood.incidenceFromGoodSections`).

## Main results

* `Stacks.EtaleCohomology.existsElementaryFibrationNeighbourhood`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

universe u

namespace Stacks.EtaleCohomology

/-- **Elementary fibration neighbourhoods exist** (SGA 4, Exposé XI, Proposition 3.3): over an
algebraically closed field, every closed point of a smooth irreducible scheme of relative
dimension `d ≥ 1` has an open neighbourhood which is an elementary fibration over an irreducible
affine scheme smooth of relative dimension `d - 1`. -/
theorem existsElementaryFibrationNeighbourhood (k : Type u) [Field k] [IsAlgClosed k] :
    ExistsElementaryFibrationNeighbourhood k :=
  existsElementaryFibrationNeighbourhood_of_goodSections k
    (AlgebraicGeometry.GoodNeighbourhood.existsGoodSections k)
    (AlgebraicGeometry.GoodNeighbourhood.incidenceFromGoodSections k)

end Stacks.EtaleCohomology

end
