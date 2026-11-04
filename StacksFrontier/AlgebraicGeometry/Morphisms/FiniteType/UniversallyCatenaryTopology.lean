module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.Topology.Dimension.CatenaryEncodings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Topological catenarity of universally catenary schemes

Universal catenarity of a locally Noetherian scheme `S`,
`AlgebraicGeometry.Scheme.IsUniversallyCatenary`, is stated through the bundled catenarity
predicate `IrreducibleClosedsCodim.IsCatenarySpace` on the source of every morphism to `S` which
is locally of finite type. Since this predicate agrees with the unbundled predicate
`TopologicalSpace.IsTopologicallyCatenary`
(`IrreducibleClosedsCodim.isCatenarySpace_iff_isTopologicallyCatenary`), universal catenarity
gives the unbundled predicate, both for `S` and for any scheme locally of finite type over it.

## Main results

* `AlgebraicGeometry.Scheme.IsUniversallyCatenary.isTopologicallyCatenary_of_locallyOfFiniteType`:
  the space of a scheme locally of finite type over a universally catenary scheme is
  topologically catenary.
* `AlgebraicGeometry.Scheme.IsUniversallyCatenary.isTopologicallyCatenary`: the space of a
  universally catenary scheme is itself topologically catenary.

## References

* [Stacks Project, Tag 02J8](https://stacks.math.columbia.edu/tag/02J8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The underlying topological space of a scheme locally of finite type over a universally
catenary scheme is topologically catenary. -/
@[ega "IV 10.6.1" "(i)"]
theorem IsUniversallyCatenary.isTopologicallyCatenary_of_locallyOfFiniteType
    {S X : Scheme.{u}} [IsLocallyNoetherian S] (hS : IsUniversallyCatenary S) (f : X ⟶ S)
    [LocallyOfFiniteType f] : IsTopologicallyCatenary X :=
  (hS.isCatenarySpace f).isTopologicallyCatenary

/-- The underlying topological space of a universally catenary scheme is topologically
catenary. -/
theorem IsUniversallyCatenary.isTopologicallyCatenary {S : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : IsUniversallyCatenary S) : IsTopologicallyCatenary S :=
  hS.isTopologicallyCatenary_of_locallyOfFiniteType (𝟙 S)

end AlgebraicGeometry.Scheme

end
