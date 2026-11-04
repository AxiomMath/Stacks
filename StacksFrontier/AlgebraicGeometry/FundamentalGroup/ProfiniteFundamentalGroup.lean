module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.Topology.Algebra.ProfiniteGroup

/-!
# The étale fundamental group is profinite

Let `X` be a connected scheme and `x` a geometric point of `X`. The étale fundamental group
`π₁(X, x) = Aut(F_x)` carries the topology induced by its action on every geometric fibre, and
that topology makes it a profinite group: a topological group whose underlying space is compact,
Hausdorff and totally disconnected.

The three topological conditions hold because the component embedding of `Aut(F_x)` into the
product of the permutation groups of the fibres is a closed embedding and each fibre is a finite
discrete space, so the ambient product is a profinite space. Finiteness of the geometric fibres
of a finite étale cover is `AlgebraicGeometry.finite_finiteEtaleFiber`, and needs no part of the
Galois-category theory of `FÉt_X`.

## Main results

* `AlgebraicGeometry.isProfiniteTop_etaleFundamentalGroup`: the étale fundamental group of a
  connected scheme at a geometric point is profinite.

## Implementation notes

Being profinite is spelled `Stacks.Chapter05.Tag_0BR1.IsProfiniteTop`, the conjunction of
compactness, Hausdorffness and total disconnectedness of the underlying space; the
topological-group structure is the instance
`AlgebraicGeometry.etaleFundamentalGroupIsTopologicalGroup`, so the two together say that
`π₁(X, x)` is a profinite group.

## References

* [Stacks Project, Tag 03VF](https://stacks.math.columbia.edu/tag/03VF)
* [Stacks Project, Tag 0BMR](https://stacks.math.columbia.edu/tag/0BMR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03VF, part (2).** With its canonical topology the étale fundamental
group of a connected scheme at a geometric point is a profinite group: it is a topological group
by `AlgebraicGeometry.etaleFundamentalGroupIsTopologicalGroup`, and its underlying space is
compact, Hausdorff and totally disconnected. -/
@[stacks 03VF "part (2)"]
theorem isProfiniteTop_etaleFundamentalGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    Stacks.Chapter05.Tag_0BR1.IsProfiniteTop (EtaleFundamentalGroup X x) :=
  ⟨compactSpace_etaleFundamentalGroup X x, t2Space_etaleFundamentalGroup X x,
    totallyDisconnectedSpace_etaleFundamentalGroup X x⟩

end AlgebraicGeometry

end
