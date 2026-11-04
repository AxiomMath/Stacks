module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.AutomorphismTopology

/-!
# The canonical topology on the automorphism group of a set-valued functor

Let `F : C ⥤ Type w` be a set-valued functor. Each value `F.obj X` is given the discrete
topology, so that its permutation group `Equiv.Perm (F.obj X)` carries the topology of
pointwise convergence (`autTopology`, Stacks 0BMC), and the product
`∀ X, Equiv.Perm (F.obj X)` carries the product topology. Evaluating a natural automorphism of
`F` at every object of `C` is an injective group homomorphism
`Aut F →* ∀ X, Equiv.Perm (F.obj X)`, and `Aut F` is topologised by the induced topology.

The point of Stacks 0BMR is that this homomorphism is a *closed* embedding: its image is the
set of families `(γ_X)` commuting with every `F.map f`, which is an intersection of sets cut out
by equations between continuous functions into discrete spaces. Consequently, when every value
`F.obj X` is finite, each `Equiv.Perm (F.obj X)` is a finite discrete group, the product is a
profinite space, and `Aut F` — being closed inside it — is a profinite topological group.

## Main definitions

* `Stacks.FundamentalGroup.componentEmbedding` — evaluation of a natural automorphism at every
  object, as a group homomorphism.
* `Stacks.FundamentalGroup.automorphismProductTopology` — the product of the
  pointwise-convergence topologies on the automorphism groups of the values.
* `Stacks.FundamentalGroup.functorAutomorphismTopology` — the topology on `Aut F` induced by the
  component embedding.
* `Stacks.FundamentalGroup.functorAutomorphismIsTopologicalGroup` — that topology makes `Aut F`
  a topological group.

## Main results

* `Stacks.FundamentalGroup.isClosedEmbedding_componentEmbedding` — the component embedding is a
  closed embedding.
* `Stacks.FundamentalGroup.isProfiniteTop_functorAutomorphismTopology` — if every value of `F`
  is finite then `Aut F` is compact, Hausdorff and totally disconnected, hence a profinite
  group.

## Implementation notes

None of `componentEmbedding`, `automorphismProductTopology`, `functorAutomorphismTopology`,
`functorAutomorphismIsTopologicalGroup` or `isClosedEmbedding_componentEmbedding` is declared
here. They are the repository's canonical declarations in `CategoryTheory`, in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/AutomorphismTopology.lean`,
which is where the two parts of `@[stacks 0BMR]` are registered; they are re-exported into
`Stacks.FundamentalGroup` here, so the consumers that spell them with this prefix name those
constants. Declaring each of them only once keeps a single declaration for each part of 0BMR.

`isProfiniteTop_functorAutomorphismTopology` keeps its own declaration only because its name
differs from the canonical `CategoryTheory.isProfiniteGrp_functorAutomorphismTopology`; it is
proved by that lemma rather than by a second copy of its proof.

The topologies on `Aut F` and on the product are *definitions* rather than instances: a
category can carry several set-valued functors, and `Aut F` is a bare type synonym for which an
instance would fire indiscriminately. Statements about them therefore use `@`-applied forms.
"Profinite" is spelled with `Stacks.Chapter05.Tag_0BR1.IsProfiniteTop`, the
conjunction of compactness, Hausdorffness and total disconnectedness; the group structure is
supplied separately by `functorAutomorphismIsTopologicalGroup`.

## References

* [Stacks Project, Tag 0BMR](https://stacks.math.columbia.edu/tag/0BMR)
-/

@[expose] public section

open CategoryTheory Topology

universe u v w

namespace Stacks.FundamentalGroup

export CategoryTheory (componentEmbedding automorphismProductTopology
  functorAutomorphismTopology functorAutomorphismIsTopologicalGroup
  isClosedEmbedding_componentEmbedding)

variable {C : Type u} [Category.{v} C]

/-- If every value of a set-valued functor is finite, then its automorphism group, with the
topology induced by componentwise evaluation, is compact, Hausdorff and totally disconnected;
together with `Stacks.FundamentalGroup.functorAutomorphismIsTopologicalGroup` this says that it
is a profinite group.

This is the `Stacks.FundamentalGroup` spelling of
`CategoryTheory.isProfiniteGrp_functorAutomorphismTopology`, which carries
`@[stacks 0BMR "profinite group"]`. -/
public lemma isProfiniteTop_functorAutomorphismTopology (F : C ⥤ Type w)
    [∀ X, Finite (F.obj X)] :
    @Stacks.Chapter05.Tag_0BR1.IsProfiniteTop (Aut F) (functorAutomorphismTopology F) :=
  isProfiniteGrp_functorAutomorphismTopology F

end Stacks.FundamentalGroup

end
