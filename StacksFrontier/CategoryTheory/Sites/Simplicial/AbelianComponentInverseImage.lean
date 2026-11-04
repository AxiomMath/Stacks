module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerived

/-!
# The component restriction of abelian sheaves as an abelian inverse image

Let `S` be a simplicial-site situation. Restriction of abelian sheaves from its total site to the
site of one simplicial degree has two spellings: the direct image along the continuous component
inclusion, `CategoryTheory.SimplicialSiteSituation.restrictAb`, and the abelian inverse image of
the component morphism of topoi of Stacks 09WG. This module fixes the second spelling and the
transition of Stacks 09WF at it, which is the spelling that
`CategoryTheory.SimplicialSiteSituation.abelianFiberTransition` and Stacks 0D7J are stated at.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.abelianComponent'`: restriction of abelian sheaves
  from the total site to a simplicial degree, as the abelian inverse image of the component
  morphism of topoi.
* `CategoryTheory.SimplicialSiteSituation.abelianComponentTransition`: **Stacks 09WF** on abelian
  sheaves with that functor as its source and target.

## Main results

* `CategoryTheory.SimplicialSiteSituation.abelianComponent'_exact`: restriction to a simplicial
  degree is exact on abelian sheaves.

## Implementation notes

**Why the name is primed.** `restrictAb` is the same functor up to isomorphism — restriction
followed by *sheafification*, `CategoryTheory.gInv`, is restriction, which is Stacks 00XR (1),
formalized on sheaves of sets by `componentMorphismInverseImageIso` and on commutative group
objects by `abelianComponentIso`, both in
`StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre`. What keeps the two spellings
apart is the transitions: `abelianFiberTransition` and its invertibility criterion
`abelianFiberTransition_isIso_iff` are *stated* at the abelian inverse image, and the cocycle and
unit laws of `StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionCocycle` — the only
consumer of this module — are proved there. Routing those onto `restrictAb` would restate proved
results at a different transition rather than rewire them.

(Stacks 0D7J is *not* among the results that would have to move: its statement
`ObjectProperty.IsWeakSerreClass (IsCartesianAbSheaf S)` is about the underlying sheaf of
sets and mentions no model of the restriction; only its proof passes through
`abelianFiberTransition_isIso_iff`.)

The component restriction is `CategoryTheory.Sites.abelianInverseImage` of the component
morphism of topoi, exactly as the simplex transitions `abelianTransition` of Stacks 0D9G are;
its exactness is therefore the exactness of an abelian inverse image, Stacks 04JC, and needs no
separate argument.

**Where cartesianness of a derived object lives.** Stacks 07TF (3) is
`CategoryTheory.SimplicialSiteSituation.IsCartesianDerived` and Stacks 0D7L (1) is
`isCartesianDerived_iff_forall_isCartesianAbSheaf_homology'`, both in
`StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves`, at the derived functor of
`restrictAb` and for an arbitrary choice of derived categories. There is no second notion at the
abelian inverse image: the cohomology criterion for 0D7L is read off the transition of Stacks
09WF on sheaves of sets, which is common to both spellings, so nothing is gained by localizing
`abelianComponent'` as well.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

end CategoryTheory.SimplicialSiteSituation

end
