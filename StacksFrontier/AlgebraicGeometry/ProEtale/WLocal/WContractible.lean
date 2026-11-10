module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings

/-!
# W-contractible rings

A commutative ring is w-contractible when every faithfully flat weakly étale algebra over it
admits a retraction to the base ring. For an affine scheme `Spec A` this holds exactly when every
pro-étale covering has a refinement by a finite Zariski decomposition into pairwise disjoint
clopen pieces.

## Main results

The predicate `ProetaleWContractible.IsWContractible` renders the source definition directly: its
weakly étale condition is the conjunction defining `Algebra.WeaklyEtale`, faithful flatness is
`Module.FaithfullyFlat`, and a retraction is a nonempty type of algebra homomorphisms back to the
base ring. The covering-refinement condition is
`ProetaleWContractible.EveryProetaleCoverHasZariskiRefinement`, encoded by finitely many open
immersions with pairwise disjoint clopen images covering the affine scheme, refinement meaning
that every component belongs to the given covering sieve. The two implications
`ProetaleWContractible.everyProetaleCoverHasZariskiRefinement_of_wContractible` and
`ProetaleWContractible.isWContractible_of_zariskiRefinement` together give the equivalence.

## References

* [Stacks Project, Tag 0981](https://stacks.math.columbia.edu/tag/0981)
* [Stacks Project, Tag 098F](https://stacks.math.columbia.edu/tag/098F)
-/

@[expose] public section

add_to_stacks 098F "w-contractible implies the covering-refinement condition"
  ProetaleWContractible.everyProetaleCoverHasZariskiRefinement_of_wContractible

add_to_stacks 098F "the covering-refinement condition implies w-contractibility"
  ProetaleWContractible.isWContractible_of_zariskiRefinement

end
