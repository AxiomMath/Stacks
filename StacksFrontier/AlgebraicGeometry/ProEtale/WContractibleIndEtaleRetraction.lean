module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings

/-!
# W-contractible rings retract faithfully flat ind-étale algebras

Stacks 0982 characterises the w-contractible rings `A` (Stacks 0981: every faithfully flat
weakly étale `A → B` has a retraction) in two further ways: by every faithfully flat
*ind-étale* `A → B` having a retraction, and by `Spec(A)` being w-local with extremally
disconnected space of connected components and strictly henselian local rings at the maximal
ideals.

This file proves the implication from w-contractibility to the ind-étale retraction property,
which is the one part of that equivalence not depending on the w-local machinery of
Stacks 61.6–61.11: an ind-étale algebra is weakly étale (Stacks 097N), so w-contractibility
applies to it verbatim.

## Main definitions

No new definitions are introduced.

## Main results

* `ProetaleWContractible.IsWContractible.nonempty_algHom_of_indEtale`: a w-contractible ring
  retracts every faithfully flat ind-étale algebra. This is the implication (1) ⇒ (2) of
  Stacks 0982.

## Implementation notes

Ind-étaleness is `StacksDraft.IndEtale`, the universe-independent form of
`(CommAlgCat.etale A).ind (CommAlgCat.of A B)`; in a single universe the two agree by
`StacksDraft.indEtale_iff`. Weak étaleness of `A → B` as required by
`ProetaleWContractible.IsWContractible` is the pair of flatness of `B` and of the
multiplication map, i.e. the two fields of Mathlib's `Algebra.WeaklyEtale`.

## References

* [Stacks Project, Tag 0982](https://stacks.math.columbia.edu/tag/0982)
* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)
-/

@[expose] public section

universe u v

namespace ProetaleWContractible

/-- A w-contractible ring retracts every faithfully flat ind-étale algebra over it: an
ind-étale algebra is weakly étale (Stacks 097N), so the defining property of
w-contractibility applies. This is the implication (1) ⇒ (2) of Stacks 0982. -/
theorem IsWContractible.nonempty_algHom_of_indEtale {A : Type u} [CommRing A]
    (h : IsWContractible.{u, v} A) (B : Type v) [CommRing B] [Algebra A B]
    (hff : Module.FaithfullyFlat A B) (hind : StacksDraft.IndEtale A B) :
    Nonempty (B →ₐ[A] A) := by
  have hwe : Algebra.WeaklyEtale A B := Algebra.weaklyEtale_of_ind_etale hind
  exact h B ⟨hwe.flat, Algebra.WeaklyEtale.flat_lmul' A B⟩ hff

end ProetaleWContractible

end
