module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed
import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity of the sheaf of sections supported on a closed subset

Let `Z` be a closed subset of a topological space `X` and let `I` be an injective abelian sheaf
on `X`. The sheaf of sections of `I` supported on `Z`, regarded as an abelian sheaf on `Z`, is
again injective.

The proof is the adjunction argument. Pushforward along the inclusion of a closed subset is
left adjoint to the supported-sections functor (Stacks 01AZ), and it is exact (Stacks 01AX); a
right adjoint whose left adjoint preserves monomorphisms carries injectives to injectives, so
the conclusion is immediate. The sheaf on `Z` itself is the functorial realization of the
supported-sections subsheaf of Stacks 01AY, which is characterised up to natural isomorphism
by its pushforward along the closed inclusion.

## Main results

* `ClosedImmersionSheaves.supportedSectionsOnClosed_injective`: the supported-sections functor
  on a closed subset sends injective abelian sheaves to injective abelian sheaves.

## Implementation notes

The statement is placed in the namespace `ClosedImmersionSheaves`, which is where the three
inputs live: the realization `supportedSectionsOnClosedFunctor`, its adjunction
`closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction` and the exactness
`Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward` of the pushforward.

Exactness of the pushforward is available in the bundled form
`CategoryTheory.Limits.exactFunctor`; only its finite-limit half is used here, and only
through the monomorphism preservation it implies.

## References

* [Stacks Project, Tag 0A3A](https://stacks.math.columbia.edu/tag/0A3A)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Tag 01AY](https://stacks.math.columbia.edu/tag/01AY)
* [Stacks Project, Tag 01AZ](https://stacks.math.columbia.edu/tag/01AZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

universe u

namespace ClosedImmersionSheaves

/-- **Stacks Project, Tag 0A3A.** Sections of an injective abelian sheaf supported on a closed
subset form an injective abelian sheaf on that subset. -/
@[stacks 0A3A]
theorem supportedSectionsOnClosed_injective {X : TopCat.{u}}
    (Z : Set X) (hZ : IsClosed Z) (I : X.Sheaf AddCommGrpCat.{u})
    [Injective I] :
    Injective ((supportedSectionsOnClosedFunctor Z hZ).obj I) := by
  have : PreservesFiniteLimits
      (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)) :=
    ((exactFunctor_iff _).mp
      (Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward
        (closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal)).1
  exact (closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction
    Z hZ).map_injective I inferInstance

end ClosedImmersionSheaves
