module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.Exactness

/-!
# Exactness of extension from a simplicial component

For the situation of Stacks 09WE, the lower shriek of abelian sheaves along the inclusion of a
simplicial component into the total site is exact, with no hypothesis on the situation. This is
assertion (7) of Stacks 09WG.

## Main results

* `Stacks.Sites.AbelianLowerShriek.preservesMonomorphisms_componentLowerShriek`: the lower shriek
  of abelian sheaves from a simplicial component preserves monomorphisms, as an instance.
* `Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_componentLowerShriek`: the lower shriek
  of abelian sheaves from a simplicial component is left exact, as an instance.
* `Stacks.Sites.AbelianLowerShriek.componentLowerShriek_exact'`: the lower shriek built from an
  abstract right adjoint is exact.

## Implementation notes

Both lower-shriek functors of `Mathlib.CategoryTheory.Sites.Pullback` are covered: the one built
from left Kan extension and sheafification, which is the functor whose exactness is asserted, and
the one built from an abstract right adjoint. They are compared by
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`.

No hypothesis on sheafification or on left Kan extensions is carried: for a Grothendieck topology
on a small site both hold for abelian groups at the site's universe. The coefficient category is
`AddCommGrpCat` at the site's universe.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Sites.AbelianLowerShriek

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- **The lower shriek of abelian sheaves from a simplicial component preserves
monomorphisms.** Here the lower shriek is the one built from left Kan extension and
sheafification. -/
instance preservesMonomorphisms_componentLowerShriek :
    (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n)
      AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology).PreservesMonomorphisms :=
  (Functor.PreservesMonomorphisms.iso_iff
    (Functor.sheafPullbackConstruction.sheafPullbackIso (S.componentFunctor n)
      AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology)).mp inferInstance

/-- **The lower shriek of abelian sheaves from a simplicial component is left exact.** -/
instance preservesFiniteLimits_componentLowerShriek :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n)
        AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology) :=
  preservesFiniteLimits_of_preservesMonomorphisms _

/-- **Stacks 09WG (7)**, for the lower shriek built from an abstract right adjoint: it is an exact
functor. The same assertion for the lower shriek built from left Kan extension and sheafification
is `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`, which carries the
tag. -/
theorem componentLowerShriek_exact' :
    exactFunctor
      (Sheaf (S.componentTopology n) AddCommGrpCat.{u})
      (Sheaf S.totalTopology AddCommGrpCat.{u})
      ((S.componentFunctor n).sheafPullback AddCommGrpCat.{u}
        (S.componentTopology n) S.totalTopology) :=
  (exactFunctor _ _).prop_of_iso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (S.componentFunctor n)
      AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology).symm
    (CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor S n)

end Stacks.Sites.AbelianLowerShriek

end
