module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves

/-!
# Extension from a simplicial component is left adjoint to restriction, on abelian sheaves

In the situation of Stacks 09WE the inclusion of the component in simplicial degree `n` into the
total category is continuous, so on abelian sheaves extension by lower shriek `g_{n!}` is left
adjoint to restriction `g_n^{-1}`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekAbAdjunction`: the adjunction
  `g_{n!} ⊣ g_n^{-1}` on abelian sheaves.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- Extension by lower shriek from a simplicial component is left adjoint to restriction to that
component, on abelian sheaves. -/
noncomputable def componentLowerShriekAbAdjunction :
    Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⊣ S.abelianComponent n :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (S.componentFunctor n) Ab.{u}
    (S.componentTopology n) S.totalTopology

/-- Extension by lower shriek from a simplicial component is left adjoint to restriction to that
component, on abelian sheaves. -/
noncomputable def componentLowerShriekAbAdjunction' :
    Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⊣ S.restrictAb n :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (S.componentFunctor n) Ab.{u}
    (S.componentTopology n) S.totalTopology

end CategoryTheory.SimplicialSiteSituation

end
