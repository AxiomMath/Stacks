module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentLowerShriekAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Extension from a simplicial component is left adjoint to restriction, on derived categories

In the situation of Stacks 09WE extension by lower shriek from the component in simplicial degree
`n` is left adjoint to restriction to that component on abelian sheaves, and both functors are
exact, so the adjunction descends to the unbounded derived categories: `g_{n!}` applied to
complexes and localized at the quasi-isomorphisms is left adjoint to the derived restriction
`CategoryTheory.SimplicialSiteSituation.derivedComponent`.

This is what lets a map out of a derived restriction be transposed into a map out of an extension,
which is how the terms of a resolution of a cartesian object are compared with the object itself.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived`: extension by lower shriek
  on unbounded derived categories.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerivedAdjunction`: the adjunction
  `g_{n!} ⊣ g_n^{-1}` on unbounded derived categories.

## Implementation notes

The two `HasDerivedCategory` instances are hypotheses rather than a fixed choice of model, as in
Tag 0D9G and as in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedSheaves.lean`, so a consumer may
supply `HasDerivedCategory.standard` or any other model.  That is why the descent uses
`CategoryTheory.Adjunction.mapDerivedCategory`, which carries them as instance arguments, rather
than a variant that fixes the standard model.  The abelian adjunction is kept in a separate
module upstream of this one so that its consumers do not pay for that import.

The lower shriek is written out rather than named through the reducible abbreviation
`CategoryTheory.SimplicialSiteSituation.componentLowerShriekAb`, for the reason recorded in
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentLowerShriekAdjunction.lean`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ k, HasDerivedCategory.{v} (Sheaf (S.componentTopology k) Ab.{u})]

/-- Extension by lower shriek from a simplicial component on unbounded derived categories,
obtained by applying the exact functor to complexes and localizing at quasi-isomorphisms. -/
noncomputable def componentLowerShriekDerived :
    DerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
    (S.componentTopology n) S.totalTopology).mapDerivedCategory

/-- The derived form of `g_{n!} ⊣ g_n^{-1}`: extension from a simplicial component is left adjoint
to restriction on unbounded derived categories, both functors being exact. -/
noncomputable def componentLowerShriekDerivedAdjunction :
    S.componentLowerShriekDerived n ⊣ S.derivedComponent n :=
  CategoryTheory.Adjunction.mapDerivedCategory (S.componentLowerShriekAbAdjunction n)

end CategoryTheory.SimplicialSiteSituation

end
