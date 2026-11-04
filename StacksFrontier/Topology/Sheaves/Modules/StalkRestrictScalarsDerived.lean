module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalars

/-!
# The stalk of a restriction of scalars, in the derived categories

Let `X` be a topological space and `α : O ⟶ O'` a morphism of sheaves of rings on `X`. The stalk at
`x` of a restriction of scalars along `α` is the stalk read over `O_x` along the induced map of
stalk rings, which is
`AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso`. This module descends that
comparison to the derived categories and, more importantly, **splits the right-hand side into the
two derived functors it is composed of**.

## Main results

* `AlgebraicGeometry.SheafOfModules.derivedStalkFunctorRestrictScalarsCompIso`: the splitting
  `(stalkFunctor O' x ⋙ ModuleCat.restrictScalars (ringStalkMap α x)).mapDerivedCategory ≅
  (stalkFunctor O' x).mapDerivedCategory ⋙
  (ModuleCat.restrictScalars (ringStalkMap α x)).mapDerivedCategory`.

## Why this module exists, and why it is stated with the sheaves of rings as variables

A consumer that needs this splitting at a *fixed* morphism of sheaves of rings — for instance at
`AlgebraicGeometry.inverseImageRingToStructure f` and a point of a scheme, which is what the Tor
clause of [Stacks, Tag 0DJZ] needs — cannot obtain it in its own file. The implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeTorDimensionStalkObject.lean` record the
obstruction: at a fixed morphism, instance search does not find
`(ModuleCat.restrictScalars (SemilinearStalk.ringStalkMap α.hom x).hom).Additive`, because the
implicit `Ring` arguments of `ModuleCat.restrictScalars` that the fixed spelling carries agree with
the ones instance search offers only at default transparency, and instance search runs at
reducible transparency. Re-stating the instance in the consuming file does not help, nor does
registering the theorems of
`StacksFrontier/AlgebraicGeometry/Perfect/ScalarRestrictionStalk.lean` with
`attribute [local instance]`, nor does passing both factors explicitly to
`CategoryTheory.Limits.comp_preservesFiniteLimits`; and `CategoryTheory.Functor` has no
`(F ⋙ G).Additive` instance to chain through in any case.

With `O`, `O'`, `α` and `x` left as variables the obstruction disappears, because there is no fixed
spelling to disagree with: the three exactness facts are then about a restriction of scalars along
a variable ring homomorphism, where the general instances apply. This is the same device, and for
the same reason, as the one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeTorDimensionStalkBridge.lean` record for
`AlgebraicGeometry.Scheme.Hom.stalkObjRingIso`, whose sheaf of rings is a variable so that the
`Module` instances on its two carriers are findable. Instantiating a *proved* statement at a fixed
morphism runs no instance search, so the consumer gets the splitting for free.

Nothing here is specific to schemes, to the inverse-image ringed space, or to Tor amplitude, which
is why it lives beside the undescended comparison rather than in the consumer.

No `stacks` attribute is placed: this is the derived-category bookkeeping attached to Tag 01AH's
stalk API, not a clause of a tag.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  {O O' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (α : O ⟶ O') (x : X)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of scalars along the stalk map of `α` is additive: on underlying abelian groups it
does not move the morphism. -/
public instance additive_restrictScalars_ringStalkMap_var :
    (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.ringStalkMap α.hom x).hom).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along the stalk map of `α` preserves finite limits. -/
public instance preservesFiniteLimits_restrictScalars_ringStalkMap_var :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.ringStalkMap α.hom x).hom) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits
    (SemilinearStalk.ringStalkMap α.hom x).hom

/-- Restriction of scalars along the stalk map of `α` preserves finite colimits. -/
public instance preservesFiniteColimits_restrictScalars_ringStalkMap_var :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.ringStalkMap α.hom x).hom) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits
    (SemilinearStalk.ringStalkMap α.hom x).hom

/-- The stalk functor preserves finite colimits: it preserves all of them, which is Tag 01AH
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`). Its additivity and its
preservation of finite limits are already instances for a variable sheaf of rings, in
`StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness`. -/
public instance preservesFiniteColimits_stalkFunctor_var :
    PreservesFiniteColimits (stalkFunctor O' x) :=
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits O' x
  inferInstance

/-- **The derived stalk of a restriction of scalars, split into its two derived functors.** Taking
the derived stalk at `x` and then reading it over `O_x` along the stalk map of `α` is the descent
of the composite of the two.

This is `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` at the stalk functor and the
restriction of scalars along the stalk map. Stated with `α` and `x` variable, which is what makes
the three exactness instances above findable; see the module docstring. -/
public def derivedStalkFunctorRestrictScalarsCompIso :
    (stalkFunctor O' x ⋙
        ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap α.hom x).hom).mapDerivedCategory ≅
      (stalkFunctor O' x).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap α.hom x).hom).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (stalkFunctor O' x)
    (ModuleCat.restrictScalars.{u} (SemilinearStalk.ringStalkMap α.hom x).hom)

end AlgebraicGeometry.SheafOfModules

end
