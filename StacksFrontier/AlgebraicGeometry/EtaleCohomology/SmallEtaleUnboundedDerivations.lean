module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence

/-!
# The unbounded derivations on a small étale site exist

Abelian sheaves on the small étale site of a scheme form a Grothendieck abelian category
(`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale`), so by Stacks 079P every
cochain complex of them — bounded or not — admits a quasi-isomorphism into a K-injective
complex, and by Stacks 070K every functor out of the unbounded homotopy category therefore has a
pointwise total right derived functor along the quasi-isomorphisms.

In particular unbounded derived direct image `Rf_*` of abelian sheaves on small étale sites
exists along every morphism of schemes.

## Main results

* `Stacks.EtaleCohomology.hasRightDerivedFunctor_smallEtalePushforwardAb`: unbounded derived
  direct image of abelian sheaves along a morphism of schemes exists.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Direct image of abelian sheaves on small étale sites along a morphism of schemes, read into the
unbounded derived category of the target, has a total right derived functor along the
quasi-isomorphisms. -/
instance hasRightDerivedFunctor_smallEtalePushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :=
  haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  haveI : ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :=
    Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective
  inferInstance

end Stacks.EtaleCohomology

end
