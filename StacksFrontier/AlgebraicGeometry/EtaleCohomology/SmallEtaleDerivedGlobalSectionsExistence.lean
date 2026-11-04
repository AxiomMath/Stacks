module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors

/-!
# Unbounded derived global sections exist on every small étale site

`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections` is the total right derived functor of
global sections of abelian sheaves on the small étale site of a scheme, taken on the whole
unbounded homotopy category of cochain complexes. This file discharges the hypothesis that the
derivation exists: for every scheme `X` the functor

`Γ(X, -) : K(X_étale) ⥤ D(Ab)`

has a pointwise right derived functor along the quasi-isomorphisms, hence a right derived
functor, so `RΓ(X, -) : D(X_étale) ⥤ D(Ab)` is defined with no hypothesis beyond `X` itself.

Abelian sheaves on the small étale site form a Grothendieck abelian category
(`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale`), so every cochain complex of
them admits a quasi-isomorphism into a K-injective complex, which is [Stacks, Tag 079P]; a
K-injective resolution is a terminal index of the colimit computing the left Kan extension of a
functor on `K(X_étale)` along the localization `K(X_étale) ⥤ D(X_étale)`, so that Kan extension
exists and is computed pointwise, which is [Stacks, Tag 070K]. Neither step uses boundedness,
exactness of countable products, or anything about global sections beyond its being a functor.

## Main results

* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasPointwiseRightDerivedFunctor` and
  `Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` — the derivation of
  global sections on the small étale site of a scheme exists, pointwise and then as a functor.

## References

* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **Global sections of abelian sheaves on a small étale site admit a pointwise right derived
functor on the whole unbounded homotopy category.** Such sheaves are a Grothendieck abelian
category, so every cochain complex of them has a K-injective resolution ([Stacks, Tag 079P]) and
[Stacks, Tag 070K] applies to the functor of degreewise global sections followed by the
localization of `Ab`-complexes. -/
public instance smallEtaleGlobalSectionsAb_hasPointwiseRightDerivedFunctor (X : Scheme.{u}) :
    ((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :=
  have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- **Unbounded derived global sections exist on the small étale site of any scheme**, which is
what `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections` needs in order to be defined. -/
public instance smallEtaleGlobalSectionsAb_hasRightDerivedFunctor (X : Scheme.{u}) :
    ((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

end Stacks.EtaleCohomology

end
