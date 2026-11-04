module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardFromDisjointOpen
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Sections supported on a closed subset preserve K-injectivity

Let `Z` be a closed subset of a ringed space `X`, let `𝒪_X|_Z` be the restricted structure
sheaf and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. Applying the functor
`H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on `Z` degreewise to a K-injective
complex of `𝒪_X`-modules yields a K-injective complex of `𝒪_X|_Z`-modules.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isKInjective_supportedSectionsOnClosed`: **Stacks
  0G6Z**, `H_Z` preserves K-injective cochain complexes.

## Implementation notes

`H_Z` is a right adjoint of `i_*`, which is exact, so this is the adjoint criterion for
K-injectivity `CochainComplex.isKInjective_mapHomologicalComplex_of_exact` (Stacks 08BJ)
applied to the adjunction of Stacks 0G6P.

## References

* [Stacks Project, Lemma 20.34.3 (Tag 0G6Z)](https://stacks.math.columbia.edu/tag/0G6Z)
* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Lemma 13.31.9 (Tag 08BJ)](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SupportedComplexes

/- `Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedFunctor_additive` -- that
the supported-sections functor on a closed subset is additive -- is **not** restated here.  It
is an instance, obtained from the same adjunction, in
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardFromDisjointOpen.lean`,
which this module imports.

Not to be confused with `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_additive`
(`StacksFrontier/Topology/Sheaves/ClosedImmersion/AbelianLocalCohomologySheaves.lean`), which is a
different statement: it is about the `TopCat`-indexed functor on sheaves of abelian groups of
`StacksFrontier/Topology/Sheaves/ClosedImmersion/SupportedSectionsOnClosed.lean`, not the
`RingedSpace`-indexed functor on modules of
`StacksFrontier/Topology/Sheaves/Modules/SupportedSectionsAdjunction.lean`. -/

/-- **Stacks 0G6Z.** Let `Z` be a closed subset of a ringed space `X` and let
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. If `I` is a K-injective complex of
`𝒪_X`-modules, then the complex `H_Z(I)` of sections supported on `Z` is a K-injective complex
of `𝒪_X|_Z`-modules. -/
@[stacks 0G6Z]
theorem isKInjective_supportedSectionsOnClosed (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedFunctor
        X Z hZ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := pushforward_preservesFiniteLimits X Z
  have := pushforward_preservesFiniteColimits X Z hZ
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedFunctor X Z hZ)
    (modulePushforward (closedSubsetInclusion X Z))
    (Stacks.SheafOfModules.SupportedSections.modulePushforward_supportedSectionsOnClosed_adjunction
      X Z hZ) I

end Stacks.Cohomology.SupportedComplexes

end
