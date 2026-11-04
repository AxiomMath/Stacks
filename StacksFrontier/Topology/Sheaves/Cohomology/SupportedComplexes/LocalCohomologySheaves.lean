module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsKInjective
import StacksCore.Tactic.StacksAttribute

/-!
# The local cohomology sheaves of a closed subset

Let `Z` be a closed subset of a ringed space `X`, let `𝒪_X|_Z = i⁻¹𝒪_X` be the restricted
structure sheaf and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. Sections supported on
`Z` form a functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)`, right adjoint to `i_*`; this file forms its
right derived functors, the **local cohomology sheaves**

`ℋ ⁿ_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)`.

Because `H_Z` is a right adjoint it is additive and left exact, and `Mod(𝒪_X)` is a Grothendieck
abelian category, hence has enough injectives; so the derived functors exist with no further
hypothesis, `ℋ ⁰_Z` is `H_Z` itself, and `ℋ ⁿ_Z` vanishes in negative degrees.

## Main definitions

* `localCohomologySheafFunctor X Z hZ n`: the `ℕ`-indexed `ℋ ⁿ_Z`, Mathlib's
  `CategoryTheory.Functor.rightDerived` of `H_Z`.
* `localCohomologySheaf X Z hZ n F`: the sheaf `ℋ ⁿ_Z(ℱ)` of `𝒪_X|_Z`-modules itself, which is
  the object a Gysin-type map `𝒢 ⟶ ℋ ᶜ_Z(ℱ)` out of a sheaf on `Z` lands in.
* `localCohomologySheafFunctorInt X Z hZ n`: the `ℤ`-indexed `ℋ ⁿ_Z`, the project's
  `CategoryTheory.Functor.rightDerivedPlus` of `H_Z`, in which the vanishing in negative
  degrees can be stated.

## Main results

* `localCohomologySheafFunctorZeroIso`: `ℋ ⁰_Z ≅ H_Z`, the degree-zero identification.
* `localCohomologySheafFunctorZeroCompPushforwardIso`: pushing `ℋ ⁰_Z` forward to `X` recovers
  the subsheaf of sections supported on `Z`.
* `isZero_localCohomologySheafFunctor_obj_injective_succ`: `ℋ ⁿ⁺¹_Z(ℐ) = 0` for an injective
  `𝒪_X`-module `ℐ`.
* `localCohomologySheafFunctorIntZeroIso`, `isZero_localCohomologySheafFunctorInt_of_neg`: the
  degree-zero identification and the vanishing `ℋ ⁿ_Z = 0` for `n < 0` in the `ℤ`-indexing.
* `localCohomologySheafFunctorIntIso`: the two indexings agree in the degrees where both are
  defined.

## Implementation notes

Both indexings of the higher right derived functors are available in this repository, and the
two are used in different places: the global-sections analogue
`Stacks.Cohomology.SectionsWithSupport` and the cohomology functors of
`StacksFrontier/Topology/Sheaves/Cohomology/Locality/CohomologyVanishesLocally.lean` use Mathlib's
`ℕ`-indexed `CategoryTheory.Functor.rightDerived`, whereas the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` is the spelling in which the neighbouring
`isZero_rightDerivedPlus_supportedSectionsOnClosed_modulePushforward` (Stacks 0A3B (3)) already
states a vanishing statement about `ℋ ᵖ_Z`.

The `ℕ`-indexed functor is taken as primary here, because it is the indexing in which the
source's degrees `ℋ ᶜ_Z` for `c : ℕ` are expressed without a cast, and because it needs no
choice of derived category: Mathlib's `Functor.rightDerived` is computed from the chosen
injective resolution, and its degree-zero identification `Functor.rightDerivedZeroIsoSelf` is
available for any left exact functor. The `ℤ`-indexed functor is supplied alongside it, since
only it admits negative degrees, and the two are identified by
`Stacks.DerivedIndexing.rightDerivedIso`. The `ℤ`-indexed declarations are made under the local
instance `HasDerivedCategory.standard`, as elsewhere in this directory.

Three inputs make all of this unconditional, and two of them are already instances: additivity
of `H_Z`, which is
`Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedFunctor_additive`, and the
enough-injectives property of `Mod(𝒪_X)`, which holds because `Mod(𝒪_X)` is Grothendieck
abelian and is
`Stacks.Cohomology.SectionsWithSupport.moduleSheaves_enoughInjectives`. The third is added
here: `supportedSectionsOnClosedFunctor_preservesFiniteLimits`, left exactness of `H_Z`, which
holds because `H_Z` is a right adjoint (Stacks 0G6P) and so preserves all limits. It is what
makes the canonical map `H_Z ⟶ ℋ ⁰_Z` an isomorphism.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

/-! ### Left exactness of the supported-sections functor -/

/-- `H_Z` preserves finite limits. It is right adjoint to pushforward along the inclusion of
`Z` (Stacks 0G6P), and a right adjoint preserves all limits. -/
@[stacks 0G6N "left exactness of H_Z"]
instance supportedSectionsOnClosedFunctor_preservesFiniteLimits (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    PreservesFiniteLimits (supportedSectionsOnClosedFunctor X Z hZ) := by
  have := (modulePushforward_supportedSectionsOnClosed_adjunction X Z
    hZ).rightAdjoint_preservesLimits
  exact inferInstanceAs (PreservesFiniteLimits (supportedSectionsOnClosedFunctor X Z hZ))

/-! ### The `ℕ`-indexed local cohomology sheaves -/

/-- **The local cohomology sheaves `ℋ ⁿ_Z`**, the right derived functors of the functor `H_Z`
of sections supported on the closed subset `Z`, as functors `Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)`.

Concretely, `ℋ ⁿ_Z(ℱ)` is the degree-`n` cohomology of the complex `H_Z(ℐ ⁼)` obtained by
applying `H_Z` to an injective resolution `0 ⟶ ℱ ⟶ ℐ ⁼` of `ℱ` by `𝒪_X`-modules; such a
resolution exists because `Mod(𝒪_X)` has enough injectives, and the result is independent of
it. -/
def localCohomologySheafFunctor (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (n : ℕ) :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)) :=
  (supportedSectionsOnClosedFunctor X Z hZ).rightDerived n

/-- The local cohomology sheaf `ℋ ⁿ_Z(ℱ)` of an `𝒪_X`-module `ℱ`, a sheaf of
`𝒪_X|_Z`-modules. -/
abbrev localCohomologySheaf (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (n : ℕ) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)) :=
  (localCohomologySheafFunctor X Z hZ n).obj F

/-- **The degree-zero local cohomology sheaf is the supported-sections functor.** The canonical
map `H_Z ⟶ ℋ ⁰_Z` is an isomorphism because `H_Z` is left exact, being a right adjoint. -/
def localCohomologySheafFunctorZeroIso (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    localCohomologySheafFunctor X Z hZ 0 ≅ supportedSectionsOnClosedFunctor X Z hZ :=
  (supportedSectionsOnClosedFunctor X Z hZ).rightDerivedZeroIsoSelf

/-- Pushing `ℋ ⁰_Z` forward to `X` recovers the subsheaf of sections supported on `Z`: the
composite of the degree-zero identification `ℋ ⁰_Z ≅ H_Z` with the defining property of
`H_Z`. -/
def localCohomologySheafFunctorZeroCompPushforwardIso (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    localCohomologySheafFunctor X Z hZ 0 ⋙ modulePushforward (closedSubsetInclusion X Z) ≅
      supportedSectionsFunctor X Z :=
  Functor.isoWhiskerRight (localCohomologySheafFunctorZeroIso X Z hZ)
      (modulePushforward (closedSubsetInclusion X Z)) ≪≫
    supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ

/-- An injective `𝒪_X`-module has no higher local cohomology: `ℋ ⁿ⁺¹_Z(ℐ) = 0`. The chosen
injective resolution of `ℐ` may be taken to be `ℐ` itself. -/
theorem isZero_localCohomologySheafFunctor_obj_injective_succ (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (n : ℕ)
    (I : _root_.SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    IsZero (localCohomologySheaf X Z hZ (n + 1) I) :=
  Functor.isZero_rightDerived_obj_injective_succ _ n I

/-! ### The `ℤ`-indexed local cohomology sheaves -/

section Int

attribute [local instance] HasDerivedCategory.standard

/-- **The local cohomology sheaves `ℋ ⁿ_Z`, indexed by `ℤ`** as in the source: the degree-`n`
cohomology of `RH_Z(ℱ[0])` in the bounded below derived category of `𝒪_X|_Z`-modules. This
agrees with `localCohomologySheafFunctor` in nonnegative degrees, by
`localCohomologySheafFunctorIntIso`, and vanishes in negative degrees. -/
def localCohomologySheafFunctorInt (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (n : ℤ) :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)) :=
  (supportedSectionsOnClosedFunctor X Z hZ).rightDerivedPlus n

/-- **The two indexings of the local cohomology sheaves agree** in the degrees where both are
defined. -/
def localCohomologySheafFunctorIntIso (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (n : ℕ) :
    localCohomologySheafFunctor X Z hZ n ≅ localCohomologySheafFunctorInt X Z hZ (n : ℤ) :=
  Stacks.DerivedIndexing.rightDerivedIso (supportedSectionsOnClosedFunctor X Z hZ) n

/-- **The local cohomology sheaves vanish in negative degrees.** This is part (1) of Stacks
05TD for `H_Z`: a right derived functor on the bounded below derived category has no homology
below degree `0` at a complex concentrated in degree `0`. -/
theorem isZero_localCohomologySheafFunctorInt_of_neg (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (n : ℤ) (hn : n < 0) :
    IsZero (localCohomologySheafFunctorInt X Z hZ n) :=
  (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    (supportedSectionsOnClosedFunctor X Z hZ)
    (supportedSectionsOnClosedFunctor X Z hZ).rightDerivedFunctorPlus
    (supportedSectionsOnClosedFunctor X Z hZ).rightDerivedFunctorPlusUnit).1 n hn

/-- **The degree-zero local cohomology sheaf is the supported-sections functor**, in the
`ℤ`-indexing. -/
def localCohomologySheafFunctorIntZeroIso (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    localCohomologySheafFunctorInt X Z hZ 0 ≅ supportedSectionsOnClosedFunctor X Z hZ :=
  (localCohomologySheafFunctorIntIso X Z hZ 0).symm ≪≫
    localCohomologySheafFunctorZeroIso X Z hZ

/-- An injective `𝒪_X`-module has no higher local cohomology, in the `ℤ`-indexing:
`ℋ ⁿ_Z(ℐ) = 0` for every `n ≠ 0`. -/
theorem isZero_localCohomologySheafFunctorInt_obj_injective (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (n : ℤ) (hn : n ≠ 0)
    (I : _root_.SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    IsZero ((localCohomologySheafFunctorInt X Z hZ n).obj I) :=
  Functor.isZero_rightDerivedPlus_obj_injective _ n hn I

end Int

end Stacks.Cohomology.SupportedComplexes

end
