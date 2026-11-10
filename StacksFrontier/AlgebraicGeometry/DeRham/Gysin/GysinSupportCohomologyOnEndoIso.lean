module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinSupportCohomologyOnBridge
public import
StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetEndofunctorSpelling
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetUnitPostcompose
public import StacksFrontier.Homology.DerivedIndexing.SourceCongruenceCoherence

/-!
# The two derived/classical bridges for `i_*ℋ ⁿ_T` are one

The project identifies the degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])` with Mathlib's
classical right derived functor `Rⁿ H_T(ℱ)` twice over:

* `Stacks.Gysin.supportCohomologyOnIso`, built in two steps — move `i_*` past the cohomology
  sheaf, then cross from the derived to the classical spelling on `T` — which is the
  identification the Gysin map of [Stacks, Tag 0G86] and its excision are written through; and
* `Stacks.Perfect.SupportedEndoForgetEndofunctor.supportCohomologySheafFunctorEndoIso`, the
  single generic bridge
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` taken at the
  supported-sections **endofunctor** and its canonical total right derived functor
  `Stacks.Perfect.SupportedFraction.supportPush`, which is the identification [Stacks, Tag 0G74]
  part (2) in degree `n` is written through.

They are the same isomorphism: `supportCohomologyOnIso_eq_endoIso`.  This is what lets the
degree-`n` square of [Stacks, Tag 0G87] at the endofunctor spelling be read at the Gysin spelling,
and it was the step the two halves of that reading did not have in common.

## Main results

* `Stacks.Gysin.supportCohomologyOnIso_hom_app_eq_endoIso` and
  `Stacks.Gysin.supportCohomologyOnIso_eq_endoIso`: **the two bridges agree**, componentwise and
  as isomorphisms of functors, at every closed subset and in every degree, with no hypothesis
  beyond the closedness of `T`.

## Implementation notes

**Both bridges are the same generic bridge, read through [Stacks, Tag 0G6N].**
`Stacks.Gysin.supportCohomologyOnIso_hom_app_eq_bridge` says `supportCohomologyOnIso` is the
generic bridge for the *composite* `H_T^{on T} ⋙ i_*`, taken at `R𝓗_T ⋙ D(i_*)` with
`Stacks.DerivedFunctor.postcomposeUnit`, followed by
`CategoryTheory.NatTrans.rightDerived` of the degree-zero identification `κ` of [Stacks, Tag 0G6N].
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app` says the
same of the bridge for the *endofunctor*, as soon as the two derivation units are related by `κ`,
which is
`Stacks.Perfect.SupportedEndoForget.derivedSupportedPushforwardUnit_app_eq_postcomposeUnit`.  So
the two bridges are equal to one and the same three-factor composite, and the identity is one
`Eq.trans`.

**The two `CategoryTheory.Functor.IsRightDerivedFunctor` instances are supplied by hand.**  The
same functor carries them at two spellings: `Stacks.Perfect.SupportedFraction.supportPush` is
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward`, a plain `def`, and the
coherence is applied at the spelling `R𝓗_T ⋙ D(i_*)`.  Instance search runs at `instances`
transparency and does not cross the two, so the instance for the endofunctor unit is introduced by
a `let` whose type is ascribed at the composite spelling.  Both classes are `Prop`s, so the two
occurrences of each inside the bridge agree by proof irrelevance and the assembly is by `exact`,
never `rw`.

**No `@[stacks ...]` attribute is attached to any declaration here.**  This identifies two of the
project's own constructions of one isomorphism and states no numbered result of the source.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Lemma 20.34.9 (Tag 0G87)](https://stacks.math.columbia.edu/tag/0G87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedEndoForgetEndofunctor (supportCohomologySheafFunctorEndoIso)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardUnit)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) (n : ℕ)

/-- **The two derived/classical bridges for `i_*ℋ ⁿ_T` agree, at a module.**  At an `𝒪_X`-module
`ℱ`, `Stacks.Gysin.supportCohomologyOnIso` — the identification the Gysin map of
[Stacks, Tag 0G86] is written through — and
`Stacks.Perfect.SupportedEndoForgetEndofunctor.supportCohomologySheafFunctorEndoIso` — the one
[Stacks, Tag 0G74] part (2) in degree `n` is written through — are the same map
`Hⁿ(i_* R𝓗_T(ℱ[0])) ⟶ Rⁿ H_T(ℱ)`.

Both are the generic bridge for the composite `H_T^{on T} ⋙ i_*` followed by the degree-`n` right
derived functor of [Stacks, Tag 0G6N]: for the first that is
`Stacks.Gysin.supportCohomologyOnIso_hom_app_eq_bridge`, and for the second it is
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app` applied with
`Stacks.Perfect.SupportedEndoForget.derivedSupportedPushforwardUnit_app_eq_postcomposeUnit`. -/
theorem supportCohomologyOnIso_hom_app_eq_endoIso (F : X.Modules) :
    (supportCohomologyOnIso X T hT n).hom.app F =
      (supportCohomologySheafFunctorEndoIso hT n).hom.app F := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace T
  let := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  let := Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
    (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
    (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
    (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
    (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
    Stacks.Cohomology.Localization.enoughKInjectives
  let : (derivedSupportedSectionsOnClosed X.toRingedSpace T hT ⋙
        (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory
      ).IsRightDerivedFunctor
        (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
        (HomotopyCategory.quasiIso
          (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)) :=
    Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward_isRightDerivedFunctor
      X.toRingedSpace T hT
  exact (supportCohomologyOnIso_hom_app_eq_bridge X T hT n F).trans
    (Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app
      (supportedSectionsOnClosedFunctor X.toRingedSpace T hT ⋙
        modulePushforward (closedSubsetInclusion X.toRingedSpace T))
      (supportedSectionsFunctor X.toRingedSpace T)
      (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X.toRingedSpace T hT)
      (derivedSupportedSectionsOnClosed X.toRingedSpace T hT ⋙
        (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory)
      (Stacks.DerivedFunctor.postcomposeUnit
        (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
        (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
        (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
        (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT))
      (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
      Stacks.Cohomology.Localization.enoughKInjectives
      (Stacks.Perfect.SupportedEndoForget.derivedSupportedPushforwardUnit_app_eq_postcomposeUnit
        X.toRingedSpace T hT) n F).symm

/-- **The two derived/classical bridges for `i_*ℋ ⁿ_T` are the same isomorphism of functors.**
`supportCohomologyOnIso_hom_app_eq_endoIso` read through `CategoryTheory.Iso.ext` and
`CategoryTheory.NatTrans.ext`: two isomorphisms with the same `hom` are equal.

So anything proved of one spelling of this bridge holds of the other; in particular the degree-`n`
square of [Stacks, Tag 0G87] at the supported-sections endofunctor spelling can be read at the
spelling of the Gysin target. -/
theorem supportCohomologyOnIso_eq_endoIso :
    supportCohomologyOnIso X T hT n = supportCohomologySheafFunctorEndoIso hT n :=
  Iso.ext (NatTrans.ext (funext fun F =>
    supportCohomologyOnIso_hom_app_eq_endoIso X T hT n F))

end Stacks.Gysin

end
