module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.InjectiveSupportedSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local cohomology sheaves of an abelian sheaf

Let `Z` be a closed subset of a topological space `X` and let `i : Z → X` be the inclusion.
Sections supported on `Z`, regarded as an abelian sheaf on `Z`, form a functor
`H_Z : Ab(X) ⥤ Ab(Z)` right adjoint to `i_*`; this file forms its right derived functors, the
**local cohomology sheaves of abelian sheaves**

`ℋ ⁿ_Z : Ab(X) ⥤ Ab(Z)`.

Because `H_Z` is a right adjoint it is additive and left exact, and abelian sheaves on a
topological space form a Grothendieck abelian category, hence have enough injectives; so the
derived functors exist with no hypothesis beyond closedness of `Z`, `ℋ ⁰_Z` is `H_Z` itself, and
`ℋ ⁿ⁺¹_Z` vanishes on injectives.

## Main definitions

* `ClosedImmersionSheaves.localCohomologySheafFunctor`: the `ℕ`-indexed `ℋ ⁿ_Z`, Mathlib's
  `CategoryTheory.Functor.rightDerived` of `H_Z`.
* `ClosedImmersionSheaves.localCohomologySheaf`: the abelian sheaf `ℋ ⁿ_Z(F)` on `Z` itself.

## Main results

* `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_additive` and
  `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_preservesFiniteLimits`: `H_Z` is
  additive and left exact, both because it is a right adjoint.
* `ClosedImmersionSheaves.localCohomologySheafFunctorZeroIso`: `ℋ ⁰_Z ≅ H_Z`, the degree-zero
  identification.
* `ClosedImmersionSheaves.localCohomologySheafFunctorZeroCompPushforwardIso`: pushing `ℋ ⁰_Z`
  forward to `X` recovers the subsheaf of sections supported on `Z`.
* `ClosedImmersionSheaves.isZero_localCohomologySheafFunctor_obj_injective_succ`:
  `ℋ ⁿ⁺¹_Z(I) = 0` for an injective abelian sheaf `I`.

## Implementation notes

This is the abelian-sheaf counterpart of
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctor`, the local cohomology
sheaves of a sheaf of `𝒪_X`-modules on a ringed space, and is built in exactly the same way:
`CategoryTheory.Functor.rightDerived` of the supported-sections functor, whose two inputs are
additivity and the enough-injectives property of the source. Additivity and left exactness are
read off the adjunction `i_* ⊣ H_Z` of Stacks 01AZ,
`ClosedImmersionSheaves.closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction`:
a right adjoint is additive once its left adjoint is, and preserves all limits. Enough
injectives is found by instance search, abelian sheaves on a topological space being a
Grothendieck abelian category.

The `ℕ`-indexing is used because it is the one in which the source's degrees `ℋ ᶜ_Z` for
`c : ℕ` are expressed without a cast, as in the module-level file.

No declaration here carries a Stacks tag. The functor is the abelian-sheaf half of the
situation of Stacks 0G74 part (2); the comparison of these derived functors with the
module-level ones is not proved here. It is proved elsewhere, in part:
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorZeroForgetIso` identifies
`ℋ ⁰_Z(ℱ)` with `ℋ ⁰_Z(ℱ_ab)`, and
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison` builds the canonical
comparison map of Stacks 0G74 part (2) in the derived category. Invertibility of that map in the
higher degrees is still open.

## References

* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
* [Stacks Project, Lemma 17.5.6 (Tag 01AZ)](https://stacks.math.columbia.edu/tag/01AZ)
* [Stacks Project, Tag 0A3A](https://stacks.math.columbia.edu/tag/0A3A)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

universe u

namespace ClosedImmersionSheaves

variable {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)

/-! ### Additivity and left exactness of the supported-sections functor -/

/-- `H_Z` is additive. It is right adjoint to pushforward along the inclusion of `Z` (Stacks
01AZ), and a right adjoint of an additive functor is additive. -/
instance supportedSectionsOnClosedFunctor_additive :
    (supportedSectionsOnClosedFunctor Z hZ).Additive :=
  (closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction Z
    hZ).right_adjoint_additive

/-- `H_Z` preserves finite limits. It is right adjoint to pushforward along the inclusion of
`Z` (Stacks 01AZ), and a right adjoint preserves all limits. -/
instance supportedSectionsOnClosedFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (supportedSectionsOnClosedFunctor Z hZ) := by
  have := (closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction Z
    hZ).rightAdjoint_preservesLimits
  exact inferInstanceAs (PreservesFiniteLimits (supportedSectionsOnClosedFunctor Z hZ))

/-! ### The local cohomology sheaves -/

/-- **The local cohomology sheaves `ℋ ⁿ_Z` of abelian sheaves**, the right derived functors of
the functor `H_Z` of sections supported on the closed subset `Z`, as functors
`Ab(X) ⥤ Ab(Z)`.

Concretely, `ℋ ⁿ_Z(F)` is the degree-`n` cohomology of the complex `H_Z(I ⁼)` obtained by
applying `H_Z` to an injective resolution `0 ⟶ F ⟶ I ⁼` of `F` by abelian sheaves on `X`; such
a resolution exists because `Ab(X)` has enough injectives, and the result is independent of
it. -/
@[sga "2 I 2.1" "special case"]
def localCohomologySheafFunctor (n : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  (supportedSectionsOnClosedFunctor Z hZ).rightDerived n

/-- The local cohomology sheaf `ℋ ⁿ_Z(F)` of an abelian sheaf `F` on `X`, an abelian sheaf on
the closed subset `Z`. -/
abbrev localCohomologySheaf (n : ℕ) (F : X.Sheaf AddCommGrpCat.{u}) :
    (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  (localCohomologySheafFunctor Z hZ n).obj F

/-- **The degree-zero local cohomology sheaf is the supported-sections functor.** The canonical
map `H_Z ⟶ ℋ ⁰_Z` is an isomorphism because `H_Z` is left exact, being a right adjoint. -/
def localCohomologySheafFunctorZeroIso :
    localCohomologySheafFunctor Z hZ 0 ≅ supportedSectionsOnClosedFunctor Z hZ :=
  (supportedSectionsOnClosedFunctor Z hZ).rightDerivedZeroIsoSelf

/-- Pushing `ℋ ⁰_Z` forward to `X` recovers the subsheaf of sections supported on `Z`: the
composite of the degree-zero identification `ℋ ⁰_Z ≅ H_Z` with the defining property of
`H_Z`. -/
def localCohomologySheafFunctorZeroCompPushforwardIso :
    localCohomologySheafFunctor Z hZ 0 ⋙
        closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z) ≅
      supportedSectionsFunctor Z :=
  Functor.isoWhiskerRight (localCohomologySheafFunctorZeroIso Z hZ)
      (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)) ≪≫
    supportedSectionsOnClosedFunctor_comp_pushforward_iso Z hZ

/-- An injective abelian sheaf has no higher local cohomology: `ℋ ⁿ⁺¹_Z(I) = 0`. The chosen
injective resolution of `I` may be taken to be `I` itself. -/
theorem isZero_localCohomologySheafFunctor_obj_injective_succ (n : ℕ)
    (I : X.Sheaf AddCommGrpCat.{u}) [Injective I] :
    IsZero (localCohomologySheaf Z hZ (n + 1) I) :=
  Functor.isZero_rightDerived_obj_injective_succ _ n I

end ClosedImmersionSheaves

end
