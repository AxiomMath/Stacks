module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetUnits

/-!
# The derivation unit of `i_* R𝓗_T` is the post-composition unit, transported by Stacks 0G6N

`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward` exhibits
`R𝓗_T` followed by the exact direct image from the closed subset as a right derived functor of the
supported-sections **endofunctor** `ℱ ↦ H_T(ℱ)` of `𝒪_X`-modules, with derivation unit
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforwardUnit`.  The same functor is a
right derived functor of the **composite** `H_T^{on T} ⋙ i_*`, with derivation unit
`Stacks.DerivedFunctor.postcomposeUnit`.  The two underived functors are identified by
[Stacks, Tag 0G6N] —
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of
`Stacks.SheafOfModules.SupportedSections` — and this file records that the two units are related
by exactly that identification:

`unit_endo = κ⁻¹ ⋅ unit_postcompose`,

the degreewise action of `κ⁻¹` on the homotopy category followed by the post-composition unit.

## Main results

* `derivedSupportedPushforwardUnit_app_eq_postcomposeUnit`: **the two derivation units differ by
  the degreewise action of [Stacks, Tag 0G6N]**, at an object of the homotopy category.  This is
  the hypothesis `hα` of
  `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app`, which is
  what makes the two derived/classical bridges for `i_*ℋ ⁿ_T` comparable.

## Implementation notes

**Both units are already open.**  `derivedSupportedPushforwardUnit_app` and
`derivedSupportedPushforwardSplit_hom_app` of this namespace, and
`Stacks.DerivedFunctor.postcomposeUnit_app`, write each unit at an object as a two-factor
composite whose second factor —
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the direct image, inverted, followed by the
direct image of the unit of `R𝓗_T` — is literally the same on both sides.  What is left is the
first factor: the localization of `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of `κ`
inverted on the one side, and nothing on the other.  That the first factor is the degreewise
action of `κ⁻¹` is `rfl`: `CategoryTheory.Functor.mapHomotopyCategoryCompIso` is
`CategoryTheory.Quotient.natIsoLift` of `CategoryTheory.NatIso.mapHomologicalComplex`, whose `inv`
is `CategoryTheory.NatTrans.mapHomologicalComplex` of `κ.inv`, which is what
`CategoryTheory.NatTrans.mapHomotopyCategory` of `κ.inv` is.

The reassociation is `assoc_head`, a `private` lemma at a variable category with the objects
implicit and the morphisms explicit, applied with `exact`: the two spellings
`(H_T^{on T} ⋙ i_*).mapHomotopyCategory c` and
`(H_T^{on T}).mapHomotopyCategory c ⋙ (i_*).mapHomotopyCategory c` of the middle object are
definitionally but not syntactically equal, so a rewrite whose motive crosses them is not
type-correct.

**The exactness of the direct image is a `letI` in the statement**, not a hypothesis: it occurs in
the statement through `CategoryTheory.Functor.mapDerivedCategory`, and `IsClosed` is not a class.
This is the shape `derivedSupportedPushforwardUnit_app` already has.

**No `@[stacks ...]` attribute is attached to any declaration here.**  This compares two
presentations of one derived functor of the project's own making.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardSplit derivedSupportedPushforwardUnit)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportedEndoForget

attribute [local instance 10000] HasDerivedCategory.standard

/-- A reassociation with the head re-spelled.  Stated at a variable category with the objects
implicit and the morphisms explicit, so that `a` and `a'` may be given at two definitionally equal
spellings of one object. -/
private theorem assoc_head {D : Type*} [Category* D] {x y z t : D} (a a' : x ⟶ y) (b : y ⟶ z)
    (c : z ⟶ t) (h : a = a') : (a ≫ b) ≫ c = a' ≫ b ≫ c := by
  rw [h, Category.assoc]

variable (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)

/-- **The derivation unit of `i_* R𝓗_T` as a right derived functor of the supported-sections
endofunctor is the post-composition unit, preceded by the degreewise action of [Stacks, Tag 0G6N]
inverted.**

For a ringed space `X`, a closed subset `T ⊆ X` and an object `K` of the homotopy category of
cochain complexes of `𝒪_X`-modules,

`unit_endo(K) = Qh(κ⁻¹_K) ≫ unit_postcompose(K)`,

where `κ` is
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of
`Stacks.SheafOfModules.SupportedSections`, the identification of `H_T^{on T} ⋙ i_*` with the
supported-sections endofunctor `H_T`.

This is the hypothesis that
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_sourceCongr_app` needs in
order to compare the derived/classical bridge for the endofunctor with the one for the composite:
it says the two presentations of `i_* R𝓗_T` as a right derived functor really are the same
presentation read through `κ`. -/
theorem derivedSupportedPushforwardUnit_app_eq_postcomposeUnit
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    (derivedSupportedPushforwardUnit X T hT).app K =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT).inv
            (ComplexShape.up ℤ)).app K) ≫
        (Stacks.DerivedFunctor.postcomposeUnit
          (supportedSectionsOnClosedFunctor X T hT)
          (modulePushforward (closedSubsetInclusion X T))
          (derivedSupportedSectionsOnClosed X T hT)
          (derivedSupportedSectionsOnClosedUnit X T hT)).app K := by
  let := pushforward_preservesFiniteLimits X T
  let := pushforward_preservesFiniteColimits X T hT
  rw [derivedSupportedPushforwardUnit_app X T hT K,
    derivedSupportedPushforwardSplit_hom_app X T hT K,
    Stacks.DerivedFunctor.postcomposeUnit_app]
  exact assoc_head _ _ _ _ rfl

end Stacks.Perfect.SupportedEndoForget

end
