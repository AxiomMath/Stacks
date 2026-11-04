module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatSectionsOverOpen
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayRestrictSections

/-!
# The cohomology edge morphism of derived sections, against restriction to a smaller open

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison` at
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` is the edge morphism
`H^q(RΓ(U, K)) ⟶ Γ(U, H^q K)`. The tail of conclusion (c) of [Stacks, Tag 0EX3] meets it over two
opens at once: the `γ⁺` side leaves the edge morphism of `RΓ(h⁻¹V, -)` where the crossing at `f''`
over the smaller affine `W` meets the edge morphism of `RΓ(W, -)`. This file supplies the identity
that moves between them: the edge morphism is compatible with restriction to a smaller open.

Nothing new is proved. `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` is the naturality of the edge morphism in the
**functor**, along a natural transformation of two left exact functors with compatible right
derived functors; restriction of sections is such a transformation, by
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrictLE`, and its derived companion is
`…DerivedSectionsLeray.derivedSectionsOverOpenRestrictLE`, whose characterising factorisation
`…derivedSectionsOverOpenRestrictLE_fac_app` is written in exactly the shape the coherence datum
asks for. So the content here is the instantiation.

The one thing that has to be built is the unit exhibiting `RΓ(U', -)` followed by restriction of
scalars as the right derived functor of `Γ(U', -)` followed by restriction of scalars — the
`G`-side datum, which `derivedSectionsOverOpenRestrictLE` does not need and so does not carry (it
is constructed out of the universal property of the `U`-side derived functor alone).

## Main results

* `Stacks.EdgeCompat.sectionsOverOpenRestrictCompUnit` and
  `Stacks.EdgeCompat.isRightDerivedFunctor_sectionsOverOpenRestrictCompUnit`: `RΓ(U', -)` followed
  by restriction of scalars is the right derived functor of `Γ(U', -)` followed by restriction of
  scalars. The unit is the one `…DerivedSectionsLeray.sectionsOverOpenRestrictUnit` already uses
  after its leading degreewise restriction, and both are one application of
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` and
  `…HomologyComparison.isRightDerivedFunctor_exactPostcomposeUnit`, whose criterion is
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`
  `.isRightDerivedFunctor_of_isIso_app_isKInjective`: restriction of scalars carries the
  invertibility of the unit at a K-injective complex along.
* `Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict`: **the edge morphism of
  derived sections is compatible with restriction to a smaller open.** The edge morphism over `U`
  followed by restriction of sections to `U'` is the derived restriction followed by the edge
  morphism over `U'`. No hypothesis on `X`, on the two opens or on `q`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison
  derivedHomologyComparison_naturality_natTrans exactPostcomposeUnit
  isRightDerivedFunctor_exactPostcomposeUnit)

namespace Stacks.EdgeCompat

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of modules on a ringed space have enough injectives: they form a Grothendieck abelian
category, in the one module universe available there. This is
`SheafOfModules.enoughInjectivesU` at three equal universes, which is not the shape instance
search finds unaided. -/
local instance moduleSheaves_enoughInjectives' (Z : RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing Z)) :=
  SheafOfModules.enoughInjectivesU.{u, u, u} (structureSheafRing Z)

variable {X : RingedSpace.{u, u}} {U U' : Opens X.carrier} (hUU' : U' ≤ U)

/-- **The unit exhibiting `RΓ(U', -)` followed by restriction of scalars as a right derived
functor.** For opens `U' ⊆ U` of a ringed space `X`, this is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` at the pair
`(Γ(U', -), res_{U' ≤ U})`: the comparison of the two readings of restriction of scalars on the
derived category followed by the unit of `RΓ(U', -)` pushed along it. Restriction of scalars is
exact, which is the general brick's only hypothesis on the second factor.

Its leading isomorphism is `Stacks.Cohomology.DerivedSectionsLeray.sectionsRestrictHomotopyIso`,
written out at this pair; the two agree by definition.

It is the part of `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrictUnit` after its
leading degreewise restriction: that transformation starts at the termwise sections over `U`,
because it is built to be factored through the universal property of `RΓ(U, -)`, whereas this one
starts at the termwise sections over `U'` with scalars restricted, which is what the right derived
functor of that composite is a derived functor *of*. -/
def sectionsOverOpenRestrictCompUnit :
    (sectionsOverOpen X U' ⋙ sectionsRestrictScalars X hUU').mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        derivedSectionsOverOpen X U' ⋙ (sectionsRestrictScalars X hUU').mapDerivedCategory :=
  exactPostcomposeUnit (sectionsOverOpen X U') (sectionsRestrictScalars X hUU')
    (derivedSectionsOverOpen X U') (derivedSectionsOverOpenUnit X U')

/-- **`sectionsOverOpenRestrictCompUnit` does exhibit a right derived functor.** The general
brick `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isRightDerivedFunctor_exactPostcomposeUnit`, with the K-injective resolutions on `X` supplied by
`Stacks.Cohomology.DerivedSectionsLeray.exists_quasiIso_isKInjective`. -/
instance isRightDerivedFunctor_sectionsOverOpenRestrictCompUnit :
    (derivedSectionsOverOpen X U' ⋙
        (sectionsRestrictScalars X hUU').mapDerivedCategory).IsRightDerivedFunctor
      (sectionsOverOpenRestrictCompUnit hUU')
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X)

/-- **The cohomology edge morphism of derived sections is compatible with restriction to a smaller
open.** For opens `U' ⊆ U` of a ringed space `X` and a degree `q`,

> `H^q(RΓ(U, K)) ⟶ Γ(U, H^q K) ⟶ Γ(U', H^q K)` versus
> `H^q(RΓ(U, K)) ⟶ H^q(RΓ(U', K)) ⟶ Γ(U', H^q K)`

commute: the edge morphism over `U` followed by restriction of sections to `U'` is the derived
restriction `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrictLE` followed by
the edge morphism over `U'`, both read over `Γ(U, 𝒪_X)`.

This is `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` at the natural transformation
`…DerivedSectionsLeray.sectionsOverOpenRestrictLE`, whose coherence datum is the characterising
factorisation `…DerivedSectionsLeray.derivedSectionsOverOpenRestrictLE_fac_app` of the derived
restriction. Nothing is assumed of `X`, of the two opens or of `q`. -/
theorem derivedHomologyComparison_sectionsOverOpenRestrict (q : ℤ) :
    derivedHomologyComparison (sectionsOverOpen X U) (derivedSectionsOverOpen X U)
            (derivedSectionsOverOpenUnit X U) (exists_quasiIso_isKInjective X) q ≫
        Functor.whiskerLeft
          (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q)
          (sectionsOverOpenRestrictLE X hUU') =
      Functor.whiskerRight (derivedSectionsOverOpenRestrictLE X hUU')
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) q) ≫
        derivedHomologyComparison (sectionsOverOpen X U' ⋙ sectionsRestrictScalars X hUU')
          (derivedSectionsOverOpen X U' ⋙ (sectionsRestrictScalars X hUU').mapDerivedCategory)
          (sectionsOverOpenRestrictCompUnit hUU') (exists_quasiIso_isKInjective X) q := by
  have hcoh : Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (sectionsOverOpenRestrictLE X hUU') (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ sectionsOverOpenRestrictCompUnit hUU' =
      derivedSectionsOverOpenUnit X U ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedSectionsOverOpenRestrictLE X hUU') := by
    ext K
    exact (derivedSectionsOverOpenRestrictLE_fac_app X hUU' K).symm
  exact derivedHomologyComparison_naturality_natTrans (sectionsOverOpen X U)
    (sectionsOverOpenRestrictLE X hUU') (derivedSectionsOverOpen X U)
    (derivedSectionsOverOpenUnit X U)
    (derivedSectionsOverOpen X U' ⋙ (sectionsRestrictScalars X hUU').mapDerivedCategory)
    (sectionsOverOpenRestrictCompUnit hUU') (derivedSectionsOverOpenRestrictLE X hUU') hcoh
    (exists_quasiIso_isKInjective X) q

end Stacks.EdgeCompat

end
