module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedPullbackInvertible
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0G78 is an isomorphism along an open immersion

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an **open immersion** of ringed spaces, let `Z ⊆ X` be
closed and let `Z' = f^{-1}(Z)`.  Then the canonical map of [Stacks, Tag 0G78]

`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`

is an isomorphism for every `K` in `D(𝒪_X)`, with no further hypothesis.

## Main results

* `derivedSupportedSectionsOnClosedPullbackNatIso`: **the comparison of functors**
  `R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}`.
* `isIso_supportedPullbackMap_of_isOpenImmersion`: **[Stacks, Tag 0G78] along an open
  immersion**, unconditionally.

## Implementation notes

**The route.**  `Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_natIso`
reduces the invertibility of the canonical map to the existence of *any* natural isomorphism
between the two composite functors, with no compatibility asked for.  Both composites are right
derived functors of degreewise-isomorphic functors, so Mathlib's
`CategoryTheory.Functor.rightDerivedNatIso` supplies the comparison:

* `R𝓗_Z ⋙ L(f|_{Z'})^*` derives `H_Z ⋙ (f|_{Z'})^*`.  The derived pullback along the open
  immersion `f|_{Z'}` of `isOpenImmersion_closedSubsetRestriction` is the degreewise pullback,
  by `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`, and
  postcomposing a total right derived functor with any functor again gives a right derived
  functor, by
  `Stacks.Cohomology.SiteCohomologyPresheaf.isRightDerivedFunctor_totalRightDerived_comp`.
* `Lf^* ⋙ R𝓗_{Z'}` derives `f^* ⋙ H_{Z'}`, by
  `Stacks.Cohomology.composite_isRightDerivedFunctor`: `f^*` is exact, so it is its own right
  derived functor, and the unit of `R𝓗_{Z'}` is invertible at `f^*` of a K-injective complex
  because `f^*` carries K-injective complexes to K-injective complexes
  (`Stacks.Cohomology.openImmersionModulePullback_preservesKInjective`).
* the degreewise comparison `H_Z ⋙ (f|_{Z'})^* ≅ f^* ⋙ H_{Z'}` is
  `supportedSectionsOnClosedPullbackNatIso`, which is where the mathematics is.

The two sources on the homotopy category are identified by
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` and
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`, exactly as in
`Stacks.Cohomology.SiteCohomologyPresheaf.mapDerivedCategorySourceIso`.

**Nothing is claimed about the canonical map itself here** beyond its invertibility, and nothing
has to be — see the implementation notes of
`Stacks.Cohomology.SupportedComplexes.SupportedPullbackInvertible`.  The comparison of functors
built here **is** the canonical map of Tag 0G78, by
`Stacks.Cohomology.SupportedComplexes`
`.supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso` of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedPullbackComparison.lean`;
that identification is downstream of this file and is not used by anything in it.

**Only an open immersion.**  `f` carries `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`
throughout, and nothing is claimed for a general morphism of ringed spaces.  `Z` is closed, as
it must be for `R𝓗_Z` to be defined at all.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-! ### `R𝓗_Z ⋙ L(f|_{Z'})^*` derives `H_Z ⋙ (f|_{Z'})^*` -/

/-- The candidate unit exhibiting `R𝓗_Z ⋙ (f|_{Z'})^*` as a right derived functor of
`H_Z ⋙ (f|_{Z'})^*`: the unit of `R𝓗_Z` with `(f|_{Z'})^*` applied to it. -/
def derivedSupportedSectionsOnClosedCompUnit (hZ : IsClosed Z) :
    (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⋙
        (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ derivedSupportedSectionsOnClosed X Z hZ ⋙
        (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory :=
  Functor.whiskerRight (derivedSupportedSectionsOnClosedUnit X Z hZ)
    (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory

/-- The unit of `R𝓗_S` is invertible at every K-injective complex. -/
private theorem isIso_derivedSupportedSectionsOnClosedUnit_app {Y : RingedSpace.{u, u}}
    (S : Set Y.carrier) (hS : IsClosed S)
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    [CochainComplex.IsKInjective I] :
    IsIso ((derivedSupportedSectionsOnClosedUnit Y S hS).app
      ((HomotopyCategory.quotient _ _).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((supportedSectionsOnClosedFunctor Y S hS).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (Stacks.Cohomology.sheaf_exists_kInjective_resolution Y)).2 DerivedCategory.Qh
    (derivedSupportedSectionsOnClosed Y S hS) (derivedSupportedSectionsOnClosedUnit Y S hS)
    I inferInstance

/-- **`R𝓗_Z ⋙ (f|_{Z'})^*` is a right derived functor of `H_Z ⋙ (f|_{Z'})^*`.**  The unit of
`R𝓗_Z` is invertible at every K-injective complex, so its image under any functor is, and a
comparison invertible on K-injectives is a right derived functor. -/
theorem isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp (hZ : IsClosed Z) :
    (derivedSupportedSectionsOnClosed X Z hZ ⋙
        (modulePullback
          (closedSubsetRestriction f Z)).mapDerivedCategory).IsRightDerivedFunctor
      (derivedSupportedSectionsOnClosedCompUnit f Z hZ)
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.isRightDerivedFunctor_of_isIso_on_kInjectives
    (Stacks.Cohomology.sheaf_exists_kInjective_resolution X) _ _ _ (fun I hI => ?_)
  have := hI
  have := isIso_derivedSupportedSectionsOnClosedUnit_app Z hZ I
  show IsIso ((modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory.map
    ((derivedSupportedSectionsOnClosedUnit X Z hZ).app
      ((HomotopyCategory.quotient _ _).obj I)))
  infer_instance

/-! ### `Lf^* ⋙ R𝓗_{Z'}` derives `f^* ⋙ H_{Z'}` -/

/-- **`Lf^* ⋙ R𝓗_{Z'}` is a right derived functor of `f^* ⋙ H_{Z'}`** for `f` an open
immersion.

The degreewise pullback `f^*` is exact, hence its own right derived functor, and the unit of
`R𝓗_{Z'}` is invertible at `f^*` of a K-injective complex because `f^*` preserves
K-injectivity.  This is the unbounded form of [Stacks, Tag 015Z] that the comparison below
needs. -/
theorem isRightDerivedFunctor_modulePullback_comp_derivedSupportedSectionsOnClosed
    (hZ' : IsClosed (closedSubsetPreimage f Z)) :
    ((modulePullback f).mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z)
          hZ').IsRightDerivedFunctor
      (Functor.whiskerLeft ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
          (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') ≫
        Functor.whiskerRight (modulePullback f).mapDerivedCategoryFactorsh.inv
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ'))
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) := by
  have : (modulePullback f).mapDerivedCategory.IsRightDerivedFunctor
      (modulePullback f).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ (modulePullback f).mapDerivedCategory
      (modulePullback f).mapDerivedCategoryFactorsh
  refine Stacks.Cohomology.composite_isRightDerivedFunctor
    (Stacks.Cohomology.sheaf_exists_kInjective_resolution X) (modulePullback f)
    (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ') _ _ _ _ ?_
  intro I hI
  have := hI
  have : CochainComplex.IsKInjective
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    Stacks.Cohomology.openImmersionModulePullback_preservesKInjective f I
  exact isIso_derivedSupportedSectionsOnClosedUnit_app _ hZ'
    (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-! ### The comparison of the two derived composites -/

/-- **The comparison of functors `R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}`** for an open
immersion `f` of ringed spaces and a closed `Z ⊆ X`.

Both sides are right derived functors of the degreewise-isomorphic functors
`H_Z ⋙ (f|_{Z'})^*` and `f^* ⋙ H_{Z'}`, so the uniqueness of right derived functors supplies
the comparison; the degreewise isomorphism is
`supportedSectionsOnClosedPullbackNatIso`.

No compatibility with the canonical map of [Stacks, Tag 0G78] is claimed here, and none is
needed for `isIso_supportedPullbackMap_of_isOpenImmersion`.  This comparison is nevertheless
**equal** to that canonical map, by
`supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso` of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedPullbackComparison.lean`. -/
def derivedSupportedSectionsOnClosedPullbackNatIso (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z)) :
    derivedSupportedSectionsOnClosed X Z hZ ⋙
        derivedPullback (closedSubsetRestriction f Z) ≅
      derivedPullback f ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' :=
  let A := supportedSectionsOnClosedFunctor X Z hZ
  let A' := supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'
  let F := modulePullback f
  let G := modulePullback (closedSubsetRestriction f Z)
  let W := HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)
  let δ : A ⋙ G ≅ F ⋙ A' := supportedSectionsOnClosedPullbackNatIso f Z hZ hZ'
  let τ : A.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ G.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (A'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft (A.mapHomotopyCategory (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso δ (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ A'))
            (ComplexShape.up ℤ)).symm) DerivedCategory.Qh
  haveI := isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp f Z hZ
  haveI := isRightDerivedFunctor_modulePullback_comp_derivedSupportedSectionsOnClosed f Z hZ'
  Functor.isoWhiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)) ≪≫
    Functor.rightDerivedNatIso (derivedSupportedSectionsOnClosed X Z hZ ⋙ G.mapDerivedCategory)
      (F.mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosedCompUnit f Z hZ)
      (Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
          (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') ≫
        Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ'))
      W τ ≪≫
    Functor.isoWhiskerRight (derivedPullbackOpenImmersionIso f).symm
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')

/-! ### Tag 0G78 along an open immersion -/

/-- **[Stacks, Tag 0G78] along an open immersion, unconditionally.**  For an open immersion of
ringed spaces `f : X' ⟶ X`, a closed `Z ⊆ X` and `Z' = f^{-1}(Z)`, the canonical map

`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`

of [Stacks, Tag 0G78] is an isomorphism for every `K` in `D(𝒪_X)`.

Nothing is assumed beyond `f` being an open immersion and `Z` being closed.  The proof is
`isIso_supportedPullbackMap_of_natIso` applied to
`derivedSupportedSectionsOnClosedPullbackNatIso`. -/
@[stacks 0G78 "the canonical map is an isomorphism along an open immersion of ringed spaces, \
  unconditionally"]
theorem isIso_supportedPullbackMap_of_isOpenImmersion (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    IsIso (supportedPullbackMap f Z hZ hZ' K) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  exact isIso_supportedPullbackMap_of_natIso f Z hZ hZ'
    (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ') K

end Stacks.Cohomology.SupportedComplexes

end
