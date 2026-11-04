module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianPushforwardExact
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomology

/-!
# Complexes supported on a closed subset

Let `Z` be a closed subset of a ringed space `X`, viewed as a ringed space `(Z, 𝒪_X|_Z)` by
restricting the structure sheaf, and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion.  Then
`i_*` is exact, so it induces a functor on unbounded derived categories directly, and the
cohomology sheaves of `i_* K` are supported on `Z`.

## Main definitions

* `closedSubsetRingedSpace`: the closed subset with the restricted structure sheaf.
* `closedSubsetInclusion`: the inclusion morphism of ringed spaces.
* `SupportedDerivedCategory`: the full subcategory of complexes with cohomology supported
  on `Z`.
* `derivedPushforwardToSupported`: derived pushforward, corestricted to that subcategory.

## Main results

* `pushforward_supported`: the cohomology sheaves of `i_* K` are supported on `Z`.

## Implementation notes

The support statement is checked one cohomology sheaf at a time.  Because `i_*` is exact, it
commutes with the cohomology functors of the derived category, so the `n`-th cohomology sheaf
of `i_* K` is `i_*` of the `n`-th cohomology sheaf of `K`.  That is the content of
`exactFunctorDerivedHomologyIso`, imported from
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomology`, where
it is proved for a general exact functor by lifting the complex-level comparison
`exactFunctorHomologyIso` through the localization `DerivedCategory.Q`.

Having identified the cohomology sheaf as a pushforward, the vanishing of its stalks off `Z`
is the forward direction of Tag 01AX: the underlying sheaf of abelian groups of a pushforward
of sheaves of modules *is* the abelian-sheaf pushforward (the identification
`PresheafOfModules.pushforwardCompToPresheaf` is `Iso.refl`), so the cohomology sheaf lies in
the essential image of the abelian-sheaf pushforward along `Z ⟶ X`, and
`Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_support_subset` bounds its
support by the image of `Z`.

Exactness of `i_*` is Tag 08KS: left exactness because `i_*` is a right adjoint, and right
exactness from preservation of epimorphisms, which is where the closed-embedding hypothesis
enters.  Both halves are consumed here through
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`.

## References

* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-- The ringed space on a closed subset, with the restricted structure sheaf. -/
noncomputable abbrev closedSubsetRingedSpace (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    RingedSpace.{u, u} :=
  AlgebraicGeometry.RingedSpace.inverseImage X (ClosedImmersionSheaves.closedSubsetInclusion Z)

/-- The canonical inclusion of a closed subset as a morphism of ringed spaces. -/
noncomputable abbrev closedSubsetInclusion (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    closedSubsetRingedSpace X Z ⟶ X :=
  AlgebraicGeometry.RingedSpace.inverseImageProjection X
    (ClosedImmersionSheaves.closedSubsetInclusion Z)

/-- The derived category of complexes with cohomology supported on `Z`. -/
noncomputable abbrev SupportedDerivedCategory (X : RingedSpace.{u, u}) (Z : Set X.carrier) :=
  let P : ObjectProperty (DerivedCategory
    (Stacks.Cohomology.DerivedPushforwardComposition.ModuleSheaves X)) :=
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
  P.FullSubcategory

/-- The inclusion of a closed subset is a closed embedding on underlying spaces. -/
theorem closedSubsetInclusion_isClosedEmbedding (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    Topology.IsClosedEmbedding (closedSubsetInclusion X Z).hom.base :=
  hZ.isClosedEmbedding_subtypeVal

/-- **Stacks 08KS.** Pushforward along the inclusion of a closed subset is left exact. -/
theorem pushforward_preservesFiniteLimits (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z)) :=
  Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward _

/-- **Stacks 08KS.** Pushforward along the inclusion of a closed subset is right exact. -/
theorem pushforward_preservesFiniteColimits (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z)) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward _
    (closedSubsetInclusion_isClosedEmbedding X Z hZ)

/-! ### Part (1): pushforward lands in the supported subcategory -/

/-- **Stacks 0AEF, part (1).** For `K` in the derived category of `𝒪_X|_Z`-modules, the
cohomology sheaves of `i_* K` are supported on `Z`. -/
@[stacks 0AEF "part (1)"]
theorem pushforward_supported (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (K : DerivedCategory (Stacks.Cohomology.DerivedPushforwardComposition.ModuleSheaves
      (closedSubsetRingedSpace X Z))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj K) := by
  set i := closedSubsetInclusion X Z with hi
  let _ : PreservesFiniteLimits (modulePushforward i) :=
    pushforward_preservesFiniteLimits X Z
  let _ : PreservesFiniteColimits (modulePushforward i) :=
    pushforward_preservesFiniteColimits X Z hZ
  intro n x hx
  set M := (DerivedCategory.homologyFunctor _ n).obj K with hM
  set G := (SheafOfModules.toSheaf (structureSheafRing X)).obj
    ((DerivedCategory.homologyFunctor _ n).obj
      ((modulePushforward i).mapDerivedCategory.obj K)) with hG
  have e : (closedInclusionPushforward (TopCat.of Z) X.carrier i.hom.base).obj
      ((SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))).obj M) ≅ G :=
    Iso.refl _ ≪≫ (SheafOfModules.toSheaf (structureSheafRing X)).mapIso
      ((exactFunctorDerivedHomologyIso (modulePushforward i) n).app K).symm
  have hess : (closedInclusionPushforward (TopCat.of Z) X.carrier i.hom.base).essImage G :=
    ⟨_, ⟨e⟩⟩
  have hsupport :=
    (Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_support_subset
      i.hom.base (closedSubsetInclusion_isClosedEmbedding X Z hZ) G).mp hess
  have hxrange : x ∉ Set.range i.hom.base := by
    rintro ⟨z, rfl⟩
    exact hx z.property
  have hnot : x ∉ Stacks.AbelianSheaf.support G := fun hs ↦ hxrange (hsupport hs)
  have hzero : IsZero (TopCat.Presheaf.stalk G.1 x) := by
    by_contra hnonzero
    exact hnot hnonzero
  exact hzero

/-- Derived pushforward along the inclusion of a closed subset, corestricted to the complexes
with cohomology supported on `Z`. -/
noncomputable def derivedPushforwardToSupported (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    DerivedCategory (Stacks.Cohomology.DerivedPushforwardComposition.ModuleSheaves
      (closedSubsetRingedSpace X Z)) ⥤
      SupportedDerivedCategory X Z :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  let P : ObjectProperty (DerivedCategory
    (Stacks.Cohomology.DerivedPushforwardComposition.ModuleSheaves X)) :=
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
  P.lift (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory
    (pushforward_supported X Z hZ)

end Stacks.Cohomology.SupportedComplexes

end
