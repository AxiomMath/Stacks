module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the projection-formula map along the inclusion of a closed subset

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The projection-formula map of
[Stacks, Tag 0B53] is

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap`, and [Stacks, Tag 0B55] says
it is an isomorphism whenever `f` is a homeomorphism onto a closed subset.

Writing the map through the unit of `Lf^* ⊣ Rf_*` splits it into three factors,

`Rf_*E ⊗^𝐋 K --η--> Rf_*Lf^*(Rf_*E ⊗^𝐋 K) --Rf_*(α)--> Rf_*(Lf^*Rf_*E ⊗^𝐋 Lf^*K)
   --Rf_*(ε ⊗ 1)--> Rf_*(E ⊗^𝐋 Lf^*K)`,

of which the middle one is invertible for *every* morphism of ringed spaces, the comparison `α`
of [Stacks, Tag 079U] being an isomorphism of bifunctors.  So invertibility of the whole map is
equivalent to invertibility of the outer two, and this file carries that reduction out and then
applies it to the inclusion of a closed subset.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_iff_isIso_unit`: over an
  abstract adjunction, with the comparison and the counit invertible, the projection-formula map
  is invertible **exactly when** the unit is invertible at `A (R G, H)`.  Nothing of the geometry
  enters, and nothing is lost: this is an equivalence, not a sufficient condition.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_of_mem_essImage`: for a
  fully faithful right adjoint the counit hypothesis is automatic and the unit hypothesis becomes
  membership of `A (R G, H)` in the essential image of `R`.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_iff_isIso_unit` and
  `isIso_projectionFormulaMap_of_mem_essImage`: the same two statements at `Lf^* ⊣ Rf_*` and the
  derived tensor products, for an arbitrary morphism of ringed spaces.
* `Stacks.Cohomology.SupportedComplexes.fullyFaithful_derivedPushforward_closedSubsetInclusion`:
  for the inclusion `i` of a closed subset, `Ri_*` is fully faithful, and
  `isIso_derivedAdjunction_counit_app_closedSubsetInclusion`: its counit `Li^*Ri_*E ⟶ E` is
  therefore invertible, unconditionally.
* `Stacks.Cohomology.SupportedComplexes.isIso_projectionFormulaMap_closedSubsetInclusion`:
  **[Stacks, Tag 0B55] for the inclusion of a closed subset, on one hypothesis** — that
  `Ri_*E ⊗^𝐋_{𝒪_X} K` has its cohomology sheaves supported on `Z`.

## The inclusion of a closed subset

Everything above except the last hypothesis is unconditional.  Concretely, for
`i = closedSubsetInclusion X Z` with `Z` closed:

* the comparison of [Stacks, Tag 079U] is an isomorphism of bifunctors
  (`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`), so the middle factor is
  invertible with no hypothesis at all;
* `Ri_*` is fully faithful.  This is *not* a hypothesis: the functor `i_*^D` induced on derived
  categories by the exact functor `i_*` has invertible unit against `R𝓗_Z`, which is
  [Stacks, Tag 0A3B] part (2) in the form
  `Stacks.Cohomology.SupportedComplexes.isIso_unit_derivedPushforwardAdjunction`, hence `i_*^D`
  is fully faithful; and `Ri_*` is isomorphic to it by the comparison of [Stacks, Tag 0E2K],
  `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, since `i_*` is exact;
* consequently the counit `Li^*Ri_*E ⟶ E` is invertible, so the third factor is invertible;
* the unit at `Ri_*E ⊗^𝐋 K` is invertible as soon as that object lies in the essential image of
  `Ri_*`, and by [Stacks, Tag 0AEF] part (2),
  `Stacks.Cohomology.SupportedComplexes.essImage_derivedPushforward_of_supported`, a complex
  whose cohomology sheaves are supported on `Z` does lie there.

The one hypothesis is the *support* statement: that the derived tensor product of a complex
pushed forward from `Z` with an arbitrary complex on `X` again has cohomology supported on `Z`.
It is a statement about the derived tensor product and not a step of the argument here, and it
is the explicit hypothesis `hsupp` of `isIso_projectionFormulaMap_closedSubsetInclusion`.  Its
underived counterpart holds: `Stacks.AffineProjectionFormula.smul_tensorSheaf_eq_zero` makes the
kernel ideal annihilate `i_*𝒢 ⊗ ℋ`, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` ([Stacks, Tag 01CB]) kills its
stalks off `Z`.

## Relation to the underived projection formula

`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap` proves the *underived* projection
formula `f_*𝒢 ⊗ ℋ ≅ f_*(𝒢 ⊗ f^*ℋ)` for a `ClosedQuotientMorphismOfRingedSpaces`, i.e. a
homeomorphism onto a closed subset whose comorphism of structure sheaves is in addition locally
surjective.  That extra condition is a genuine strengthening of the hypothesis of
[Stacks, Tag 0B55] — for a homeomorphism of spaces with an arbitrary injection of structure
sheaves the three-factor argument used there breaks down, because `f_*` is then not fully
faithful — so the result does not generalise to a bare closed embedding by that route.

It is, however, *not* a restriction for the inclusion of a closed subset.  The comorphism
`𝒪_X ⟶ i_*(i^{-1}𝒪_X)` of that inclusion *is* locally surjective — this is
`Stacks.SheafOfModules.SupportedSections.isLocallySurjective_inverseImageProjection_c`, the
input of `Stacks.SheafOfModules.SupportedSections.fullyFaithfulModulePushforwardClosedSubset` —
so `closedSubsetInclusion X Z` satisfies the closed-quotient hypothesis and the underived
projection formula applies to it with no extra assumption.  Full faithfulness of `i_*` is what
`fullyFaithfulMapDerivedCategoryClosedSubsetInclusion` below rests on, through
[Stacks, Tag 0A3B].

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0A3B](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.ProjectionFormula

/-! ### The abstract reduction to the unit of the adjunction -/

section Abstract

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The second and third factors of the projection-formula map together: invertible as soon as
the comparison is invertible at `(R G, H)` and the counit is invertible at `G`.  This holds for
every morphism of ringed spaces at the derived tensor products, the comparison of
[Stacks, Tag 079U] being an isomorphism of bifunctors. -/
lemma isIso_adjunctionTensorMap_tail (G : D) (H : C)
    [IsIso (α.app (R.obj G, H))] [IsIso (adj.counit.app G)] :
    IsIso (R.map (α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)))) := by
  have hprod : IsIso (adj.counit.app G ×ₘ 𝟙 (L.obj H)) :=
    ((asIso (adj.counit.app G)).prod (Iso.refl (L.obj H))).isIso_hom
  infer_instance

/-- **The abstract projection formula from invertibility of the unit.**  If the comparison `α` is
invertible at `(R G, H)`, the counit at `G` and the unit at `A (R G, H)`, then the abstract
projection-formula map `A (R G, H) ⟶ R (B (G, L H))` is invertible. -/
theorem isIso_adjunctionTensorMap_of_isIso_unit (G : D) (H : C)
    [IsIso (α.app (R.obj G, H))] [IsIso (adj.counit.app G)]
    [IsIso (adj.unit.app (A.obj (R.obj G, H)))] :
    IsIso (adjunctionTensorMap adj A B α G H) := by
  have htail := isIso_adjunctionTensorMap_tail adj A B α G H
  rw [adjunctionTensorMap_eq_unit_comp adj A B α G H]
  infer_instance

/-- **The abstract projection formula map is invertible exactly when the unit is.**  With the
comparison and the counit invertible, the remaining two factors of the three-factor
decomposition are an isomorphism, so nothing is lost in either direction: the content of the
projection formula is precisely that `A (R G, H)` is taken to itself by `R L`. -/
theorem isIso_adjunctionTensorMap_iff_isIso_unit (G : D) (H : C)
    [IsIso (α.app (R.obj G, H))] [IsIso (adj.counit.app G)] :
    IsIso (adjunctionTensorMap adj A B α G H) ↔
      IsIso (adj.unit.app (A.obj (R.obj G, H))) := by
  refine ⟨fun h => ?_, fun _ => isIso_adjunctionTensorMap_of_isIso_unit adj A B α G H⟩
  have htail := isIso_adjunctionTensorMap_tail adj A B α G H
  rw [adjunctionTensorMap_eq_unit_comp adj A B α G H] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ htail h

/-- **The abstract projection formula for a fully faithful right adjoint.**  The counit is then
invertible everywhere, and the unit is invertible exactly on the essential image of `R`, so the
only hypothesis left is that `A (R G, H)` lie in that essential image. -/
theorem isIso_adjunctionTensorMap_of_mem_essImage (G : D) (H : C)
    [R.Full] [R.Faithful] [IsIso (α.app (R.obj G, H))]
    (hmem : R.essImage (A.obj (R.obj G, H))) :
    IsIso (adjunctionTensorMap adj A B α G H) := by
  have hcounit : IsIso (adj.counit.app G) :=
    Stacks.AffineProjectionFormula.isIso_counit_app adj G
  have hunit : IsIso (adj.unit.app (A.obj (R.obj G, H))) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage adj).mpr hmem
  exact isIso_adjunctionTensorMap_of_isIso_unit adj A B α G H

end Abstract

end Stacks.AlgebraicGeometry.ProjectionFormula

/-! ### The derived projection-formula map on a ringed space -/

namespace Stacks.Cohomology.DerivedProjectionFormula

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Every component of the derived pullback-tensor comparison of [Stacks, Tag 079U] is an
isomorphism: the comparison is the forward map of the isomorphism of bifunctors
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`. -/
instance isIso_pullbackTensorComparison_app
    (p : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ×
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso ((pullbackTensorComparison f).app p) :=
  ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).app p).isIso_hom

/-- **The derived projection-formula map is invertible exactly when the unit of `Lf^* ⊣ Rf_*` is
invertible at `Rf_*E ⊗^𝐋 K`**, granted invertibility of the counit at `E`.  The comparison of
[Stacks, Tag 079U] is unconditionally invertible, so no further hypothesis enters; this is the
three-factor decomposition of the map of [Stacks, Tag 0B53] read as an equivalence. -/
theorem isIso_projectionFormulaMap_iff_isIso_unit
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hcounit : IsIso ((derivedAdjunction f).counit.app E)) :
    IsIso (projectionFormulaMap f E K) ↔
      IsIso ((derivedAdjunction f).unit.app
        (((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj E)).obj K)) :=
  Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_iff_isIso_unit
    (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) E K

/-- **The derived projection-formula map is invertible when `Rf_*` is fully faithful and
`Rf_*E ⊗^𝐋 K` lies in its essential image.**  This is [Stacks, Tag 0B53]'s map, so the statement
is about the canonical morphism and not about an unspecified isomorphism of its endpoints. -/
theorem isIso_projectionFormulaMap_of_mem_essImage
    [(derivedPushforward f).Full] [(derivedPushforward f).Faithful]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hmem : (derivedPushforward f).essImage
      (((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj E)).obj K)) :
    IsIso (projectionFormulaMap f E K) :=
  Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_of_mem_essImage
    (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) E K hmem

end Stacks.Cohomology.DerivedProjectionFormula

/-! ### The inclusion of a closed subset -/

namespace Stacks.Cohomology.SupportedComplexes

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

include hZ

/-- **[Stacks, Tag 0A3B] part (2) as full faithfulness.**  The functor `i_*^D` induced on derived
categories by pushforward along the inclusion of a closed subset is fully faithful: the unit of
its adjunction with `R𝓗_Z` is invertible. -/
def fullyFaithfulMapDerivedCategoryClosedSubsetInclusion :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.FullyFaithful :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  Adjunction.fullyFaithfulLOfIsIsoUnit (derivedPushforwardAdjunction X Z hZ)

/-- The comparison of [Stacks, Tag 0E2K] for the inclusion of a closed subset: pushforward is
exact, so the functor it induces on derived categories is its own total right derived functor
`Ri_*`, which is the one the projection formula of [Stacks, Tag 0B53] is stated for. -/
abbrev closedSubsetPushforwardComparison :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ≅
      derivedPushforward (closedSubsetInclusion X Z) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
    (modulePushforward (closedSubsetInclusion X Z))

/-- **`Ri_*` is fully faithful for the inclusion of a closed subset.**  It is isomorphic, by the
comparison of [Stacks, Tag 0E2K], to the functor induced on derived categories by the exact
functor `i_*`, which is fully faithful by [Stacks, Tag 0A3B] part (2). -/
def fullyFaithful_derivedPushforward_closedSubsetInclusion :
    (derivedPushforward (closedSubsetInclusion X Z)).FullyFaithful :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := (fullyFaithfulMapDerivedCategoryClosedSubsetInclusion X Z hZ).full
  letI := (fullyFaithfulMapDerivedCategoryClosedSubsetInclusion X Z hZ).faithful
  letI : (derivedPushforward (closedSubsetInclusion X Z)).Full :=
    Functor.Full.of_iso (closedSubsetPushforwardComparison X Z hZ)
  letI : (derivedPushforward (closedSubsetInclusion X Z)).Faithful :=
    Functor.Faithful.of_iso (closedSubsetPushforwardComparison X Z hZ)
  .ofFullyFaithful _

/-- **The counit `Li^*Ri_*E ⟶ E` of the derived adjunction of [Stacks, Tag 079W] is invertible
for the inclusion of a closed subset**, with no hypothesis on `E`: the right adjoint `Ri_*` is
fully faithful. -/
theorem isIso_derivedAdjunction_counit_app_closedSubsetInclusion
    (E : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    IsIso ((derivedAdjunction (closedSubsetInclusion X Z)).counit.app E) :=
  let := (fullyFaithful_derivedPushforward_closedSubsetInclusion X Z hZ).full
  let := (fullyFaithful_derivedPushforward_closedSubsetInclusion X Z hZ).faithful
  Stacks.AffineProjectionFormula.isIso_counit_app
    (derivedAdjunction (closedSubsetInclusion X Z)) E

/-- **[Stacks, Tag 0AEF] part (2) for `Ri_*`.**  A complex of `𝒪_X`-modules whose cohomology
sheaves are supported on the closed subset `Z` lies in the essential image of the total right
derived pushforward `Ri_*`, and not merely in that of the functor induced by `i_*`: the two are
isomorphic by [Stacks, Tag 0E2K]. -/
theorem essImage_derivedPushforward_closedSubsetInclusion_of_supported
    (C : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hC : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z C) :
    (derivedPushforward (closedSubsetInclusion X Z)).essImage C := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  obtain ⟨W, ⟨e⟩⟩ := essImage_derivedPushforward_of_supported X Z hZ C hC
  exact ⟨W, ⟨((closedSubsetPushforwardComparison X Z hZ).app W).symm ≪≫ e⟩⟩

/-- **[Stacks, Tag 0B55] for the inclusion of a closed subset**, on the single hypothesis that
the derived tensor product `Ri_*E ⊗^𝐋_{𝒪_X} K` has its cohomology sheaves supported on `Z`.

The projection-formula map of [Stacks, Tag 0B53]

`Ri_*E ⊗^𝐋_{𝒪_X} K ⟶ Ri_*(E ⊗^𝐋_{𝒪_X|_Z} Li^*K)`

is then an isomorphism, for arbitrary `E` in `D(𝒪_X|_Z)` and `K` in `D(𝒪_X)`.  Everything else
the argument needs is proved: the comparison of [Stacks, Tag 079U] is invertible for
every morphism of ringed spaces, and `Ri_*` is fully faithful for this `i`, so its counit is
invertible and its unit is invertible exactly on its essential image, which by
[Stacks, Tag 0AEF] part (2) contains every complex supported on `Z`. -/
/-
NO `@[stacks 0B55]` ATTRIBUTE IS CARRIED, DELIBERATELY.

[Stacks, Tag 0B55] concludes that (0B53) is an isomorphism *always*, given only that `i` is a
homeomorphism onto a closed subset. The statement below concludes it only given `hsupp`, that
`Ri_*E ⊗ᴸ K` has cohomology sheaves supported on `Z`. That is a genuine *weakening* of the tag
rather than a citation of a missing input, so the attribute is withheld.

Nothing else about the source is altered: `E` and `K` are arbitrary objects of their derived
categories, with no finiteness, flatness, boundedness or quasi-coherence, and the source's own
hypothesis on `i` is not strengthened. `hsupp` is a condition on the *object* `Ri_*E ⊗ᴸ K`, not
on the map whose invertibility is concluded, and it is consumed exactly once, to place that
object in the essential image of `Ri_*` via [Stacks, Tag 0AEF] part (2).
-/
theorem isIso_projectionFormulaMap_closedSubsetInclusion
    (E : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hsupp : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
      (((derivedTensorProductFunctor X.sheaf).obj
        ((derivedPushforward (closedSubsetInclusion X Z)).obj E)).obj K)) :
    IsIso (projectionFormulaMap (closedSubsetInclusion X Z) E K) :=
  let := (fullyFaithful_derivedPushforward_closedSubsetInclusion X Z hZ).full
  let := (fullyFaithful_derivedPushforward_closedSubsetInclusion X Z hZ).faithful
  isIso_projectionFormulaMap_of_mem_essImage (closedSubsetInclusion X Z) E K
    (essImage_derivedPushforward_closedSubsetInclusion_of_supported X Z hZ _ hsupp)

end Stacks.Cohomology.SupportedComplexes

end
