module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# The direct image of the structure sheaf along a closed immersion, in degree zero

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `S`. The complex `i_*𝒪_Z[0]` of
`D(𝒪_X)` is supported on the image `|Z|` of `|i|`, and it is pseudo-coherent when `X` is
Noetherian. These are the two halves of clause (5) of Stacks 0CTR over a Noetherian base.

## Main results

* `AlgebraicGeometry.Space.cohomologySupportedOn_single_structureSheafPushforward`: the support.
* `AlgebraicGeometry.Space.isPseudoCoherent_single_structureSheafPushforward`: pseudo-coherence
  on a Noetherian algebraic space, by Stacks 08IK.

## References

* [Stacks Project, Tag 0CTR](https://stacks.math.columbia.edu/tag/0CTR)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS}

/-- The direct image of the structure sheaf along a closed immersion is supported on the image
of the closed immersion. -/
theorem supportOfSheaf_structureSheafPushforward_subset (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (structureSheafPushforward B S hS i))
      ⊆ Set.range (pointsMap B S hS Z.1 i.hom) :=
  supportOfSheaf_modulePushforward_subset_of_isClosed B S hS i _ _
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 i.hom hi) fun z _ => ⟨z, rfl⟩

/-- **Stacks 0CTR, clause (5), support part, for `E = (b, c)_*𝒪_Z`.** The complex `i_*𝒪_Z[0]` is
supported on the image of the closed immersion `i`. -/
theorem cohomologySupportedOn_single_structureSheafPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    CohomologySupportedOn B S hS X.1 X.2 (Set.range (pointsMap B S hS Z.1 i.hom))
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
        (structureSheafPushforward B S hS i)) := by
  intro n
  let M := structureSheafPushforward B S hS i
  let H := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
    ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M)
  rcases eq_or_ne n 0 with rfl | hn
  · exact (supportOfSheaf_eq_of_iso B S hS X ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (Modules.{u, u} B S hS X.1 X.2) 0).app M)).trans_subset
      (supportOfSheaf_structureSheafPushforward_subset B S hS i hi)
  · have hH : IsZero H := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact DerivedCategory.isZero_of_isGE (C := Modules.{u, u} B S hS X.1 X.2) _ 0 n h
      · exact DerivedCategory.isZero_of_isLE (C := Modules.{u, u} B S hS X.1 X.2) _ 0 n h
    exact ((supportOfSheaf_eq_empty_iff_isZero B S hS X H).2 hH).trans_subset
      (Set.empty_subset _)

/-- **Stacks 0CTR, clause (5), pseudo-coherence part, for `E = (b, c)_*𝒪_Z`, over a Noetherian
algebraic space.** For a closed immersion `i : Z ⟶ X` into a Noetherian algebraic space, the
complex `i_*𝒪_Z[0]` is pseudo-coherent: by Stacks 08IK, its only cohomology sheaf `i_*𝒪_Z` being
coherent. -/
theorem isPseudoCoherent_single_structureSheafPushforward (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsNoetherian B S hS hZ X.1) (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
        (structureSheafPushforward B S hS i)) := by
  let M := structureSheafPushforward B S hS i
  refine (isPseudoCoherent_iff_isCoherent_homology hZ X hX
    ⟨_, derivedCategoryB_singleFunctor_obj B S hS X.1 X.2 M
      (isQuasicoherentOnSite_structureSheafPushforward B S hS i hi)⟩).2 ⟨⟨0, fun n hn =>
      DerivedCategory.isZero_of_isLE (C := Modules.{u, u} B S hS X.1 X.2) _ 0 n hn⟩, fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact isCoherent_of_iso B S hS X.2 ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (Modules.{u, u} B S hS X.1 X.2) 0).app M).symm
      (isCoherent_structureSheafPushforward B S hS hX.2.2 i hi)
  · apply IsCoherent.of_isZero
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE (C := Modules.{u, u} B S hS X.1 X.2) _ 0 n h
    · exact DerivedCategory.isZero_of_isLE (C := Modules.{u, u} B S hS X.1 X.2) _ 0 n h

end AlgebraicGeometry.Space

end
