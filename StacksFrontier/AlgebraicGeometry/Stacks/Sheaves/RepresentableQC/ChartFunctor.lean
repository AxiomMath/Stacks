module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedCategory

/-!
# The affine étale charts of a representing algebraic space inside `𝒳_{affine}`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids which is representable by an
algebraic space `F`, through an equivalence `e` over `(Sch/S)_{fppf}` between `𝒳` and the
category of elements of `F`. Stacks 073M attaches to `e` a fully faithful functor
`F_{étale} ⥤ 𝒳` (`AlgebraicGeometry.Space.restrictionFunctor`) lying over the canonical
functor to `(Sch/S)_{fppf}`. On the affine charts of `F` (Stacks 0H01) its values lie over affine
schemes, so it corestricts to a functor from the affine étale site of `F` to the affine
subcategory `𝒳_{affine}` of Stacks 0H0A. This file constructs that functor and records how it
interacts with the étale topologies and with the rings of functions.

## Main definitions

* `AlgebraicGeometry.Stack.affineEtaleInclusion`: the functor
  `F_{affine, étale} ⥤ 𝒳_{affine}`.

## Main results

* `AlgebraicGeometry.Stack.affineEtaleInclusion_comp_toScheme`: the affine scheme underlying the
  image of an affine chart is the scheme of that chart.
* `AlgebraicGeometry.Stack.affineEtaleInclusion_isContinuous` and
  `AlgebraicGeometry.Stack.affineEtaleInclusion_isCocontinuous`: the functor is continuous and
  cocontinuous for the affine étale topology of `F` and the associated affine étale topology
  of `𝒳`.
* `AlgebraicGeometry.Stack.affineEtaleInclusion_op_comp_affineStructureCommPresheaf`: the ring of
  functions of `𝒳_{affine}`, restricted along the functor, is the presheaf of chart rings of
  the affine étale site of `F`, on the nose.
* `AlgebraicGeometry.Stack.isSheaf_of_cartesian_affineEtaleChartRings`: a cartesian presheaf of
  modules over the chart rings of the affine étale site of `F` is a sheaf, at any module
  universe containing that of the schemes.

## Implementation notes

The continuity and cocontinuity statements are deduced from those of the composite
`F_{affine, étale} ⥤ F_{étale} ⥤ 𝒳` (Stacks 04JS and 073M) through the affine inclusion
`𝒳_{affine} ⥤ 𝒳`, which is a dense subsite inclusion by Stacks 0H0B: a sieve of `𝒳_{affine}`
covers exactly when its image in `𝒳` does, and the inclusion is fully faithful.

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

universe u v w m

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- The object of `𝒳` attached to an affine étale chart of `F` lies over an affine scheme. -/
theorem isAffineObject_restrictionFunctor_obj (y : AffineEtale B S hS F) :
    IsAffineObject B S hS p ((restrictionFunctor B S hS F p e).obj y.obj) := by
  change IsAffine (((restrictionFunctor B S hS F p e ⋙ p) ⋙ BigFppfOver.toScheme B S hS).obj
    y.obj)
  rw [restrictionFunctor_comp]
  exact y.property

/-- **The affine étale charts of `F` inside `𝒳_{affine}`**: the functor of Stacks 073M,
restricted to the affine étale site of `F`, lands in the affine subcategory of `𝒳`. -/
noncomputable def affineEtaleInclusion : AffineEtale B S hS F ⥤ AffineCategory B S hS p :=
  ObjectProperty.lift _ (AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e)
    (isAffineObject_restrictionFunctor_obj B S hS F p e)

/-- Followed by the inclusion of `𝒳_{affine}` into `𝒳`, the functor is the functor of Stacks 073M
restricted to the affine charts. -/
theorem affineEtaleInclusion_comp_inclusion :
    affineEtaleInclusion B S hS F p e ⋙ AffineCategory.inclusion B S hS p =
      AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e :=
  rfl

/-- The image of an affine chart lies over the object of the big fppf site underlying it. -/
theorem affineEtaleInclusion_comp_inclusion_comp :
    affineEtaleInclusion B S hS F p e ⋙ AffineCategory.inclusion B S hS p ⋙ p =
      AffineEtale.toOver B S hS F := by
  change AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e ⋙ p = _
  rw [restrictionFunctor_comp]

/-- **The affine scheme underlying the image of an affine chart is the scheme of the chart.** -/
theorem affineEtaleInclusion_comp_toScheme :
    affineEtaleInclusion B S hS F p e ⋙ AffineCategory.toScheme B S hS p =
      AffineEtale.toScheme B S hS F := by
  change (affineEtaleInclusion B S hS F p e ⋙ AffineCategory.inclusion B S hS p ⋙ p) ⋙
    BigFppfOver.toScheme B S hS = _
  rw [affineEtaleInclusion_comp_inclusion_comp]

/-- The functor `affineEtaleInclusion` is full. -/
instance affineEtaleInclusion_full : (affineEtaleInclusion B S hS F p e).Full := by
  unfold affineEtaleInclusion
  infer_instance

/-- The functor `affineEtaleInclusion` is faithful. -/
instance affineEtaleInclusion_faithful : (affineEtaleInclusion B S hS F p e).Faithful := by
  unfold affineEtaleInclusion
  infer_instance

/-- **The rings of functions of `𝒳_{affine}`, restricted to the affine étale charts of `F`, are
the chart rings of `F`**: the two presheaves of commutative rings on `F_{affine, étale}` are
equal. -/
theorem affineEtaleInclusion_op_comp_affineStructureCommPresheaf :
    (affineEtaleInclusion B S hS F p e).op ⋙ affineStructureCommPresheaf B S hS p =
      affineEtaleChartRings B S hS F := by
  change (affineEtaleInclusion B S hS F p e ⋙ AffineCategory.toScheme B S hS p).op ⋙ Scheme.Γ = _
  rw [affineEtaleInclusion_comp_toScheme]
  rfl

/-! ### Continuity and cocontinuity -/

/-- The functor `F_{affine, étale} ⥤ 𝒳_{affine}` preserves fibre products. -/
instance affineEtaleInclusion_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (affineEtaleInclusion B S hS F p e) := by
  have : PreservesLimitsOfShape WalkingCospan
      (affineEtaleInclusion B S hS F p e ⋙ AffineCategory.inclusion B S hS p) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (AffineCategory.inclusion B S hS p)

section Continuity

variable (hF : IsAlgebraicSpace B S hS F) (hp : p.IsFiberedInGroupoids)
include hF hp

/-- The composite `F_{affine, étale} ⥤ F_{étale} ⥤ 𝒳` is continuous for the étale topologies. -/
theorem inclusion_comp_restrictionFunctor_isContinuous :
    (AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e).IsContinuous
      (AffineEtale.topology B S hS F) (associatedTopology B S hS p B.etaleTopology) := by
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have : (restrictionFunctor B S hS F p e).IsContinuous (Space.SmallEtale.topology B S hS F)
      (associatedTopology B S hS p B.etaleTopology) :=
    restrictionFunctor_isContinuous B S hS F p hp e
  exact Functor.isContinuous_comp _ _ _ (Space.SmallEtale.topology B S hS F) _

/-- The composite `F_{affine, étale} ⥤ F_{étale} ⥤ 𝒳` is cocontinuous for the étale
topologies. -/
theorem inclusion_comp_restrictionFunctor_isCocontinuous :
    (AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e).IsCocontinuous
      (AffineEtale.topology B S hS F) (associatedTopology B S hS p B.etaleTopology) := by
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).1
  have : (restrictionFunctor B S hS F p e).IsCocontinuous (Space.SmallEtale.topology B S hS F)
      (associatedTopology B S hS p B.etaleTopology) :=
    restrictionFunctor_isCocontinuous B S hS F p hp e
  exact isCocontinuous_comp _ _ _ (Space.SmallEtale.topology B S hS F)

/-- **The functor `F_{affine, étale} ⥤ 𝒳_{affine}` is continuous** for the affine étale topology
of `F` and the associated affine étale topology of `𝒳`. -/
theorem affineEtaleInclusion_isContinuous :
    (affineEtaleInclusion B S hS F p e).IsContinuous (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS)) := by
  have hd := isDenseSubsite_affineInclusion_etale B S hS p hp
  have := inclusion_comp_restrictionFunctor_isContinuous B S hS F p e hF hp
  have hcp : CoverPreserving (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
      (affineEtaleInclusion B S hS F p e) := by
    refine ⟨fun {y} R hR => ?_⟩
    rw [← hd.functorPushforward_mem_iff, ← Sieve.functorPushforward_comp]
    exact (CoverPreserving.of_isContinuous
      (AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e) _ _).cover_preserve hR
  let _ : Functor.PreservesOneHypercovers.{u + 1} (affineEtaleInclusion B S hS F p e)
      (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS)) :=
    Functor.PreservesOneHypercovers.of_coverPreserving hcp
  infer_instance

/-- **The functor `F_{affine, étale} ⥤ 𝒳_{affine}` is cocontinuous** for the affine étale
topology of `F` and the associated affine étale topology of `𝒳`: an étale covering of the image
of an affine chart is refined by a covering of the chart by affine charts. -/
theorem affineEtaleInclusion_isCocontinuous :
    (affineEtaleInclusion B S hS F p e).IsCocontinuous (AffineEtale.topology B S hS F)
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS)) := by
  have hd := isDenseSubsite_affineInclusion_etale B S hS p hp
  have := inclusion_comp_restrictionFunctor_isCocontinuous B S hS F p e hF hp
  refine ⟨fun {y} R hR => ?_⟩
  rw [← hd.functorPushforward_mem_iff] at hR
  have h := (AffineEtale.inclusion B S hS F ⋙ restrictionFunctor B S hS F p e).cover_lift
    (AffineEtale.topology B S hS F) (associatedTopology B S hS p B.etaleTopology) hR
  change Sieve.functorPullback
    (affineEtaleInclusion B S hS F p e ⋙ AffineCategory.inclusion B S hS p)
      (Sieve.functorPushforward (AffineCategory.inclusion B S hS p) R) ∈ _ at h
  rwa [Sieve.functorPullback_comp, Sieve.functorPullback_functorPushforward_eq] at h

end Continuity

/-! ### Cartesian modules over the chart rings are sheaves -/

/-- **A cartesian presheaf of modules over the chart rings of the affine étale site of `F` is a
sheaf**, at every module universe containing the universe of the schemes. -/
theorem isSheaf_of_cartesian_affineEtaleChartRings
    (M : PresheafOfModules.{max m u}
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (AffineEtale B S hS F)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, m} M f)) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf := by
  refine Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'.{u, u + 1, u, m, u,
    u + 1} (AffineEtale.toScheme B S hS F) (affineEtaleChartRings B S hS F) ?_ ?_ M hM
    (AffineEtale.topology B S hS F) ?_
  · intro U E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineEtale.toScheme B S hS F))).mp hE
    exact faithfullyFlat_pi_affineEtaleChartRings B S hS F E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineEtaleChartRings B S hS F h
  · intro U T hT
    obtain ⟨E, hfin, hE, -, hle⟩ := Stacks.Sites.exists_finite_flat_covering_refinement
      (AffineEtale.toScheme B S hS F) (AffineEtale.precoverage B S hS F)
      (affineEtale_covering_finite_flat B S hS F) T hT
    exact ⟨E, hfin, hE, hle⟩

end AlgebraicGeometry.Stack
