module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonSituation
public import StacksFrontier.CategoryTheory.Sites.SheafEquivOfTopologyEq
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.CohomologicalDescent
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Size.FiniteType
import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement
import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi
import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiPullbackWeakSerre

/-!
# The situation comparing fppf and étale cohomology

Let `B` be a big fppf site and let `(Sch/S)_étale` be the étale site on the same category of
schemes (`AlgebraicGeometry.associatedBigEtaleSite`). Stacks 0F0H puts the comparison morphism
`ε : (Sch/S)_fppf ⟶ (Sch/S)_étale` into Situation 0EZ3 of the chapter on cohomology on sites,
with `𝒫` the class of finite morphisms and, for every `X`, the class `𝒜'_X` of abelian sheaves
on `(Sch/X)_étale` of the form `π_X⁻¹F` for `F` an abelian sheaf on the small étale site of `X`.
This file sets up these data and proves that `𝒜'_X` is a weak Serre subcategory and that
properties (0EZ4), (0EZ5), (0EZ6) and (0EZ8) of the situation hold, following the source:

* weak Serre: `π_X⁻¹` is exact and fully faithful with exact right adjoint (Stacks 0DDI);
* (0EZ4): finite morphisms are stable under base change (Stacks 01WL);
* (0EZ5): relocalization of `π_Y⁻¹F` along `f : X ⟶ Y` is `π_X⁻¹f_small⁻¹F` (Stacks 021I);
* (0EZ6): `π_X⁻¹F` is an fppf sheaf (Stacks 0DDL);
* (0EZ8): an fppf covering is refined through an étale covering and finite locally free
  surjections (Stacks 0DET).

Property (0EZ7), that the higher direct images along a finite morphism preserve `𝒜'`, is
reduced by `AlgebraicGeometry.fppfEtaleWeakSerre_rightDerived_of_exact` to the exactness of the
direct image along a finite morphism and to the identification `f_{big,*}π_X⁻¹ = π_Y⁻¹f_{small,*}`
in degree zero, which are the two inputs of the proof of Stacks 0DDJ (4).

## Main definitions

* `AlgebraicGeometry.fppfEtaleFinite`: the class `𝒫` of finite morphisms.
* `AlgebraicGeometry.fppfEtaleProjectionPullback`,
  `AlgebraicGeometry.fppfEtaleProjectionRestriction` and
  `AlgebraicGeometry.fppfEtaleProjectionAdjunction`: `π_X⁻¹ ⊣ π_{X,*}` on abelian sheaves, with
  the big étale site of `X` written as the localization of the étale site at `X`.
* `AlgebraicGeometry.fppfEtaleWeakSerre`: the class `𝒜'_X`.
* `AlgebraicGeometry.fppfEtaleCohomologyComparisonOfFinite`: Situation 0EZ3 for these data, built
  from the two inputs of property (0EZ7).

## Main results

* `AlgebraicGeometry.fppfEtaleWeakSerre_isWeakSerreClass`,
  `AlgebraicGeometry.fppfEtaleFinite_baseChange`,
  `AlgebraicGeometry.fppfEtaleWeakSerre_overMapPullback`,
  `AlgebraicGeometry.fppfEtaleWeakSerre_isSheaf_fppf` and
  `AlgebraicGeometry.fppfCovering_refinement_etale_finite`: the weak Serre condition and the
  properties (0EZ4), (0EZ5), (0EZ6) and (0EZ8).

## Implementation notes

Situation 0EZ3 localizes the coarse topology, so `𝒜'_X` lives on sheaves for
`(associatedBigEtaleSite B).topology.over X`, while the small-to-big projection of the étale
development lives on `BigEtaleOver.topology`. The two topologies are equal
(`AlgebraicGeometry.bigEtaleOver_topology_eq`) but not definitionally so, and `π_X⁻¹` is the
sheaf pullback along the small étale inclusion followed by `CategoryTheory.sheafEquivOfTopologyEq`,
which does not change underlying presheaves.

## References

* [Stacks Project, Tag 0F0H](https://stacks.math.columbia.edu/tag/0F0H)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The étale precoverage of all schemes is stable under composition: a composite of étale
morphisms is étale, and jointly surjective families compose to jointly surjective families. -/
instance etalePrecoverage_isStableUnderComposition :
    Scheme.etalePrecoverage.{u}.IsStableUnderComposition := by
  refine ⟨fun {ι S X} f hf {σ Y} g hg ↦ ?_⟩
  have hf' := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp hf
  have hg' i := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp (hg i)
  refine (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mpr ⟨fun z ↦ ?_, fun ⟨i, j⟩ ↦ ?_⟩
  · obtain ⟨i, y, rfl⟩ := hf'.1 z
    obtain ⟨j, x, rfl⟩ := (hg' i).1 y
    exact ⟨⟨i, j⟩, x, rfl⟩
  · have := (hg' i).2 j
    have := hf'.2 i
    infer_instance

/-- The precoverage of a big étale site is stable under composition. -/
instance bigEtalePrecoverage_isStableUnderComposition (E : BigEtaleSite.{u}) :
    E.precoverage.IsStableUnderComposition := by
  rw [bigEtalePrecoverage_eq_comap]
  infer_instance

variable (B : BigFppfSite.{u})

/-- Every covering family of the étale site associated with a big fppf site is a covering family
of the fppf site. -/
theorem associatedEtalePrecoverage_le_fppfPrecoverage :
    (associatedBigEtaleSite B).precoverage ≤ B.precoverage := by
  rintro X R ⟨E, hR, hE⟩
  exact ⟨E, hR, ((etaleBounded_eq_fppfEtaleBounded B ⟨X, E⟩).mpr hE).1⟩

/-- The finite morphisms of the common underlying category of a big fppf site and its associated
étale site. -/
abbrev fppfEtaleFinite : MorphismProperty B.Schemes :=
  fun _ _ f ↦ IsFinite (B.inclusion.map f)

variable (X : B.Schemes)

/-- The inverse image `π_X⁻¹` of abelian sheaves from the small étale site of `X` to the big
étale site of `X`, the latter written as the localization at `X` of the étale site associated
with `B`. -/
abbrev fppfEtaleProjectionPullback :
    Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1} :=
  (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) ⋙
    (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).functor

/-- The direct image `π_{X,*}` of abelian sheaves, restriction to the small étale site. -/
abbrev fppfEtaleProjectionRestriction :
    Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} :=
  (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).inverse ⋙
    (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)

/-- The adjunction `π_X⁻¹ ⊣ π_{X,*}` on abelian sheaves. -/
def fppfEtaleProjectionAdjunction :
    fppfEtaleProjectionPullback B X ⊣ fppfEtaleProjectionRestriction B X :=
  ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).comp
    (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).toAdjunction

/-- `π_X⁻¹` preserves finite limits. -/
instance : PreservesFiniteLimits (fppfEtaleProjectionPullback B X) := by
  have := ((exactFunctor_iff _).mp
    (projectionPullback_exact.{u, 0} (associatedBigEtaleSite B) X.1 X.2)).1
  exact comp_preservesFiniteLimits _ _

/-- `π_X⁻¹` preserves finite colimits. -/
instance : PreservesFiniteColimits (fppfEtaleProjectionPullback B X) := by
  have := ((exactFunctor_iff _).mp
    (projectionPullback_exact.{u, 0} (associatedBigEtaleSite B) X.1 X.2)).2
  exact comp_preservesFiniteColimits _ _

/-- `π_{X,*}` preserves finite limits. -/
instance : PreservesFiniteLimits (fppfEtaleProjectionRestriction B X) := by
  have := ((exactFunctor_iff _).mp
    (projectionRestriction_exact.{u, 0} (associatedBigEtaleSite B) X.1 X.2)).1
  exact comp_preservesFiniteLimits _ _

/-- `π_{X,*}` preserves finite colimits. -/
instance : PreservesFiniteColimits (fppfEtaleProjectionRestriction B X) := by
  have := ((exactFunctor_iff _).mp
    (projectionRestriction_exact.{u, 0} (associatedBigEtaleSite B) X.1 X.2)).2
  exact comp_preservesFiniteColimits _ _

/-- The first factor of `π_X⁻¹` is fully faithful, the small étale inclusion being fully
faithful, continuous and cocontinuous. -/
private theorem full_and_faithful_projectionSheafPullback :
    ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).Full ∧
    ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).Faithful := by
  have := smallEtaleInclusion_isCocontinuous (associatedBigEtaleSite B) X.1 X.2
  have : ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).IsRightAdjoint :=
    ((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} _ _).isRightAdjoint
  exact Functor.full_and_faithful_sheafPullback _ _ _ _

/-- `π_X⁻¹` is full. -/
instance fppfEtaleProjectionPullback_full : (fppfEtaleProjectionPullback B X).Full := by
  have := (full_and_faithful_projectionSheafPullback B X).1
  infer_instance

/-- `π_X⁻¹` is faithful. -/
instance fppfEtaleProjectionPullback_faithful : (fppfEtaleProjectionPullback B X).Faithful := by
  have := (full_and_faithful_projectionSheafPullback B X).2
  infer_instance

/-- `π_X⁻¹` is additive. -/
instance fppfEtaleProjectionPullback_additive : (fppfEtaleProjectionPullback B X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `π_{X,*}` is additive. -/
instance fppfEtaleProjectionRestriction_additive :
    (fppfEtaleProjectionRestriction B X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The class `𝒜'_X` of Stacks 0F0H: abelian sheaves on the big étale site of `X` of the form
`π_X⁻¹F` for an abelian sheaf `F` on the small étale site of `X`. -/
abbrev fppfEtaleWeakSerre :
    ObjectProperty (Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1}) :=
  (fppfEtaleProjectionPullback B X).essImage

/-- **The weak Serre condition of Stacks 0F0H.** `𝒜'_X` is a weak Serre subcategory of the
abelian sheaves on the big étale site of `X`: `π_X⁻¹` is exact and fully faithful, and its right
adjoint `π_{X,*}` is exact (Stacks 0DDI). -/
theorem fppfEtaleWeakSerre_isWeakSerreClass : (fppfEtaleWeakSerre B X).IsWeakSerreClass := by
  have h := ObjectProperty.isWeakSerreClass_map_top (fppfEtaleProjectionAdjunction B X)
  have e : (⊤ : ObjectProperty _).map (fppfEtaleProjectionPullback B X) =
      fppfEtaleWeakSerre B X := by
    ext G
    exact ⟨fun ⟨A, _, h⟩ ↦ ⟨A, h⟩, fun ⟨A, h⟩ ↦ ⟨A, trivial, h⟩⟩
  rwa [e] at h

/-- **Property (0EZ4) of Situation 0EZ3 in Stacks 0F0H.** Finite morphisms have all base changes
in the common underlying category, and these are again finite (Stacks 01WL). -/
theorem fppfEtaleFinite_baseChange ⦃X Y Y' : B.Schemes⦄ (f : X ⟶ Y) (hf : fppfEtaleFinite B f)
    (g : Y' ⟶ Y) : ∃ (Z : B.Schemes) (q : Z ⟶ X) (p : Z ⟶ Y'),
      IsPullback q p f g ∧ fppfEtaleFinite B p := by
  have : IsFinite (B.inclusion.map f) := hf
  have : HasPullbacks B.Schemes := hasPullbacks_bigEtaleSite (associatedBigEtaleSite B)
  have : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigEtaleSiteInclusion (associatedBigEtaleSite B)
  exact ⟨pullback f g, pullback.fst f g, pullback.snd f g, IsPullback.of_hasPullback f g,
    MorphismProperty.of_isPullback (P := @IsFinite)
      ((IsPullback.of_hasPullback f g).map B.inclusion) hf⟩

variable {B} in
/-- Relocalization of `π_Y⁻¹` along a morphism `f : X ⟶ Y` is `π_X⁻¹` of the small étale inverse
image along `f`: the two composite left adjoints have the same right adjoint, restriction along
`SmallEtale.inclusion ⋙ Over.pullback f`, which is small étale base change followed by the
inclusion (Stacks 021I). -/
def fppfEtaleProjectionPullbackOverMapPullbackIso {X Y : B.Schemes} (f : X ⟶ Y) :
    fppfEtaleProjectionPullback B Y ⋙
        (associatedBigEtaleSite B).topology.overMapPullback AddCommGrpCat.{u + 1} f ≅
      (smallEtaleBaseChange (associatedBigEtaleSite B) f).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
          (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) ⋙
        fppfEtaleProjectionPullback B X :=
  ((fppfEtaleProjectionAdjunction B Y).comp
      ((Over.mapPullbackAdj f).sheafPushforwardAdjunction AddCommGrpCat.{u + 1})).leftAdjointUniq
    (((smallEtaleBaseChange (associatedBigEtaleSite B) f).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} _ _).comp (fppfEtaleProjectionAdjunction B X))

variable {B} in
/-- **Property (0EZ5) of Situation 0EZ3 in Stacks 0F0H.** Relocalization along any morphism
preserves `𝒜'`: `f⁻¹π_Y⁻¹F = π_X⁻¹f_small⁻¹F` (Stacks 021I). -/
theorem fppfEtaleWeakSerre_overMapPullback {X Y : B.Schemes} (f : X ⟶ Y)
    (F : Sheaf ((associatedBigEtaleSite B).topology.over Y) AddCommGrpCat.{u + 1})
    (hF : fppfEtaleWeakSerre B Y F) :
    fppfEtaleWeakSerre B X
      (((associatedBigEtaleSite B).topology.overMapPullback AddCommGrpCat.{u + 1} f).obj F) := by
  obtain ⟨A, ⟨e⟩⟩ := hF
  exact ⟨_, ⟨((fppfEtaleProjectionPullbackOverMapPullbackIso f).app A).symm ≪≫
    ((associatedBigEtaleSite B).topology.overMapPullback AddCommGrpCat.{u + 1} f).mapIso e⟩⟩

/-- The forgetful functor of abelian groups preserves left Kan extensions along the opposite of
the small étale inclusion: that inclusion preserves finite limits, so the categories indexing
the pointwise Kan extensions are filtered, and forgetting commutes with filtered colimits. -/
instance forget_preservesLeftKanExtensions_smallEtaleInclusion :
    (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).op := by
  have : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesFiniteLimits (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  have : RepresentablyFlat (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2) :=
    flat_of_preservesFiniteLimits _
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  intro P
  have : (forget AddCommGrpCat.{u + 1}).PreservesPointwiseLeftKanExtension P
      (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).op := fun Z ↦ by
    have : IsFiltered (CostructuredArrow
      (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).op Z) := inferInstance
    infer_instance
  infer_instance

/-- The underlying presheaf of sets of `π_X⁻¹F`, for an abelian sheaf `F`, is the inverse image of
the underlying sheaf of sets of `F` along the projection of topoi. -/
def fppfEtaleProjectionPullbackForgetIso
    (A : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    ((fppfEtaleProjectionPullback B X).obj A).obj ⋙ forget AddCommGrpCat.{u + 1} ≅
      ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) X.1 X.2).inverseImage.obj
        ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).obj A)).obj :=
  let i := SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2
  let J := SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2
  let K := BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2
  Functor.isoWhiskerRight ((sheafToPresheaf K _).mapIso
      ((Functor.sheafPullbackConstruction.sheafPullbackIso i AddCommGrpCat.{u + 1} J K).app A))
      (forget AddCommGrpCat.{u + 1}) ≪≫
    (sheafifyComposeIso K (forget AddCommGrpCat.{u + 1}) (i.op.leftKanExtension A.obj)).symm ≪≫
    (sheafToPresheaf K _).mapIso ((presheafToSheaf K _).mapIso
      ((forget AddCommGrpCat.{u + 1}).leftKanExtensionCompIsoOfPreserves A.obj i.op)) ≪≫
    (sheafToPresheaf K _).mapIso
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous i (Type (u + 1)) J
        K).leftAdjointUniq
          (bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) X.1 X.2).adj).app
          ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj A))

variable {B} in
/-- **Property (0EZ6) of Situation 0EZ3 in Stacks 0F0H.** Every object of `𝒜'_X` satisfies the
sheaf condition for fppf coverings (Stacks 0DDL). -/
theorem fppfEtaleWeakSerre_isSheaf_fppf {X : B.Schemes}
    (F : Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1})
    (hF : fppfEtaleWeakSerre B X F) : Presheaf.IsSheaf (B.topology.over X) F.obj := by
  obtain ⟨A, ⟨e⟩⟩ := hF
  rw [Presheaf.isSheaf_iff_isSheaf_forget (B.topology.over X) F.obj (forget AddCommGrpCat.{u + 1})]
  refine (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso e.symm)
    (forget AddCommGrpCat.{u + 1}) ≪≫ fppfEtaleProjectionPullbackForgetIso B X A)).2 ?_
  exact smallEtaleInverseImage_isSheaf_fppf B X _

/-- **Property (0EZ8) of Situation 0EZ3 in Stacks 0F0H.** Every fppf covering is refined by first
taking an étale covering, then a single surjective finite locally free morphism over each member,
which is an fppf covering, and finally the trivial étale covering of its source (Stacks 0DET). -/
theorem fppfCovering_refinement_etale_finite (U : B.Schemes) (R : Presieve U)
    (hR : R ∈ B.precoverage U) :
    ∃ S : Presieve U, S ∈ (associatedBigEtaleSite B).precoverage U ∧
      ∀ ⦃V : B.Schemes⦄ (v : V ⟶ U), S v →
        ∃ (W : B.Schemes) (f : W ⟶ V), fppfEtaleFinite B f ∧
          Presieve.singleton f ∈ B.precoverage V ∧
          ∃ T : Presieve W, T ∈ (associatedBigEtaleSite B).precoverage W ∧
            T.FactorsThruAlong R (f ≫ v) := by
  obtain ⟨cover, hR, hcover⟩ := hR
  let schemeCover : U.1.Cover.{u + 1} Scheme.fppfPrecoverage :=
    { __ := cover.map B.inclusion
      mem₀ := by
        rw [PreZeroHypercover.presieve₀_map]
        exact hcover.1 }
  obtain ⟨etaleCover, fineCover, ⟨refinement⟩, reindex, finiteArrow, hcomp, hsurj, hfree⟩ :=
    Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates schemeCover
  let indices := Σ index : fineCover.I₀, (etaleCover.X (reindex index)).affineCover.I₀
  let etaleSource (index : indices) := (etaleCover.X (reindex index.1)).affineCover.X index.2
  let etaleArrow (index : indices) : etaleSource index ⟶ U.1 :=
    (etaleCover.X (reindex index.1)).affineCover.f index.2 ≫ etaleCover.f (reindex index.1)
  have hetale (index : indices) : Etale (etaleArrow index) := by
    have := etaleCover.map_prop (reindex index.1)
    dsimp [etaleArrow]
    infer_instance
  have hsmall (index : indices) : (etaleSource index).size < B.cutoff := by
    have := hetale index
    exact (Scheme.size_le_of_locallyOfFiniteType (etaleArrow index)).trans_lt U.2
  let boundedSource (index : indices) : B.Schemes := ⟨etaleSource index, hsmall index⟩
  choose boundedArrow hboundedArrow using fun index : indices ↦
    B.inclusion.map_surjective (X := boundedSource index) (Y := U) (etaleArrow index)
  refine ⟨Presieve.ofArrows boundedSource boundedArrow, ?_, ?_⟩
  · rw [bigEtalePrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    simp only [hboundedArrow]
    change Presieve.ofArrows etaleSource etaleArrow ∈ Scheme.precoverage @Etale U.1
    rw [Scheme.ofArrows_mem_precoverage_iff (@Etale)]
    refine ⟨fun point ↦ ?_, hetale⟩
    obtain ⟨index, sourcePoint, hpoint⟩ :=
      ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).1 etaleCover.mem₀).1 point
    obtain ⟨index, rfl⟩ := reindex.surjective index
    obtain ⟨affineIndex, affinePoint, haffine⟩ :=
      (etaleCover.X (reindex index)).affineCover.exists_eq sourcePoint
    refine ⟨⟨index, affineIndex⟩, affinePoint, ?_⟩
    simpa [etaleSource, etaleArrow, Scheme.Hom.comp_apply, haffine] using hpoint
  · rintro V arrow ⟨index⟩
    let affineArrow := (etaleCover.X (reindex index.1)).affineCover.f index.2
    obtain ⟨_, _, _⟩ :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        (finiteArrow index.1)).mp (hfree index.1)
    have := hsurj index.1
    let source := pullback (finiteArrow index.1) affineArrow
    let finiteMap : source ⟶ etaleSource index := pullback.snd (finiteArrow index.1) affineArrow
    have hsource : source.size < B.cutoff :=
      Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact finiteMap (hsmall index)
    let W : B.Schemes := ⟨source, hsource⟩
    obtain ⟨boundedFinite, hboundedFinite⟩ :=
      B.inclusion.map_surjective (X := W) (Y := boundedSource index) finiteMap
    refine ⟨W, boundedFinite, ?_, ?_, Presieve.singleton (𝟙 W), ?_, ?_⟩
    · change IsFinite (B.inclusion.map boundedFinite)
      rw [hboundedFinite]
      infer_instance
    · rw [bigFppfPrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton,
        hboundedFinite]
      exact finiteMap.singleton_mem_fppfPrecoverage
    · rw [bigEtalePrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton,
        show (associatedBigEtaleSite B).inclusion = B.inclusion from rfl, B.inclusion.map_id]
      change Presieve.singleton (𝟙 source) ∈ Scheme.precoverage @Etale source
      rw [Scheme.singleton_mem_precoverage_iff (@Etale)]
      exact ⟨Function.surjective_id, inferInstance⟩
    · rintro Z identity ⟨⟩
      let target := cover.X (refinement.s₀ index.1)
      obtain ⟨factor, hfactor⟩ := B.inclusion.map_surjective (X := W) (Y := target)
        (pullback.fst (finiteArrow index.1) affineArrow ≫ refinement.h₀ index.1)
      refine ⟨target, factor, cover.f (refinement.s₀ index.1), ?_, ?_⟩
      · rw [hR]
        exact Presieve.ofArrows.mk (refinement.s₀ index.1)
      · apply B.inclusion.map_injective
        simp only [Functor.map_comp, hfactor, hboundedFinite, hboundedArrow, Category.id_comp]
        change (pullback.fst (finiteArrow index.1) affineArrow ≫
          refinement.h₀ index.1) ≫ schemeCover.f (refinement.s₀ index.1) =
            finiteMap ≫ etaleArrow index
        rw [Category.assoc, refinement.w₀, ← hcomp, ← Category.assoc, pullback.condition]
        exact Category.assoc _ _ _

variable {B} in
/-- **Reduction of property (0EZ7) of Situation 0EZ3 to the degree-zero comparison and exactness.**
Let `f : X ⟶ Y` be a morphism whose relocalization direct image `f_*` on abelian sheaves of the
big étale sites is exact and carries every `π_X⁻¹F` into `𝒜'_Y`. Then every higher direct image
`R^i f_*` carries `𝒜'_X` into `𝒜'_Y`: for `i = 0` it is `f_*`, and for `i > 0` it vanishes. -/
theorem fppfEtaleWeakSerre_rightDerived_of_exact {X Y : B.Schemes} (f : X ⟶ Y)
    [PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y))]
    (hbc : ∀ A, fppfEtaleWeakSerre B Y
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).obj
          ((fppfEtaleProjectionPullback B X).obj A)))
    (F : Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1})
    (hF : fppfEtaleWeakSerre B X F) (i : ℕ) :
    fppfEtaleWeakSerre B Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).rightDerived i).obj F) := by
  have := fppfEtaleWeakSerre_isWeakSerreClass B Y
  have := ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    ((associatedBigEtaleSite B).topology.over X)
    ((associatedBigEtaleSite B).topology.over Y)).isRightAdjoint
  obtain ⟨A, ⟨e⟩⟩ := hF
  rcases i with _ | n
  · exact (fppfEtaleWeakSerre B Y).prop_of_iso
      (((Over.map f).sheafPushforwardCocontinuous _ _ _).mapIso e ≪≫
        (Functor.rightDerivedZeroIsoSelf _).symm.app F) (hbc A)
  · exact (fppfEtaleWeakSerre B Y).prop_of_isZero
      (Functor.isZero_rightDerived_of_exact _ F (n + 1) n.succ_pos)

/-- Pullback along a morphism of the common underlying category is continuous for the big étale
topologies, the case of the associated étale site of Stacks 021H. -/
instance fppfEtaleOverPullback_isContinuous {X Y : B.Schemes} (f : X ⟶ Y) :
    (Over.pullback f).IsContinuous (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) :=
  bigEtalePullback_isContinuous (associatedBigEtaleSite B) X Y f

variable {B} in
/-- The relocalization direct image `f_*` on the localizations of the étale site is the direct
image along `Over.pullback f` on the big étale sites, read through
`CategoryTheory.sheafEquivOfTopologyEq`: `Over.map f ⊣ Over.pullback f`. -/
def fppfEtaleOverMapPushforwardIso {X Y : B.Schemes} (f : X ⟶ Y) :
    (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y) ≅
      (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).inverse ⋙
        (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
          (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) ⋙
        (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
          AddCommGrpCat.{u + 1}).functor :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso AddCommGrpCat.{u + 1}

variable {B} in
/-- Exactness of the direct image along `f` on the big étale sites gives exactness of the
relocalization direct image `f_*` of Situation 0EZ3. -/
theorem fppfEtale_preservesFiniteColimits_overMap {X Y : B.Schemes} (f : X ⟶ Y)
    [PreservesFiniteColimits ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2))] :
    PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y)) :=
  preservesFiniteColimits_of_natIso (fppfEtaleOverMapPushforwardIso f).symm

variable {B} in
/-- If the direct image along `f` on the big étale sites carries `π_X⁻¹F` into the essential
image of `π_Y⁻¹`, then the relocalization direct image `f_*` of Situation 0EZ3 carries it into
`𝒜'_Y`. -/
theorem fppfEtaleWeakSerre_overMapPushforward_of {X Y : B.Schemes} (f : X ⟶ Y)
    (A : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})
    (h : ((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)).essImage
      (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).obj
          (((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback
            AddCommGrpCat.{u + 1} (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
            (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)).obj A))) :
    fppfEtaleWeakSerre B Y
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).obj
          ((fppfEtaleProjectionPullback B X).obj A)) := by
  obtain ⟨A', ⟨e⟩⟩ := h
  exact ⟨A', ⟨(sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
    AddCommGrpCat.{u + 1}).functor.mapIso e ≪≫
      ((fppfEtaleOverMapPushforwardIso f).app ((fppfEtaleProjectionPullback B X).obj A)).symm⟩⟩

/-- Situation 0EZ3 for the comparison of the fppf and the étale topology on a big fppf site, with
`𝒫` the finite morphisms and `𝒜'_X` the sheaves `π_X⁻¹F`, built from the two facts about the
direct image along a finite morphism that property (0EZ7) needs: its exactness on abelian sheaves
of the big étale sites, and that it carries every `π_X⁻¹F` into `𝒜'_Y`. -/
def fppfEtaleCohomologyComparisonOfFinite
    (hex : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f →
      PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y)))
    (hbc : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f → ∀ A, fppfEtaleWeakSerre B Y
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).obj
          ((fppfEtaleProjectionPullback B X).obj A))) :
    Stacks.ComparingTopologies.CohomologyComparison B.Schemes where
  fineCoverage := B.precoverage
  fine_hasIsos := inferInstance
  fine_stableUnderComposition := inferInstance
  fine_hasPullbacks := inferInstance
  fine_stableUnderBaseChange := inferInstance
  coarseCoverage := (associatedBigEtaleSite B).precoverage
  coarse_hasIsos := inferInstance
  coarse_stableUnderComposition := inferInstance
  coarse_hasPullbacks := inferInstance
  coarse_stableUnderBaseChange := inferInstance
  coarse_le_fine := associatedEtalePrecoverage_le_fppfPrecoverage B
  morphismProperty := fppfEtaleFinite B
  weakSerre := fppfEtaleWeakSerre B
  weakSerreClass := fppfEtaleWeakSerre_isWeakSerreClass B
  morphismProperty_baseChange := fppfEtaleFinite_baseChange B
  weakSerre_relocalizationInverseImage := fun _ _ f ↦ fppfEtaleWeakSerre_overMapPullback f
  weakSerre_isSheaf_fine := fun _ ↦ fppfEtaleWeakSerre_isSheaf_fppf
  weakSerre_rightDerived_relocalizationPushforward := fun _ _ f hf ↦
    have := hex f hf
    fppfEtaleWeakSerre_rightDerived_of_exact f (hbc f hf)
  covering_refinement := fppfCovering_refinement_etale_finite B

end AlgebraicGeometry
