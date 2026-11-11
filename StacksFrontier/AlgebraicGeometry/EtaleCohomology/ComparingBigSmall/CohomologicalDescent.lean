module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.RingTheory.Dualizing.Ext
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomological descent from the big to the small étale site

Let `S` be a scheme in a big étale site. Restriction of abelian sheaves from the big étale
slice over `S` to the small étale site of `S` is the direct image of the projection of topoi,
and extension is its inverse image. Both are exact, and the unit of the adjunction induces an
isomorphism on unbounded derived categories: cohomology computed on the small site agrees with
cohomology computed on the big one.

## Main definitions

* `AlgebraicGeometry.projectionRestriction` and `AlgebraicGeometry.projectionPullback` — the
  direct and inverse image functors of the projection, on abelian sheaves.
* `AlgebraicGeometry.projectionInverseImage` — the inverse image with no adjunction assumed,
  exact by `AlgebraicGeometry.projectionInverseImage_exact`.
* `AlgebraicGeometry.projectionDerivedUnit` — the adjunction unit on unbounded derived
  categories, with target the functor induced by the composite `π_{S,*} ∘ π_S⁻¹`.

## Main results

* `AlgebraicGeometry.projectionPullback_exact` and
  `AlgebraicGeometry.projectionRestriction_exact` — both functors are exact.
* `AlgebraicGeometry.projectionDerivedUnit_isIso` — the derived unit into the functor induced by
  the composite is an isomorphism. Stacks 0DDI itself, with target `Rπ_{S,*} ∘ π_S⁻¹`, is
  `AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso` in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProjectionDerivedUnit`.

## Implementation notes

Exactness of the inverse image is left exactness of the presheaf-level left Kan extension
along the small-site inclusion: the inclusion is representably flat, so each comma category
`CostructuredArrow` is filtered, the Kan extension is a filtered colimit evaluated pointwise,
and filtered colimits of abelian groups commute with finite limits. `lanEvaluationIsoColimit`
is that pointwise description; it repeats Mathlib's `lanEvaluationIsoColim` without the
restriction to small categories, since the étale categories have their objects and their
morphisms in different universes.

Exactness of the direct image uses that the inclusion is also *cocontinuous*, so restriction
is simultaneously a sheaf pullback, which is a left adjoint and hence preserves colimits.

Both functors being exact, the derived functors are their induced functors on unbounded
derived categories, and the derived unit is the localization of the degreewise unit. That is
invertible because the unit itself is: the inclusion is fully faithful and cocontinuous.

## References

* [Stacks Project, Lemma 59.99.4 (Tag 0DDI)](https://stacks.math.columbia.edu/tag/0DDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
attribute [local instance] reflectsLimitsOfShape_of_reflectsIsomorphisms

/-- The forgetful functor on abelian groups preserves filtered colimits of size `u + 1`. -/
local instance : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
    (forget AddCommGrpCat.{max (u + 1) v}) :=
  preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v} _

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on the small étale site of `S` can be sheafified. -/
local instance : HasSheafify (SmallEtale.topology B S hS)
    AddCommGrpCat.{max (u + 1) v} := by infer_instance
/-- Abelian presheaves on the big étale slice over `S` can be sheafified. -/
local instance : HasSheafify (BigEtaleOver.topology B S hS)
    AddCommGrpCat.{max (u + 1) v} := by infer_instance


/-- Abelian sheaves on the small étale site of `S`. -/
abbrev smallSheaves :=
  Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}

/-- Abelian sheaves on the big étale slice over `S`. -/
abbrev bigSheaves :=
  Sheaf (BigEtaleOver.topology B S hS) AddCommGrpCat.{max (u + 1) v}

/-- Abelian sheaves on the small étale site of `S` form an abelian category. -/
local instance : Abelian (smallSheaves.{u, v} B S hS) :=
  CategoryTheory.sheafIsAbelian
/-- Abelian sheaves on the big étale slice over `S` form an abelian category. -/
local instance : Abelian (bigSheaves.{u, v} B S hS) :=
  CategoryTheory.sheafIsAbelian

/-- The small-site inclusion is representably flat: the small étale category has all finite
limits and the inclusion preserves them. -/
private theorem smallEtaleInclusion_representablyFlat :
    RepresentablyFlat (SmallEtale.inclusion B S hS) := by
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (SmallEtale.inclusion B S hS) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesFiniteLimits (SmallEtale.inclusion B S hS) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact flat_of_preservesFiniteLimits _

/-- The small-site inclusion is cocontinuous for the small and big étale topologies. -/
private theorem smallEtaleInclusion_isCocontinuous :
    (SmallEtale.inclusion B S hS).IsCocontinuous
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) := by
  have ev : smallEtaleToBigEtaleFunctor B (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS)) =
      SmallEtale.inclusion B S hS := by
    dsimp [smallEtaleToBigEtaleFunctor]
    rw [Over.mapId_eq]
    rfl
  exact ev ▸ smallEtaleToBigEtaleFunctor_isCocontinuous B
    (B.obj S hS) (B.obj S hS) (𝟙 (B.obj S hS))

/-- Restriction of abelian sheaves from the big étale slice over `S` to the small étale site
of `S`, the direct image of the projection of topoi. -/
abbrev projectionRestriction : bigSheaves.{u, v} B S hS ⥤
    smallSheaves.{u, v} B S hS :=
  (SmallEtale.inclusion B S hS).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS)
    (BigEtaleOver.topology B S hS)

/-- Extension of abelian sheaves from the small étale site of `S` to the big étale slice
over `S`, the inverse image of the projection of topoi. -/
abbrev projectionPullback
    [(projectionRestriction.{u, v} B S hS).IsRightAdjoint] :
    smallSheaves.{u, v} B S hS ⥤ bigSheaves.{u, v} B S hS :=
  (SmallEtale.inclusion B S hS).sheafPullback
    AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS)
    (BigEtaleOver.topology B S hS)

/-- `AlgebraicGeometry.projectionRestriction` is a right adjoint. -/
local instance : (projectionRestriction.{u, v} B S hS).IsRightAdjoint :=
  ((SmallEtale.inclusion B S hS).sheafAdjunctionContinuous
    AddCommGrpCat.{max (u + 1) v} _ _).isRightAdjoint

/-- Extension of abelian sheaves from the small étale site of `S` to the big étale slice over
`S`, the inverse image of the projection of topoi, with no adjunction assumed: the inclusion of
the small étale site is continuous, so `CategoryTheory.Functor.sheafAdjunctionContinuous`
supplies the right adjoint.  It is `AlgebraicGeometry.projectionPullback` at that adjunction. -/
@[sga "4 VII 4.0" "special case"]
abbrev projectionInverseImage : smallSheaves.{u, v} B S hS ⥤ bigSheaves.{u, v} B S hS :=
  projectionPullback.{u, v} B S hS

/-- Extension from the small to the big étale site is exact. An ingredient of Stacks 0DDI, which
is `AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso`. -/
theorem projectionPullback_exact :
    exactFunctor _ _ (projectionPullback.{u, v} B S hS) := by
  rw [exactFunctor_iff]
  constructor
  · let : RepresentablyFlat (SmallEtale.inclusion B S hS) :=
      smallEtaleInclusion_representablyFlat B S hS
    let F := (SmallEtale.inclusion B S hS).op
    have hlan : PreservesFiniteLimits (F.lan :
        ((SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤
          (BigEtaleOver B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
      intro I _ _
      apply preservesLimitsOfShape_of_evaluation _ I
      intro Y
      let : IsFiltered (CostructuredArrow F Y) :=
        IsFiltered.of_equivalence
          (structuredArrowOpEquivalence (SmallEtale.inclusion B S hS) Y.unop)
      let : PreservesFilteredColimitsOfSize.{u, u + 1}
          (forget AddCommGrpCat.{max (u + 1) v}) :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1}
          (forget AddCommGrpCat.{max (u + 1) v})
      let : PreservesColimitsOfShape (CostructuredArrow F Y)
          (forget AddCommGrpCat.{max (u + 1) v}) :=
        PreservesFilteredColimitsOfSize.preserves_filtered_colimits
          (CostructuredArrow F Y)
      let : PreservesLimitsOfShape I (forget AddCommGrpCat.{max (u + 1) v}) := by
        infer_instance
      let : ReflectsLimitsOfShape I (forget AddCommGrpCat.{max (u + 1) v}) := by
        infer_instance
      let : PreservesLimitsOfShape I
          (colim : (CostructuredArrow F Y ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤ _) :=
        inferInstance
      exact preservesLimitsOfShape_of_natIso
        (lanEvaluationIsoColimit AddCommGrpCat.{max (u + 1) v} F Y).symm
    let : PreservesFiniteLimits (F.lan :
        ((SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤
          (BigEtaleOver B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) := hlan
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits
      (SmallEtale.inclusion B S hS) AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
  · let := (Functor.sheafAdjunctionContinuous
        (SmallEtale.inclusion B S hS) AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)).isLeftAdjoint
    infer_instance

/-- The inverse image with no adjunction assumed, `AlgebraicGeometry.projectionInverseImage`, is
exact. An ingredient of Stacks 0DDI, which is
`AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso`. -/
theorem projectionInverseImage_exact :
    exactFunctor _ _ (projectionInverseImage.{u, v} B S hS) :=
  projectionPullback_exact.{u, v} B S hS

/-- Restriction from the big to the small étale site is exact. An ingredient of Stacks 0DDI,
which is `AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso`. -/
theorem projectionRestriction_exact :
    exactFunctor _ _ (projectionRestriction.{u, v} B S hS) := by
  rw [exactFunctor_iff]
  have := smallEtaleInclusion_isCocontinuous B S hS
  let : ∀ F : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (SmallEtale.inclusion B S hS).op.HasPointwiseRightKanExtension F := by
    intro F
    infer_instance
  let e := Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (SmallEtale.inclusion B S hS) AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
  constructor
  · exact preservesFiniteLimits_of_natIso e
  · exact preservesFiniteColimits_of_natIso e

/-- `AlgebraicGeometry.projectionPullback` preserves finite limits. -/
local instance : PreservesFiniteLimits (projectionPullback.{u, v} B S hS) :=
  (projectionPullback_exact.{u, v} B S hS).1
/-- `AlgebraicGeometry.projectionPullback` preserves finite colimits. -/
local instance : PreservesFiniteColimits (projectionPullback.{u, v} B S hS) :=
  (projectionPullback_exact.{u, v} B S hS).2
/-- `AlgebraicGeometry.projectionRestriction` preserves finite limits. -/
local instance : PreservesFiniteLimits (projectionRestriction.{u, v} B S hS) :=
  (projectionRestriction_exact.{u, v} B S hS).1
/-- `AlgebraicGeometry.projectionRestriction` preserves finite colimits. -/
local instance : PreservesFiniteColimits (projectionRestriction.{u, v} B S hS) :=
  (projectionRestriction_exact.{u, v} B S hS).2

/-- `AlgebraicGeometry.projectionPullback` is additive. -/
local instance : (projectionPullback.{u, v} B S hS).Additive :=
  (projectionPullback.{u, v} B S hS).additive_of_preservesBinaryBiproducts
/-- `AlgebraicGeometry.projectionRestriction` is additive. -/
local instance : (projectionRestriction.{u, v} B S hS).Additive :=
  (projectionRestriction.{u, v} B S hS).additive_of_preservesBinaryBiproducts

/-- The unit of the projection adjunction, on unbounded derived categories. -/
public def projectionDerivedUnit :
    𝟭 (DerivedCategory (smallSheaves.{u, v} B S hS)) ⟶
      ((projectionPullback.{u, v} B S hS ⋙
        projectionRestriction.{u, v} B S hS).mapDerivedCategory) :=
  Dualizing.PowerTorsionBaseChange.derivedUnit
    (projectionPullback.{u, v} B S hS ⋙ projectionRestriction.{u, v} B S hS)
    ((SmallEtale.inclusion B S hS).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v} _ _).unit

/-- The unit `projectionDerivedUnit`, with target the functor induced by the composite
`π_{S,*} ∘ π_S⁻¹`, is an isomorphism. This is the main ingredient of Stacks 0DDI, which is
`AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso`, stated there with target
`Rπ_{S,*} ∘ π_S⁻¹`. -/
theorem projectionDerivedUnit_isIso :
    IsIso (projectionDerivedUnit.{u, v} B S hS) := by
  let i := SmallEtale.inclusion B S hS
  let J := SmallEtale.topology B S hS
  let K := BigEtaleOver.topology B S hS
  let A := AddCommGrpCat.{max (u + 1) v}
  have : i.IsCocontinuous J K := smallEtaleInclusion_isCocontinuous B S hS
  let : i.IsContinuous J K :=
    (smallEtaleInclusion_isMorphismOfSites B S hS).toIsContinuous
  let : ∀ F : (SmallEtale B S hS)ᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F := by
    intro F
    infer_instance
  let adj := i.sheafAdjunctionContinuous A J K
  have hη : IsIso adj.unit :=
    Functor.isIso_unit_of_sheafPushforwardContinuous i A J K adj
  let F := projectionPullback.{u, v} B S hS ⋙ projectionRestriction.{u, v} B S hS
  let η := ((SmallEtale.inclusion B S hS).sheafAdjunctionContinuous A J K).unit
  have hη' : IsIso η := by simpa [η, adj] using hη
  let cu := Dualizing.PowerTorsionBaseChange.complexUnit F η
  have hComplex : IsIso cu := by
    have hX (X : CochainComplex (smallSheaves.{u, v} B S hS) ℤ) : IsIso (cu.app X) := by
      have hcomp : ∀ n : ℤ, IsIso ((cu.app X).f n) := by
        intro n
        dsimp [cu, Dualizing.PowerTorsionBaseChange.complexUnit]
        exact (NatTrans.isIso_iff_isIso_app η).mp hη' (X.X n)
      have : ∀ n : ℤ, IsIso ((cu.app X).f n) := hcomp
      exact HomologicalComplex.Hom.isIso_of_components (cu.app X)
    have : ∀ X, IsIso (cu.app X) := hX
    exact NatIso.isIso_of_isIso_app cu
  let eC : 𝟭 (CochainComplex (smallSheaves.{u, v} B S hS) ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) := asIso cu
  let eQ : DerivedCategory.Q (C := smallSheaves.{u, v} B S hS) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q (C := smallSheaves.{u, v} B S hS) :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight eC
      (DerivedCategory.Q (C := smallSheaves.{u, v} B S hS))
  let e := Localization.liftNatIso
    (DerivedCategory.Q (C := smallSheaves.{u, v} B S hS))
    (HomologicalComplex.quasiIso (smallSheaves.{u, v} B S hS) (.up ℤ))
    (DerivedCategory.Q (C := smallSheaves.{u, v} B S hS))
    (F.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q (C := smallSheaves.{u, v} B S hS))
    (𝟭 (DerivedCategory (smallSheaves.{u, v} B S hS))) F.mapDerivedCategory eQ
  change IsIso e.hom
  infer_instance


/-- The unit of the projection adjunction on unbounded derived categories, stated through the
inverse image with no adjunction assumed, `AlgebraicGeometry.projectionInverseImage`: the
adjunction is the one `CategoryTheory.Functor.sheafAdjunctionContinuous` supplies for the
continuous small-site inclusion. It is `AlgebraicGeometry.projectionDerivedUnit`. -/
public def projectionInverseImageDerivedUnit :
    𝟭 (DerivedCategory (smallSheaves.{u, v} B S hS)) ⟶
      ((projectionInverseImage.{u, v} B S hS ⋙
        projectionRestriction.{u, v} B S hS).mapDerivedCategory) :=
  projectionDerivedUnit.{u, v} B S hS

/-- For every `K` in `D(S_étale)` the map `K ⟶ Rπ_{S,*} π_S⁻¹ K` is an isomorphism, with the
inverse image `projectionInverseImage` taken with no adjunction assumed. Both functors are exact
(`projectionInverseImage_exact`, `projectionRestriction_exact`), so their derived functors are the
induced functors on derived categories. The target here is the functor induced by the composite
`π_{S,*} ∘ π_S⁻¹`; Stacks 0DDI itself, with target `Rπ_{S,*} ∘ π_S⁻¹`, is
`AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso`. -/
theorem projectionInverseImageDerivedUnit_isIso :
    IsIso (projectionInverseImageDerivedUnit.{u, v} B S hS) :=
  projectionDerivedUnit_isIso.{u, v} B S hS

end AlgebraicGeometry
