module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectHomAffineLeaf

/-!
# The affine case of Stacks 09RI for perfect objects, on the restricted situation

In Situation 09RH read as Situation 0DKU
(`AlgebraicGeometry.Space.DescentSituation.toRelative`), let `g : U₀ ⟶ X₀` be a flat morphism of
finite presentation from an affine algebraic space, and restrict the situation along `g`
(`AlgebraicGeometry.Space.RelativeDescentSituation.restrict`), so that its stages are the
`X_i ×_{X₀} U₀` and its limit is `X ×_{X₀} U₀`.  This file proves that for perfect objects `E`
and `K` of `D(𝒪_{U₀})`,

`Hom(Lk^*E, Lk^*K) = colim_i Hom(Lk_i^*E, Lk_i^*K)`,

the derived pullbacks being taken with their canonical pseudofunctoriality.  The restricted stages
are identified with the affine models of the base changes of Situation 09RH along an affine point
`h_T ≅ U₀`, and the statement is transported from
`AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_of_isPerfect` along that identification.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isColim_restrict_toRelative_of_isPerfect`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.toRelative.X₀)
  (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)
  {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  (e : U₀ ≅ yoneda.obj T) (u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hu : e.inv ≫ g = u) (hconv : SiteContainsBaseChangeLimits B S hS D.system)

/-- The projection of a restricted stage to `U₀`. -/
def restrictStageToX₀ (i : D.Stages) :
    (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ i.1 i.2 ⟶ U₀ :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).toX₀ i.1 i.2

/-- The projection of a restricted stage to the stage of Situation 09RH. -/
def restrictStageToYᵢ (i : D.Stages) :
    (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ i.1 i.2 ⟶ D.system.obj (op i.1) :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).toYᵢ i.1 i.2

/-- The transition morphism of the restricted stages. -/
def restrictStageMap {i j : D.Stages} (h : i ≤ j) :
    (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ j.1 j.2 ⟶
      (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ i.1 i.2 :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).fᵢⱼ i.1 j.1 i.2 j.2 h

/-- The projection of the restricted limit to `U₀`. -/
def restrictLimitToX₀ : (D.toRelative.restrict hU₀ g hgflat hgfp).X ⟶ U₀ :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).toInitial

/-- The projection of the restricted limit to the limit of Situation 09RH. -/
def restrictLimitToY : (D.toRelative.restrict hU₀ g hgflat hgfp).X ⟶ D.limitCone.pt :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).toLimit

/-- The projection of the restricted limit to a restricted stage. -/
def restrictLimitProj (j : D.Stages) :
    (D.toRelative.restrict hU₀ g hgflat hgfp).X ⟶
      (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ j.1 j.2 :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).fᵢ j.1 j.2

/-- The transition morphisms of the restricted stages are compatible with the projections to the
stages of Situation 09RH. -/
theorem restrictStageMap_toYᵢ {i j : D.Stages} (h : i ≤ j) :
    restrictStageMap hU₀ g hgflat hgfp h ≫ restrictStageToYᵢ hU₀ g hgflat hgfp i =
      restrictStageToYᵢ hU₀ g hgflat hgfp j ≫ D.system.map (homOfLE h).op :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).fᵢⱼ_toYᵢ i.1 j.1 i.2 j.2 h

/-- The transition morphisms of the restricted stages commute with the projections to `U₀`. -/
theorem restrictStageMap_toX₀ {i j : D.Stages} (h : i ≤ j) :
    restrictStageMap hU₀ g hgflat hgfp h ≫ restrictStageToX₀ hU₀ g hgflat hgfp i =
      restrictStageToX₀ hU₀ g hgflat hgfp j :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).fᵢⱼ_toX₀ i.1 j.1 i.2 j.2 h

/-- The projections of the restricted limit to the restricted stages are compatible with the
limit projections of Situation 09RH. -/
theorem restrictLimitProj_toYᵢ (j : D.Stages) :
    restrictLimitProj hU₀ g hgflat hgfp j ≫ restrictStageToYᵢ hU₀ g hgflat hgfp j =
      restrictLimitToY hU₀ g hgflat hgfp ≫ D.limitCone.π.app (op j.1) :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).fᵢ_toYᵢ j.1 j.2

/-- The projections of the restricted limit to the restricted stages commute with the projections
to `U₀`. -/
theorem restrictLimitProj_toX₀ (j : D.Stages) :
    restrictLimitProj hU₀ g hgflat hgfp j ≫ restrictStageToX₀ hU₀ g hgflat hgfp j =
      restrictLimitToX₀ hU₀ g hgflat hgfp :=
  (D.toRelative.restrict hU₀ g hgflat hgfp).fᵢ_toX₀ j.1 j.2

/-- Two morphisms into a restricted stage agree if they agree after composing with the projections
to the stage of Situation 09RH and to `U₀`. -/
theorem restrictStage_hom_ext {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : D.Stages)
    {a b : W ⟶ (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ i.1 i.2}
    (h₁ : a ≫ restrictStageToYᵢ hU₀ g hgflat hgfp i = b ≫ restrictStageToYᵢ hU₀ g hgflat hgfp i)
    (h₂ : a ≫ restrictStageToX₀ hU₀ g hgflat hgfp i = b ≫ restrictStageToX₀ hU₀ g hgflat hgfp i) :
    a = b :=
  ((D.toRelative.restrict hU₀ g hgflat hgfp).stage_isPullback i.1 i.2).hom_ext h₁ h₂

/-- Composing `affinePointRestrictStageIso` with the projection of the restricted stage to the
stage of Situation 09RH gives `affinePointStageFst`. -/
@[reassoc]
theorem affinePointRestrictStageIso_hom_restrictStageToYᵢ (i : D.Stages) :
    (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom ≫
        restrictStageToYᵢ hU₀ g hgflat hgfp i = affinePointStageFst hT u i :=
  affinePointRestrictStageIso_hom_toYᵢ hU₀ g hgflat hgfp hT e u hu i

/-- Composing `affinePointRestrictStageIso` with the projection of the restricted stage to `U₀`
gives `affinePointStageSnd` followed by `e.inv`. -/
@[reassoc]
theorem affinePointRestrictStageIso_hom_restrictStageToX₀ (i : D.Stages) :
    (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom ≫
        restrictStageToX₀ hU₀ g hgflat hgfp i = affinePointStageSnd hT u i ≫ e.inv :=
  affinePointRestrictStageIso_hom_toX₀ hU₀ g hgflat hgfp hT e u hu i

/-- Composing `affinePointRestrictLimitIso` with the projection of the restricted limit to the
limit of Situation 09RH gives `affinePointLimitFst`. -/
@[reassoc]
theorem affinePointRestrictLimitIso_hom_restrictLimitToY :
    (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom ≫
        restrictLimitToY hU₀ g hgflat hgfp = affinePointLimitFst hT u :=
  affinePointRestrictLimitIso_hom_toLimit hU₀ g hgflat hgfp hT e u hu

/-- Composing `affinePointRestrictLimitIso` with the projection of the restricted limit to `U₀`
gives `affinePointLimitSnd` followed by `e.inv`. -/
@[reassoc]
theorem affinePointRestrictLimitIso_hom_restrictLimitToX₀ :
    (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom ≫
        restrictLimitToX₀ hU₀ g hgflat hgfp = affinePointLimitSnd hT u ≫ e.inv :=
  affinePointRestrictLimitIso_hom_toInitial hU₀ g hgflat hgfp hT e u hu

/-- The isomorphisms `affinePointRestrictStageIso` intertwine the transition morphisms of the
affine-point situation with those of the restricted stages. -/
theorem affinePointRestrictStageIso_comm {i j : D.Stages} (h : i ≤ j) :
    (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu j).hom ≫
        restrictStageMap hU₀ g hgflat hgfp h =
      (affinePointSituation D hT u).system.map (homOfLE h).op ≫
        (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom := by
  refine restrictStage_hom_ext hU₀ g hgflat hgfp i ?_ ?_
  · rw [Category.assoc, restrictStageMap_toYᵢ,
      affinePointRestrictStageIso_hom_restrictStageToYᵢ_assoc, Category.assoc,
      affinePointRestrictStageIso_hom_restrictStageToYᵢ, affinePoint_map_comp_stageFst]
  · rw [Category.assoc, restrictStageMap_toX₀, affinePointRestrictStageIso_hom_restrictStageToX₀,
      Category.assoc, affinePointRestrictStageIso_hom_restrictStageToX₀,
      affinePoint_map_comp_stageSnd_assoc]

/-- The isomorphism `affinePointRestrictLimitIso` intertwines the limit projections of the
affine-point situation with the projections of the restricted limit, via
`affinePointRestrictStageIso`. -/
theorem affinePointRestrictLimitIso_comm (j : D.Stages) :
    (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom ≫
        restrictLimitProj hU₀ g hgflat hgfp j =
      (affinePointSituation D hT u).limitCone.π.app (op j) ≫
        (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu j).hom := by
  refine restrictStage_hom_ext hU₀ g hgflat hgfp j ?_ ?_
  · rw [Category.assoc, restrictLimitProj_toYᵢ,
      affinePointRestrictLimitIso_hom_restrictLimitToY_assoc, Category.assoc,
      affinePointRestrictStageIso_hom_restrictStageToYᵢ, affinePoint_π_comp_stageFst]
  · rw [Category.assoc, restrictLimitProj_toX₀, affinePointRestrictLimitIso_hom_restrictLimitToX₀,
      Category.assoc, affinePointRestrictStageIso_hom_restrictStageToX₀, ← Category.assoc,
      affinePoint_π_comp_stageSnd]

/-- The isomorphism of `U₀` with the affine point `h_T`, in the category of algebraic spaces. -/
abbrev affinePointBaseIso :
    (⟨U₀, hU₀⟩ : AlgebraicSpaces B S hS) ≅ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :=
  ObjectProperty.isoMk _ e

/-- The isomorphism of an affine model with the corresponding restricted stage. -/
abbrev affineModelRestrictIso (i : D.Stages) :
    (⟨yoneda.obj (affineModel hT u i), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ (D.toRelative.restrict hU₀ g hgflat hgfp).stageSource i :=
  ObjectProperty.isoMk _
    ((affineModelIso hT u i).symm ≪≫ affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i)

/-- The isomorphism of the affine model of the limit with the restricted limit. -/
abbrev affineModelRestrictLimitIso :
    (⟨yoneda.obj (affineLimitModel hT u hconv), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ (D.toRelative.restrict hU₀ g hgflat hgfp).limitSource :=
  ObjectProperty.isoMk _
    ((affineLimitModelIso hT u hconv).symm ≪≫
      affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu)

/-- **The affine models map isomorphically onto the restricted situation**, as a morphism of
systems over `h_T`. -/
def affineModelRestrictHom :
    PullbackData.LimitSystem.Hom (affineModelSystem hT u hconv).toLimitSystem
      ((D.toRelative.restrict hU₀ g hgflat hgfp).toLimitSystem.comp
        (affinePointBaseIso hU₀ e).hom) where
  app i := (affineModelRestrictIso hU₀ g hgflat hgfp hT e u hu i).hom
  app_toBase i := ObjectProperty.hom_ext _ (by
    change ((affineModelIso hT u i).inv ≫
        (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom) ≫
        restrictStageToX₀ hU₀ g hgflat hgfp i ≫ e.hom =
      yoneda.map (yoneda.preimage ((affineModelIso hT u i).inv ≫
        affinePointStageSnd hT u i))
    rw [Functor.map_preimage, Category.assoc,
      affinePointRestrictStageIso_hom_restrictStageToX₀_assoc, Iso.inv_hom_id, Category.comp_id])
  app_transition {i j} h := ObjectProperty.hom_ext _ (by
    change ((affineModelIso hT u j).inv ≫
        (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu j).hom) ≫
        restrictStageMap hU₀ g hgflat hgfp h =
      yoneda.map (affineModelMap hT u h) ≫
        (affineModelIso hT u i).inv ≫
        (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom
    rw [yoneda_map_affineModelMap, Category.assoc, affinePointRestrictStageIso_comm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc])
  limitApp := (affineModelRestrictLimitIso hU₀ g hgflat hgfp hT e u hu hconv).hom
  limitApp_toBase := ObjectProperty.hom_ext _ (by
    change ((affineLimitModelIso hT u hconv).inv ≫
        (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom) ≫
        restrictLimitToX₀ hU₀ g hgflat hgfp ≫ e.hom =
      yoneda.map (yoneda.preimage ((affineLimitModelIso hT u hconv).inv ≫
        affinePointLimitSnd hT u))
    rw [Functor.map_preimage, Category.assoc,
      affinePointRestrictLimitIso_hom_restrictLimitToX₀_assoc, Iso.inv_hom_id, Category.comp_id])
  limitApp_proj j := ObjectProperty.hom_ext _ (by
    change ((affineLimitModelIso hT u hconv).inv ≫
        (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom) ≫
        restrictLimitProj hU₀ g hgflat hgfp j =
      yoneda.map (affineLimitModelProj hT u hconv j) ≫
        (affineModelIso hT u j).inv ≫
        (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu j).hom
    rw [yoneda_map_affineLimitModelProj, Category.assoc, affinePointRestrictLimitIso_comm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc])

include hT e hu hconv in
/-- **The affine case of Stacks 09RI for perfect objects, on the restricted situation.** -/
theorem isColim_restrict_toRelative_of_isPerfect_of_iso
    (X Y : @DerivedCategory (Modules.{u, u} B S hS U₀ hU₀) _ _ (HasDerivedCategory.standard _))
    (hX : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS U₀ hU₀)
      (smallEtaleRingedSite B S hS U₀ hU₀).IsPerfect X)
    (hY : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS U₀ hU₀)
      (smallEtaleRingedSite B S hS U₀ hU₀).IsPerfect Y) :
    (D.toRelative.restrict hU₀ g hgflat hgfp).toLimitSystem.IsColim
      (DerivedPullbackComposition.canonical B S hS).toPullbackData X Y := by
  have hP := (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  set eS := affinePointBaseIso hU₀ e
  set α := affineModelRestrictHom hU₀ g hgflat hgfp hT e u hu hconv
  have hX' := isPerfect_smallEtaleDerivedModulePullback eS.inv X hX
  have hY' := isPerfect_smallEtaleDerivedModulePullback eS.inv Y hY
  have h₁ := (affineModelSystem hT u hconv).isColim_of_isPerfect
    (isRingColimit_affineModelSystem hT u hconv) _ _ hX' hY'
  have h₂ := (PullbackData.LimitSystem.Hom.isColim_iff α _ _ hP
    (fun j => PullbackData.bijective_factorHom_of_fullyFaithful _ _
      (smallEtaleDerivedModulePullbackEquivalence B S hS
        (affineModelRestrictIso hU₀ g hgflat hgfp hT e u hu j)).fullyFaithfulFunctor _ _)
    (PullbackData.bijective_factorHom_of_fullyFaithful _ _
      (smallEtaleDerivedModulePullbackEquivalence B S hS
        (affineModelRestrictLimitIso hU₀ g hgflat hgfp hT e u hu hconv)).fullyFaithfulFunctor
      _ _)).2 h₁
  have h₃ := (PullbackData.LimitSystem.isColim_comp_iff
    (S := (D.toRelative.restrict hU₀ g hgflat hgfp).toLimitSystem) hP eS.hom _ _).1 h₂
  exact (h₃.of_iso_fst hP ((smallEtaleDerivedModulePullbackHomInvIso B S hS eS).app X)).of_iso_snd
    hP _ ((smallEtaleDerivedModulePullbackHomInvIso B S hS eS).app Y)

include hconv in
/-- **The affine case of Stacks 09RI for perfect objects, on the restricted situation**: for an
affine algebraic space `U₀` flat and of finite presentation over `X₀`. -/
theorem isColim_restrict_toRelative_of_isPerfect (hU₀a : IsAffineSpace B S hS U₀)
    (X Y : @DerivedCategory (Modules.{u, u} B S hS U₀ hU₀) _ _ (HasDerivedCategory.standard _))
    (hX : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS U₀ hU₀)
      (smallEtaleRingedSite B S hS U₀ hU₀).IsPerfect X)
    (hY : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS U₀ hU₀)
      (smallEtaleRingedSite B S hS U₀ hU₀).IsPerfect Y) :
    (D.toRelative.restrict hU₀ g hgflat hgfp).toLimitSystem.IsColim
      (DerivedPullbackComposition.canonical B S hS).toPullbackData X Y := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hU₀a
  obtain ⟨u, hu⟩ : ∃ u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)), e.inv ≫ g = u :=
    ⟨e.inv ≫ g, rfl⟩
  exact isColim_restrict_toRelative_of_isPerfect_of_iso hU₀ g hgflat hgfp hT e u hu hconv X Y hX hY

end DescentSituation

end AlgebraicGeometry.Space

end
