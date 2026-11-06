module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LocallyNoetherianExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence

/-!
# The comparison morphism `X'' ⟶ X'` on locally Noetherian schemes

In the situation of Stacks 0GH8, let `X` carry a functorial bijection `α : F ≅ Mor_S(-, X)` on
locally Noetherian schemes, as in **Stacks 0GHC**, and let `h : X'' ⟶ X` be the algebraization
over `X` of the formal modification `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}`
(`AlgebraicGeometry.Artin.ContractionSituation.Algebraization`). This file attaches to a
morphism `ξ : V ⟶ X''` from a locally Noetherian scheme a morphism `y : V ⟶ X'`.

Let `t = (Z, u', x̂)` be the triple matching `ξ ∘ h` and let `V' ⟶ V`, `x̂'`, `x'` witness its
compatibility. The morphism `ξ_{/Z}` followed by `X''_{/T''} ≅ X_{/T} ×_W X'_{/T'} ⟶ X'_{/T'}` is
a morphism `s : V_{/Z} ⟶ X'_{/T'}` with `g ∘ s = x̂`
(`AlgebraicGeometry.Artin.ContractionSituation.modificationCompletion_comp_g`), hence a section
of `V'_{/Z} = V_{/Z} ×_W X'_{/T'}` over `V_{/Z}`. By Stacks 0GDR over `V` it is the completion of a
section `σ : V ⟶ V'`, and `y = x' ∘ σ` restricts to `u'` on `V ∖ Z` and to `s` on `V_{/Z}`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_mor_restrict_completion`: the morphism
  `y` with its two restrictions.

## References

* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ContractionSolutionModificationMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ContractionSolutionModificationMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_ContractionSolutionModificationMap.has_limit _

/-- Pullbacks of fppf sheaves in `Type (u + 1)` on `BigFppfOver B S hS`: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_ContractionSolutionModificationMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) := by
  set_option synthInstance.maxHeartbeats 400000 in infer_instance

local instance (priority := high) hasLimit_cospan_sheaf_ContractionSolutionModificationMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)
    {hX : IsAlgebraicSpace B S hS X}
    {hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)}
    (A : Algebraization c α hX hft)

/-- The isomorphism `X''_{/T''} ≅ X_{/T} ×_{a, W, g} X'_{/T'}` of the algebraization, as a
morphism out of the completion of `X''` along `T'' = |h|⁻¹ T`. -/
noncomputable def Algebraization.eLeft :
    Space.completionSheaf B S hS A.Y (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) ⟶
      pullback c.g (completionSheafIsoWExt c α hX hft).hom :=
  A.e.hom.left

/-- The isomorphism of the algebraization lies over `X_{/T}`. -/
theorem Algebraization.eLeft_comp :
    A.eLeft ≫ contractionModification c α hX hft =
      Space.completionSheafMap B S hS A.h (contractedLocus c α) :=
  Over.w A.e.hom

/-- The closed subset of the triple matching `ξ ∘ h` lies over `T'' = |h|⁻¹ T`. -/
theorem tripleOfMor_Z_subset (V : LocallyNoetherianOver B S hS) (ξ : yoneda.obj V.obj ⟶ A.Y) :
    (tripleOfMor c α V (ξ ≫ A.h)).Z ⊆ Space.pointsMap B S hS (yoneda.obj V.obj) ξ ⁻¹'
      (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) := fun z hz => by
  rwa [← preimage_contractedLocus c α V (ξ ≫ A.h), Space.pointsMap_comp] at hz

/-- The morphism `V_{/Z} ⟶ X'_{/T'}` attached to `ξ : V ⟶ X''`: the completion of `ξ`, followed
by the identification `X''_{/T''} ≅ X_{/T} ×_{a, W, g} X'_{/T'}` and the projection. -/
noncomputable def modificationCompletion (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ A.Y) :
    Space.completionSheaf B S hS (yoneda.obj V.obj) (tripleOfMor c α V (ξ ≫ A.h)).Z ⟶
      Space.completionSheaf B S hS c.X' c.T' :=
  Space.completionSheafRestrict B S hS ξ _ _ (tripleOfMor_Z_subset c α A V ξ) ≫ A.eLeft ≫
    pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom

/-- `g ∘ s = x̂` for the morphism `s` attached to `ξ` and the triple `(Z, u', x̂)` of `ξ ∘ h`. -/
theorem modificationCompletion_comp_g (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ A.Y) :
    modificationCompletion c α A V ξ ≫ c.g = (tripleOfMor c α V (ξ ≫ A.h)).xhat := by
  have hw : A.eLeft ≫ pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom ≫ c.g =
      Space.completionSheafMap B S hS A.h (contractedLocus c α) ≫
        (completionSheafIsoWExt c α hX hft).hom := by
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ (completionSheafIsoWExt c α hX hft).hom) A.eLeft_comp
  rw [tripleOfMor_xhat c α hX hft, modificationCompletion]
  simp only [Category.assoc]
  rw [hw, ← Space.completionSheafRestrict_self B S hS A.h (contractedLocus c α) (fun _ h => h),
    ← Category.assoc, Space.completionSheafRestrict_comp B S hS ξ A.h _ _ _
      (tripleOfMor_Z_subset c α A V ξ) (fun _ h => h)]

/-- Restricting a completion along the identity to a set of points equal to the given one is an
isomorphism. -/
theorem isIso_completionSheafRestrict_id {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T' T : Set (Space.points B S hS F)) (hT : T' = T)
    (h : T' ⊆ Space.pointsMap B S hS F (𝟙 F) ⁻¹' T) :
    IsIso (Space.completionSheafRestrict B S hS (𝟙 F) T' T h) := by
  subst hT
  rw [Space.completionSheafRestrict_id]
  infer_instance

/-- For a locally Noetherian scheme `V` and `ξ : V ⟶ X''`, let `(Z, u', x̂)` be the triple matching
`ξ ∘ h`. There is a morphism `y : V ⟶ X'` restricting to `u'` on `V ∖ Z` and to the morphism
`AlgebraicGeometry.Artin.ContractionSituation.modificationCompletion` on `V_{/Z}`. -/
theorem exists_mor_restrict_completion (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ A.Y) :
    ∃ y : yoneda.obj V.obj ⟶ c.X',
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
          (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι ≫ y =
        (tripleOfMor c α V (ξ ≫ A.h)).u ≫ c.U'.ι ∧
      Space.completionSheafInclusion B S hS (yoneda.obj V.obj) (tripleOfMor c α V (ξ ≫ A.h)).Z ≫
          Space.sheafifiedULiftMap B S hS y =
        modificationCompletion c α A V ξ ≫ Space.completionSheafInclusion B S hS c.X' c.T' := by
  obtain ⟨w⟩ := (tripleOfMor c α V (ξ ≫ A.h)).compatible
  have hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.obj) := V.property
  have hN := Space.hasEtaleLocalProperty_isLocallyNoetherian_yoneda hVN
  have hYV := isAlgebraicSpace_yoneda B S hS V.obj
  have hpb := w.isPullback_j.flip
  have hpU : IsIso (pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
      (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι) := by
    have : pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
        (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι = hpb.isoPullback.inv := by
      rw [← Iso.cancel_iso_hom_left hpb.isoPullback, Iso.hom_inv_id, hpb.isoPullback_hom_snd]
    rw [this]
    infer_instance
  have bij := Space.completionOverFunctor_map_bijective hYV hN
    (tripleOfMor c α V (ξ ≫ A.h)).isClosed_Z w.isAlgebraicSpace_V' w.isProper_p.2.1.1 hpU
    (𝟙 (yoneda.obj V.obj)) hYV hN
  let κ := Space.completionSheafMap B S hS (𝟙 (yoneda.obj V.obj)) (tripleOfMor c α V (ξ ≫ A.h)).Z
  let lift := w.isPullback_xhat'.lift κ (κ ≫ modificationCompletion c α A V ξ)
    (by rw [Category.assoc, modificationCompletion_comp_g])
  have hlift : lift ≫ Space.completionSheafMap B S hS w.p (tripleOfMor c α V (ξ ≫ A.h)).Z = κ := by
    rw [← Space.completionSheafRestrict_self B S hS w.p _ (fun _ hz => hz)]
    exact w.isPullback_xhat'.lift_fst _ _ _
  obtain ⟨σ, hσ⟩ := bij.2 (Over.homMk lift hlift)
  have hσl : Space.completionOverMap B S hS (tripleOfMor c α V (ξ ≫ A.h)).Z σ = lift :=
    congrArg (fun φ => φ.left) hσ
  have hσw : σ.left ≫ w.p = 𝟙 _ := Over.w σ
  refine ⟨σ.left ≫ w.x', ?_, ?_⟩
  · have hj : (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
        (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι ≫ σ.left = w.j := by
      have hw : 𝟙 _ ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
          (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι =
          ((Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
            (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι ≫ σ.left) ≫ w.p := by
        rw [Category.assoc, hσw]
        simp
      have h1 := w.isPullback_j.lift_fst _ _ hw
      have h2 := w.isPullback_j.lift_snd _ _ hw
      rw [Category.comp_id] at h1
      rw [← h2, h1, Category.id_comp]
    rw [← Category.assoc, hj, w.restrict_x']
  · have hκr : κ = _ := (Space.completionSheafRestrict_self B S hS (𝟙 (yoneda.obj V.obj))
      (tripleOfMor c α V (ξ ≫ A.h)).Z (fun _ hz => hz)).symm
    have hκ : κ ≫ Space.completionSheafInclusion B S hS (yoneda.obj V.obj)
        (tripleOfMor c α V (ξ ≫ A.h)).Z =
        Space.completionSheafInclusion B S hS (yoneda.obj V.obj)
          (Space.pointsMap B S hS (yoneda.obj V.obj) (𝟙 _) ⁻¹'
            (tripleOfMor c α V (ξ ≫ A.h)).Z) := by
      rw [hκr]
      exact (Space.completionSheafRestrict_comp_inclusion B S hS (𝟙 _) _ _
        (fun _ hz => hz)).trans (by rw [Space.sheafifiedULiftMap_id, Category.comp_id])
    have hiso : IsIso κ := by
      rw [hκr]
      exact isIso_completionSheafRestrict_id _ _ (by rw [Space.pointsMap_id, Set.preimage_id]) _
    have hcomp : lift ≫ Space.completionSheafInclusion B S hS w.V'
        (Space.pointsMap B S hS w.V' w.p ⁻¹' (tripleOfMor c α V (ξ ≫ A.h)).Z) =
        Space.completionSheafInclusion B S hS (yoneda.obj V.obj)
          (Space.pointsMap B S hS (yoneda.obj V.obj) (𝟙 _) ⁻¹'
            (tripleOfMor c α V (ξ ≫ A.h)).Z) ≫ Space.sheafifiedULiftMap B S hS σ.left := by
      rw [← hσl]
      exact Space.completionOverMap_comp_inclusion B S hS _ σ
    rw [← cancel_epi κ, ← Category.assoc, hκ, Space.sheafifiedULiftMap_comp, ← Category.assoc,
      ← hcomp, Category.assoc, w.completion_x', ← Category.assoc, w.isPullback_xhat'.lift_snd,
      Category.assoc]

/-- A section of the ambient sheafified universe lift of an fppf sheaf `F` which comes from the
completion `F_{/T}` and equals the section given by `v ∈ F(U)` forces `v` to have point-set image
in `T`: the completion of a sheaf is the subfunctor of sections with image in `T`. -/
theorem hasImageIn_of_completionSheafInclusion_app_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hFu : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F ⋙ uliftFunctor.{u + 1}))
    {T : Set (Space.points B S hS F)} {U : BigFppfOver B S hS}
    (w : (Space.completionSheaf B S hS F T).obj.obj (op U)) (v : F.obj (op U))
    (h : (Space.completionSheafInclusion B S hS F T).hom.app (op U) w =
      ((BigFppfOver.topology B S hS).toSheafify (F ⋙ uliftFunctor.{u + 1})).app (op U)
        (ULift.up v)) :
    Space.HasImageIn B S hS F T U v := by
  let e := Space.completionSheafIsoSubfunctor B S hS hF T
  have hw : FormalSpace.presheafSection B S hS (e.hom.app (op U) w).1.down
      (e.hom.app (op U) w).2 = w :=
    congrArg (fun φ => φ.app (op U) w) e.hom_inv_id
  have h2 := FormalSpace.inclusion_presheafSection B S hS (T := T) (e.hom.app (op U) w).1.down
    (e.hom.app (op U) w).2
  rw [hw] at h2
  have hv := congrArg (FormalSpace.ambientRead B S hS hFu) (h2.symm.trans h)
  rw [FormalSpace.ambientRead_toSheafify, FormalSpace.ambientRead_toSheafify] at hv
  rw [← hv]
  exact (e.hom.app (op U) w).2

/-- Read on a section `x` with image in `Z`, the compatibility of `y : V ⟶ X'` with
`s : V_{/Z} ⟶ X'_{/T'}` says that the section `y(x)` is the one `s` attaches to `x`. -/
theorem completionSheafInclusion_app_eq_of_comp_eq {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z : Set (Space.points B S hS F')} {T : Set (Space.points B S hS F)} (y : F' ⟶ F)
    (s : Space.completionSheaf B S hS F' Z ⟶ Space.completionSheaf B S hS F T)
    (hy : Space.completionSheafInclusion B S hS F' Z ≫ Space.sheafifiedULiftMap B S hS y =
      s ≫ Space.completionSheafInclusion B S hS F T)
    {U : BigFppfOver B S hS} (x : F'.obj (op U)) (hx : Space.HasImageIn B S hS F' Z U x) :
    (Space.completionSheafInclusion B S hS F T).hom.app (op U)
        (s.hom.app (op U) (FormalSpace.presheafSection B S hS x hx)) =
      ((BigFppfOver.topology B S hS).toSheafify (F ⋙ uliftFunctor.{u + 1})).app (op U)
        (ULift.up (y.app (op U) x)) := by
  have h := congrArg (fun φ => φ.hom.app (op U) (FormalSpace.presheafSection B S hS x hx)) hy
  change (Space.sheafifiedULiftMap B S hS y).hom.app (op U)
      ((Space.completionSheafInclusion B S hS F' Z).hom.app (op U)
        (FormalSpace.presheafSection B S hS x hx)) = _ at h
  refine h.symm.trans ?_
  rw [FormalSpace.inclusion_presheafSection, FormalSpace.sheafifiedULiftMap_toSheafify]

/-- A morphism `y : F' ⟶ F` into an algebraic space compatible with a morphism of completions
`F'_{/Z} ⟶ F_{/T}` carries `Z` into `T`. -/
theorem image_subset_of_completion_comp_eq {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {Z : Set (Space.points B S hS F')}
    {T : Set (Space.points B S hS F)} (y : F' ⟶ F)
    (s : Space.completionSheaf B S hS F' Z ⟶ Space.completionSheaf B S hS F T)
    (hy : Space.completionSheafInclusion B S hS F' Z ≫ Space.sheafifiedULiftMap B S hS y =
      s ≫ Space.completionSheafInclusion B S hS F T) :
    Space.pointsMap B S hS F' y '' Z ⊆ T := by
  rintro _ ⟨z, hz, rfl⟩
  induction z using Quot.ind with | _ p =>
  have hp : Space.HasImageIn B S hS F' Z p.siteObject p.value := by
    rw [Space.hasImageIn_iff_range_subset]
    rintro _ ⟨w, rfl⟩
    rw [Space.FieldValuedPoint.pointsMap_eq_class]
    exact hz
  have hyp := hasImageIn_of_completionSheafInclusion_app_eq hF.isSheaf
    (FormalSpace.isSheaf_comp_uliftFunctor B S hS hF) _ _
    (completionSheafInclusion_app_eq_of_comp_eq y s hy p.value hp)
  rw [Space.hasImageIn_iff_range_subset, ← yonedaEquiv_symm_naturality_right] at hyp
  have h := hyp ⟨(Space.FieldValuedPoint.tautological B S hS p).class B S hS _, rfl⟩
  have h2 : Space.pointsMap B S hS F' y (p.class B S hS F') ∈ T := by
    rw [← Space.FieldValuedPoint.pointsMap_class_tautological B S hS p,
      ← Function.comp_apply (f := Space.pointsMap B S hS F' y), ← Space.pointsMap_comp]
    exact h
  exact h2

/-- **Uniqueness of `y`.** Two morphisms `V ⟶ X'` with the same restriction to `V ∖ Z` and
compatible with the same morphism `s : V_{/Z} ⟶ X'_{/T'}` are equal, by Stacks 0AR7. -/
theorem eq_of_restrict_completion (V : LocallyNoetherianOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V.obj))} (hZ : IsClosed Z)
    (m : (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj) Zᶜ).toFunctor ⟶ c.X')
    (s : Space.completionSheaf B S hS (yoneda.obj V.obj) Z ⟶
      Space.completionSheaf B S hS c.X' c.T') {y₁ y₂ : yoneda.obj V.obj ⟶ c.X'}
    (h₁ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj) Zᶜ).ι ≫ y₁ = m)
    (h₁' : Space.completionSheafInclusion B S hS (yoneda.obj V.obj) Z ≫
        Space.sheafifiedULiftMap B S hS y₁ = s ≫ Space.completionSheafInclusion B S hS c.X' c.T')
    (h₂ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj) Zᶜ).ι ≫ y₂ = m)
    (h₂' : Space.completionSheafInclusion B S hS (yoneda.obj V.obj) Z ≫
        Space.sheafifiedULiftMap B S hS y₂ = s ≫ Space.completionSheafInclusion B S hS c.X' c.T') :
    y₁ = y₂ := by
  have hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.obj) := V.property
  have hFu := FormalSpace.isSheaf_comp_uliftFunctor B S hS c.isAlgebraicSpace_X'
  refine Space.eq_of_eq_on_compl_of_completionSubfunctorMap_eq B S hS
    (isAlgebraicSpace_yoneda B S hS V.obj) c.isAlgebraicSpace_X'
    (Space.hasEtaleLocalProperty_isLocallyNoetherian_yoneda hVN)
    (FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian
      c.isAlgebraicSpace_X'
      (isLocallyNoetherian_of_isLocallyOfFiniteType_base c c.isLocallyOfFiniteType_X'))
    hZ c.isClosed_T' y₁ y₂
    (image_subset_of_completion_comp_eq c.isAlgebraicSpace_X' y₁ _ h₁')
    (image_subset_of_completion_comp_eq c.isAlgebraicSpace_X' y₂ _ h₂') (h₁.trans h₂.symm) ?_
  ext U ⟨⟨x⟩, hx⟩
  apply Subtype.ext
  apply ULift.ext
  have e₁ := completionSheafInclusion_app_eq_of_comp_eq y₁ _ h₁' x hx
  have e₂ := completionSheafInclusion_app_eq_of_comp_eq y₂ _ h₂' x hx
  have h := congrArg (FormalSpace.ambientRead B S hS hFu) (e₁.symm.trans e₂)
  rwa [FormalSpace.ambientRead_toSheafify, FormalSpace.ambientRead_toSheafify] at h

/-- The morphism `y : V ⟶ X'` attached to `ξ : V ⟶ X''`
(`AlgebraicGeometry.Artin.ContractionSituation.exists_mor_restrict_completion`). -/
noncomputable def modificationMor (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ A.Y) : yoneda.obj V.obj ⟶ c.X' :=
  (exists_mor_restrict_completion c α A V ξ).choose

/-- The restriction of `modificationMor c α A V ξ` to the complement of `Z` is `u` followed by the
inclusion `U' ⟶ X'`, where `(Z, u, s)` is the triple attached to `ξ ≫ A.h`. -/
theorem modificationMor_restrict (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ A.Y) :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
        (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι ≫ modificationMor c α A V ξ =
      (tripleOfMor c α V (ξ ≫ A.h)).u ≫ c.U'.ι :=
  (exists_mor_restrict_completion c α A V ξ).choose_spec.1

/-- On the completion of `V` along `Z`, the morphism `modificationMor c α A V ξ` agrees with
`modificationCompletion c α A V ξ` followed by the inclusion of the completion of `X'` along
`T'`. -/
theorem modificationMor_completion (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ A.Y) :
    Space.completionSheafInclusion B S hS (yoneda.obj V.obj) (tripleOfMor c α V (ξ ≫ A.h)).Z ≫
        Space.sheafifiedULiftMap B S hS (modificationMor c α A V ξ) =
      modificationCompletion c α A V ξ ≫ Space.completionSheafInclusion B S hS c.X' c.T' :=
  (exists_mor_restrict_completion c α A V ξ).choose_spec.2

/-- The triple matching a morphism restricted along `φ` is the transported triple. -/
theorem tripleOfMor_comp {V₂ V₁ : LocallyNoetherianOver B S hS} (φ : V₂ ⟶ V₁)
    (ζ : yoneda.obj V₁.obj ⟶ X) :
    tripleOfMor c α V₂ (yoneda.map φ.hom ≫ ζ) = mapTriple c φ.hom (tripleOfMor c α V₁ ζ) := by
  have h := tripleOfMor_map c α φ (yonedaEquiv ζ)
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  congr 1
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map, map_yonedaEquiv]

/-- **Naturality of `y`** in the locally Noetherian scheme `V`, for `ξ₂ = ξ ∘ φ`. -/
theorem modificationMor_naturality_of_eq {V₂ V₁ : LocallyNoetherianOver B S hS} (φ : V₂ ⟶ V₁)
    (ξ : yoneda.obj V₁.obj ⟶ A.Y) (ξ₂ : yoneda.obj V₂.obj ⟶ A.Y)
    (hξ : yoneda.map φ.hom ≫ ξ = ξ₂) :
    modificationMor c α A V₂ ξ₂ = yoneda.map φ.hom ≫ modificationMor c α A V₁ ξ := by
  have htr : tripleOfMor c α V₂ (ξ₂ ≫ A.h) =
      mapTriple c φ.hom (tripleOfMor c α V₁ (ξ ≫ A.h)) := by
    rw [← hξ, Category.assoc]; exact tripleOfMor_comp c α φ (ξ ≫ A.h)
  have hq : (tripleOfMor c α V₂ (ξ₂ ≫ A.h)).Z ⊆
      Space.pointsMap B S hS (yoneda.obj V₂.obj) (yoneda.map φ.hom) ⁻¹'
        (tripleOfMor c α V₁ (ξ ≫ A.h)).Z := by
    rw [htr]; exact (mapTriple_Z_eq_preimage c φ.hom _).subset
  refine eq_of_restrict_completion c V₂ (tripleOfMor c α V₂ (ξ₂ ≫ A.h)).isClosed_Z _
    (modificationCompletion c α A V₂ ξ₂)
    (modificationMor_restrict c α A V₂ _) (modificationMor_completion c α A V₂ _) ?_ ?_
  · rw [htr]
    have k1 := Space.openSubspaceOfPointsRestrict_comp_ι B S hS (yoneda.map φ.hom)
      (mapTriple c φ.hom (tripleOfMor c α V₁ (ξ ≫ A.h))).Zᶜ
      (tripleOfMor c α V₁ (ξ ≫ A.h)).Zᶜ (fun _ hz => hz)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ modificationMor c α A V₁ ξ)
      k1.symm)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (modificationMor_restrict c α A V₁ ξ)).trans
          (Category.assoc _ _ _).symm))
  · have e2 := Space.completionSheafRestrict_comp_inclusion B S hS (yoneda.map φ.hom) _ _ hq
    have e3 := modificationMor_completion c α A V₁ ξ
    have e4 : Space.completionSheafRestrict B S hS (yoneda.map φ.hom) _ _ hq ≫
        modificationCompletion c α A V₁ ξ = modificationCompletion c α A V₂ ξ₂ := by
      subst hξ
      have e1 := Space.completionSheafRestrict_comp B S hS (yoneda.map φ.hom) ξ _ _
        (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) hq
        (tripleOfMor_Z_subset c α A V₁ ξ) (tripleOfMor_Z_subset c α A V₂ (yoneda.map φ.hom ≫ ξ))
      unfold modificationCompletion
      rw [e1]
      simp only [Category.assoc]
    rw [← e4, Category.assoc, ← e3, ← Category.assoc, e2, Space.sheafifiedULiftMap_comp,
      Category.assoc]

/-- **Naturality of `y`** in the locally Noetherian scheme `V`. -/
theorem modificationMor_naturality {V₂ V₁ : LocallyNoetherianOver B S hS} (φ : V₂ ⟶ V₁)
    (ξ : yoneda.obj V₁.obj ⟶ A.Y) :
    modificationMor c α A V₂ (yoneda.map φ.hom ≫ ξ) =
      yoneda.map φ.hom ≫ modificationMor c α A V₁ ξ :=
  modificationMor_naturality_of_eq c α A φ ξ _ rfl

/-- `X''` is locally of finite type over `S`: `h : X'' ⟶ X` is proper and `X` is locally of
finite type over `S`. -/
theorem Algebraization.isLocallyOfFiniteType_Y :
    Space.IsLocallyOfFiniteType B S hS (terminal.from A.Y) := by
  let e : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS _)
  rw [show terminal.from A.Y = A.h ≫ terminal.from X from terminal.hom_ext _ _]
  exact Space.isLocallyOfFiniteType_comp' (f := A.h) (g := terminal.from X) (hG := hX) (hH := hT)
    (hf := A.isProper_h.2.1.1) (hg := hft)

/-- The morphisms `y`, as a transformation of functors on locally Noetherian schemes over `S`
from `X''` to `X'`. -/
noncomputable def modificationTrans :
    (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ A.Y ⋙
          uliftFunctor.{u + 1} ⟶
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ c.X' ⋙
          uliftFunctor.{u + 1} where
  app V := ↾fun a => ULift.up (yonedaEquiv (modificationMor c α A V.unop
    (yonedaEquiv.symm a.down)))
  naturality V₁ V₂ φ := by
    ext a
    apply ULift.ext
    change yonedaEquiv (modificationMor c α A V₂.unop
      (yonedaEquiv.symm (A.Y.map φ.unop.hom.op a.down))) =
      c.X'.map φ.unop.hom.op (yonedaEquiv (modificationMor c α A V₁.unop
        (yonedaEquiv.symm a.down)))
    have h1 : yonedaEquiv.symm (A.Y.map φ.unop.hom.op a.down) =
        yoneda.map φ.unop.hom ≫ yonedaEquiv.symm a.down := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      exact (yonedaEquiv_symm_app_apply (X := V₁.unop.obj) a.down (op V₂.unop.obj) φ.unop.hom).symm
    rw [h1, modificationMor_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
      map_yonedaEquiv]

/-- There is a unique morphism `x'' : X'' ⟶ X'` whose restriction to locally Noetherian schemes is
the transformation `AlgebraicGeometry.Artin.ContractionSituation.modificationTrans`. -/
theorem existsUnique_modificationHom :
    ∃! x : A.Y ⟶ c.X', Functor.whiskerRight (Functor.whiskerLeft
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op x)
        uliftFunctor.{u + 1} = modificationTrans c α A := by
  have := c.isLocallyNoetherian_base
  exact Space.existsUnique_hom_whiskerRight_whiskerLeft_eq B S hS A.isAlgebraicSpace_Y
    A.isLocallyOfFiniteType_Y c.isAlgebraicSpace_X' c.isLocallyOfFiniteType_X' _

/-- The comparison morphism `x'' : X'' ⟶ X'`. -/
noncomputable def modificationHom : A.Y ⟶ c.X' :=
  (existsUnique_modificationHom c α A).exists.choose

/-- On a locally Noetherian scheme `V`, the comparison morphism `x''` sends `ξ : V ⟶ X''` to the
morphism `y : V ⟶ X'` of `AlgebraicGeometry.Artin.ContractionSituation.modificationMor`. -/
theorem comp_modificationHom (V : LocallyNoetherianOver B S hS) (ξ : yoneda.obj V.obj ⟶ A.Y) :
    ξ ≫ modificationHom c α A = modificationMor c α A V ξ := by
  have h := congrArg (fun τ => (τ.app (op V) (ULift.up (yonedaEquiv (C := BigFppfOver B S hS)
    (X := V.obj) ξ))).down) (existsUnique_modificationHom c α A).exists.choose_spec
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  refine h.trans ?_
  show yonedaEquiv (modificationMor c α A V (yonedaEquiv.symm (yonedaEquiv ξ))) = _
  rw [Equiv.symm_apply_apply]

end AlgebraicGeometry.Artin.ContractionSituation

end
