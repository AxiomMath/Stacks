module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageAdicness
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalLinear
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalLift

/-!
# The formal component on the descended system

For a stage witness `V'_{k₀} ⟶ V_{k₀}` and a lift `ℓ : V'_{k₀,/} ⟶ W₀ ≅ Spf B` of `g ∘ y^∧`
restricting to `x₀` over the limit
(`AlgebraicGeometry.Artin.ContractionSituation.StageWitness.exists_stage_lift`), this file
defines the ring map `ψ : B ⟶ C_{k₀}^∧` of `ℓ` and proves two facts about it: the image of `ψ` in
`C^∧` is `α ∘ φ` for the ring map `φ : B → A^∧` of `x₀`, and a continuous `φ_k : B → A_k^∧` with
`α ∘ φ_k = ψ` gives a formal component compatible with the witness at the stage `k`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I} (W : StageWitness c κ ξ w k₀)

/-- The terminal stage `𝟙 : k₀ ⟶ k₀`. -/
abbrev topStage (k₀ : I) : Over k₀ := Over.mk (𝟙 k₀)

/-- The projection `V'_k ⟶ V'_{k₀}`. -/
abbrev stageToBase (k : Over k₀) : (stageSpace W k).1 ⟶ W.Y :=
  pullback.snd _ _

/-- Restricting along `f` and then `g` is restricting along any `f'` equal to `f ≫ g`. -/
private theorem completionSheafRestrict_comp_congr {F'' F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F'' ⟶ F'} {g : F' ⟶ F} {f' : F'' ⟶ F} (hf : f ≫ g = f')
    {T'' : Set (Space.points B S hS F'')} {T' : Set (Space.points B S hS F')}
    {T : Set (Space.points B S hS F)} (h₁ : T'' ⊆ Space.pointsMap B S hS F'' f ⁻¹' T')
    (h₂ : T' ⊆ Space.pointsMap B S hS F' g ⁻¹' T) (h' : T'' ⊆ Space.pointsMap B S hS F'' f' ⁻¹' T) :
    Space.completionSheafRestrict B S hS f T'' T' h₁ ≫
      Space.completionSheafRestrict B S hS g T' T h₂ =
    Space.completionSheafRestrict B S hS f' T'' T h' :=
  (Space.completionSheafRestrict_comp B S hS f g T'' T' T h₁ h₂ (hf ▸ h')).symm.trans
    (Space.completionSheafRestrict_congr B S hS hf _ _ _ _)

omit [IsCofiltered I] in
/-- The transition map `V'_{k'} ⟶ V'_k` commutes with the projections to `V'_{k₀}`. -/
theorem stageHom_stageToBase {k k' : Over k₀} (f : k' ⟶ k) :
    stageHom W f ≫ stageToBase W k = stageToBase W k' :=
  stageHom_snd W f

omit [IsCofiltered I] in
/-- The projection `V'_k ⟶ V'_{k₀}` maps the closed subset of `V'_k` over `Z_k` into the
preimage of `Z` in `V'_{k₀}`. -/
theorem subset_stageToBase (k : Over k₀) :
    Space.pointsMap B S hS _ (stageQ W k) ⁻¹' (W.baseChange k.hom).Z ⊆
      Space.pointsMap B S hS _ (stageToBase W k) ⁻¹' (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z) := by
  intro x hx
  change Space.pointsMap B S hS _ W.q (Space.pointsMap B S hS _ (stageToBase W k) x) ∈ W.Z
  rw [← Space.pointsMap_comp_apply, ← pullback.condition, Space.pointsMap_comp_apply]
  exact hx

variable {W₀ : FormalSpace.FppfSheaf B S hS}
  (ℓ : Space.completionSheaf B S hS W.Y (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z) ⟶ W₀)

/-- **The lift `ℓ` restricted to `V'_k`.** -/
def stageFormal (k : Over k₀) :
    Space.completionSheaf B S hS (stageSpace W k).1
      (Space.pointsMap B S hS _ (stageQ W k) ⁻¹' (W.baseChange k.hom).Z) ⟶ W₀ :=
  Space.completionSheafRestrict B S hS (stageToBase W k) _ _ (subset_stageToBase W k) ≫ ℓ

omit [IsCofiltered I] in
/-- The transition map `V'_{k'} ⟶ V'_k` maps the closed subset over `Z_{k'}` into the closed
subset over `Z_k`. -/
theorem subset_stageHom {k k' : Over k₀} (f : k' ⟶ k) :
    Space.pointsMap B S hS _ (stageQ W k') ⁻¹' (W.baseChange k'.hom).Z ⊆
      Space.pointsMap B S hS _ (stageHom W f) ⁻¹'
        (Space.pointsMap B S hS _ (stageQ W k) ⁻¹' (W.baseChange k.hom).Z) := by
  intro x hx
  change Space.pointsMap B S hS _ (stageQ W k) (Space.pointsMap B S hS _ (stageHom W f) x) ∈
    Space.pointsMap B S hS _ (yoneda.map (D.map k.hom).hom) ⁻¹' W.Z
  rw [← Space.pointsMap_comp_apply, stageHom_q, Space.pointsMap_comp_apply, Set.mem_preimage,
    ← Space.pointsMap_comp_apply, ← Functor.map_comp, map_left_hom_comp]
  exact hx

omit [IsCofiltered I] in
/-- Restricting `stageFormal W ℓ k` along the transition map `V'_{k'} ⟶ V'_k` gives
`stageFormal W ℓ k'`. -/
theorem completionSheafRestrict_stageHom_stageFormal {k k' : Over k₀} (f : k' ⟶ k) :
    Space.completionSheafRestrict B S hS (stageHom W f) _ _ (subset_stageHom W f) ≫
      stageFormal W ℓ k = stageFormal W ℓ k' := by
  rw [stageFormal, stageFormal, ← Category.assoc,
    completionSheafRestrict_comp_congr (stageHom_stageToBase W f)]

omit [IsCofiltered I] in
/-- The map `V' ⟶ V'_k` from the limit maps the preimage of `ξ.Z` into the closed subset of
`V'_k` over `Z_k`. -/
theorem subset_stageA (k : Over k₀) :
    Space.pointsMap B S hS w.V' w.p ⁻¹' ξ.Z ⊆
      Space.pointsMap B S hS _ (stageA W k) ⁻¹'
        (Space.pointsMap B S hS _ (stageQ W k) ⁻¹' (W.baseChange k.hom).Z) :=
  (W.baseChange k.hom).toStageModel.subset_preimage_preimage

omit [IsCofiltered I] in
/-- Restricting `stageFormal W ℓ k` along `V' ⟶ V'_k` agrees with restricting `ℓ` along
`V' ⟶ V'_{k₀}`. -/
theorem completionSheafRestrict_stageA_stageFormal (k : Over k₀) :
    Space.completionSheafRestrict B S hS (stageA W k) _ _ (subset_stageA W k) ≫
      stageFormal W ℓ k =
    Space.completionSheafRestrict B S hS W.a _ _ W.toStageModel.subset_preimage_preimage ≫ ℓ := by
  rw [stageFormal, ← Category.assoc,
    completionSheafRestrict_comp_congr (stageA_snd W k)]

section Psi

variable [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}
  (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
    ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
      (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : FormalSpace.QuotientSystem B S hS Bt} (e : W₀ ≅ FormalSpace.formalSpectrum DB)

/-- **The ring map `ψ : B ⟶ C_k^∧` of the lift `ℓ`.** -/
def stagePsi (k : Over k₀) : Bt →+* towerRing (stageIdeal I₀ k) (stageQ W k) :=
  towerRingHom (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k) hB (stageFormal W ℓ k ≫ e.hom)

omit [IsCofiltered I] hD hpt in
/-- The closed subset `ξ.Z` of the limit lies in the preimage of `Z_k`. -/
theorem subset_preimage_stage_Z (k : Over k₀) :
    ξ.Z ⊆ Space.pointsMap B S hS _ (yoneda.map (limitMap κ k)) ⁻¹' (W.baseChange k.hom).Z :=
  (W.baseChange k.hom).toStageModel.subset_preimage_Z

omit [IsCofiltered I] hD hpt in
/-- For `f : k' ⟶ k`, the subset `Z_{k'}` lies in the preimage of `Z_k` under the transition
map. -/
theorem stage_Z_subset {k k' : Over k₀} (f : k' ⟶ k) :
    (W.baseChange k'.hom).Z ⊆
      Space.pointsMap B S hS _ (yoneda.map (D.map f.left).hom) ⁻¹' (W.baseChange k.hom).Z := by
  intro x hx
  change Space.pointsMap B S hS _ (yoneda.map (D.map k.hom).hom)
    (Space.pointsMap B S hS _ (yoneda.map (D.map f.left).hom) x) ∈ W.Z
  rw [← Space.pointsMap_comp_apply, ← Functor.map_comp, map_left_hom_comp]
  exact hx

omit [IsCofiltered I] in
/-- **The image of `ψ` in `C^∧` is `α ∘ φ`** for the ring map `φ : B → A^∧` of `x₀`. -/
theorem limitAlpha_continuousHomEquiv_symm
    {x₀ : Space.completionSheaf B S hS (yoneda.obj κ.pt.obj) ξ.Z ⟶ W₀}
    (hℓ : Space.completionSheafRestrict B S hS W.a _ _ W.toStageModel.subset_preimage_preimage ≫ ℓ =
      Space.completionSheafRestrict B S hS w.p _ ξ.Z (fun _ h => h) ≫ x₀) (k : Over k₀) (b : Bt) :
    limitAlpha W hZI₀ (((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom)).toRingHom b) =
      towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
        (stageA W k) (stageA_q W k) (stagePsi W ℓ hZI₀ hB e k b) := by
  have h1 := towerRingHom_completionSheafRestrict_comp_continuousHomEquiv (limitP w)
    (limit_hZI hZI₀) (limit_hqc (I₀ := I₀) (w := w)) hB
    ((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom))
  rw [Equiv.apply_symm_apply] at h1
  have h2 := towerRingMap_comp_towerRingHom (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k)
    (limitMap κ k) (stageIdeal_map_limit I₀ k).le (limitP w) (stageA W k) (stageA_q W k)
    (limit_hZI hZI₀) (limit_hqc (I₀ := I₀) (w := w)) hB (subset_preimage_stage_Z W k)
    (subset_stageA W k) (stageFormal W ℓ k ≫ e.hom)
  have h3 : Space.completionSheafRestrict B S hS (stageA W k) _ _ (subset_stageA W k) ≫
      stageFormal W ℓ k ≫ e.hom =
    Space.completionSheafRestrict B S hS (limitP w) _ ξ.Z (fun _ hx => hx) ≫ x₀ ≫ e.hom := by
    rw [← Category.assoc, completionSheafRestrict_stageA_stageFormal, hℓ, Category.assoc]
  have h4 := congrArg (fun φ => φ b) h2
  have h5 := congrArg (fun φ => φ b) h1
  rw [h3] at h4
  exact h5.symm.trans h4.symm

omit [IsCofiltered I] hpt in
/-- **A continuous `φ_k : B → A_k^∧` with `α ∘ φ_k = ψ` restricts on `V'_k` to the lift `ℓ`.** -/
theorem completionSheafRestrict_comp_continuousHomEquiv_eq (k : Over k₀)
    (φc : FormalSpace.ContinuousHom DB
      (completionQuotientSystem (D.obj k.left).obj (stageIdeal I₀ k)))
    (F : k ⟶ topStage k₀)
    (h : (stageAlpha W hZI₀ k).comp φc.toRingHom =
      (towerRingMap (D.map F.left).hom (stageIdeal_map_le I₀ F) (stageQ W (topStage k₀))
        (stageQ W k) (stageHom W F) (stageHom_q W F)).comp
          (stagePsi W ℓ hZI₀ hB e (topStage k₀))) :
    Space.completionSheafRestrict B S hS (stageQ W k)
        (Space.pointsMap B S hS _ (stageQ W k) ⁻¹' (W.baseChange k.hom).Z) (W.baseChange k.hom).Z
        (fun _ hx => hx) ≫ continuousHomEquiv (stage_hZI hZI₀ k) hB φc =
      stageFormal W ℓ k ≫ e.hom := by
  refine eq_of_towerRingHom_eq (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k) hB ?_
  have h1 := towerRingHom_completionSheafRestrict_comp_continuousHomEquiv (stageQ W k)
    (stage_hZI hZI₀ k) (stage_hqc W k) hB φc
  have h2 := towerRingMap_comp_towerRingHom (stageQ W (topStage k₀)) (stage_hZI hZI₀ _)
    (stage_hqc W _) (D.map F.left).hom (stageIdeal_map_le I₀ F) (stageQ W k) (stageHom W F)
    (stageHom_q W F) (stage_hZI hZI₀ k) (stage_hqc W k) hB (stage_Z_subset W F)
    (subset_stageHom W F) (stageFormal W ℓ (topStage k₀) ≫ e.hom)
  have h3 : Space.completionSheafRestrict B S hS (stageHom W F) _ _ (subset_stageHom W F) ≫
      stageFormal W ℓ (topStage k₀) ≫ e.hom = stageFormal W ℓ k ≫ e.hom := by
    rw [← Category.assoc, completionSheafRestrict_stageHom_stageFormal]
  rw [h3] at h2
  exact h1.trans (h.trans h2)

end Psi

end AlgebraicGeometry.Artin.LimitStages

end
