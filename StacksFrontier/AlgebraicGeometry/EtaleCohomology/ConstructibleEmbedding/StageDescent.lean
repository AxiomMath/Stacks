module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.LocallyConstantLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.LocallyConstantPushforward
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination

/-!
# Sections of direct images of locally constant maps along a limit of finite morphisms

Let `f : Y ⟶ X` be a morphism presented as the limit of finite morphisms `f_i : Y_i ⟶ X` (an
`AlgebraicGeometry.IntegralLimitPresentation`, Stacks 09YZ), and let `M` be a `Λ`-module. Over an
affine étale `X`-scheme `W` the sections of `f_* 𝓛_Y(M)` are the locally constant maps on
`W ×_X Y = lim_i W ×_X Y_i`, and those come from a stage, uniquely up to passing to a later stage
(`AlgebraicGeometry.exists_locallyConstant_comap_eq_of_isLimit`). So the sections of `f_* 𝓛_Y(M)`
over `W` are the filtered colimit of the sections of the `f_{i,*} 𝓛_{Y_i}(M)`.

## Main definitions

* `Stacks.EtaleCohomology.IntegralLimitPresentation.stageMap` — the comparison
  `f_{i,*} 𝓛_{Y_i}(M) ⟶ f_* 𝓛_Y(M)`.
* `Stacks.EtaleCohomology.IntegralLimitPresentation.transitionMap` — the comparison between two
  stages.

## Main results

* `Stacks.EtaleCohomology.IntegralLimitPresentation.exists_stageMap_app_eq` and
  `Stacks.EtaleCohomology.IntegralLimitPresentation.exists_transitionMap_app_eq` — surjectivity
  and injectivity of the colimit of sections over an affine étale `X`-scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology.IntegralLimitPresentation

attribute [local instance] AlgebraicGeometry.IntegralLimitPresentation.indexPreorder
  AlgebraicGeometry.IntegralLimitPresentation.indexNonempty
  AlgebraicGeometry.IntegralLimitPresentation.indexDirected

variable (Λ : Type r) [Ring Λ] (M : Type (max (u + 1) r)) [AddCommGroup M] [Module Λ M]
  {X Y : Scheme.{u}} {f : Y ⟶ X} (P : AlgebraicGeometry.IntegralLimitPresentation f)

/-- The structure morphism of a stage. -/
abbrev stage (i : P.indexTypeᵒᵖ) : P.diagram.obj i ⟶ X := P.structureMap.app i

/-- The stage structure morphisms commute with the transition maps of the diagram. -/
theorem stage_naturality {i j : P.indexTypeᵒᵖ} (φ : i ⟶ j) :
    P.diagram.map φ ≫ stage P j = stage P i := by
  simp

/-- The comparison `f_{i,*} 𝓛_{Y_i}(M) ⟶ f_* 𝓛_Y(M)` of a stage with the limit. -/
def stageMap (i : P.indexTypeᵒᵖ) :
    (etaleModuleDirectImage.{u, r} Λ (stage P i)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ (P.diagram.obj i) M) ⟶
      (etaleModuleDirectImage.{u, r} Λ f).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y M) :=
  locallyConstantPushforwardMap Λ M (stage P i) f (P.limitCone.app i) (P.compatible i).symm

/-- The comparison between two stages. -/
def transitionMap {i j : P.indexTypeᵒᵖ} (φ : i ⟶ j) :
    (etaleModuleDirectImage.{u, r} Λ (stage P j)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ (P.diagram.obj j) M) ⟶
      (etaleModuleDirectImage.{u, r} Λ (stage P i)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ (P.diagram.obj i) M) :=
  locallyConstantPushforwardMap Λ M (stage P j) (stage P i) (P.diagram.map φ)
    (stage_naturality P φ)

/-- The comparison maps of the stages are compatible with the transition maps. -/
theorem transitionMap_comp_stageMap {i j : P.indexTypeᵒᵖ} (φ : i ⟶ j) :
    transitionMap Λ M P φ ≫ stageMap Λ M P i = stageMap Λ M P j := by
  rw [transitionMap, stageMap, locallyConstantPushforwardMap_comp]
  congr 1
  simpa using (P.limitCone.naturality φ).symm

/-- The transition maps compose: `transitionMap ψ ≫ transitionMap φ = transitionMap (φ ≫ ψ)`. -/
theorem transitionMap_comp {i j k : P.indexTypeᵒᵖ} (φ : i ⟶ j) (ψ : j ⟶ k) :
    transitionMap Λ M P ψ ≫ transitionMap Λ M P φ = transitionMap Λ M P (φ ≫ ψ) := by
  rw [transitionMap, transitionMap, locallyConstantPushforwardMap_comp, transitionMap]
  congr 1
  exact (P.diagram.map_comp φ ψ).symm

/-- The transition morphisms of the diagram of a presentation are affine. -/
instance isAffineHom_diagram_map {i j : P.indexTypeᵒᵖ} (φ : i ⟶ j) :
    IsAffineHom (P.diagram.map φ) := by
  have : IsFinite (stage P j) := P.stageFinite j
  have : IsFinite (stage P i) := P.stageFinite i
  have : IsAffineHom (P.diagram.map φ ≫ stage P j) := by
    rw [stage_naturality]
    infer_instance
  exact IsAffineHom.of_comp (P.diagram.map φ) (stage P j)

/-- The base change of a stage along a morphism from an affine scheme is affine. -/
instance isAffine_pullback_stage {W : Scheme.{u}} [IsAffine W] (w : W ⟶ X)
    (i : P.indexTypeᵒᵖ) : IsAffine (pullback w (stage P i)) := by
  have : IsFinite (stage P i) := P.stageFinite i
  exact isAffine_of_isAffineHom (pullback.fst w (stage P i))

/-- The limit cone of the presentation, base changed along `w : W ⟶ X`, is a limit cone. -/
def isLimitOverBaseChange {W : Scheme.{u}} (w : W ⟶ X) :
    IsLimit (overBaseChangeCone (Cone.mk Y P.limitCone) w (stage P) (stage_naturality P) f
      (fun i => (P.compatible i).symm)) :=
  isLimitOverBaseChangeCone (Cone.mk Y P.limitCone) P.isLimit w (stage P) (stage_naturality P) f
    (fun i => (P.compatible i).symm)

/-- The leg at `i` of the base-changed limit cone is the map `W ×_X Y ⟶ W ×_X Y_i` induced by
`Y ⟶ Y_i`. -/
theorem overBaseChangeCone_π_app_eq {W : Scheme.{u}} (w : W ⟶ X) (i : P.indexTypeᵒᵖ) :
    (overBaseChangeCone (Cone.mk Y P.limitCone) w (stage P) (stage_naturality P) f
        (fun i => (P.compatible i).symm)).π.app i =
      pullback.map w f w (stage P i) (𝟙 _) (P.limitCone.app i) (𝟙 _) (by simp)
        (by simp [P.compatible i]) := by
  ext <;> simp [pullback.map]

variable {P} in
/-- Compactness and quasi-separatedness of the stages of a base change along an affine scheme. -/
private theorem stage_compact_qs {W : Scheme.{u}} [IsAffine W] (w : W ⟶ X) :
    (∀ i, CompactSpace
      ↥((overBaseChangeDiagram P.diagram w (stage P) (stage_naturality P)).obj i)) ∧
    (∀ i, QuasiSeparatedSpace
      ↥((overBaseChangeDiagram P.diagram w (stage P) (stage_naturality P)).obj i)) :=
  have := isAffine_pullback_stage P w
  ⟨fun i => inferInstanceAs (CompactSpace ↥(pullback w (stage P i))),
    fun i => inferInstanceAs (QuasiSeparatedSpace ↥(pullback w (stage P i)))⟩

/-- **Every section of `f_* 𝓛_Y(M)` over an affine étale `X`-scheme comes from a stage.** -/
theorem exists_stageMap_app_eq (W : X.Etale) [IsAffine W.left]
    (σ : ((etaleModuleDirectImage.{u, r} Λ f).obj
      (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y M)).obj.obj (op W)) :
    ∃ (i : P.indexTypeᵒᵖ) (τ : ((etaleModuleDirectImage.{u, r} Λ (stage P i)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ (P.diagram.obj i) M)).obj.obj (op W)),
      (stageMap Λ M P i).hom.app (op W) τ = σ := by
  let w : W.left ⟶ X := W.hom
  obtain ⟨h₁, h₂⟩ := stage_compact_qs (P := P) w
  obtain ⟨i, τ, hτ⟩ := exists_locallyConstant_comap_eq_of_isLimit _ _ (isLimitOverBaseChange P w)
    (M := M) (σ : LocallyConstant ↥(pullback w f) M)
  refine ⟨i, τ, ?_⟩
  rw [← hτ, overBaseChangeCone_π_app_eq]
  rfl

/-- **Two sections of a stage which agree in `f_* 𝓛_Y(M)` over an affine étale `X`-scheme agree
at a later stage.** -/
theorem exists_transitionMap_app_eq (W : X.Etale) [IsAffine W.left] {i : P.indexTypeᵒᵖ}
    (τ τ' : ((etaleModuleDirectImage.{u, r} Λ (stage P i)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ (P.diagram.obj i) M)).obj.obj (op W))
    (h : (stageMap Λ M P i).hom.app (op W) τ = (stageMap Λ M P i).hom.app (op W) τ') :
    ∃ (j : P.indexTypeᵒᵖ) (φ : j ⟶ i),
      (transitionMap Λ M P φ).hom.app (op W) τ = (transitionMap Λ M P φ).hom.app (op W) τ' := by
  let w : W.left ⟶ X := W.hom
  obtain ⟨h₁, -⟩ := stage_compact_qs (P := P) w
  have h' : (τ : LocallyConstant ↥(pullback w (stage P i)) M).comap
        ((overBaseChangeCone (Cone.mk Y P.limitCone) w (stage P) (stage_naturality P) f
          (fun i => (P.compatible i).symm)).π.app i).base.hom =
      (τ' : LocallyConstant ↥(pullback w (stage P i)) M).comap
        ((overBaseChangeCone (Cone.mk Y P.limitCone) w (stage P) (stage_naturality P) f
          (fun i => (P.compatible i).symm)).π.app i).base.hom := by
    rw [overBaseChangeCone_π_app_eq]
    exact h
  obtain ⟨j, φ, hj⟩ := exists_locallyConstant_comap_map_eq_of_isLimit _ _
    (isLimitOverBaseChange P w) τ τ' h'
  refine ⟨j, φ, ?_⟩
  have hmap : (overBaseChangeDiagram P.diagram w (stage P) (stage_naturality P)).map φ =
      pullback.map w (stage P j) w (stage P i) (𝟙 _) (P.diagram.map φ) (𝟙 _) (by simp)
        (by simp [stage_naturality P φ]) := by
    ext <;> simp [pullback.map]
  rw [hmap] at hj
  exact hj

end Stacks.EtaleCohomology.IntegralLimitPresentation


end
