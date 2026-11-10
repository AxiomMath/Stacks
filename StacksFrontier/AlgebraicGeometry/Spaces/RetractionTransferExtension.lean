module

public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionTransfer

/-!
# The transfer as a morphism of extensions

Let `X₁`, `X₂` be split square-zero thickenings of `X₀` by `M₁`, `M₂`, in the sense of
`AlgebraicGeometry.Space.IsSplitThickeningBy`, with the same scalars on `X₀`, and let
`h : X₂ ⟶ X₁` be compatible with the retractions and the sections and carry the square-zero
functions `ι₁ v` to `ι₂ (f v)` for a linear map `f : M₁ ⟶ M₂`. For flat quasi-coherent modules
`ℱ₁`, `ℱ₂` with identifications `ψⱼ : iⱼ^*ℱⱼ ≅ 𝒢` and a morphism `θ : h^*ℱ₁ ⟶ ℱ₂` compatible
with them, the transfer `r₁_*ℱ₁ ⟶ r₂_*ℱ₂` is a morphism of the extensions of
`AlgebraicGeometry.Space.retractionCopowerExtension` over `f`, so their classes in `Ext¹`
correspond under `𝒢 ⊗ f`.

For an endomorphism of a module inducing the identity of `𝒢`, its direct image is compatible
with the projection to `𝒢` and fixes the factored multiplications.

## Main results

* `AlgebraicGeometry.Space.transferMap_comp_retractionProjection`: the transfer `r₁_*ℱ₁ ⟶ r₂_*ℱ₂`
  is compatible with the projections to `𝒢`.
* `AlgebraicGeometry.Space.extensionClass_retractionCopowerExtension_transfer`: the classes in
  `Ext¹` of the two extensions correspond under `𝒢 ⊗ f`.
* `AlgebraicGeometry.Space.retractionPushforward_map_comp_projection` and
  `AlgebraicGeometry.Space.retractionMultiplicationFactor_comp_map`: the direct image of an
  endomorphism inducing the identity of `𝒢` is compatible with the projection and fixes the
  factored multiplications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] Abelian.hasFiniteBiproducts

universe w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `p₁` is epi, `Φ` commutes with the multiplications `mᵢ = pᵢ ≫ fᵢ` and `Φ ≫ p₂ = p₁`, then
`f₁ ≫ Φ = f₂`. -/
private theorem comp_eq_of_epi_of_comm {C : Type*} [Category C] {P₁ P₂ G : C} {p₁ : P₁ ⟶ G}
    {p₂ : P₂ ⟶ G} {f₁ : G ⟶ P₁} {f₂ : G ⟶ P₂} {m₁ : P₁ ⟶ P₁} {m₂ : P₂ ⟶ P₂}
    (hp : Epi p₁) (Φ : P₁ ⟶ P₂) (e₁ : p₁ ≫ f₁ = m₁) (e₂ : m₁ ≫ Φ = Φ ≫ m₂) (e₃ : Φ ≫ p₂ = p₁)
    (e₄ : p₂ ≫ f₂ = m₂) : f₁ ≫ Φ = f₂ :=
  haveI := hp
  (cancel_epi p₁).1 (by rw [← Category.assoc, e₁, e₂, ← e₄, ← Category.assoc, e₃])

section Transfer

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
  {r₁ : X₁ ⟶ X₀} {hrep₁ : yoneda.relativelyRepresentable r₁.hom} {i₁ : X₀ ⟶ X₁}
  {hi₁ : i₁ ≫ r₁ = 𝟙 X₀}
  {r₂ : X₂ ⟶ X₀} {hrep₂ : yoneda.relativelyRepresentable r₂.hom} {i₂ : X₀ ⟶ X₂}
  {hi₂ : i₂ ≫ r₂ = 𝟙 X₀}
  {k : Type u} [Field k] {M₁ M₂ : FGModuleCat.{u} k}
  {ψ₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O)}
  {ψ'₁ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₁.1 X₁.2).O)}
  {ψ'₂ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O)}
  {ι₁ : ↥M₁ →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₁.1 X₁.2).O)}
  {ι₂ : ↥M₂ →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O)}
  (hs₁ : IsSplitThickeningBy B S hS r₁ hrep₁ i₁ hi₁ M₁ ψ₀ ψ'₁ ι₁)
  (hs₂ : IsSplitThickeningBy B S hS r₂ hrep₂ i₂ hi₂ M₂ ψ₀ ψ'₂ ι₂)
  {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
  {G : Modules.{u, u} B S hS X₀.1 X₀.2}
  (ψ₁ : (modulePullback B S hS i₁).obj F₁ ≅ G) (ψ₂ : (modulePullback B S hS i₂).obj F₂ ≅ G)
  (hF₁ : F₁.IsQuasicoherentOnSite) (hF₂ : F₂.IsQuasicoherentOnSite)

/-- **The transfer is compatible with the projections to `𝒢`.** -/
theorem transferMap_comp_retractionProjection (h : X₂ ⟶ X₁) (hr : h ≫ r₁ = r₂)
    (hih : i₂ ≫ h = i₁) (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂)
    (hψ : ψ₁.hom = (modulePullbackTriangle B S hS hih).hom.app F₁ ≫
      (modulePullback B S hS i₂).map θ ≫ ψ₂.hom) :
    transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ ≫
        retractionProjection B S hS r₂ hrep₂ i₂ hi₂ F₂ G ψ₂ =
      retractionProjection B S hS r₁ hrep₁ i₁ hi₁ F₁ G ψ₁ := by
  rw [retractionProjection, retractionProjection, ← Category.assoc,
    transferMap_comp_reductionMap B S hS r₁ hrep₁ r₂ hrep₂ h hr hi₁ hi₂ hih θ, hψ]
  simp only [Category.assoc]

variable [HasExt.{w'} (Modules.{u, u} B S hS X₀.1 X₀.2)]
  (hflat₁ : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ n : Fin (Module.finrank k M₁) → F₁.val.obj (op (retractionChartDiagram B S hS r₁ hrep₁ i₁
      hi₁ U).V),
      ∑ j, (ι₁ (Deformation.ModuleDeformation.stdBasis M₁ j)).1
          (op (retractionChartDiagram B S hS r₁ hrep₁ i₁ hi₁ U).V) • n j = 0 →
        ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS i₁
          (retractionChartDiagram B S hS r₁ hrep₁ i₁ hi₁ U))) •
            (⊤ : Submodule (chartRing B S hS X₁.1 X₁.2
                (retractionChartDiagram B S hS r₁ hrep₁ i₁ hi₁ U).V)
              (F₁.val.obj (op (retractionChartDiagram B S hS r₁ hrep₁ i₁ hi₁ U).V))))
  (hflat₂ : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ n : Fin (Module.finrank k M₂) → F₂.val.obj (op (retractionChartDiagram B S hS r₂ hrep₂ i₂
      hi₂ U).V),
      ∑ j, (ι₂ (Deformation.ModuleDeformation.stdBasis M₂ j)).1
          (op (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).V) • n j = 0 →
        ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS i₂
          (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U))) •
            (⊤ : Submodule (chartRing B S hS X₂.1 X₂.2
                (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).V)
              (F₂.val.obj (op (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).V))))

open Deformation.ModuleDeformation in
include hs₁ hs₂ in
/-- **The extension classes correspond under the map of coefficient spaces.** -/
theorem extensionClass_retractionCopowerExtension_transfer (f : M₁ ⟶ M₂) (h : X₂ ⟶ X₁)
    (hr : h ≫ r₁ = r₂) (hih : i₂ ≫ h = i₁) (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂)
    (hψ : ψ₁.hom = (modulePullbackTriangle B S hS hih).hom.app F₁ ≫
      (modulePullback B S hS i₂).map θ ≫ ψ₂.hom)
    (hι : ∀ (U : SmallEtale B S hS X₀.1) (v : ↥M₁),
      chartDiagramRestrict B S hS h (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U)
        ((ι₁ v).1 (op ((smallBaseChange B S hS r₁ hrep₁).obj U))) =
          (ι₂ (f.hom.hom v)).1 (op ((smallBaseChange B S hS r₂ hrep₂).obj U))) :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    (retractionCopowerExtension B S hS F₁ G ψ₁ hF₁ hs₁ hflat₁).extensionClass.comp
        (Ext.mk₀ ((copowerFunctor G).map f)) (add_zero 1) =
      (retractionCopowerExtension B S hS F₂ G ψ₂ hF₂ hs₂ hflat₂).extensionClass := by
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  have := epi_retractionProjection B S hS F₁ G ψ₁ hF₁ hs₁
  refine CopowerExtension.extensionClass_comp_mk₀_map _ _ f
    (transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ)
    (transferMap_comp_retractionProjection B S hS ψ₁ ψ₂ h hr hih θ hψ) (fun v => ?_)
  rw [retractionCopowerExtension_μ, retractionCopowerExtension_μ]
  exact comp_eq_of_epi_of_comm this _
    (retractionProjection_comp_factor B S hS F₁ G ψ₁ hF₁ hs₁ v)
    (transferMap_comp_globalSmul B S hS r₁ hrep₁ r₂ hrep₂ h hr θ _ _ (fun U => hι U v))
    (transferMap_comp_retractionProjection B S hS ψ₁ ψ₂ h hr hih θ hψ)
    (retractionProjection_comp_factor B S hS F₂ G ψ₂ hF₂ hs₂ (f.hom.hom v))

end Transfer

/-! ### Automorphisms -/

section Automorphism

variable {X₀ X' : AlgebraicSpaces B S hS} {r : X' ⟶ X₀}
  {hrep : yoneda.relativelyRepresentable r.hom} {i : X₀ ⟶ X'} {hi : i ≫ r = 𝟙 X₀}
  {k : Type u} [Field k] {M : FGModuleCat.{u} k}
  {ψ₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O)}
  {ψ' : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  {ι : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  (hs : IsSplitThickeningBy B S hS r hrep i hi M ψ₀ ψ' ι)
  {F : Modules.{u, u} B S hS X'.1 X'.2} {G : Modules.{u, u} B S hS X₀.1 X₀.2}
  (ψ : (modulePullback B S hS i).obj F ≅ G) (hF : F.IsQuasicoherentOnSite)

/-- **The direct image of an endomorphism inducing the identity of `𝒢` is compatible with the
projection.** -/
theorem retractionPushforward_map_comp_projection (a : F ⟶ F)
    (ha : (modulePullback B S hS i).map a ≫ ψ.hom = ψ.hom) :
    (retractionPushforward B S hS r hrep).map a ≫ retractionProjection B S hS r hrep i hi F G ψ =
      retractionProjection B S hS r hrep i hi F G ψ := by
  rw [retractionProjection, ← Category.assoc, reductionMap_naturality, Category.assoc, ha]

include hs in
/-- **The direct image of an endomorphism inducing the identity of `𝒢` fixes the factored
multiplications.** -/
theorem retractionMultiplicationFactor_comp_map (a : F ⟶ F)
    (ha : (modulePullback B S hS i).map a ≫ ψ.hom = ψ.hom) (v : ↥M) :
    retractionMultiplicationFactor B S hS F G ψ hF hs v ≫
        (retractionPushforward B S hS r hrep).map a =
      retractionMultiplicationFactor B S hS F G ψ hF hs v := by
  have := epi_retractionProjection B S hS F G ψ hF hs
  refine comp_eq_of_epi_of_comm this _ (retractionProjection_comp_factor B S hS F G ψ hF hs v) ?_
    (retractionPushforward_map_comp_projection B S hS ψ a ha)
    (retractionProjection_comp_factor B S hS F G ψ hF hs v)
  rw [retractionMultiplication, ← Functor.map_comp, ← Functor.map_comp,
    Stacks.Cohomology.SiteModules.comp_globalSmul]

end Automorphism

end AlgebraicGeometry.Space

end
