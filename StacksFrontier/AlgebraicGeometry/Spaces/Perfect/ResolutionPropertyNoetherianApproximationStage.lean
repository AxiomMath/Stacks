module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardUnitTensorFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubmoduleAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituationStage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeModuleAffineBaseChangePaste
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPushforwardUnitTensorMul
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeModulePushforwardUnitIsoMul
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardUnitTensorMultiplication
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituationIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteModelUnderConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeDescentUnderConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleFullnessUnderConvention
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSupportedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# The second paragraph of the converse of Stacks 0GV1, up to the Noetherian stage

The second paragraph of the proof of the converse of Stacks 0GV1 writes `X = lim X_i` (Stacks
07SU), descends `π : Y ⟶ X` to a finite morphism of finite presentation `π_i : Y_i ⟶ X_i`
(Stacks 07SK, 084Z), descends `ℰ` (Stacks 0D2X) and the map `ℰ ⟶ π_*𝒪_Y` (Stacks 07V7) to a
stage, and then moves the data to later stages `Y_j = Y_i ×_{X_i} X_j`.  This file carries the
bookkeeping of that last move: how the map `ℰ_i ⟶ π_{i,*}𝒪_{Y_i}` and its inverse image to the
limit, read through the affine base change isomorphisms `g^*(π_*𝒪) ≅ π'_*𝒪` of Stacks 07U8,
behave along two stacked cartesian squares, and how the multiplication of the image moves along
a cartesian square.

The main result is
`AlgebraicGeometry.Space.exists_noetherianApproximation_stage_of_isFinitePresentation`: a stage of
a Noetherian approximation carrying a situation of Stacks 0GUY and a map `ℰ_i ⟶ π_{i,*}𝒪_{Y_i}`
from a finite locally free module with image `π_{i,*}ℐ_i`.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModulesNoetherianStage
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-! ### Images -/

/-- Precomposition with an epimorphism does not change the image. -/
private theorem imageSubmodule_epi_comp_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N L : SheafOfModules.{u} R} [Abelian (SheafOfModules.{u} R)]
    (p : M ⟶ N) [Epi p] (g : N ⟶ L) :
    Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (p ≫ g) =
      Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule g := by
  refine le_antisymm (imageSubmodule_le _ fun X m => apply_mem_imageSubmodule g _)
    (imageSubmodule_le g fun X n => ?_)
  refine J.superset_covering ?_ ((isLocallySurjective_of_epi p).imageSieve_mem n)
  rintro V a ⟨m, hm⟩
  refine ⟨m, ?_⟩
  change g.val.app (op V) (p.val.app (op V) m) = L.val.map a.op (g.val.app X n)
  rw [show p.val.app (op V) m = N.val.map a.op n from hm]
  exact PresheafOfModules.naturality_apply g.val a.op n

/-- Equal maps have equal images. -/
private theorem imageSubmodule_eq_of_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} {f g : M ⟶ N} (h : f = g) :
    Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f =
      Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule g := by
  rw [h]

/-- **The image of `π_*ℐ ⟶ π_*𝒪_Y` is `π_*ℐ`**, as a submodule of `π_*𝒪_Y`. -/
private theorem imageSubmodule_map_ι_eq_pushforwardSubmodule {X Y : AlgebraicSpaces B S hS}
    (π : Y ⟶ X) (hπ : yoneda.relativelyRepresentable π.hom)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule) :
    Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
        ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map I.ι) =
      pushforwardSubmodule B S hS π hπ _ I := by
  have hle := imageSubmodule_le ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map I.ι)
    (P := pushforwardSubmodule B S hS π hπ _ I) fun X m => m.2
  refine SheafOfModules.Submodule.ext ?_
  ext X x
  exact ⟨fun hx => hle X hx, fun hx => apply_mem_imageSubmodule
    ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map I.ι) (X := X) ⟨x, hx⟩⟩

/-! ### Squares of affine base change -/

/-- Cancellation of an isomorphism on the left. -/
private theorem iso_inv_comp_eq_of_eq_hom_comp {C : Type*} [Category C] {P Q T : C} (t : P ≅ Q)
    (b : P ⟶ T) (r : Q ⟶ T) (h : b = t.hom ≫ r) : t.inv ≫ b = r := by
  rw [h, Iso.inv_hom_id_assoc]

section Squares

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : AlgebraicSpaces B S hS} {π₀ : Y₀ ⟶ X₀} {π₁ : Y₁ ⟶ X₁}
  {π₂ : Y₂ ⟶ X₂} {g₁ : X₁ ⟶ X₀} {g₁' : Y₁ ⟶ Y₀} {g₂ : X₂ ⟶ X₁} {g₂' : Y₂ ⟶ Y₁}
  {k : X₂ ⟶ X₀} {k' : Y₂ ⟶ Y₀}

/-- **Pasting the affine base change isomorphisms.**  For cartesian squares `(g₁', π₁, π₀, g₁)` and
`(g₂', π₂, π₁, g₂)` with `π₀`, `π₁` affine and an outer cartesian square along `k = g₂ ≫ g₁`, the
isomorphism `k^*(π₀_*𝒪) ≅ π₂_*𝒪` of the outer square, preceded by the comparison
`g₂^* g₁^* ≅ k^*` of Stacks 03LU, is `g₂^*` of the isomorphism of the right square followed by the
isomorphism of the left square: the pasting law
`AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom_paste`. -/
private theorem modulePullbackTriangle_app_inv_comp_unitIso_hom
    (sq₁ : IsPullback g₁' π₁ π₀ g₁) (sq₂ : IsPullback g₂' π₂ π₁ g₂)
    (hk : g₂ ≫ g₁ = k) (sq : IsPullback k' π₂ π₀ k)
    (hπa₀ : IsAffineHom B S hS π₀.hom) (hπa₁ : IsAffineHom B S hS π₁.hom)
    (hπ₀ : yoneda.relativelyRepresentable π₀.hom) (hπ₁ : yoneda.relativelyRepresentable π₁.hom)
    (hπ₂ : yoneda.relativelyRepresentable π₂.hom)
    (hk' : g₂' ≫ g₁' = k') :
    ((modulePullbackTriangle B S hS hk).app
          ((smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj
            (SheafOfModules.unit (structureRingSheaf B S hS Y₀)))).inv ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa₀ hπ₀ hπ₂).hom =
      (modulePullback B S hS g₂).map
          (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₁ hπa₀ hπ₀ hπ₁).hom ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₂ hπa₁ hπ₁ hπ₂).hom :=
  iso_inv_comp_eq_of_eq_hom_comp ((modulePullbackTriangle B S hS hk).app _) _ _
    (modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom_paste sq₁ sq₂ hk hk' sq hπa₀ hπa₁
      hπ₀ hπ₁ hπ₂)

/-- For isomorphisms `te`, `ta` and `bo`, if `te.hom ≫ x ≫ ta.inv = e ≫ fl ≫ bo.inv` and
`ta.inv ≫ bo.hom = b ≫ c`, then `x ≫ b ≫ c = te.inv ≫ e ≫ fl`. -/
private theorem comp_comp_eq_of_conj_eq {C : Type*} [Category C] {P Q R T U W P' : C}
    (te : P ≅ Q) (ta : R ≅ T) (x : Q ⟶ T) (b : T ⟶ U) (c : U ⟶ W) (bo : R ≅ W) (e : P ⟶ P')
    (fl : P' ⟶ W) (hx : te.hom ≫ x ≫ ta.inv = e ≫ fl ≫ bo.inv) (h₁ : ta.inv ≫ bo.hom = b ≫ c) :
    x ≫ b ≫ c = te.inv ≫ e ≫ fl := by
  have hx' : x = te.inv ≫ (e ≫ fl ≫ bo.inv) ≫ ta.hom := by
    rw [← hx]
    simp
  rw [← h₁, hx']
  simp

/-- **A map at the limit restricted from a stage.**  In the situation of
`AlgebraicGeometry.Space.modulePullback_map_comp_unitIso_hom_eq`, let `ψ : g₁^*ℰ₀ ⟶ g₁^*(π₀_*𝒪)`
restrict along `g₂` (`AlgebraicGeometry.Space.restrictPullbackHom`) to `ε ≫ f_L ≫ β⁻¹`, for `β`
the affine base change isomorphism of the outer square.  Then the map `ψ ≫ β₁ : g₁^*ℰ₀ ⟶ π₁_*𝒪`
of the middle stage satisfies `g₂^*(ψ ≫ β₁) ≫ β₂ = ε' ≫ f_L` for the isomorphism
`g₂^*g₁^*ℰ₀ ≅ k^*ℰ₀ ≅ ℰ_L`. -/
private theorem restrictPullbackHom_comp_unitIso_hom_eq
    (sq₁ : IsPullback g₁' π₁ π₀ g₁) (sq₂ : IsPullback g₂' π₂ π₁ g₂)
    (hk : g₂ ≫ g₁ = k) (sq : IsPullback k' π₂ π₀ k)
    (hπa₀ : IsAffineHom B S hS π₀.hom) (hπa₁ : IsAffineHom B S hS π₁.hom)
    (hπ₀ : yoneda.relativelyRepresentable π₀.hom) (hπ₁ : yoneda.relativelyRepresentable π₁.hom)
    (hπ₂ : yoneda.relativelyRepresentable π₂.hom)
    (hk' : g₂' ≫ g₁' = k')
    {E₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    {EL : Modules.{u, u} B S hS X₂.1 X₂.2} (ε : (modulePullback B S hS k).obj E₀ ≅ EL)
    (fL : EL ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y₂)))
    (ψ : (modulePullback B S hS g₁).obj E₀ ⟶ (modulePullback B S hS g₁).obj
      ((smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y₀))))
    (hψ : restrictPullbackHom g₂ hk ψ = ε.hom ≫ fL ≫
      (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa₀ hπ₀ hπ₂).inv) :
    (modulePullback B S hS g₂).map (ψ ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₁ hπa₀ hπ₀ hπ₁).hom) ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₂ hπa₁ hπ₁ hπ₂).hom =
      ((modulePullbackTriangle B S hS hk).app E₀).inv ≫ ε.hom ≫ fL := by
  have h₁ := modulePullbackTriangle_app_inv_comp_unitIso_hom sq₁ sq₂ hk sq hπa₀ hπa₁ hπ₀ hπ₁ hπ₂
    hk'
  have hψ' : ((modulePullbackTriangle B S hS hk).app E₀).hom ≫
      (modulePullback B S hS g₂).map ψ ≫
      ((modulePullbackTriangle B S hS hk).app
          ((smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj
            (SheafOfModules.unit (structureRingSheaf B S hS Y₀)))).inv =
      ε.hom ≫ fL ≫ (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa₀ hπ₀ hπ₂).inv :=
    hψ
  exact (congrArg (fun z => z ≫
      (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₂ hπa₁ hπ₁ hπ₂).hom)
      ((modulePullback B S hS g₂).map_comp _ _)).trans ((Category.assoc _ _ _).trans
        (comp_comp_eq_of_conj_eq _ _ _ _ _ _ _ _ hψ' h₁))

/-- **A map at a stage, moved to a later stage.**  Let `f₀ : ℰ₀ ⟶ π₀_*𝒪` at the bottom right of
two stacked cartesian squares be such that `k^*f₀`, read in `π₂_*𝒪` through the affine base change
isomorphism of the outer square, is `ε ≫ f_L` for an isomorphism `ε : k^*ℰ₀ ≅ ℰ_L`.  Then the map
`f₁ = g₁^*f₀ ≫ β₁ : g₁^*ℰ₀ ⟶ π₁_*𝒪` of the middle stage has the same property along `g₂`, with the
isomorphism `g₂^*g₁^*ℰ₀ ≅ k^*ℰ₀ ≅ ℰ_L`. -/
private theorem modulePullback_map_comp_unitIso_hom_eq
    (sq₁ : IsPullback g₁' π₁ π₀ g₁) (sq₂ : IsPullback g₂' π₂ π₁ g₂)
    (hk : g₂ ≫ g₁ = k) (sq : IsPullback k' π₂ π₀ k)
    (hπa₀ : IsAffineHom B S hS π₀.hom) (hπa₁ : IsAffineHom B S hS π₁.hom)
    (hπ₀ : yoneda.relativelyRepresentable π₀.hom) (hπ₁ : yoneda.relativelyRepresentable π₁.hom)
    (hπ₂ : yoneda.relativelyRepresentable π₂.hom)
    (hk' : g₂' ≫ g₁' = k')
    {E₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    (f₀ : E₀ ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y₀)))
    {EL : Modules.{u, u} B S hS X₂.1 X₂.2} (ε : (modulePullback B S hS k).obj E₀ ≅ EL)
    (fL : EL ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y₂)))
    (hf : (modulePullback B S hS k).map f₀ ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa₀ hπ₀ hπ₂).hom =
      ε.hom ≫ fL) :
    (modulePullback B S hS g₂).map ((modulePullback B S hS g₁).map f₀ ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₁ hπa₀ hπ₀ hπ₁).hom) ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₂ hπa₁ hπ₁ hπ₂).hom =
      ((modulePullbackTriangle B S hS hk).app E₀).inv ≫ ε.hom ≫ fL := by
  have h₂ : (modulePullback B S hS g₂).map ((modulePullback B S hS g₁).map f₀) ≫
      ((modulePullbackTriangle B S hS hk).app
          ((smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj
            (SheafOfModules.unit (structureRingSheaf B S hS Y₀)))).inv =
      ((modulePullbackTriangle B S hS hk).app E₀).inv ≫ (modulePullback B S hS k).map f₀ :=
    (modulePullbackTriangle B S hS hk).inv.naturality f₀
  refine restrictPullbackHom_comp_unitIso_hom_eq sq₁ sq₂ hk sq hπa₀ hπa₁ hπ₀ hπ₁ hπ₂ hk' ε fL _ ?_
  change _ ≫ _ ≫ ((modulePullbackTriangle B S hS hk).app _).inv = _
  rw [h₂, ← Iso.app_hom, Iso.hom_inv_id_assoc]
  exact ((Iso.eq_comp_inv _).2 hf).trans (Category.assoc _ _ _)

/-- **The vanishing of `ℰ ⊗ π_*𝒪 ⟶ π_*𝒪 ⟶ coker f` moves along a cartesian square**, read
through the affine base change isomorphism `β : g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}`: Stacks 03EL for the
multiplication, with `β` multiplicative
(`AlgebraicGeometry.Space.modulePullback_map_pushforwardUnitTensorMulHom_comp_unitIso_hom`). -/
private theorem modulePullback_map_mul_comp_cokernelπ_eq_zero_iff
    {X Y X' Y' : AlgebraicSpaces B S hS} {π : Y ⟶ X} {g : X' ⟶ X} {π' : Y' ⟶ X'}
    {g' : Y' ⟶ Y} (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) {E : Modules.{u, u} B S hS X.1 X.2}
    (f : E ⟶ chartBaseChangeStructureModule B S hS π hπ) :
    (modulePullback B S hS g).map (pushforwardUnitTensorMulHom f ≫ cokernel.π f) = 0 ↔
      pushforwardUnitTensorMulHom ((modulePullback B S hS g).map f ≫
          (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom) ≫
        cokernel.π ((modulePullback B S hS g).map f ≫
          (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom) = 0 :=
  modulePullback_map_pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_iff g
    (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ')
    (modulePullback_map_pushforwardUnitTensorMulHom_comp_unitIso_hom sq hπa hπ hπ') f

/-- **A map onto the direct image of an ideal has image closed under multiplication**, so
`ℰ ⊗ π_*𝒪 ⟶ π_*𝒪 ⟶ coker f` vanishes. -/
private theorem pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_of_eq
    {X Y : AlgebraicSpaces B S hS} {π : Y ⟶ X} {hπ : yoneda.relativelyRepresentable π.hom}
    {E : Modules.{u, u} B S hS X.1 X.2} (f : E ⟶ chartBaseChangeStructureModule B S hS π hπ)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (h : pushforwardSubmodule B S hS π hπ _ I =
      Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f) :
    pushforwardUnitTensorMulHom f ≫ cokernel.π f = 0 := by
  refine pushforwardUnitTensorMulHom_comp_eq_zero_of_mul_mem f fun Q b m hm => ?_
  rw [← h] at hm ⊢
  exact (I.obj _).smul_mem b hm

/-- Transport of the vanishing of `ℰ ⊗ π_*𝒪 ⟶ π_*𝒪 ⟶ coker f` along an equality of maps. -/
private theorem pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_of_eq_of_eq
    {X Y : AlgebraicSpaces B S hS} {π : Y ⟶ X} {hπ : yoneda.relativelyRepresentable π.hom}
    {E : Modules.{u, u} B S hS X.1 X.2} {f f' : E ⟶ chartBaseChangeStructureModule B S hS π hπ}
    (h : f = f') (h' : pushforwardUnitTensorMulHom f' ≫ cokernel.π f' = 0) :
    pushforwardUnitTensorMulHom f ≫ cokernel.π f = 0 :=
  h ▸ h'

end Squares

/-! ### Base change of a finite morphism to a later stage -/

/-- **A finite morphism of finite presentation at a stage, moved to a later stage, with the
square over the limit.**  Let `π₀ : Y₀ ⟶ X₀` be finite and of finite presentation, `g : X₁ ⟶ X₀`,
and let `Y_L ⟶ Y₀` exhibit `π_L : Y_L ⟶ X_L` as the base change of `π₀` along `b = a ≫ g`.  Then
`Y₁ = Y₀ ×_{X₀} X₁` has `π₁` finite and of finite presentation, and the square of `Y_L ⟶ Y₁` over
`a` is cartesian. -/
private theorem exists_isPullback_stage {X₀ X₁ XL Y₀ YL : AlgebraicSpaces B S hS}
    (π₀ : Y₀ ⟶ X₀) (hfin : IsFinite B S hS π₀.hom) (hfp : IsFinitePresentation B S hS π₀.hom)
    (g : X₁ ⟶ X₀) (a : XL ⟶ X₁) {b : XL ⟶ X₀} (hb : a ≫ g = b) (πL : YL ⟶ XL) (gL : YL ⟶ Y₀)
    (sqo : IsPullback gL πL π₀ b) :
    ∃ (Y₁ : AlgebraicSpaces B S hS) (π₁ : Y₁ ⟶ X₁) (g' : Y₁ ⟶ Y₀) (g₁ : YL ⟶ Y₁),
      IsFinite B S hS π₁.hom ∧ IsFinitePresentation B S hS π₁.hom ∧ IsPullback g' π₁ π₀ g ∧
        IsPullback g₁ πL π₁ a ∧ g₁ ≫ g' = gL := by
  let Y₁ : AlgebraicSpaces B S hS :=
    ⟨pullback π₀.hom g.hom, isAlgebraicSpace_pullback B S hS π₀.hom g.hom Y₀.2 X₁.2 X₀.2⟩
  have sq₀ : IsPullback (pullback.fst π₀.hom g.hom) (pullback.snd π₀.hom g.hom) π₀.hom g.hom :=
    IsPullback.of_hasPullback _ _
  have sq : IsPullback (ObjectProperty.homMk (pullback.fst π₀.hom g.hom) : Y₁ ⟶ Y₀)
      (ObjectProperty.homMk (pullback.snd π₀.hom g.hom) : Y₁ ⟶ X₁) π₀ g :=
    isPullback_of_isPullback_hom B S hS sq₀
  have hw : gL.hom ≫ π₀.hom = πL.hom ≫ a.hom ≫ g.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      ← ObjectProperty.FullSubcategory.comp_hom, sqo.w, hb]
  let g₁ : YL ⟶ Y₁ := ObjectProperty.homMk (pullback.lift gL.hom (πL.hom ≫ a.hom) hw)
  have hg₁ : g₁ ≫ (ObjectProperty.homMk (pullback.fst π₀.hom g.hom) : Y₁ ⟶ Y₀) = gL :=
    ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  exact ⟨Y₁, ObjectProperty.homMk (pullback.snd π₀.hom g.hom),
    ObjectProperty.homMk (pullback.fst π₀.hom g.hom), g₁,
    isFinite_of_isPullback B S hS sq₀ hfin,
    isFinitePresentation_pullback_snd B S hS π₀.hom g.hom Y₀.2 X₀.2 X₁.2 hfp, sq,
    IsPullback.of_right (by rwa [hg₁, hb]) (ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _))
      sq, hg₁⟩

/-- The projections `lim D ⟶ D_i` and `lim D ⟶ D_j` are compatible with `D_i ⟶ D_j`. -/
private theorem homMk_limit_π_comp_homMk_map {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDlim : IsAlgebraicSpace B S hS (limit D)) {i j : I} (e : i ⟶ j) :
    (ObjectProperty.homMk (limit.π D i) :
        (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj i, hD i⟩) ≫
      (ObjectProperty.homMk (D.map e) :
        (⟨D.obj i, hD i⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j, hD j⟩) =
      ObjectProperty.homMk (limit.π D j) :=
  ObjectProperty.hom_ext _ (limit.w D e)

/-! ### From a stage carrying the map to a stage carrying the closed subspace -/

section Step

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 07V7 and the ideal of a later stage.**  Let `X = lim X_i` with Noetherian stages under
the convention, `π_L : Y_L ⟶ X` finite, `ℐ_L ⊆ 𝒪_{Y_L}` quasi-coherent and `f_L : ℰ_L ⟶ π_{L*}𝒪`
with image `π_{L*}ℐ_L`.  Let `π_k : Y_k ⟶ X_k` be finite of finite presentation with
`Y_L = Y_k ×_{X_k} X`, and `ℰ_k` finite locally free with `ℰ_L ≅ (X ⟶ X_k)^*ℰ_k`.

By fullness (`exists_stage_restrictPullbackHom_eq_of_siteContainsBaseChangeLimits`) `f_L` comes
from a map `f_j : ℰ_j ⟶ π_{j*}𝒪` at a stage `j`, read through the affine base change isomorphisms
of Stacks 07U8.  The vanishing of `ℰ_j ⊗ π_{j*}𝒪 ⟶ π_{j*}𝒪 ⟶ coker f_j` over the
limit descends to a stage `j'` by faithfulness
(`AlgebraicGeometry.Space.exists_stage_modulePullback_map_eq_of_siteContainsBaseChangeLimits`; the
tensor product is of finite presentation since `X_j` is Noetherian), so the image of the map
`f_{j'}` at `Y_{j'} = Y_j ×_{X_j} X_{j'}` is `π_{j'*}ℐ_{j'}` for a closed subspace
`Z_{j'} = V(ℐ_{j'})` with finitely presented inclusion, and `ℐ_L` is the ideal of the inverse
image of `Z_{j'}`: the pullback of `ℐ_{j'}` generates `ℐ_L`. -/
private theorem exists_stage_closedSubspace_of_stage
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hN : ∀ i, HasEtaleLocalProperty B S hS (D.obj i)
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hDlim : IsAlgebraicSpace B S hS (limit D)) (hqcL : IsQuasiCompactSpace B S hS (limit D))
    {YL : AlgebraicSpaces B S hS}
    (πL : YL ⟶ (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS)) (hπLfin : IsFinite B S hS πL.hom)
    (hrepL : yoneda.relativelyRepresentable πL.hom)
    (IL : (SheafOfModules.unit (structureRingSheaf B S hS YL)).Submodule)
    (hIL : IL.toSheafOfModules.IsQuasicoherentOnSite)
    {EL : Modules.{u, u} B S hS (limit D) hDlim}
    (fL : EL ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS πL hrepL).obj
      (SheafOfModules.unit (structureRingSheaf B S hS YL)))
    (hfL : Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule fL =
      pushforwardSubmodule B S hS πL hrepL _ IL)
    {k : I} {Yk : AlgebraicSpaces B S hS}
    (πk : Yk ⟶ (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS)) (hπkfin : IsFinite B S hS πk.hom)
    (hπkfp : IsFinitePresentation B S hS πk.hom) (gk : YL ⟶ Yk)
    (sqk : IsPullback gk πL πk (ObjectProperty.homMk (limit.π D k) :
      (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj k, hD k⟩))
    {Ek : Modules.{u, u} B S hS (D.obj k) (hD k)}
    (hEk : SheafOfModules.IsFiniteLocallyFreeOnSite Ek)
    (εk : (modulePullback B S hS (ObjectProperty.homMk (limit.π D k) :
      (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj k, hD k⟩)).obj Ek ≅ EL) :
    ∃ (j' : I) (_ : j' ⟶ k) (Yj' : AlgebraicSpaces B S hS)
      (πj' : Yj' ⟶ (⟨D.obj j', hD j'⟩ : AlgebraicSpaces B S hS)) (gj' : YL ⟶ Yj')
      (hπj'fin : IsFinite B S hS πj'.hom), IsFinitePresentation B S hS πj'.hom ∧
      IsPullback gj' πL πj' (ObjectProperty.homMk (limit.π D j') :
        (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j', hD j'⟩) ∧
      ∃ Zj' : ClosedSubspaces B S hS Yj'.1, IsFinitePresentation B S hS Zj'.1.ι ∧
        IL = definingIdealSheaf B S hS YL (preimageSubspace B S hS gj' Zj') ∧
        ∃ (Ej' : Modules.{u, u} B S hS (D.obj j') (hD j'))
          (_ : SheafOfModules.IsFiniteLocallyFreeOnSite Ej')
          (fj' : Ej' ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS πj'
            (relativelyRepresentable_hom_of_isFinite B S hS πj' hπj'fin)).obj
              (SheafOfModules.unit (structureRingSheaf B S hS Yj'))),
          Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule fj' =
            pushforwardSubmodule B S hS πj'
              (relativelyRepresentable_hom_of_isFinite B S hS πj' hπj'fin) _
              (definingIdealSheaf B S hS Yj' Zj') := by
  have hrepk := relativelyRepresentable_hom_of_isFinite B S hS πk hπkfin
  have hπkaff := hπkfin.isAffineHom
  have hπLaff := hπLfin.isAffineHom
  -- Stacks 07V7, fullness: `ℰ ⟶ π_*𝒪` comes from a stage `j ⟶ k`
  obtain ⟨j, ejk, ψ, hψ⟩ := exists_stage_restrictPullbackHom_eq_of_siteContainsBaseChangeLimits
    B S hS D hconv hD hAff hZ hQc hQs (k := k) (E := Ek)
    (G := (smallBaseChangeModulePushforward.{u, u} B S hS πk hrepk).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Yk)))
    (SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hEk)
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS πk hπkfin _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (εk.hom ≫ fL ≫
      (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqk hπkaff hrepk hrepL).inv)
  -- the stage `j`: `Y_j = Y_k ×_{X_k} X_j`, and `f_j = ψ ≫ β_{jk}`
  have hjk := homMk_limit_π_comp_homMk_map D hD hDlim ejk
  obtain ⟨Yj, πj, gjk, gj, hπjfin, hπjfp, sqjk, sqj, hgj⟩ :=
    exists_isPullback_stage πk hπkfin hπkfp _ _ hjk πL gk sqk
  have hrepj := relativelyRepresentable_hom_of_isFinite B S hS πj hπjfin
  have hπjaff := hπjfin.isAffineHom
  have hIdj := restrictPullbackHom_comp_unitIso_hom_eq sqjk sqj hjk sqk hπkaff hπjaff hrepk hrepj
    hrepL hgj εk fL ψ hψ
  -- `ℰ_j ⊗ π_{j*}𝒪 ⟶ π_{j*}𝒪 ⟶ coker f_j` vanishes over the limit
  have : (modulePullback B S hS (ObjectProperty.homMk (limit.π D j) :
      (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j, hD j⟩)).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS _⟩⟩
  have hL : (modulePullback B S hS (ObjectProperty.homMk (limit.π D j) :
        (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j, hD j⟩)).map
      (pushforwardUnitTensorMulHom
          (ψ ≫
            (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqjk hπkaff hrepk hrepj).hom) ≫
        cokernel.π
          (ψ ≫
            (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqjk hπkaff hrepk hrepj).hom)) =
      0 := by
    refine (modulePullback_map_mul_comp_cokernelπ_eq_zero_iff sqj hπjaff hrepj hrepL _).2 ?_
    refine pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_of_eq_of_eq hIdj ?_
    refine pushforwardUnitTensorMulHom_comp_cokernelπ_eq_zero_of_eq _ IL ?_
    refine hfL.symm.trans ?_
    exact ((Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp
      ((modulePullbackTriangle B S hS hjk).app Ek).symm _).trans
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp εk fL)).symm
  -- Stacks 07V7, faithfulness: the vanishing descends to a stage `j' ⟶ j`
  have hEjqc : ((modulePullback B S hS (ObjectProperty.homMk (D.map ejk) :
      (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj k, hD k⟩)).obj
        Ek).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite (X := ⟨D.obj k, hD k⟩) Ek hEk)
  have hEj := isFiniteLocallyFreeOnSite_modulePullback B S hS
    (ObjectProperty.homMk (D.map ejk) :
      (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj k, hD k⟩) Ek
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite (X := ⟨D.obj k, hD k⟩) Ek hEk) hEk
  obtain ⟨j', ej'j, hj'⟩ := exists_stage_modulePullback_map_eq_of_siteContainsBaseChangeLimits
    B S hS D hconv hD hAff hQc (k := j)
    (isFinitePresentationOnSite_sheafTensor_chartBaseChangeStructureModule
      B S hS (X := ⟨D.obj j, hD j⟩) πj hπjfin hrepj (hN j) _ hEj)
    (@isQuasicoherentOnSite_cokernel_unconditional B S hS _ _ _ _ hEjqc
      (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS πj hπjfin
        (SheafOfModules.unit (structureRingSheaf B S hS Yj))
        (SheafOfModules.isQuasicoherentOnSite_unit _))
      (ψ ≫ (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqjk hπkaff hrepk hrepj).hom))
    _ 0 (hL.trans (Functor.map_zero _ _ _).symm)
  -- the stage `j'`: `Y_{j'} = Y_j ×_{X_j} X_{j'}` and `f_{j'} = (D.map e')^*f_j ≫ β_{j'j}`
  have hj'j := homMk_limit_π_comp_homMk_map D hD hDlim ej'j
  obtain ⟨Yj', πj', gYj'j, gj', hπj'fin, hπj'fp, sqj'j, sqj', hgj'⟩ :=
    exists_isPullback_stage πj hπjfin hπjfp _ _ hj'j πL gj sqj
  have hrepj' := relativelyRepresentable_hom_of_isFinite B S hS πj' hπj'fin
  have hπj'aff := hπj'fin.isAffineHom
  have : (modulePullback B S hS (ObjectProperty.homMk (D.map ej'j) :
      (⟨D.obj j', hD j'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j, hD j⟩)).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS _⟩⟩
  have hmulj' := (modulePullback_map_mul_comp_cokernelπ_eq_zero_iff sqj'j hπjaff hrepj hrepj'
    (ψ ≫ (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqjk hπkaff hrepk hrepj).hom)).1
      (hj'.trans (Functor.map_zero _ _ _))
  have hIdj' := modulePullback_map_comp_unitIso_hom_eq sqj'j sqj' hj'j sqj hπjaff hπj'aff hrepj
    hrepj' hrepL hgj'
    (ψ ≫ (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqjk hπkaff hrepk hrepj).hom)
    ((modulePullbackTriangle B S hS hjk).app Ek).symm (εk.hom ≫ fL) hIdj
  -- the ideal `ℐ_{j'}` of the stage: `π_{j'*}ℐ_{j'}` is the image of `f_{j'}`
  have hEj' := isFiniteLocallyFreeOnSite_modulePullback B S hS
    (ObjectProperty.homMk (D.map ej'j) :
      (⟨D.obj j', hD j'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j, hD j⟩) _ hEjqc hEj
  have hEj'qc := isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite (X := ⟨D.obj j', hD j'⟩) _
    hEj'
  obtain ⟨Ij', hIj'qc, hIj'ft, hIj'⟩ := exists_ideal_pushforwardSubmodule_eq_imageSubmodule _
    hπj'aff hmulj' (isQuasicoherentOnSite_imageSubmodule _ hEj'qc
      (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS πj' hπj'fin
        (SheafOfModules.unit (structureRingSheaf B S hS Yj'))
        (SheafOfModules.isQuasicoherentOnSite_unit _)))
  obtain ⟨Zj', hZj', -, hZj'fp⟩ :=
    exists_closedSubspace_isFinitePresentation_ι_of_isFiniteTypeQuasicoherentIdeal B S hS Yj' Ij'
      ⟨hIj'qc, hIj'ft (isFiniteTypeOnSite_imageSubmodule _
        (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _
          (SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hEj')))⟩
  have hfj' : Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
      ((modulePullback B S hS (ObjectProperty.homMk (D.map ej'j) :
          (⟨D.obj j', hD j'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj j, hD j⟩)).map
        (ψ ≫ (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqjk hπkaff hrepk hrepj).hom) ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sqj'j hπjaff hrepj hrepj').hom) =
      pushforwardSubmodule B S hS πj' hrepj' (SheafOfModules.unit (structureRingSheaf B S hS Yj'))
        (definingIdealSheaf B S hS Yj' Zj') :=
    hIj'.symm.trans (congrArg (pushforwardSubmodule B S hS πj' hrepj' _) hZj'.symm)
  -- the pullback of `ℐ_{j'}` generates `ℐ_L`
  have himL := imageSubmodule_modulePullback_map_comp_unitIso_hom sqj' hπj'aff hπLaff hrepj' hrepL
    Zj' _ hfj'
  have hA : pushforwardSubmodule B S hS πL hrepL _ IL =
      pushforwardSubmodule B S hS πL hrepL _
        (definingIdealSheaf B S hS YL (preimageSubspace B S hS gj' Zj')) := by
    refine hfL.symm.trans (Eq.trans ?_ himL)
    refine Eq.trans ?_ (imageSubmodule_eq_of_eq hIdj').symm
    exact (((Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp
      ((modulePullbackTriangle B S hS hj'j).app _).symm _).trans
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp
        ((modulePullbackTriangle B S hS hjk).app Ek).symm _)).trans
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp εk fL)).symm
  obtain ⟨ZL, hZL⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS YL IL hIL
  have hZLeq := eq_of_pushforwardSubmodule_definingIdealSheaf_eq hqcL πL hπLaff hrepL ZL
    (preimageSubspace B S hS gj' Zj')
    ((congrArg (pushforwardSubmodule B S hS πL hrepL _) hZL).trans hA)
  exact ⟨j', ej'j ≫ ejk, Yj', πj', gj', hπj'fin, hπj'fp, sqj', Zj', hZj'fp,
    hZL.symm.trans (congrArg (definingIdealSheaf B S hS YL) hZLeq), _, hEj', _, hfj'⟩

end Step

/-! ### The second paragraph -/

section Main

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The second paragraph of the proof of the converse of Stacks 0GV1, up to the Noetherian
stage.**  Let `X` be a quasi-compact and quasi-separated algebraic space over `Spec ℤ` with a
situation of Stacks 0GUY whose finite morphism `π : Y ⟶ X` is of finite presentation, and let a
finite locally free `𝒪_X`-module surject onto `π_*ℐ`.  Then `X` has a Noetherian approximation
`X = lim X_i` (Stacks 07SU) under the convention of Section 70.2, and some stage `X_i` carries a
situation of Stacks 0GUY together with a map `ℰ_i ⟶ π_{i,*}𝒪_{Y_i}` from a finite locally free
`𝒪_{X_i}`-module whose image is `π_{i,*}ℐ_i`.

The finite morphism comes from a stage by Stacks 07SK and 084Z, the module by Stacks 0D2X, the
map `ℰ ⟶ π_*𝒪_Y` by Stacks 07V7 (fullness), read through the affine base change isomorphisms of
Stacks 07U8; the vanishing of `ℰ_i ⊗ π_{i,*}𝒪 ⟶ π_{i,*}𝒪 ⟶ coker` descends by Stacks 07V7
(faithfulness), so the image is `π_{i,*}ℐ_i` for an ideal whose inverse image generates `ℐ`
(`AlgebraicGeometry.Space.imageSubmodule_modulePullback_map_comp_unitIso_hom`); the open part
`V_i` at a later stage is supplied by
`exists_resolutionPropertyDescentSituation_stage_of_siteContainsBaseChangeLimits`. Stacks 0GV0 at
that stage and Stacks 0GUU along the projection `X ⟶ X_i` then finish the proof
(`hasResolutionProperty_of_exists_epi_idealDirectImage_of_isFinitePresentation`). -/
theorem exists_noetherianApproximation_stage_of_isFinitePresentation
    {X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    {hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X.1}
    {hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X.1}
    (sit : ResolutionPropertyDescentSituation B (⊤_ Scheme.{u}) hZ hZ X hqc hqs)
    (hfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ sit.π)
    (h : ∃ (E : Modules.{u, u} B (⊤_ Scheme.{u}) hZ X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ sit.idealDirectImage B (⊤_ Scheme.{u}) hZ hZ), Epi p) :
    ∃ (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X.1),
      letI := A.preorder; letI := A.nonempty; letI := A.isDirected
      ∃ (_ : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram) (i : (A.I)ᵒᵖ)
      (sit' : ResolutionPropertyDescentSituation B (⊤_ Scheme.{u}) hZ hZ
        ⟨A.diagram.obj i, A.isAlgebraicSpace i⟩ (A.isNoetherian i).1 (A.isNoetherian i).2.1)
      (E' : Modules.{u, u} B (⊤_ Scheme.{u}) hZ (A.diagram.obj i) (A.isAlgebraicSpace i))
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E')
      (f : E' ⟶ (smallBaseChangeModulePushforward.{u, u} B (⊤_ Scheme.{u}) hZ sit'.πHom
        (relativelyRepresentable_hom_of_isFinite B (⊤_ Scheme.{u}) hZ sit'.πHom
          sit'.isFinite_π)).obj (SheafOfModules.unit (structureRingSheaf B _ hZ sit'.Y))),
      pushforwardSubmodule B (⊤_ Scheme.{u}) hZ sit'.πHom
        (relativelyRepresentable_hom_of_isFinite B (⊤_ Scheme.{u}) hZ sit'.πHom sit'.isFinite_π) _
          sit'.I = Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f := by
  obtain ⟨E, hE, p, hp⟩ := h
  have hsurj := (presheafSurjective_iff_isSurjective_yoneda B _ hZ X.1 X.2 sit.V sit.φ).2
    sit.isSurjective_φ
  obtain ⟨A, hconv⟩ := hasConventionalNoetherianApproximation_of_etaleAtlas X.2 hqc hqs sit.V
    sit.φ hsurj sit.isEtale_φ
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  have := A.isCofiltered_op
  -- the system `X = lim X_i` and its limit as an algebraic space
  have hD : ∀ i, IsAlgebraicSpace B _ hZ (A.diagram.obj i) := A.isAlgebraicSpace
  have hAff : ∀ {i j : A.Iᵒᵖ} (f : i ⟶ j), IsAffineHom B _ hZ (A.diagram.map f) :=
    fun f => A.isAffineHom_map f
  have hQc : ∀ i, IsQuasiCompactSpace B _ hZ (A.diagram.obj i) := fun i => (A.isNoetherian i).1
  have hQs : ∀ i, IsAbsolutelyQuasiSeparated B _ hZ hZ (A.diagram.obj i) :=
    fun i => (A.isNoetherian i).2.1
  have hDlim := isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B _ hZ A.diagram hconv hD
    hAff hQc
  let e₀ : X.1 ≅ limit A.diagram := A.isLimit.conePointUniqueUpToIso (limit.isLimit A.diagram)
  let e : X ≅ (⟨limit A.diagram, hDlim⟩ : AlgebraicSpaces B _ hZ) := ObjectProperty.isoMk _ e₀
  have hqcL : IsQuasiCompactSpace B _ hZ (limit A.diagram) :=
    IsQuasiCompactSpace.of_iso B _ hZ hqc e₀
  have hqsL : IsAbsolutelyQuasiSeparated B _ hZ hZ (limit A.diagram) :=
    isAbsolutelyQuasiSeparated_of_iso B _ hZ hZ hDlim e₀.symm hqs
  -- the situation of Stacks 0GUY over the limit
  let sitL := sit.ofIso e hqcL hqsL
  have hfpL : IsFinitePresentation B _ hZ sitL.π := sit.isFinitePresentation_π_ofIso e hqcL hqsL hfp
  obtain ⟨EL, hEL, pL, hpL⟩ := sit.exists_epi_idealDirectImage_ofIso e hqcL hqsL ⟨E, hE, p, hp⟩
  -- Stacks 07SK and 084Z: `π` is the base change of a finite morphism of finite presentation
  obtain ⟨i₀, T₀, hT₀alg, hT₀fin, hT₀fp, ⟨eT⟩⟩ :=
    exists_isFinite_model_of_siteContainsBaseChangeLimits B _ hZ hZ A.diagram hD hAff hQc hQs hconv
      hDlim (Over.mk sitL.π) sit.Y.2 sitL.isFinite_π hfpL
  -- Stacks 0D2X: `ℰ` is the inverse image of a finite locally free module on a stage
  obtain ⟨i₁, E₁', hE₁', ⟨εE'⟩⟩ :=
    exists_isFiniteLocallyFreeOnSite_stage_of_siteContainsBaseChangeLimits B _ hZ A.diagram hconv
      hD hAff hZ hQc hQs EL hEL
  let E₁ : Modules.{u, u} B _ hZ (A.diagram.obj i₁) (hD i₁) := E₁'
  have hE₁ : SheafOfModules.IsFiniteLocallyFreeOnSite E₁ := hE₁'
  let εE : EL ≅ (modulePullback B _ hZ (ObjectProperty.homMk (limit.π A.diagram i₁) :
      (⟨limit A.diagram, hDlim⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj i₁, hD _⟩)).obj E₁ :=
    εE'
  -- a common stage `k`
  obtain ⟨m, hm₀, hm₁⟩ := directed_of (· ≤ ·) i₀ i₁.unop
  -- the cartesian square of `π` over `lim ⟶ X_{i₀}`
  have hsq₀ : IsPullback (eT.hom.left ≫ pullback.fst T₀.hom (limit.π A.diagram (op i₀))) sitL.π
      T₀.hom (limit.π A.diagram (op i₀)) := by
    refine (IsPullback.of_hasPullback T₀.hom (limit.π A.diagram (op i₀))).of_iso
      ((Over.forget _).mapIso eT).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · have := Over.w eT.inv
      simp only [Over.mk_hom, Over.pullback_obj_hom] at this
      simp [this]
    · simp
    · simp
  have hsq₀' := isPullback_of_isPullback_hom B _ hZ (F := ⟨T₀.left, hT₀alg⟩)
    (H := ⟨A.diagram.obj (op i₀), hD _⟩) (G := ⟨limit A.diagram, hDlim⟩) (P := sit.Y)
    (f := ObjectProperty.homMk T₀.hom) (g := ObjectProperty.homMk (limit.π A.diagram (op i₀)))
    (fst := ObjectProperty.homMk (eT.hom.left ≫ pullback.fst T₀.hom (limit.π A.diagram (op i₀))))
    (snd := sitL.πHom) hsq₀
  obtain ⟨Yk, πk, -, gk, hπkfin, hπkfp, -, sqk, -⟩ := exists_isPullback_stage
    (ObjectProperty.homMk T₀.hom : (⟨T₀.left, hT₀alg⟩ : AlgebraicSpaces B _ hZ) ⟶
      ⟨A.diagram.obj (op i₀), hD _⟩) hT₀fin hT₀fp
    (ObjectProperty.homMk (A.diagram.map (homOfLE hm₀).op) :
      (⟨A.diagram.obj (op m), hD _⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj (op i₀), hD _⟩)
    (ObjectProperty.homMk (limit.π A.diagram (op m)) :
      (⟨limit A.diagram, hDlim⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj (op m), hD _⟩)
    (ObjectProperty.hom_ext _ (limit.w A.diagram (homOfLE hm₀).op)) sitL.πHom _ hsq₀'
  have hrepk := relativelyRepresentable_hom_of_isFinite B _ hZ πk hπkfin
  have hπkaff := hπkfin.isAffineHom
  have hrepL := relativelyRepresentable_hom_of_isFinite B _ hZ sitL.πHom sitL.isFinite_π
  -- `ℰ` from the stage `k`
  have hk₁ := homMk_limit_π_comp_homMk_map A.diagram hD hDlim (homOfLE hm₁).op
  let Ek := (modulePullback B _ hZ (ObjectProperty.homMk (A.diagram.map (homOfLE hm₁).op) :
    (⟨A.diagram.obj (op m), hD _⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj i₁, hD _⟩)).obj E₁
  have hEk : SheafOfModules.IsFiniteLocallyFreeOnSite Ek :=
    isFiniteLocallyFreeOnSite_modulePullback B _ hZ
      (ObjectProperty.homMk (A.diagram.map (homOfLE hm₁).op) :
        (⟨A.diagram.obj (op m), hD _⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj i₁, hD _⟩) E₁
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite (X := ⟨A.diagram.obj i₁, hD _⟩) E₁ hE₁)
      hE₁
  let εk : (modulePullback B _ hZ (ObjectProperty.homMk (limit.π A.diagram (op m)) :
      (⟨limit A.diagram, hDlim⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj (op m), hD _⟩)).obj Ek ≅
      EL := (εE ≪≫ (modulePullbackTriangle B _ hZ hk₁).app E₁).symm
  -- the map `ℰ ⟶ π_*ℐ ⊆ π_*𝒪_Y` over the limit
  let fup : EL ⟶ (smallBaseChangeModulePushforward.{u, u} B _ hZ sitL.πHom hrepL).obj
      (SheafOfModules.unit (structureRingSheaf B _ hZ sit.Y)) :=
    pL ≫ (smallBaseChangeModulePushforward.{u, u} B _ hZ sitL.πHom hrepL).map sit.I.ι
  -- the image of `ℰ ⟶ π_*𝒪_Y` over the limit is `π_*ℐ`
  have hfup : Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule fup =
      pushforwardSubmodule B _ hZ sitL.πHom hrepL _ sit.I :=
    (@imageSubmodule_epi_comp_eq _ _ _ _ _ _ _ _ pL hpL _).trans
      (imageSubmodule_map_ι_eq_pushforwardSubmodule sitL.πHom hrepL sit.I)
  -- Stacks 07V7 and the ideal of a later stage
  obtain ⟨j, -, Yj, πj, gj, hπjfin, hπjfp, sqj, Zj, hZjfp, hIZ, Ej, hEj, fj, hfj⟩ :=
    exists_stage_closedSubspace_of_stage A.diagram hconv hD hAff hQc hZ hQs
      (fun i => (A.isNoetherian i).2.2) hDlim hqcL sitL.πHom sitL.isFinite_π hrepL sit.I
      sit.isFiniteTypeQuasicoherent_I.1 fup hfup πk hπkfin hπkfp gk sqk hEk εk
  -- the situation of Stacks 0GUY at a later stage `i'`
  have hIL : idealZeroLocus B _ hZ sitL.Y sitL.I = Set.range (pointsMap B _ hZ
      (Zj.1.preimage gj.hom).toFunctor (Zj.1.preimage gj.hom).ι) :=
    (congrArg (idealZeroLocus B _ hZ sit.Y) hIZ).trans
      (range_pointsMap_ι_eq_idealZeroLocus B _ hZ sit.Y (preimageSubspace B _ hZ gj Zj)).symm
  obtain ⟨i', hji', sit', g', -, -, sq', -, -, hI'⟩ :=
    exists_resolutionPropertyDescentSituation_stage_of_siteContainsBaseChangeLimits A.diagram hD
      hAff hQc hQs hconv hDlim sitL j.unop πj hπjfin hπjfp gj sqj Zj hZjfp hIL
  -- the map `ℰ_{i'} ⟶ π_{i'*}𝒪` at that stage, with image `π_{i'*}ℐ_{i'}`
  have hrepj := relativelyRepresentable_hom_of_isFinite B _ hZ πj hπjfin
  have hπjaff := hπjfin.isAffineHom
  have hrep' := relativelyRepresentable_hom_of_isFinite B _ hZ sit'.πHom sit'.isFinite_π
  have hπ'aff := sit'.isFinite_π.isAffineHom
  have himg := imageSubmodule_modulePullback_map_comp_unitIso_hom sq' hπjaff hπ'aff hrepj hrep' Zj
    fj hfj
  refine ⟨A, hconv, op i', sit', _, isFiniteLocallyFreeOnSite_modulePullback B _ hZ
      (ObjectProperty.homMk (A.diagram.map (homOfLE hji').op) :
        (⟨A.diagram.obj (op i'), hD _⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj j, hD _⟩) Ej
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite (X := ⟨A.diagram.obj j, hD _⟩) Ej hEj)
      hEj, (modulePullback B _ hZ (ObjectProperty.homMk (A.diagram.map (homOfLE hji').op) :
        (⟨A.diagram.obj (op i'), hD _⟩ : AlgebraicSpaces B _ hZ) ⟶ ⟨A.diagram.obj j, hD _⟩)).map
          fj ≫
      (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq' hπjaff hrepj hrep').hom, ?_⟩
  exact (congrArg (pushforwardSubmodule B _ hZ sit'.πHom hrep' _) hI').trans himg.symm

end Main

end AlgebraicGeometry.Space

end
