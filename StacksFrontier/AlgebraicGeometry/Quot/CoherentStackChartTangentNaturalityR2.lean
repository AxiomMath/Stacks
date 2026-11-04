module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackExtensionMap
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackTrivial

/-!
# Naturality of the difference of lifts along a morphism of split thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'`, `h₂ : T ⟶ T'₂` split
first order thickenings with retractions `r`, `r₂`, and `g : T'₂ ⟶ T'` a morphism under `T`. The
unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is a morphism from the extension `0 ⟶ I ⊗ i_*𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0`
attached to a lift to the direct image of the one attached to its pullback (Stacks 08MQ). When on
`X_T` it is the identity of `𝒢` on the quotients and a map `κ` of coefficient modules on the
kernels, pulling back lifts along `g` is composition with `κ` on the differences from the trivial
lifts (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference`). The kernel map is
read on `X_T` over arbitrary categories and functors
(`Stacks.Homology.retraction_kernelMap_comp_eq`), from the compatibility of the actions given by
the ideal-square compatibility of `λ`
(`Deformation.ToposThickening.ThickeningTargetMorphism.hkey_of_idealMap`). This is the
naturality of `T_x(M) = Ext¹(𝒢, 𝒢 ⊗ M)` in `M` in the second proof of Stacks 08WA.

## Main results

* `Stacks.Homology.retraction_kernelMap_comp_eq`.
* `thickeningLiftDifference_pullback_eq_comp_of_extensionMaps` (in the namespace
  `AlgebraicGeometry.Space.CoherentSituation`).

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- TC for (smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat) exceeds 1000
-- heartbeats below priority 10000
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe e u

namespace Stacks.Homology

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-- **A kernel map, read on the base through retractions.** Let `restrₖ : Mₖ ⥤ Cₖ` be restrictions
of scalars, `Ψ : M₂ ⥤ M₁` and `J : C₂ ⥤ C₁` the direct images along a morphism of thickenings
with `rI : J ∘ restr₂ ≅ restr₁ ∘ Ψ` natural, `ρₖ : Cₖ ⥤ X` the direct images along retractions
with `c : ρ₁ ∘ J ≅ ρ₂`, `ιₖ : X ⥤ Mₖ` the direct images along the thickenings with
`E : Ψ ∘ ι₂ ≅ ι₁` and `retₖ : ρₖ ∘ restrₖ ∘ ιₖ ≅ 𝟭`, compatible through `hcoh`. For a map
`a₁ ≫ a₂ : K₁ ⟶ Ψ K₂` which under `tₖ : Kₖ ≅ ιₖ Nₖ` is `ι₁ l` up to `E` (`hkey`), with
`l = γ₁ ≫ κ ≫ γ₂⁻¹`, the map `ρ₁(restr₁(a₁ ≫ a₂) ≫ rI⁻¹)` followed by `c` is `κ` read through the
identifications `ρₖ restrₖ Kₖ ≅ Nₖ ≅ Qₖ`. -/
theorem retraction_kernelMap_comp_eq {M₁ : Type u₁} [Category.{v₁} M₁]
    {M₂ : Type u₂} [Category.{v₂} M₂] {C₁ : Type u₃} [Category.{v₃} C₁]
    {C₂ : Type u₄} [Category.{v₄} C₂] {X : Type u₅} [Category.{v₅} X]
    (restr₁ : M₁ ⥤ C₁) (restr₂ : M₂ ⥤ C₂) (Ψ : M₂ ⥤ M₁) (J : C₂ ⥤ C₁) (ρ₁ : C₁ ⥤ X)
    (ρ₂ : C₂ ⥤ X) (ι₁ : X ⥤ M₁) (ι₂ : X ⥤ M₂)
    (rI : ∀ K, J.obj (restr₂.obj K) ≅ restr₁.obj (Ψ.obj K))
    (hrI : ∀ {K K' : M₂} (ψ : K ⟶ K'),
      J.map (restr₂.map ψ) ≫ (rI K').hom = (rI K).hom ≫ restr₁.map (Ψ.map ψ))
    (c : J ⋙ ρ₁ ≅ ρ₂) (E : ι₂ ⋙ Ψ ≅ ι₁)
    (ret₁ : ι₁ ⋙ restr₁ ⋙ ρ₁ ≅ 𝟭 X) (ret₂ : ι₂ ⋙ restr₂ ⋙ ρ₂ ≅ 𝟭 X)
    (hcoh : ∀ N, ρ₁.map (restr₁.map (E.inv.app N) ≫ (rI (ι₂.obj N)).inv) ≫
      c.hom.app (restr₂.obj (ι₂.obj N)) ≫ ret₂.hom.app N = ret₁.hom.app N)
    {K₁ : M₁} {K₂ : M₂} {P₁ : M₁} {N₁ N₂ : X} (a₁ : K₁ ⟶ P₁) (a₂ : P₁ ⟶ Ψ.obj K₂)
    (t₁ : K₁ ≅ ι₁.obj N₁) (t₂ : K₂ ≅ ι₂.obj N₂) {P₁' : M₁} (t₁₁ : K₁ ⟶ P₁')
    (t₁₂ : P₁' ⟶ ι₁.obj N₁) (ht₁ : t₁.hom = t₁₁ ≫ t₁₂) {P₂' : M₂} (t₂₁ : K₂ ⟶ P₂')
    (t₂₂ : P₂' ⟶ ι₂.obj N₂) (ht₂ : t₂.hom = t₂₁ ≫ t₂₂) (l : N₁ ⟶ N₂)
    (hkey : t₁₁ ≫ t₁₂ ≫ ι₁.map l = a₁ ≫ a₂ ≫ Ψ.map (t₂₁ ≫ t₂₂) ≫ E.hom.app N₂)
    {Q₁ Q₂ : X} (γ₁ : N₁ ≅ Q₁) (γ₂ : N₂ ≅ Q₂) (κ : Q₁ ⟶ Q₂)
    (hl : l = γ₁.hom ≫ κ ≫ γ₂.inv) :
    ρ₁.map (restr₁.map (a₁ ≫ a₂) ≫ (rI K₂).inv) ≫ c.hom.app (restr₂.obj K₂) =
      ((restr₁ ⋙ ρ₁).mapIso t₁ ≪≫ ret₁.app N₁ ≪≫ γ₁).hom ≫ κ ≫
        ((restr₂ ⋙ ρ₂).mapIso t₂ ≪≫ ret₂.app N₂ ≪≫ γ₂).inv := by
  rw [← ht₂] at hkey
  have hrI' : (rI K₂).inv ≫ J.map (restr₂.map t₂.hom) =
      restr₁.map (Ψ.map t₂.hom) ≫ (rI (ι₂.obj N₂)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hrI, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc : c.hom.app (restr₂.obj K₂) ≫ ρ₂.map (restr₂.map t₂.hom) =
      ρ₁.map (J.map (restr₂.map t₂.hom)) ≫ c.hom.app (restr₂.obj (ι₂.obj N₂)) :=
    (c.hom.naturality (restr₂.map t₂.hom)).symm
  have hr : ρ₁.map (restr₁.map (ι₁.map l)) ≫ ret₁.hom.app N₂ = ret₁.hom.app N₁ ≫ l :=
    ret₁.hom.naturality l
  have hl' : γ₁.hom ≫ κ = l ≫ γ₂.hom := by rw [hl]; simp
  have hE : restr₁.map (E.hom.app N₂) ≫ restr₁.map (E.inv.app N₂) = 𝟙 _ := by
    rw [← restr₁.map_comp, Iso.hom_inv_id_app, restr₁.map_id]
  have key : (ρ₁.map (restr₁.map (a₁ ≫ a₂) ≫ (rI K₂).inv) ≫ c.hom.app (restr₂.obj K₂)) ≫
      ρ₂.map (restr₂.map t₂.hom) ≫ ret₂.hom.app N₂ ≫ γ₂.hom =
      ρ₁.map (restr₁.map t₁.hom) ≫ ret₁.hom.app N₁ ≫ γ₁.hom ≫ κ := by
    rw [hl', ← reassoc_of% hr, ← reassoc_of% (ρ₁.map_comp _ _), ← restr₁.map_comp, ht₁,
      Category.assoc t₁₁, hkey,
      ← hcoh N₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hc, ← ρ₁.map_comp_assoc (rI K₂).inv, hrI',
      ← ρ₁.map_comp_assoc (restr₁.map (E.hom.app N₂)), hE, ρ₁.map_id, Category.id_comp]
    simp only [Functor.map_comp, Category.assoc]
  refine ((Iso.eq_comp_inv _).2 ?_).trans (Category.assoc _ _ _)
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
    Category.assoc] using key

end Stacks.Homology

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hgr : r₂ = g ≫ r)
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

set_option maxHeartbeats 400000 in
-- The kernel's check of the final `rfl` needs more than the default 200000 heartbeats
-- (it passes at 400000).
/-- **`λ` through `f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥`**: the map of pulled-back ideals of the relative squares
is `λ_g` pulled back along `X_T ⟶ T`, read through
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareThickeningTestIdealIso`. -/
theorem relativeSquareIdealMap_eq_thickeningTestIdeal :
    relativeSquareIdealMap h h₂ g hg hh hh₂ =
      (relativeSquareThickeningTestIdealIso h hh).hom ≫
        ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules).map
          (thickeningIdealMap h.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
            (isIso_toRange_testSchemeMap h hh) (isFirstOrderThickening_range_yoneda_map B S hS _ hh)
            (isIso_toRange_testSchemeMap h₂ hh₂)
            (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂) hh hh₂) ≫
        (relativeSquareThickeningTestIdealIso h₂ hh₂).inv := by
  unfold relativeSquareIdealMap relativeSquareThickeningTestIdealIso thickeningTestIdeal
    QuotientSituation.testSchemeBasePullbackIdeal Deformation.ToposThickening.basePullbackIdeal
    QuotientSituation.testSchemeFirstOrderThickening
  with_reducible rfl

/-- `AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap` unfolded. -/
theorem thickeningCoefficientMap_eq_map :
    thickeningCoefficientMap g hg hh hh₂ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
        (objectToposModule ξ)).map
        (((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules).map
          (thickeningIdealMap h.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
            (isIso_toRange_testSchemeMap h hh) (isFirstOrderThickening_range_yoneda_map B S hS _ hh)
            (isIso_toRange_testSchemeMap h₂ hh₂)
            (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂) hh hh₂)) := by
  delta thickeningCoefficientMap
  refine congrArg _ ?_
  refine congrArg _ ?_
  congr

section Ext

variable
  {heP : HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))}
  {heT : HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))}
  {heP₂ : HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))}
  {heT₂ : HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))}
  {heX : HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
include hr hr₂ in
/-- **Pulling back lifts along a morphism of split thickenings is composition with a map of
coefficient modules, given a morphism of the attached extensions.** Let `τ₁`, `τ₃` be maps of
the kernels and of the quotients of the extensions `0 ⟶ I ⊗ 𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` attached to a lift
and to its pullback along `g`, through which the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is a morphism of
extensions (`hK`, `hQ`, Stacks 08MQ), and `cmp : ρ_*(X_g)_* ≅ ρ₂_*` a comparison of the direct
images along the retractions. If on `X_T` the map of quotients is the identity of `𝒢` (`h₃`) and
the map of kernels is `κ : 𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂` (`h₁`), then the difference from the
trivial lift (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference`) of the
pullback of a class is the difference of the class followed by `κ`. -/
theorem thickeningLiftDifference_pullback_eq_comp_of_extensionMaps
    (cmp : (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap g)).pushforwardModules ⋙
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r₂)).pushforwardModules)
    (κ : thickeningCoefficient ξ h hh ⟶ thickeningCoefficient ξ h₂ hh₂)
    (τ₁ : (structureRestrict (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).obj (thickeningKernel h hh hfl) ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (thickeningKernel h₂ hh₂ hfl₂)))
    (τ₃ : (structureRestrict (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).obj (thickenedModule ξ h) ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (thickenedModule ξ h₂)))
    (hK : ∀ L : D.ThickeningLift ξ h,
      (thickeningLiftExtension h hh L).f ≫ thickeningLiftPullbackUnit hh hh₂ g hg L =
        τ₁ ≫ (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
          (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).f)
    (hQ : ∀ L : D.ThickeningLift ξ h,
      (thickeningLiftExtension h hh L).g ≫ τ₃ =
        thickeningLiftPullbackUnit hh hh₂ g hg L ≫ (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
          (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g)
    (h₁ : (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₁ ≫
        cmp.hom.app ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (thickeningKernel h₂ hh₂ hfl₂)) =
      (thickeningKernelRetractionIso h r hr hh hfl).hom ≫ κ ≫
        (thickeningKernelRetractionIso h₂ r₂ hr₂ hh₂ hfl₂).inv)
    (h₃ : (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₃ ≫
        cmp.hom.app ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (thickenedModule ξ h₂)) =
      (thickenedModuleRetractionIso h r hr).hom ≫ (thickenedModuleRetractionIso h₂ r₂ hr₂).inv)
    (c : D.ThickeningLiftClass ξ h) :
    thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
      (thickeningLiftDifference h r hr hh hfl c).comp (Abelian.Ext.mk₀ κ) (add_zero 1) := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r₂
  have := preservesFiniteColimits_retraction_pushforwardModules h₂ r₂ hr₂ hh₂
  induction c using Quotient.ind with | _ L => ?_
  rw [ThickeningLiftClass.pullback_mk, thickeningLiftDifference_mk, thickeningLiftDifference_mk,
    thickeningLiftExtClass_trivial, thickeningLiftExtClass_trivial, sub_zero, sub_zero]
  exact Stacks.Homology.extConj_mapExactFunctor_extClass_naturality
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r)).pushforwardModules
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r₂)).pushforwardModules
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap g)).pushforwardModules
    cmp (yonedaExtension_shortExact (thickeningLiftExtension h hh L))
    (yonedaExtension_shortExact (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)))
    τ₁ (thickeningLiftPullbackUnit hh hh₂ g hg L) τ₃ (hK L) (hQ L)
    (thickenedModuleRetractionIso h r hr).symm (thickenedModuleRetractionIso h₂ r₂ hr₂).symm
    (thickeningKernelRetractionIso h r hr hh hfl) (thickeningKernelRetractionIso h₂ r₂ hr₂ hh₂ hfl₂)
    κ h₁ h₃

end Ext

end AlgebraicGeometry.Space.CoherentSituation

end
