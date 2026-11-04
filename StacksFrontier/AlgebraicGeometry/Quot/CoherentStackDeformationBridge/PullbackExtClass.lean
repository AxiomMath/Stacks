module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackKernelRetraction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackDifferenceClass
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturalityR3
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturalityR2

/-!
# Crossings for the class on `X_T` of the pullback of a lift

Comparisons used for the naturality of the class on `X_T` of a lift along a morphism
`g : T'₂ ⟶ T'` of split thickenings (in the namespace `AlgebraicGeometry.Space.CoherentSituation`:
`thickeningLiftExtClass_eq_comp_of_hom`,
`thickeningLiftDifference_pullback_eq_comp_of_extensionMaps`), each comparison of two spellings
made once over variables (`CategoryTheory.map_comp_hom_app_eq_of_heq`,
`CategoryTheory.comp_heq_of_heq_iso`).

## Main results

* `CategoryTheory.map_comp_hom_app_eq_of_heq`: a map followed by a component, compared through
  heterogeneous equalities of all its pieces.
* `CategoryTheory.comp_heq_of_heq_iso`: `β₁ ≫ κ ≫ β₂⁻¹` for identifications given as composites,
  compared with the composite of their components.
* `retraction_map_thickeningLiftPullbackQuotientMap_comp_eq_thickenedModule` (in the namespace
  `AlgebraicGeometry.Space.CoherentSituation`): the quotient square on `X_T` at the quotient
  `i₂_*𝒢` of the extension attached to the pullback, in the form of the hypothesis `h₃` of
  `thickeningLiftDifference_pullback_eq_comp_of_extensionMaps`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe e u

namespace CategoryTheory

/-- **A map followed by a component, through heterogeneous equalities of all its pieces**: the
two spellings of each object, functor, isomorphism and map are compared on their own, and
`subst` does the rest. -/
theorem map_comp_hom_app_eq_of_heq {X M₁ M₂ : Type*} [Category* X] [Category* M₁]
    [Category* M₂] (ρ₁ : M₁ ⥤ X) (ρ₂ : M₂ ⥤ X) {γ γ' : M₂ ⥤ M₁} (hγ : γ = γ')
    {c : γ ⋙ ρ₁ ≅ ρ₂} {c' : γ' ⋙ ρ₁ ≅ ρ₂} (hc : HEq c c') {Z Z' : M₁} (hZ : Z = Z')
    {Y Y' : M₂} (hY : Y = Y') {τ : Z ⟶ γ.obj Y} {q : Z' ⟶ γ'.obj Y'} (hτ : HEq τ q)
    {R : ρ₁.obj Z ⟶ ρ₂.obj Y} {R' : ρ₁.obj Z' ⟶ ρ₂.obj Y'} (hR : HEq R R')
    (H : ρ₁.map q ≫ c'.hom.app Y' = R') : ρ₁.map τ ≫ c.hom.app Y = R := by
  subst hγ hZ hY
  cases hc
  cases hτ
  cases hR
  exact H

/-- **`β₁ ≫ κ ≫ β₂⁻¹` for identifications `βₖ` given as composites**, compared with the composite
of their components, through heterogeneous equalities of objects and isomorphisms. -/
theorem comp_heq_of_heq_iso {X M₁ M₂ A₁ A₂ : Type*} [Category* X] [Category* M₁]
    [Category* M₂] [Category* A₁] [Category* A₂] (ρ₁ : M₁ ⥤ X) (ρ₂ : M₂ ⥤ X) (S₁ : A₁ ⥤ M₁)
    (S₂ : A₂ ⥤ M₂) (P₁ : X ⥤ A₁) (P₂ : X ⥤ A₂) (r₁ : P₁ ⋙ S₁ ⋙ ρ₁ ≅ 𝟭 X)
    (r₂ : P₂ ⋙ S₂ ⋙ ρ₂ ≅ 𝟭 X) {K₁ : A₁} {K₂ : A₂} {N₁ N₂ Q₁ Q₂ : X}
    (K₁' : K₁ ≅ P₁.obj N₁) (K₂' : K₂ ≅ P₂.obj N₂) (γ₁ : N₁ ≅ Q₁) (γ₂ : N₂ ≅ Q₂) (κ : Q₁ ⟶ Q₂)
    {Z : M₁} {Y : M₂} (hZ : Z = S₁.obj K₁) (hY : Y = S₂.obj K₂) {β₁ : ρ₁.obj Z ≅ Q₁}
    {β₂ : ρ₂.obj Y ≅ Q₂} (hβ₁ : HEq β₁ ((S₁ ⋙ ρ₁).mapIso K₁' ≪≫ r₁.app N₁ ≪≫ γ₁))
    (hβ₂ : HEq β₂ ((S₂ ⋙ ρ₂).mapIso K₂' ≪≫ r₂.app N₂ ≪≫ γ₂)) :
    HEq (β₁.hom ≫ κ ≫ β₂.inv)
      ((ρ₁.map (S₁.map K₁'.hom) ≫ r₁.hom.app N₁ ≫ γ₁.hom) ≫ κ ≫
        ((γ₂.inv ≫ r₂.inv.app N₂) ≫ ρ₂.map (S₂.map K₂'.inv))) := by
  subst hZ hY
  cases hβ₁
  cases hβ₂
  exact heq_of_eq (by simp)

end CategoryTheory

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (hgr : r₂ = g ≫ r)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]


omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- The quotient `i₂_*𝒢` of the extension attached to a lift across `h₂`, in the spelling of
`Deformation.ToposThickening.thickenedModulesFunctor`. -/
theorem structureRestrict_obj_thickenedModule_eq :
    (structureRestrict
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))).obj
        (thickenedModule ξ h₂) =
      ((structureRestrict
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))).obj
        ((thickenedModulesFunctor
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))).obj
            ξ.F)) :=
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- **The quotient square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, read on `X_T`**, at the quotient
`i₂_*𝒢` of the extension attached to the pullback
(`retraction_map_thickeningLiftPullbackQuotientMap_comp_eq` across the identification of objects
`structureRestrict_obj_thickenedModule_eq`). -/
theorem retraction_map_thickeningLiftPullbackQuotientMap_comp_eq_thickenedModule
    (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        (thickeningLiftPullbackQuotientMap g hg) ≫
      (retractionPushforwardCompIso g hgr).hom.app
        ((structureRestrict
            (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))).obj
          (thickenedModule ξ h₂)) =
      (thickenedModuleRetractionIso h r hr).hom ≫ (thickenedModuleRetractionIso h₂ r₂ hr₂).inv :=
  map_comp_hom_app_eq_of_heq _ _ rfl HEq.rfl rfl
    (structureRestrict_obj_thickenedModule_eq (ξ := ξ) (h₂ := h₂))
    HEq.rfl HEq.rfl (retraction_map_thickeningLiftPullbackQuotientMap_comp_eq g hg hr hr₂ hgr)

end AlgebraicGeometry.Space.CoherentSituation

end
