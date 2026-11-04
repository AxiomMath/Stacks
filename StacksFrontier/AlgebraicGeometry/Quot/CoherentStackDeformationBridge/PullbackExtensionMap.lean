module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackKernelSquare

/-!
# The morphism of extensions attached to the pullback of a lift

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `L` a lift of `ξ` across a first
order thickening `h : T ⟶ T'` and `g : T'₂ ⟶ T'` a morphism under `T` from a first order
thickening `h₂ : T ⟶ T'₂`. The unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is a morphism from the extension
`0 ⟶ I ⊗ 𝒢 ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` attached to `L` (Stacks 08MQ) to the direct image along `X_g` of the
extension attached to the pullback of `L`: on the quotients it is the comparison
`(X_h)_*𝒢 ≅ (X_g)_*(X_{h₂})_*𝒢` of Stacks 03LU, and on the kernels it is the map of square-zero
ideals induced by `X_g` tensored with `𝒢`
(`Deformation.ToposThickening.ThickeningTargetMorphism.f_comp_eq_idealTensorMap_comp`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit`: the
  kernel square.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_g_comp_pullbackQuotientMap`:
  the quotient square.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

universe e u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `AlgebraicGeometry.Space.comp_pushforwardModulesIsoModulePushforward_inv_app_comp_map_comp_eq`
with the first composite formed among sheaves of modules on the small étale ringed topos. -/
theorem comp_pushforwardModulesIsoModulePushforward_inv_app_comp_map_comp_eq_sheafOfModules
    {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {N : Modules.{u, u} B S hS X₂.1 X₂.2}
    {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2} (v : F₁ ⟶ (modulePushforward B S hS b).obj N)
    (Y : N ⟶ (structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj F₀))
    (Y' : N ⟶ (smallEtaleRingedToposHom B S hS a).pushforwardModules.obj F₀)
    (hY : @Eq (N ⟶ (structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj F₀)) Y Y') :
    ((@CategoryStruct.comp (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS X₁).O)) _ F₁ _ _ v
        ((pushforwardModulesIsoModulePushforward B S hS b).inv.app N)) ≫
      (smallEtaleRingedToposHom B S hS b).pushforwardModules.map Y ≫
      (pushforwardModulesCompAt B S hS a b).hom.app F₀ ≫
      eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj F₀) e)) ≫
        (pushforwardModulesIsoModulePushforward B S hS k).hom.app F₀ =
      v ≫ (modulePushforward B S hS b).map Y' ≫ (modulePushforward B S hS b).map
          ((pushforwardModulesIsoModulePushforward B S hS a).hom.app F₀) ≫
        (modulePushforwardCompIso B S hS a b ≪≫
          eqToIso (congrArg (modulePushforward B S hS) e)).hom.app F₀ :=
  comp_pushforwardModulesIsoModulePushforward_inv_app_comp_map_comp_eq a b e v Y Y' hY

/-- **The reduction square of a map of extensions along `a ≫ b = k`, read through `j_*M ≅ Ψ₀M`**:
for extensions `E₁`, `E₂` of `k_*M`, `a_*M` and a map `u : E₁ ⟶ b_*E₂` lying over the comparison
`b_*a_* ≅ k_*` of Stacks 03LU, `u` followed by `b_*` of the quotient map of `E₂` and
`j_*a_*M ≅ Ψ₀ a_*M` is the quotient map of `E₁` followed by `k_*M ≅ Ψ₀ a_*M`. -/
theorem comp_map_g_comp_restrictIso_hom_eq_of_comp_map_g_eq {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O))
    {K₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₁).O)}
    {K₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₂).O)}
    (E₁ : Abelian.YonedaExtension ((structureRestrict (smallEtaleRingedToposHom B S hS k)).obj
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj M)) K₁ 0)
    (E₂ : Abelian.YonedaExtension ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) K₂ 0)
    (u : E₁.Z.left ⟶ (smallEtaleRingedToposHom B S hS b).pushforwardModules.obj E₂.Z.left)
    (hQ : u ≫ (smallEtaleRingedToposHom B S hS b).pushforwardModules.map E₂.g ≫
        (pushforwardModulesCompAt B S hS a b).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e) = E₁.g) :
    @CategoryStruct.comp _ _ E₁.Z.left
        ((smallEtaleThickeningTargetOfEq a b k e).j.pushforwardModules.obj E₂.Z.left) _ u
        ((smallEtaleThickeningTargetOfEq a b k e).j.pushforwardModules.map E₂.g ≫
          ((smallEtaleThickeningTargetOfEq a b k e).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).hom) =
      E₁.g ≫ (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso a b k e).inv.app M) :=
  comp_comp_restrictIso_hom_eq_comp_map_smallEtaleThickenedModulesCompIso_inv_app a b e M u
    ((smallEtaleRingedToposHom B S hS b).pushforwardModules.map E₂.g) E₁.g hQ

/-- **The quotient square of a map of extensions along `a ≫ b = k`**: for extensions `E₁`, `E₂` of
`k_*M`, `a_*M` and a map `u : E₁ ⟶ b_*E₂` lying over the comparison `b_*a_* ≅ k_*` of Stacks 03LU,
the quotient map of `E₁` followed by `k_*M ≅ Ψ₀ a_*M ≅ b_* a_*M` is `u` followed by `b_*` of the
quotient map of `E₂`. -/
theorem g_comp_restrictIso_inv_eq_of_comp_map_g_eq {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O))
    {K₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₁).O)}
    {K₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₂).O)}
    (E₁ : Abelian.YonedaExtension ((structureRestrict (smallEtaleRingedToposHom B S hS k)).obj
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj M)) K₁ 0)
    (E₂ : Abelian.YonedaExtension ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) K₂ 0)
    (u : E₁.Z.left ⟶ (smallEtaleRingedToposHom B S hS b).pushforwardModules.obj E₂.Z.left)
    (hQ : u ≫ (smallEtaleRingedToposHom B S hS b).pushforwardModules.map E₂.g ≫
        (pushforwardModulesCompAt B S hS a b).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e) = E₁.g) :
    E₁.g ≫ (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso a b k e).inv.app M) ≫
      ((smallEtaleThickeningTargetOfEq a b k e).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv =
      u ≫ (smallEtaleRingedToposHom B S hS b).pushforwardModules.map E₂.g := by
  have h := comp_map_g_comp_restrictIso_hom_eq_of_comp_map_g_eq a b e M E₁ E₂ u hQ
  exact (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).2
    (h.symm.trans (Category.assoc _ _ _).symm))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))

/-- **The unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`** of a lift `𝒢'`, from the middle term of the extension
attached to `L` to the direct image of that attached to its pullback: the unit of the inverse
image along `X_g` followed by the identification of the two direct images (Stacks 03LU). -/
abbrev thickeningLiftPullbackUnit (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    @Quiver.Hom (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O)) _
      (thickeningLiftExtension h hh L).Z.left
      ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).Z.left) :=
  @CategoryStruct.comp (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O)) _ L.F _ _
    ((modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap g)).unit.app L.F)
    ((pushforwardModulesIsoModulePushforward B S hS
        (D.relativeSquareSituation.relativeMap g)).inv.app
      ((modulePullback B S hS (D.relativeSquareSituation.relativeMap g)).obj L.F))

/-- **The reduction square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**, on the extensions attached to
`L` and to its pullback, among sheaves of modules on the small étale ringed topos. -/
theorem thickeningLiftPullbackUnit_comp_map_thickeningLiftExtension_g (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    thickeningLiftPullbackUnit hh hh₂ g hg L ≫
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g ≫
      (pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g)).hom.app ξ.F ≫
      eqToHom (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
          D.relativeSquareSituation.space T' =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj ξ.F)
        (relativeMap_comp_of_comp_eq g hg)) = (thickeningLiftExtension h hh L).g := by
  refine (Iso.cancel_iso_hom_right _ _ ((pushforwardModulesIsoModulePushforward B S hS
    (D.relativeSquareSituation.relativeMap h)).app ξ.F)).1 ?_
  refine (comp_pushforwardModulesIsoModulePushforward_inv_app_comp_map_comp_eq_sheafOfModules
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (relativeMap_comp_of_comp_eq g hg) (F₁ := L.F)
    (N := (modulePullback B S hS (D.relativeSquareSituation.relativeMap g)).obj L.F) (F₀ := ξ.F)
    ((modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap g)).unit.app L.F)
    (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g ((L.pullback g hg).toThickened h₂)
    (thickeningLiftExtension_g_eq hh₂ (L.pullback g hg))).trans ?_
  refine (unit_comp_map_pullback_toThickened_comp_eq_aux g hg L).trans ?_
  refine (L.reduction_pullback g hg).symm.trans ?_
  refine L.toThickened_comp_pushforwardModulesIsoModulePushforward_hom_app.symm.trans ?_
  exact congrArg (· ≫ _) (thickeningLiftExtension_g_eq hh L).symm

/-- **The reduction square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, read through `j_*M ≅ Ψ₀M`.** -/
theorem thickeningLiftPullbackUnit_comp_map_g_comp_restrictIso_hom (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    type_of% (comp_map_g_comp_restrictIso_hom_eq_of_comp_map_g_eq
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (relativeMap_comp_of_comp_eq g hg) ξ.F
      (thickeningLiftExtension h hh L) (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
      (thickeningLiftPullbackUnit hh hh₂ g hg L)
      (thickeningLiftPullbackUnit_comp_map_thickeningLiftExtension_g hh hh₂ g hg L)) :=
  comp_map_g_comp_restrictIso_hom_eq_of_comp_map_g_eq
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (relativeMap_comp_of_comp_eq g hg) ξ.F
    (thickeningLiftExtension h hh L) (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
    (thickeningLiftPullbackUnit hh hh₂ g hg L)
    (thickeningLiftPullbackUnit_comp_map_thickeningLiftExtension_g hh hh₂ g hg L)

/-- **The kernel square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**: on the kernels `I ⊗ i_*𝒢` and
`I₂ ⊗ i₂_*𝒢` of the extensions attached to `L` and to its pullback, the unit is
`I ⊗ (i_*𝒢 ≅ Ψ₀ i₂_*𝒢)` followed by the comparison `I ⊗ Ψ₀ i₂_*𝒢 ⟶ Ψ₀(I₂ ⊗ i₂_*𝒢)` of the map
of square-zero ideals
(`Deformation.ToposThickening.ThickeningTargetMorphism.f_comp_eq_idealTensorMap_comp`). -/
theorem thickeningLiftExtension_f_comp_pullbackUnit (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    type_of% ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).f_comp_eq_idealTensorMap_comp
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
      (F₁ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).obj ξ.F)
      (F₂ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)
      ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F)
      (thickeningLiftExtension h hh L) (extensionActionMap_thickeningLiftExtension hh L)
      (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
      (extensionActionMap_thickeningLiftExtension hh₂ (L.pullback g hg))
      (thickeningLiftPullbackUnit hh hh₂ g hg L)
      (thickeningLiftPullbackUnit_comp_map_g_comp_restrictIso_hom hh hh₂ g hg L)) :=
  (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).f_comp_eq_idealTensorMap_comp
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (F₁ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h))).obj ξ.F)
    (F₂ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)
    ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F)
    (thickeningLiftExtension h hh L) (extensionActionMap_thickeningLiftExtension hh L)
    (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
    (extensionActionMap_thickeningLiftExtension hh₂ (L.pullback g hg))
    (thickeningLiftPullbackUnit hh hh₂ g hg L)
    (thickeningLiftPullbackUnit_comp_map_g_comp_restrictIso_hom hh hh₂ g hg L)

/-- **The quotient square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**: the reduction of `L` followed by
`i_*𝒢 ≅ Ψ₀ i₂_*𝒢 ≅ (X_g)_* i₂_*𝒢` is the unit followed by the direct image of the reduction of the
pulled back lift. -/
theorem thickeningLiftExtension_g_comp_pullbackQuotientMap (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    type_of% (g_comp_restrictIso_inv_eq_of_comp_map_g_eq
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (relativeMap_comp_of_comp_eq g hg) ξ.F
      (thickeningLiftExtension h hh L) (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
      (thickeningLiftPullbackUnit hh hh₂ g hg L)
      (thickeningLiftPullbackUnit_comp_map_thickeningLiftExtension_g hh hh₂ g hg L)) :=
  g_comp_restrictIso_inv_eq_of_comp_map_g_eq
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (relativeMap_comp_of_comp_eq g hg) ξ.F
    (thickeningLiftExtension h hh L) (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
    (thickeningLiftPullbackUnit hh hh₂ g hg L)
    (thickeningLiftPullbackUnit_comp_map_thickeningLiftExtension_g hh hh₂ g hg L)

/-- **The quotient map read on `X_T`**: through the retractions `ρ = X_r`, `ρ₂ = X_{r₂}` with
`r₂ = g ≫ r`, the map `ρ_*(i_*𝒢 ≅ Ψ₀ i₂_*𝒢 ≅ (X_g)_* i₂_*𝒢)` followed by
`ρ_*(X_g)_* ≅ ρ₂_*` is `ρ_* i_*𝒢 ≅ 𝒢 ≅ ρ₂_* i₂_*𝒢` (the associativity coherence of Stacks 03LU). -/
theorem retraction_map_pullbackQuotientMap (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) {r : T' ⟶ ξ.T}
    {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T) (hgr : r₂ = g ≫ r) :
    type_of% ((Iso.eq_comp_inv ((CoherentSituation.pushforwardModulesRetractionIso
        (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap r₂)
        (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂)).app ξ.F)).2
      ((Category.assoc _ _ _).trans (pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso
        (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
        (D.relativeSquareSituation.relativeMap r) (relativeMap_comp_of_comp_eq g hg)
        (relativeMap_comp_of_eq_comp g hgr) (relativeMap_comp_relativeMap_retraction h r hr)
        (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂) ξ.F))) :=
  (Iso.eq_comp_inv ((CoherentSituation.pushforwardModulesRetractionIso
        (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap r₂)
        (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂)).app ξ.F)).2
    ((Category.assoc _ _ _).trans (pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso
        (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
        (D.relativeSquareSituation.relativeMap r) (relativeMap_comp_of_comp_eq g hg)
        (relativeMap_comp_of_eq_comp g hgr) (relativeMap_comp_relativeMap_retraction h r hr)
        (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂) ξ.F))

end AlgebraicGeometry.Space.CoherentSituation

end
