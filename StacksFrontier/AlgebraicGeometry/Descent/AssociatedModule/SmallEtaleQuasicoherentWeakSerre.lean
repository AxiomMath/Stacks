module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteGrothendieck

/-!
# Quasi-coherent modules on the small étale site form a weak Serre subcategory

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites whose
inverse image `ε^* = (𝓕 ↦ 𝓕^a)` is `AlgebraicGeometry.SmallEtale.associatedModule` and whose
direct image is the restriction `AlgebraicGeometry.SmallEtale.restrictModule`. The
quasi-coherent `𝒪`-modules on `S_étale` are closed under kernels, cokernels and extensions, so
they form a weak Serre subcategory of all `𝒪`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_kernel` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_cokernel`: the kernel and the cokernel of a
  morphism of quasi-coherent `𝒪`-modules on `S_étale` are quasi-coherent, as the instances
  `AlgebraicGeometry.SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite` and
  `AlgebraicGeometry.SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite`.
* `AlgebraicGeometry.SmallEtale.epi_restrictModule_map_g_of_isZero_rightDerived`: the
  restriction to `S_Zar` of a short exact sequence `0 → 𝓗₁ → 𝓔 → 𝓗₂ → 0` on `S_étale` is exact
  on the right as soon as `H¹(U_étale, 𝓗₁)` vanishes for the affine opens `U` of `S`.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_X₂_of_shortExact_of_isZero_rightDerived`:
  under that vanishing, an extension of two quasi-coherent `𝒪`-modules on `S_étale` is
  quasi-coherent.
* `AlgebraicGeometry.SmallEtale.isClosedUnderExtensions_isQuasicoherentOnSite`: quasi-coherent
  `𝒪`-modules on `S_étale` are closed under extensions.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Kernels and cokernels -/

/-- Naturality of the counit, conjugated by the inverse counits:
`f ≫ ε_Y⁻¹ = ε_X⁻¹ ≫ ε^* ε_* f`. -/
private theorem comp_inv_counit_eq {X Y : SheafOfModules.{u} (structureSheaf B S hS)} (f : X ⟶ Y)
    [IsIso ((associatedModuleAdjunction B S hS).counit.app X)]
    [IsIso ((associatedModuleAdjunction B S hS).counit.app Y)] :
    f ≫ inv ((associatedModuleAdjunction B S hS).counit.app Y) =
      inv ((associatedModuleAdjunction B S hS).counit.app X) ≫
        (associatedModule B S hS).map ((restrictModule B S hS).map f) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact ((associatedModuleAdjunction B S hS).counit.naturality f).symm

/-- An `𝒪`-module on `S_étale` isomorphic to `ε^* 𝓜` for a quasi-coherent `𝓜` on `S_Zar` is
quasi-coherent. -/
private theorem isQuasicoherentOnSite_of_iso_associatedModule
    {Z : SheafOfModules.{u} (structureSheaf B S hS)} {𝓜 : S.Modules}
    (h𝓜 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓜)
    (e : (associatedModule B S hS).obj 𝓜 ≅ Z) : Z.IsQuasicoherentOnSite :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS)).prop_of_iso e
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS 𝓜 h𝓜)

/-- The kernel of a morphism of quasi-coherent `𝒪`-modules on `S_étale` is quasi-coherent. -/
public theorem isQuasicoherentOnSite_kernel
    {X Y : SheafOfModules.{u} (structureSheaf B S hS)} (f : X ⟶ Y)
    (hX : X.IsQuasicoherentOnSite) (hY : Y.IsQuasicoherentOnSite) :
    (kernel f).IsQuasicoherentOnSite := by
  have hX' := isQuasicoherent_restrictModule B S hS X hX
  have hY' := isQuasicoherent_restrictModule B S hS Y hY
  have := isIso_counit B S hS X hX hX'
  have := isIso_counit B S hS Y hY hY'
  have : PreservesFiniteLimits (associatedModule B S hS) :=
    preservesFiniteLimits_associatedModule B S hS
  exact isQuasicoherentOnSite_of_iso_associatedModule B S hS
    (@Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel S _ _ _ hX' hY')
    (PreservesKernel.iso (associatedModule B S hS) ((restrictModule B S hS).map f) ≪≫
      (kernel.mapIso _ _ (asIso ((associatedModuleAdjunction B S hS).counit.app X)).symm
        (asIso ((associatedModuleAdjunction B S hS).counit.app Y)).symm
        (comp_inv_counit_eq B S hS f)).symm)

/-- The cokernel of a morphism of quasi-coherent `𝒪`-modules on `S_étale` is quasi-coherent. -/
public theorem isQuasicoherentOnSite_cokernel
    {X Y : SheafOfModules.{u} (structureSheaf B S hS)} (f : X ⟶ Y)
    (hX : X.IsQuasicoherentOnSite) (hY : Y.IsQuasicoherentOnSite) :
    (cokernel f).IsQuasicoherentOnSite := by
  have hX' := isQuasicoherent_restrictModule B S hS X hX
  have hY' := isQuasicoherent_restrictModule B S hS Y hY
  have := isIso_counit B S hS X hX hX'
  have := isIso_counit B S hS Y hY hY'
  exact isQuasicoherentOnSite_of_iso_associatedModule B S hS
    (@Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel S _ _ _ hX' hY')
    (PreservesCokernel.iso (associatedModule B S hS) ((restrictModule B S hS).map f) ≪≫
      (cokernel.mapIso _ _ (asIso ((associatedModuleAdjunction B S hS).counit.app X)).symm
        (asIso ((associatedModuleAdjunction B S hS).counit.app Y)).symm
        (comp_inv_counit_eq B S hS f)).symm)

/-- Quasi-coherent `𝒪`-modules on `S_étale` are closed under kernels. -/
public instance isClosedUnderKernels_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (isQuasicoherentOnSite_kernel B S hS f hX hY)

/-- Quasi-coherent `𝒪`-modules on `S_étale` are closed under cokernels. -/
public instance isClosedUnderCokernels_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (isQuasicoherentOnSite_cokernel B S hS f hX hY)

/-! ### Extensions -/

section Extensions

variable {B S hS}

/-- The restriction to `S_Zar` of a short exact sequence `0 → 𝓗₁ → 𝓔 → 𝓗₂ → 0` on `S_étale` is
exact on the right when `H¹(U_étale, 𝓗₁)` vanishes for every affine open `U` of `S`. -/
public theorem epi_restrictModule_map_g_of_isZero_rightDerived
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h : ∀ U : S.Opens, IsAffineOpen U →
      IsZero (((SheafOfModules.evaluation (structureSheaf B S hS)
        (op ((opensToSmallEtale B S hS).obj U))).rightDerived 1).obj T.X₁)) :
    Epi ((restrictModule B S hS).map T.g) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf B S hS))
  have hsurj : ∀ U : S.Opens, IsAffineOpen U →
      Function.Surjective (T.g.val.app (op ((opensToSmallEtale B S hS).obj U))) := by
    intro U hU
    let := HasDerivedCategory.standard
      (ModuleCat.{u} ((structureSheaf B S hS).obj.obj (op ((opensToSmallEtale B S hS).obj U))))
    exact (ModuleCat.epi_iff_surjective _).1 <|
      Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one
        (SheafOfModules.evaluation (structureSheaf B S hS) (op ((opensToSmallEtale B S hS).obj U)))
        hT (h U hU)
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s => ?_⟩
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hx
  exact ⟨V, homOfLE hVU, hsurj V hV _, hxV⟩

/-- The middle term of a short exact sequence `0 → 𝓗₁ → 𝓔 → 𝓗₂ → 0` of `𝒪`-modules on
`S_étale` with `𝓗₁` and `𝓗₂` quasi-coherent is quasi-coherent, as soon as `H¹(U_étale, 𝓗₁)`
vanishes for every affine open `U` of `S`. -/
public theorem isQuasicoherentOnSite_X₂_of_shortExact_of_isZero_rightDerived
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
    (h : ∀ U : S.Opens, IsAffineOpen U →
      IsZero (((SheafOfModules.evaluation (structureSheaf B S hS)
        (op ((opensToSmallEtale B S hS).obj U))).rightDerived 1).obj T.X₁)) :
    T.X₂.IsQuasicoherentOnSite := by
  have := hT.mono_f
  have : PreservesFiniteLimits (restrictModule B S hS) :=
    (associatedModuleAdjunction B S hS).rightAdjoint_preservesLimits.{0, 0}.preservesFiniteLimits
  have hRT : (T.map (restrictModule B S hS)).ShortExact :=
    { exact := hT.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
      mono_f := (inferInstance : Mono ((restrictModule B S hS).map T.f))
      epi_g := epi_restrictModule_map_g_of_isZero_rightDerived hT h }
  have hR₁ := isQuasicoherent_restrictModule B S hS T.X₁ h₁
  have hR₃ := isQuasicoherent_restrictModule B S hS T.X₃ h₃
  have hR₂ : ((restrictModule B S hS).obj T.X₂).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact hRT hR₁ hR₃
  have : PreservesFiniteLimits (associatedModule B S hS) :=
    preservesFiniteLimits_associatedModule B S hS
  have hLRT := hRT.map_of_exact (associatedModule B S hS)
  have : IsIso (T.mapNatTrans (associatedModuleAdjunction B S hS).counit).τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
      (T.mapNatTrans (associatedModuleAdjunction B S hS).counit) hLRT
      (hT.map_of_exact (𝟭 _)) (isIso_counit B S hS T.X₁ h₁ hR₁)
      (isIso_counit B S hS T.X₃ h₃ hR₃)
  exact isQuasicoherentOnSite_of_iso_associatedModule B S hS hR₂
    (asIso (T.mapNatTrans (associatedModuleAdjunction B S hS).counit).τ₂)

variable (B S hS) in
/-- Quasi-coherent `𝒪`-modules on `S_étale` are closed under extensions: in a short exact
sequence `0 → 𝓗₁ → 𝓔 → 𝓗₂ → 0` of `𝒪`-modules with `𝓗₁` and `𝓗₂` quasi-coherent, `𝓔` is
quasi-coherent. -/
public instance isClosedUnderExtensions_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ :=
    isQuasicoherentOnSite_X₂_of_shortExact_of_isZero_rightDerived hT h₁ h₃ fun U hU =>
      isZero_rightDerived_evaluation_of_isAffine B S hS T.X₁ h₁ ((opensToSmallEtale B S hS).obj U)
        hU 1 Nat.one_pos

end Extensions

end AlgebraicGeometry.SmallEtale

end
