module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageSubsheafUniversal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalEtaleRestrictionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardSubmoduleIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspacePushforwardImage

/-!
# The direct image of the ideal of an inverse image, under affine base change

Let

```
Y' --g'--> Y
|π'         |π
v           v
X' --g-->  X
```

be a cartesian square of algebraic spaces with `π` affine, let `Z ⊆ Y` be a closed subspace with
defining ideal `ℐ`, and let `f : ℰ ⟶ π_*𝒪_Y` be a morphism of `𝒪_X`-modules whose image is the
direct image `π_*ℐ`.  Then the image of the inverse image `g^*f`, read in `π'_*𝒪_{Y'}` through the
affine base change isomorphism `β : g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}` of Stacks 07U8, is the direct image
`π'_*ℐ'` of the defining ideal `ℐ'` of the inverse image `(g')⁻¹(Z) = Z ×_Y Y'`.

## Main results

* `AlgebraicGeometry.Space.imageSubmodule_modulePullback_map_comp_unitIso_hom`: the statement
  above.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

/-! ### Images -/

section Image

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N L : SheafOfModules.{u} R}

/-- Reassociation of a composite through two commuting squares. -/
private theorem comp_comp_eq_of_eq_of_eq {D : Type*} [Category D] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : D}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (h : P₃ ⟶ P₄) (k : P₄ ⟶ P₅) (c' : P₂ ⟶ P₆)
    (l : P₆ ⟶ P₄) (m : P₆ ⟶ P₇) (p : P₇ ⟶ P₅) (h₁ : c ≫ h = c' ≫ l) (h₂ : l ≫ k = m ≫ p) :
    (a ≫ b ≫ c) ≫ h ≫ k = (a ≫ b ≫ c' ≫ m) ≫ p := by
  simp only [Category.assoc, reassoc_of% h₁, h₂]

end Image

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identification of the direct image of a submodule with the direct image of the module
carries the direct image of the inclusion to the inclusion. -/
private theorem pushforwardSubmoduleIso_hom_comp_map_ι {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    (F : SheafOfModules.{u} (smallEtaleRingSheaf B S hS Y.1 Y.2)) (P : F.Submodule) :
    (pushforwardSubmoduleIso B S hS f hf F P).hom ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS f hf).map P.ι =
      (pushforwardSubmodule B S hS f hf F P).ι := by
  have := mono_map_ι_smallBaseChangeModulePushforward B S hS f hf F P
  have h1 : (monoRangeSubmoduleIso
        ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).map P.ι)).inv ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS f hf).map P.ι =
      (monoRangeSubmodule ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).map P.ι)).ι := by
    rw [Iso.inv_comp_eq, monoRangeSubmoduleIso_hom_comp_ι]
  rw [pushforwardSubmoduleIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc, h1]
  exact Stacks.SheafOfModules.Submodule.eqToHom_comp_ι
    (monoRangeSubmodule_map_ι_eq B S hS f hf F P).symm _

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModulesIdealBaseChange
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- The base-change direct image along an affine morphism preserves epimorphisms of
quasi-coherent modules. -/
private theorem epi_smallBaseChangeModulePushforward_map {X Y : AlgebraicSpaces B S hS}
    (π : Y ⟶ X) (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) [Epi φ] :
    Epi ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map φ) := by
  have h : (modulePushforward B S hS π).map φ ≫ (modulePushforwardChartIso B S hS π hπ).hom.app N =
      (modulePushforwardChartIso B S hS π hπ).hom.app M ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map φ :=
    (modulePushforwardChartIso B S hS π hπ).hom.naturality φ
  have h1 := epi_modulePushforward_map_of_isAffineHom π hπa hM hN φ
  have h3 : Epi ((modulePushforward B S hS π).map φ ≫
      (modulePushforwardChartIso B S hS π hπ).hom.app N) :=
    @epi_comp' _ _ _ _ _ _ _ h1 (@IsIso.epi_of_iso _ _ _ _ _
      (Iso.isIso_hom ((modulePushforwardChartIso B S hS π hπ).app N)))
  rw [h] at h3
  exact @epi_of_epi _ _ _ _ _ _ _ h3

section BaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} {π : Y ⟶ X} {g : X' ⟶ X} {π' : Y' ⟶ X'}
  {g' : Y' ⟶ Y}

/-- **The image of the inverse image of a map onto `π_*ℐ` is the direct image of the ideal of the
inverse image.**  For a cartesian square with `π` affine, a closed subspace `Z ⊆ Y` with defining
ideal `ℐ`, and `f : ℰ ⟶ π_*𝒪_Y` with image `π_*ℐ`, the image of `g^*f`, read in `π'_*𝒪_{Y'}`
through the affine base change isomorphism, is `π'_*ℐ'` for `ℐ'` the defining ideal of
`(g')⁻¹(Z)`. -/
theorem imageSubmodule_modulePullback_map_comp_unitIso_hom (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ'a : IsAffineHom B S hS π'.hom)
    (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (Z : ClosedSubspaces B S hS Y.1)
    {E : Modules.{u, u} B S hS X.1 X.2}
    (f : E ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y)))
    (hf : imageSubmodule f =
      pushforwardSubmodule B S hS π hπ _ (definingIdealSheaf B S hS Y Z)) :
    imageSubmodule ((modulePullback B S hS g).map f ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom) =
      pushforwardSubmodule B S hS π' hπ' _
        (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)) := by
  have hIqc := isQuasicoherentOnSite_definingIdealSheaf B S hS Y Z
  have hI'qc := isQuasicoherentOnSite_definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)
  let q : E ⟶ (pushforwardSubmodule B S hS π hπ _
      (definingIdealSheaf B S hS Y Z)).toSheafOfModules :=
    toImage f ≫ eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules hf)
  have hq : q ≫ (pushforwardSubmodule B S hS π hπ _ (definingIdealSheaf B S hS Y Z)).ι = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => toImage f ≫ z)
        (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι hf _)).trans (toImage_ι f))
  have : Epi q := epi_comp' (epi_toImage f)
    (@IsIso.epi_of_iso _ _ _ _ _
      (Iso.isIso_hom (eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules hf))))
  have hN := pushforwardSubmoduleIso_hom_comp_map_ι π hπ
    (SheafOfModules.unit (structureRingSheaf B S hS Y)) (definingIdealSheaf B S hS Y Z)
  have hN' := pushforwardSubmoduleIso_hom_comp_map_ι π' hπ'
    (SheafOfModules.unit (structureRingSheaf B S hS Y'))
    (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z))
  have hnat := smallBaseChangeModuleAffineBaseChangeIso_hom_naturality sq hπa hπ hπ'
    (G := SheafOfModules.unit (structureRingSheaf B S hS Y)) hIqc
    (SheafOfModules.isQuasicoherentOnSite_unit _) (definingIdealSheaf B S hS Y Z).ι
  have hι := idealSheafMap_comp_ι B S hS (preimageSubspace B S hS g' Z) Z g'
    (preimageProjection B S hS g' Z) (conormalEtaleRestrictionSquare B S hS g' Z)
  have hs : structureSheafMap B S hS g' = (modulePullbackUnitIso B S hS g').hom :=
    structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS g'
  have m1 : (modulePullback B S hS g).map f =
      (modulePullback B S hS g).map q ≫
        (modulePullback B S hS g).map (pushforwardSubmoduleIso B S hS π hπ _
          (definingIdealSheaf B S hS Y Z)).hom ≫
        (modulePullback B S hS g).map ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map
          (definingIdealSheaf B S hS Y Z).ι) := by
    rw [← hq, ← hN]
    exact ((modulePullback B S hS g).map_comp _ _).trans
      (congrArg (fun z => (modulePullback B S hS g).map q ≫ z)
        ((modulePullback B S hS g).map_comp _ _))
  obtain ⟨kv, hkv⟩ : ∃ kv : (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        ((modulePullback B S hS g').obj (SheafOfModules.unit (structureRingSheaf B S hS Y))) ⟶
      ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y')) : Modules.{u, u} B S hS X'.1 X'.2),
      kv = (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
        (modulePullbackUnitIso B S hS g').hom := ⟨_, rfl⟩
  obtain ⟨lv, hlv⟩ : ∃ lv : (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        ((modulePullback B S hS g').obj (definingIdealSheaf B S hS Y Z).toSheafOfModules) ⟶
      ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        ((modulePullback B S hS g').obj (SheafOfModules.unit (structureRingSheaf B S hS Y))) :
          Modules.{u, u} B S hS X'.1 X'.2),
      lv = (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
        ((modulePullback B S hS g').map (definingIdealSheaf B S hS Y Z).ι) := ⟨_, rfl⟩
  obtain ⟨mv, hmv⟩ : ∃ mv : (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        ((modulePullback B S hS g').obj (definingIdealSheaf B S hS Y Z).toSheafOfModules) ⟶
      ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)).toSheafOfModules :
          Modules.{u, u} B S hS X'.1 X'.2),
      mv = (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
          (idealSheafMap B S hS (preimageSubspace B S hS g' Z) Z g'
            (preimageProjection B S hS g' Z) (conormalEtaleRestrictionSquare B S hS g' Z)) :=
    ⟨_, rfl⟩
  obtain ⟨pv, hpv⟩ : ∃ pv : (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)).toSheafOfModules ⟶
      ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y')) : Modules.{u, u} B S hS X'.1 X'.2),
      pv = (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
          (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)).ι := ⟨_, rfl⟩
  have hU : (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom =
      (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ'
        (SheafOfModules.unit (structureRingSheaf B S hS Y))
        (SheafOfModules.isQuasicoherentOnSite_unit _)).hom ≫ kv := by
    rw [hkv]
    exact modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom sq hπa hπ hπ'
  have hnat' : (modulePullback B S hS g).map
        ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map
          (definingIdealSheaf B S hS Y Z).ι) ≫
      (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ'
        (SheafOfModules.unit (structureRingSheaf B S hS Y))
        (SheafOfModules.isQuasicoherentOnSite_unit _)).hom =
      (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' _ hIqc).hom ≫ lv := by
    rw [hlv]
    exact hnat
  have m3 : lv ≫ kv = mv ≫ pv := by
    have hι' : (modulePullback B S hS g').map (definingIdealSheaf B S hS Y Z).ι ≫
        (modulePullbackUnitIso B S hS g').hom =
        idealSheafMap B S hS (preimageSubspace B S hS g' Z) Z g'
            (preimageProjection B S hS g' Z) (conormalEtaleRestrictionSquare B S hS g' Z) ≫
          (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)).ι := by
      rw [← hs]
      exact hι.symm
    rw [hkv, hlv, hmv, hpv]
    exact (((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map_comp _ _).symm.trans
      (congrArg (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map hι')).trans
      ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map_comp _ _)
  have e1 : (modulePullback B S hS g).map f ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom =
      ((modulePullback B S hS g).map q ≫
        (modulePullback B S hS g).map (pushforwardSubmoduleIso B S hS π hπ _
          (definingIdealSheaf B S hS Y Z)).hom ≫
        (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' _ hIqc).hom ≫ mv) ≫ pv := by
    rw [m1, hU]
    exact comp_comp_eq_of_eq_of_eq _ _ _ _ _ _ _ _ _ hnat' m3
  have hmvepi : Epi mv := by
    have := epi_idealSheafMap B S hS g' Z
    have h := epi_smallBaseChangeModulePushforward_map π' hπ'a hπ'
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' _ hIqc) hI'qc
      (idealSheafMap B S hS (preimageSubspace B S hS g' Z) Z g'
            (preimageProjection B S hS g' Z) (conormalEtaleRestrictionSquare B S hS g' Z))
    subst hmv
    exact h
  have := preservesEpimorphisms_modulePullback B S hS g
  have hpre : Epi ((modulePullback B S hS g).map q ≫
        (modulePullback B S hS g).map (pushforwardSubmoduleIso B S hS π hπ _
          (definingIdealSheaf B S hS Y Z)).hom ≫
        (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' _ hIqc).hom ≫ mv) :=
    epi_comp' ((modulePullback B S hS g).map_epi q)
      (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullback B S hS g).mapIso
          (pushforwardSubmoduleIso B S hS π hπ _ (definingIdealSheaf B S hS Y Z)))))
        (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) hmvepi))
  refine (congrArg imageSubmodule e1).trans
    ((imageSubmodule_locallySurjective_comp _
      (@Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _ _ _ _ _ _ _ _ hpre)
      pv).trans ?_)
  subst hpv
  have hle := imageSubmodule_le ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
      (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)).ι)
    (P := pushforwardSubmodule B S hS π' hπ' _
      (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z))) fun X m => m.2
  refine SheafOfModules.Submodule.ext ?_
  ext X x
  exact ⟨fun hx => hle X hx, fun hx => apply_mem_imageSubmodule
    ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
      (definingIdealSheaf B S hS Y' (preimageSubspace B S hS g' Z)).ι) (X := X) ⟨x, hx⟩⟩

end BaseChange

end AlgebraicGeometry.Space

end
