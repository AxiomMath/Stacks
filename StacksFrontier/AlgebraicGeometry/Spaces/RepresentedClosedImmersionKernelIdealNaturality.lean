module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapChartHom
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafPowersEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingPullbackCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingPullbackUnit

/-!
# Naturality of the Zariski reading of the kernel ideal sheaf along étale base change

Let `j : Z ⟶ T` and `j' : Z' ⟶ T'` be morphisms of test objects sitting in a cartesian square of
represented algebraic spaces `j' ≫ b = a ≫ j` with `b` étale.  The Zariski reading of the kernel
ideal sheaf `𝓘_j` of `yonedaSpaceMap j` is the ideal sheaf of the scheme morphism of `j`
(`AlgebraicGeometry.Space.zariskiReadingKernelIdealIso`).  This file proves that this
identification is compatible with the étale restriction `φ_b^*𝓘_j ≅ 𝓘_{j'}` of Stacks 03LW and the
base change of the Zariski reading on one side, and with the map of ideal sheaves of the scheme
square (Stacks 01R4) on the other.  Both sides are compared inside `𝒪_{T'}`, where the check
reduces to the unit law of the base change of the Zariski reading
(`AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_unit`) and to Stacks 03LW at the
structure sheaf.  It also identifies the composition laws of inverse images of modules on schemes
around a commutative square with `Stacks.ClosedImmersion.pullbackCompIso`.

These are the ideal-level ingredients of the naturality of
`AlgebraicGeometry.Space.zariskiReadingConormalIso` along such squares.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSheafZPowEtaleRestrictionIso_hom_comp_ι`: the étale
  restriction of the powers of the kernel ideal sheaf is compatible with the inclusions into the
  structure sheaves.
* `AlgebraicGeometry.Space.kernelIdealSheafEtaleRestrictionHom`: `φ^*𝓘_i ⟶ 𝓘_{i_U}` in degree one,
  and `AlgebraicGeometry.Space.kernelIdealSheafEtaleRestrictionHom_comp_ι`.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_unit_comp_inv`: the unit law with the
  identifications of the structure sheaves moved across.
* `AlgebraicGeometry.Space.zariskiReadingKernelIdealIso_naturality`: **the ideal-level square**.
* `AlgebraicGeometry.Space.schemePullbackCompOfEq_hom_app_comp_inv_app`: the identification
  `f^*j^* ≅ i^*k^*` of a commutative square of schemes through the composition laws is
  `Stacks.ClosedImmersion.pullbackCompIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Transport along an equality of sheaf submodules commutes with the inclusions. -/
theorem SheafOfModules.Submodule.eqToHom_toSheafOfModules_comp_ι {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
    {N₁ N₂ : M.Submodule} (h : N₁ = N₂) :
    eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules h) ≫ N₂.ι = N₁.ι := by
  subst h
  exact Category.id_comp _

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section SchemeSquare

variable {Z' Z T' T : Scheme.{u}}

/-- The composition law of inverse images of modules on schemes is the inverse of the one of
ringed spaces. -/
theorem scheme_modules_pullbackComp_hom_app_eq (f : Z' ⟶ Z) (g : Z ⟶ T)
    (N : T.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app N =
      (RingedSpaceModuleAdjunction.modulePullbackComp f.toLRSHom.toShHom
        g.toLRSHom.toShHom).inv.app N :=
  rfl

/-- **The identification `f^*j^* ≅ i^*k^*` of a commutative square of schemes** through the two
composition laws named along a common composite `c` is
`Stacks.ClosedImmersion.pullbackCompIso`. -/
theorem schemePullbackCompOfEq_hom_app_comp_inv_app (i : Z' ⟶ T') (k : T' ⟶ T) (f : Z' ⟶ Z)
    (j : Z ⟶ T) (c : Z' ⟶ T) (h₁ : f ≫ j = c) (h₂ : i ≫ k = c) (N : T.Modules) :
    (schemePullbackCompOfEq f j c h₁).hom.app N ≫ (schemePullbackCompOfEq i k c h₂).inv.app N =
      (Stacks.ClosedImmersion.pullbackCompIso
        (Stacks.Conormal.comm_toShHom (h₂.trans h₁.symm)) N).hom := by
  subst h₁
  have hL : (schemePullbackCompOfEq f j (f ≫ j) rfl).hom.app N =
      (RingedSpaceModuleAdjunction.modulePullbackComp f.toLRSHom.toShHom j.toLRSHom.toShHom).inv.app
        N := by
    simp only [schemePullbackCompOfEq, eqToIso_refl, Iso.trans_refl]
    rfl
  have hR : (schemePullbackCompOfEq i k (f ≫ j) h₂).inv.app N =
      (eqToHom (congrArg Scheme.Modules.pullback h₂.symm)).app N ≫
        (RingedSpaceModuleAdjunction.modulePullbackComp i.toLRSHom.toShHom
          k.toLRSHom.toShHom).hom.app N := by
    simp only [schemePullbackCompOfEq, Iso.trans_inv, eqToIso.inv, NatTrans.comp_app]
    rfl
  rw [hL, hR]
  simp only [Stacks.ClosedImmersion.pullbackCompIso,
    RingedSpaceModuleAdjunction.modulePullbackCongr, Iso.trans_hom, Iso.symm_hom, eqToHom_app]
  refine congrArg (_ ≫ ·) (congrArg (· ≫ _) ?_)
  exact (eqToHom_app _ _).symm

end SchemeSquare


section Ideal

variable (B S hS) {U X Z ZU : AlgebraicSpaces B S hS}

/-- **The étale restriction of the powers of the kernel ideal sheaf is compatible with the
inclusions into the structure sheaves**: `φ^*(𝓘ⁿ) ≅ 𝓘_Uⁿ ⊆ 𝒪_U` is the inverse image of
`𝓘ⁿ ⊆ 𝒪_X` followed by `φ^*𝒪_X ≅ 𝒪_U`. -/
theorem kernelIdealSheafZPowEtaleRestrictionIso_hom_comp_ι (p : ZU ⟶ Z) (iU : ZU ⟶ U)
    (i : Z ⟶ X) (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (kernelIdealSheafZPowEtaleRestrictionIso B S hS p iU i φ sq hφ n).hom ≫
        (kernelIdealSheafZPow B S hS iU n).ι =
      (modulePullback B S hS φ).map (kernelIdealSheafZPow B S hS i n).ι ≫
        (modulePullbackUnitIso B S hS φ).hom := by
  have h1 := SheafOfModules.Submodule.eqToHom_toSheafOfModules_comp_ι
    (etaleRestrictionIdealSheafZPowSheaf_eq B S hS φ hφ (kernelIdealSheaf B S hS i)
      (kernelIdealSheaf B S hS iU) (fun W ↦ kernelIdealSheaf_baseChange_obj B S hS p iU i φ sq hφ W)
      n)
  have h2 := (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.naturality
    (kernelIdealSheafZPow B S hS i n).ι
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h1).trans ?_
  refine h2.symm.trans ?_
  exact congrArg (_ ≫ ·) (modulePullbackIsoEtaleModulePullback_hom_app_unit B S hS φ hφ)

/-- **The étale restriction of the kernel ideal sheaf**: for a cartesian square
`i_U ≫ φ = p ≫ i` with `φ` étale, the identification `φ^*𝓘_i ≅ 𝓘_{i_U}` of Stacks 03LW and
`AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq`, in degree one. -/
def kernelIdealSheafEtaleRestrictionHom (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) :
    (modulePullback B S hS φ).obj (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS iU).toSheafOfModules :=
  (modulePullback B S hS φ).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
      (kernelIdealSheafZPow_one B S hS i).symm)) ≫
    (kernelIdealSheafZPowEtaleRestrictionIso B S hS p iU i φ sq hφ 1).hom ≫
    eqToHom (C := Modules.{u, u} B S hS U.1 U.2) (congrArg SheafOfModules.Submodule.toSheafOfModules
      (kernelIdealSheafZPow_one B S hS iU))

/-- `AlgebraicGeometry.Space.kernelIdealSheafEtaleRestrictionHom` is compatible with the
inclusions into the structure sheaves. -/
theorem kernelIdealSheafEtaleRestrictionHom_comp_ι (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) :
    kernelIdealSheafEtaleRestrictionHom B S hS p iU i φ sq hφ ≫ (kernelIdealSheaf B S hS iU).ι =
      (modulePullback B S hS φ).map (kernelIdealSheaf B S hS i).ι ≫
        (modulePullbackUnitIso B S hS φ).hom := by
  have h1 := SheafOfModules.Submodule.eqToHom_toSheafOfModules_comp_ι
    (kernelIdealSheafZPow_one B S hS iU)
  have h2 := SheafOfModules.Submodule.eqToHom_toSheafOfModules_comp_ι
    (kernelIdealSheafZPow_one B S hS i).symm
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1))).trans ?_
  refine (congrArg (_ ≫ ·)
    (kernelIdealSheafZPowEtaleRestrictionIso_hom_comp_ι B S hS p iU i φ sq hφ 1)).trans ?_
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)
  exact ((modulePullback B S hS φ).map_comp _ _).symm.trans
    (congrArg (modulePullback B S hS φ).map h2)

end Ideal

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

/-- `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_unit` with `𝒪_T ≅ R_T 𝒪` and
`𝒪_{T'} ≅ R_{T'} 𝒪` moved to the other side. -/
theorem zariskiReadingPullbackHom_app_unit_comp_inv {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    (zariskiReadingPullbackHom τ).app
          (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) ≫
        (zariskiReadingFunctor T').map
          (modulePullbackUnitIso B S hS (representedSpaceMap B S hS τ)).hom ≫
        (zariskiReadingUnitHomIso T').inv =
      (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          (zariskiReadingUnitHomIso T).inv ≫
        RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)) := by
  have hU := zariskiReadingPullbackHom_app_unit τ
  have hT : (zariskiReadingUnitHomIso T).hom = zariskiReadingUnitHom T := rfl
  have hT' : (zariskiReadingUnitHomIso T').hom = zariskiReadingUnitHom T' := rfl
  rw [← hT, ← hT'] at hU
  refine (Iso.eq_inv_comp ((Stacks.RingedSpace.pullbackFunctor
    (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).mapIso
      (zariskiReadingUnitHomIso T))).2 ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hU)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
    (Category.comp_id _))

/-- A functor carries an equation `x ≫ y = u ≫ v` to one that can be used inside a longer
composite. -/
private theorem map_comp_comp_eq_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B₁ B₂ A' : C} {x : A ⟶ B₁} {y : B₁ ⟶ A'} {u : A ⟶ B₂} {v : B₂ ⟶ A'}
    (h : x ≫ y = u ≫ v) {W : D} (k : F.obj A' ⟶ W) :
    F.map x ≫ F.map y ≫ k = F.map u ≫ F.map v ≫ k := by
  rw [← F.map_comp_assoc, h, F.map_comp_assoc]

section KernelIdeal

variable {Z T Z' T' : BigFppfOver B S hS} (j : Z ⟶ T) (j' : Z' ⟶ T') (a : Z' ⟶ Z) (b : T' ⟶ T)

/-- The two spellings of the morphism of represented algebraic spaces of a morphism of test
objects agree. -/
theorem yonedaSpaceMap_eq_representedSpaceMap {T T' : BigFppfOver B S hS} (b : T' ⟶ T) :
    yonedaSpaceMap b = representedSpaceMap B S hS b :=
  rfl

/-- The inverse images along the two spellings of the morphism of represented algebraic spaces
agree on morphisms. -/
theorem modulePullback_map_yonedaSpaceMap {T T' : BigFppfOver B S hS} (b : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2} (g : M ⟶ N) :
    (modulePullback B S hS (yonedaSpaceMap b)).map g =
      (modulePullback B S hS (representedSpaceMap B S hS b)).map g := by
  with_reducible rfl

/-- The inverse images of modules on schemes in the spellings of Mathlib and of ringed spaces
agree on morphisms. -/
theorem scheme_modules_pullback_map_eq_pullbackFunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (g : M ⟶ N) :
    (Scheme.Modules.pullback f).map g =
      (Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom f)).map g :=
  rfl

/-- Naturality of the base change of the Zariski reading, with the inverse image spelled along
`AlgebraicGeometry.Space.yonedaSpaceMap`. -/
theorem zariskiReadingPullbackHom_naturality_yonedaSpaceMap
    {M N : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2} (g : M ⟶ N) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map b)).map
          ((zariskiReadingFunctor T).map g) ≫ (zariskiReadingPullbackHom b).app N =
      (zariskiReadingPullbackHom b).app M ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (yonedaSpaceMap b)).map g) := by
  have h : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map b)).map
          ((zariskiReadingFunctor T).map g) ≫ (zariskiReadingPullbackHom b).app N =
      (zariskiReadingPullbackHom b).app M ≫
        (zariskiReadingFunctor T').map
          ((modulePullback B S hS (representedSpaceMap B S hS b)).map g) :=
    (zariskiReadingPullbackHom b).naturality g
  exact h.trans (congrArg (fun k => (zariskiReadingPullbackHom b).app M ≫
    (zariskiReadingFunctor T').map k) (modulePullback_map_yonedaSpaceMap b g).symm)

/-- The identification `φ^*𝒪 ≅ 𝒪` in the two spellings of the morphism of represented
algebraic spaces. -/
theorem modulePullbackUnitIso_hom_yonedaSpaceMap {T T' : BigFppfOver B S hS} (b : T' ⟶ T) :
    (modulePullbackUnitIso B S hS (yonedaSpaceMap b)).hom =
      (modulePullbackUnitIso B S hS (representedSpaceMap B S hS b)).hom := by
  with_reducible rfl

/-- `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_unit_comp_inv`, with `φ^*𝒪 ≅ 𝒪`
spelled along `AlgebraicGeometry.Space.yonedaSpaceMap`. -/
theorem zariskiReadingPullbackHom_app_unit_comp_inv_yonedaSpaceMap :
    (zariskiReadingPullbackHom b).app
          (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) ≫
        (zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS (yonedaSpaceMap b)).hom ≫
        (zariskiReadingUnitHomIso T').inv =
      (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          (zariskiReadingUnitHomIso T).inv ≫
        RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b)) :=
  (congrArg (fun k => (zariskiReadingPullbackHom b).app
      (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) ≫
    (zariskiReadingFunctor T').map k ≫ (zariskiReadingUnitHomIso T').inv)
      (modulePullbackUnitIso_hom_yonedaSpaceMap b)).trans
    (zariskiReadingPullbackHom_app_unit_comp_inv b)

/-- The right half of the naturality of `R_T 𝓘 ≅ 𝓘_j`, read inside `𝒪_{T'}`. -/
theorem zariskiReadingKernelIdealIso_naturality_right
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
      (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          (zariskiReadingKernelIdealIso j).hom ≫
        Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm) ≫
        Stacks.ClosedImmersion.idealSheafι ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom =
      (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          ((zariskiReadingFunctor T).map (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι) ≫
        (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          (zariskiReadingUnitHomIso T).inv ≫
        RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b)) := by
  have hISM := Stacks.ClosedImmersion.idealSheafMap_comp_ι (Stacks.Conormal.comm_toShHom comm)
  have hK := zariskiReadingKernelIdealIso_hom_comp_ι j
  exact (congrArg (_ ≫ ·) hISM).trans (map_comp_comp_eq_of_comp_eq _ hK _)

/-- The left half of the naturality of `R_T 𝓘 ≅ 𝓘_j`, read inside `𝒪_{T'}`. -/
theorem zariskiReadingKernelIdealIso_naturality_left
    (sq : IsPullback (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b))
    (hb : IsEtale B S hS (yonedaSpaceMap b).hom) :
    (zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
        (zariskiReadingFunctor T').map (kernelIdealSheafEtaleRestrictionHom B S hS
          (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b) sq hb) ≫
        (zariskiReadingKernelIdealIso j').hom ≫
        Stacks.ClosedImmersion.idealSheafι ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map b)).map
          ((zariskiReadingFunctor T).map (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι) ≫
        (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          (zariskiReadingUnitHomIso T).inv ≫
        RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b)) := by
  have hK' := zariskiReadingKernelIdealIso_hom_comp_ι j'
  have hBR := kernelIdealSheafEtaleRestrictionHom_comp_ι B S hS
    (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b) sq hb
  have hN := zariskiReadingPullbackHom_naturality_yonedaSpaceMap b
    (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι
  have hU := zariskiReadingPullbackHom_app_unit_comp_inv_yonedaSpaceMap b
  have e : (zariskiReadingFunctor T').map (kernelIdealSheafEtaleRestrictionHom B S hS
        (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b) sq hb) ≫
        zariskiReadingKernelIdealι j' =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (yonedaSpaceMap b)).map
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι) ≫
        (zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS (yonedaSpaceMap b)).hom ≫
        (zariskiReadingUnitHomIso T').inv := by
    exact map_comp_comp_eq_of_comp_eq _ hBR _
  refine (congrArg (fun k => (zariskiReadingPullbackHom b).app _ ≫ _ ≫ k) hK').trans ?_
  refine (congrArg ((zariskiReadingPullbackHom b).app _ ≫ ·) e).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hN.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) hU

/-- **Naturality of `R_T 𝓘 ≅ 𝓘_j` along étale base change**: for a cartesian square
`j' ≫ b = a ≫ j` of test objects with `b` étale, the base change of the Zariski reading of the
kernel ideal sheaf, its étale restriction `φ_b^*𝓘_j ≅ 𝓘_{j'}` and the reading at `j'` give the
reading at `j` pulled back along `b` followed by the map of ideal sheaves of the scheme square. -/
theorem zariskiReadingKernelIdealIso_naturality
    (sq : IsPullback (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b))
    (hb : IsEtale B S hS (yonedaSpaceMap b).hom)
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
      (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
        (zariskiReadingFunctor T').map (kernelIdealSheafEtaleRestrictionHom B S hS
          (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b) sq hb) ≫
        (zariskiReadingKernelIdealIso j').hom =
      (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          (zariskiReadingKernelIdealIso j).hom ≫
        Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm) := by
  have : Mono (Stacks.ClosedImmersion.idealSheafι
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) :=
    inferInstanceAs (Mono (kernel.ι _))
  refine Mono.right_cancellation (f := Stacks.ClosedImmersion.idealSheafι
    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) _ _ ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans ?_
  refine (zariskiReadingKernelIdealIso_naturality_left j j' a b sq hb).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (zariskiReadingKernelIdealIso_naturality_right j j' a b comm).symm
  exact congrArg (· ≫ _) (scheme_modules_pullback_map_eq_pullbackFunctor_map _ _)

end KernelIdeal

end AlgebraicGeometry.Space

end
