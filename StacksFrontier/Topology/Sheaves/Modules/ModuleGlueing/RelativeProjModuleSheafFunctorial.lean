module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Functoriality
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.SectionModuleFunctorial
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Hom
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheaf

/-!
# Functoriality of the sheaf attached to a graded module on a relative projective spectrum

Let `s` be a relative `Proj` situation and let `ℳ` be a graded module over its graded algebra
with quasi-coherent homogeneous pieces, so that the sheaf
`ℳ̃ = Stacks.RelativeProj.Situation.moduleSheaf ℳ` is defined. A homomorphism `f : ℳ ⟶ 𝒩` of
graded modules induces a morphism `ℳ̃ ⟶ 𝒩̃`, and the construction is functorial: the identity
induces the identity and a composite induces the composite.

## Main definitions

* `Stacks.RelativeProj.Situation.moduleChartMap`: the morphism of the chart sheaves induced by a
  homomorphism of graded modules.
* `Stacks.RelativeProj.Situation.modulesDirectedGlueHom`: those chart morphisms as a morphism of
  the locally directed glueing datum.
* `Stacks.RelativeProj.Situation.moduleSheafMap`: the morphism `ℳ̃ ⟶ 𝒩̃` induced by a
  homomorphism of graded modules.
* `Stacks.RelativeProj.Situation.moduleSheafFunctor`: the functor `ℳ ↦ ℳ̃` from quasi-coherent
  graded modules to modules on the relative projective spectrum.

## Main results

* `Stacks.RelativeProj.Situation.modulePushforwardMap_moduleChartMap`: the chart morphisms commute
  with the comparisons of the chart sheaves.
* `Stacks.RelativeProj.Situation.moduleSheafMap_chartSec`: the induced morphism is the chart
  morphism on sections over an open lying in a chart.
* `Stacks.RelativeProj.Situation.moduleSheafMap_id` and
  `Stacks.RelativeProj.Situation.moduleSheafMap_comp`: the construction is functorial.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjModuleComparison Stacks.SheafOfModules Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.ProjModuleComparison

variable {A B M N M₂ N₂ : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup N₂] [Module B N₂]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The module fibre comparison of a graded ring homomorphism commutes with a localized linear
map, given a square of linear maps commuting on the nose: `f` and `f₂` are the semilinear maps
being compared across `φ`, and `u`, `v` are linear maps of the sources and of the targets with
`f₂ ∘ u = v ∘ f`. -/
public theorem fibreMap_localizedModuleMap (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (f : M →ₛₗ[φ.toRingHom] N) (f₂ : M₂ →ₛₗ[φ.toRingHom] N₂)
    (u : M →ₗ[A] M₂) (v : N →ₗ[B] N₂) (huv : ∀ m : M, f₂ (u m) = v (f m))
    (y : ProjectiveSpectrum ℬ)
    (z : ModuleFiber (M := M) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ f₂ y
        (LocalizedModule.map
          (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl u z)
      = LocalizedModule.map y.asHomogeneousIdeal.toIdeal.primeCompl v
          (fibreMap φ hφ f y z) := by
  induction z using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.map_mk, fibreMap_mk, fibreMap_mk, LocalizedModule.map_mk, huv]

end Stacks.ProjModuleComparison

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}}
  {ℳ 𝒩 𝒬 : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}

/-- An equality of the underlying linear maps is carried through the construction of the morphism
of associated sheaves on an absolute projective spectrum. -/
private theorem associatedModuleSheafMap_eq_of_eq {S M N : Type u} {σ τ υ : Type u}
    [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
    [SetLike.GradedSMul 𝒮 𝒨]
    [SetLike υ N] [AddSubgroupClass υ N] (𝒩' : ℤ → υ) [DirectSum.Decomposition 𝒩']
    [SetLike.GradedSMul 𝒮 𝒩']
    {φ ψ : M →ₗ[S] N} (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩' i)
    (hψ : ∀ i (m : M), m ∈ 𝒨 i → ψ m ∈ 𝒩' i) (e : φ = ψ) :
    associatedModuleSheafMap 𝒮 𝒨 𝒩' φ hφ = associatedModuleSheafMap 𝒮 𝒨 𝒩' ψ hψ := by
  subst e
  rfl

/-- The morphism of the chart sheaves induced by a homomorphism of graded modules: the morphism
of associated sheaves attached to the induced map of the graded modules of local sections over the
affine open `W` of the base. -/
public noncomputable def moduleChartMap (f : ℳ ⟶ 𝒩) (W : s.base.affineOpens) :
    moduleChart ℳ W ⟶ moduleChart 𝒩 W :=
  associatedModuleSheafMap (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)
    (sectionModuleGrading 𝒩 W.1) (sectionModuleMapₗ f W.1) (sectionModuleMapₗ_mem_grading f W.1)

/-- The identity homomorphism induces the identity morphism of the chart sheaves. -/
public theorem moduleChartMap_id (W : s.base.affineOpens) :
    moduleChartMap (𝟙 ℳ) W = 𝟙 (moduleChart ℳ W) := by
  have e : sectionModuleMapₗ (𝟙 ℳ) W.1 = LinearMap.id :=
    LinearMap.ext fun z ↦ DFunLike.congr_fun (sectionModuleMap_id (ℳ := ℳ) W.1) z
  exact (associatedModuleSheafMap_eq_of_eq (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading ℳ W.1)
      (sectionModuleMapₗ_mem_grading (𝟙 ℳ) W.1) (fun _ _ hz ↦ hz) e).trans
    (associatedModuleSheafMap_id (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1))

/-- A composite of homomorphisms induces the composite of the morphisms of the chart sheaves. -/
public theorem moduleChartMap_comp (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬) (W : s.base.affineOpens) :
    moduleChartMap (f ≫ g) W = moduleChartMap f W ≫ moduleChartMap g W := by
  have e : sectionModuleMapₗ (f ≫ g) W.1
      = (sectionModuleMapₗ g W.1).comp (sectionModuleMapₗ f W.1) :=
    LinearMap.ext fun z ↦ DFunLike.congr_fun (sectionModuleMap_comp f g W.1) z
  exact (associatedModuleSheafMap_eq_of_eq (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒬 W.1)
      (sectionModuleMapₗ_mem_grading (f ≫ g) W.1)
      (fun i z hz ↦ sectionModuleMapₗ_mem_grading g W.1 i _
        (sectionModuleMapₗ_mem_grading f W.1 i z hz)) e).trans
    (associatedModuleSheafMap_comp (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)
      (sectionModuleGrading 𝒩 W.1) (sectionModuleGrading 𝒬 W.1)
      (sectionModuleMapₗ f W.1) (sectionModuleMapₗ_mem_grading f W.1)
      (sectionModuleMapₗ g W.1) (sectionModuleMapₗ_mem_grading g W.1))

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent] in
/-- The chart morphisms commute with the comparisons of the chart sheaves attached to an
inclusion `W ≤ W'` of affine opens of the base. -/
public theorem modulePushforwardMap_moduleChartMap (f : ℳ ⟶ 𝒩)
    {W W' : s.base.affineOpens} (h : W ≤ W') {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W') (moduleChart ℳ W') V)) :
    ((modulePushforwardMap 𝒩 h).val.app (op V)).hom
        ((((Scheme.Modules.pushforward (relativeProjChart s W')).map
          (moduleChartMap f W')).val.app (op V)).hom y)
      = (((Scheme.Modules.pushforward (relativeProjChart s W)).map
          (moduleChartMap f W)).val.app (op V)).hom
          (((modulePushforwardMap ℳ h).val.app (op V)).hom y) :=
  Subtype.ext <| funext fun x ↦
    fibreMap_localizedModuleMap (gradedSectionRestriction s W.1 W'.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
      (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ 𝒩 h)
      (sectionModuleMapₗ f W'.1) (sectionModuleMapₗ f W.1)
      (fun m ↦ (sectionModuleMap_restrict f h m).symm) x.1
      (y.1 ⟨_, comapFun_gradedSectionRestriction_mem s h x⟩)

/-- The chart morphisms as a morphism of the locally directed glueing datum of the chart
sheaves. -/
public noncomputable def modulesDirectedGlueHom (f : ℳ ⟶ 𝒩) :
    ModulesDirectedGlueData.Hom (modulesDirectedGlueData ℳ) (modulesDirectedGlueData 𝒩) where
  chart := moduleChartMap f
  chart_trans := by
    intro W W' h V hV t
    refine (bijective_modulePushforwardMap_app 𝒩 h hV).1 ?_
    refine (modulePushforwardMap_moduleChartMap f h (moduleTransEquiv ℳ h hV t)).trans ?_
    refine (congrArg
      (fun z ↦ (((Scheme.Modules.pushforward (relativeProjChart s W)).map
          (moduleChartMap f W)).val.app (op V)).hom z)
      (modulePushforwardMap_moduleTransEquiv ℳ h hV t)).trans ?_
    exact (modulePushforwardMap_moduleTransEquiv 𝒩 h hV _).symm

/-- The morphism `ℳ̃ ⟶ 𝒩̃` induced by a homomorphism of graded modules, glued from the
morphisms of the chart sheaves. -/
public noncomputable def moduleSheafMap (f : ℳ ⟶ 𝒩) : moduleSheaf ℳ ⟶ moduleSheaf 𝒩 :=
  (modulesDirectedGlueHom f).glued

/-- The induced morphism is the chart morphism on sections over an open of the relative
projective spectrum lying in the chart over `W`, read through the identification of those
sections with the sections of the chart sheaf. -/
public theorem moduleSheafMap_chartSec (f : ℳ ⟶ 𝒩) (W : s.base.affineOpens)
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (x : ToType ((moduleSheaf ℳ).val.obj (op V))) :
    ((modulesDirectedGlueData 𝒩).chartSectionsIso W hV).hom
        (((moduleSheafMap f).val.app (op V)).hom x)
      = (((Scheme.Modules.pushforward (relativeProjChart s W)).map
          (moduleChartMap f W)).val.app (op V)).hom
          (((modulesDirectedGlueData ℳ).chartSectionsIso W hV).hom x) :=
  (modulesDirectedGlueHom f).chartSectionsIso_glued W hV x

/-- The identity homomorphism of graded modules induces the identity morphism of the attached
sheaves. -/
public theorem moduleSheafMap_id : moduleSheafMap (𝟙 ℳ) = 𝟙 (moduleSheaf ℳ) :=
  (modulesDirectedGlueHom (𝟙 ℳ)).glued_eq_id fun W ↦ moduleChartMap_id W

/-- A composite of homomorphisms of graded modules induces the composite of the morphisms of the
attached sheaves. -/
public theorem moduleSheafMap_comp [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent]
    (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬) :
    moduleSheafMap (f ≫ g) = moduleSheafMap f ≫ moduleSheafMap g :=
  (modulesDirectedGlueHom f).glued_eq_comp (modulesDirectedGlueHom g)
    (modulesDirectedGlueHom (f ≫ g)) fun W ↦ moduleChartMap_comp f g W

/-! ### The functor -/

variable (s) in
/-- The category of quasi-coherent graded modules over the graded algebra of a relative `Proj`
situation: the graded modules all of whose homogeneous pieces are quasi-coherent, with all
homomorphisms of graded modules between them. -/
public abbrev QcohGradedModule : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra =>
      ∀ n : ℤ, (ℳ.piece n).IsQuasicoherent)

variable (s) in
/-- The construction `ℳ ↦ ℳ̃` is functorial in `ℳ`: it is a functor from the quasi-coherent
graded modules over the graded algebra `𝒜` to the modules over the relative projective spectrum
`Proj_S(𝒜)`, sending `ℳ` to the sheaf `Stacks.RelativeProj.Situation.moduleSheaf ℳ` and a
homomorphism to the glued morphism `Stacks.RelativeProj.Situation.moduleSheafMap` of the chart
morphisms. -/
@[stacks 01O7 "property (4): the construction ℳ ↦ ℳ̃ is a functor from quasi-coherent graded
modules over 𝒜 to modules on the relative projective spectrum"]
public noncomputable def moduleSheafFunctor : QcohGradedModule s ⥤ (relativeProj s).Modules where
  obj ℳ :=
    haveI : ∀ n : ℤ, (ℳ.obj.piece n).IsQuasicoherent := ℳ.property
    moduleSheaf ℳ.obj
  map {ℳ 𝒩} φ :=
    haveI : ∀ n : ℤ, (ℳ.obj.piece n).IsQuasicoherent := ℳ.property
    haveI : ∀ n : ℤ, (𝒩.obj.piece n).IsQuasicoherent := 𝒩.property
    moduleSheafMap φ.hom
  map_id ℳ :=
    haveI : ∀ n : ℤ, (ℳ.obj.piece n).IsQuasicoherent := ℳ.property
    moduleSheafMap_id
  map_comp {ℳ 𝒩 𝒬} φ χ :=
    haveI : ∀ n : ℤ, (ℳ.obj.piece n).IsQuasicoherent := ℳ.property
    haveI : ∀ n : ℤ, (𝒩.obj.piece n).IsQuasicoherent := 𝒩.property
    haveI : ∀ n : ℤ, (𝒬.obj.piece n).IsQuasicoherent := 𝒬.property
    moduleSheafMap_comp φ.hom χ.hom

/-- The functor `ℳ ↦ ℳ̃` on objects is `Stacks.RelativeProj.Situation.moduleSheaf`. -/
public theorem moduleSheafFunctor_obj
    (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
    [hℳ : ∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] :
    (moduleSheafFunctor s).obj ⟨ℳ, hℳ⟩ = moduleSheaf ℳ := rfl

/-- The functor `ℳ ↦ ℳ̃` on morphisms is `Stacks.RelativeProj.Situation.moduleSheafMap`. -/
public theorem moduleSheafFunctor_map
    {ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}
    [hℳ : ∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [h𝒩 : ∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]
    (f : ℳ ⟶ 𝒩) :
    (moduleSheafFunctor s).map (ObjectProperty.homMk f :
        (⟨ℳ, hℳ⟩ : QcohGradedModule s) ⟶ ⟨𝒩, h𝒩⟩) = moduleSheafMap f := rfl

end Stacks.RelativeProj.Situation

end
