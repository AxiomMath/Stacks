module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionScalar
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.BasicOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorGlueChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafDegreeZero

/-!
# The canonical map `π^*ℳ_0 ⟶ ℳ̃` on a relative projective spectrum

Let `s` be a relative `Proj` situation (Situation 01NN) with structure morphism
`π : Proj_S(𝒜) ⟶ S`, and let `ℳ` be a graded `𝒜`-module with quasi-coherent homogeneous pieces,
so that the sheaf `ℳ̃` of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheaf.lean` is defined.
Property (3) of Tag 01O7 is a canonical map

`π^*ℳ_0 ⟶ ℳ̃`.

This file constructs it as the transpose, across `π^* ⊣ π_*`, of a morphism `ℳ_0 ⟶ π_* ℳ̃` of
sheaves of modules on `S`. That morphism is given on the sections over the affine opens `W` of
`S`, which form a basis, by `m ↦ m / 1`: the part `π⁻¹(W)` of the relative projective spectrum
lying over `W` is the chart `Proj 𝒜(W)`, on which `ℳ̃` is the sheaf attached to the graded module
of sections `Γ(W, ℳ)`, and a section `m` of `ℳ_0` over `W` is a degree-zero element of it, hence
names the global section `m / 1` of Tag 01M7.

Three facts make this a morphism. The map is additive. It is linear over `Γ(W, 𝒪_S)`, which acts
on `π_* ℳ̃` through `π^♯`: a function `r` on `W` pulls back to the chart as the degree-zero
fraction `r / 1` of its image in `𝒜(W)_0`
(`Stacks.RelativeProj.Situation.relativeProjToBase_app_relativeProjChart_app`), and `r` acts on
`Γ(W, ℳ_0)` as its image in `𝒜(W)_0` acts on `Γ(W, ℳ)`. And it commutes with restriction to a
smaller affine open, which is the glue square
`Stacks.RelativeProj.Situation.modulePushforwardMap_degreeZeroToGlobalSections` read through the
identifications of the sections of `ℳ̃` with those of the chart sheaves.

## Main definitions

* `Stacks.RelativeProj.Situation.degreeZeroSection`: the section `m / 1` of `ℳ̃` over `π⁻¹(W)`.
* `Stacks.RelativeProj.Situation.degreeZeroPushforwardHom`: the morphism `ℳ_0 ⟶ π_* ℳ̃`.
* `Stacks.RelativeProj.Situation.degreeZeroSheafMap`: **the canonical map `π^*ℳ_0 ⟶ ℳ̃` of
  property (3) of Tag 01O7.**

## Main results

* `Stacks.RelativeProj.Situation.degreeZeroPushforwardHom_app_apply`: on the sections over an
  affine open `W`, the transpose of the canonical map is `m ↦ m / 1`.
* `Stacks.RelativeProj.Situation.existsUnique_degreeZeroSheafMap`: the canonical map is the only
  morphism `π^*ℳ_0 ⟶ ℳ̃` with that description.
* `Stacks.RelativeProj.Situation.chartSectionsIso_hom_degreeZeroSection`: read on the chart over
  `W`, the section `m / 1` of `ℳ̃` is the global section `m / 1` of the sheaf attached to
  `Γ(W, ℳ)`.

## Implementation notes

The linearity of the scalars is checked on bare variables first
(`appLE_comp_spec_map_fromSpec`): stated at the relative projective spectrum, the identification
of the preimage of a composite with an iterated preimage has to be unfolded through the
non-exposed definitions of the glued scheme, which exceeds the heartbeat budget.

The sections of `π_* ℳ̃` over `W` are given the name
`Stacks.RelativeProj.Situation.pushforwardSections`, so that the module structure over the
functions on `W` is the one instance search finds, and not the module structure of `ℳ̃` over the
functions on `π⁻¹(W)` lying underneath it.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjModuleComparison Stacks.SheafOfModules Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

variable {S M σ τ : Type u}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

omit [DirectSum.Decomposition 𝒨] in
/-- **A degree-zero scalar acts on the global section `m / 1` through the structure morphism**:
for `a` of degree zero and `m` of degree zero, the global section of `M̃` attached to `a · m` is
the function `π^♯(a)` pulled back along `π : Proj 𝒮 ⟶ Spec 𝒮_0` times the one attached to
`m`. -/
public theorem degreeZeroToGlobalSections_pullbackDegreeZero (a : 𝒮 0) (m am : 𝒨 0)
    (ham : (am : M) = (a : S) • (m : M)) :
    degreeZeroToGlobalSections 𝒮 𝒨 am =
      Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeZero 𝒮 a •
        degreeZeroToGlobalSections 𝒮 𝒨 m := by
  refine (associatedModuleSheafSectionsEquiv 𝒮 𝒨 ⊤).injective ?_
  refine Subtype.ext (funext fun x => ?_)
  have hscalar : HomogeneousLocalization.val
      ((Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeZero 𝒮 a).1 x) =
      algebraMap S (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (a : S) :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val 𝒮 a x.1
  change LocalizedModule.mk (am : M) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
    HomogeneousLocalization.val
      ((Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeZero 𝒮 a).1 x) •
      LocalizedModule.mk (m : M) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [ham, hscalar, algebraMap_smul, LocalizedModule.smul'_mk]

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

namespace Stacks.RelativeProj.Situation

/-- Two equal morphisms of schemes induce the same map of sections between two given opens. -/
theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- A morphism `X ⟶ Spec A ⟶ Spec Γ(Y, U) ⟶ Y` through an affine open `U`, induced by a ring map
`φ : Γ(Y, U) ⟶ A`, acts on the functions on `U` as `φ` followed by the global sections of
`X ⟶ Spec A`. Stated for arbitrary schemes, so that no concrete scheme is unfolded. -/
private theorem appLE_comp_spec_map_fromSpec {X Y : Scheme.{u}} {A : CommRingCat.{u}}
    {U : Y.Opens} (hU : IsAffineOpen U) (g : X ⟶ Spec A) (φ : Γ(Y, U) ⟶ A) (V : X.Opens)
    (e : V ≤ ((g ≫ Spec.map φ) ≫ hU.fromSpec) ⁻¹ᵁ U) :
    ((g ≫ Spec.map φ) ≫ hU.fromSpec).appLE U V e =
      φ ≫ (Scheme.ΓSpecIso A).inv ≫ g.appLE ⊤ V le_top := by
  have e₁ : V ≤ (g ≫ Spec.map φ) ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) := e
  have e₂ : V ≤ (g ≫ Spec.map φ) ⁻¹ᵁ ⊤ := le_top
  calc ((g ≫ Spec.map φ) ≫ hU.fromSpec).appLE U V e
      = hU.fromSpec.app U ≫ (g ≫ Spec.map φ).appLE (hU.fromSpec ⁻¹ᵁ U) V e₁ :=
        Scheme.Hom.comp_appLE _ _ _ _ _
    _ = (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ ((Spec Γ(Y, U)).presheaf.map
          (eqToHom hU.fromSpec_preimage_self).op ≫
          (g ≫ Spec.map φ).appLE (hU.fromSpec ⁻¹ᵁ U) V e₁) := by
        rw [hU.fromSpec_app_self, Category.assoc]
    _ = (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (g ≫ Spec.map φ).appLE ⊤ V e₂ := by
        rw [Scheme.Hom.map_appLE]
    _ = (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (Spec.map φ).app ⊤ ≫ g.appLE ⊤ V le_top := by
        rw [Scheme.Hom.comp_appLE]
        rfl
    _ = φ ≫ (Scheme.ΓSpecIso A).inv ≫ g.appLE ⊤ V le_top :=
        (Scheme.ΓSpecIso_inv_naturality_assoc φ _).symm

variable (s : Situation.{u})

/-- The chart over `W` followed by the structure morphism is the structure morphism of
`Proj 𝒜(W)` over `Spec 𝒜(W)_0`, followed by `Spec 𝒜(W)_0 ⟶ Spec Γ(W, 𝒪) ≅ W ⊆ S`. -/
public theorem relativeProjChart_comp_relativeProjToBase (W : s.base.affineOpens) :
    relativeProjChart s W ≫ relativeProjToBase s =
      Proj.toSpecZero (s.sectionRingGrading W.1) ≫ Spec.map (sectionRingZeroMap s W.1) ≫
        W.2.fromSpec := by
  refine (relativeProjChart_isPullback s W).w.trans ?_
  change (Proj.toSpecZero (s.sectionRingGrading W.1) ≫ Spec.map (sectionRingZeroMap s W.1) ≫
    W.2.isoSpec.inv) ≫ W.1.ι = _
  rw [Category.assoc, Category.assoc]
  rfl

/-- **A function on an affine open `W` of the base, pulled back to the chart over `W`, is the
degree-zero fraction of its image in `𝒜(W)_0`.** The structure morphism of the relative
projective spectrum followed by the chart over `W` acts on the functions on `W` as the
identification `Γ(W, 𝒪) ⟶ 𝒜(W)_0` followed by the structure morphism of `Proj 𝒜(W)` over
`Spec 𝒜(W)_0`. -/
public theorem relativeProjToBase_app_relativeProjChart_app (W : s.base.affineOpens) :
    (relativeProjToBase s).app W.1 ≫
        (relativeProjChart s W).app (relativeProjToBase s ⁻¹ᵁ W.1) =
      sectionRingZeroMap s W.1 ≫
        Stacks.AlgebraicGeometry.ProjShiftedSections.degreeZeroPullbackHom
          (s.sectionRingGrading W.1) ≫
        (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).presheaf.map
          (homOfLE le_top).op := by
  have h₁ : (relativeProjToBase s).app W.1 ≫
        (relativeProjChart s W).app (relativeProjToBase s ⁻¹ᵁ W.1) =
      (relativeProjChart s W ≫ relativeProjToBase s).appLE W.1 _ le_rfl :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm
  refine h₁.trans ((appLE_eq_of_eq ((relativeProjChart_comp_relativeProjToBase s W).trans
    (Category.assoc _ _ _).symm) _ _ _).trans
      ((appLE_comp_spec_map_fromSpec W.2 _ _ _ _).trans ?_))
  rw [Stacks.AlgebraicGeometry.ProjShiftedSections.degreeZeroPullbackHom, Category.assoc]
  rfl

variable {s} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)

/-- The part of the relative projective spectrum lying over an affine open `W` of the base lies in
the chart over `W`. -/
public theorem preimage_le_opensRange_relativeProjChart (W : s.base.affineOpens) :
    relativeProjToBase s ⁻¹ᵁ W.1 ≤ (relativeProjChart s W).opensRange :=
  (opensRange_relativeProjChart s W).ge

/-- A section of the degree-zero piece of `ℳ` over an open `U` of the base, read as a degree-zero
element of the graded module of sections of `ℳ` over `U`. -/
public def degreeZeroSectionElem (U : s.base.Opens) (m : (ℳ.piece 0).val.obj (op U)) :
    sectionModuleGrading ℳ U 0 :=
  ⟨DirectSum.of (sectionModulePieces ℳ U) 0 m, mem_sectionModuleGrading_of ℳ U m⟩

/-- A function on `U` acts on the degree-zero element attached to a section of `ℳ_0` through its
image in the degree-zero part of the graded ring of sections over `U`. -/
public theorem degreeZeroSectionElem_smul (U : s.base.Opens)
    (r : s.base.ringCatSheaf.obj.obj (op U))
    (m : (ℳ.piece 0).val.obj (op U)) :
    ((degreeZeroSectionElem ℳ U (r • m) : sectionModuleGrading ℳ U 0) : sectionModule ℳ U) =
      ((sectionRingZeroMap s U r : s.sectionRingGrading U 0) : s.sectionRing U) •
        ((degreeZeroSectionElem ℳ U m : sectionModuleGrading ℳ U 0) : sectionModule ℳ U) := by
  have h : ((sectionRingZeroMap s U r : s.sectionRingGrading U 0) : s.sectionRing U) =
      s.sectionRingBaseMap U r :=
    congrArg Subtype.val
      (GradedRing.projZeroRingHom'_apply_coe _ ⟨_, sectionRingBaseMap_mem_zero s U r⟩)
  rw [h]
  exact (sectionRingBaseMap_smul_of ℳ U 0 r m).symm

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- **The section `m / 1` of the chart sheaf over `W`**, attached to a section `m` of `ℳ_0` over an
affine open `W` of the base, on the part of the relative projective spectrum lying over `W`. -/
public def degreeZeroChartSection (W : s.base.affineOpens) (m : (ℳ.piece 0).val.obj (op W.1)) :
    ToType ((moduleChart ℳ W).val.obj
      (op (relativeProjChart s W ⁻¹ᵁ (relativeProjToBase s ⁻¹ᵁ W.1)))) :=
  (moduleChart ℳ W).val.map (homOfLE le_top).op
    (degreeZeroToGlobalSections (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)
      (degreeZeroSectionElem ℳ W.1 m))

/-- **The section `m / 1` of `ℳ̃`** over the part of the relative projective spectrum lying over an
affine open `W` of the base, attached to a section `m` of `ℳ_0` over `W`: the section
`Stacks.RelativeProj.Situation.degreeZeroChartSection` of the chart sheaf, read in `ℳ̃` through
the identification of the sections of `ℳ̃` over an open lying in the chart over `W`. -/
public def degreeZeroSection (W : s.base.affineOpens) (m : (ℳ.piece 0).val.obj (op W.1)) :
    ToType ((moduleSheaf ℳ).val.obj (op (relativeProjToBase s ⁻¹ᵁ W.1))) :=
  ((modulesDirectedGlueData ℳ).chartSectionsIso W
    (preimage_le_opensRange_relativeProjChart W)).inv.hom (degreeZeroChartSection ℳ W m)

/-- A function on an affine open `W` of the base, pulled back to the part of the relative
projective spectrum lying over `W`, named at the type the scalars of the sections of a sheaf of
modules there take. -/
public def baseFunction (W : s.base.affineOpens) (r : s.base.ringCatSheaf.obj.obj (op W.1)) :
    ToType ((relativeProj s).ringCatSheaf.obj.obj (op (relativeProjToBase s ⁻¹ᵁ W.1))) :=
  (relativeProjToBase s).app W.1 r

/-- A function on an affine open `W` of the base, pulled back to the chart over `W`, named at the
type the scalars of the sections of a sheaf of modules on the chart take. -/
public def chartBaseFunction (W : s.base.affineOpens) (r : s.base.ringCatSheaf.obj.obj (op W.1)) :
    ToType ((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).ringCatSheaf.obj.obj
      (op (relativeProjChart s W ⁻¹ᵁ (relativeProjToBase s ⁻¹ᵁ W.1)))) :=
  (relativeProjChart s W).app (relativeProjToBase s ⁻¹ᵁ W.1) (baseFunction W r)

omit [∀ (n : ℤ), (ℳ.piece n).IsQuasicoherent] in
/-- **The section `m / 1` of the chart sheaf is linear over the functions on the base**, which act
on the chart through the structure morphism followed by the chart. -/
public theorem degreeZeroChartSection_smul (W : s.base.affineOpens)
    (r : s.base.ringCatSheaf.obj.obj (op W.1)) (m : (ℳ.piece 0).val.obj (op W.1)) :
    degreeZeroChartSection ℳ W (r • m) =
      chartBaseFunction W r • degreeZeroChartSection ℳ W m := by
  have hfun : chartBaseFunction W r =
      (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).presheaf.map (homOfLE le_top).op
        (Stacks.AlgebraicGeometry.ProjShiftedSections.degreeZeroPullbackHom
          (s.sectionRingGrading W.1) (sectionRingZeroMap s W.1 r)) :=
    congrArg (fun k => k r) (relativeProjToBase_app_relativeProjChart_app s W)
  have hsec := degreeZeroToGlobalSections_pullbackDegreeZero (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionRingZeroMap s W.1 r) (degreeZeroSectionElem ℳ W.1 m)
    (degreeZeroSectionElem ℳ W.1 (r • m)) (degreeZeroSectionElem_smul ℳ W.1 r m)
  refine (congrArg (fun z => (moduleChart ℳ W).val.map (homOfLE le_top).op z) hsec).trans ?_
  refine (PresheafOfModules.map_smul (moduleChart ℳ W).val (homOfLE le_top).op _ _).trans ?_
  exact congrArg (fun t => t • degreeZeroChartSection ℳ W m) hfun.symm

omit [∀ (n : ℤ), (ℳ.piece n).IsQuasicoherent] in
/-- The section `m / 1` of the chart sheaf is additive in `m`. -/
public theorem degreeZeroChartSection_add (W : s.base.affineOpens)
    (m m' : (ℳ.piece 0).val.obj (op W.1)) :
    degreeZeroChartSection ℳ W (m + m') =
      degreeZeroChartSection ℳ W m + degreeZeroChartSection ℳ W m' := by
  have helem : degreeZeroSectionElem ℳ W.1 (m + m') =
      degreeZeroSectionElem ℳ W.1 m + degreeZeroSectionElem ℳ W.1 m' :=
    Subtype.ext (map_add (DirectSum.of (sectionModulePieces ℳ W.1) 0) m m')
  refine (congrArg (fun z => (moduleChart ℳ W).val.map (homOfLE le_top).op
    (degreeZeroToGlobalSections (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1) z))
      helem).trans ?_
  refine (congrArg (fun z => (moduleChart ℳ W).val.map (homOfLE le_top).op z)
    (map_add (degreeZeroToGlobalSections (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1)) _ _)).trans ?_
  exact map_add ((moduleChart ℳ W).val.map (homOfLE le_top).op).hom _ _

/-- **The section `m / 1` of `ℳ̃` is linear over the functions on the base**, which act on `ℳ̃`
through the structure morphism. -/
public theorem degreeZeroSection_smul (W : s.base.affineOpens)
    (r : s.base.ringCatSheaf.obj.obj (op W.1)) (m : (ℳ.piece 0).val.obj (op W.1)) :
    degreeZeroSection ℳ W (r • m) = baseFunction W r • degreeZeroSection ℳ W m := by
  unfold degreeZeroSection
  rw [degreeZeroChartSection_smul]
  exact ((modulesDirectedGlueData ℳ).chartSectionsIso W
    (preimage_le_opensRange_relativeProjChart W)).inv.hom.map_smul (baseFunction W r)
      (degreeZeroChartSection ℳ W m)

/-- The section `m / 1` of `ℳ̃` is additive in `m`. -/
public theorem degreeZeroSection_add (W : s.base.affineOpens)
    (m m' : (ℳ.piece 0).val.obj (op W.1)) :
    degreeZeroSection ℳ W (m + m') = degreeZeroSection ℳ W m + degreeZeroSection ℳ W m' := by
  unfold degreeZeroSection
  rw [degreeZeroChartSection_add]
  exact map_add _ _ _

/-- The sections of `π_* ℳ̃` over an affine open `W` of the base, as a module over the functions
on `W`: a named object, so that instance search sees the module structure of the pushforward
rather than that of `ℳ̃` underneath. -/
public def pushforwardSections (W : s.base.affineOpens) :
    ModuleCat (s.base.ringCatSheaf.obj.obj (op W.1)) :=
  ((Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ)).val.obj (op W.1)

/-- **The map `ℳ_0(W) ⟶ (π_* ℳ̃)(W)`, `m ↦ m / 1`**, as a linear map over the functions on `W`. -/
public def degreeZeroSectionLinearMap (W : s.base.affineOpens) :
    (ℳ.piece 0).val.obj (op W.1) →ₗ[s.base.ringCatSheaf.obj.obj (op W.1)]
      pushforwardSections ℳ W where
  toFun := degreeZeroSection ℳ W
  map_add' := degreeZeroSection_add ℳ W
  map_smul' := degreeZeroSection_smul ℳ W

/-- `Stacks.RelativeProj.Situation.degreeZeroSectionLinearMap` as a morphism of modules. -/
public def degreeZeroSectionHom (W : s.base.affineOpens) :
    (ℳ.piece 0).val.obj (op W.1) ⟶ pushforwardSections ℳ W :=
  ModuleCat.ofHom (X := (ℳ.piece 0).val.obj (op W.1)) (Y := pushforwardSections ℳ W)
    (degreeZeroSectionLinearMap ℳ W)

/-- `Stacks.RelativeProj.Situation.degreeZeroSectionHom` is `m ↦ m / 1`. -/
public theorem degreeZeroSectionHom_apply (W : s.base.affineOpens)
    (m : (ℳ.piece 0).val.obj (op W.1)) :
    (degreeZeroSectionHom ℳ W).hom m = degreeZeroSection ℳ W m := rfl

/-- An isomorphism of modules cancels its inverse on elements. -/
public theorem iso_hom_inv_apply {R : Type u} [Ring R] {X Y : ModuleCat.{u} R} (e : X ≅ Y)
    (y : Y) : e.hom.hom (e.inv.hom y) = y :=
  congrArg (fun k : Y ⟶ Y => k.hom y) e.inv_hom_id

/-- An isomorphism of modules cancels its forward map on elements. -/
private theorem iso_inv_hom_apply {R : Type u} [Ring R] {X Y : ModuleCat.{u} R} (e : X ≅ Y)
    (x : X) : e.inv.hom (e.hom.hom x) = x :=
  congrArg (fun k : X ⟶ X => k.hom x) e.hom_inv_id

/-- Two successive restrictions of a section of a sheaf of modules are one restriction. -/
private theorem map_map_le {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens} (hAB : A ≤ B)
    (hBC : B ≤ C) (x : ToType (M.val.obj (op C))) :
    M.val.map (homOfLE hAB).op (M.val.map (homOfLE hBC).op x) =
      M.val.map (homOfLE (hAB.trans hBC)).op x := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- **The sections `m / 1` of `ℳ̃` commute with restriction**: for affine opens `W' ≤ W` of the
base, the section attached to the restriction of `m` to `W'` is the restriction of the section
attached to `m`. This is the compatibility of the family `degreeZeroSectionHom` with the
restriction maps between the affine opens of the base. -/
public theorem degreeZeroSection_restrict {W W' : s.base.affineOpens} (h : W'.1 ≤ W.1)
    (m : (ℳ.piece 0).val.obj (op W.1)) :
    degreeZeroSection ℳ W' ((ℳ.piece 0).val.map (homOfLE h).op m) =
      ((Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ)).val.map
        (homOfLE h).op (degreeZeroSection ℳ W m) := by
  have hV' := preimage_le_opensRange_relativeProjChart W'
  have hV := preimage_le_opensRange_relativeProjChart W
  have hle : relativeProjToBase s ⁻¹ᵁ W'.1 ≤ relativeProjToBase s ⁻¹ᵁ W.1 :=
    (relativeProjToBase s).preimage_mono h
  set z := ((Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ)).val.map
    (homOfLE h).op (degreeZeroSection ℳ W m)
  have key : ((modulesDirectedGlueData ℳ).chartSectionsIso W' hV').hom.hom z =
      degreeZeroChartSection ℳ W' ((ℳ.piece 0).val.map (homOfLE h).op m) := by
    refine (modulePushforwardMap_chartSectionsIso ℳ (W := W') (W' := W) h hV' z).symm.trans ?_
    have hres := (modulesDirectedGlueData ℳ).toModulesGlueData.chartSectionsIso_restrict W hV hle
      (degreeZeroSection ℳ W m)
    have hstep : ((Scheme.Modules.pushforward (relativeProjChart s W)).obj
        (moduleChart ℳ W)).val.restrictₛₗ (homOfLE hle).op (degreeZeroChartSection ℳ W m) =
        (moduleChart ℳ W).val.map (homOfLE le_top).op
          (degreeZeroToGlobalSections (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)
            (degreeZeroSectionElem ℳ W.1 m)) :=
      map_map_le (moduleChart ℳ W) ((relativeProjChart s W).preimage_mono hle) le_top _
    refine (congrArg (fun t => ((modulePushforwardMap ℳ (W := W') (W' := W) h).val.app
      (op (relativeProjToBase s ⁻¹ᵁ W'.1))).hom t) (hres.trans
        ((congrArg (((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (moduleChart ℳ W)).val.restrictₛₗ (homOfLE hle).op)
          (iso_hom_inv_apply ((modulesDirectedGlueData ℳ).chartSectionsIso W hV)
            (degreeZeroChartSection ℳ W m))).trans hstep))).trans ?_
    refine (modulePushforwardMap_degreeZeroToGlobalSections (ℳ := ℳ) (W := W') (W' := W) h
      (V := relativeProjToBase s ⁻¹ᵁ W'.1) (degreeZeroSectionElem ℳ W.1 m)).trans ?_
    refine congrArg (fun e => (moduleChart ℳ W').val.map (homOfLE le_top).op
      (degreeZeroToGlobalSections (s.sectionRingGrading W'.1) (sectionModuleGrading ℳ W'.1) e))
        (Subtype.ext ?_)
    exact sectionModuleRestrict_of ℳ h m
  exact (congrArg (fun y => ((modulesDirectedGlueData ℳ).chartSectionsIso W' hV').inv.hom y)
    key).symm.trans (iso_inv_hom_apply ((modulesDirectedGlueData ℳ).chartSectionsIso W' hV') z)

/-- **Read on the chart over `W`, the section `m / 1` of `ℳ̃` is the global section `m / 1`** of
the sheaf attached to the graded module of sections of `ℳ` over `W`. -/
public theorem chartSectionsIso_hom_degreeZeroSection (W : s.base.affineOpens)
    (m : (ℳ.piece 0).val.obj (op W.1)) :
    ((modulesDirectedGlueData ℳ).chartSectionsIso W
        (preimage_le_opensRange_relativeProjChart W)).hom.hom (degreeZeroSection ℳ W m) =
      degreeZeroChartSection ℳ W m :=
  iso_hom_inv_apply _ _

/-- The affine opens of the base, as a family of opens, form a basis of its topology. -/
public theorem isBasis_range_affineOpens :
    Opens.IsBasis (Set.range (fun W : s.base.affineOpens => W.1)) := by
  rw [Subtype.range_coe]
  exact s.base.isBasis_affineOpens

/-- The family `degreeZeroSectionHom` is compatible with the restriction maps between the affine
opens of the base. -/
public theorem isCompatibleOnBasis_degreeZeroSectionHom :
    Stacks.BasisRestriction.IsCompatibleOnBasis (ℳ.piece 0)
      ((Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ))
      (fun W : s.base.affineOpens => W.1) (fun W => degreeZeroSectionHom ℳ W) :=
  fun _ _ h m => degreeZeroSection_restrict ℳ h m

/-- **The adjoint form of the canonical map of property (3) of Tag 01O7**: the morphism
`ℳ_0 ⟶ π_* ℳ̃` of sheaves of modules on the base which on the sections over every affine open `W`
is `m ↦ m / 1`. -/
public def degreeZeroPushforwardHom :
    ℳ.piece 0 ⟶ (Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ) :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis (ℳ.piece 0)
    ((Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ))
    (fun W : s.base.affineOpens => W.1) (fun W => degreeZeroSectionHom ℳ W)
    (isBasis_range_affineOpens (s := s)) (isCompatibleOnBasis_degreeZeroSectionHom ℳ)

/-- On the sections over an affine open `W` of the base, `ℳ_0 ⟶ π_* ℳ̃` is `m ↦ m / 1`. -/
public theorem degreeZeroPushforwardHom_app_apply (W : s.base.affineOpens)
    (m : (ℳ.piece 0).val.obj (op W.1)) :
    ((degreeZeroPushforwardHom ℳ).val.app (op W.1)).hom m = degreeZeroSection ℳ W m :=
  congrArg (fun k => k.hom m)
    (Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app (ℳ.piece 0)
      ((Scheme.Modules.pushforward (relativeProjToBase s)).obj (moduleSheaf ℳ))
      (fun W : s.base.affineOpens => W.1) (fun W => degreeZeroSectionHom ℳ W)
      (isBasis_range_affineOpens (s := s)) (isCompatibleOnBasis_degreeZeroSectionHom ℳ) W)

/-- **Stacks Project, Tag 01O7, property (3).** The canonical map

`π^*ℳ_0 ⟶ ℳ̃`

on the relative projective spectrum `π : Proj_S(𝒜) ⟶ S`, for a graded `𝒜`-module `ℳ` with
quasi-coherent homogeneous pieces. It is the transpose, across the adjunction `π^* ⊣ π_*`, of
`Stacks.RelativeProj.Situation.degreeZeroPushforwardHom`, the morphism `ℳ_0 ⟶ π_* ℳ̃` which on
the sections over an affine open `W` of the base carries `m` to the section `m / 1` of `ℳ̃` over
`π⁻¹(W)`: under the identification of `ℳ̃` over `π⁻¹(W)` with the sheaf of the graded module of
sections of `ℳ` over `W` on `Proj 𝒜(W)`, this is the global section `m / 1` of Tag 01M7. -/
@[stacks 01O7 "property (3): the canonical map from the pullback of the degree-zero part of a
graded module to its associated sheaf on the relative projective spectrum",
  ega "II 3.3.2" "Map (3.3.2.4) for n = 0"]
public def degreeZeroSheafMap :
    (Scheme.Modules.pullback (relativeProjToBase s)).obj (ℳ.piece 0) ⟶ moduleSheaf ℳ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv _ _).symm
    (degreeZeroPushforwardHom ℳ)

/-- The transpose of the canonical map `π^*ℳ_0 ⟶ ℳ̃` across `π^* ⊣ π_*` is `ℳ_0 ⟶ π_* ℳ̃`. -/
public theorem homEquiv_degreeZeroSheafMap :
    (Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv _ _
        (degreeZeroSheafMap ℳ) = degreeZeroPushforwardHom ℳ :=
  Equiv.apply_symm_apply _ _

/-- **The canonical map `π^*ℳ_0 ⟶ ℳ̃` is pinned down by its effect on the sections over the
affine opens of the base**: it is the only morphism whose transpose `ℳ_0 ⟶ π_* ℳ̃` carries a
section `m` of `ℳ_0` over an affine open `W` to the section `m / 1` of `ℳ̃` over `π⁻¹(W)`. -/
public theorem existsUnique_degreeZeroSheafMap :
    ∃! φ : (Scheme.Modules.pullback (relativeProjToBase s)).obj (ℳ.piece 0) ⟶ moduleSheaf ℳ,
      ∀ (W : s.base.affineOpens) (m : (ℳ.piece 0).val.obj (op W.1)),
        ((((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv _ _
          φ).val.app (op W.1)).hom m) = degreeZeroSection ℳ W m := by
  refine ⟨degreeZeroSheafMap ℳ, fun W m => ?_, fun φ hφ => ?_⟩
  · rw [homEquiv_degreeZeroSheafMap]
    exact degreeZeroPushforwardHom_app_apply ℳ W m
  · refine ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProjToBase s)).homEquiv
      _ _).injective ?_
    rw [homEquiv_degreeZeroSheafMap]
    refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _
      (fun W : s.base.affineOpens => W.1) (isBasis_range_affineOpens (s := s)) _ _ fun W => ?_
    exact ModuleCat.hom_ext (LinearMap.ext fun m =>
      (hφ W m).trans (degreeZeroPushforwardHom_app_apply ℳ W m).symm)

end Stacks.RelativeProj.Situation

end
