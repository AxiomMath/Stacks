module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.TensorSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorGlueChart
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjQuasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Stalk

/-!
# Property (6) of Tag 01O7: the canonical map out of the tensor product

Let `s` be a relative `Proj` situation and let `ℳ`, `𝒩` be left graded modules over its graded
algebra with quasi-coherent homogeneous pieces. Property (6) of Tag 01O7 asserts a canonical map

`ℳ̃ ⊗_𝒪 𝒩̃ ⟶ (ℳ ⊗_𝒜 𝒩)~`

on the relative projective spectrum — the relative form of the map of Tag 01MK. This file
constructs it, by glueing the chart members
`Stacks.RelativeProj.Situation.moduleSheafTensorChartMap` along the chart cover.

The glueing is `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, whose
compatibility hypothesis asks that two chart members act equally on the sections over any open of
the relative projective spectrum seen by both charts. That hypothesis is reached in three steps:

* an arbitrary pair of charts is reduced to a nested pair by
  `Stacks.RelativeProj.Situation.localApp_relativeProjChart_eq_of_nested`;
* for a nested pair, an arbitrary section is reduced to the images of pure tensors by
  `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_eq_of_toTensorSheafSection`;
* on the image of a pure tensor the two members are computed, through the identifications of the
  glued sheaves with their chart sheaves, and the resulting identity is the fibre square
  `Stacks.RelativeProj.Situation.modulePushforwardMap_moduleChartTensorMap`.

The map is **not** an isomorphism, and nothing here says it is:
`Stacks.EvenWeightProj.not_isIso_associatedModuleSheafTensorMap` exhibits a graded ring and two
graded modules over it for which the absolute map of Tag 01MK is not invertible.

## Main results

* `Stacks.RelativeProj.Situation.tensorModuleSheafMap`: **the canonical map
  `ℳ̃ ⊗_𝒪 𝒩̃ ⟶ (ℳ ⊗_𝒜 𝒩)~` of property (6) of Tag 01O7.**
* `Stacks.RelativeProj.Situation.existsUnique_tensorModuleSheafMap`: it is the **unique** morphism
  restricting on every chart to the chart member, and
  `Stacks.RelativeProj.Situation.restrictFunctor_map_tensorModuleSheafMap` is that restriction
  property for it.
* `Stacks.RelativeProj.Situation.localApp_moduleSheafTensorChartMap_eq`: the glueing
  compatibility of the chart members over an **arbitrary** pair of affine opens of the base.
* `Stacks.RelativeProj.Situation.localApp_moduleSheafTensorChartMap_eq_of_le` and
  `...localApp_moduleSheafTensorChartMap_eq_of_nested`: the compatibility for a nested pair, on
  the image of a pure tensor and then on an arbitrary section.
* `Stacks.RelativeProj.Situation.chartSectionsIso_localApp_moduleSheafTensorChartMap`: **the chart
  member read on the sections over an open lying in the chart, through the glueing datum**: on the
  image of a pure tensor it is the chart comparison applied to the pure tensor of the chart
  readings of the two sections.
* `Stacks.RelativeProj.Situation.moduleSheafChartIso_hom_map_eqToHom` and
  `...chartSectionsIso_map_eqToHom_moduleSheafChartIso_inv`: the two transports between an open
  lying in a chart and the image of its preimage cancel against the chart identification, so
  reading a section of a glued sheaf through the chart identification is reading it through the
  glueing datum.
* `Stacks.RelativeProj.Situation.moduleSheafTensorChartMap_app_toTensorSheafSection_tmul`: the
  chart member on the image of a pure tensor, with the chart identification of the target on the
  side the glueing compatibility needs it.

## Implementation notes

The transition of the glueing datum of `ℳ̃` is
`Stacks.RelativeProj.Situation.modulePushforwardMap`
(`Stacks.RelativeProj.Situation.modulePushforwardMap_chartSectionsIso`), so the nested identity,
read through the glueing datum on the smaller chart, is exactly the fibre square of
`StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorGlue.lean`. No comparison of the
pushed-forward *tensor* chart sheaves is needed, and none is constructed: the square is only ever
read on the image of a pure tensor, and there the two factors transport separately by their own
`modulePushforwardMap`.

Heartbeats are counted cumulatively over a declaration and cannot be raised in this library, so
every step whose cost is a single large definitional unfolding is a declaration of its own. Two
such crossings occur here: the identification of
`Stacks.RingedSpace.tensorSheafUnit` with
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`, which is made on bare
variables in `Stacks.RelativeProj.Situation.toTensorSheafSection_map`, and the decomposition of
the chart member into its defining composite, which is made in
`StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorGlueChart.lean`. Making either inside a
statement about a relative projective spectrum exceeds the budget.

`AlgebraicGeometry.ProjectiveSpectrum.isPrime` is installed as a local instance at file scope, as
in the other files of this chain: an `attribute [local instance]` inside a namespace does not
survive the `end`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)

## Not done here

Properties (1) to (5), (7) and (8) of Tag 01O7 are elsewhere. The map constructed here is not
compared with the relative tensor product of Tag 01MK in any other presentation, and no
hypothesis under which it becomes an isomorphism is given.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization Stacks.ProjModuleComparison
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped TensorProduct

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ModuleHomGlue

attribute [local instance] sectionModuleDecomposition

/-- Restriction along two morphisms of opens in opposite directions is the identity: the two
opens are then equal and the composite is the identity morphism. -/
private theorem map_map_eq_self {X : Scheme.{u}} (M : X.Modules) {U U' : X.Opens}
    (g₁ : (op U : (TopologicalSpace.Opens X)ᵒᵖ) ⟶ op U')
    (g₂ : (op U' : (TopologicalSpace.Opens X)ᵒᵖ) ⟶ op U)
    (w : ToType (M.val.obj (op U))) :
    (M.val.presheaf.map g₂) ((M.val.presheaf.map g₁) w) = w := by
  obtain rfl : U = U' := le_antisymm (leOfHom g₂.unop) (leOfHom g₁.unop)
  obtain rfl : g₁ = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : g₂ = 𝟙 _ := Subsingleton.elim _ _
  simp
  rfl

/-- An isomorphism of sheaves of modules on a scheme cancels its forward map on sections. -/
private theorem iso_inv_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (Z : (TopologicalSpace.Opens X)ᵒᵖ) (y : ToType (M.val.obj Z)) :
    (e.inv.val.app Z).hom ((e.hom.val.app Z).hom y) = y :=
  congrArg (fun k : M ⟶ M => (k.val.app Z).hom y) e.hom_inv_id

/-- An isomorphism of sheaves of modules on a scheme cancels its inverse on sections. -/
private theorem iso_hom_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (Z : (TopologicalSpace.Opens X)ᵒᵖ) (y : ToType (N.val.obj Z)) :
    (e.hom.val.app Z).hom ((e.inv.val.app Z).hom y) = y :=
  congrArg (fun k : N ⟶ N => (k.val.app Z).hom y) e.inv_hom_id

variable {s : Situation.{u}} (ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]

/-- Reading a section of `ℳ̃` written through the chart identification backwards on the chart it
came from returns it, up to the identification of the preimage of the image of an open with the
open. -/
public theorem chartSectionsIso_moduleSheafChartIso_inv
    (𝒬 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
    [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] (W : s.base.affineOpens)
    (U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (z : ToType ((moduleChart 𝒬 W).val.obj (op U₁))) :
    ((modulesDirectedGlueData 𝒬).chartSectionsIso W
          ((relativeProjChart s W).image_le_opensRange U₁)).hom
        (((moduleSheafChartIso 𝒬 W).inv.val.app (op U₁)).hom z)
      = ((moduleChart 𝒬 W).val.presheaf.map
          (eqToHom ((relativeProjChart s W).preimage_image_eq U₁)).op) z := by
  have hz := (iso_hom_inv_app (moduleSheafChartIso 𝒬 W) (op U₁) z).symm.trans
    ((modulesDirectedGlueData 𝒬).toModulesGlueData.chartIso_hom_app W U₁
      (((moduleSheafChartIso 𝒬 W).inv.val.app (op U₁)).hom z))
  exact ((congrArg (fun w => ((moduleChart 𝒬 W).val.presheaf.map
        (eqToHom ((relativeProjChart s W).preimage_image_eq U₁)).op) w) hz).trans
    (map_map_eq_self (moduleChart 𝒬 W) _ _ _)).symm


/-- **The sheafification unit of a tensor product commutes with restriction**, at the
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` spelling. This is
`Stacks.AlgebraicGeometry.RestrictionSections.tensorSheafUnit_val_map`; the two spellings of the
unit are the same term, and the identification is made here on bare variables because making it
inside a statement about a relative projective spectrum exhausts the heartbeat budget. -/
private theorem toTensorSheafSection_map {X : Scheme.{u}} (A B : X.Modules)
    {U U' : (TopologicalSpace.Opens X)ᵒᵖ} (g : U ⟶ U')
    (a : ToType (A.val.obj U)) (b : ToType (B.val.obj U)) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj
          (B))).val.presheaf.map g)
        (toTensorSheafSection X.toRingedSpace A B U (a ⊗ₜ b))
      = toTensorSheafSection X.toRingedSpace A B U'
          ((A.val.presheaf.map g) a ⊗ₜ (B.val.presheaf.map g) b) :=
  Stacks.AlgebraicGeometry.RestrictionSections.tensorSheafUnit_val_map A B g a b

/-- **Reading a section of `𝒬̃` over an open lying in a chart on that chart**: the chart
identification, applied to the section transported onto the image of the preimage, is the reading
given by the glueing datum. The two transports along the identification of an open inside a chart
with the image of its preimage cancel. -/
public theorem moduleSheafChartIso_hom_map_eqToHom
    (𝒬 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
    [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] (W : s.base.affineOpens)
    {V₀ : (relativeProj s).Opens} (hV : V₀ ≤ (relativeProjChart s W).opensRange)
    (p : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V₀) = V₀)
    (a : ToType ((moduleSheaf 𝒬).val.obj (op V₀))) :
    (((moduleSheafChartIso 𝒬 W).hom.val.app (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
        (((moduleSheaf 𝒬).val.presheaf.map (eqToHom p).op) a))
      = ((modulesDirectedGlueData 𝒬).chartSectionsIso W hV).hom a := by
  refine Eq.trans ((modulesDirectedGlueData 𝒬).toModulesGlueData.chartIso_hom_app W
    (relativeProjChart s W ⁻¹ᵁ V₀) _) ?_
  refine Eq.trans (congrArg _
    ((modulesDirectedGlueData 𝒬).toModulesGlueData.chartSectionsIso_restrict
      W hV (le_of_eq p) a)) ?_
  exact map_map_eq_self (moduleChart 𝒬 W) _ _ _

/-- **Writing a section of the chart sheaf back as a section of `𝒬̃` over an open lying in the
chart**: the inverse chart identification, transported onto the open, is undone by the reading of
the glueing datum. -/
public theorem chartSectionsIso_map_eqToHom_moduleSheafChartIso_inv
    (𝒬 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
    [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] (W : s.base.affineOpens)
    {V₀ : (relativeProj s).Opens} (hV : V₀ ≤ (relativeProjChart s W).opensRange)
    (p : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V₀) = V₀)
    (z : ToType ((moduleChart 𝒬 W).val.obj (op (relativeProjChart s W ⁻¹ᵁ V₀)))) :
    ((modulesDirectedGlueData 𝒬).chartSectionsIso W hV).hom
        (((moduleSheaf 𝒬).val.presheaf.map (eqToHom p.symm).op)
          (((moduleSheafChartIso 𝒬 W).inv.val.app
            (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom z))
      = z := by
  refine Eq.trans ((modulesDirectedGlueData 𝒬).toModulesGlueData.chartSectionsIso_restrict
    W ((relativeProjChart s W).image_le_opensRange _) (le_of_eq p.symm) _) ?_
  refine Eq.trans (congrArg _ (chartSectionsIso_moduleSheafChartIso_inv 𝒬 W _ z)) ?_
  exact map_map_eq_self (moduleChart 𝒬 W) _ _ _


/-- A morphism of bundled modules which is an isomorphism is injective on elements. -/
private theorem hom_inj_of_iso {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    {x y : ToType M} (hxy : (e.hom).hom x = (e.hom).hom y) : x = y :=
  Eq.trans (congrArg (fun k : M ⟶ M => k.hom x) e.hom_inv_id).symm
    (Eq.trans (congrArg (e.inv).hom hxy) (congrArg (fun k : M ⟶ M => k.hom y) e.hom_inv_id))

/-- **The chart member of property (6) on the image of a pure tensor**, in the form the glueing
compatibility is checked in: the inverse chart identification of the target, applied to the chart
comparison of the pure tensor of the chart readings. -/
public theorem moduleSheafTensorChartMap_app_toTensorSheafSection_tmul (W : s.base.affineOpens)
    (U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (a : ToType ((moduleSheaf ℳ).val.obj (op (relativeProjChart s W ''ᵁ U₁))))
    (b : ToType ((moduleSheaf 𝒩).val.obj (op (relativeProjChart s W ''ᵁ U₁)))) :
    letI := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    ((moduleSheafTensorChartMap ℳ 𝒩 W).val.app (op U₁)).hom
        (toTensorSheafSection (relativeProj s).toRingedSpace
          (moduleSheaf ℳ) (moduleSheaf 𝒩) (op (relativeProjChart s W ''ᵁ U₁)) (a ⊗ₜ[_] b))
      = ((moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W).inv.val.app (op U₁)).hom
          (((moduleChartTensorMap ℳ 𝒩 W).val.app (op U₁)).hom
            (toTensorSheafSection
              (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
              (moduleChart ℳ W) (moduleChart 𝒩 W) (op U₁)
              (((moduleSheafChartIso ℳ W).hom.val.app (op U₁)).hom a ⊗ₜ[_]
                ((moduleSheafChartIso 𝒩 W).hom.val.app (op U₁)).hom b))) := by
  let := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  let := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  refine Eq.trans (iso_inv_hom_app (moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W)
    (op U₁) _).symm ?_
  exact congrArg _ (moduleSheafChartIso_moduleSheafTensorChartMap_toTensorSheafSection_tmul
    ℳ 𝒩 W U₁ a b)

/-- The chart member of property (6) applied to the image of a pure tensor transported onto the
image of the preimage of an open. Separated from
`Stacks.RelativeProj.Situation.chartSectionsIso_localApp_moduleSheafTensorChartMap` because the
two steps together exceed a declaration's heartbeat budget. -/
private theorem chartMap_app_map_eqToHom_toTensorSheafSection (W : s.base.affineOpens)
    {V₀ : (relativeProj s).Opens}
    (p : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V₀) = V₀)
    (a : ToType ((moduleSheaf ℳ).val.obj (op V₀)))
    (b : ToType ((moduleSheaf 𝒩).val.obj (op V₀))) :
    letI := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    ((moduleSheafTensorChartMap ℳ 𝒩 W).val.app
          (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
        ((((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(((relativeProj s).toRingedSpace)).presheaf,
                  (((relativeProj s).toRingedSpace)).IsSheaf⟩).obj
                ((moduleSheaf ℳ))).obj ((moduleSheaf 𝒩)))).val.presheaf.map (eqToHom p).op)
          (toTensorSheafSection (relativeProj s).toRingedSpace
            (moduleSheaf ℳ) (moduleSheaf 𝒩) (op V₀) (a ⊗ₜ[_] b)))
      = ((moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W).inv.val.app
            (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
          (((moduleChartTensorMap ℳ 𝒩 W).val.app
              (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
            (toTensorSheafSection
              (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
              (moduleChart ℳ W) (moduleChart 𝒩 W) (op (relativeProjChart s W ⁻¹ᵁ V₀))
              (((moduleSheafChartIso ℳ W).hom.val.app
                    (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
                  (((moduleSheaf ℳ).val.presheaf.map (eqToHom p).op) a) ⊗ₜ[_]
                ((moduleSheafChartIso 𝒩 W).hom.val.app
                    (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
                  (((moduleSheaf 𝒩).val.presheaf.map (eqToHom p).op) b)))) := by
  let := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  let := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  refine Eq.trans (congrArg (fun z => ((moduleSheafTensorChartMap ℳ 𝒩 W).val.app
      (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom z)
    (toTensorSheafSection_map (moduleSheaf ℳ) (moduleSheaf 𝒩) (eqToHom p).op a b)) ?_
  exact moduleSheafTensorChartMap_app_toTensorSheafSection_tmul ℳ 𝒩 W
    (relativeProjChart s W ⁻¹ᵁ V₀) _ _

/-- **The chart member of property (6), read on the sections over an open lying in the chart
through the glueing datum**: on the image of a pure tensor it is the chart comparison applied to
the pure tensor of the chart readings of the two sections. All the transports between an open
inside a chart and the image of its preimage cancel. -/
public theorem chartSectionsIso_localApp_moduleSheafTensorChartMap (W : s.base.affineOpens)
    {V₀ : (relativeProj s).Opens} (hV : V₀ ≤ (relativeProjChart s W).opensRange)
    (p : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V₀) = V₀)
    (a : ToType ((moduleSheaf ℳ).val.obj (op V₀)))
    (b : ToType ((moduleSheaf 𝒩).val.obj (op V₀))) :
    letI := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    ((modulesDirectedGlueData (s.leftGradedTensor ℳ 𝒩)).chartSectionsIso W hV).hom
        (localApp (relativeProjChart s W) (moduleSheafTensorChartMap ℳ 𝒩 W) p
          (toTensorSheafSection (relativeProj s).toRingedSpace
            (moduleSheaf ℳ) (moduleSheaf 𝒩) (op V₀) (a ⊗ₜ[_] b)))
      = ((moduleChartTensorMap ℳ 𝒩 W).val.app
            (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
          (toTensorSheafSection
            (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
            (moduleChart ℳ W) (moduleChart 𝒩 W) (op (relativeProjChart s W ⁻¹ᵁ V₀))
            (((modulesDirectedGlueData ℳ).chartSectionsIso W hV).hom a ⊗ₜ[_]
              ((modulesDirectedGlueData 𝒩).chartSectionsIso W hV).hom b)) := by
  let := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  let := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  refine Eq.trans (congrArg _ (localApp_apply (relativeProjChart s W)
    (moduleSheafTensorChartMap ℳ 𝒩 W) p _)) ?_
  refine Eq.trans (congrArg (fun z => ((modulesDirectedGlueData
      (s.leftGradedTensor ℳ 𝒩)).chartSectionsIso W hV).hom
      (((moduleSheaf (s.leftGradedTensor ℳ 𝒩)).val.presheaf.map (eqToHom p.symm).op) z))
    (chartMap_app_map_eqToHom_toTensorSheafSection ℳ 𝒩 W p a b)) ?_
  refine Eq.trans (chartSectionsIso_map_eqToHom_moduleSheafChartIso_inv
    (s.leftGradedTensor ℳ 𝒩) W hV p _) ?_
  exact congrArg₂ (fun z w => ((moduleChartTensorMap ℳ 𝒩 W).val.app
      (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
    (toTensorSheafSection (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
      (moduleChart ℳ W) (moduleChart 𝒩 W) (op (relativeProjChart s W ⁻¹ᵁ V₀)) (z ⊗ₜ[_] w)))
    (moduleSheafChartIso_hom_map_eqToHom ℳ W hV p a)
    (moduleSheafChartIso_hom_map_eqToHom 𝒩 W hV p b)


/-- **The chart members of property (6) of Tag 01O7 over two nested affine opens of the base
agree on the image of a pure tensor**, over an open of the relative projective spectrum lying in
the smaller chart. -/
public theorem localApp_moduleSheafTensorChartMap_eq_of_le {W W' : s.base.affineOpens} (h : W ≤ W')
    {V₀ : (relativeProj s).Opens}
    (p₁ : relativeProjChart s W ''ᵁ (relativeProjChart s W ⁻¹ᵁ V₀) = V₀)
    (p₂ : relativeProjChart s W' ''ᵁ (relativeProjChart s W' ⁻¹ᵁ V₀) = V₀)
    (a : ToType ((moduleSheaf ℳ).val.obj (op V₀)))
    (b : ToType ((moduleSheaf 𝒩).val.obj (op V₀))) :
    localApp (relativeProjChart s W) (moduleSheafTensorChartMap ℳ 𝒩 W) p₁
        (toTensorSheafSection (relativeProj s).toRingedSpace
          (moduleSheaf ℳ) (moduleSheaf 𝒩) (op V₀) (a ⊗ₜ[_] b))
      = localApp (relativeProjChart s W') (moduleSheafTensorChartMap ℳ 𝒩 W') p₂
        (toTensorSheafSection (relativeProj s).toRingedSpace
          (moduleSheaf ℳ) (moduleSheaf 𝒩) (op V₀) (a ⊗ₜ[_] b)) := by
  have hV : V₀ ≤ (relativeProjChart s W).opensRange :=
    (le_of_eq p₁.symm).trans ((relativeProjChart s W).image_le_opensRange _)
  have hV' : V₀ ≤ (relativeProjChart s W').opensRange :=
    hV.trans (opensRange_relativeProjChart_mono s h)
  refine hom_inj_of_iso
    ((modulesDirectedGlueData (s.leftGradedTensor ℳ 𝒩)).chartSectionsIso W hV) ?_
  refine Eq.trans (chartSectionsIso_localApp_moduleSheafTensorChartMap ℳ 𝒩 W hV p₁ a b) ?_
  refine Eq.trans ?_ (modulePushforwardMap_chartSectionsIso (s.leftGradedTensor ℳ 𝒩) h hV _)
  refine Eq.trans ?_ (congrArg
    (fun z => ((modulePushforwardMap (s.leftGradedTensor ℳ 𝒩) h).val.app (op V₀)).hom z)
    (chartSectionsIso_localApp_moduleSheafTensorChartMap ℳ 𝒩 W' hV' p₂ a b)).symm
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.trans ?_ (modulePushforwardMap_moduleChartTensorMap ℳ 𝒩 h
    (((modulesDirectedGlueData ℳ).chartSectionsIso W' hV').hom a)
    (((modulesDirectedGlueData 𝒩).chartSectionsIso W' hV').hom b) x).symm
  refine congrArg (fun q => q.1 x) (congrArg₂
    (fun z w => ((moduleChartTensorMap ℳ 𝒩 W).val.app
        (op (relativeProjChart s W ⁻¹ᵁ V₀))).hom
      (toTensorSheafSection (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
        (moduleChart ℳ W) (moduleChart 𝒩 W) (op (relativeProjChart s W ⁻¹ᵁ V₀)) (z ⊗ₜ[_] w)))
    (modulePushforwardMap_chartSectionsIso ℳ h hV a).symm
    (modulePushforwardMap_chartSectionsIso 𝒩 h hV b).symm)


/-- **The chart members of property (6) of Tag 01O7 over two nested affine opens of the base
agree on the sections over any open of the relative projective spectrum seen by both charts.** The
pure-tensor case is
`Stacks.RelativeProj.Situation.localApp_moduleSheafTensorChartMap_eq_of_le`, and a section of a
tensor product sheaf is locally a finite sum of pure tensors. -/
public theorem localApp_moduleSheafTensorChartMap_eq_of_nested {W W' : s.base.affineOpens}
    (h : W ≤ W') {V : (relativeProj s).Opens}
    {U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens}
    {U₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens}
    (h₁ : relativeProjChart s W ''ᵁ U₁ = V) (h₂ : relativeProjChart s W' ''ᵁ U₂ = V) :
    localApp (relativeProjChart s W) (moduleSheafTensorChartMap ℳ 𝒩 W) h₁
      = localApp (relativeProjChart s W') (moduleSheafTensorChartMap ℳ 𝒩 W') h₂ :=
  localApp_eq_of_toTensorSheafSection (relativeProjChart s W) (relativeProjChart s W')
    (moduleSheafTensorChartMap ℳ 𝒩 W) (moduleSheafTensorChartMap ℳ 𝒩 W') h₁ h₂
    fun _ p₁ p₂ a b => localApp_moduleSheafTensorChartMap_eq_of_le ℳ 𝒩 h p₁ p₂ a b

/-- **The glueing compatibility of the chart members of property (6) of Tag 01O7**: over an
arbitrary pair of affine opens of the base the two members agree on the sections over any open of
the relative projective spectrum seen by both charts. This is the hypothesis `hψ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the chart cover,
obtained from the nested case by
`Stacks.RelativeProj.Situation.localApp_relativeProjChart_eq_of_nested`. -/
public theorem localApp_moduleSheafTensorChartMap_eq (W W' : s.base.affineOpens)
    (U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (U₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens)
    (V : (relativeProj s).Opens)
    (h₁ : relativeProjChart s W ''ᵁ U₁ = V) (h₂ : relativeProjChart s W' ''ᵁ U₂ = V) :
    localApp (relativeProjChart s W) (moduleSheafTensorChartMap ℳ 𝒩 W) h₁
      = localApp (relativeProjChart s W') (moduleSheafTensorChartMap ℳ 𝒩 W') h₂ :=
  localApp_relativeProjChart_eq_of_nested (moduleSheafTensorChartMap ℳ 𝒩)
    (fun _ _ hle _ _ _ q₁ q₂ =>
      (localApp_moduleSheafTensorChartMap_eq_of_nested ℳ 𝒩 hle q₂ q₁).symm)
    W W' U₁ U₂ V h₁ h₂

/-- **There is exactly one morphism `ℳ̃ ⊗_𝒪 𝒩̃ ⟶ (ℳ ⊗_𝒜 𝒩)~` restricting on every chart of the
relative projective spectrum to the chart member of property (6) of Tag 01O7.** -/
public theorem existsUnique_tensorModuleSheafMap :
    ∃! φ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((relativeProj s).toRingedSpace)).presheaf,
          (((relativeProj s).toRingedSpace)).IsSheaf⟩).obj ((moduleSheaf ℳ))).obj
        ((moduleSheaf 𝒩))) ⟶ s.tensorModuleSheaf ℳ 𝒩,
      ∀ W : s.base.affineOpens,
        (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map φ
          = moduleSheafTensorChartMap ℳ 𝒩 W :=
  existsUnique_hom_of_restrict_cover (relativeProjChart s)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange]
      using iSup_opensRange_relativeProjChart s)
    (moduleSheafTensorChartMap ℳ 𝒩) (localApp_moduleSheafTensorChartMap_eq ℳ 𝒩)


/-- **The canonical map `ℳ̃ ⊗_𝒪 𝒩̃ ⟶ (ℳ ⊗_𝒜 𝒩)~` of property (6) of Tag 01O7**, for two left
graded modules with quasi-coherent homogeneous pieces over the graded algebra of a relative `Proj`
situation. It is glued from the chart members
`Stacks.RelativeProj.Situation.moduleSheafTensorChartMap`, to each of which it restricts, and it
is the only morphism that does so. -/
@[stacks 01O7 "property (6): the canonical map from the tensor product of the sheaves attached to
two left graded modules with quasi-coherent homogeneous pieces to the sheaf attached to the
tensor product of those modules, on a relative projective spectrum"]
public noncomputable def tensorModuleSheafMap :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((relativeProj s).toRingedSpace)).presheaf,
          (((relativeProj s).toRingedSpace)).IsSheaf⟩).obj ((moduleSheaf ℳ))).obj
        ((moduleSheaf 𝒩))) ⟶ s.tensorModuleSheaf ℳ 𝒩 :=
  (existsUnique_tensorModuleSheafMap ℳ 𝒩).exists.choose

/-- **The canonical map of property (6) of Tag 01O7 restricts on each chart of the relative
projective spectrum to the chart member it was glued from.** This is what pins it down. -/
public theorem restrictFunctor_map_tensorModuleSheafMap (W : s.base.affineOpens) :
    (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map (tensorModuleSheafMap ℳ 𝒩)
      = moduleSheafTensorChartMap ℳ 𝒩 W :=
  (existsUnique_tensorModuleSheafMap ℳ 𝒩).exists.choose_spec W

end Stacks.RelativeProj.Situation

end
