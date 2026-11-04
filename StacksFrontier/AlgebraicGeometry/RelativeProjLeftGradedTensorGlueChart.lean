module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorGlue

/-!
# The chart comparison of property (6) of Tag 01O7, transported onto the glued sheaves

Let `s` be a relative `Proj` situation and let `ℳ`, `𝒩` be left graded modules over its graded
algebra with quasi-coherent homogeneous pieces. Property (6) of Tag 01O7 asks for a morphism
`ℳ̃ ⊗_𝒪 𝒩̃ ⟶ (ℳ ⊗_𝒜 𝒩)~` on the relative projective spectrum, and
`Stacks.RelativeProj.Situation.moduleSheafTensorChartMap` is the member of that morphism over an
affine open `W` of the base: the chart comparison
`Stacks.RelativeProj.Situation.moduleChartTensorMap`, conjugated by the identification of the
restriction of a tensor product with the tensor product of the restrictions
(`Stacks.ProjectionFormula.restrictTensorIso` and
`Stacks.ProjectionFormula.tensorSheafIsoMk`) and by the chart identifications
`Stacks.RelativeProj.Situation.moduleSheafChartIso` of the two factors and of the target.

This file reads that conjugated morphism on a pure tensor of honest sections of `ℳ̃` and `𝒩̃`,
which is what the glueing of the chart members has to compare.

## Main results

* `RelativeProj.Situation.moduleSheafChartIso_moduleSheafTensorChartMap_toTensorSheafSection_tmul`:
  **the chart comparison of property (6), read through the chart identification of the target,
  carries the image of a pure tensor of sections of `ℳ̃` and `𝒩̃` over the image of an open of the
  chart to the image under the chart comparison of the pure tensor of the chart readings of those
  sections.** The three conjugating isomorphisms are discharged here: the target's chart
  identification cancels, and the two factors cross the restriction comparison unchanged.
* `Stacks.RelativeProj.Situation.modulePushforwardMap_chartSectionsIso`: **reading a section of
  `ℳ̃` on the chart over the larger of two nested affine opens of the base and then comparing the
  chart sheaves is reading it on the chart over the smaller one.** This identifies the transition
  of the glueing datum of `ℳ̃` with `Stacks.RelativeProj.Situation.modulePushforwardMap`.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_apply`: the action of
  `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` on a section, as
  `Stacks.AlgebraicGeometry.ModuleHomGlue.appImage` conjugated by the restriction maps along the
  equality of opens that `localApp` transports along.

## Implementation notes

The two comparisons named `restrictTensorIso` — `Stacks.ProjectionFormula.restrictTensorIso`,
which the chart member is built from, and
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso`, which has the description on
local sections — are the same term, and the second one's description applies to the first with no
bridge. The equality of the two *isomorphisms* is not provable within the heartbeat budget, but
the equality of their values on the image of a pure tensor is, and that is all that is used:
`Stacks.RelativeProj.Situation.restrictTensorIso_app_toTensorSheafSection_tmul` states it at the
`Stacks.ProjectionFormula` spelling and proves it by the `RestrictionSections` lemma.

Heartbeats are counted cumulatively over a declaration, and two steps here each cost most of a
budget on their own: the elaborator's decomposition of the four-term composite defining the chart
member, and the identification of the two spellings of the restriction comparison. Each is
therefore a declaration of its own — proved by `rfl` and by a single lemma application
respectively — and the main result composes them. Written as `have`s inside one proof the
declaration exceeds the budget, and the limit cannot be raised in this library.

`AlgebraicGeometry.ProjectiveSpectrum.isPrime` is installed as a local instance at file scope, as
in the files proving the fibre and glue identities: an `attribute [local instance]` inside a
namespace does not survive the `end`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)

## Not done here

No Stacks tag is carried. The morphism of property (6) of Tag 01O7 is not constructed: the
identity proved here is about one chart member on the image of a pure tensor, and the hypothesis
`hψ` of `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` compares two
chart members on an arbitrary section. Nothing here passes from pure tensors to arbitrary
sections.
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

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
  (ψ : M.restrict f ⟶ N.restrict f)

/-- `localApp` is `appImage` conjugated by the restriction maps along the equality of opens. -/
public theorem localApp_apply {W : X.Opens} {V : Y.Opens} (hWV : f ''ᵁ W = V)
    (x : ToType (M.val.obj (op V))) :
    localApp f ψ hWV x =
      N.presheaf.map (eqToHom hWV.symm).op
        (appImage f ψ W (M.presheaf.map (eqToHom hWV).op x)) := by
  subst hWV
  simp
  rfl

end Stacks.AlgebraicGeometry.ModuleHomGlue

namespace Stacks.RelativeProj.Situation

open Stacks.SheafOfModules

/-- An isomorphism of sheaves of modules on a scheme cancels its inverse on sections. -/
private theorem iso_hom_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (Z : (TopologicalSpace.Opens X)ᵒᵖ) (y : ToType (N.val.obj Z)) :
    (e.hom.val.app Z).hom ((e.inv.val.app Z).hom y) = y :=
  congrArg (fun k : N ⟶ N => (k.val.app Z).hom y) e.inv_hom_id

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- Reading a section of `ℳ̃` on the chart over the bigger open and then comparing the chart
sheaves is reading it on the chart over the smaller open. -/
public theorem modulePushforwardMap_chartSectionsIso {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (x : ToType ((moduleSheaf ℳ).val.obj (op V))) :
    ((modulePushforwardMap ℳ h).val.app (op V)).hom
        (((modulesDirectedGlueData ℳ).chartSectionsIso W'
          (hV.trans (opensRange_relativeProjChart_mono s h))).hom x)
      = ((modulesDirectedGlueData ℳ).chartSectionsIso W hV).hom x := by
  refine Eq.trans ?_ ((modulesDirectedGlueData ℳ).toModulesGlueData.trans_chartSectionsIso
    W' W (hV.trans (opensRange_relativeProjChart_mono s h)) hV x)
  refine Eq.trans ?_ ((modulesDirectedGlueData ℳ).pairTrans_eq_trans_symm h hV
    (((modulesDirectedGlueData ℳ).chartSectionsIso W'
      (hV.trans (opensRange_relativeProjChart_mono s h))).hom x)).symm
  exact (LinearEquiv.eq_symm_apply _).mpr
    ((LinearEquiv.ofBijective _ (bijective_modulePushforwardMap_app ℳ h hV)).symm_apply_apply _)


attribute [local instance] sectionModuleDecomposition

variable (𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]

/-- The chart comparison of property (6) is its defining composite on sections over an open of
the chart. True by `rfl`; it is separated out because the elaborator's decomposition of the
composite costs most of a declaration's heartbeat budget. -/
private theorem moduleSheafTensorChartMap_app (W : s.base.affineOpens)
    (U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (t : ToType (((Scheme.Modules.restrictFunctor (relativeProjChart s W)).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((relativeProj s).toRingedSpace)).presheaf,
          (((relativeProj s).toRingedSpace)).IsSheaf⟩).obj ((moduleSheaf ℳ))).obj
            ((moduleSheaf 𝒩))))).val.obj (op U₁))) :
    ((moduleSheafTensorChartMap ℳ 𝒩 W).val.app (op U₁)).hom t
      = ((moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W).inv.val.app (op U₁)).hom
          (((moduleChartTensorMap ℳ 𝒩 W).val.app (op U₁)).hom
            (((Stacks.ProjectionFormula.tensorSheafIsoMk (moduleSheafChartIso ℳ W)
                  (moduleSheafChartIso 𝒩 W)).hom.val.app (op U₁)).hom
              (((Stacks.ProjectionFormula.restrictTensorIso (relativeProjChart s W)
                  (moduleSheaf ℳ) (moduleSheaf 𝒩)).hom.val.app (op U₁)).hom t))) := rfl

/-- **The restriction-of-a-tensor-product comparison carries the image of a pure tensor of
sections over the image open to the image of the same pure tensor.** This is
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso_hom_unit_tmul` read at the
`Stacks.ProjectionFormula.restrictTensorIso` spelling, which the chart comparison of property
(6) is built from; the two comparisons are the same term, and no bridge is needed. -/
public theorem restrictTensorIso_app_toTensorSheafSection_tmul (W : s.base.affineOpens)
    (U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (a : ToType ((moduleSheaf ℳ).val.obj (op (relativeProjChart s W ''ᵁ U₁))))
    (b : ToType ((moduleSheaf 𝒩).val.obj (op (relativeProjChart s W ''ᵁ U₁)))) :
    (((Stacks.ProjectionFormula.restrictTensorIso (relativeProjChart s W)
          (moduleSheaf ℳ) (moduleSheaf 𝒩)).hom.val.app (op U₁)).hom
        (TensorStalkRingedSpace.toTensorSheafSection (relativeProj s).toRingedSpace
          (moduleSheaf ℳ) (moduleSheaf 𝒩) (op (relativeProjChart s W ''ᵁ U₁)) (a ⊗ₜ[_] b)))
      = TensorStalkRingedSpace.toTensorSheafSection
          (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
          ((Scheme.Modules.restrictFunctor (relativeProjChart s W)).obj (moduleSheaf ℳ))
          ((Scheme.Modules.restrictFunctor (relativeProjChart s W)).obj (moduleSheaf 𝒩))
          (op U₁) (a ⊗ₜ[_] b) :=
  Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso_hom_unit_tmul
    (relativeProjChart s W) (moduleSheaf ℳ) (moduleSheaf 𝒩) U₁ a b

/-- **The chart comparison of property (6), read through the chart identification of the target**,
on the image of a pure tensor of sections of `ℳ̃` and `𝒩̃` over the image of an open of the
chart. -/
public theorem moduleSheafChartIso_moduleSheafTensorChartMap_toTensorSheafSection_tmul
    (W : s.base.affineOpens) (U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens)
    (a : ToType ((moduleSheaf ℳ).val.obj (op (relativeProjChart s W ''ᵁ U₁))))
    (b : ToType ((moduleSheaf 𝒩).val.obj (op (relativeProjChart s W ''ᵁ U₁)))) :
    letI := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    (((moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W).hom.val.app (op U₁)).hom
        (((moduleSheafTensorChartMap ℳ 𝒩 W).val.app (op U₁)).hom
          (TensorStalkRingedSpace.toTensorSheafSection (relativeProj s).toRingedSpace
            (moduleSheaf ℳ) (moduleSheaf 𝒩) (op (relativeProjChart s W ''ᵁ U₁)) (a ⊗ₜ[_] b))))
      = ((moduleChartTensorMap ℳ 𝒩 W).val.app (op U₁)).hom
          (TensorStalkRingedSpace.toTensorSheafSection
            (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace
            (moduleChart ℳ W) (moduleChart 𝒩 W) (op U₁)
            (((moduleSheafChartIso ℳ W).hom.val.app (op U₁)).hom a ⊗ₜ[_]
              ((moduleSheafChartIso 𝒩 W).hom.val.app (op U₁)).hom b)) := by
  let := tensorGrading_decomposition (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  let := tensorGrading_gradedSMul (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  refine Eq.trans (congrArg
    (fun z => ((moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W).hom.val.app (op U₁)).hom z)
    (moduleSheafTensorChartMap_app ℳ 𝒩 W U₁ _)) ?_
  refine Eq.trans (iso_hom_inv_app
    (moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W) (op U₁) _) ?_
  refine congrArg (fun z => ((moduleChartTensorMap ℳ 𝒩 W).val.app (op U₁)).hom z) ?_
  refine Eq.trans (congrArg (fun z => ((Stacks.ProjectionFormula.tensorSheafIsoMk
      (moduleSheafChartIso ℳ W) (moduleSheafChartIso 𝒩 W)).hom.val.app (op U₁)).hom z)
    (restrictTensorIso_app_toTensorSheafSection_tmul ℳ 𝒩 W U₁ a b)) ?_
  exact TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
    (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace _ _ _ _
    (moduleSheafChartIso ℳ W).hom (moduleSheafChartIso 𝒩 W).hom U₁ a b

end Stacks.RelativeProj.Situation

end
