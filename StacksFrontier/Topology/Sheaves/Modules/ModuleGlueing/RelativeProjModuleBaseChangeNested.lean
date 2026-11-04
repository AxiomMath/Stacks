module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.ComparisonChart
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChartRefine
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeGlue
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleChartRefine

/-!
# The nested case of the base-change comparison of `ℳ̃`

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback of that of `s`, let `Ψ` identify `ℳ'` with
the pullback of `ℳ` degreewise, and let `r = relativeProjBaseChange g Φ hΦ`.

The chart members of the base-change comparison of `ℳ̃` are indexed by pairs `W' ⊆ g⁻¹W` of affine
opens, ordered componentwise, and
`Stacks.RelativeProj.Situation.localApp_baseChangeCover_eq_of_nested` reduces the glueing
compatibility for an arbitrary pair of indices to the case of a nested pair. A nested pair factors
through the index with the smaller open of `S'` and the larger open of `S`, so that case splits in
two, each moving one component:

* the open of `S` shrinks, the open of `S'` fixed. The chart of `Proj_{S'}(𝒜')` is then the *same*
  on both sides, so the two chart members agree as morphisms out of one inverse image and the
  compatibility is a congruence. This is
  `Stacks.RelativeProj.Situation.moduleChartBaseChangeHom_comp_eq_of_target_le`, **proved here**.
* the open of `S'` shrinks, the open of `S` fixed. The chart of `Proj_{S'}(𝒜')` changes, so the
  compatibility is `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` for the two
  charts. Its hypothesis is
  `AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq`, specialised to the sheaves of
  Tag 01M6 as `Stacks.ProjModuleComparison.moduleMap_chartMember_pullback_eq`; the square it needs
  is `Stacks.RelativeProj.Situation.baseChangeChart_source_le`, proved here. See the note below.

Both steps rest on the same three ingredients: the chart-refinement law of the glueing of `ℳ̃` --
`Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_moduleMap`, used for `ℳ` on the base of the
first step and for `ℳ'` on the base of the second; the composition law
`Stacks.ProjModuleComparison.moduleMap_comp_of_eq` of the chart comparisons across the two
factorizations of the graded base change; and the coherence of the chart description of an inverse
image, `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso_refine` for the first step and
`pullbackChartDesc_precomp` for the second.

## Main definitions

* `Stacks.RelativeProj.Situation.baseChangeChart`: the base-change morphism of charts over a pair
  of affine opens.

## Main results

* `Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_moduleMap`: the chart-refinement law
  of the glueing of `ℳ̃` in the shape the chart description of an inverse image consumes.
* `Stacks.RelativeProj.Situation.baseChangeChart_source_le`: the factorization of the base change
  of charts through the chart comparison of `s'`.
* `Stacks.RelativeProj.Situation.moduleChartBaseChangeHom_comp_eq_of_target_le`: **the chart member
  of the base-change comparison does not change when the affine open of `S` is shrunk.**

## Not done here

No attribute is claimed here. Tag 01O7 states eight properties, and its registration belongs on a
declaration stating all eight; this file proves one half of the nested case of property (8).

The other half -- the affine open of `S'` shrinking, which is the instantiation of
`Stacks.ProjModuleComparison.moduleMap_chartMember_pullback_eq` at `relativeProj s'`,
`moduleSheaf ℳ` and `moduleSheaf ℳ'` -- is in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeSource.lean`, and
the glueing of the chart members into `r^* ℳ̃ ⟶ ℳ̃'` is in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeGlued.lean`.
That the comparison is an isomorphism is in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeIso.lean`.

The twisting sheaves `𝒪(n)` of a relative projective spectrum are not treated here.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.ProjModuleComparison

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleHomGlue

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))
  {ℳ : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra}
  {ℳ' : SheafOfModules.LeftGradedModule.{u, u, u} s'.algebra}
  (Ψ : ∀ n : ℤ, (Scheme.Modules.pullback g).obj (ℳ.piece n) ⟶ ℳ'.piece n)
  (hΨ : ∀ (i : ℕ) (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
    (a : s.sectionPieces W i) (x : sectionModulePieces ℳ W n),
    pieceSectionModuleHom g Ψ ((i : ℤ) + n) W W' h (ℳ.smul (i : ℤ) n (op W) a x)
      = ℳ'.smul (i : ℤ) n (op W') (pieceSectionHom g Φ i W W' h a)
          (pieceSectionModuleHom g Ψ n W W' h x))

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent]

/-! ### The chart-refinement law of `ℳ̃` in the shape the chart description consumes -/

/-- **The chart-refinement law of the glueing of `ℳ̃`, as the hypothesis of
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso_refine`.** This is
`Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_moduleMap` with its first two factors
recognised as the chart description of the inverse image along the chart comparison morphism; the
two spellings are the same term. -/
public theorem pullbackIsoOfRestrictIso_comp_moduleMap {t : Situation.{u}}
    (𝒬 : SheafOfModules.LeftGradedModule.{u, u, u} t.algebra)
    [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] {W W' : t.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t W') (moduleSheafChartIso 𝒬 W')
          (projInclusionMap t W.1 W'.1 h W.2 W'.2)
          (relativeProjChart_transition t h).symm).hom
        ≫ moduleMap (gradedSectionRestriction t W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2)
            (sectionModuleRestrictₛₗ 𝒬 h) (sectionModuleRestrictₛₗ_mem_grading 𝒬 h)
      = (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart t W)).app
            (moduleSheaf 𝒬)).symm ≪≫ moduleSheafChartIso 𝒬 W).hom :=
  ((eq_whisker (Scheme.Modules.pullbackIsoOfRestrictIso_hom (relativeProjChart t W')
        (moduleSheafChartIso 𝒬 W') (projInclusionMap t W.1 W'.1 h W.2 W'.2)
        (relativeProjChart_transition t h).symm) _).trans
      (((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).trans
        (eq_whisker (Scheme.Modules.pullbackCongr_symm_hom_app
          (relativeProjChart_transition t h) (moduleSheaf 𝒬)) _))).trans
    (pullbackCongr_inv_comp_moduleMap 𝒬 h)

/-! ### The two spellings of the chart data -/

/-- `Stacks.RelativeProj.Situation.moduleSheafPullbackChartIso` is the chart description of the
inverse image of `ℳ̃` along the chart. True by unfolding the two definitions; it is stated so that
the identities below can be rewritten into the spelling the generic lemmas are stated at, instead
of leaving the kernel to check the whole identity up to definitional equality. -/
public theorem moduleSheafPullbackChartIso_eq {T : Scheme.{u}} (W : s.base.affineOpens)
    (b : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) {hm : T ⟶ relativeProj s}
    (hfac : hm = b ≫ relativeProjChart s W) :
    moduleSheafPullbackChartIso ℳ W b hfac
      = Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W)
          (moduleSheafChartIso ℳ W) b hfac :=
  rfl

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent] in
/-- `Stacks.RelativeProj.Situation.moduleChartBaseChangeHom` is
`Stacks.ProjModuleComparison.moduleMap` of the base change of the graded modules of sections. True
by unfolding the definition. -/
public theorem moduleChartBaseChangeHom_eq (W : s.base.affineOpens) (W' : s'.base.affineOpens)
    (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    moduleChartBaseChangeHom g Φ hΦ Ψ hΨ W W' h
      = moduleMap (gradedBaseChange g Φ W.1 W'.1 h)
          (irrelevant_le_gradedBaseChange g Φ W W' h hΦ)
          (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W'.1 h)
          (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W.1 W'.1 h i hz) :=
  rfl

/-! ### Shrinking the affine open of `S` -/

/-- The base-change morphism of charts over a pair `W' ⊆ g⁻¹W` of affine opens: the morphism of
homogeneous spectra induced by the base change of the graded section rings. Named so that the
statements below do not have to spell it out. -/
public abbrev baseChangeChart (W : s.base.affineOpens) (W' : s'.base.affineOpens)
    (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    AlgebraicGeometry.Proj (s'.sectionRingGrading W'.1) ⟶
      AlgebraicGeometry.Proj (s.sectionRingGrading W.1) :=
  AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W'.1 h)
    (irrelevant_le_gradedBaseChange g Φ W W' h hΦ)

section TargetLe

variable {W₁ W₂ : s.base.affineOpens} (h₁₂ : W₁ ≤ W₂) (W' : s'.base.affineOpens)
  (h₁ : W'.1 ≤ g ⁻¹ᵁ W₁.1) (h₂ : W'.1 ≤ g ⁻¹ᵁ W₂.1)

omit [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent] in
include hΨ h₁₂ in
/-- **The chart member of the base-change comparison does not change when the affine open of `S`
is shrunk.** For a fixed affine open `W'` of `S'` lying in the preimage of both `W₁ ≤ W₂`, reading
`ℳ̃` on the chart of `S` over `W₂` and comparing with the chart sheaf of `ℳ'` over `W'` is reading
it on the chart over `W₁` and comparing.

This is `Stacks.ProjModuleComparison.moduleMap_comp_pullbackChartDesc` for the two charts of `S`
over `W₁ ≤ W₂`: the chart-refinement law of the glueing of `ℳ̃` is
`Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_moduleMap`, and the factorization of
the graded base change is
`Stacks.RelativeProj.Situation.gradedBaseChange_comp_gradedRestrict` with its module companion
`Stacks.RelativeProj.Situation.sectionModuleBaseChange_sectionModuleRestrict`.

The chart of `Proj_{S'}(𝒜')` does not enter: both sides are morphisms out of the inverse image of
`ℳ̃` along the one morphism `hm`, so this identity is between the chart members *themselves*, not
merely between their actions on sections. -/
public theorem moduleChartBaseChangeHom_comp_eq_of_target_le
    {hm : AlgebraicGeometry.Proj (s'.sectionRingGrading W'.1) ⟶ relativeProj s}
    (hfac₁ : hm = baseChangeChart g Φ hΦ W₁ W' h₁ ≫ relativeProjChart s W₁)
    (hfac₂ : hm = baseChangeChart g Φ hΦ W₂ W' h₂ ≫ relativeProjChart s W₂) :
    (moduleSheafPullbackChartIso ℳ W₂ (baseChangeChart g Φ hΦ W₂ W' h₂) hfac₂).hom
        ≫ moduleChartBaseChangeHom g Φ hΦ Ψ hΨ W₂ W' h₂
      = (moduleSheafPullbackChartIso ℳ W₁ (baseChangeChart g Φ hΦ W₁ W' h₁) hfac₁).hom
        ≫ moduleChartBaseChangeHom g Φ hΦ Ψ hΨ W₁ W' h₁ := by
  rw [moduleSheafPullbackChartIso_eq _ _ hfac₁, moduleSheafPullbackChartIso_eq _ _ hfac₂,
    moduleChartBaseChangeHom_eq, moduleChartBaseChangeHom_eq]
  exact moduleMap_comp_pullbackChartDesc (gradedSectionRestriction s W₁.1 W₂.1 h₁₂)
    (irrelevant_le_map_gradedSectionRestriction s W₁.1 W₂.1 h₁₂ W₁.2 W₂.2)
    (sectionModuleRestrictₛₗ ℳ h₁₂) (sectionModuleRestrictₛₗ_mem_grading ℳ h₁₂)
    (gradedBaseChange g Φ W₁.1 W'.1 h₁) (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₁.1 W'.1 h₁)
    (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W₁.1 W'.1 h₁ i hz)
    (gradedBaseChange g Φ W₂.1 W'.1 h₂) (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₂.1 W'.1 h₂)
    (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W₂.1 W'.1 h₂ i hz)
    (relativeProjChart s W₂) (moduleSheafChartIso ℳ W₂)
    (relativeProjChart_transition s h₁₂).symm (moduleSheafChartIso ℳ W₁)
    (pullbackIsoOfRestrictIso_comp_moduleMap ℳ h₁₂) hfac₂ hfac₁
    (gradedBaseChange_comp_gradedRestrict g Φ h₁₂ W'.1 h₁ h₂).symm
    (fun m => (sectionModuleBaseChange_sectionModuleRestrict g Ψ h₁₂ W'.1 h₁ h₂ m).symm)

end TargetLe

/-! ### Shrinking the affine open of `S'` -/

section SourceLe

variable (W : s.base.affineOpens) {W₁' W₂' : s'.base.affineOpens} (h' : W₁' ≤ W₂')
  (h₂ : W₂'.1 ≤ g ⁻¹ᵁ W.1) (h₁ : W₁'.1 ≤ g ⁻¹ᵁ W.1)

/-- **The base changes of charts over `(W, W₁')` and `(W, W₂')` are related by the chart comparison
morphism of `s'`.** This is `Stacks.ProjModuleComparison.projMapComp` for
`Stacks.RelativeProj.Situation.gradedRestrict_comp_gradedBaseChange`, and it is the square
`hsq` that `AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` takes. -/
public theorem baseChangeChart_source_le :
    projInclusionMap s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2 ≫ baseChangeChart g Φ hΦ W W₂' h₂
      = baseChangeChart g Φ hΦ W W₁' h₁ :=
  projMapComp (gradedBaseChange g Φ W.1 W₂'.1 h₂)
    (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
    (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
    (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2)
    (gradedBaseChange g Φ W.1 W₁'.1 h₁) (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ)
    (gradedRestrict_comp_gradedBaseChange g Φ W.1 h' h₂ h₁).symm

end SourceLe

end Stacks.RelativeProj.Situation

end
