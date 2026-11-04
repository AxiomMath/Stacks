module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SectionModuleBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback

/-!
# The sheaf attached to a graded module on a relative projective spectrum, and base change

Let `g : S' ⟶ S` be a morphism of schemes, let `s` and `s'` be relative `Proj` situations over
`S` and `S'`, let `Φ` identify the graded algebra of `s'` with the pullback of that of `s`, and
let `r = relativeProjBaseChange g Φ hΦ : Proj_{S'}(𝒜') ⟶ Proj_S(𝒜)` be the base-change morphism
of the two relative projective spectra. Let `ℳ` be a graded `𝒜`-module, `ℳ'` a graded
`𝒜'`-module, and let `Ψ` identify `ℳ'` with the pullback of `ℳ` degreewise.

This file constructs the comparison

`r^* ℳ̃ ⟶ ℳ̃'`

on each chart of `Proj_{S'}(𝒜')`. The charts are indexed by pairs `W' ⊆ g⁻¹W` of affine opens of
`S'` and of `S`, as they are for the base-change morphism of schemes itself: an affine open of
`S'` need not map into any single affine open of `S`, so there is no choice-free indexing by
affine opens of `S'` alone.

On the chart over such a pair the comparison is the absolute one. The chart of `Proj_{S'}(𝒜')`
over `W'` maps to the chart of `Proj_S(𝒜)` over `W` by `AlgebraicGeometry.Proj.map` of the base
change `𝒜(W) ⟶ 𝒜'(W')` of graded section rings, `ℳ̃` pulled back along a morphism factoring
through a chart is the pullback of the chart sheaf, and the chart sheaves are the sheaves of Tag
01M6 of the graded modules of sections, between which the base change of graded modules of
sections induces `Stacks.ProjModuleComparison.moduleMap`.

## Main definitions

* `Stacks.RelativeProj.Situation.moduleChartBaseChangeHom`: the comparison
  `(Proj.map 𝒜(W) → 𝒜'(W'))^* ℳ(W)~ ⟶ ℳ'(W')~` of the chart sheaves.
* `Stacks.RelativeProj.Situation.moduleSheafBaseChangeChartHom`: `ℳ̃` pulled back along the chart
  of `Proj_{S'}(𝒜')` over `W'` followed by `r`, compared with the chart sheaf of `ℳ'` over `W'`.
* `Stacks.RelativeProj.Situation.moduleSheafBaseChangeRestrictHom`: the same read as a morphism
  of the restrictions of `r^* ℳ̃` and of `ℳ̃'` to the chart over `W'`.

## Main results

* `Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange_eq`: the chart of
  `Proj_{S'}(𝒜')` over `W'` followed by `r` is `Proj.map` of the base change of graded section
  rings followed by the chart of `Proj_S(𝒜)` over `W`.
* `Stacks.RelativeProj.Situation.fibreMap_gradedBaseChange_target_le` and
  `fibreMap_gradedBaseChange_source_le`: **the glue squares of the chart comparisons**, one for
  shrinking the affine open of `S` and one for shrinking the affine open of `S'`, read in the
  module fibres. Each is one application of
  `Stacks.ProjModuleComparison.fibreMap_comp_of_eq` to a factorization of the base change of
  graded section rings and its companion for the graded modules of sections.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.ProjModuleComparison
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))
  {ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}
  {ℳ' : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s'.algebra}
  (Ψ : ∀ n : ℤ, (Scheme.Modules.pullback g).obj (ℳ.piece n) ⟶ ℳ'.piece n)
  (hΨ : ∀ (i : ℕ) (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
    (a : s.sectionPieces W i) (x : sectionModulePieces ℳ W n),
    pieceSectionModuleHom g Ψ ((i : ℤ) + n) W W' h (ℳ.smul (i : ℤ) n (op W) a x)
      = ℳ'.smul (i : ℤ) n (op W') (pieceSectionHom g Φ i W W' h a)
          (pieceSectionModuleHom g Ψ n W W' h x))

/-! ### The comparison of the chart sheaves -/

include hΨ in
/-- **The comparison of the chart sheaves of a relative-`Proj` base change.** On the chart over a
pair `W' ⊆ g⁻¹W` of affine opens, the base change of the graded modules of sections induces the
canonical comparison of the sheaves of Tag 01M6 across `AlgebraicGeometry.Proj.map` of the base
change of the graded section rings. -/
public def moduleChartBaseChangeHom (W : s.base.affineOpens) (W' : s'.base.affineOpens)
    (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W'.1 h)
        (irrelevant_le_gradedBaseChange g Φ W W' h hΦ))).obj (moduleChart ℳ W)
      ⟶ moduleChart ℳ' W' :=
  Stacks.ProjModuleComparison.moduleMap (gradedBaseChange g Φ W.1 W'.1 h)
    (irrelevant_le_gradedBaseChange g Φ W W' h hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W'.1 h)
    (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W.1 W'.1 h i hz)

/-! ### The compatibility of the chart comparisons in each of the two opens -/

include hΨ in
/-- **The chart comparisons are compatible with shrinking the affine open of `S`.** Comparing on
the chart over the pair `(W₂, W')` is comparing on the chart over `(W₁, W')` after the chart
transition of `s` attached to `W₁ ≤ W₂`.

Both sides are read in the module fibres, where the comparison is the localization of the base
change of the graded modules of sections; the identity is the factorization
`Stacks.RelativeProj.Situation.gradedBaseChange_comp_gradedRestrict` of the base change of graded
section rings together with its module companion
`Stacks.RelativeProj.Situation.sectionModuleBaseChange_sectionModuleRestrict`. The fibre family
is kept abstract, because the two sides index it at two definitionally equal but syntactically
different points of `Proj 𝒜(W₂)`. -/
public theorem fibreMap_gradedBaseChange_target_le
    {W₁ W₂ : s.base.affineOpens} (h₁₂ : W₁.1 ≤ W₂.1) (W' : s'.base.affineOpens)
    (h₁ : W'.1 ≤ g ⁻¹ᵁ W₁.1) (h₂ : W'.1 ≤ g ⁻¹ᵁ W₂.1)
    (y : ProjectiveSpectrum (s'.sectionRingGrading W'.1))
    {Q : ProjectiveSpectrum (s.sectionRingGrading W₂.1) → Prop}
    (a : ∀ q : Subtype Q,
      ModuleFiber (M := sectionModule ℳ W₂.1) (s.sectionRingGrading W₂.1) q.1)
    (k₁ : Q (ProjectiveSpectrum.comapFun (gradedBaseChange g Φ W₂.1 W'.1 h₂)
      (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ) y))
    (k₂ : Q (ProjectiveSpectrum.comapFun (gradedSectionRestriction s W₁.1 W₂.1 h₁₂)
      (irrelevant_le_map_gradedSectionRestriction s W₁.1 W₂.1 h₁₂ W₁.2 W₂.2)
      (ProjectiveSpectrum.comapFun (gradedBaseChange g Φ W₁.1 W'.1 h₁)
        (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ) y))) :
    fibreMap (gradedBaseChange g Φ W₂.1 W'.1 h₂)
        (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ)
        (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₂.1 W'.1 h₂) y (a ⟨_, k₁⟩)
      = fibreMap (gradedBaseChange g Φ W₁.1 W'.1 h₁)
          (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ)
          (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₁.1 W'.1 h₁) y
          (fibreMap (gradedSectionRestriction s W₁.1 W₂.1 h₁₂)
            (irrelevant_le_map_gradedSectionRestriction s W₁.1 W₂.1 h₁₂ W₁.2 W₂.2)
            (sectionModuleRestrictₛₗ ℳ h₁₂) _ (a ⟨_, k₂⟩)) :=
  fibreMap_comp_of_eq (gradedSectionRestriction s W₁.1 W₂.1 h₁₂)
    (irrelevant_le_map_gradedSectionRestriction s W₁.1 W₂.1 h₁₂ W₁.2 W₂.2)
    (sectionModuleRestrictₛₗ ℳ h₁₂)
    (gradedBaseChange g Φ W₁.1 W'.1 h₁) (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₁.1 W'.1 h₁)
    (gradedBaseChange g Φ W₂.1 W'.1 h₂) (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ)
    (gradedBaseChange_comp_gradedRestrict g Φ h₁₂ W'.1 h₁ h₂).symm
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₂.1 W'.1 h₂)
    (fun m => (sectionModuleBaseChange_sectionModuleRestrict g Ψ h₁₂ W'.1 h₁ h₂ m).symm)
    y a k₁ k₂

include hΨ in
/-- **The chart comparisons are compatible with shrinking the affine open of `S'`.** Comparing on
the chart over the pair `(W, W₁')` is the chart transition of `s'` attached to `W₁' ≤ W₂'` after
comparing on the chart over `(W, W₂')`.

This is `Stacks.RelativeProj.Situation.gradedRestrict_comp_gradedBaseChange` together with its
module companion
`Stacks.RelativeProj.Situation.sectionModuleRestrict_sectionModuleBaseChange`, read in the module
fibres. -/
public theorem fibreMap_gradedBaseChange_source_le (W : s.base.affineOpens)
    {W₁' W₂' : s'.base.affineOpens} (h' : W₁'.1 ≤ W₂'.1)
    (h₂ : W₂'.1 ≤ g ⁻¹ᵁ W.1) (h₁ : W₁'.1 ≤ g ⁻¹ᵁ W.1)
    (y : ProjectiveSpectrum (s'.sectionRingGrading W₁'.1))
    {Q : ProjectiveSpectrum (s.sectionRingGrading W.1) → Prop}
    (a : ∀ q : Subtype Q,
      ModuleFiber (M := sectionModule ℳ W.1) (s.sectionRingGrading W.1) q.1)
    (k₁ : Q (ProjectiveSpectrum.comapFun (gradedBaseChange g Φ W.1 W₁'.1 h₁)
      (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ) y))
    (k₂ : Q (ProjectiveSpectrum.comapFun (gradedBaseChange g Φ W.1 W₂'.1 h₂)
      (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
      (ProjectiveSpectrum.comapFun (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
        (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2) y))) :
    fibreMap (gradedBaseChange g Φ W.1 W₁'.1 h₁)
        (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ)
        (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₁'.1 h₁) y (a ⟨_, k₁⟩)
      = fibreMap (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
          (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2)
          (sectionModuleRestrictₛₗ ℳ' h') y
          (fibreMap (gradedBaseChange g Φ W.1 W₂'.1 h₂)
            (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
            (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₂'.1 h₂) _ (a ⟨_, k₂⟩)) :=
  fibreMap_comp_of_eq (gradedBaseChange g Φ W.1 W₂'.1 h₂)
    (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₂'.1 h₂)
    (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
    (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2)
    (sectionModuleRestrictₛₗ ℳ' h')
    (gradedBaseChange g Φ W.1 W₁'.1 h₁) (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ)
    (gradedRestrict_comp_gradedBaseChange g Φ W.1 h' h₂ h₁).symm
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₁'.1 h₁)
    (fun m => (sectionModuleRestrict_sectionModuleBaseChange g Ψ W.1 h' h₂ h₁ m).symm)
    y a k₁ k₂

/-! ### The factorization of a chart of the new spectrum through a chart of the old -/

/-- **The chart of `Proj_{S'}(𝒜')` over `W'` followed by the base-change morphism factors through
the chart of `Proj_S(𝒜)` over `W`**, by `AlgebraicGeometry.Proj.map` of the base change of the
graded section rings. This is
`Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange` with the chart
comparison morphism unfolded to the shape the pullback comparison of `ℳ̃` consumes. -/
public theorem relativeProjChart_comp_relativeProjBaseChange_eq
    (p : (baseChangeCover g).I₀) :
    relativeProjChart s' p.1.1 ≫ relativeProjBaseChange g Φ hΦ
      = AlgebraicGeometry.Proj.map (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
          (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ)
        ≫ relativeProjChart s p.1.2 :=
  relativeProjChart_comp_relativeProjBaseChange g Φ hΦ p

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent]

include hΨ in
/-- **`ℳ̃` pulled back to a chart of the base-changed relative projective spectrum, compared with
the chart sheaf of `ℳ'`.** The pullback of `ℳ̃` along the chart over `W'` followed by the
base-change morphism is the pullback of the chart sheaf of `ℳ` over `W`, because that composite
factors through the chart over `W`; there the comparison is the absolute one. -/
public def moduleSheafBaseChangeChartHom (p : (baseChangeCover g).I₀) :
    (Scheme.Modules.pullback
        (relativeProjChart s' p.1.1 ≫ relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ)
      ⟶ moduleChart ℳ' p.1.1 :=
  (moduleSheafPullbackChartIso ℳ p.1.2
      (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
        (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ))
      (relativeProjChart_comp_relativeProjBaseChange_eq g Φ hΦ p)).hom
    ≫ moduleChartBaseChangeHom g Φ hΦ Ψ hΨ p.1.2 p.1.1 p.2

include hΨ in
/-- **The chart comparison read as a morphism of the restrictions to the chart over `W'`.** This
is `Stacks.RelativeProj.Situation.moduleSheafBaseChangeChartHom` with the restriction along the
chart identified with the pullback along it on the left and `ℳ̃'` identified with its chart sheaf
on the right.

This is the shape a gluing of the chart comparisons consumes: it is the family `ψ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` over the chart cover
`Stacks.RelativeProj.Situation.baseChangeCover` of `Proj_{S'}(𝒜')`; the agreement of two members
over the overlap of their charts is
`Stacks.RelativeProj.Situation.localApp_moduleSheafBaseChangeRestrictHom_eq_of_nested`. -/
public def moduleSheafBaseChangeRestrictHom (p : (baseChangeCover g).I₀) :
    ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj
        (moduleSheaf ℳ)).restrict (relativeProjChart s' p.1.1)
      ⟶ (moduleSheaf ℳ').restrict (relativeProjChart s' p.1.1) :=
  ((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s' p.1.1)).app
      ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ))).hom
    ≫ ((Scheme.Modules.pullbackComp (relativeProjChart s' p.1.1)
        (relativeProjBaseChange g Φ hΦ)).app (moduleSheaf ℳ)).hom
    ≫ moduleSheafBaseChangeChartHom g Φ hΦ Ψ hΨ p
    ≫ (moduleSheafChartIso ℳ' p.1.1).inv

end Stacks.RelativeProj.Situation

end
