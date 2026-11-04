module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeSource

/-!
# The base-change comparison of `ℳ̃`, glued

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback of that of `s`, let `Ψ` identify `ℳ'` with
the pullback of `ℳ` degreewise, and let `r = relativeProjBaseChange g Φ hΦ`.

This file assembles **property (8) of Tag 01O7**: the formation of `ℳ̃` commutes with base
change. The two directions of the nested case of the glueing compatibility are in place -- the
affine open of `S` shrinking in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeNested.lean`, the
affine open of `S'` shrinking in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeSource.lean` --
and a nested pair of indices factors through the index with the smaller open of `S'` and the
larger open of `S`, so the two compose to the nested case. `localApp_baseChangeCover_eq_of_nested`
turns that into the compatibility for an arbitrary pair, and
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` glues.

## Main results

* `Stacks.RelativeProj.Situation.baseChangeMember_target_le`: the chart member of the base-change
  comparison, in the spelled-out shape, does not change when the affine open of `S` shrinks.
* `Stacks.RelativeProj.Situation.localApp_moduleSheafBaseChangeRestrictHom_eq_of_nested`: the
  glueing compatibility of the chart members over a nested pair of indices.
* `Stacks.RelativeProj.Situation.existsUnique_moduleSheafBaseChangeHom`: **the base-change
  comparison `r^* ℳ̃ ⟶ ℳ̃'` exists and is unique with the given restriction to every chart.**
* `Stacks.RelativeProj.Situation.moduleSheafBaseChangeHom`: that morphism.

## Where the rest is

That the base-change comparison is an **isomorphism** is
`Stacks.RelativeProj.Situation.isIso_moduleSheafBaseChangeHom` of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeIso.lean`, and
property (8) of Tag 01O7 is registered there, on
`Stacks.RelativeProj.Situation.moduleSheafPullbackIso`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
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

/-! ### Shrinking the affine open of `S`, in the spelled-out shape -/

section TargetLe

variable {W₁ W₂ : s.base.affineOpens} (h₁₂ : W₁ ≤ W₂) (W' : s'.base.affineOpens)
  (h₁ : W'.1 ≤ g ⁻¹ᵁ W₁.1) (h₂ : W'.1 ≤ g ⁻¹ᵁ W₂.1)

include hΨ h₁₂ in
/-- **The chart member of the base-change comparison does not change when the affine open of `S`
is shrunk**, in the shape the glueing compatibility below consumes. This is
`Stacks.RelativeProj.Situation.moduleChartBaseChangeHom_comp_eq_of_target_le`, whose two factors
are the middle two here, rewritten through the two spelling lemmas
`Stacks.RelativeProj.Situation.moduleSheafPullbackChartIso_eq` and
`moduleChartBaseChangeHom_eq`. The outer two factors do not mention the affine open of `S` and are
untouched. -/
public theorem baseChangeMember_target_le :
    (Scheme.Modules.pullbackComp (relativeProjChart s' W')
          (relativeProjBaseChange g Φ hΦ)).hom.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W₂)
              (moduleSheafChartIso ℳ W₂)
              (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W₂.1 W'.1 h₂)
                (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ))
              (relativeProjChart_comp_projMap g Φ hΦ W₂ W' h₂)).hom
        ≫ moduleMap (gradedBaseChange g Φ W₂.1 W'.1 h₂)
            (irrelevant_le_gradedBaseChange g Φ W₂ W' h₂ hΦ)
            (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₂.1 W'.1 h₂)
            (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W₂.1 W'.1 h₂ i hz)
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' W')).app (moduleSheaf ℳ')).symm
            ≪≫ moduleSheafChartIso ℳ' W').inv
      = (Scheme.Modules.pullbackComp (relativeProjChart s' W')
            (relativeProjBaseChange g Φ hΦ)).hom.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W₁)
              (moduleSheafChartIso ℳ W₁)
              (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W₁.1 W'.1 h₁)
                (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ))
              (relativeProjChart_comp_projMap g Φ hΦ W₁ W' h₁)).hom
        ≫ moduleMap (gradedBaseChange g Φ W₁.1 W'.1 h₁)
            (irrelevant_le_gradedBaseChange g Φ W₁ W' h₁ hΦ)
            (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W₁.1 W'.1 h₁)
            (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W₁.1 W'.1 h₁ i hz)
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' W')).app (moduleSheaf ℳ')).symm
            ≪≫ moduleSheafChartIso ℳ' W').inv :=
  whisker_eq _
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker
          (((eq_whisker (congrArg Iso.hom (moduleSheafPullbackChartIso_eq W₂ _
                  (relativeProjChart_comp_projMap g Φ hΦ W₂ W' h₂))) _).trans
              (whisker_eq _ (moduleChartBaseChangeHom_eq g Φ hΦ Ψ hΨ W₂ W' h₂))).symm.trans
            ((moduleChartBaseChangeHom_comp_eq_of_target_le g Φ hΦ Ψ hΨ h₁₂ W' h₁ h₂
                  (relativeProjChart_comp_projMap g Φ hΦ W₁ W' h₁)
                  (relativeProjChart_comp_projMap g Φ hΦ W₂ W' h₂)).trans
              ((eq_whisker (congrArg Iso.hom (moduleSheafPullbackChartIso_eq W₁ _
                    (relativeProjChart_comp_projMap g Φ hΦ W₁ W' h₁))) _).trans
                (whisker_eq _ (moduleChartBaseChangeHom_eq g Φ hΦ Ψ hΨ W₁ W' h₁)))))
          _).trans
        (Category.assoc _ _ _)))

end TargetLe

/-! ### The nested case, and the glueing -/

include hΨ in
/-- **The glueing compatibility of the chart members of the base-change comparison over a nested
pair of indices.** For `q ≤ p` in the index of the chart cover -- that is, the affine open of `S'`
and the affine open of `S` both shrink -- the two chart members act in the same way on the
sections over an open of `Proj_{S'}(𝒜')` seen by both charts.

The pair factors through the index with the smaller open of `S'` and the larger open of `S`, so
the identity is the composite of the two one-component steps:
`Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom_source_le` shrinks the open of
`S'`, through `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`, and
`Stacks.RelativeProj.Situation.baseChangeMember_target_le` then shrinks the open of `S` -- the
chart of `Proj_{S'}(𝒜')` being fixed there, that step is a congruence under `localApp`. -/
public theorem localApp_moduleSheafBaseChangeRestrictHom_eq_of_nested
    {p q : (baseChangeCover g).I₀} (hpq : q ≤ p)
    {V : (relativeProj s').Opens}
    {U₁ : (AlgebraicGeometry.Proj (s'.sectionRingGrading p.1.1.1)).Opens}
    {U₂ : (AlgebraicGeometry.Proj (s'.sectionRingGrading q.1.1.1)).Opens}
    (e₁ : relativeProjChart s' p.1.1 ''ᵁ U₁ = V)
    (e₂ : relativeProjChart s' q.1.1 ''ᵁ U₂ = V) :
    localApp (relativeProjChart s' p.1.1) (moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ p) e₁
      = localApp (relativeProjChart s' q.1.1)
          (moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ q) e₂ := by
  have hle : q.1.1.1 ≤ g ⁻¹ᵁ p.1.2.1 := le_trans hpq.1 p.2
  -- the comparison morphism of the charts of `s'`, at the `AlgebraicGeometry.Proj.map` spelling
  have : IsOpenImmersion (AlgebraicGeometry.Proj.map
      (gradedSectionRestriction s' q.1.1.1 p.1.1.1 hpq.1)
      (irrelevant_le_map_gradedSectionRestriction s' q.1.1.1 p.1.1.1 hpq.1 q.1.1.2 p.1.1.2)) :=
    projInclusionMap_eq_projMap (t := s') hpq.1 ▸
      isOpenImmersion_projInclusionMap s' hpq.1 q.1.1.2 p.1.1.2
  rw [moduleSheafBaseChangeRestrictHom_eq_ofPullback,
    moduleSheafBaseChangeRestrictHom_eq_ofPullback, moduleSheafBaseChangePullbackHom_eq,
    moduleSheafBaseChangePullbackHom_eq,
    ← baseChangeMember_target_le g Φ hΦ Ψ hΨ hpq.2 q.1.1 q.2 hle]
  exact localApp_ofPullback_eq _ _ (projMap_comp_relativeProjChart hpq.1) _ _
    (moduleSheafBaseChangePullbackHom_source_le g Φ hΦ Ψ hΨ p.1.2 hpq.1 p.2 hle) e₁ e₂

include hΨ in
/-- **The canonical base-change comparison of `ℳ̃`.** For
`g : S' ⟶ S`, a relative `Proj` situation `s'` over `S'` whose graded algebra is identified with
the pullback of that of `s` by `Φ`, and a graded module `ℳ'` on `S'` identified with the pullback
of `ℳ` degreewise by `Ψ`, there is exactly one morphism
`r^* ℳ̃ ⟶ ℳ̃'` on `Proj_{S'}(𝒜')` restricting on each chart of the base-change cover to the
comparison `Stacks.RelativeProj.Situation.moduleSheafBaseChangeRestrictHom` built there from the
base change of the graded modules of sections.

This is `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the chart
cover `Stacks.RelativeProj.Situation.baseChangeCover`: the charts cover by
`iSup_image_top_baseChangeCover`, and the compatibility of two members over an arbitrary pair of
indices is `localApp_baseChangeCover_eq_of_nested` applied to the nested case
`localApp_moduleSheafBaseChangeRestrictHom_eq_of_nested`.

What is constructed is the canonical comparison morphism together with the property that
determines it. That it is an isomorphism is
`Stacks.RelativeProj.Situation.isIso_moduleSheafBaseChangeHom`. -/
public theorem existsUnique_moduleSheafBaseChangeHom :
    ∃! α : (Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ) ⟶
        moduleSheaf ℳ',
      ∀ p : (baseChangeCover g).I₀,
        (Scheme.Modules.restrictFunctor (relativeProjChart s' p.1.1)).map α
          = moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ p :=
  existsUnique_hom_of_restrict_cover
    (fun p : (baseChangeCover g).I₀ => relativeProjChart s' p.1.1)
    (iSup_image_top_baseChangeCover g) (moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ)
    (fun p q U₁ U₂ V e₁ e₂ =>
      localApp_baseChangeCover_eq_of_nested g (moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ)
        (fun _ _ hab _ _ _ f₁ f₂ =>
          localApp_moduleSheafBaseChangeRestrictHom_eq_of_nested g Φ hΦ Ψ hΨ hab f₁ f₂)
        p q U₁ U₂ V e₁ e₂)

include hΨ in
/-- **The base-change comparison of `ℳ̃`**, the morphism `r^* ℳ̃ ⟶ ℳ̃'` of property (8) of
Tag 01O7, glued from the chart comparisons. Its defining property is
`Stacks.RelativeProj.Situation.restrictFunctor_map_moduleSheafBaseChangeHom`. -/
public noncomputable def moduleSheafBaseChangeHom :
    (Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ) ⟶
      moduleSheaf ℳ' :=
  (existsUnique_moduleSheafBaseChangeHom g Φ hΦ Ψ hΨ).exists.choose

include hΨ in
/-- The base-change comparison restricts on the chart over an index of the base-change cover to
the chart comparison built from the base change of the graded modules of sections. -/
public theorem restrictFunctor_map_moduleSheafBaseChangeHom (p : (baseChangeCover g).I₀) :
    (Scheme.Modules.restrictFunctor (relativeProjChart s' p.1.1)).map
        (moduleSheafBaseChangeHom g Φ hΦ Ψ hΨ)
      = moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ p :=
  (existsUnique_moduleSheafBaseChangeHom g Φ hΦ Ψ hΨ).exists.choose_spec p

end Stacks.RelativeProj.Situation

end
