module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeNested

/-!
# Shrinking the affine open of `S'` in the base-change comparison of `ℳ̃`

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback of that of `s`, let `Ψ` identify `ℳ'` with
the pullback of `ℳ` degreewise, and let `r = relativeProjBaseChange g Φ hΦ`.

`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeNested.lean`
settles the nested case of the glueing compatibility of the base-change comparison of `ℳ̃` in the
direction where the affine open of `S` shrinks. This file settles the other direction, where the
affine open of `S'` shrinks, by instantiating
`Stacks.ProjModuleComparison.moduleMap_chartMember_pullback_eq`.

## Implementation notes

That instantiation is where the chain used to die: stated at
`Stacks.RelativeProj.Situation.projInclusionMap`, the comparison morphism of the charts of `s'`,
it exhausts the elaborator's heartbeats, and in the arrangement that does elaborate it exhausts
the kernel's budget. The generic lemma is stated at `AlgebraicGeometry.Proj.map`, and
`projInclusionMap` is *definitionally* that — the same morphism read through the identification of
its domain with the whole of the smaller homogeneous spectrum — so the two spellings differ by an
unfolding of `AlgebraicGeometry.Proj.map` which the elaborator is otherwise left to rediscover at
each of the four places the morphism occurs, inside a statement that also carries eleven
occurrences of `Stacks.RelativeProj.Situation.moduleSheaf`.

What makes it checkable is to pay that unfolding **once**, in a declaration of its own:
`Stacks.RelativeProj.Situation.projInclusionMap_eq_projMap` is the identity, by `rfl`, and the
statements below are written at `AlgebraicGeometry.Proj.map` so that nothing is unified against
`projInclusionMap` again. The morphism does not occur in the conclusion of
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`, only in its hypotheses, so the
glueing compatibility this file ends with is stated in neither spelling and needs no transport
back.

Heartbeats are counted per declaration, so the chain is split as well: the chart member is put
into the generic shape by
`Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom_eq`, the chart-refinement law is
restated at `AlgebraicGeometry.Proj.map` by
`pullbackIsoOfRestrictIso_comp_moduleMap_projMap`, and only then is the generic lemma applied.

## Main results

* `Stacks.RelativeProj.Situation.projInclusionMap_eq_projMap`: the comparison morphism of the
  charts is `AlgebraicGeometry.Proj.map` of the restriction of graded section rings.
* `Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom_eq`: the chart member of the
  base-change comparison, in the shape the generic nested lemma is stated at.
* `Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom_source_le`: **the chart member
  over `(W, W₁')` is the inverse image of the one over `(W, W₂')`** along the comparison morphism
  of the charts of `s'`, for `W₁' ≤ W₂'` inside the preimage of `W`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
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

/-! ### The comparison morphism of charts at the spelling the generic lemmas use -/

/-- **The comparison morphism of the charts over an inclusion of affine opens is
`AlgebraicGeometry.Proj.map` of the restriction of graded section rings.** True by unfolding
`Stacks.RelativeProj.Situation.projInclusionMap`, which reads that morphism through the
identification of its domain with the whole of the smaller homogeneous spectrum.

It is worth a declaration of its own: the generic lemmas about morphisms of homogeneous spectra
are stated at `AlgebraicGeometry.Proj.map`, and leaving the elaborator to rediscover this identity
at each occurrence of the morphism in a large statement is what exhausts the heartbeat budget. -/
public theorem projInclusionMap_eq_projMap {t : Situation.{u}} {W W' : t.base.affineOpens}
    (h : W ≤ W') :
    projInclusionMap t W.1 W'.1 h W.2 W'.2
      = AlgebraicGeometry.Proj.map (gradedSectionRestriction t W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2) :=
  rfl

/-- The chart transition law of a relative projective spectrum, written at
`AlgebraicGeometry.Proj.map`: `Stacks.RelativeProj.Situation.relativeProjChart_transition`
transported along `Stacks.RelativeProj.Situation.projInclusionMap_eq_projMap`. -/
public theorem projMap_comp_relativeProjChart {t : Situation.{u}} {W W' : t.base.affineOpens}
    (h : W ≤ W') :
    AlgebraicGeometry.Proj.map (gradedSectionRestriction t W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2)
        ≫ relativeProjChart t W'
      = relativeProjChart t W :=
  (congrArg (· ≫ relativeProjChart t W') (projInclusionMap_eq_projMap h)).symm.trans
    (relativeProjChart_transition t h)

/-- The chart-refinement law of the glueing of `ℳ̃`, written at `AlgebraicGeometry.Proj.map`. This
is `Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_moduleMap` at the other spelling
of the comparison morphism of charts; the two statements are the same term, and stating this one
separately is what keeps that unfolding out of the proof below. -/
public theorem pullbackIsoOfRestrictIso_comp_moduleMap_projMap {t : Situation.{u}}
    (𝒬 : SheafOfModules.LeftGradedModule.{u, u, u} t.algebra)
    [∀ n : ℤ, (𝒬.piece n).IsQuasicoherent] {W W' : t.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart t W') (moduleSheafChartIso 𝒬 W')
          (AlgebraicGeometry.Proj.map (gradedSectionRestriction t W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2))
          (projMap_comp_relativeProjChart h).symm).hom
        ≫ moduleMap (gradedSectionRestriction t W.1 W'.1 h)
            (irrelevant_le_map_gradedSectionRestriction t W.1 W'.1 h W.2 W'.2)
            (sectionModuleRestrictₛₗ 𝒬 h) (sectionModuleRestrictₛₗ_mem_grading 𝒬 h)
      = (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart t W)).app
            (moduleSheaf 𝒬)).symm ≪≫ moduleSheafChartIso 𝒬 W).hom :=
  pullbackIsoOfRestrictIso_comp_moduleMap 𝒬 h

/-! ### The chart member of the base-change comparison, in the generic shape -/

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

/-- The chart square of the base-change morphism over a pair of affine opens, stated at the pair
rather than at an index of the chart cover. This is
`Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange_eq`, and its purpose
is to spend the reduction of the cover index's projections here, once, instead of inside the
statements below. -/
public theorem relativeProjChart_comp_projMap (W : s.base.affineOpens)
    (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    relativeProjChart s' W' ≫ relativeProjBaseChange g Φ hΦ
      = AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W'.1 h)
            (irrelevant_le_gradedBaseChange g Φ W W' h hΦ)
        ≫ relativeProjChart s W :=
  relativeProjChart_comp_relativeProjBaseChange_eq g Φ hΦ ⟨(W', W), h⟩

include hΨ in
/-- **The chart member of the base-change comparison of `ℳ̃`, in the shape the generic nested
lemma is stated at.** `Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom` is a
composite of four morphisms and the generic shape is a composite of four morphisms; the two differ
by the bracketing of the middle two, so one associativity step is the whole proof.

The index of the chart cover is a *variable* here, and the pair of affine opens appears only
through its projections. Writing it instead as the pair, with the index built by its constructor,
makes the kernel reduce that constructor inside a statement with eleven occurrences of
`Stacks.RelativeProj.Situation.moduleSheaf`, and that exhausts its budget; against a variable the
projections are inert. -/
public theorem moduleSheafBaseChangePullbackHom_eq (p : (baseChangeCover g).I₀) :
    moduleSheafBaseChangePullbackHom g Φ hΦ Ψ hΨ p
      = (Scheme.Modules.pullbackComp (relativeProjChart s' p.1.1)
            (relativeProjBaseChange g Φ hΦ)).hom.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s p.1.2)
              (moduleSheafChartIso ℳ p.1.2)
              (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
                (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ))
              (relativeProjChart_comp_projMap g Φ hΦ p.1.2 p.1.1 p.2)).hom
        ≫ moduleMap (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
            (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ)
            (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ p.1.2.1 p.1.1.1 p.2)
            (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ p.1.2.1 p.1.1.1 p.2 i hz)
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' p.1.1)).app (moduleSheaf ℳ')).symm
            ≪≫ moduleSheafChartIso ℳ' p.1.1).inv :=
  whisker_eq _ (Category.assoc _ _ _)

/-! ### Shrinking the affine open of `S'` -/

section SourceLe

variable (W : s.base.affineOpens) {W₁' W₂' : s'.base.affineOpens} (h' : W₁' ≤ W₂')
  (h₂ : W₂'.1 ≤ g ⁻¹ᵁ W.1) (h₁ : W₁'.1 ≤ g ⁻¹ᵁ W.1)

include hΨ in
/-- **The chart member of the base-change comparison over `(W, W₁')` is the inverse image of the
one over `(W, W₂')`** along the comparison morphism of the charts of `s'` attached to `W₁' ≤ W₂'`,
for two affine opens of `S'` inside the preimage of one affine open `W` of `S`.

This is `Stacks.ProjModuleComparison.moduleMap_chartMember_pullback_eq` for the chart of `S` over
`W` and the two charts of `S'`: the chart-refinement law of the glueing of `ℳ̃` on `S'` is
`pullbackIsoOfRestrictIso_comp_moduleMap_projMap`, and the factorization of the graded base change
is `Stacks.RelativeProj.Situation.gradedRestrict_comp_gradedBaseChange` with its module companion
`Stacks.RelativeProj.Situation.sectionModuleRestrict_sectionModuleBaseChange`.

Both sides are morphisms of inverse images along the chart over `W₁'`, so this is the hypothesis
`hφ` of `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`.

The two chart members are written out rather than named by
`Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom`, whose argument is an index of
the chart cover: naming them would put that index's constructor inside this statement, and
reducing it here is what exhausts the kernel's budget.
`Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom_eq` relates the two spellings at a
*variable* index, which is where that step belongs. With both members written out this proof is a
single application, with nothing to rewrite. -/
public theorem moduleSheafBaseChangePullbackHom_source_le :
    (Scheme.Modules.pullbackCongr (projMap_comp_relativeProjChart h')).inv.app
          ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ))
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
                (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2))
              (relativeProjChart s' W₂')).inv.app
            ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ))
        ≫ (Scheme.Modules.pullback
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
                (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2))).map
            ((Scheme.Modules.pullbackComp (relativeProjChart s' W₂')
                  (relativeProjBaseChange g Φ hΦ)).hom.app (moduleSheaf ℳ)
              ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W)
                    (moduleSheafChartIso ℳ W)
                    (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W₂'.1 h₂)
                      (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ))
                    (relativeProjChart_comp_projMap g Φ hΦ W W₂' h₂)).hom
              ≫ moduleMap (gradedBaseChange g Φ W.1 W₂'.1 h₂)
                  (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
                  (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₂'.1 h₂)
                  (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W.1 W₂'.1 h₂ i hz)
              ≫ (((Scheme.Modules.restrictFunctorIsoPullback
                    (relativeProjChart s' W₂')).app (moduleSheaf ℳ')).symm
                  ≪≫ moduleSheafChartIso ℳ' W₂').inv)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
                (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2))
              (relativeProjChart s' W₂')).hom.app (moduleSheaf ℳ')
        ≫ (Scheme.Modules.pullbackCongr
              (projMap_comp_relativeProjChart h')).hom.app (moduleSheaf ℳ')
      = (Scheme.Modules.pullbackComp (relativeProjChart s' W₁')
            (relativeProjBaseChange g Φ hΦ)).hom.app (moduleSheaf ℳ)
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (relativeProjChart s W)
              (moduleSheafChartIso ℳ W)
              (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W₁'.1 h₁)
                (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ))
              (relativeProjChart_comp_projMap g Φ hΦ W W₁' h₁)).hom
        ≫ moduleMap (gradedBaseChange g Φ W.1 W₁'.1 h₁)
            (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ)
            (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₁'.1 h₁)
            (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W.1 W₁'.1 h₁ i hz)
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback
              (relativeProjChart s' W₁')).app (moduleSheaf ℳ')).symm
            ≪≫ moduleSheafChartIso ℳ' W₁').inv :=
  moduleMap_chartMember_pullback_eq
    (gradedBaseChange g Φ W.1 W₂'.1 h₂) (irrelevant_le_gradedBaseChange g Φ W W₂' h₂ hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₂'.1 h₂)
    (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W.1 W₂'.1 h₂ i hz)
    (gradedSectionRestriction s' W₁'.1 W₂'.1 h')
    (irrelevant_le_map_gradedSectionRestriction s' W₁'.1 W₂'.1 h' W₁'.2 W₂'.2)
    (sectionModuleRestrictₛₗ ℳ' h') (sectionModuleRestrictₛₗ_mem_grading ℳ' h')
    (gradedBaseChange g Φ W.1 W₁'.1 h₁) (irrelevant_le_gradedBaseChange g Φ W W₁' h₁ hΦ)
    (sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W.1 W₁'.1 h₁)
    (fun i {_} hz => sectionModuleBaseChange_mem_grading g Ψ W.1 W₁'.1 h₁ i hz)
    (relativeProjBaseChange g Φ hΦ) (relativeProjChart s W) (moduleSheafChartIso ℳ W)
    (relativeProjChart s' W₂') (moduleSheafChartIso ℳ' W₂')
    (projMap_comp_relativeProjChart h') (moduleSheafChartIso ℳ' W₁')
    (relativeProjChart_comp_projMap g Φ hΦ W W₂' h₂)
    (relativeProjChart_comp_projMap g Φ hΦ W W₁' h₁)
    (pullbackIsoOfRestrictIso_comp_moduleMap_projMap ℳ' h')
    (gradedRestrict_comp_gradedBaseChange g Φ W.1 h' h₂ h₁).symm
    (fun m => (sectionModuleRestrict_sectionModuleBaseChange g Ψ W.1 h' h₂ h₁ m).symm)

end SourceLe

end Stacks.RelativeProj.Situation

end
