module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChange

/-!
# The glueing datum of the base-change comparison of `ℳ̃`, reduced to its nested case

Let `g : S' ⟶ S`, let `s` and `s'` be relative `Proj` situations over `S` and `S'`, let `Φ`
identify the graded algebra of `s'` with the pullback of that of `s`, and let
`r = relativeProjBaseChange g Φ hΦ`. The morphism
`Stacks.RelativeProj.Situation.moduleSheafBaseChangeRestrictHom` is the chart-level comparison of
`r^* ℳ̃` with `ℳ̃'`, one member for each index of the chart cover
`Stacks.RelativeProj.Situation.baseChangeCover` of `Proj_{S'}(𝒜')`. Glueing those members into a
morphism on all of `Proj_{S'}(𝒜')` is
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, which asks for the
agreement of two members over the overlap of their charts, for an **arbitrary** pair of indices.

This file discharges everything in that hypothesis except the nested case. The cover is covered,
each pairwise overlap is covered by the charts below both indices, and the chart family is
recognised as `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of a morphism of inverse
images — the form in which
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` consumes a nested pair.

The index of the cover is a **pair** `W' ⊆ g⁻¹W` of affine opens, of `S'` and of `S`, and the
order on it is componentwise. The relation along which the nested case is taken is therefore that
order, not the containment of chart images:
`Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` leaves the nested relation free for
exactly this reason, and the directedness of the index that supplies it is
`Stacks.RelativeProj.Situation.baseChangeCover_hdir`.

## Main definitions

* `Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom`: the chart member of the
  base-change comparison as a morphism of **inverse images** along the chart, rather than of the
  restrictions.

## Main results

* `Stacks.RelativeProj.Situation.iSup_image_top_baseChangeCover`: the charts of the base-change
  cover exhaust `Proj_{S'}(𝒜')`, written with the chart images as images of the top open — the
  shape the glueing theorem's covering hypothesis takes.
* `Stacks.RelativeProj.Situation.image_top_baseChangeCover_inf_le_iSup`: **the overlap of two
  charts of the base-change cover is covered by the charts over the indices below both.**
* `Stacks.RelativeProj.Situation.localApp_baseChangeCover_eq_of_nested`: **for the base-change
  cover, the glueing compatibility over an arbitrary pair of indices follows from the case of a
  nested pair.** Nothing is assumed of the two sheaves of modules or of the local morphism data,
  so this is the base-change-cover half of any such glueing.
* `Stacks.RelativeProj.Situation.moduleSheafBaseChangeRestrictHom_eq_ofPullback`: the chart member
  of the base-change comparison is the `ofPullback` of
  `Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom`.

## Implementation notes

`moduleSheafBaseChangeRestrictHom` is a composite of four morphisms whose first factor is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` at the source. `ofPullback` is the
conjugate by that same comparison at both ends, so the recognition lemma is the cancellation of
its appearance at the *target*: the morphism of inverse images is the last three factors of
`moduleSheafBaseChangeRestrictHom` followed by the comparison at `ℳ̃'`, and the two copies of it
cancel. The one step `simp` does not take is the two spellings `(e.app X).hom` and `e.hom.app X`
of a component of a natural isomorphism, which `CategoryTheory.Iso.app_hom` relates; the
definition in `RelativeProjModuleBaseChange.lean` uses the first and `ofPullback` the second.

## Not done here

No attribute is claimed here. Tag 01O7 states eight properties, and its registration belongs on a
declaration stating all eight; this file discharges the cover-combinatorial part of property (8)
only. Nothing here says the comparison is an isomorphism.

What the nested case needs is two identities, and **both are now proved**:

* the **morphism-level** composition law for `Stacks.ProjModuleComparison.moduleMap`, out of which
  `Stacks.RelativeProj.Situation.moduleChartBaseChangeHom` is built. This is
  `Stacks.ProjModuleComparison.moduleMap_comp_of_eq` of
  `StacksFrontier/AlgebraicGeometry/RelativeProj/ModuleSheaf/ComparisonComp.lean`.
* **the chart-refinement law of the glueing of `ℳ̃`.** The laws wanted for
  `Stacks.RelativeProj.Situation.moduleSheafPullbackChartIso` and for
  `Stacks.RelativeProj.Situation.moduleSheafChartIso` are one identity, because the first
  construction is `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso` of the second. It is
  `Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_moduleMap` of
  `StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleChartRefine.lean`, proved
  across the pullback--pushforward adjunction by the route `moduleMap_comp_of_eq` itself takes:
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.transpose_restrictIso` computes the two chart transposes,
  `Stacks.ProjModuleComparison.transpose_moduleMap` the middle one, the middle factors become
  `Stacks.RelativeProj.Situation.modulePushforwardMap` once
  `Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id` fires, and the
  residue is settled over the opens inside the chart by
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.hom_ext_of_resLE_injective` with
  `injective_pushforward_resLE`.

  Its section-level step is
  `Stacks.RelativeProj.Situation.modulePushforwardMap_chartSectionsIso` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorGlueChart.lean`, proved together
  with property (6).

  `moduleSheafPullbackChartIso` itself still has no lemma of its own; what it has is the coherence
  of the generic `pullbackIsoOfRestrictIso` it is built from, in
  `StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/PullbackChartRefine.lean`.

With those two in hand the nested case splits along the two components of the index, and both
halves are proved. The case in which the affine open of `S` shrinks is
`Stacks.RelativeProj.Situation.moduleChartBaseChangeHom_comp_eq_of_target_le` of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeNested.lean`; the
case in which the affine open of `S'` shrinks is
`Stacks.RelativeProj.Situation.moduleSheafBaseChangePullbackHom_source_le` of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeSource.lean`, the
instantiation of `Stacks.ProjModuleComparison.moduleMap_chartMember_pullback_eq` at this
situation. The two are composed and glued into `r^* ℳ̃ ⟶ ℳ̃'` in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeGlued.lean`, by
`Stacks.RelativeProj.Situation.existsUnique_moduleSheafBaseChangeHom`.

The section-level route that closed property (6) is not available here. There the source of the
chart member was a tensor product sheaf, whose sections are generated by the images of pure
tensors under `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`, and
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_eq_of_toTensorSheafSection` extends an identity
on those to all sections. Here the source is `r^* ℳ̃`, the inverse image of a sheaf of modules
along a morphism that is not an open immersion, and its sections over an open of
`Proj_{S'}(𝒜')` have no such generators. That is why the nested case has to be an identity of
*morphisms* rather than of maps on sections, and why `ofPullback` is the shape this file puts the
chart family into.

The twisting sheaves `𝒪(n)` of a relative projective spectrum are not treated here.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleHomGlue

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)

/-! ### The base-change cover covers, and refines its own overlaps -/

/-- **The charts of the base-change cover exhaust the base-changed relative projective
spectrum.** This is the covering hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, with the chart images
written as images of the top open. A point lies in the chart over any affine open of `S'`
containing its image which lies in the preimage of an affine open of `S`, and
`Stacks.RelativeProj.Situation.exists_baseChangeIndex` produces one. -/
public theorem iSup_image_top_baseChangeCover :
    ⨆ p : (baseChangeCover g).I₀, relativeProjChart s' p.1.1 ''ᵁ (⊤ : _) = ⊤ := by
  simp only [Scheme.Hom.image_top_eq_opensRange]
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨p, hy, -⟩ := exists_baseChangeIndex g (relativeProjToBase s' x) ⊤ trivial
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨p, ?_⟩
  rw [opensRange_relativeProjChart]
  exact hy

/-- **The overlap of two charts of the base-change cover is covered by the charts over the indices
below both.** This is `Stacks.RelativeProj.Situation.baseChangeCover_hdir` with the chart images
written as images of the top open, which is the shape
`Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` consumes. The index below both is
produced by choosing an affine open of `S` inside the intersection of the two partners and then an
affine open of `S'` inside the intersection of the two members and the preimage of that. -/
public theorem image_top_baseChangeCover_inf_le_iSup (p q : (baseChangeCover g).I₀) :
    relativeProjChart s' p.1.1 ''ᵁ ⊤ ⊓ relativeProjChart s' q.1.1 ''ᵁ ⊤
      ≤ ⨆ r : {r : (baseChangeCover g).I₀ // r ≤ p ∧ r ≤ q},
          relativeProjChart s' r.1.1.1 ''ᵁ (⊤ : _) := by
  simp only [Scheme.Hom.image_top_eq_opensRange]
  intro x hx
  obtain ⟨r, hrp, hrq, hxr⟩ := baseChangeCover_hdir g p q x hx.1 hx.2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hrp, hrq⟩, hxr⟩

/-- **For the base-change cover, the glueing compatibility over an arbitrary pair of indices
follows from the nested case.** Given local morphism data on the charts which agrees wherever one
index is below another, the data agrees wherever two charts see the same open of
`Proj_{S'}(𝒜')` — which is the hypothesis `hψ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the cover
`Stacks.RelativeProj.Situation.baseChangeCover`.

This is `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` for that cover: the relation
on the index is its componentwise order, and the covering of each pairwise overlap by members
below both is `Stacks.RelativeProj.Situation.image_top_baseChangeCover_inf_le_iSup`. The order on
the index is the right relation and the containment of chart images is not, because the chart over
an index depends only on its affine open of `S'` while the comparison over it depends on both
components. Nothing is assumed of the two sheaves of modules. -/
public theorem localApp_baseChangeCover_eq_of_nested
    {M N : (relativeProj s').Modules}
    (Θ : ∀ p : (baseChangeCover g).I₀,
      M.restrict (relativeProjChart s' p.1.1) ⟶ N.restrict (relativeProjChart s' p.1.1))
    (hnest : ∀ p q : (baseChangeCover g).I₀, q ≤ p →
      ∀ (V : (relativeProj s').Opens)
        (W₁ : (AlgebraicGeometry.Proj (s'.sectionRingGrading p.1.1.1)).Opens)
        (W₂ : (AlgebraicGeometry.Proj (s'.sectionRingGrading q.1.1.1)).Opens)
        (h₁ : relativeProjChart s' p.1.1 ''ᵁ W₁ = V)
        (h₂ : relativeProjChart s' q.1.1 ''ᵁ W₂ = V),
        localApp (relativeProjChart s' p.1.1) (Θ p) h₁
          = localApp (relativeProjChart s' q.1.1) (Θ q) h₂)
    (p q : (baseChangeCover g).I₀)
    (W₁ : (AlgebraicGeometry.Proj (s'.sectionRingGrading p.1.1.1)).Opens)
    (W₂ : (AlgebraicGeometry.Proj (s'.sectionRingGrading q.1.1.1)).Opens)
    (V : (relativeProj s').Opens)
    (h₁ : relativeProjChart s' p.1.1 ''ᵁ W₁ = V)
    (h₂ : relativeProjChart s' q.1.1 ''ᵁ W₂ = V) :
    localApp (relativeProjChart s' p.1.1) (Θ p) h₁
      = localApp (relativeProjChart s' q.1.1) (Θ q) h₂ :=
  Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine
    (fun p : (baseChangeCover g).I₀ => relativeProjChart s' p.1.1) Θ
    (κ := fun p q => {r : (baseChangeCover g).I₀ // r ≤ p ∧ r ≤ q})
    (fun _ _ r => r.1) (fun p q => q ≤ p)
    (fun _ _ r => r.2.1) (fun _ _ r => r.2.2)
    (image_top_baseChangeCover_inf_le_iSup g)
    (fun i j hij => hnest i j hij) p q W₁ W₂ V h₁ h₂

/-! ### The chart family as local data on inverse images -/

section Pullback

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

variable (Φ : SheafOfModules.GradedAlgebra.UnitalHom
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

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (ℳ'.piece n).IsQuasicoherent]

include hΨ in
/-- **The chart member of the base-change comparison of `ℳ̃`, as a morphism of inverse images
along the chart.** The restrictions of `r^* ℳ̃` and of `ℳ̃'` to the chart over the affine open of
`S'` are their inverse images along it, and this is
`Stacks.RelativeProj.Situation.moduleSheafBaseChangeRestrictHom` read on that side: the
identification of the inverse image along the chart followed by `r` with the inverse image of the
chart sheaf, the chart comparison, and the chart sheaf of `ℳ'` identified with the restriction of
`ℳ̃'` and then with its inverse image.

This is the form in which
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` consumes local data for a pair of
members of a cover one of which factors through the other. -/
public def moduleSheafBaseChangePullbackHom (p : (baseChangeCover g).I₀) :
    (Scheme.Modules.pullback (relativeProjChart s' p.1.1)).obj
        ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (moduleSheaf ℳ))
      ⟶ (Scheme.Modules.pullback (relativeProjChart s' p.1.1)).obj (moduleSheaf ℳ') :=
  ((Scheme.Modules.pullbackComp (relativeProjChart s' p.1.1)
        (relativeProjBaseChange g Φ hΦ)).app (moduleSheaf ℳ)).hom
    ≫ moduleSheafBaseChangeChartHom g Φ hΦ Ψ hΨ p
    ≫ (moduleSheafChartIso ℳ' p.1.1).inv
    ≫ (Scheme.Modules.restrictFunctorIsoPullback
        (relativeProjChart s' p.1.1)).hom.app (moduleSheaf ℳ')

include hΨ in
/-- **The chart member of the base-change comparison is the `ofPullback` of its reading on
inverse images.** The two appearances of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` at `ℳ̃'` cancel. -/
public theorem moduleSheafBaseChangeRestrictHom_eq_ofPullback (p : (baseChangeCover g).I₀) :
    moduleSheafBaseChangeRestrictHom g Φ hΦ Ψ hΨ p
      = ofPullback (relativeProjChart s' p.1.1)
          (moduleSheafBaseChangePullbackHom g Φ hΦ Ψ hΨ p) := by
  simp only [ofPullback, moduleSheafBaseChangePullbackHom, moduleSheafBaseChangeRestrictHom,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.app_hom]

end Pullback

end Stacks.RelativeProj.Situation

end
