module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.TwistChartBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChange

/-!
# The twisting sheaves of a relative `Proj` base change, on a chart

Let `g : S' ⟶ S` be a morphism of schemes, let `s` and `s'` be relative `Proj` situations over
`S` and `S'`, let `Φ` identify the graded algebra of `s'` with the pullback along `g` of that of
`s` isomorphically in every nonnegative degree, and let
`r = relativeProjBaseChange g Φ hΦ : Proj_{S'}(𝒜') ⟶ Proj_S(𝒜)` be the base-change morphism of
the two relative projective spectra. The second assertion of Tag 01O3 is a graded isomorphism

`θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(n)) ⟶ ⨁_{n ∈ ℤ} 𝒪_{Proj_{S'}(𝒜')}(n)`.

This file constructs its degree-`n` component **on each chart** of `Proj_{S'}(𝒜')` and proves
that each chart component is an isomorphism. The charts are indexed by pairs `W' ⊆ g⁻¹W` of
affine opens of `S'` and of `S`, as they are for the base-change morphism of schemes itself: an
affine open of `S'` need not map into any single affine open of `S`, so there is no choice-free
indexing by affine opens of `S'` alone.

On the chart over such a pair the component is the absolute comparison. The chart of
`Proj_{S'}(𝒜')` over `W'` followed by `r` factors through the chart of `Proj_S(𝒜)` over `W` by
`AlgebraicGeometry.Proj.map` of the base change of graded section rings
(`Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange_eq`); `𝒪(n)` pulled
back along a morphism factoring through a chart is the pullback of the chart twist
(`Stacks.RelativeProj.Situation.twistSheafPullbackChartIso`); and between the chart twists the
base change of graded section rings induces Tag 01MY's comparison
`Stacks.ProjTwistComparison.twistMap`, which is an isomorphism by
`Stacks.RelativeProj.Situation.isIso_twistMap_gradedBaseChange`.

## Main definitions

* `Stacks.RelativeProj.Situation.twistSheafBaseChangeChartHom`: `𝒪_{Proj_S(𝒜)}(n)` pulled back
  along the chart of `Proj_{S'}(𝒜')` over `W'` followed by `r`, compared with the chart twist of
  `s'` over `W'`.
* `Stacks.RelativeProj.Situation.twistSheafBaseChangeRestrictHom`: the same read as a morphism of
  the restrictions of `r^* 𝒪_{Proj_S(𝒜)}(n)` and of `𝒪_{Proj_{S'}(𝒜')}(n)` to the chart over
  `W'`.

## Main results

* `Stacks.RelativeProj.Situation.isIso_twistSheafBaseChangeChartHom` and
  `isIso_twistSheafBaseChangeRestrictHom`: **the chart components of `θ` are isomorphisms**, in
  every degree and with no hypothesis beyond the two situations and the datum `Φ`.

## Not done here

No tag attribute is claimed. Tag 01O3's twist assertion is global, and gluing these chart
components into a morphism `r^* 𝒪_{Proj_S(𝒜)}(n) ⟶ 𝒪_{Proj_{S'}(𝒜')}(n)` on all of
`Proj_{S'}(𝒜')` is not done. The cover combinatorics that gluing needs is already available and
is stated with no reference to the sheaves involved —
`Stacks.RelativeProj.Situation.iSup_image_top_baseChangeCover`,
`image_top_baseChangeCover_inf_le_iSup` and `localApp_baseChangeCover_eq_of_nested` of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleBaseChangeGlue.lean` — so
what is missing is the agreement of two chart components over a *nested* pair of indices. For
the sheaf of a graded module that agreement is
`Stacks.RelativeProj.Situation.moduleChartBaseChangeHom_comp_eq_of_target_le` and
`moduleSheafBaseChangePullbackHom_source_le`, and it rests on the composition law
`Stacks.ProjModuleComparison.moduleMap_comp_of_eq` and the chart-refinement law
`Stacks.RelativeProj.Situation.pullbackCongr_inv_comp_moduleMap`; neither of those two laws has a
counterpart for `Stacks.ProjTwistComparison.twistMap` in the library, and they are what the twist
case still needs.

Multiplicativity of `θ` — its compatibility with the maps `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)` and with the
unit — is not treated either, exactly as it is not for clause (3) of Tag 01N2 in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjBaseChangeTwist.lean`.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.RelativeProj.Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ))) (n : ℤ)

/-- **`𝒪_{Proj_S(𝒜)}(n)` pulled back to a chart of the base-changed relative projective
spectrum, compared with the chart twist of `s'`.** The pullback along the chart over `W'`
followed by the base-change morphism is the pullback of the chart twist over `W`, because that
composite factors through the chart over `W`; there the comparison is the absolute one. -/
public def twistSheafBaseChangeChartHom (p : (baseChangeCover g).I₀) :
    (Scheme.Modules.pullback
        (relativeProjChart s' p.1.1 ≫ relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n)
      ⟶ twistChart s' n p.1.1 :=
  (twistSheafPullbackChartIso s n p.1.2
      (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
        (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ))
      (relativeProjChart_comp_relativeProjBaseChange_eq g Φ hΦ p)).hom
    ≫ Stacks.ProjTwistComparison.twistMap (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
        (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ) n

/-- **The chart component of `θ` is an isomorphism.** It is an isomorphism of chart
identifications followed by Tag 01MY's comparison for the base change of graded section rings,
and that is invertible by
`Stacks.RelativeProj.Situation.isIso_twistMap_gradedBaseChange`. -/
public instance isIso_twistSheafBaseChangeChartHom (p : (baseChangeCover g).I₀) :
    IsIso (twistSheafBaseChangeChartHom g Φ hΦ n p) := by
  have : IsIso (Stacks.ProjTwistComparison.twistMap
      (gradedBaseChange g Φ p.1.2.1 p.1.1.1 p.2)
      (irrelevant_le_gradedBaseChange g Φ p.1.2 p.1.1 p.2 hΦ) n) :=
    isIso_twistMap_gradedBaseChange g Φ hΦ p.1.2 p.1.1 p.2 n
  exact IsIso.comp_isIso

/-- **The chart component of `θ` read as a morphism of the restrictions to the chart over `W'`.**
This is `Stacks.RelativeProj.Situation.twistSheafBaseChangeChartHom` with the restriction along
the chart identified with the pullback along it on the left and `𝒪_{Proj_{S'}(𝒜')}(n)` identified
with its chart twist on the right.

This is the shape a gluing of the chart components consumes: it is the family `ψ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` over the chart cover
`Stacks.RelativeProj.Situation.baseChangeCover` of `Proj_{S'}(𝒜')`. -/
public def twistSheafBaseChangeRestrictHom (p : (baseChangeCover g).I₀) :
    ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj
        (twistSheaf s n)).restrict (relativeProjChart s' p.1.1)
      ⟶ (twistSheaf s' n).restrict (relativeProjChart s' p.1.1) :=
  ((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s' p.1.1)).app
      ((Scheme.Modules.pullback (relativeProjBaseChange g Φ hΦ)).obj (twistSheaf s n))).hom
    ≫ ((Scheme.Modules.pullbackComp (relativeProjChart s' p.1.1)
        (relativeProjBaseChange g Φ hΦ)).app (twistSheaf s n)).hom
    ≫ twistSheafBaseChangeChartHom g Φ hΦ n p
    ≫ (twistSheafChartIso s' n p.1.1).inv

/-- **The chart component of `θ`, read on the restrictions, is an isomorphism.** -/
public instance isIso_twistSheafBaseChangeRestrictHom (p : (baseChangeCover g).I₀) :
    IsIso (twistSheafBaseChangeRestrictHom g Φ hΦ n p) := by
  unfold twistSheafBaseChangeRestrictHom
  infer_instance

end Stacks.RelativeProj.Situation

end
