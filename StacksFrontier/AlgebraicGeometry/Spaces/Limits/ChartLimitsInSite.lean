module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Inverse systems whose affine charts have their limits inside the site

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms. For an affine scheme-valued point `f₀ : U₀ ⟶ D i₀` of a stage, the base changes
`U_j = D j ×_{D i₀} U₀` of the later stages are affine objects of the site
(`AlgebraicGeometry.Space.AffineChartSystem`), and their limit *in schemes* is the affine scheme
`Spec (colim_j Γ(U_j))`. The proof of Stacks 07SF, and with it every argument of Stacks 07SK,
07V7 and their relatives, uses that this scheme is the chart `X ×_{X_{i₀}} U₀` of the limit
`X = lim D`. In the big fppf site of `S`, which is cut off at `B.cutoff`, this holds exactly
when the limit in schemes lies in the site. That is the standing convention of the chapter on
limits of algebraic spaces (Section 70.2, tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`; this file reads it on chart systems.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_iff`: the convention says exactly that
  for every stage, every affine point of it and every chart system there, the limit in schemes
  of the charts is an object of the site.
* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_hasBoundedBaseChanges`: the convention
  holds when the base changes of every stage along affine points are bounded below the cutoff.
* `AlgebraicGeometry.Space.exists_isLimit_contains_of_iso`: the condition on one chart system is
  invariant under reindexing.

## Implementation notes

**Why some condition is needed.** The literal reading of "let `X = lim X_i`" as the limit of the
system in presheaves (equivalently, in algebraic spaces) on the size-bounded site makes Stacks
07V7 false. Take `S = Spec ℚ`, a field `L` of cardinality at least `B.cutoff` that is the union
of a directed family of countable subfields `L_i`, and `X_i = Spec (ℚ × L_i)`. These are affine
objects of the site with affine transition morphisms. A morphism from an object `V` of the site
to the limit of the `X_i` is a ring map `ℚ × L ⟶ Γ(V, 𝒪_V)`; since `L` is a field larger than
`Γ(V, 𝒪_V)` it must be killed, so the limit in the site is `Spec ℚ = S`, while the limit in
schemes is `Spec (ℚ × L)`, which is not in the site. On `X_i` the endomorphism of `𝒪_{X_i}` given
by multiplication by the idempotent `(0, 1)` is nonzero at every stage, yet its inverse image to
`X = Spec ℚ` is zero: the faithfulness clause of Stacks 07V7 fails. The condition of this file
excludes exactly this collapse, and Stacks' own construction of the limit (the proof of Stacks
07SF, with `U = lim U_i` a limit of schemes) presupposes it.

**Why this condition rather than a bound on the index.** It is implied both by the bound on the
index category used by `AlgebraicGeometry.Space.AffineChartSystem.limitBridge` and by the
bounded base changes `AlgebraicGeometry.Space.HasBoundedBaseChanges` of Stacks 07SQ, but neither
implies it in the other direction: a cofiltered system of affine schemes of the site indexed by
an arbitrarily large category whose limit in schemes is an object of the site — which is what
Artin's Axioms, Definition 07XL quantifies over — satisfies it, as do all of its base changes,
and has no bounded base changes.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace AffineChartSystem

variable {I : Type u} [Category.{u} I] {i₀ : I} {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- The isomorphism of a chart system with the base changes is natural in the stage. -/
private theorem iso_hom_app_naturality (C : AffineChartSystem B S hS i₀ D U₀ f₀) {j k : Over i₀}
    (e : j ⟶ k) :
    yoneda.map (C.siteDiagram.map e) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map e :=
  C.iso.hom.naturality e

/-- The projections of the charts to their stages are natural in the stage. -/
theorem stageMap_comp_map (C : AffineChartSystem B S hS i₀ D U₀ f₀) {j k : Over i₀}
    (e : j ⟶ k) :
    C.stageMap j ≫ D.map e.left = yoneda.map (C.siteDiagram.map e) ≫ C.stageMap k := by
  symm
  have hfst : (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map e ≫
        stageBaseChangeFst B S hS i₀ D U₀ f₀ k =
      stageBaseChangeFst B S hS i₀ D U₀ f₀ j ≫ D.map e.left := by
    dsimp [stageBaseChangeFst, Over.pullback, Over.post]
    simp only [Over.homMk_left, pullback.lift_fst]
  simp only [stageMap]
  rw [← Category.assoc, iso_hom_app_naturality C e, Category.assoc, hfst, Category.assoc]

/-- The projections of the charts to `U₀` are compatible with the transition morphisms. -/
theorem map_baseMap (C : AffineChartSystem B S hS i₀ D U₀ f₀) {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (C.siteDiagram.map e) ≫ C.baseMap k = C.baseMap j := by
  have hsnd : (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map e ≫
        stageBaseChangeSnd B S hS i₀ D U₀ f₀ k = stageBaseChangeSnd B S hS i₀ D U₀ f₀ j := by
    dsimp [stageBaseChangeSnd, Over.pullback, Over.post]
    simp only [Over.homMk_left, pullback.lift_snd]
  simp only [baseMap]
  rw [← Category.assoc, iso_hom_app_naturality C e, Category.assoc, hsnd]

end AffineChartSystem

/-- The limit cone of a chart system in the site, read in schemes, witnesses the condition. -/
theorem AffineChartSystem.LimitBridge.exists_cone {I : Type u} [Category.{u} I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge) :
    ∃ c : Cone C.schemeDiagram, Nonempty (IsLimit c) ∧ B.Contains c.pt :=
  ⟨_, ⟨L.schemeIsLimit⟩, L.cone.pt.left.property⟩

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The chapter's convention (Stacks 07SD), read on chart systems.** The limits of the affine
charts of `D` lie in the site in the sense of
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` — on every limit cone of every lift of the
diagram of base changes — exactly when for every stage `i₀`, every affine scheme-valued point
`f₀ : U₀ ⟶ D i₀` and every system of affine charts `U_j = D j ×_{D i₀} U₀`, some limit of the
charts in the category of all schemes is an object of the big fppf site of `S`. A chart system is
such a lift, and a limit of schemes inside the site bounds the size of every other limit, which is
isomorphic to it. -/
theorem siteContainsBaseChangeLimits_iff :
    SiteContainsBaseChangeLimits B S hS D ↔
      ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
        (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
        (C : AffineChartSystem B S hS i₀ D U₀ f₀),
        ∃ c : Cone C.schemeDiagram, Nonempty (IsLimit c) ∧ B.Contains c.pt := by
  refine ⟨fun h i₀ U₀ f₀ C => ?_, fun h i Z g W e c hc => ?_⟩
  · exact (C.limitBridgeOfLimitInSite
      (C.limitInSite_of_siteContainsBaseChangeLimits h)).exists_cone
  · obtain ⟨c₀, ⟨hc₀⟩, hcont⟩ := h i Z g ⟨W, e⟩
    show c.pt.size < B.cutoff
    rw [Scheme.size_congr (hc.conePointUniqueUpToIso hc₀)]
    exact hcont

/-- **An inverse system with bounded base changes satisfies the chapter's convention**
(`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBounded`). -/
theorem siteContainsBaseChangeLimits_of_hasBoundedBaseChanges
    (hb : ∀ i, HasBoundedBaseChanges B S hS i D) : SiteContainsBaseChangeLimits B S hS D :=
  (siteContainsBaseChangeLimits_iff D).2 fun i₀ _ _ C =>
    (C.limitBridgeOfBounded (C.diagramBoundedBelow (hb i₀))).exists_cone

/-- **The condition is invariant under reindexing a chart system.** If the diagram of schemes `E₂`
is isomorphic to the reindexing along an equivalence of a diagram `E₁` whose limit in schemes
lies in the site, then so does the limit of `E₂`, with the same vertex. -/
theorem exists_isLimit_contains_of_iso {J₁ J₂ : Type*} [Category* J₁] [Category* J₂]
    {E₁ : J₁ ⥤ Scheme.{u}} {E₂ : J₂ ⥤ Scheme.{u}} (e : J₂ ≌ J₁) (α : E₂ ≅ e.functor ⋙ E₁)
    (h : ∃ c : Cone E₁, Nonempty (IsLimit c) ∧ B.Contains c.pt) :
    ∃ c : Cone E₂, Nonempty (IsLimit c) ∧ B.Contains c.pt := by
  obtain ⟨c, ⟨hc⟩, hcont⟩ := h
  exact ⟨(Cone.postcompose α.inv).obj (c.whisker e.functor),
    ⟨(IsLimit.postcomposeInvEquiv α _).symm (hc.whiskerEquivalence e)⟩, hcont⟩

end AlgebraicGeometry.Space

end
