module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitsInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleAffineSystem

/-!
# The limit of an inverse system of algebraic spaces with its charts inside the site

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms. This file records the standing hypothesis under which Stacks 07V7 is proved in the
files that follow — the limit `lim D` is an algebraic space and the affine charts of `D` have
their limits inside the site (`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`) — together
with the limit read as an algebraic space, its projections, and the faithfulness clause of Stacks
07V7 under that hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.HasSiteLimit`: the standing hypothesis.
* `AlgebraicGeometry.Space.limitSpace` and `AlgebraicGeometry.Space.limitSpaceProjection`: the
  limit and its projections, as an object and morphisms of the category of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.hasSiteLimit_of_lt_cof`: an index category small compared to the
  cofinality of the cutoff provides the standing hypothesis, and then
  `AlgebraicGeometry.Space.limitSpace` is `AlgebraicGeometry.Space.limitAlgebraicSpace`.
* `AlgebraicGeometry.Space.eventually_eq_of_modulePullback_limitSpaceProjection_eq`: **Stacks
  07V7, faithfulness**, under the standing hypothesis.

## Implementation notes

The algebraicity of the limit is part of the hypothesis rather than a consequence of it, as in
`AlgebraicGeometry.Space.MorphismDescentSystem` and `AlgebraicGeometry.Space.DescentSituation`:
the situation of Stacks 07SK speaks of the limit `X` as an algebraic space. The tagged form of
Stacks 07V7, `AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_isLimit`, takes an
algebraic space with a limiting cone, so that algebraicity is part of its data.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The standing hypothesis of Stacks 07SK, read in the site.** The transition morphisms of the
inverse system `D` are affine, its limit is an algebraic space over `S`, and the affine charts of
`D` have their limits inside the site, so that the limit is the one the source constructs in the
proof of Stacks 07SF. -/
def HasSiteLimit {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Prop :=
  (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) ∧ IsAlgebraicSpace B S hS (limit D) ∧
    SiteContainsBaseChangeLimits B S hS D

variable {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **An inverse system indexed by a small category has its limit in the site**: Stacks 07SF
and the limits of the affine charts of `AlgebraicGeometry.Space.AffineChartSystem.limitBridge`. -/
theorem hasSiteLimit_of_lt_cof [IsCofiltered I] (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    HasSiteLimit B S hS D :=
  ⟨hAffine, isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine,
    IsSiteSmall.siteContainsBaseChangeLimits B S hS D (IsSiteSmall.of_lt_cof hSize hHomSize)⟩

variable (hL : HasSiteLimit B S hS D) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- The limit of the system, as an object of the category of algebraic spaces over `S`. -/
noncomputable def limitSpace : AlgebraicSpaces B S hS := ⟨limit D, hL.2.1⟩

/-- The projection of the limit to a stage, as a morphism of algebraic spaces over `S`. -/
noncomputable def limitSpaceProjection (i : I) :
    limitSpace B S hS D hL ⟶ stageAlgebraicSpace B S hS D hD i :=
  ObjectProperty.homMk (limit.π D i)

/-- The projections of the limit are compatible with the transition morphisms. -/
theorem limitSpaceProjection_comp {i j : I} (e : j ⟶ i) :
    limitSpaceProjection B S hS D hL hD j ≫ stageTransition B S hS D hD e =
      limitSpaceProjection B S hS D hL hD i :=
  ObjectProperty.hom_ext _ (limit.w D e)

/-- For a small index category the limit space is the limit algebraic space of Stacks 07SF. -/
theorem limitSpace_eq_limitAlgebraicSpace [IsCofiltered I] (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    limitSpace B S hS D (hasSiteLimit_of_lt_cof B S hS D hD hSize hHomSize hAffine) =
      limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine :=
  rfl

/-! ### Faithfulness -/

section Faithfulness

variable [IsCofiltered I]

/-- **Stacks 07V7, faithfulness**, with the affine chart system and its limit given. -/
private theorem eventually_eq_of_chartSystem' {i₀ : I} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) (L : AffineChartSystem.LimitBridge C)
    (hf₀ : IsEtale B S hS f₀)
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀)
    (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i₀).1
      (stageAlgebraicSpace B S hS D hD i₀).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i₀)).map φ =
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i₀)).map ψ) :
    ∃ (j : I) (e : j ⟶ i₀),
      (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
        (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ := by
  let base : Over i₀ := Over.mk (𝟙 i₀)
  let cmBase : schemeSpace (C.siteDiagram.obj base) ⟶
      stageAlgebraicSpace B S hS D hD i₀ := chartStageMap B S hS D hD U₀ f₀ C base
  let ell : schemeSpace L.cone.pt ⟶ limitSpace B S hS D hL := ObjectProperty.homMk L.toLimit
  have key : schemeSpaceMap (L.cone.π.app base) ≫ cmBase =
      ell ≫ limitSpaceProjection B S hS D hL hD i₀ :=
    ObjectProperty.hom_ext _ (L.toLimit_comp_limitπ base).symm
  have hchart : (modulePullback B S hS (schemeSpaceMap (L.cone.π.app base))).map
        ((modulePullback B S hS cmBase).map φ) =
      (modulePullback B S hS (schemeSpaceMap (L.cone.π.app base))).map
        ((modulePullback B S hS cmBase).map ψ) := by
    have h₁ : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i₀) ⋙
          modulePullback B S hS ell).map φ =
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i₀) ⋙
          modulePullback B S hS ell).map ψ :=
      congrArg (modulePullback B S hS ell).map h
    exact Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
      (modulePullbackCompIso B S hS ell (limitSpaceProjection B S hS D hL hD i₀) ≪≫
          eqToIso (congrArg (fun t => modulePullback B S hS t) key.symm) ≪≫
          (modulePullbackCompIso B S hS (schemeSpaceMap (L.cone.π.app base))
            cmBase).symm) h₁
  obtain ⟨k, e, hk⟩ := eventualModuleMapEqOverAffineSystem B S hS C.siteDiagram C.isAffine_obj
    L.cone L.schemeIsLimit base
    ((modulePullback B S hS cmBase).obj M) ((modulePullback B S hS cmBase).obj N)
    (isFinitePresentationOnSite_modulePullback B S hS cmBase M hM)
    (isFinitePresentationOnSite_modulePullback B S hS cmBase N hN)
    ((modulePullback B S hS cmBase).map φ) ((modulePullback B S hS cmBase).map ψ) hchart
  refine ⟨k.left, k.hom, ?_⟩
  have key' : schemeSpaceMap (C.siteDiagram.map e) ≫ cmBase =
      chartStageMap B S hS D hD U₀ f₀ C k ≫ stageTransition B S hS D hD k.hom := by
    apply ObjectProperty.hom_ext
    show yoneda.map (C.siteDiagram.map e) ≫ C.stageMap base = C.stageMap k ≫ D.map k.hom
    rw [← C.stageMap_comp_map e, (Category.comp_id e.left).symm.trans (Over.w e)]
  have hstage : (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C k)).map
        ((modulePullback B S hS (stageTransition B S hS D hD k.hom)).map φ) =
      (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C k)).map
        ((modulePullback B S hS (stageTransition B S hS D hD k.hom)).map ψ) := by
    have h₁ : (modulePullback B S hS cmBase ⋙
          modulePullback B S hS (schemeSpaceMap (C.siteDiagram.map e))).map φ =
        (modulePullback B S hS cmBase ⋙
          modulePullback B S hS (schemeSpaceMap (C.siteDiagram.map e))).map ψ := hk
    exact Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
      (modulePullbackCompIso B S hS (schemeSpaceMap (C.siteDiagram.map e)) cmBase ≪≫
          eqToIso (congrArg (fun t => modulePullback B S hS t) key') ≪≫
          (modulePullbackCompIso B S hS (chartStageMap B S hS D hD U₀ f₀ C k)
            (stageTransition B S hS D hD k.hom)).symm) h₁
  have : (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C k)).Faithful :=
    faithful_modulePullback B S hS (C.siteDiagram.obj k)
      (chartStageMap B S hS D hD U₀ f₀ C k)
      (isEtale_of_isPullback_yoneda B S hS (C.isPullback k).flip hf₀)
      (have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
          (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
        MorphismProperty.relative_isStableUnderBaseChange _
      MorphismProperty.of_isPullback (C.isPullback k).flip hs₀)
  exact (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C k)).map_injective hstage

/-- **Stacks 07V7, the faithfulness clause of the colimit assertion, for a limit inside the
site.** Two morphisms of finitely presented `𝒪_{X_i}`-modules on a quasi-compact stage whose
inverse images along the projection of the limit agree already have equal inverse images along a
transition morphism from a later stage.

The proof is the source's reduction to a surjective étale affine chart `U₀ ⟶ X_i`: the limit of
the chart system lies in the site by hypothesis, it is the chart of the limit, and Stacks 01ZR(3)
on that system of affine schemes produces the later stage. -/
theorem eventually_eq_of_modulePullback_limitSpaceProjection_eq (i : I)
    (hQc : IsQuasiCompactSpace B S hS (D.obj i))
    (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).map φ =
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).map ψ) :
    ∃ (j : I) (e : j ⟶ i),
      (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
        (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ := by
  obtain ⟨V₀, f₀, hV₀, hs₀, hf₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i) (hD i)).mp hQc
  let C := affineChartSystem B S hS i D ⟨V₀, hV₀⟩ f₀ hL.1
  exact eventually_eq_of_chartSystem' B S hS D hL hD C
    (C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hL.2.2)) hf₀ hs₀
    M N hM hN φ ψ h

end Faithfulness

end AlgebraicGeometry.Space

end
