module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Finitely presented modules over an inverse limit of algebraic spaces

Let `D` be a cofiltered inverse system of algebraic spaces over a scheme `S` with affine
transition morphisms, small enough for the big fppf site, and let `X = lim D`. Stacks 07V7
asserts that the category of `𝒪_X`-modules of finite presentation is the colimit over the
index category of the categories of `𝒪_{X_i}`-modules of finite presentation, the comparison
functor being induced by the inverse images along the projections of the limit.

This file sets up that limit situation in the vocabulary of Stacks 07SK — the same index
category, the same diagram of presheaves, the same projections — and proves the **faithfulness
clause** of the colimit assertion.

## Main definitions

* `AlgebraicGeometry.Space.limitAlgebraicSpace` and `AlgebraicGeometry.Space.stageAlgebraicSpace`
  read the limit and the stages of the system as objects of the category of algebraic spaces,
  so that the inverse image of modules of Stacks 03LU applies to the projections.
* `AlgebraicGeometry.Space.limitProjection` and `AlgebraicGeometry.Space.stageTransition` are
  the projections of the limit and the transition morphisms, as morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.EventualModuleMapEqOverAffineSystem` is the affine case of the
  faithfulness clause, carried as a named hypothesis; see below.

## Main results

* `AlgebraicGeometry.Space.eventually_eq_of_modulePullback_limitProjection_eq`: **Stacks 07V7,
  faithfulness.** Two morphisms of finitely presented `𝒪_{X_i}`-modules whose inverse images
  to the limit agree already have equal inverse images at a later stage.

## What of Stacks 07V7 is covered

The colimit assertion has three halves: essential surjectivity (every finitely presented
`𝒪_X`-module is an inverse image from a stage), fullness (a morphism between inverse images
comes from a later stage) and faithfulness. Only faithfulness is proved here, and the tag's
clause says so.

That the system of categories and comparison functors exists at all — that the inverse image
along a morphism of algebraic spaces carries finitely presented modules to finitely presented
modules — is not restated here: it is the library's Stacks 03DO for Stacks 03DL(7),
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`, and it is what supplies
the finite presentation hypotheses of the carried affine case below.

The other two halves are out of reach in this tree, and for a reason that is worth recording.
The source proves Stacks 07V7 by choosing an étale presentation `X = U/R` with `U = lim U_i`
affine and `R = lim R_i`, applying the scheme-level colimit statement Stacks 01ZR on `U`, `R`
and `R ×_{s, U, t} R`, and transporting the result along the equivalence
`QCoh(𝒪_X) = QCoh(U, R, s, t, c)` of Properties of Spaces, Proposition 66.32.1 (Stacks 03M3).
Of that equivalence this tree has only the functor in one direction,
`AlgebraicGeometry.Space.quasicoherentFromSpaceBase`, whose own tag records that neither its
full faithfulness nor its essential surjectivity is available. Faithfulness needs no descent of
objects or of morphisms, only that an equality of morphisms of modules may be checked on a
surjective étale chart, which *is* available as
`AlgebraicGeometry.Space.faithful_modulePullback`; that is why this half goes through and the
other two do not.

## The carried affine case

`AlgebraicGeometry.Space.EventualModuleMapEqOverAffineSystem` is the faithfulness clause for an
inverse system of *affine* schemes of the site: for a cofiltered diagram `E` of objects of the
big fppf site with affine underlying schemes whose underlying schemes form a limit at a cone
`c`, two morphisms of finitely presented modules on the algebraic space of a stage whose
inverse images to the algebraic space of `c.pt` agree have equal inverse images at a later
stage.

This is Stacks 01ZR, part (3), read on the small étale ringed sites of those representable
algebraic spaces. The tree proves Stacks 01ZR(3) —
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit` — for Mathlib's
`AlgebraicGeometry.Scheme.Modules`, the sheaves of modules on the *Zariski* site of opens of a
scheme, whereas the modules of an algebraic space are sheaves on its small étale site.

What is missing is exactly the change of site, and not the two renderings of finite
presentation: `SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'` in
`StacksFrontier/AlgebraicGeometry/Topologies/FinitePresentationOnSiteUniverses.lean` passes from
the on-site notion of Stacks 03DL(7) to Mathlib's `SheafOfModules.IsFinitePresentation` on an
arbitrary site and in an arbitrary module universe.

The change of site is a functor with no inverse. Both directions exist for the algebraic space
a scheme of the site represents — `AlgebraicGeometry.Space.representedAssociatedModule` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleComparison.lean` and
`AlgebraicGeometry.Space.representedZariskiRestrictionFunctor` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiRestriction.lean` — and the notes of
the second say that "no adjunction between the two directions is claimed and neither composite
is identified with an identity: that is Stacks 03DX (2)". What Stacks 03DX(2) is missing is one
step: `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcohOnSite` is unconditional,
and the equivalence is proved over the essential surjectivity
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`, which
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean` does
not have. Supplying that would discharge the hypothesis below, after the compatibility of the
comparison with inverse images, which those notes also record as unproved. So the affine case
is carried, as Stacks 07VT carries its three cited inputs in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineOfUniversallyClosedSurjection.lean`.

The carried statement is about inverse systems all of whose stages are affine schemes of the
site; the conclusion below is about a system of arbitrary quasi-compact algebraic spaces, and
the step between the two — the only content here — is the reduction to a surjective étale
affine chart, which is the first paragraph of the source's proof.

## Implementation notes

The chart system is `AlgebraicGeometry.Space.affineChartSystem` and its limit
`AlgebraicGeometry.Space.AffineChartSystem.limitBridge`, from
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineChartSystem.lean`: it is indexed by the
slice `CategoryTheory.Over i` at the stage `i` carrying the two morphisms, and the carried
affine case is instantiated there, at the slice's base object `Over.mk (𝟙 i)`. That object's
chart is the base change of the chosen chart along `D.map (𝟙 i)` rather than the chart itself;
as in `StacksFrontier/AlgebraicGeometry/ModuleLimits/EventualMapEq.lean` no isomorphism is
transported to repair this, the argument simply runs with the base change throughout.

All identifications of iterated inverse images are the canonical composition comparisons
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU, and they are used only through
`Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso`: an equality of images of two parallel
morphisms under one functor passes to any isomorphic functor, so no coherence between the
comparisons is needed.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-! ### The limit situation of Stacks 07SK, read in the category of algebraic spaces -/

/-- The limit of the system, as an object of the category of algebraic spaces over `S`. -/
noncomputable def limitAlgebraicSpace : AlgebraicSpaces B S hS :=
  ⟨limit D, isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine⟩

/-- A stage of the system, as an object of the category of algebraic spaces over `S`. -/
def stageAlgebraicSpace (i : I) : AlgebraicSpaces B S hS := ⟨D.obj i, hD i⟩

/-- The projection of the limit to a stage, as a morphism of algebraic spaces over `S`. -/
noncomputable def limitProjection (i : I) :
    limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine ⟶
      stageAlgebraicSpace B S hS D hD i :=
  ObjectProperty.homMk (limit.π D i)

/-- A transition morphism of the system, as a morphism of algebraic spaces over `S`. -/
def stageTransition {i j : I} (e : i ⟶ j) :
    stageAlgebraicSpace B S hS D hD i ⟶ stageAlgebraicSpace B S hS D hD j :=
  ObjectProperty.homMk (D.map e)

/-- The projections of the limit are compatible with the transition morphisms. -/
theorem limitProjection_comp {i j : I} (e : j ⟶ i) :
    limitProjection B S hS D hSize hHomSize hD hAffine j ≫ stageTransition B S hS D hD e =
      limitProjection B S hS D hSize hHomSize hD hAffine i := by
  apply ObjectProperty.hom_ext
  exact limit.w D e

/-! ### The affine case, as a named hypothesis -/

/-- **Stacks 01ZR, part (3) on the small étale ringed sites of affine schemes of the big fppf
site**, as a named hypothesis: for a cofiltered inverse system `E` of objects of the big fppf
site of `S` with affine underlying schemes whose underlying schemes form a limit at a cone `c`,
two morphisms of finitely presented modules on the algebraic space of a stage whose inverse
images to the algebraic space of `c.pt` agree already have equal inverse images at a later
stage.

The module documentation records why this is carried rather than deduced: the tree's Stacks
01ZR(3) concludes about Mathlib's Zariski `AlgebraicGeometry.Scheme.Modules`, and the
comparison with the small étale modules of an algebraic space is not available. -/
def EventualModuleMapEqOverAffineSystem : Prop :=
  ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ BigFppfOver B S hS),
    (∀ j : J, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j))) →
      ∀ c : Cone E, IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) → ∀ j : J,
        ∀ M N : Modules.{u, u} B S hS (schemeSpace (E.obj j)).1
            (schemeSpace (E.obj j)).2,
          M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
            (modulePullback B S hS (schemeSpaceMap (c.π.app j))).map φ =
                (modulePullback B S hS (schemeSpaceMap (c.π.app j))).map ψ →
              ∃ (k : J) (e : k ⟶ j),
                (modulePullback B S hS (schemeSpaceMap (E.map e))).map φ =
                  (modulePullback B S hS (schemeSpaceMap (E.map e))).map ψ

/-! ### The reduction to an affine chart -/

section Chart

variable {i₀ : I} (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)

omit [IsCofiltered I] hSize hHomSize hD hAffine in
/-- The projections of the base changes of the stages above `i₀` along `f₀` to those stages are
natural in the stage. -/
private theorem stageBaseChangeFst_naturality {j k : Over i₀} (e : j ⟶ k) :
    (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map e ≫
        stageBaseChangeFst B S hS i₀ D U₀ f₀ k =
      stageBaseChangeFst B S hS i₀ D U₀ f₀ j ≫ D.map e.left := by
  dsimp [stageBaseChangeFst, Over.pullback, Over.post]
  simp only [Over.homMk_left, pullback.lift_fst]

omit [IsCofiltered I] hSize hHomSize hD hAffine in
/-- The projections of the charts to their stages are natural in the stage. -/
private theorem stageMap_naturality (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (C.siteDiagram.map e) ≫ C.stageMap k = C.stageMap j ≫ D.map e.left := by
  have hnat : yoneda.map (C.siteDiagram.map e) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map e :=
    C.iso.hom.naturality e
  have hfst := stageBaseChangeFst_naturality B S hS D U₀ f₀ e
  calc yoneda.map (C.siteDiagram.map e) ≫ C.stageMap k
      = (yoneda.map (C.siteDiagram.map e) ≫ C.iso.hom.app k) ≫
          stageBaseChangeFst B S hS i₀ D U₀ f₀ k := by
        rw [AffineChartSystem.stageMap, Category.assoc]
    _ = C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map e ≫
          stageBaseChangeFst B S hS i₀ D U₀ f₀ k := by rw [hnat, Category.assoc]
    _ = C.iso.hom.app j ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ j ≫ D.map e.left := by
        rw [hfst]
    _ = C.stageMap j ≫ D.map e.left := by rw [AffineChartSystem.stageMap, Category.assoc]

/-- The projection of a chart to its stage, as a morphism of algebraic spaces over `S`. -/
noncomputable def chartStageMap (C : AffineChartSystem B S hS i₀ D U₀ f₀) (j : Over i₀) :
    schemeSpace (C.siteDiagram.obj j) ⟶ stageAlgebraicSpace B S hS D hD j.left :=
  ObjectProperty.homMk (C.stageMap j)

variable {U₀ f₀}

omit [IsCofiltered I] hSize hHomSize hAffine in
/-- A chart is étale over its stage: it is a base change of the chart `f₀` of the stage
`i₀`. -/
private theorem isEtale_chartStageMap (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hf₀ : IsEtale B S hS f₀) (j : Over i₀) :
    IsEtale B S hS (chartStageMap B S hS D hD U₀ f₀ C j).hom :=
  isEtale_of_isPullback_yoneda B S hS (C.isPullback j).flip hf₀

omit [IsCofiltered I] hSize hHomSize hAffine in
/-- A chart is surjective onto its stage: it is a base change of the chart `f₀` of the stage
`i₀`. -/
private theorem surjective_chartStageMap (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀) (j : Over i₀) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (chartStageMap B S hS D hD U₀ f₀ C j).hom :=
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  MorphismProperty.of_isPullback (C.isPullback j).flip hs₀

omit [IsCofiltered I] hSize hHomSize hAffine in
/-- The inverse image along the projection of a chart to its stage is faithful: the chart is
surjective and étale. -/
private theorem faithful_modulePullback_chartStageMap
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) (hf₀ : IsEtale B S hS f₀)
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀) (j : Over i₀) :
    (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C j)).Faithful :=
  faithful_modulePullback B S hS (C.siteDiagram.obj j)
    (chartStageMap B S hS D hD U₀ f₀ C j)
    (isEtale_chartStageMap B S hS D hD C hf₀ j)
    (surjective_chartStageMap B S hS D hD C hs₀ j)

/-- **Stacks 07V7, faithfulness**, with the affine chart system and its limit given.

Two morphisms of finitely presented `𝒪_{X_{i₀}}`-modules whose inverse images to the limit
agree have equal inverse images over the chart of the limit, hence — by the carried affine case
applied to the chart system — over the chart of some later stage, hence over that stage itself,
because the inverse image along a surjective étale chart is faithful. -/
private theorem eventually_eq_of_chartSystem
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) (L : AffineChartSystem.LimitBridge C)
    (hf₀ : IsEtale B S hS f₀)
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀)
    (haffine : EventualModuleMapEqOverAffineSystem B S hS)
    (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i₀).1
      (stageAlgebraicSpace B S hS D hD i₀).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i₀)).map φ =
        (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i₀)).map ψ) :
    ∃ (j : I) (e : j ⟶ i₀),
      (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
        (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ := by
  let base : Over i₀ := Over.mk (𝟙 i₀)
  let cmBase : schemeSpace (C.siteDiagram.obj base) ⟶
      stageAlgebraicSpace B S hS D hD i₀ := chartStageMap B S hS D hD U₀ f₀ C base
  let ell : schemeSpace L.cone.pt ⟶
      limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine := ObjectProperty.homMk L.toLimit
  have key : schemeSpaceMap (L.cone.π.app base) ≫ cmBase =
      ell ≫ limitProjection B S hS D hSize hHomSize hD hAffine i₀ := by
    apply ObjectProperty.hom_ext
    exact (L.toLimit_comp_limitπ base).symm
  have hchart : (modulePullback B S hS (schemeSpaceMap (L.cone.π.app base))).map
        ((modulePullback B S hS cmBase).map φ) =
      (modulePullback B S hS (schemeSpaceMap (L.cone.π.app base))).map
        ((modulePullback B S hS cmBase).map ψ) := by
    have h₁ : (modulePullback B S hS (limitProjection B S hS D hSize hHomSize hD hAffine i₀) ⋙
          modulePullback B S hS ell).map φ =
        (modulePullback B S hS (limitProjection B S hS D hSize hHomSize hD hAffine i₀) ⋙
          modulePullback B S hS ell).map ψ :=
      congrArg (modulePullback B S hS ell).map h
    exact Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
      (modulePullbackCompIso B S hS ell
            (limitProjection B S hS D hSize hHomSize hD hAffine i₀) ≪≫
          eqToIso (congrArg (fun t => modulePullback B S hS t) key.symm) ≪≫
          (modulePullbackCompIso B S hS (schemeSpaceMap (L.cone.π.app base))
            cmBase).symm) h₁
  obtain ⟨k, e, hk⟩ := haffine C.siteDiagram C.isAffine_obj L.cone L.schemeIsLimit base
    ((modulePullback B S hS cmBase).obj M) ((modulePullback B S hS cmBase).obj N)
    (isFinitePresentationOnSite_modulePullback B S hS cmBase M hM)
    (isFinitePresentationOnSite_modulePullback B S hS cmBase N hN)
    ((modulePullback B S hS cmBase).map φ) ((modulePullback B S hS cmBase).map ψ) hchart
  refine ⟨k.left, k.hom, ?_⟩
  have hleft : e.left = k.hom :=
    (Category.comp_id e.left).symm.trans (Over.w e)
  have key' : schemeSpaceMap (C.siteDiagram.map e) ≫ cmBase =
      chartStageMap B S hS D hD U₀ f₀ C k ≫ stageTransition B S hS D hD k.hom := by
    apply ObjectProperty.hom_ext
    show yoneda.map (C.siteDiagram.map e) ≫ C.stageMap base = C.stageMap k ≫ D.map k.hom
    rw [stageMap_naturality B S hS D U₀ f₀ C e, hleft]
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
  have := faithful_modulePullback_chartStageMap B S hS D hD C hf₀ hs₀ k
  exact (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C k)).map_injective hstage

end Chart

/-! ### Faithfulness of the comparison functor -/

/-- **Stacks 07V7, the faithfulness clause of the colimit assertion.** Two morphisms of
finitely presented `𝒪_{X_i}`-modules on a stage of the system whose inverse images along the
projection of the limit agree already have equal inverse images along a transition morphism
from a later stage.

The proof is the source's reduction to an affine chart. Choose a surjective étale chart
`f₀ : U₀ ⟶ X_i` with `U₀` affine, available because `X_i` is quasi-compact, and base change the
later stages along it: this is a cofiltered system of affine schemes of the site whose limit is
the chart `U₀ ×_{X_i} X` of the limit, so the carried affine case applies to the inverse images
of the two morphisms to that chart and produces a later stage at which they agree over the
corresponding chart. The chart of that stage is again surjective and étale, so the inverse image
along it is faithful and the two morphisms agree over the stage itself. -/
@[stacks 07V7 "the faithfulness clause of the colimit assertion: two morphisms of finitely \
presented modules on a stage whose inverse images to the limit agree already agree at a later \
stage. Granted `haffine`, the same clause for an inverse system of affine schemes of the site, \
which is Stacks 01ZR(3) read on their small étale ringed sites — this tree proves Stacks \
01ZR(3) only for Mathlib's `Scheme.Modules` on the Zariski site of opens, and the comparison \
with the small étale modules of the algebraic space a scheme represents is a functor with no \
inverse: the notes of `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiRestriction.lean` \
record that neither composite is identified with an identity, that being Stacks 03DX(2), which \
is proved only over the essential surjectivity \
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule` that \
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean` does \
not have; the carried \
statement is about systems of affine schemes and the conclusion about systems of quasi-compact \
algebraic spaces, so it is not the universally quantified form of this conclusion. The \
essential surjectivity and fullness clauses of Stacks 07V7 are not covered: both need the \
equivalence `QCoh(𝒪_X) = QCoh(U, R, s, t, c)` of Stacks 03M3, of which this tree has only the \
functor in one direction"]
theorem eventually_eq_of_modulePullback_limitProjection_eq
    (haffine : EventualModuleMapEqOverAffineSystem B S hS) (i : I)
    (hQc : IsQuasiCompactSpace B S hS (D.obj i))
    (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i)).map φ =
        (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i)).map ψ) :
    ∃ (j : I) (e : j ⟶ i),
      (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
        (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ := by
  classical
  obtain ⟨V₀, f₀, hV₀, hs₀, hf₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i) (hD i)).mp hQc
  exact eventually_eq_of_chartSystem B S hS D hSize hHomSize hD hAffine
    (affineChartSystem B S hS i D ⟨V₀, hV₀⟩ f₀ hAffine)
    ((affineChartSystem B S hS i D ⟨V₀, hV₀⟩ f₀ hAffine).limitBridge hSize hHomSize)
    hf₀ hs₀ haffine M N hM hN φ ψ h

end AlgebraicGeometry.Space

end
