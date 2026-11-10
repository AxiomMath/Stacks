module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleBaseChangeSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism

/-!
# The fullness clause of Stacks 07V7

Let `D` be a cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces with
affine transition morphisms, and let `X` be its limit.  A morphism between the inverse images to
`X` of two finitely presented `𝒪_{X_i}`-modules is the inverse image of a morphism between their
inverse images to a later stage, through the canonical identification of iterated inverse
images.

## Main results

* `AlgebraicGeometry.Space.exists_homRestrict_eq_limitProjection`: the fullness clause, phrased
  through `AlgebraicGeometry.Space.moduleHomRestrict`.

## Implementation notes

The source's proof: pull the morphism back to an affine étale chart `U = lim U_j` of the limit,
descend it there to a stage by the affine case (Stacks 01ZR on the small étale sites,
`AlgebraicGeometry.Space.exists_homRestrict_eq_of_isAffine`), and descend the result along the
chart `U_k ⟶ X_k` of a later stage.  That needs the two restrictions to the kernel pair
`U_k ×_{X_k} U_k` to agree, which holds at the limit and therefore, by the faithfulness clause
for the system of base changes of that kernel pair
(`AlgebraicGeometry.Space.eventually_map_eq_of_baseChange`), at a later stage.  The kernel pair is
quasi-compact because the stages are quasi-separated.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_FinitePresentationModuleFullness
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_FinitePresentationModuleFullness
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hL : HasSiteLimit B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- The kernel pair of a morphism into a quasi-separated algebraic space from a quasi-compact
one is quasi-compact. -/
theorem isQuasiCompactSpace_pullback_self {U X : AlgebraicSpaces B S hS} (g : U ⟶ X)
    (hU : IsQuasiCompactSpace B S hS U.1) (hX : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    IsQuasiCompactSpace B S hS (pullback g.hom g.hom) := by
  have hg := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hX hU g.hom
  exact isQuasiCompactSpace_source_of_isQuasiCompact B S hS U.2 hU
    (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g.hom g.hom).flip hg)

/-- A surjective étale morphism of algebraic spaces with representable source is an étale
covering. -/
theorem isEtaleCovering_of_surjective_etale {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (hg : IsEtale B S hS g.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g.hom) :
    IsEtaleCovering B S hS (fun _ : Unit => Q.1) (fun _ => g.hom) where
  target_isAlgebraicSpace := P.2
  source_isAlgebraicSpace := fun _ => Q.2
  etale := fun _ => hg
  jointly_surjective := by
    refine Set.eq_univ_iff_forall.2 fun x => Set.mem_iUnion.2 ⟨(), ?_⟩
    exact isSurjective_of_presheafSurjective B S hS g.hom hs x

/-- **The fullness clause for a system of affine schemes over a base.**  For a cofiltered
system of affine schemes of the site with compatible morphisms `w k` to an algebraic space `Z`
and finitely presented `𝒪_Z`-modules `M`, `N`, every morphism between the inverse images to the
limit is, at a later stage, the restriction of a morphism between the inverse images there. -/
theorem exists_homRestrict_eq_of_isAffine_base {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ BigFppfOver B S hS) (c : Cone E)
    (hE : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j)))
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) {Z : AlgebraicSpaces B S hS}
    (w : ∀ k, schemeSpace (E.obj k) ⟶ Z)
    (hw : ∀ {k k' : J} (e : k ⟶ k'), schemeSpaceMap (E.map e) ≫ w k' = w k) (b : J)
    {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (v : schemeSpace c.pt ⟶ Z) (hv : schemeSpaceMap (coneLeg B S hS E c b) ≫ w b = v)
    (χ : (modulePullback B S hS v).obj M ⟶ (modulePullback B S hS v).obj N) :
    ∃ (l : J) (e : l ⟶ b) (ψ : (modulePullback B S hS (w l)).obj M ⟶
        (modulePullback B S hS (w l)).obj N),
      moduleHomRestrict M N (schemeSpaceMap (coneLeg B S hS E c l)) (w l) v
        (by rw [← hv, ← hw e, ← Category.assoc, schemeSpaceMap_π_comp]) ψ = χ := by
  subst hv
  obtain ⟨l, e, ψ', hψ'⟩ := exists_homRestrict_eq_of_isAffine B S hS E c hE hc b
    ((modulePullback B S hS (w b)).obj M) ((modulePullback B S hS (w b)).obj N)
    (isFinitePresentationOnSite_modulePullback B S hS _ M hM)
    (isFinitePresentationOnSite_modulePullback B S hS _ N hN)
    (homConjInv (w b) (schemeSpaceMap (coneLeg B S hS E c b)) χ)
  obtain ⟨ψ, hψ⟩ := exists_homRestrict_eq_of_homRestrict_eq_homConjInv (w b)
    (schemeSpaceMap (E.map e)) (schemeSpaceMap (coneLeg B S hS E c l))
    (schemeSpaceMap (coneLeg B S hS E c b)) (schemeSpaceMap_π_comp B S hS E c e) (w l) (hw e) ψ'
    χ hψ'
  exact ⟨l, e, ψ, hψ⟩

section ChartFacts

variable {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

omit [IsCofiltered I] hL in
/-- **The chart of a stage is an étale covering of the stage**: it is a base change of the chart
`f₀`, which is étale and surjective. -/
theorem isEtaleCovering_chartStageMap (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hf₀ : IsEtale B S hS f₀)
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀) (j : Over i₀) :
    IsEtaleCovering B S hS (fun _ : Unit => (schemeSpace (C.siteDiagram.obj j)).1)
      (fun _ => (chartStageMap B S hS D hD U₀ f₀ C j).hom) :=
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  isEtaleCovering_of_surjective_etale B S hS _
    (isEtale_of_isPullback_yoneda B S hS (C.isPullback j).flip hf₀)
    (MorphismProperty.of_isPullback (C.isPullback j).flip hs₀)

end ChartFacts

section Chart

variable {i : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i}
  (C : AffineChartSystem B S hS i D U₀ f₀) (L : AffineChartSystem.LimitBridge C)

/-- The composite of the chart of a stage with the transition morphism to `X_i`. -/
noncomputable abbrev chartStageToBase (k : Over i) :
    schemeSpace (C.siteDiagram.obj k) ⟶ stageAlgebraicSpace B S hS D hD i :=
  chartStageMap B S hS D hD U₀ f₀ C k ≫ stageTransition B S hS D hD k.hom

omit [IsCofiltered I] in
/-- The charts of the stages commute with the transition morphisms of the chart system and of
`D`. -/
theorem chartStageMap_naturality {k k' : Over i} (e : k ⟶ k') :
    schemeSpaceMap (C.siteDiagram.map e) ≫ chartStageMap B S hS D hD U₀ f₀ C k' =
      chartStageMap B S hS D hD U₀ f₀ C k ≫ stageTransition B S hS D hD e.left := by
  apply ObjectProperty.hom_ext
  have hnat : yoneda.map (C.siteDiagram.map e) ≫ C.iso.hom.app k' =
      C.iso.hom.app k ≫ (stageBaseChangeDiagram B S hS i D U₀ f₀).map e :=
    C.iso.hom.naturality e
  change yoneda.map (C.siteDiagram.map e) ≫ C.iso.hom.app k' ≫
      stageBaseChangeFst B S hS i D U₀ f₀ k' =
    (C.iso.hom.app k ≫ stageBaseChangeFst B S hS i D U₀ f₀ k) ≫ D.map e.left
  rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_fst,
    Category.assoc]

omit [IsCofiltered I] in
/-- The transition morphisms between the stages compose: `X_a ⟶ X_b ⟶ X_c` is `X_a ⟶ X_c`. -/
theorem stageTransition_comp {a b c : I} (e : a ⟶ b) (e' : b ⟶ c) :
    stageTransition B S hS D hD e ≫ stageTransition B S hS D hD e' =
      stageTransition B S hS D hD (e ≫ e') :=
  ObjectProperty.hom_ext _ (D.map_comp e e').symm

omit [IsCofiltered I] in
/-- The morphisms `chartStageToBase` from the charts of the stages to `X_i` commute with the
transition morphisms of the chart system. -/
theorem chartStageToBase_naturality {k k' : Over i} (e : k ⟶ k') :
    schemeSpaceMap (C.siteDiagram.map e) ≫ chartStageToBase B S hS D hD C k' =
      chartStageToBase B S hS D hD C k := by
  rw [chartStageToBase, chartStageToBase, ← Category.assoc, chartStageMap_naturality,
    Category.assoc, stageTransition_comp, Over.w e]

/-- The chart of the limit, as a morphism of algebraic spaces into the limit. -/
noncomputable def chartLimitMap :
    schemeSpace L.cone.pt ⟶ limitSpace B S hS D hL :=
  ObjectProperty.homMk L.toLimit

omit [IsCofiltered I] in
/-- The chart of the limit followed by the projection to `X_k` is the projection of the limit
chart to the chart of the stage `k`, followed by that chart. -/
theorem chartLimitMap_comp (k : Over i) :
    chartLimitMap B S hS D hL C L ≫
        limitSpaceProjection B S hS D hL hD k.left =
      schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone k) ≫
        chartStageMap B S hS D hD U₀ f₀ C k :=
  ObjectProperty.hom_ext _ (L.toLimit_comp_limitπ k)

omit [IsCofiltered I] in
/-- The chart of the limit followed by the projection to `X_i` is the projection of the limit
chart to the chart of the stage `k`, followed by `chartStageToBase`. -/
theorem chartLimitMap_comp_base (k : Over i) :
    chartLimitMap B S hS D hL C L ≫
        limitSpaceProjection B S hS D hL hD i =
      schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone k) ≫
        chartStageToBase B S hS D hD C k := by
  rw [chartStageToBase, ← Category.assoc, ← chartLimitMap_comp, Category.assoc,
    limitSpaceProjection_comp]

omit [IsCofiltered I] in
variable {C} in
/-- The chart of the limit is étale. -/
theorem isEtale_chartLimitMap (hf₀ : IsEtale B S hS f₀) :
    IsEtale B S hS (chartLimitMap B S hS D hL C L).hom :=
  isEtale_of_isPullback_yoneda B S hS L.isPullback.flip hf₀

omit [IsCofiltered I] in
variable {C} in
/-- The chart of the limit is surjective. -/
theorem surjective_chartLimitMap
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (chartLimitMap B S hS D hL C L).hom :=
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  MorphismProperty.of_isPullback L.isPullback.flip hs₀

end Chart

section KernelPair

variable {i : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i}
  (C : AffineChartSystem B S hS i D U₀ f₀) (l : Over i)

/-- The kernel pair `U_l ×_{X_l} U_l` of the chart of a stage. -/
noncomputable abbrev stageChartPair : AlgebraicSpaces B S hS :=
  ⟨pullback (chartStageMap B S hS D hD U₀ f₀ C l).hom (chartStageMap B S hS D hD U₀ f₀ C l).hom,
    isAlgebraicSpace_pullback B S hS _ _ (schemeSpace (C.siteDiagram.obj l)).2
      (schemeSpace (C.siteDiagram.obj l)).2 (hD l.left)⟩

/-- The first projection of the kernel pair. -/
noncomputable def stageChartPairFst :
    stageChartPair B S hS D hD C l ⟶ schemeSpace (C.siteDiagram.obj l) :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The second projection of the kernel pair. -/
noncomputable def stageChartPairSnd :
    stageChartPair B S hS D hD C l ⟶ schemeSpace (C.siteDiagram.obj l) :=
  ObjectProperty.homMk (pullback.snd _ _)

omit [IsCofiltered I] in
/-- The two projections of the kernel pair have equal composites with the chart of the stage. -/
theorem chartPair_condition :
    stageChartPairFst B S hS D hD C l ≫ chartStageMap B S hS D hD U₀ f₀ C l =
      stageChartPairSnd B S hS D hD C l ≫ chartStageMap B S hS D hD U₀ f₀ C l :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The kernel pair maps to the stage. -/
noncomputable def chartPairToStage :
    stageChartPair B S hS D hD C l ⟶ stageAlgebraicSpace B S hS D hD l.left :=
  stageChartPairFst B S hS D hD C l ≫ chartStageMap B S hS D hD U₀ f₀ C l

/-- The stage `j' = Over.mk (j.hom ≫ l.hom)` of the chart system attached to a stage `j` above
`l.left`. -/
abbrev overStageComp (j : Over l.left) : Over i := Over.mk (j.hom ≫ l.hom)

/-- The morphism `j' ⟶ l` of the chart system. -/
def overCompHom (j : Over l.left) : overStageComp l j ⟶ l := Over.homMk j.hom

variable (pr : stageChartPair B S hS D hD C l ⟶ schemeSpace (C.siteDiagram.obj l))
  (hpr : pr ≫ chartStageMap B S hS D hD U₀ f₀ C l = chartPairToStage B S hS D hD C l)

include hpr in
omit [IsCofiltered I] in
/-- On underlying morphisms of presheaves, `pr` followed by the chart of the stage `l` is the
morphism `chartPairToStage` of the kernel pair to the stage. -/
theorem pr_comp_stageMap :
    pr.hom ≫ C.stageMap l = (chartPairToStage B S hS D hD C l).hom :=
  congrArg (fun t => t.hom) hpr

/-- The projection of the base change `X_j ×_{X_l} (U_l ×_{X_l} U_l)` to the chart of `j'`
induced by a projection `pr` of the kernel pair. -/
noncomputable def pairStageProj (j : Over l.left) :
    stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D l.left
        (chartPairToStage B S hS D hD C l).hom)
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l)) j ⟶
      schemeSpace (C.siteDiagram.obj (overStageComp l j)) :=
  ObjectProperty.homMk ((C.isPullback (overStageComp l j)).lift
    (pullback.fst (D.map j.hom) (chartPairToStage B S hS D hD C l).hom)
    (pullback.snd (D.map j.hom) (chartPairToStage B S hS D hD C l).hom ≫ pr.hom ≫ C.baseMap l)
    (by
      have h1 := pullback.condition (f := D.map j.hom) (g := (chartPairToStage B S hS D hD C l).hom)
      have h2 := (C.isPullback l).w
      have h3 := pr_comp_stageMap B S hS D hD C l pr hpr
      change _ ≫ D.map (j.hom ≫ l.hom) = _
      rw [D.map_comp]
      calc _ = (pullback.fst (D.map j.hom) (chartPairToStage B S hS D hD C l).hom ≫ D.map j.hom) ≫
            D.map l.hom := (Category.assoc _ _ _).symm
        _ = (pullback.snd (D.map j.hom) (chartPairToStage B S hS D hD C l).hom ≫
            (chartPairToStage B S hS D hD C l).hom) ≫ D.map l.hom := by rw [h1]; try rfl
        _ = pullback.snd (D.map j.hom) (chartPairToStage B S hS D hD C l).hom ≫ pr.hom ≫
            (C.stageMap l ≫ D.map l.hom) := by
              rw [← h3]; simp only; try rfl
        _ = pullback.snd (D.map j.hom) (chartPairToStage B S hS D hD C l).hom ≫ pr.hom ≫
            (C.baseMap l ≫ f₀) :=
              congrArg (fun t => pullback.snd (D.map j.hom)
                (chartPairToStage B S hS D hD C l).hom ≫ pr.hom ≫ t) h2
        _ = _ := by simp only; try rfl))

include hpr in
omit [IsCofiltered I] in
/-- The projection `pairStageProj`, followed by the chart of `j'`, is the first projection of the
base change `X_j ×_{X_l} (U_l ×_{X_l} U_l)`. -/
theorem pairStageProj_comp_stageMap (j : Over l.left) :
    (pairStageProj B S hS D hD C l pr hpr j).hom ≫ C.stageMap (overStageComp l j) =
      pullback.fst (D.map j.hom) (chartPairToStage B S hS D hD C l).hom :=
  (C.isPullback (overStageComp l j)).lift_fst _ _ _

include hpr in
omit [IsCofiltered I] in
/-- The projection `pairStageProj`, followed by the morphism of the chart of `j'` to `U₀`, is the
second projection of the base change followed by `pr` and the morphism of the chart of `l` to
`U₀`. -/
theorem pairStageProj_comp_baseMap (j : Over l.left) :
    (pairStageProj B S hS D hD C l pr hpr j).hom ≫ C.baseMap (overStageComp l j) =
      pullback.snd (D.map j.hom) (chartPairToStage B S hS D hD C l).hom ≫ pr.hom ≫ C.baseMap l :=
  (C.isPullback (overStageComp l j)).lift_snd _ _ _

omit [IsCofiltered I] in
/-- In a category, given a pullback square `smL`, `bmL`, `Dl`, `f₀` and a morphism `v` into `Uj`
whose composites with `smJ` and `bmJ` are `fst` and `snd ≫ pr ≫ bmL`, the composite `v ≫ u` is
`snd ≫ pr`. -/
theorem pullback_comp_eq_aux {C' : Type*} [Category C'] {P A Uj Ul Xj Xl Xi V : C'}
    (fst : P ⟶ Xj) (snd : P ⟶ A) (Dj : Xj ⟶ Xl) (ρ : A ⟶ Xl) (hP : fst ≫ Dj = snd ≫ ρ)
    (pr : A ⟶ Ul) (smL : Ul ⟶ Xl) (bmL : Ul ⟶ V) (Dl : Xl ⟶ Xi) (f₀ : V ⟶ Xi)
    (hL : IsPullback smL bmL Dl f₀) (hpr : pr ≫ smL = ρ) (smJ : Uj ⟶ Xj) (bmJ : Uj ⟶ V)
    (u : Uj ⟶ Ul) (n1 : u ≫ smL = smJ ≫ Dj) (n2 : u ≫ bmL = bmJ) (v : P ⟶ Uj)
    (hv1 : v ≫ smJ = fst) (hv2 : v ≫ bmJ = snd ≫ pr ≫ bmL) : v ≫ u = snd ≫ pr := by
  apply hL.hom_ext
  · rw [Category.assoc, n1, ← Category.assoc, hv1, hP, Category.assoc, hpr]
  · rw [Category.assoc, n2, hv2, Category.assoc]

include hpr in
omit [IsCofiltered I] in
/-- The projection of the base change, followed by the chart transition to `l`, is the
projection of the kernel pair. -/
theorem pairStageProj_comp_transition (j : Over l.left) :
    pairStageProj B S hS D hD C l pr hpr j ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom l j)) =
      stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) j ≫ pr :=
  ObjectProperty.hom_ext _ (pullback_comp_eq_aux _ _ (D.map j.hom)
    (chartPairToStage B S hS D hD C l).hom pullback.condition pr.hom (C.stageMap l)
    (C.baseMap l) (D.map l.hom) f₀ (C.isPullback l) (pr_comp_stageMap B S hS D hD C l pr hpr)
    (C.stageMap (overStageComp l j)) (C.baseMap (overStageComp l j))
    (yoneda.map (C.siteDiagram.map (overCompHom l j)))
    (congrArg (fun z => z.hom) (chartStageMap_naturality B S hS D hD C (overCompHom l j)))
    (AffineChartSystem.baseMap_naturality C (overCompHom l j)) _
    (pairStageProj_comp_stageMap B S hS D hD C l pr hpr j)
    (pairStageProj_comp_baseMap B S hS D hD C l pr hpr j))

omit [IsCofiltered I] in
/-- In a category, if morphisms into `Uj` are determined by their composites with `smJ` and
`bmJ`, then a morphism `v` with `v ≫ fst = a ≫ smJ` and `v ≫ snd ≫ pr = a ≫ u` satisfies
`v ≫ prj = a`. -/
theorem factor_eq_aux {C' : Type*} [Category C'] {T P A Uj Ul Xj V : C'}
    (fst : P ⟶ Xj) (snd : P ⟶ A) (pr : A ⟶ Ul) (smJ : Uj ⟶ Xj) (bmJ : Uj ⟶ V)
    (hJ : ∀ {W : C'} (g h : W ⟶ Uj), g ≫ smJ = h ≫ smJ → g ≫ bmJ = h ≫ bmJ → g = h)
    (bmL : Ul ⟶ V) (u : Uj ⟶ Ul) (n2 : u ≫ bmL = bmJ) (prj : P ⟶ Uj)
    (hp1 : prj ≫ smJ = fst) (hp2 : prj ≫ bmJ = snd ≫ pr ≫ bmL) (a : T ⟶ Uj) (v : T ⟶ P)
    (hv1 : v ≫ fst = a ≫ smJ) (hv2 : v ≫ snd ≫ pr = a ≫ u) : v ≫ prj = a := by
  apply hJ
  · rw [Category.assoc, hp1, hv1]
  · rw [Category.assoc, hp2, ← Category.assoc snd, ← Category.assoc, ← Category.assoc,
      Category.assoc v, hv2, Category.assoc, n2]

omit [IsCofiltered I] in
/-- In a category, if `a ≫ smJ = b ≫ smJ` and `u ≫ smL = smJ ≫ Dj`, then
`(a ≫ u) ≫ smL = (b ≫ u) ≫ smL`. -/
theorem factor_aux₁ {C' : Type*} [Category C'] {T Uj Ul Xj Xl : C'} {a b : T ⟶ Uj}
    (u : Uj ⟶ Ul) (smL : Ul ⟶ Xl) (smJ : Uj ⟶ Xj) (Dj : Xj ⟶ Xl) (n1 : u ≫ smL = smJ ≫ Dj)
    (hab : a ≫ smJ = b ≫ smJ) : (a ≫ u) ≫ smL = (b ≫ u) ≫ smL := by
  rw [Category.assoc, Category.assoc, n1, ← Category.assoc, hab, Category.assoc]

omit [IsCofiltered I] in
/-- In a category, if `inner ≫ fstK = a ≫ u` and `u ≫ smL = smJ ≫ Dj`, then
`(a ≫ smJ) ≫ Dj = inner ≫ fstK ≫ smL`. -/
theorem factor_aux₂ {C' : Type*} [Category C'] {T Uj Ul Xj Xl K : C'} {a : T ⟶ Uj}
    (u : Uj ⟶ Ul) (smL : Ul ⟶ Xl) (smJ : Uj ⟶ Xj) (Dj : Xj ⟶ Xl) (n1 : u ≫ smL = smJ ≫ Dj)
    (inner : T ⟶ K) (fstK : K ⟶ Ul) (h : inner ≫ fstK = a ≫ u) :
    (a ≫ smJ) ≫ Dj = inner ≫ fstK ≫ smL := by
  rw [← Category.assoc inner, h, Category.assoc a u, n1, Category.assoc]

omit [IsCofiltered I] in
/-- In a category, if `v ≫ snd = inner` and `inner ≫ pr = w`, then `v ≫ snd ≫ pr = w`. -/
theorem comp_assoc_aux {C' : Type*} [Category C'] {T P A Ul : C'} (v : T ⟶ P) (snd : P ⟶ A)
    (pr : A ⟶ Ul) (inner : T ⟶ A) {w : T ⟶ Ul} (h1 : v ≫ snd = inner) (h2 : inner ≫ pr = w) :
    v ≫ snd ≫ pr = w := by
  rw [← Category.assoc, h1, h2]

omit [IsCofiltered I] in
/-- **Every pair of morphisms into the chart of `j'` with equal composites to the stage factors
through the base change of the kernel pair.** -/
theorem exists_factor_pairStageProj (j : Over l.left) (T : AlgebraicSpaces B S hS)
    (a b : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp l j)))
    (hab : a ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j) =
      b ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j)) :
    ∃ v, v ≫ pairStageProj B S hS D hD C l (stageChartPairFst B S hS D hD C l) rfl j = a ∧
      v ≫ pairStageProj B S hS D hD C l (stageChartPairSnd B S hS D hD C l)
        (by rw [← chartPair_condition]; rfl) j = b := by
  let u := yoneda.map (C.siteDiagram.map (overCompHom l j))
  have hab' : a.hom ≫ C.stageMap (overStageComp l j) = b.hom ≫ C.stageMap (overStageComp l j) :=
    congrArg (fun t => t.hom) hab
  have n1 : yoneda.map (C.siteDiagram.map (overCompHom l j)) ≫ C.stageMap l =
      C.stageMap (overStageComp l j) ≫ D.map j.hom :=
    congrArg (fun z => z.hom) (chartStageMap_naturality B S hS D hD C (overCompHom l j))
  have hin : (a.hom ≫ u) ≫ C.stageMap l = (b.hom ≫ u) ≫ C.stageMap l :=
    factor_aux₁ u (C.stageMap l) (C.stageMap (overStageComp l j)) (D.map j.hom) n1 hab'
  let inner : T.1 ⟶ (stageChartPair B S hS D hD C l).1 := pullback.lift (a.hom ≫ u) (b.hom ≫ u) hin
  have hout : (a.hom ≫ C.stageMap (overStageComp l j)) ≫ D.map j.hom =
      inner ≫ (chartPairToStage B S hS D hD C l).hom :=
    factor_aux₂ u (C.stageMap l) (C.stageMap (overStageComp l j)) (D.map j.hom) n1 inner
      (pullback.fst _ _) (pullback.lift_fst _ _ _)
  let v : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D l.left
        (chartPairToStage B S hS D hD C l).hom)
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l)) j :=
    ObjectProperty.homMk (pullback.lift (a.hom ≫ C.stageMap (overStageComp l j)) inner hout)
  have hJ : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g h : W ⟶ (C.siteDiagram ⋙ yoneda).obj
      (overStageComp l j)),
      g ≫ C.stageMap (overStageComp l j) = h ≫ C.stageMap (overStageComp l j) →
      g ≫ C.baseMap (overStageComp l j) = h ≫ C.baseMap (overStageComp l j) → g = h :=
    fun g h h1 h2 => (C.isPullback (overStageComp l j)).hom_ext h1 h2
  have n2 := AffineChartSystem.baseMap_naturality C (overCompHom l j)
  refine ⟨v, ObjectProperty.hom_ext _ ?_, ObjectProperty.hom_ext _ ?_⟩ <;>
    refine factor_eq_aux _ _ _ _ _ hJ (C.baseMap l) u n2 _
      (pairStageProj_comp_stageMap B S hS D hD C l _ _ j)
      (pairStageProj_comp_baseMap B S hS D hD C l _ _ j) _ v.hom ?_
      (comp_assoc_aux v.hom _ _ inner (pullback.lift_snd _ _ _) ?_)
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_fst _ _ _).trans hab'
  · exact pullback.lift_snd _ _ _

variable (L : AffineChartSystem.LimitBridge C)

include hpr in
omit [IsCofiltered I] in
/-- **The base change of the kernel pair to the limit factors through the chart of the limit.** -/
theorem exists_limit_factor :
    ∃ μ : limitBaseChangeSpace B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) ⟶ schemeSpace L.cone.pt,
      μ ≫ chartLimitMap B S hS D hL C L =
          limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l) ∧
        μ ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) =
          limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l) ≫ pr := by
  have h1 := congrArg (fun t => t.hom) (limitBaseChangeFst_comp B S hS D hL hD
    (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l))
  have h2 := pr_comp_stageMap B S hS D hD C l pr hpr
  have eq : (limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l)).hom ≫ limit.π D l.left =
      ((limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l)).hom ≫ pr.hom) ≫ C.stageMap l :=
    h1.trans ((congrArg (fun t => (limitBaseChangeSnd B S hS D hL hD
      (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l)).hom ≫ t) h2).symm.trans
        (Category.assoc _ _ _).symm)
  exact ⟨ObjectProperty.homMk ((L.isPullback_stage l).lift _ _ eq),
    ObjectProperty.hom_ext _ ((L.isPullback_stage l).lift_fst _ _ _),
    ObjectProperty.hom_ext _ ((L.isPullback_stage l).lift_snd _ _ _)⟩

omit [IsCofiltered I] in
/-- In a category, if `P ≫ u = s ≫ pr`, `u ≫ (cm ≫ t) = cj` and `pr ≫ cm = r`, then
`P ≫ cj = (s ≫ r) ≫ t`. -/
theorem comp_eq_aux₃ {C' : Type*} [Category C'] {R Uj Ul A Xl Xi : C'} (P : R ⟶ Uj)
    (u : Uj ⟶ Ul) (s : R ⟶ A) (pr : A ⟶ Ul) (cm : Ul ⟶ Xl) (t : Xl ⟶ Xi) (cj : Uj ⟶ Xi)
    (r : A ⟶ Xl) (h1 : P ≫ u = s ≫ pr) (h2 : u ≫ (cm ≫ t) = cj) (hpr : pr ≫ cm = r) :
    P ≫ cj = (s ≫ r) ≫ t := by
  rw [← h2, ← Category.assoc, h1, ← hpr]
  simp only [Category.assoc]

omit [IsCofiltered I] in
/-- The two projections of the base change of the kernel pair to the chart of `j'`, read on a
morphism over the chart of `l`. -/
theorem moduleHomRestrict_pairStageProj_eq {M N : Modules.{u, u} B S hS
      (stageAlgebraicSpace B S hS D hD i).1 (stageAlgebraicSpace B S hS D hD i).2}
    (j : Over l.left)
    (ψ : (modulePullback B S hS (chartStageToBase B S hS D hD C l)).obj M ⟶
      (modulePullback B S hS (chartStageToBase B S hS D hD C l)).obj N) :
    moduleHomRestrict M N (pairStageProj B S hS D hD C l pr hpr j)
        (chartStageToBase B S hS D hD C (overStageComp l j))
        ((stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) j ≫ chartPairToStage B S hS D hD C l) ≫
          stageTransition B S hS D hD l.hom)
        (comp_eq_aux₃ _ _ _ pr _ _ _ _ (pairStageProj_comp_transition B S hS D hD C l pr hpr j)
          (chartStageToBase_naturality B S hS D hD C (overCompHom l j)) hpr)
        (moduleHomRestrict M N (schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
          (chartStageToBase B S hS D hD C l) (chartStageToBase B S hS D hD C (overStageComp l j))
          (chartStageToBase_naturality B S hS D hD C (overCompHom l j)) ψ) =
      homConj (stageTransition B S hS D hD l.hom)
        (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) j ≫ chartPairToStage B S hS D hD C l)
        (moduleHomRestrict _ _ (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l) j)
          (chartPairToStage B S hS D hD C l) _ rfl
          (moduleHomRestrict _ _ pr (chartStageMap B S hS D hD U₀ f₀ C l)
            (chartPairToStage B S hS D hD C l) hpr
            (homConjInv (stageTransition B S hS D hD l.hom)
              (chartStageMap B S hS D hD U₀ f₀ C l) ψ))) := by
  rw [moduleHomRestrict_homRestrict' _ _ _ (pairStageProj_comp_transition B S hS D hD C l pr hpr j),
    moduleHomRestrict_homRestrict' _ _ _ rfl, homConj_homRestrict', homConj_homConjInv]

omit [IsCofiltered I] in
/-- **The descent condition at the stage `j'`**, from the agreement of the two restrictions to the
base change of the kernel pair. -/
theorem descent_condition_of_pair {M N : Modules.{u, u} B S hS
      (stageAlgebraicSpace B S hS D hD i).1 (stageAlgebraicSpace B S hS D hD i).2}
    (j : Over l.left)
    (ψ : (modulePullback B S hS (chartStageToBase B S hS D hD C l)).obj M ⟶
      (modulePullback B S hS (chartStageToBase B S hS D hD C l)).obj N)
    (hE : moduleHomRestrict _ _
          (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l) j)
          (chartPairToStage B S hS D hD C l) _ rfl
          (moduleHomRestrict _ _ (stageChartPairFst B S hS D hD C l)
            (chartStageMap B S hS D hD U₀ f₀ C l)
            (chartPairToStage B S hS D hD C l) rfl
            (homConjInv (stageTransition B S hS D hD l.hom)
              (chartStageMap B S hS D hD U₀ f₀ C l) ψ)) =
        moduleHomRestrict _ _ (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l) j)
          (chartPairToStage B S hS D hD C l) _ rfl
          (moduleHomRestrict _ _ (stageChartPairSnd B S hS D hD C l)
            (chartStageMap B S hS D hD U₀ f₀ C l)
            (chartPairToStage B S hS D hD C l) (chartPair_condition B S hS D hD C l).symm
            (homConjInv (stageTransition B S hS D hD l.hom)
              (chartStageMap B S hS D hD U₀ f₀ C l) ψ)))
    (T : AlgebraicSpaces B S hS) (a b : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp l j)))
    (hab : a ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j) =
      b ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j)) :
    moduleHomRestrict M N a (chartStageToBase B S hS D hD C (overStageComp l j))
        ((a ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j)) ≫
          stageTransition B S hS D hD (overStageComp l j).hom) (Category.assoc _ _ _).symm
        (moduleHomRestrict M N (schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
          (chartStageToBase B S hS D hD C l) (chartStageToBase B S hS D hD C (overStageComp l j))
          (chartStageToBase_naturality B S hS D hD C (overCompHom l j)) ψ) =
      moduleHomRestrict M N b (chartStageToBase B S hS D hD C (overStageComp l j))
        ((a ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j)) ≫
          stageTransition B S hS D hD (overStageComp l j).hom)
        (by rw [← Category.assoc, hab])
        (moduleHomRestrict M N (schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
          (chartStageToBase B S hS D hD C l) (chartStageToBase B S hS D hD C (overStageComp l j))
          (chartStageToBase_naturality B S hS D hD C (overCompHom l j)) ψ) := by
  obtain ⟨v, hv₁, hv₂⟩ := exists_factor_pairStageProj B S hS D hD C l j T a b hab
  have key := fun pr hpr => comp_eq_aux₃ _ _ _ pr _ _ _ _
    (pairStageProj_comp_transition B S hS D hD C l pr hpr j)
    (chartStageToBase_naturality B S hS D hD C (overCompHom l j)) hpr
  refine moduleHomRestrict_eq_of_factor _ _ _ _
    ((stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l) j ≫ chartPairToStage B S hS D hD C l) ≫
      stageTransition B S hS D hD l.hom)
    (key _ rfl) (key _ (chartPair_condition B S hS D hD C l).symm) ?_ v a b hv₁ hv₂ _ _ _
  exact (moduleHomRestrict_pairStageProj_eq B S hS D hD C l _ rfl j ψ).trans
    ((congrArg _ hE).trans (moduleHomRestrict_pairStageProj_eq B S hS D hD C l _
      (chartPair_condition B S hS D hD C l).symm j ψ).symm)

omit [IsCofiltered I] in
/-- In a category, if `pr ≫ cm = r`, then `(lbs ≫ pr) ≫ cm ≫ t = (lbs ≫ r) ≫ t`. -/
theorem comp_eq_aux₄ {C' : Type*} [Category C'] {T R U X Y : C'} (lbs : T ⟶ R) (r : R ⟶ X)
    (t : X ⟶ Y) (pr : R ⟶ U) (cm : U ⟶ X) (hpr : pr ≫ cm = r) :
    (lbs ≫ pr) ≫ cm ≫ t = (lbs ≫ r) ≫ t := by
  rw [← hpr]; simp only [Category.assoc]

omit [IsCofiltered I] in
/-- One side of the agreement at the limit: the restriction to the base change of the kernel pair
of a projection of a descended morphism is the restriction of the given morphism on the limit. -/
theorem homConj_limit_side {M N : Modules.{u, u} B S hS
      (stageAlgebraicSpace B S hS D hD i).1 (stageAlgebraicSpace B S hS D hD i).2}
    (φ : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj M ⟶
      (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj N)
    (ψ : (modulePullback B S hS (chartStageToBase B S hS D hD C l)).obj M ⟶
      (modulePullback B S hS (chartStageToBase B S hS D hD C l)).obj N)
    (hψ : moduleHomRestrict M N (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l))
      (chartStageToBase B S hS D hD C l)
      (chartLimitMap B S hS D hL C L ≫
        limitSpaceProjection B S hS D hL hD i)
      (chartLimitMap_comp_base B S hS D hL hD C L l).symm ψ =
      moduleHomRestrict M N (chartLimitMap B S hS D hL C L)
        (limitSpaceProjection B S hS D hL hD i) _ rfl φ) :
    homConj (stageTransition B S hS D hD l.hom)
        (limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ chartPairToStage B S hS D hD C l)
        (moduleHomRestrict _ _ (limitBaseChangeSnd B S hS D hL hD
            (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l))
          (chartPairToStage B S hS D hD C l) _ rfl
          (moduleHomRestrict _ _ pr (chartStageMap B S hS D hD U₀ f₀ C l)
            (chartPairToStage B S hS D hD C l) hpr
            (homConjInv (stageTransition B S hS D hD l.hom)
              (chartStageMap B S hS D hD U₀ f₀ C l) ψ))) =
      moduleHomRestrict M N (limitBaseChangeFst B S hS D hL hD
          (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l))
        (limitSpaceProjection B S hS D hL hD i) _
        (by rw [← limitSpaceProjection_comp B S hS D hL hD l.hom, ← Category.assoc,
          limitBaseChangeFst_comp, Category.assoc]) φ := by
  obtain ⟨μ, hμ₁, hμ₂⟩ := exists_limit_factor B S hS D hL hD C l pr hpr L
  rw [homConj_homRestrict', homConj_homRestrict', homConj_homConjInv,
    moduleHomRestrict_homRestrict' _ _ _ rfl]
  exact moduleHomRestrict_eq_of_factor_through _ φ _ _ rfl _ _ _ ψ hψ μ _ hμ₂ _ hμ₁ _
    (comp_eq_aux₄ _ _ _ _ _ hpr) _

end KernelPair

/-! ### The fullness clause -/

/-- **Stacks 07V7, the fullness clause, through restriction.**  For a cofiltered system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms and two
finitely presented `𝒪_{X_i}`-modules `M`, `N` on a stage, every morphism `φ` between their inverse
images to the limit is, at a later stage `j`, the restriction along the projection `X ⟶ X_j` of a
morphism `ψ` between their inverse images to `X_j`. -/
theorem exists_homRestrict_eq_limitProjection
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) (i : I)
    {M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2}
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj M ⟶
      (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj N) :
    ∃ (j : I) (e : j ⟶ i) (ψ : (modulePullback B S hS (stageTransition B S hS D hD e)).obj M ⟶
        (modulePullback B S hS (stageTransition B S hS D hD e)).obj N),
      moduleHomRestrict M N (limitSpaceProjection B S hS D hL hD j)
        (stageTransition B S hS D hD e) (limitSpaceProjection B S hS D hL hD i)
        (limitSpaceProjection_comp B S hS D hL hD e) ψ = φ := by
  classical
  obtain ⟨V₀, f₀, hV₀, hs₀, hf₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i) (hD i)).mp
      (hQc i)
  let C := affineChartSystem B S hS i D ⟨V₀, hV₀⟩ f₀ hL.1
  let L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hL.2.2)
  let ell := chartLimitMap B S hS D hL C L
  let p := limitSpaceProjection B S hS D hL hD i
  obtain ⟨l, e, ψ, hψ⟩ := exists_homRestrict_eq_of_isAffine_base B S hS C.siteDiagram L.cone
    C.isAffine_obj L.schemeIsLimit (fun k => chartStageToBase B S hS D hD C k)
    (fun e => chartStageToBase_naturality B S hS D hD C e) (Over.mk (𝟙 i)) hM hN (ell ≫ p)
    (chartLimitMap_comp_base B S hS D hL hD C L _).symm
    (moduleHomRestrict M N ell p (ell ≫ p) rfl φ)
  let t := stageTransition B S hS D hD l.hom
  have hUqc : IsQuasiCompactSpace B S hS (schemeSpace (C.siteDiagram.obj l)).1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (C.isAffine_obj l)
  have hRqc := isQuasiCompactSpace_pullback_self B S hS hZ
    (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C l) hUqc (hQs l.left)
  let x₁ := moduleHomRestrict ((modulePullback B S hS t).obj M) ((modulePullback B S hS t).obj N)
    (stageChartPairFst B S hS D hD C l) (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C l)
    (chartPairToStage B S hS D hD C l) rfl
    (homConjInv t (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C l) ψ)
  let x₂ := moduleHomRestrict ((modulePullback B S hS t).obj M) ((modulePullback B S hS t).obj N)
    (stageChartPairSnd B S hS D hD C l) (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C l)
    (chartPairToStage B S hS D hD C l) (chartPair_condition B S hS D hD C l).symm
    (homConjInv t (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C l) ψ)
  have hlim : (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD
      (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l))).map x₁ =
      (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD
        (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l))).map x₂ := by
    rw [← moduleHomRestrict_eq_iff _ _ _ rfl]
    apply homConj_injective t
    rw [homConj_limit_side B S hS D hL hD C l _ rfl L φ ψ hψ,
      homConj_limit_side B S hS D hL hD C l _
        (chartPair_condition B S hS D hD C l).symm L φ ψ hψ]
  obtain ⟨j, hj⟩ := eventually_map_eq_of_baseChange B S hS D hL hD
    (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l) hRqc
    (isFinitePresentationOnSite_modulePullback B S hS t M hM)
    (isFinitePresentationOnSite_modulePullback B S hS t N hN) x₁ x₂ hlim
  have hE := (moduleHomRestrict_eq_iff _ _ _ rfl x₁ x₂).2 hj
  let j' := overStageComp l j
  have hcov := isEtaleCovering_chartStageMap B S hS D hD C hf₀ hs₀ j'
  have hg := hcov.etale ()
  have hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS (hD j'.left) (C.stageMap j')
  obtain ⟨χ, hχ⟩ := exists_homRestrict_eq_of_descent B S hS
    (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C j') hg hrep hcov
    (stageTransition B S hS D hD j'.hom) _
    (fun T a b hab => descent_condition_of_pair B S hS D hD C l j ψ hE T a b hab)
  refine ⟨j'.left, j'.hom, χ, ?_⟩
  have := faithful_modulePullback B S hS L.cone.pt ell
    (isEtale_chartLimitMap B S hS D hL L hf₀)
    (surjective_chartLimitMap B S hS D hL L hs₀)
  apply moduleHomRestrict_injective ell p (ell ≫ p) rfl
  rw [moduleHomRestrict_homRestrict' _ _ _ (chartLimitMap_comp B S hS D hL hD C L j'),
    ← moduleHomRestrict_homRestrict' (chartStageMap B S hS D hD ⟨V₀, hV₀⟩ f₀ C j')
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone j')) _ rfl _ _ _ rfl
      (chartLimitMap_comp_base B S hS D hL hD C L j').symm, hχ,
    moduleHomRestrict_homRestrict' _ _ _ (schemeSpaceMap_π_comp B S hS C.siteDiagram L.cone
      (overCompHom l j))]
  exact hψ

end AlgebraicGeometry.Space

end
