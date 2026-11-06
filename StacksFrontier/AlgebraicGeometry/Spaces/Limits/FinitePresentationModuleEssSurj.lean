module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleEssSurjCocycle

/-!
# The essential surjectivity clause of Stacks 07V7

Let `D` be a cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces with
affine transition morphisms, and let `X` be its limit.  Every finitely presented `𝒪_X`-module is
the inverse image of a finitely presented `𝒪_{X_k}`-module on some stage.

## Main results

* `AlgebraicGeometry.Space.exists_iso_of_isTwistedTransition`: the descent of a module given on an
  affine étale chart of the limit together with a twisted transition morphism.
* `AlgebraicGeometry.Space.exists_iso_modulePullback_limitProjection`: **essential surjectivity**.

## Implementation notes

The source's proof: restrict the module `P` to an affine étale chart `ell : U ⟶ X` of the limit,
descend it to a chart `U_l` by the affine case, descend the canonical comparison of its two
inverse images to `U ×_X U` to the kernel pair `U_m ×_{X_m} U_m` of a later stage by the fullness
clause for the system of base changes of the kernel pair, and make its cocycle condition and its
diagonal condition hold at a still later stage `n` by the faithfulness clause for the systems of
base changes of the triple product and of the chart.  The resulting descent datum relative to
`U_n ⟶ X_n` is effective (Stacks 04W6) with a finitely presented descended module `Q`, and the
identification of `ell^*P` with `ell^*(p_n^*Q)` satisfies the descent condition along `ell`
because both have the same twisted comparisons, so it descends to an isomorphism
`P ≅ p_n^*Q`.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hL : HasSiteLimit B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
variable {i : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i}
  (C : AffineChartSystem B S hS i D U₀ f₀) (L : AffineChartSystem.LimitBridge C)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FinitePresentationModuleEssSurj :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, found directly. -/
local instance (priority := high) hasPullback_presheaf_FinitePresentationModuleEssSurj
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

omit [IsCofiltered I] in
/-- The kernel pair of the chart of a stage is quasi-compact over it, and its triple product is
quasi-compact. -/
theorem isQuasiCompactSpace_chartTriple (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (m : Over i) : IsQuasiCompactSpace B S hS (chartTriple B S hS D hD C m).1 := by
  have hUqc : IsQuasiCompactSpace B S hS (schemeSpace (C.siteDiagram.obj m)).1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (C.isAffine_obj m)
  have hcm : IsQuasiCompact B S hS (chartStageMap B S hS D hD U₀ f₀ C m).hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (hD m.left) (hQs m.left) hUqc _
  have hR'qc := isQuasiCompactSpace_pullback_self B S hS hZ
    (chartStageMap B S hS D hD U₀ f₀ C m) hUqc (hQs m.left)
  have hpr₂ : IsQuasiCompact B S hS (stageChartPairSnd B S hS D hD C m).hom :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback
      (chartStageMap B S hS D hD U₀ f₀ C m).hom (chartStageMap B S hS D hD U₀ f₀ C m).hom) hcm
  exact isQuasiCompactSpace_source_of_isQuasiCompact B S hS (stageChartPair B S hS D hD C m).2 hR'qc
    (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback
      (stageChartPairSnd B S hS D hD C m).hom (stageChartPairFst B S hS D hD C m).hom) hpr₂)

omit [IsCofiltered I] in
/-- If a chart transition `uu` commutes with the chart maps and the transition along `k`, then for
every `x`, following the chart map at `overStageComp m k` by the transitions along `f.left` and
`j.hom` agrees with following `uu` by the chart map at `m`. -/
theorem stageTransition_stage_eq {m : Over i} {j k : Over m.left} (f : k ⟶ j)
    (uu : schemeSpace (C.siteDiagram.obj (overStageComp m k)) ⟶ schemeSpace (C.siteDiagram.obj m))
    (hnat : uu ≫ chartStageMap B S hS D hD U₀ f₀ C m =
      chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) ≫ stageTransition B S hS D hD k.hom)
    {T : AlgebraicSpaces B S hS} (x : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp m k))) :
    (x ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) ≫
      stageTransition B S hS D hD f.left) ≫
        stageTransition B S hS D hD j.hom = (x ≫ uu) ≫ chartStageMap B S hS D hD U₀ f₀ C m := by
  rw [Category.assoc, Category.assoc, stageTransition_comp, Over.w f, Category.assoc, hnat]

/-- **The descent datum at a stage.**  For a twisted transition morphism `ψ` on the kernel pair of
the chart of a stage `m`, there are a later stage `n` with a chart transition `uu : U_n ⟶ U_m`
over which the pair morphisms satisfy the cocycle condition and the diagonal condition. -/
theorem exists_stage_descentDatum (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (m : Over i) {V : AlgebraicSpaces B S hS} (u : schemeSpace (C.siteDiagram.obj m) ⟶ V)
    (π : schemeSpace L.cone.pt ⟶ V)
    (hπ : schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) ≫ u = π)
    {P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1
      (limitSpace B S hS D hL).2}
    {G : Modules.{u, u} B S hS V.1 V.2} (hG : G.IsFinitePresentationOnSite)
    (η : (modulePullback B S hS (chartLimitMap B S hS D hL C L)).obj P ≅
      (modulePullback B S hS π).obj G)
    (ψ : (modulePullback B S hS (stageChartPairFst B S hS D hD C m ≫ u)).obj G ⟶
      (modulePullback B S hS (stageChartPairSnd B S hS D hD C m ≫ u)).obj G)
    (hψ : IsTwistedTransition (chartLimitMap B S hS D hL C L) π η
      (stageChartPairFst B S hS D hD C m) (stageChartPairSnd B S hS D hD C m)
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) u hπ ψ) :
    ∃ (k : Over m.left)
      (huu : ∀ (T : AlgebraicSpaces B S hS)
          (x y : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp m k))),
        x ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) =
            y ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) →
          (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) ≫
              chartStageMap B S hS D hD U₀ f₀ C m =
            (y ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) ≫
              chartStageMap B S hS D hD U₀ f₀ C m),
      (∀ (T : AlgebraicSpaces B S hS)
          (x y z : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp m k)))
        (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) =
          y ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k))
        (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) =
          z ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k)),
        pairMorphismAt B S hS D hD C m u ψ (overStageComp m k)
            (schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) huu x y hxy ≫
          pairMorphismAt B S hS D hD C m u ψ (overStageComp m k)
            (schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) huu y z hyz =
        pairMorphismAt B S hS D hD C m u ψ (overStageComp m k)
          (schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) huu x z (hxy.trans hyz)) ∧
      (∀ (T : AlgebraicSpaces B S hS) (x : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp m k))),
        pairMorphismAt B S hS D hD C m u ψ (overStageComp m k)
          (schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) huu x x rfl = 𝟙 _) := by
  have hUqc : IsQuasiCompactSpace B S hS (schemeSpace (C.siteDiagram.obj m)).1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (C.isAffine_obj m)
  obtain ⟨j₁, hj₁⟩ := exists_stage_cocycle B S hS D hL hD C L m u π hπ η ψ hψ hG
    (isQuasiCompactSpace_chartTriple B S hS hZ D hD C hQs m) (tripleToStage B S hS D hD C m)
    _ _ _ (triple_π₁_stage B S hS D hD C m) (triple_π₂_stage B S hS D hD C m)
    (triple_π₃_stage B S hS D hD C m)
  obtain ⟨j₂, hj₂⟩ := exists_stage_diag B S hS D hL hD C L m u π hπ η ψ hψ hG
    hUqc (chartStageMap B S hS D hD U₀ f₀ C m) (𝟙 _) (Category.id_comp _)
  obtain ⟨k, ⟨f₁⟩, ⟨f₂⟩⟩ : ∃ k : Over m.left, Nonempty (k ⟶ j₁) ∧ Nonempty (k ⟶ j₂) :=
    ⟨_, ⟨IsCofiltered.minToLeft j₁ j₂⟩, ⟨IsCofiltered.minToRight j₁ j₂⟩⟩
  have hnat : schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫
      chartStageMap B S hS D hD U₀ f₀ C m =
      chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) ≫ stageTransition B S hS D hD k.hom :=
    chartStageMap_naturality B S hS D hD C (overCompHom m k)
  have huu : ∀ (T : AlgebraicSpaces B S hS)
        (x y : T ⟶ schemeSpace (C.siteDiagram.obj (overStageComp m k))),
      x ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) =
          y ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) →
        (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) ≫
            chartStageMap B S hS D hD U₀ f₀ C m =
          (y ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) ≫
            chartStageMap B S hS D hD U₀ f₀ C m := fun T x y h => by
    rw [Category.assoc, hnat, ← Category.assoc, h, Category.assoc, ← hnat, Category.assoc]
  refine ⟨k, huu, fun T x y z hxy hyz => ?_, fun T x => ?_⟩
  · obtain ⟨s, hs⟩ := exists_lift_stageTriple B S hS D hD C m j₁
      (x ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) ≫
        stageTransition B S hS D hD f₁.left)
      (tripleLift B S hS D hD C m (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
        (y ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
        (z ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) (huu T x y hxy)
        (huu T y z hyz))
      (by
        rw [stageTransition_stage_eq B S hS D hD C f₁ _ hnat x]
        show _ = _ ≫ tripleFst B S hS D hD C m ≫ stageChartPairFst B S hS D hD C m ≫
          chartStageMap B S hS D hD U₀ f₀ C m
        rw [← Category.assoc, tripleLift_fst, ← Category.assoc, chartPairLift_fst])
    have key := hj₁ s (tripleLift B S hS D hD C m (x ≫ schemeSpaceMap (C.siteDiagram.map
        (overCompHom m k))) (y ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
        (z ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) (huu T x y hxy)
        (huu T y z hyz)) hs
      (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
      (y ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
      (z ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
      (by rw [← Category.assoc, tripleLift_fst, chartPairLift_fst])
      (by rw [← Category.assoc, tripleLift_fst, chartPairLift_snd])
      (by rw [← Category.assoc, tripleLift_snd, chartPairLift_snd])
      (huu T x y hxy) (huu T y z hyz)
      (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u)
      (y ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u)
      (z ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u)
      (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)
    exact (congrArg₂ (· ≫ ·) (pairMorphismAt_eq B S hS D hD C m u ψ _ _ huu x y hxy)
      (pairMorphismAt_eq B S hS D hD C m u ψ _ _ huu y z hyz)).trans
      (key.trans (pairMorphismAt_eq B S hS D hD C m u ψ _ _ huu x z (hxy.trans hyz)).symm)
  · obtain ⟨s, hs⟩ := exists_lift_stageChart B S hS D hD C m j₂
      (x ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) ≫
        stageTransition B S hS D hD f₂.left)
      (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)))
      (stageTransition_stage_eq B S hS D hD C f₂ _ hnat x)
    have key := hj₂ s (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) hs
      (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) (Category.comp_id _)
      (x ≫ schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u) (Category.assoc _ _ _)
    exact (pairMorphismAt_eq B S hS D hD C m u ψ _ _ huu x x rfl).trans key

/-- **The descent of a module given on the chart of the limit.**  A finitely presented module
`P` on the limit, identified on the affine étale chart of the limit with the inverse image of a
finitely presented module `G`, through an identification `η` admitting a twisted transition
morphism on the kernel pair of the chart of a stage, is the inverse image of a finitely presented
module on a stage. -/
theorem exists_iso_of_isTwistedTransition
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) (hf₀ : IsEtale B S hS f₀)
    (hs₀ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀)
    (m : Over i) {V : AlgebraicSpaces B S hS} (u : schemeSpace (C.siteDiagram.obj m) ⟶ V)
    (π : schemeSpace L.cone.pt ⟶ V)
    (hπ : schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) ≫ u = π)
    {P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1
      (limitSpace B S hS D hL).2}
    {G : Modules.{u, u} B S hS V.1 V.2} (hG : G.IsFinitePresentationOnSite)
    (η : (modulePullback B S hS (chartLimitMap B S hS D hL C L)).obj P ≅
      (modulePullback B S hS π).obj G)
    (ψ : (modulePullback B S hS (stageChartPairFst B S hS D hD C m ≫ u)).obj G ⟶
      (modulePullback B S hS (stageChartPairSnd B S hS D hD C m ≫ u)).obj G)
    (hψ : IsTwistedTransition (chartLimitMap B S hS D hL C L) π η
      (stageChartPairFst B S hS D hD C m) (stageChartPairSnd B S hS D hD C m)
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) u hπ ψ) :
    ∃ (k : I) (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD k).1
        (stageAlgebraicSpace B S hS D hD k).2),
      Q.IsFinitePresentationOnSite ∧
        Nonempty (P ≅ (modulePullback B S hS
          (limitSpaceProjection B S hS D hL hD k)).obj Q) := by
  obtain ⟨k, huu, hcoc, hid⟩ := exists_stage_descentDatum B S hS hZ D hL hD C
    L hQs m u π hπ hG η ψ hψ
  have hcovn := isEtaleCovering_chartStageMap B S hS D hD C hf₀ hs₀ (overStageComp m k)
  have hsurjn :
      IsSurjective B S hS (chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k)).hom := by
    have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact isSurjective_of_presheafSurjective B S hS _
      (MorphismProperty.of_isPullback (C.isPullback (overStageComp m k)).flip hs₀)
  obtain ⟨Q, hQ, α, hα⟩ := exists_descended_module_aux B S hS D hD C m u ψ (overStageComp m k)
    (schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) huu hcoc hid
    (isFinitePresentationOnSite_modulePullback B S hS _ G hG) hcovn hsurjn
  have hw₂ : schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k)) ≫
      chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) =
      chartLimitMap B S hS D hL C L ≫
        limitSpaceProjection B S hS D hL hD (overStageComp m k).left :=
    (chartLimitMap_comp B S hS D hL hD C L (overStageComp m k)).symm
  have hcl : schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k)) ≫
      schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) =
      schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) :=
    schemeSpaceMap_π_comp B S hS C.siteDiagram L.cone (overCompHom m k)
  have hu : schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k)) ≫
      schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u = π := by
    rw [← Category.assoc, hcl, hπ]
  let ζ := chartIso (chartLimitMap B S hS D hL C L) π
    (limitSpaceProjection B S hS D hL hD (overStageComp m k).left)
    (chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k))
    (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k)))
    (schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u) _ rfl hw₂ hu α.symm
  have hTC : ∀ (T : AlgebraicSpaces B S hS) (a b : T ⟶ schemeSpace L.cone.pt)
      (t : T ⟶ limitSpace B S hS D hL)
      (ha : a ≫ chartLimitMap B S hS D hL C L = t)
      (hb : b ≫ chartLimitMap B S hS D hL C L = t),
      twistedComparison (chartLimitMap B S hS D hL C L) π η a b t
          (a ≫ π) (b ≫ π) ha hb rfl rfl =
        twistedComparison (chartLimitMap B S hS D hL C L) π ζ a b t
          (a ≫ π) (b ≫ π) ha hb rfl rfl := by
    intro T a b t ha hb
    have hc' : ∀ a', a' ≫ chartLimitMap B S hS D hL C L = t →
        (a' ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k))) ≫
          chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k) =
        t ≫ limitSpaceProjection B S hS D hL hD (overStageComp m k).left := fun a' h => by
      rw [Category.assoc, hw₂, ← Category.assoc, h]
    have hcv : ∀ a' : T ⟶ schemeSpace L.cone.pt,
        (a' ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k))) ≫
        schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u = a' ≫ π := fun a' => by
      rw [Category.assoc, hu]
    have h₁ := twistedComparison_chartIso (chartLimitMap B S hS D hL C L) π
      (limitSpaceProjection B S hS D hL hD (overStageComp m k).left)
      (chartStageMap B S hS D hD U₀ f₀ C (overStageComp m k))
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp m k)))
      (schemeSpaceMap (C.siteDiagram.map (overCompHom m k)) ≫ u) _ rfl hw₂ hu α.symm a b t
      (a ≫ π) (b ≫ π) ha hb rfl rfl _ _ rfl rfl _ rfl (hc' a ha) (hc' b hb) (hcv a) (hcv b)
    have h₂ := twistedComparison_descended B S hS D hD C m u ψ (overStageComp m k)
      (schemeSpaceMap (C.siteDiagram.map (overCompHom m k))) huu α hα T _ _
      ((hc' a ha).trans (hc' b hb).symm) _ (hc' a ha) (a ≫ π) (b ≫ π) (hcv a) (hcv b)
    have h₃ := pairMorphism_eq_twistedComparison B S hS D hL hD C L m u π hπ η ψ
      hψ a b t ha hb _ _ (by rw [Category.assoc, hcl]) (by rw [Category.assoc, hcl])
      (huu T _ _ ((hc' a ha).trans (hc' b hb).symm)) (a ≫ π) (b ≫ π)
      (by rw [Category.assoc, hcv a]) (by rw [Category.assoc, hcv b])
    exact (h₁.trans (h₂.trans h₃)).symm
  let ell := chartLimitMap B S hS D hL C L
  have hell := isEtale_chartLimitMap B S hS D hL L hf₀
  have hells := surjective_chartLimitMap B S hS D hL L hs₀
  have hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS
    (limitSpace B S hS D hL).2 ell.hom
  have hcov := isEtaleCovering_of_surjective_etale B S hS ell hell hells
  obtain ⟨x, hx⟩ := exists_modulePullback_map_eq_of_homRestrict B S hS ell hell hrep hcov
    (η.hom ≫ ζ.inv) (fun T a b hab => moduleHomRestrict_eq_of_twistedComparison_eq ell π η ζ a b
      (a ≫ ell) rfl hab.symm (hTC T a b _ rfl hab.symm))
  obtain ⟨x', hx'⟩ := exists_modulePullback_map_eq_of_homRestrict B S hS ell hell hrep hcov
    (ζ.hom ≫ η.inv) (fun T a b hab => moduleHomRestrict_eq_of_twistedComparison_eq ell π ζ η a b
      (a ≫ ell) rfl hab.symm (hTC T a b _ rfl hab.symm).symm)
  have := faithful_modulePullback B S hS L.cone.pt ell hell hells
  refine ⟨(overStageComp m k).left, Q, hQ, ⟨⟨x, x', ?_, ?_⟩⟩⟩ <;>
  · apply (modulePullback B S hS ell).map_injective
    rw [Functor.map_comp, hx, hx', CategoryTheory.Functor.map_id]
    simp

omit [IsCofiltered I] in
/-- The variables of the chart system are those of the system, so the essential surjectivity
statement below carries no chart. -/
theorem modulePullback_isFinitePresentationOnSite_aux {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    {P : Modules.{u, u} B S hS Y.1 Y.2} (hP : P.IsFinitePresentationOnSite) :
    ((modulePullback B S hS g).obj P).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_modulePullback B S hS g P hP

/-- **Stacks 07V7, the essential surjectivity clause.**  For a cofiltered system of quasi-compact
and quasi-separated algebraic spaces with affine transition morphisms, every finitely presented
module on the limit is the inverse image of a finitely presented module on some stage. -/
theorem exists_iso_modulePullback_limitProjection
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1
      (limitSpace B S hS D hL).2)
    (hP : P.IsFinitePresentationOnSite) :
    ∃ (k : I) (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD k).1
        (stageAlgebraicSpace B S hS D hD k).2),
      Q.IsFinitePresentationOnSite ∧
        Nonempty (P ≅ (modulePullback B S hS
          (limitSpaceProjection B S hS D hL hD k)).obj Q) := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨V₀, f₀, hV₀, hs₀, hf₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i) (hD i)).mp
      (hQc i)
  let C := affineChartSystem B S hS i D ⟨V₀, hV₀⟩ f₀ hL.1
  let L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hL.2.2)
  obtain ⟨l, G, hG, ⟨η⟩⟩ := exists_iso_modulePullback_of_isAffine B S hS C.siteDiagram L.cone
    C.isAffine_obj L.schemeIsLimit _
    (modulePullback_isFinitePresentationOnSite_aux B S hS
      (chartLimitMap B S hS D hL C L) hP)
  obtain ⟨j, ψ, hψ⟩ := exists_isTwistedTransition B S hS hZ D hL hD C L l hQc
    hQs hG η
  exact exists_iso_of_isTwistedTransition B S hS hZ D hL hD C L hQs hf₀ hs₀
    (overStageComp l j) _ _ (schemeSpaceMap_π_comp B S hS C.siteDiagram L.cone (overCompHom l j))
    hG η ψ hψ

end AlgebraicGeometry.Space

end
