module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleEssSurjDatum

/-!
# Essential surjectivity in Stacks 07V7: the cocycle condition at a stage

The pair morphisms of a twisted transition morphism are the twisted comparisons at the limit,
so they satisfy the cocycle condition there and are the identity on the diagonal.  Read on the
triple product `U_m ×_{X_m} U_m ×_{X_m} U_m` and on the chart `U_m`, these are equalities of
morphisms between finitely presented modules whose inverse images to the limits of the systems
of base changes agree; by the faithfulness clause for those systems they hold at a later stage.

## Main results

* `AlgebraicGeometry.Space.pairMorphism_eq_twistedComparison`: the pair morphisms at the limit.
* `AlgebraicGeometry.Space.exists_stage_cocycle`: the cocycle condition at a later stage.
* `AlgebraicGeometry.Space.exists_stage_diag`: the diagonal condition at a later stage.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
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
  (C : AffineChartSystem B S hS i D U₀ f₀) (L : AffineChartSystem.LimitBridge C) (m : Over i)
  {V : AlgebraicSpaces B S hS} (u : schemeSpace (C.siteDiagram.obj m) ⟶ V)
  (π : schemeSpace L.cone.pt ⟶ V)
  (hπ : schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) ≫ u = π)
  {P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1
    (limitSpace B S hS D hL).2}
  {G : Modules.{u, u} B S hS V.1 V.2}
  (η : (modulePullback B S hS (chartLimitMap B S hS D hL C L)).obj P ≅
    (modulePullback B S hS π).obj G)
  (ψ : (modulePullback B S hS (stageChartPairFst B S hS D hD C m ≫ u)).obj G ⟶
    (modulePullback B S hS (stageChartPairSnd B S hS D hD C m ≫ u)).obj G)

include hπ in
omit [IsCofiltered I] in
/-- A morphism to the chart of the limit, composed with `π`, is the composite of its projection to
the chart of the stage with `u`. -/
theorem pairMorphism_eq_aux {T : AlgebraicSpaces B S hS} (a : T ⟶ schemeSpace L.cone.pt)
    (x : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : a ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = x) (vx : T ⟶ V)
    (hvx : x ≫ u = vx) : a ≫ π = vx := by
  rw [← hπ, ← Category.assoc, hx, hvx]

omit [IsCofiltered I] in
/-- **The pair morphisms at the limit are the twisted comparisons.** -/
theorem pairMorphism_eq_twistedComparison
    (hψ : IsTwistedTransition (chartLimitMap B S hS D hL C L) π η
      (stageChartPairFst B S hS D hD C m) (stageChartPairSnd B S hS D hD C m)
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) u hπ ψ)
    {T : AlgebraicSpaces B S hS} (a b : T ⟶ schemeSpace L.cone.pt)
    (t : T ⟶ limitSpace B S hS D hL)
    (ha : a ≫ chartLimitMap B S hS D hL C L = t)
    (hb : b ≫ chartLimitMap B S hS D hL C L = t)
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : a ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = x)
    (hy : b ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = y)
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx vy : T ⟶ V) (hvx : x ≫ u = vx) (hvy : y ≫ u = vy) :
    pairMorphism B S hS D hD C m u ψ x y h vx vy hvx hvy =
      twistedComparison (chartLimitMap B S hS D hL C L) π η a b t vx vy ha
        hb (pairMorphism_eq_aux B S hS D C L m u π hπ a x hx vx hvx)
        (pairMorphism_eq_aux B S hS D C L m u π hπ b y hy vy hvy) :=
  hψ T a b t ha hb (chartPairLift B S hS D hD C m x y h)
    (by rw [chartPairLift_fst, hx]) (by rw [chartPairLift_snd, hy]) vx vy _ _

omit [IsCofiltered I] in
/-- A morphism to the chart of the limit is given by its composites with the chart of the limit
and with the projection to the chart of a stage. -/
theorem exists_lift_chartLimit {T : AlgebraicSpaces B S hS}
    (t : T ⟶ limitSpace B S hS D hL)
    (x : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : t ≫ limitSpaceProjection B S hS D hL hD m.left =
      x ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    ∃ n : T ⟶ schemeSpace L.cone.pt,
      n ≫ chartLimitMap B S hS D hL C L = t ∧
        n ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = x :=
  ⟨ObjectProperty.homMk ((L.isPullback_stage m).lift t.hom x.hom (congrArg (fun z => z.hom) h)),
    ObjectProperty.hom_ext _ ((L.isPullback_stage m).lift_fst _ _ _),
    ObjectProperty.hom_ext _ ((L.isPullback_stage m).lift_snd _ _ _)⟩

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FinitePresentationModuleEssSurjCocycle
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Triple

/-- The triple product `U_m ×_{X_m} U_m ×_{X_m} U_m` of the chart of a stage. -/
noncomputable abbrev chartTriple : AlgebraicSpaces B S hS :=
  ⟨pullback (stageChartPairSnd B S hS D hD C m).hom (stageChartPairFst B S hS D hD C m).hom,
    isAlgebraicSpace_pullback B S hS _ _ (stageChartPair B S hS D hD C m).2
      (stageChartPair B S hS D hD C m).2 (schemeSpace (C.siteDiagram.obj m)).2⟩

/-- The projection of the triple product to the first two factors. -/
noncomputable def tripleFst : chartTriple B S hS D hD C m ⟶ stageChartPair B S hS D hD C m :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The projection of the triple product to the last two factors. -/
noncomputable def tripleSnd : chartTriple B S hS D hD C m ⟶ stageChartPair B S hS D hD C m :=
  ObjectProperty.homMk (pullback.snd _ _)

omit [IsCofiltered I] in
/-- The two projections of the triple product agree on the middle factor. -/
theorem triple_condition :
    tripleFst B S hS D hD C m ≫ stageChartPairSnd B S hS D hD C m =
      tripleSnd B S hS D hD C m ≫ stageChartPairFst B S hS D hD C m :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The morphism into the triple product given by three morphisms into the chart. -/
noncomputable def tripleLift {T : AlgebraicSpaces B S hS}
    (x y z : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = z ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    T ⟶ chartTriple B S hS D hD C m :=
  ObjectProperty.homMk (pullback.lift (chartPairLift B S hS D hD C m x y hxy).hom
    (chartPairLift B S hS D hD C m y z hyz).hom
    (congrArg (fun w => w.hom) ((chartPairLift_snd B S hS D hD C m x y hxy).trans
      (chartPairLift_fst B S hS D hD C m y z hyz).symm)))

omit [IsCofiltered I] in
/-- The first two factors of `tripleLift` form the pair given by the first two morphisms. -/
theorem tripleLift_fst {T : AlgebraicSpaces B S hS}
    (x y z : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = z ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    tripleLift B S hS D hD C m x y z hxy hyz ≫ tripleFst B S hS D hD C m =
      chartPairLift B S hS D hD C m x y hxy :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

omit [IsCofiltered I] in
/-- The last two factors of `tripleLift` form the pair given by the last two morphisms. -/
theorem tripleLift_snd {T : AlgebraicSpaces B S hS}
    (x y z : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = z ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    tripleLift B S hS D hD C m x y z hxy hyz ≫ tripleSnd B S hS D hD C m =
      chartPairLift B S hS D hD C m y z hyz :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

omit [IsCofiltered I] in
/-- The two projections of a morphism into the pair product agree over the stage. -/
theorem chartPair_stage_condition {T : AlgebraicSpaces B S hS}
    (w : T ⟶ stageChartPair B S hS D hD C m) :
    (w ≫ stageChartPairFst B S hS D hD C m) ≫ chartStageMap B S hS D hD U₀ f₀ C m =
      (w ≫ stageChartPairSnd B S hS D hD C m) ≫ chartStageMap B S hS D hD U₀ f₀ C m := by
  rw [Category.assoc, Category.assoc, chartPair_condition]

end Triple

section StageEquations

/-- The structure morphism of the triple product to the stage. -/
noncomputable abbrev tripleToStage :
    chartTriple B S hS D hD C m ⟶ stageAlgebraicSpace B S hS D hD m.left :=
  tripleFst B S hS D hD C m ≫ chartPairToStage B S hS D hD C m

omit [IsCofiltered I] in
/-- The first projection of the triple product to the chart, followed by the chart's map to the
stage, is the structure morphism `tripleToStage`. -/
theorem triple_π₁_stage : (tripleFst B S hS D hD C m ≫ stageChartPairFst B S hS D hD C m) ≫
    chartStageMap B S hS D hD U₀ f₀ C m = tripleToStage B S hS D hD C m := by
  rw [Category.assoc]; rfl

omit [IsCofiltered I] in
/-- The second projection of the triple product to the chart, followed by the chart's map to the
stage, is the structure morphism `tripleToStage`. -/
theorem triple_π₂_stage : (tripleFst B S hS D hD C m ≫ stageChartPairSnd B S hS D hD C m) ≫
    chartStageMap B S hS D hD U₀ f₀ C m = tripleToStage B S hS D hD C m := by
  rw [Category.assoc, ← chartPair_condition B S hS D hD C m]; rfl

omit [IsCofiltered I] in
/-- The third projection of the triple product to the chart, followed by the chart's map to the
stage, is the structure morphism `tripleToStage`. -/
theorem triple_π₃_stage : (tripleSnd B S hS D hD C m ≫ stageChartPairSnd B S hS D hD C m) ≫
    chartStageMap B S hS D hD U₀ f₀ C m = tripleToStage B S hS D hD C m := by
  rw [Category.assoc, ← chartPair_condition B S hS D hD C m, ← Category.assoc,
    ← triple_condition B S hS D hD C m, Category.assoc, ← chartPair_condition B S hS D hD C m]
  rfl

/-- A point of a stage of the system of base changes of the triple product. -/
theorem exists_lift_stageTriple (k : Over m.left) {T : AlgebraicSpaces B S hS}
    (τ : T ⟶ stageAlgebraicSpace B S hS D hD k.left) (w : T ⟶ chartTriple B S hS D hD C m)
    (h : τ ≫ stageTransition B S hS D hD k.hom = w ≫ tripleToStage B S hS D hD C m) :
    ∃ s : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D m.left
        (tripleToStage B S hS D hD C m).hom)
        (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (chartTriple B S hS D hD C m)
          (tripleToStage B S hS D hD C m)) k,
      s ≫ stageBaseChangeSpaceSnd B S hS D hD (chartTriple B S hS D hD C m)
        (tripleToStage B S hS D hD C m) k = w :=
  ⟨ObjectProperty.homMk (pullback.lift τ.hom w.hom (congrArg (fun z => z.hom) h)),
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)⟩

/-- A point of a stage of the system of base changes of the chart. -/
theorem exists_lift_stageChart (k : Over m.left) {T : AlgebraicSpaces B S hS}
    (τ : T ⟶ stageAlgebraicSpace B S hS D hD k.left) (x : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : τ ≫ stageTransition B S hS D hD k.hom = x ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    ∃ s : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D m.left
        (chartStageMap B S hS D hD U₀ f₀ C m).hom)
        (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (schemeSpace (C.siteDiagram.obj m))
          (chartStageMap B S hS D hD U₀ f₀ C m)) k,
      s ≫ stageBaseChangeSpaceSnd B S hS D hD (schemeSpace (C.siteDiagram.obj m))
        (chartStageMap B S hS D hD U₀ f₀ C m) k = x :=
  ⟨ObjectProperty.homMk (pullback.lift τ.hom x.hom (congrArg (fun z => z.hom) h)),
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)⟩

end StageEquations

section Cocycle

variable (hψ : IsTwistedTransition (chartLimitMap B S hS D hL C L) π η
  (stageChartPairFst B S hS D hD C m) (stageChartPairSnd B S hS D hD C m)
  (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) u hπ ψ)

include hψ in
omit [IsCofiltered I] in
/-- **The pair morphisms satisfy the cocycle condition at points of the limit.** -/
theorem pairMorphism_cocycle_of_limit {T : AlgebraicSpaces B S hS}
    (a b c : T ⟶ schemeSpace L.cone.pt)
    (t : T ⟶ limitSpace B S hS D hL)
    (ha : a ≫ chartLimitMap B S hS D hL C L = t)
    (hb : b ≫ chartLimitMap B S hS D hL C L = t)
    (hc : c ≫ chartLimitMap B S hS D hL C L = t)
    (x y z : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : a ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = x)
    (hy : b ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = y)
    (hz : c ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) = z)
    (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = z ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx vy vz : T ⟶ V) (hvx : x ≫ u = vx) (hvy : y ≫ u = vy) (hvz : z ≫ u = vz) :
    pairMorphism B S hS D hD C m u ψ x y hxy vx vy hvx hvy ≫
        pairMorphism B S hS D hD C m u ψ y z hyz vy vz hvy hvz =
      pairMorphism B S hS D hD C m u ψ x z (hxy.trans hyz) vx vz hvx hvz := by
  rw [pairMorphism_eq_twistedComparison B S hS D hL hD C L m u π hπ η ψ hψ a b
      t ha hb x y hx hy hxy vx vy hvx hvy,
    pairMorphism_eq_twistedComparison B S hS D hL hD C L m u π hπ η ψ hψ b c
      t hb hc y z hy hz hyz vy vz hvy hvz,
    pairMorphism_eq_twistedComparison B S hS D hL hD C L m u π hπ η ψ hψ a c
      t ha hc x z hx hz (hxy.trans hyz) vx vz hvx hvz, twistedComparison_comp]

omit [IsCofiltered I] in
/-- Two morphisms into the chart that agree over the stage still agree over the stage after
precomposition with any morphism. -/
theorem comp_stage_eq {T R : AlgebraicSpaces B S hS} (s : T ⟶ R)
    (x y : R ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    (s ≫ x) ≫ chartStageMap B S hS D hD U₀ f₀ C m =
      (s ≫ y) ≫ chartStageMap B S hS D hD U₀ f₀ C m := by
  rw [Category.assoc, Category.assoc, h]

omit [IsCofiltered I] in
/-- The restriction of a pair morphism along a morphism, with the restricted morphisms written as
composites. -/
theorem moduleHomRestrict₂_pairMorphism_comp {T T' : AlgebraicSpaces B S hS} (s : T' ⟶ T)
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    moduleHomRestrict₂ G G s (x ≫ u) (y ≫ u) (s ≫ x ≫ u) (s ≫ y ≫ u) rfl rfl
        (pairMorphism B S hS D hD C m u ψ x y h (x ≫ u) (y ≫ u) rfl rfl) =
      pairMorphism B S hS D hD C m u ψ (s ≫ x) (s ≫ y) (comp_stage_eq B S hS D hD C m s x y h)
        (s ≫ x ≫ u) (s ≫ y ≫ u) (Category.assoc _ _ _) (Category.assoc _ _ _) :=
  moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ s x y h _ _ rfl rfl _ _ rfl rfl _ _ _ rfl rfl
    _ _

omit [IsCofiltered I] in
/-- The restriction of a composite of two pair morphisms. -/
theorem moduleHomRestrict₂_pairMorphism_comp₂ {T T' : AlgebraicSpaces B S hS} (s : T' ⟶ T)
    (x y z : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = z ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    moduleHomRestrict₂ G G s (x ≫ u) (z ≫ u) (s ≫ x ≫ u) (s ≫ z ≫ u) rfl rfl
        (pairMorphism B S hS D hD C m u ψ x y hxy (x ≫ u) (y ≫ u) rfl rfl ≫
          pairMorphism B S hS D hD C m u ψ y z hyz (y ≫ u) (z ≫ u) rfl rfl) =
      pairMorphism B S hS D hD C m u ψ (s ≫ x) (s ≫ y) (comp_stage_eq B S hS D hD C m s x y hxy)
          (s ≫ x ≫ u) (s ≫ y ≫ u) (Category.assoc _ _ _) (Category.assoc _ _ _) ≫
        pairMorphism B S hS D hD C m u ψ (s ≫ y) (s ≫ z) (comp_stage_eq B S hS D hD C m s y z hyz)
          (s ≫ y ≫ u) (s ≫ z ≫ u) (Category.assoc _ _ _) (Category.assoc _ _ _) :=
  (moduleHomRestrict₂_comp s (x ≫ u) (y ≫ u) (z ≫ u) (s ≫ x ≫ u) (s ≫ y ≫ u) (s ≫ z ≫ u) rfl rfl
    rfl _ _).trans (congrArg₂ (· ≫ ·)
      (moduleHomRestrict₂_pairMorphism_comp B S hS D hD C m u ψ s x y hxy)
      (moduleHomRestrict₂_pairMorphism_comp B S hS D hD C m u ψ s y z hyz))

include hψ in
/-- **The cocycle condition at the limit of a system of base changes.**  For three morphisms
`x, y, z : R ⟶ U_m` over the stage, the cocycle condition of the pair morphisms holds after
inverse image to the base change `X ×_{X_m} R` of the limit. -/
theorem pairMorphism_cocycle_limitBaseChange {R : AlgebraicSpaces B S hS}
    (r : R ⟶ stageAlgebraicSpace B S hS D hD m.left) (x y z : R ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = r)
    (hy : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = r)
    (hz : z ≫ chartStageMap B S hS D hD U₀ f₀ C m = r) :
    (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map
        (pairMorphism B S hS D hD C m u ψ x y (hx.trans hy.symm) (x ≫ u) (y ≫ u) rfl rfl ≫
          pairMorphism B S hS D hD C m u ψ y z (hy.trans hz.symm) (y ≫ u) (z ≫ u) rfl rfl) =
      (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map
        (pairMorphism B S hS D hD C m u ψ x z ((hx.trans hy.symm).trans (hy.trans hz.symm))
          (x ≫ u) (z ≫ u) rfl rfl) := by
  have lift (x : R ⟶ schemeSpace (C.siteDiagram.obj m))
      (hx : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = r) := exists_lift_chartLimit B S hS D hL hD C
    L m _ (limitBaseChangeSnd B S hS D hL hD R r ≫ x)
    (by rw [limitBaseChangeFst_comp, Category.assoc, hx])
  obtain ⟨n₁, hn₁, hn₁'⟩ := lift x hx
  obtain ⟨n₂, hn₂, hn₂'⟩ := lift y hy
  obtain ⟨n₃, hn₃, hn₃'⟩ := lift z hz
  exact (moduleHomRestrict₂_eq_iff _ _ _ _ _ rfl rfl _ _).1
    ((moduleHomRestrict₂_pairMorphism_comp₂ B S hS D hD C m u ψ _ x y z _ _).trans
      ((pairMorphism_cocycle_of_limit B S hS D hL hD C L m u π hπ η ψ hψ n₁ n₂
        n₃ _ hn₁ hn₂ hn₃ _ _ _ hn₁' hn₂' hn₃' _ _ _ _ _ _ _ _).trans
        (moduleHomRestrict₂_pairMorphism_comp B S hS D hD C m u ψ _ x z _).symm))

include hψ in
/-- **The diagonal condition at the limit of a system of base changes.** -/
theorem pairMorphism_diag_limitBaseChange {R : AlgebraicSpaces B S hS}
    (r : R ⟶ stageAlgebraicSpace B S hS D hD m.left) (x : R ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = r) :
    (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map
        (pairMorphism B S hS D hD C m u ψ x x rfl (x ≫ u) (x ≫ u) rfl rfl) =
      (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map
        (𝟙 _) := by
  have hlf := limitBaseChangeFst_comp B S hS D hL hD R r
  obtain ⟨n₁, hn₁, hn₁'⟩ := exists_lift_chartLimit B S hS D hL hD C L m _
    (limitBaseChangeSnd B S hS D hL hD R r ≫ x)
    (by rw [hlf, Category.assoc, hx])
  exact (moduleHomRestrict₂_eq_iff _ _ _ _ _ rfl rfl _ _).1
    ((moduleHomRestrict₂_pairMorphism_comp B S hS D hD C m u ψ _ x x rfl).trans
      ((pairMorphism_eq_twistedComparison B S hS D hL hD C L m u π hπ η ψ hψ n₁
        n₁ _ hn₁ hn₁ _ _ hn₁' hn₁' _ _ _ _ _).trans
        ((twistedComparison_self _ _ _ _ _ _ _ _).trans (moduleHomRestrict₂_id _ _ _ _).symm)))

/-- An equation of morphisms on `R` which holds after inverse image to a stage of the system of
base changes holds after restriction to every space mapping to that stage. -/
theorem moduleHomRestrict₂_eq_of_stage {R T : AlgebraicSpaces B S hS}
    (r : R ⟶ stageAlgebraicSpace B S hS D hD m.left) (j : Over m.left)
    {p p' : R ⟶ V} (a b : (modulePullback B S hS p).obj G ⟶ (modulePullback B S hS p').obj G)
    (hj : (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).map a =
      (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).map b)
    (s : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D m.left r.hom)
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j)
    (w : T ⟶ R) (hs : s ≫ stageBaseChangeSpaceSnd B S hS D hD R r j = w) (q q' : T ⟶ V)
    (hq : w ≫ p = q) (hq' : w ≫ p' = q') :
    moduleHomRestrict₂ G G w p p' q q' hq hq' a = moduleHomRestrict₂ G G w p p' q q' hq hq' b := by
  subst hs
  exact (moduleHomRestrict₂_eq_iff _ _ _ _ _ hq hq' a b).2
    (map_comp_eq_of_map_map_eq B S hS _ _ (by rw [hj]))

end Cocycle

section StageCocycle

/-- **The cocycle condition at a stage**, for three morphisms into the chart of `m` from a space
`R` over the stage: there is a later stage such that the cocycle condition holds at every point
of `R` that lifts to the base change of that stage. -/
theorem exists_stage_cocycle
    (hψ : IsTwistedTransition (chartLimitMap B S hS D hL C L) π η
      (stageChartPairFst B S hS D hD C m) (stageChartPairSnd B S hS D hD C m)
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) u hπ ψ)
    (hG : G.IsFinitePresentationOnSite) {R : AlgebraicSpaces B S hS}
    (hRqc : IsQuasiCompactSpace B S hS R.1)
    (r : R ⟶ stageAlgebraicSpace B S hS D hD m.left) (x y z : R ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = r)
    (hy : y ≫ chartStageMap B S hS D hD U₀ f₀ C m = r)
    (hz : z ≫ chartStageMap B S hS D hD U₀ f₀ C m = r) :
    ∃ j : Over m.left, ∀ {T : AlgebraicSpaces B S hS}
      (s : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D m.left r.hom)
        (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j)
      (w : T ⟶ R) (_ : s ≫ stageBaseChangeSpaceSnd B S hS D hD R r j = w)
      (x' y' z' : T ⟶ schemeSpace (C.siteDiagram.obj m)) (_hx' : w ≫ x = x') (_hy' : w ≫ y = y')
      (_hz' : w ≫ z = z')
      (hxy : x' ≫ chartStageMap B S hS D hD U₀ f₀ C m = y' ≫ chartStageMap B S hS D hD U₀ f₀ C m)
      (hyz : y' ≫ chartStageMap B S hS D hD U₀ f₀ C m = z' ≫ chartStageMap B S hS D hD U₀ f₀ C m)
      (vx vy vz : T ⟶ V) (hvx : x' ≫ u = vx) (hvy : y' ≫ u = vy) (hvz : z' ≫ u = vz),
      pairMorphism B S hS D hD C m u ψ x' y' hxy vx vy hvx hvy ≫
          pairMorphism B S hS D hD C m u ψ y' z' hyz vy vz hvy hvz =
        pairMorphism B S hS D hD C m u ψ x' z' (hxy.trans hyz) vx vz hvx hvz := by
  obtain ⟨j, hj⟩ := eventually_map_eq_of_baseChange' B S hS D hL hD R r hRqc
    (isFinitePresentationOnSite_modulePullback B S hS (x ≫ u) G hG)
    (isFinitePresentationOnSite_modulePullback B S hS (z ≫ u) G hG) _ _
    (pairMorphism_cocycle_limitBaseChange B S hS D hL hD C L m u π hπ η ψ hψ r x
      y z hx hy hz)
  refine ⟨j, fun s w hs x' y' z' hx' hy' hz' hxy hyz vx vy vz hvx hvy hvz => ?_⟩
  have hwx : w ≫ x ≫ u = vx := by rw [← Category.assoc, hx', hvx]
  have hwy : w ≫ y ≫ u = vy := by rw [← Category.assoc, hy', hvy]
  have hwz : w ≫ z ≫ u = vz := by rw [← Category.assoc, hz', hvz]
  have e := moduleHomRestrict₂_eq_of_stage B S hS D hD m r j _ _ hj s w hs vx vz hwx hwz
  rw [moduleHomRestrict₂_comp w (x ≫ u) (y ≫ u) (z ≫ u) vx vy vz hwx hwy hwz,
    moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ w x y _ _ _ rfl rfl x' y' hx' hy' hxy vx vy
      hwx hwy hvx hvy,
    moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ w y z _ _ _ rfl rfl y' z' hy' hz' hyz vy vz
      hwy hwz hvy hvz,
    moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ w x z _ _ _ rfl rfl x' z' hx' hz'
      (hxy.trans hyz) vx vz hwx hwz hvx hvz] at e
  exact e

/-- **The diagonal condition at a stage.** -/
theorem exists_stage_diag
    (hψ : IsTwistedTransition (chartLimitMap B S hS D hL C L) π η
      (stageChartPairFst B S hS D hD C m) (stageChartPairSnd B S hS D hD C m)
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) u hπ ψ)
    (hG : G.IsFinitePresentationOnSite) {R : AlgebraicSpaces B S hS}
    (hRqc : IsQuasiCompactSpace B S hS R.1)
    (r : R ⟶ stageAlgebraicSpace B S hS D hD m.left) (x : R ⟶ schemeSpace (C.siteDiagram.obj m))
    (hx : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = r) :
    ∃ j : Over m.left, ∀ {T : AlgebraicSpaces B S hS}
      (s : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D m.left r.hom)
        (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j)
      (w : T ⟶ R) (_ : s ≫ stageBaseChangeSpaceSnd B S hS D hD R r j = w)
      (x' : T ⟶ schemeSpace (C.siteDiagram.obj m)) (_hx' : w ≫ x = x') (vx : T ⟶ V)
      (hvx : x' ≫ u = vx),
      pairMorphism B S hS D hD C m u ψ x' x' rfl vx vx hvx hvx = 𝟙 _ := by
  obtain ⟨j, hj⟩ := eventually_map_eq_of_baseChange' B S hS D hL hD R r hRqc
    (isFinitePresentationOnSite_modulePullback B S hS (x ≫ u) G hG)
    (isFinitePresentationOnSite_modulePullback B S hS (x ≫ u) G hG) _ _
    (pairMorphism_diag_limitBaseChange B S hS D hL hD C L m u π hπ η ψ hψ r x hx)
  refine ⟨j, fun s w hs x' hx' vx hvx => ?_⟩
  have hwx : w ≫ x ≫ u = vx := by rw [← Category.assoc, hx', hvx]
  have e := moduleHomRestrict₂_eq_of_stage B S hS D hD m r j _ _ hj s w hs vx vx hwx hwx
  rw [moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ w x x _ _ _ rfl rfl x' x' hx' hx' rfl vx
      vx hwx hwx hvx hvx, moduleHomRestrict₂_id] at e
  exact e

end StageCocycle

end AlgebraicGeometry.Space

end
