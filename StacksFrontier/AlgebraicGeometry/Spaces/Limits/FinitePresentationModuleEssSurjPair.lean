module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleBaseChangeFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleTwistedComparison

/-!
# Essential surjectivity in Stacks 07V7: the transition morphism at a stage

Let `D` be a cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces with
affine transition morphisms and limit `X`, let `U = lim U_j` be the affine étale chart of `X`
obtained from an affine étale chart of a stage, `ell : U ⟶ X`, and let `P` be an `𝒪_X`-module
with an identification `η : ell^*P ≅ π_l^*G` with the inverse image of a finitely presented
module `G` on a chart `U_l`.  The canonical comparison of the two inverse images of `P` to
`U ×_X U`, read through `η`, is a morphism between inverse images of `G`; by the fullness clause
for the system of base changes of the kernel pair `U_l ×_{X_l} U_l`, it comes from a morphism
between inverse images of `G` to the kernel pair `U_m ×_{X_m} U_m` of a later stage `m`, whose
restrictions to the limit are the twisted comparisons of `η`.

## Main results

* `AlgebraicGeometry.Space.exists_isTwistedTransition`: such a morphism exists.

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

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FinitePresentationModuleEssSurjPair
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

omit [IsCofiltered I] in
/-- The relation between a morphism on a stage of a system of base changes and a morphism on
the limit, read through `homConjLInv` as a relation between morphisms of inverse images of one
module. -/
theorem moduleHomRestrict₂_homConjLInv_eq {V Q Q' L R : AlgebraicSpaces B S hS}
    {G : Modules.{u, u} B S hS V.1 V.2} (lam : L ⟶ Q) (sbc : Q ⟶ R) (θ : L ⟶ Q') (lbs : Q' ⟶ R)
    (hθ : lam ≫ sbc = θ ≫ lbs) (pr₁ pr₂ : R ⟶ V)
    (ψ₀ : (modulePullback B S hS sbc).obj ((modulePullback B S hS pr₁).obj G) ⟶
      (modulePullback B S hS sbc).obj ((modulePullback B S hS pr₂).obj G))
    (Λ : (modulePullback B S hS (lbs ≫ pr₁)).obj G ⟶ (modulePullback B S hS (lbs ≫ pr₂)).obj G)
    (h : moduleHomRestrict _ _ lam sbc (θ ≫ lbs) hθ ψ₀ =
      moduleHomRestrict _ _ θ lbs (θ ≫ lbs) rfl (homConjL lbs lbs pr₁ pr₂ Λ)) :
    moduleHomRestrict₂ G G lam (sbc ≫ pr₁) (sbc ≫ pr₂) ((θ ≫ lbs) ≫ pr₁) ((θ ≫ lbs) ≫ pr₂)
        (by rw [← Category.assoc, hθ]) (by rw [← Category.assoc, hθ])
        (homConjLInv sbc sbc pr₁ pr₂ ψ₀) =
      moduleHomRestrict₂ G G θ (lbs ≫ pr₁) (lbs ≫ pr₂) ((θ ≫ lbs) ≫ pr₁) ((θ ≫ lbs) ≫ pr₂)
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm Λ := by
  have h' := congrArg (homConjLInv (θ ≫ lbs) (θ ≫ lbs) pr₁ pr₂) h
  rwa [← moduleHomRestrict₂_self, ← moduleHomRestrict₂_self, homConjLInv_moduleHomRestrict₂,
    homConjLInv_moduleHomRestrict₂, homConjLInv_homConjL] at h'

section Pair

variable {i : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i}
  (C : AffineChartSystem B S hS i D U₀ f₀) (L : AffineChartSystem.LimitBridge C) (l : Over i)

omit [IsCofiltered I] in
/-- A morphism into the base change of the limit along the kernel pair is given by its two
components. -/
theorem exists_lift_limitBaseChangeSpace {T : AlgebraicSpaces B S hS}
    (t : T ⟶ limitSpace B S hS D hL)
    (s : T ⟶ stageChartPair B S hS D hD C l)
    (h : t ≫ limitSpaceProjection B S hS D hL hD l.left =
      s ≫ chartPairToStage B S hS D hD C l) :
    ∃ y : T ⟶ limitBaseChangeSpace B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l),
      y ≫ limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) = t ∧
        y ≫ limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) = s :=
  ⟨ObjectProperty.homMk (pullback.lift t.hom s.hom (congrArg (fun z => z.hom) h)),
    ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _),
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)⟩

omit [IsCofiltered I] in
/-- Morphisms into the chart of the limit are determined by their composites with the chart and
with the projection to the chart of a stage. -/
theorem chartLimit_hom_ext {T : AlgebraicSpaces B S hS} (m : Over i)
    {x y : T ⟶ schemeSpace L.cone.pt}
    (h₁ : x ≫ chartLimitMap B S hS D hL C L =
      y ≫ chartLimitMap B S hS D hL C L)
    (h₂ : x ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m) =
      y ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) : x = y :=
  ObjectProperty.hom_ext _ ((L.isPullback_stage m).hom_ext (congrArg (fun z => z.hom) h₁)
    (congrArg (fun z => z.hom) h₂))

omit [IsCofiltered I] in
/-- Morphisms into a stage of the system of base changes are determined by their two
components. -/
theorem stageBaseChange_hom_ext {R : AlgebraicSpaces B S hS}
    (r : R ⟶ stageAlgebraicSpace B S hS D hD l.left) (j : Over l.left)
    {T : AlgebraicSpaces B S hS}
    {x y : T ⟶ stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D l.left r.hom)
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j}
    (h₁ : x ≫ stageBaseChangeSpaceFst B S hS D hD R r j =
      y ≫ stageBaseChangeSpaceFst B S hS D hD R r j)
    (h₂ : x ≫ stageBaseChangeSpaceSnd B S hS D hD R r j =
      y ≫ stageBaseChangeSpaceSnd B S hS D hD R r j) : x = y :=
  ObjectProperty.hom_ext _ (pullback.hom_ext (congrArg (fun z => z.hom) h₁)
    (congrArg (fun z => z.hom) h₂))

omit [IsCofiltered I] in
/-- The projection `pairStageProj` from the base change of the kernel pair to the stage `j`,
composed with the chart at `overStageComp l j`, is the first projection of the base change. -/
theorem pairStageProj_comp_chartStageMap
    (pr : stageChartPair B S hS D hD C l ⟶ schemeSpace (C.siteDiagram.obj l))
    (hpr : pr ≫ chartStageMap B S hS D hD U₀ f₀ C l = chartPairToStage B S hS D hD C l)
    (j : Over l.left) :
    pairStageProj B S hS D hD C l pr hpr j ≫ chartStageMap B S hS D hD U₀ f₀ C (overStageComp l j) =
      stageBaseChangeSpaceFst B S hS D hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) j :=
  ObjectProperty.hom_ext _ (pairStageProj_comp_stageMap B S hS D hD C l pr hpr j)

omit [IsCofiltered I] in
/-- Morphisms into the kernel pair are determined by their two components. -/
theorem chartPair_hom_ext {T : AlgebraicSpaces B S hS} {x y : T ⟶ stageChartPair B S hS D hD C l}
    (h₁ : x ≫ stageChartPairFst B S hS D hD C l = y ≫ stageChartPairFst B S hS D hD C l)
    (h₂ : x ≫ stageChartPairSnd B S hS D hD C l = y ≫ stageChartPairSnd B S hS D hD C l) : x = y :=
  ObjectProperty.hom_ext _ (pullback.hom_ext (congrArg (fun z => z.hom) h₁)
    (congrArg (fun z => z.hom) h₂))

omit [IsCofiltered I] in
/-- A morphism into the kernel pair is given by its two components. -/
theorem exists_lift_chartPair {T : AlgebraicSpaces B S hS}
    (a b : T ⟶ schemeSpace (C.siteDiagram.obj l))
    (h : a ≫ chartStageMap B S hS D hD U₀ f₀ C l = b ≫ chartStageMap B S hS D hD U₀ f₀ C l) :
    ∃ ρ : T ⟶ stageChartPair B S hS D hD C l,
      ρ ≫ stageChartPairFst B S hS D hD C l = a ∧ ρ ≫ stageChartPairSnd B S hS D hD C l = b :=
  ⟨ObjectProperty.homMk (pullback.lift a.hom b.hom (congrArg (fun z => z.hom) h)),
    ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _),
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)⟩

omit [IsCofiltered I] in
/-- Two morphisms into the chart of the limit over a common morphism to the limit lift to the base
change of the limit along the kernel pair, through given factorizations `μ₁`, `μ₂`. -/
theorem exists_lift_limitBaseChangeSpace_of_chartLimitMap
    (μ₁ μ₂ : limitBaseChangeSpace B S hS D hL hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l) ⟶ schemeSpace L.cone.pt)
    (hμ₁ : μ₁ ≫ chartLimitMap B S hS D hL C L =
      limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l))
    (hμ₂ : μ₂ ≫ chartLimitMap B S hS D hL C L =
      limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l))
    (hμ₁' : μ₁ ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) =
      limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) ≫ stageChartPairFst B S hS D hD C l)
    (hμ₂' : μ₂ ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) =
      limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) ≫ stageChartPairSnd B S hS D hD C l)
    {T : AlgebraicSpaces B S hS} (a b : T ⟶ schemeSpace L.cone.pt)
    (t : T ⟶ limitSpace B S hS D hL) (ha : a ≫ chartLimitMap B S hS D hL C L = t)
    (hb : b ≫ chartLimitMap B S hS D hL C L = t) :
    ∃ (y : T ⟶ limitBaseChangeSpace B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l)) (ρ : T ⟶ stageChartPair B S hS D hD C l),
      ρ ≫ stageChartPairFst B S hS D hD C l =
          a ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) ∧
        ρ ≫ stageChartPairSnd B S hS D hD C l =
          b ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) ∧
        y ≫ limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) = t ∧
        y ≫ limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) = ρ ∧
        y ≫ μ₁ = a ∧ y ≫ μ₂ = b := by
  have hcm : ∀ (m : Over i) (x : T ⟶ schemeSpace L.cone.pt),
      (x ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone m)) ≫
        chartStageMap B S hS D hD U₀ f₀ C m =
      (x ≫ chartLimitMap B S hS D hL C L) ≫ limitSpaceProjection B S hS D hL hD m.left :=
    fun m x => by rw [Category.assoc, Category.assoc, chartLimitMap_comp]
  obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_lift_chartPair B S hS D hD C l
    (a ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l))
    (b ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l))
    (by
      rw [hcm, hcm]
      exact congrArg (· ≫ limitSpaceProjection B S hS D hL hD l.left) (ha.trans hb.symm))
  obtain ⟨y, hy₁, hy₂⟩ := exists_lift_limitBaseChangeSpace B S hS D hL hD C l t ρ
    (by
      change t ≫ limitSpaceProjection B S hS D hL hD l.left =
        ρ ≫ stageChartPairFst B S hS D hD C l ≫ chartStageMap B S hS D hD U₀ f₀ C l
      rw [← Category.assoc, hρ₁, hcm, ha])
  exact ⟨y, ρ, hρ₁, hρ₂, hy₁, hy₂,
    chartLimit_hom_ext B S hS D hL C L l (by rw [Category.assoc, hμ₁, hy₁, ha])
      (by rw [Category.assoc, hμ₁', ← Category.assoc, hy₂, hρ₁]),
    chartLimit_hom_ext B S hS D hL C L l (by rw [Category.assoc, hμ₂, hy₁, hb])
      (by rw [Category.assoc, hμ₂', ← Category.assoc, hy₂, hρ₂])⟩

/-- **The transition morphism at a stage, from its restriction to the limit.**  The restriction
`ψ` along a factorization `v₀` of the kernel pair of the chart of `m = overStageComp l j`
through the base change `X_j ×_{X_l} (U_l ×_{X_l} U_l)` of a morphism `Ψ₀` whose restriction to
the limit is the twisted comparison of `η` is a twisted transition morphism. -/
theorem isTwistedTransition_of_limit
    {P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1
      (limitSpace B S hS D hL).2}
    {G : Modules.{u, u} B S hS (schemeSpace (C.siteDiagram.obj l)).1
      (schemeSpace (C.siteDiagram.obj l)).2}
    (η : (modulePullback B S hS (chartLimitMap B S hS D hL C L)).obj P ≅
      (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l))).obj G)
    (μ₁ μ₂ : limitBaseChangeSpace B S hS D hL hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l) ⟶ schemeSpace L.cone.pt)
    (hμ₁ : μ₁ ≫ chartLimitMap B S hS D hL C L =
      limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l))
    (hμ₂ : μ₂ ≫ chartLimitMap B S hS D hL C L =
      limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l))
    (hμ₁' : μ₁ ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) =
      limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) ≫ stageChartPairFst B S hS D hD C l)
    (hμ₂' : μ₂ ≫ schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l) =
      limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
        (chartPairToStage B S hS D hD C l) ≫ stageChartPairSnd B S hS D hD C l)
    (j : Over l.left)
    (Ψ₀ : (modulePullback B S hS
        (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) j ≫ stageChartPairFst B S hS D hD C l)).obj G ⟶
      (modulePullback B S hS
        (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) j ≫ stageChartPairSnd B S hS D hD C l)).obj G)
    (hKR : moduleHomRestrict₂ G G
        (limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D l.left
          (chartPairToStage B S hS D hD C l).hom)
          (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l))
          (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l)) j)
        (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) j ≫ stageChartPairFst B S hS D hD C l)
        (stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) j ≫ stageChartPairSnd B S hS D hD C l)
        ((limitBaseChangeSystemIso B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ limitBaseChangeSnd B S hS D hL hD
            (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l)) ≫
          stageChartPairFst B S hS D hD C l)
        ((limitBaseChangeSystemIso B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ limitBaseChangeSnd B S hS D hL hD
            (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l)) ≫
          stageChartPairSnd B S hS D hD C l)
        (by rw [← Category.assoc, ← limitBaseChangeSystemIso_comp_snd])
        (by rw [← Category.assoc, ← limitBaseChangeSystemIso_comp_snd]) Ψ₀ =
      moduleHomRestrict₂ G G (limitBaseChangeSystemIso B S hS D hL hD
          (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l))
        (limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ stageChartPairFst B S hS D hD C l)
        (limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ stageChartPairSnd B S hS D hD C l)
        ((limitBaseChangeSystemIso B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ limitBaseChangeSnd B S hS D hL hD
            (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l)) ≫
          stageChartPairFst B S hS D hD C l)
        ((limitBaseChangeSystemIso B S hS D hL hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l) ≫ limitBaseChangeSnd B S hS D hL hD
            (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l)) ≫
          stageChartPairSnd B S hS D hD C l)
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
        (twistedComparison (chartLimitMap B S hS D hL C L)
          (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l)) η μ₁ μ₂
          (limitBaseChangeFst B S hS D hL hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l))
          _ _ hμ₁ hμ₂ hμ₁' hμ₂'))
    (v₀ : stageChartPair B S hS D hD C (overStageComp l j) ⟶
      stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D l.left
          (chartPairToStage B S hS D hD C l).hom)
        (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (stageChartPair B S hS D hD C l)
          (chartPairToStage B S hS D hD C l)) j)
    (hv₁ : v₀ ≫ pairStageProj B S hS D hD C l (stageChartPairFst B S hS D hD C l) rfl j =
      stageChartPairFst B S hS D hD C (overStageComp l j))
    (hv₂ : v₀ ≫ pairStageProj B S hS D hD C l (stageChartPairSnd B S hS D hD C l)
        (by rw [← chartPair_condition]; rfl) j =
          stageChartPairSnd B S hS D hD C (overStageComp l j)) :
    IsTwistedTransition (chartLimitMap B S hS D hL C L)
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l)) η
      (stageChartPairFst B S hS D hD C (overStageComp l j))
      (stageChartPairSnd B S hS D hD C (overStageComp l j))
      (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp l j)))
      (schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
      (schemeSpaceMap_π_comp B S hS C.siteDiagram L.cone (overCompHom l j))
      (moduleHomRestrict₂ G G v₀ _ _ (stageChartPairFst B S hS D hD C (overStageComp l j) ≫
          schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
        (stageChartPairSnd B S hS D hD C (overStageComp l j) ≫
          schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
        (by rw [← pairStageProj_comp_transition B S hS D hD C l _ rfl j, ← Category.assoc, hv₁])
        (by rw [← pairStageProj_comp_transition B S hS D hD C l (stageChartPairSnd B S hS D hD C l)
          (chartPair_condition B S hS D hD C l).symm j, ← Category.assoc, hv₂])
        Ψ₀) := by
  intro T a b t ha hb w hw₁ hw₂ va vb hva hvb
  have hcl := schemeSpaceMap_π_comp B S hS C.siteDiagram L.cone (overCompHom l j)
  rw [moduleHomRestrict₂_moduleHomRestrict₂ v₀ w (w ≫ v₀) rfl]
  obtain ⟨y, ρ, hρ₁, hρ₂, hy₁, hy₂, hya, hyb⟩ :=
    exists_lift_limitBaseChangeSpace_of_chartLimitMap B S hS D hL hD C L l μ₁ μ₂ hμ₁ hμ₂ hμ₁' hμ₂'
      a b t ha hb
  have hwρ : (w ≫ v₀) ≫ stageBaseChangeSpaceSnd B S hS D hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l) j = ρ := by
    apply chartPair_hom_ext B S hS D hD C l
    · simp only [Category.assoc]
      rw [← pairStageProj_comp_transition B S hS D hD C l _ rfl j, ← Category.assoc v₀, hv₁,
        ← Category.assoc, hw₁, Category.assoc, hcl, hρ₁]
    · simp only [Category.assoc]
      rw [← pairStageProj_comp_transition B S hS D hD C l (stageChartPairSnd B S hS D hD C l)
        (chartPair_condition B S hS D hD C l).symm j, ← Category.assoc v₀, hv₂, ← Category.assoc,
        hw₂, Category.assoc, hcl, hρ₂]
  let θ := limitBaseChangeSystemIso B S hS D hL hD (stageChartPair B S hS D hD C l)
    (chartPairToStage B S hS D hD C l)
  let sτ := y ≫ limitBaseChangeSystemIsoInv B S hS D hL hD
    (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l)
  have hs₁ : sτ ≫ θ = y := by
    simp only [sτ, θ, Category.assoc, limitBaseChangeSystemIsoInv_comp, Category.comp_id]
  have hs₂ : sτ ≫ limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D l.left
          (chartPairToStage B S hS D hD C l).hom)
          (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l))
          (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD (stageChartPair B S hS D hD C l)
            (chartPairToStage B S hS D hD C l)) j = w ≫ v₀ := by
    apply stageBaseChange_hom_ext B S hS D hD l
    · rw [Category.assoc, ← limitBaseChangeSystemIso_comp_fst B S hS D hL hD
        (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l) j, ← Category.assoc,
        hs₁, ← Category.assoc, hy₁, Category.assoc,
        ← pairStageProj_comp_chartStageMap B S hS D hD C l _ rfl j,
        ← Category.assoc v₀, hv₁, ← Category.assoc, hw₁]
      rw [Category.assoc, ← chartLimitMap_comp B S hS D hL hD C L, ← Category.assoc, ha]
      rfl
    · rw [Category.assoc, ← limitBaseChangeSystemIso_comp_snd B S hS D hL hD
        (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l) j, ← Category.assoc,
        hs₁, hy₂, hwρ]
  have hzva : y ≫ limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l) ≫ stageChartPairFst B S hS D hD C l = va := by
    rw [← Category.assoc, hy₂, hρ₁, hva]
  have hzvb : y ≫ limitBaseChangeSnd B S hS D hL hD (stageChartPair B S hS D hD C l)
      (chartPairToStage B S hS D hD C l) ≫ stageChartPairSnd B S hS D hD C l = vb := by
    rw [← Category.assoc, hy₂, hρ₂, hvb]
  exact (moduleHomRestrict₂_eq_of_factor _ θ _ _ _ _ _ _ _ _ (Category.assoc _ _ _).symm
    (Category.assoc _ _ _).symm Ψ₀ _ hKR (w ≫ v₀) y sτ hs₂ hs₁ va vb _ _ hzva hzvb).trans
    (moduleHomRestrict₂_twistedComparison _ _ η y μ₁ μ₂ _ _ _ hμ₁ hμ₂ hμ₁' hμ₂' a b t va vb hya
      hyb hy₁ hzva hzvb ha hb hva hvb)

/-- **The transition morphism at a stage exists.**  For a finitely presented module `G` on the
chart `U_l` of a stage and an identification `η : ell^*P ≅ π_l^*G`, there are a later stage
`m = overStageComp l j` and a twisted transition morphism on the kernel pair of its chart. -/
theorem exists_isTwistedTransition (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    {P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1
      (limitSpace B S hS D hL).2}
    {G : Modules.{u, u} B S hS (schemeSpace (C.siteDiagram.obj l)).1
      (schemeSpace (C.siteDiagram.obj l)).2} (hG : G.IsFinitePresentationOnSite)
    (η : (modulePullback B S hS (chartLimitMap B S hS D hL C L)).obj P ≅
      (modulePullback B S hS (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l))).obj G) :
    ∃ (j : Over l.left)
      (ψ : (modulePullback B S hS (stageChartPairFst B S hS D hD C (overStageComp l j) ≫
          schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))).obj G ⟶
        (modulePullback B S hS (stageChartPairSnd B S hS D hD C (overStageComp l j) ≫
          schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))).obj G),
      IsTwistedTransition (chartLimitMap B S hS D hL C L)
        (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l)) η
        (stageChartPairFst B S hS D hD C (overStageComp l j))
        (stageChartPairSnd B S hS D hD C (overStageComp l j))
        (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone (overStageComp l j)))
        (schemeSpaceMap (C.siteDiagram.map (overCompHom l j)))
        (schemeSpaceMap_π_comp B S hS C.siteDiagram L.cone (overCompHom l j)) ψ := by
  obtain ⟨μ₁, hμ₁, hμ₁'⟩ := exists_limit_factor B S hS D hL hD C l
    (stageChartPairFst B S hS D hD C l) rfl L
  obtain ⟨μ₂, hμ₂, hμ₂'⟩ := exists_limit_factor B S hS D hL hD C l
    (stageChartPairSnd B S hS D hD C l) (chartPair_condition B S hS D hD C l).symm L
  have hUqc : IsQuasiCompactSpace B S hS (schemeSpace (C.siteDiagram.obj l)).1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (C.isAffine_obj l)
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (schemeSpace (C.siteDiagram.obj l)).1 := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj l)) := C.isAffine_obj l
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
      ⟨C.siteDiagram.obj l, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩
  have hRqc := isQuasiCompactSpace_pullback_self B S hS hZ
    (chartStageMap B S hS D hD U₀ f₀ C l) hUqc (hQs l.left)
  have hRqs : IsAbsolutelyQuasiSeparated B S hS hZ (stageChartPair B S hS D hD C l).1 :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ _ _ (schemeSpace (C.siteDiagram.obj l)).2
      (schemeSpace (C.siteDiagram.obj l)).2 (hD l.left) hUqs hUqs
  obtain ⟨j, ψ₀, hψ₀⟩ := exists_homRestrict_eq_of_baseChange B S hS hZ D hL hD
    (stageChartPair B S hS D hD C l) (chartPairToStage B S hS D hD C l) hQc hQs hRqc hRqs
    (isFinitePresentationOnSite_modulePullback B S hS (stageChartPairFst B S hS D hD C l) G hG)
    (isFinitePresentationOnSite_modulePullback B S hS (stageChartPairSnd B S hS D hD C l) G hG)
    (homConjL _ _ (stageChartPairFst B S hS D hD C l) (stageChartPairSnd B S hS D hD C l)
      (twistedComparison (chartLimitMap B S hS D hL C L)
        (schemeSpaceMap (coneLeg B S hS C.siteDiagram L.cone l)) η μ₁ μ₂ _ _ _ hμ₁ hμ₂ hμ₁' hμ₂'))
  obtain ⟨v₀, hv₁, hv₂⟩ := exists_factor_pairStageProj B S hS D hD C l j
    (stageChartPair B S hS D hD C (overStageComp l j))
    (stageChartPairFst B S hS D hD C (overStageComp l j))
    (stageChartPairSnd B S hS D hD C (overStageComp l j))
    (chartPair_condition B S hS D hD C (overStageComp l j))
  exact ⟨j, _, isTwistedTransition_of_limit B S hS D hL hD C L l η μ₁ μ₂ hμ₁
    hμ₂ hμ₁' hμ₂' j _ (moduleHomRestrict₂_homConjLInv_eq B S hS _ _ _ _ _ _ _ ψ₀ _ hψ₀) v₀ hv₁ hv₂⟩

end Pair

end AlgebraicGeometry.Space

end
