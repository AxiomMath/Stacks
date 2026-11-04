module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexPushforward

/-!
# Gluing morphisms of relative dualizing complexes of algebraic spaces

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation and let
`(ω₁, τ₁)`, `(ω₂, τ₂)` be relative dualizing complexes (Stacks 0E5X). Over every affine `Y'`
étale over `Y` there is a unique morphism of the base changed pairs. Granted that
`R𝓗om(ω₁, ω₂)` lies in `D^{≥ 0}`, these local morphisms glue along the étale charts of `X` to a
morphism `ω₁ ⟶ ω₂` restricting to each of them; it is compatible with the traces as soon as
`Rf_* ω₁` lies in `D^{≤ 0}`. With both halves of Stacks 0E5Y for `ω₁` and `ω₂` this gives the
unique isomorphism of pairs of Stacks 0E5Z.

## Main results

* `AlgebraicGeometry.Space.RelativeDualizingComplex.conj_eq_of_baseChange_hom`: two local
  morphisms of pairs agree on any space étale over `X` mapping to both base changes.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.exists_hom_baseChange_hom`.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.eq_of_hom`.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.existsUnique_iso_of_isIso_homothety`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

namespace RelativeDualizingComplex

section Aux

variable {C D : Type*} [Category* C] [Category* D]

/-- Equal morphisms have equal conjugates of their images, in an arbitrary category. -/
theorem conj_map_congr_aux (F : C ⥤ D) {P Q : C} {P' Q' : D} (a : P' ⟶ F.obj P)
    (b : F.obj Q ⟶ Q') {x y : P ⟶ Q} (h : x = y) : a ≫ F.map x ≫ b = a ≫ F.map y ≫ b := by
  rw [h]

/-- Rewriting the morphism in a trace condition, in an arbitrary category. -/
theorem map_comp_eq_of_eq_aux (F : C ⥤ D) {P Q : C} {U : D} {x y : P ⟶ Q} (h : x = y)
    {t : F.obj Q ⟶ U} {s : F.obj P ⟶ U} (hy : F.map y ≫ t = s) : F.map x ≫ t = s := by
  rw [h]
  exact hy

/-- The trace condition for a composite, in an arbitrary category. -/
theorem map_comp_trace_aux (F : C ⥤ D) {P Q : C} {U : D} {d : P ⟶ Q} {d' : Q ⟶ P}
    {t₁ : F.obj P ⟶ U} {t₂ : F.obj Q ⟶ U} (h : F.map d ≫ t₂ = t₁) (h' : F.map d' ≫ t₁ = t₂) :
    F.map (d ≫ d') ≫ t₁ = t₁ := by
  rw [Functor.map_comp, Category.assoc, h', h]

/-- The trace condition for an identity, in an arbitrary category. -/
theorem map_id_trace_aux (F : C ⥤ D) {P : C} {U : D} (t : F.obj P ⟶ U) :
    F.map (𝟙 P) ≫ t = t := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end Aux

/-- The conjugate of a derived pullback of a morphism of pairs, restricted along `r`, only depends
on a factorisation `r ≫ ρ = w ≫ l` of the restriction of `ρ`. -/
private theorem conj_pullback_map_eq_of_fac {Z' Z W X' X : AlgebraicSpaces B S hS}
    {r : Z' ⟶ Z} {ρ : Z ⟶ X'} {g' : X' ⟶ X} {u : Z ⟶ X} (hρ : ρ ≫ g' = u)
    {w : Z' ⟶ W} {l : W ⟶ X'} {v : W ⟶ X} (hl : l ≫ g' = v) {u' : Z' ⟶ X} (hwv : w ≫ v = u')
    (hr : r ≫ ρ = w ≫ l) (hu : r ≫ u = u')
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g').obj L) :
    (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hu).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS r).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS ρ g' ≪≫
              smallEtaleDerivedModulePullbackCongr B S hS hρ).inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS ρ).map φ ≫
              (smallEtaleDerivedModulePullbackCompIso B S hS ρ g' ≪≫
                smallEtaleDerivedModulePullbackCongr B S hS hρ).hom.app L) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hu).hom.app L =
      (smallEtaleDerivedModulePullbackCompIso B S hS w v ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hwv).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS w).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS l g' ≪≫
              smallEtaleDerivedModulePullbackCongr B S hS hl).inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS l).map φ ≫
              (smallEtaleDerivedModulePullbackCompIso B S hS l g' ≪≫
                smallEtaleDerivedModulePullbackCongr B S hS hl).hom.app L) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS w v ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hwv).hom.app L := by
  have h : (r ≫ ρ) ≫ g' = u' := by rw [Category.assoc, hρ, hu]
  have h' : (w ≫ l) ≫ g' = u' := by rw [Category.assoc, hl, hwv]
  exact (compIso_congr_conj_conj r ρ g' hρ hu h φ).trans
    ((compIso_congr_conj_eq_of_eq hr g' h h' φ).trans
    (compIso_congr_conj_conj w l g' hl hwv h' φ).symm)

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {hf : IsProper B S hS f.hom}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}
  (D₁ D₂ : RelativeDualizingComplex hZ f hf hfl hfp)

/-- **Local morphisms of pairs agree.** Let `u : Z ⟶ X` be étale and let `ρ_j : Z ⟶ X_j` factor
`u` through two base changes `X_j = X ×_Y Y_j` to affine `Y_j`. If `R𝓗om(ω₁, ω₂)` lies in
`D^{≥ 0}`, then the derived pullbacks to `Z` of morphisms of pairs over `X₁` and over `X₂` agree:
locally on `Z` both factor through a base change to an affine chart of `Y₁ ×_Y Y₂`, over which
the morphism of pairs is unique. -/
theorem conj_eq_of_baseChange_hom
    (hKL : (((smallEtaleDerivedSheafHom B S hS X).obj (op D₁.ω)).obj D₂.ω).IsGE 0)
    {Z : AlgebraicSpaces B S hS} (u : Z ⟶ X) (hu : IsEtale B S hS u.hom)
    {X₁ Y₁ : AlgebraicSpaces B S hS} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Y} {g'₁ : X₁ ⟶ X}
    (sq₁ : IsPullback g'₁ f₁ f g₁) (ρ₁ : Z ⟶ X₁) (h₁ : ρ₁ ≫ g'₁ = u)
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g'₁).obj D₁.ω ⟶
      (smallEtaleDerivedModulePullback B S hS g'₁).obj D₂.ω)
    (hφ₁ : (derivedModulePushforward B S hS f₁).map φ₁ ≫ D₂.baseChangeTrace sq₁ =
      D₁.baseChangeTrace sq₁)
    {X₂ Y₂ : AlgebraicSpaces B S hS} {f₂ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ Y} {g'₂ : X₂ ⟶ X}
    (sq₂ : IsPullback g'₂ f₂ f g₂) (ρ₂ : Z ⟶ X₂) (h₂ : ρ₂ ≫ g'₂ = u)
    (φ₂ : (smallEtaleDerivedModulePullback B S hS g'₂).obj D₁.ω ⟶
      (smallEtaleDerivedModulePullback B S hS g'₂).obj D₂.ω)
    (hφ₂ : (derivedModulePushforward B S hS f₂).map φ₂ ≫ D₂.baseChangeTrace sq₂ =
      D₁.baseChangeTrace sq₂) :
    (smallEtaleDerivedModulePullbackCompIso B S hS ρ₁ g'₁ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS h₁).inv.app D₁.ω ≫
        (smallEtaleDerivedModulePullback B S hS ρ₁).map φ₁ ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS ρ₁ g'₁ ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS h₁).hom.app D₂.ω =
      (smallEtaleDerivedModulePullbackCompIso B S hS ρ₂ g'₂ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS h₂).inv.app D₁.ω ≫
        (smallEtaleDerivedModulePullback B S hS ρ₂).map φ₂ ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS ρ₂ g'₂ ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS h₂).hom.app D₂.ω := by
  have hZ' := isGE_smallEtaleDerivedSheafHom_pullback_of_isEtale B S hS u hu D₁.ω D₂.ω 0 hKL
  have hπ : (ρ₁ ≫ f₁) ≫ g₁ = (ρ₂ ≫ f₂) ≫ g₂ := by
    rw [Category.assoc, ← sq₁.w, ← Category.assoc, h₁, Category.assoc, ← sq₂.w,
      ← Category.assoc, h₂]
  refine eq_of_smallEtaleDerivedModulePullback_map_eq B S hS hZ'
    (coversTop_affineChartDiagramCharts B S hS (pullback.lift _ _ hπ)) fun i => ?_
  obtain ⟨-, W', q, hq, hW'⟩ := i.2
  have hW : IsAffineSpace B S hS (chartSpace B S hS (pullback g₁ g₂) W').1 :=
    isAffineSpace_chartSpace B S hS _ W' hW'
  have hfac : chartToSpace B S hS Z i.1 ≫ pullback.lift _ _ hπ =
      chartSpaceMapOver B S hS q ≫ chartToSpace B S hS (pullback g₁ g₂) W' :=
    (chartSpaceMapOver_comp_chartToSpace B S hS _ q hq).symm
  have hfac₁ : chartToSpace B S hS Z i.1 ≫ ρ₁ ≫ f₁ = chartSpaceMapOver B S hS q ≫
      chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂ := by
    simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst g₁ g₂) hfac
  have hfac₂ : chartToSpace B S hS Z i.1 ≫ ρ₂ ≫ f₂ = chartSpaceMapOver B S hS q ≫
      chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.snd g₁ g₂ := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd g₁ g₂) hfac
  have hψ : (chartToSpace B S hS Z i.1 ≫ u) ≫ f = chartSpaceMapOver B S hS q ≫
      chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂ ≫ g₁ := by
    calc (chartToSpace B S hS Z i.1 ≫ u) ≫ f =
          chartToSpace B S hS Z i.1 ≫ ρ₁ ≫ g'₁ ≫ f := by rw [← h₁]; simp only [Category.assoc]
      _ = (chartToSpace B S hS Z i.1 ≫ ρ₁ ≫ f₁) ≫ g₁ := by
          rw [sq₁.w]; simp only [Category.assoc]
      _ = _ := by rw [hfac₁]; simp only [Category.assoc]
  have sqW := IsPullback.of_hasPullback f
    (chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂ ≫ g₁)
  have hcond₁ : pullback.fst f (chartToSpace B S hS (pullback g₁ g₂) W' ≫
      pullback.fst g₁ g₂ ≫ g₁) ≫ f = (pullback.snd f _ ≫
        chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂) ≫ g₁ :=
    pullback.condition.trans (by simp only [Category.assoc])
  have hcond₂ : pullback.fst f (chartToSpace B S hS (pullback g₁ g₂) W' ≫
      pullback.fst g₁ g₂ ≫ g₁) ≫ f = (pullback.snd f _ ≫
        chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.snd g₁ g₂) ≫ g₂ := by
    have hc : chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂ ≫ g₁ =
        chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.snd g₁ g₂ ≫ g₂ := by
      rw [pullback.condition (f := g₁) (g := g₂)]
    exact pullback.condition.trans ((whisker_eq _ hc).trans (by simp only [Category.assoc]))
  have hn₂ : (chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.snd g₁ g₂) ≫ g₂ =
      chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂ ≫ g₁ := by
    rw [Category.assoc, pullback.condition]
  have hB₁ := RelativeDualizingPair.baseChange_hom_of_isPullback D₁.toRelativeDualizingPair
    D₂.toRelativeDualizingPair sq₁ sqW (sq₁.lift _ _ hcond₁)
    (chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂) (sq₁.lift_fst _ _ _)
    (Category.assoc _ _ _) (sq₁.lift_snd _ _ _) φ₁ hφ₁
  have hB₂ := RelativeDualizingPair.baseChange_hom_of_isPullback D₁.toRelativeDualizingPair
    D₂.toRelativeDualizingPair sq₂ sqW (sq₂.lift _ _ hcond₂)
    (chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.snd g₁ g₂) (sq₂.lift_fst _ _ _)
    hn₂ (sq₂.lift_snd _ _ _) φ₂ hφ₂
  have heq := (RelativeDualizingPair.existsUnique_baseChange_hom D₁.toRelativeDualizingPair
    D₂.toRelativeDualizingPair sqW hW (D₁.isAffineBaseChangePair _ _ _ sqW hW)
    (D₂.isAffineBaseChangePair _ _ _ sqW hW)).unique hB₁ hB₂
  have hψf : pullback.lift _ _ hψ ≫ pullback.fst f
      (chartToSpace B S hS (pullback g₁ g₂) W' ≫ pullback.fst g₁ g₂ ≫ g₁) =
        chartToSpace B S hS Z i.1 ≫ u := pullback.lift_fst _ _ _
  have hr₁ : chartToSpace B S hS Z i.1 ≫ ρ₁ = pullback.lift _ _ hψ ≫ sq₁.lift _ _ hcond₁ := by
    refine sq₁.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h₁, sq₁.lift_fst, hψf]
    · rw [Category.assoc, Category.assoc, sq₁.lift_snd, pullback.lift_snd_assoc, hfac₁]
  have hr₂ : chartToSpace B S hS Z i.1 ≫ ρ₂ = pullback.lift _ _ hψ ≫ sq₂.lift _ _ hcond₂ := by
    refine sq₂.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h₂, sq₂.lift_fst, hψf]
    · rw [Category.assoc, Category.assoc, sq₂.lift_snd, pullback.lift_snd_assoc, hfac₂]
  refine eq_of_conj_eq ((smallEtaleDerivedModulePullbackCompIso B S hS
      (chartToSpace B S hS Z i.1) u ≪≫ smallEtaleDerivedModulePullbackCongr B S hS
        (rfl : chartToSpace B S hS Z i.1 ≫ u = _)).app D₁.ω)
    ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS Z i.1) u ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS
        (rfl : chartToSpace B S hS Z i.1 ≫ u = _)).app D₂.ω) ?_
  exact (conj_pullback_map_eq_of_fac h₁ (sq₁.lift_fst _ _ hcond₁) hψf hr₁ rfl φ₁).trans
    ((conj_map_congr_aux _ _ _ heq).trans
    (conj_pullback_map_eq_of_fac h₂ (sq₂.lift_fst _ _ hcond₂) hψf hr₂ rfl φ₂).symm)

/-- **Gluing the local morphisms of pairs.** If `R𝓗om(ω₁, ω₂)` lies in `D^{≥ 0}`, there is a
morphism `d : ω₁ ⟶ ω₂` whose base change to `X ×_Y V` is the morphism of pairs, for every affine
étale chart `V` of `Y`. -/
theorem exists_hom_baseChange_hom
    (hKL : (((smallEtaleDerivedSheafHom B S hS X).obj (op D₁.ω)).obj D₂.ω).IsGE 0) :
    ∃ d : D₁.ω ⟶ D₂.ω, ∀ V : {U : SmallEtale B S hS Y.1 //
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj U))},
      (derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V.1))).map
          ((smallEtaleDerivedModulePullback B S hS
            (pullback.fst f (chartToSpace B S hS Y V.1))).map d) ≫
        D₂.baseChangeTrace (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)) =
      D₁.baseChangeTrace (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)) := by
  have hι : ∀ V : {U : SmallEtale B S hS Y.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj U))},
      ∃ φ : (smallEtaleDerivedModulePullback B S hS
          (pullback.fst f (chartToSpace B S hS Y V.1))).obj D₁.ω ⟶
        (smallEtaleDerivedModulePullback B S hS
          (pullback.fst f (chartToSpace B S hS Y V.1))).obj D₂.ω,
        (derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V.1))).map φ ≫
          D₂.baseChangeTrace (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)) =
        D₁.baseChangeTrace (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)) := fun V =>
    (RelativeDualizingPair.existsUnique_baseChange_hom D₁.toRelativeDualizingPair
      D₂.toRelativeDualizingPair (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1))
      (isAffineSpace_chartSpace B S hS Y V.1 V.2) (D₁.isAffineBaseChangePair _ _ _ _ _)
      (D₂.isAffineBaseChangePair _ _ _ _ _)).exists
  choose ιV hιV using hι
  have hd : ∀ i : {W : SmallEtale B S hS X.1 // HasAffineChartDiagram B S hS f W},
      ∃ (V : {U : SmallEtale B S hS Y.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS Y.1).obj U))})
        (ψ : chartSpace B S hS X (affineChartDiagramCharts B S hS f i) ⟶
          pullback f (chartToSpace B S hS Y V.1)),
        ψ ≫ pullback.fst f (chartToSpace B S hS Y V.1) =
          chartToSpace B S hS X (affineChartDiagramCharts B S hS f i) := by
    intro i
    obtain ⟨-, V, q, hq, hV⟩ := i.2
    exact ⟨⟨V, hV⟩, pullback.lift _ _ (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm,
      pullback.lift_fst _ _ _⟩
  choose Vi ψ hψ using hd
  obtain ⟨d, hdi, -⟩ := existsUnique_smallEtaleDerivedModulePullback_map_eq B S hS hKL
    (coversTop_affineChartDiagramCharts B S hS f)
    (fun i => (smallEtaleDerivedModulePullbackCompIso B S hS (ψ i) _ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS (hψ i)).inv.app D₁.ω ≫
        (smallEtaleDerivedModulePullback B S hS (ψ i)).map (ιV (Vi i)) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS (ψ i) _ ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS (hψ i)).hom.app D₂.ω)
    (fun C i j c c' => by
      have h : (chartMap B S hS X c ≫ ψ i) ≫ pullback.fst f (chartToSpace B S hS Y (Vi i).1) =
          chartToSpace B S hS X C :=
        (Category.assoc _ _ _).trans ((whisker_eq _ (hψ i)).trans
          (chartMap_comp_chartToSpace B S hS X c))
      have h' : (chartMap B S hS X c' ≫ ψ j) ≫ pullback.fst f (chartToSpace B S hS Y (Vi j).1) =
          chartToSpace B S hS X C :=
        (Category.assoc _ _ _).trans ((whisker_eq _ (hψ j)).trans
          (chartMap_comp_chartToSpace B S hS X c'))
      rw [chartDerivedPullbackIso_eq, chartDerivedPullbackIso_eq]
      exact (compIso_congr_conj_conj (chartMap B S hS X c) (ψ i) _ (hψ i)
        (chartMap_comp_chartToSpace B S hS X c) h (ιV (Vi i))).trans
        ((conj_eq_of_baseChange_hom D₁ D₂ hKL (chartToSpace B S hS X C)
          (isEtale_chartToSpace B S hS X C)
          (IsPullback.of_hasPullback f (chartToSpace B S hS Y (Vi i).1))
          (chartMap B S hS X c ≫ ψ i) h (ιV (Vi i)) (hιV (Vi i))
          (IsPullback.of_hasPullback f (chartToSpace B S hS Y (Vi j).1))
          (chartMap B S hS X c' ≫ ψ j) h' (ιV (Vi j)) (hιV (Vi j))).trans
          (compIso_congr_conj_conj (chartMap B S hS X c') (ψ j) _ (hψ j)
            (chartMap_comp_chartToSpace B S hS X c') h' (ιV (Vi j))).symm))
  refine ⟨d, fun V => map_comp_eq_of_eq_aux _ ?_ (hιV V)⟩
  have hfst : IsEtale B S hS (pullback.fst f (chartToSpace B S hS Y V.1)).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback f _).flip
      (isEtale_chartToSpace B S hS Y V.1)
  have hXV := isGE_smallEtaleDerivedSheafHom_pullback_of_isEtale B S hS _ hfst D₁.ω D₂.ω 0 hKL
  refine eq_of_smallEtaleDerivedModulePullback_map_eq B S hS hXV
    (coversTop_affineChartDiagramCharts B S hS
      (pullback.fst f (chartToSpace B S hS Y V.1) ≫ f)) fun E => ?_
  have hi₀ : HasAffineChartDiagram B S hS f ((smallEtalePostcomp B S hS _ hfst).obj E.1) := by
    obtain ⟨hA, V', q, hq, hV'⟩ := E.2
    exact ⟨hA, V', q, hq.trans (by rw [smallEtalePostcomp_obj_hom]; rfl), hV'⟩
  have hr : chartToSpace B S hS _ E.1 ≫ pullback.fst f (chartToSpace B S hS Y V.1) =
      chartToSpace B S hS X (affineChartDiagramCharts B S hS f ⟨_, hi₀⟩) := rfl
  refine eq_of_conj_eq ((smallEtaleDerivedModulePullbackCompIso B S hS
      (chartToSpace B S hS _ E.1) (pullback.fst f (chartToSpace B S hS Y V.1)) ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS hr).app D₁.ω)
    ((smallEtaleDerivedModulePullbackCompIso B S hS
      (chartToSpace B S hS _ E.1) (pullback.fst f (chartToSpace B S hS Y V.1)) ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS hr).app D₂.ω) ?_
  have e1 := compIso_congr_conj_map (chartToSpace B S hS _ E.1)
    (pullback.fst f (chartToSpace B S hS Y V.1)) hr d
  have e3 := conj_eq_of_baseChange_hom D₁ D₂ hKL
    (chartToSpace B S hS X (affineChartDiagramCharts B S hS f ⟨_, hi₀⟩))
    (isEtale_chartToSpace B S hS X _)
    (IsPullback.of_hasPullback f (chartToSpace B S hS Y (Vi ⟨_, hi₀⟩).1)) (ψ ⟨_, hi₀⟩)
    (hψ ⟨_, hi₀⟩) (ιV (Vi ⟨_, hi₀⟩)) (hιV (Vi ⟨_, hi₀⟩))
    (IsPullback.of_hasPullback f (chartToSpace B S hS Y V.1)) (chartToSpace B S hS _ E.1) hr
    (ιV V) (hιV V)
  exact e1.trans ((hdi ⟨_, hi₀⟩).trans e3)

/-- **Morphisms of pairs are unique** if `R𝓗om(ω₁, ω₂)` lies in `D^{≥ 0}`: their base changes to
the affine étale charts of `Y` are the unique morphisms of base changed pairs. -/
theorem eq_of_hom (hKL : (((smallEtaleDerivedSheafHom B S hS X).obj (op D₁.ω)).obj D₂.ω).IsGE 0)
    (d d' : D₁.ω ⟶ D₂.ω) (hd : (derivedModulePushforward B S hS f).map d ≫ D₂.τ = D₁.τ)
    (hd' : (derivedModulePushforward B S hS f).map d' ≫ D₂.τ = D₁.τ) : d = d' := by
  refine eq_of_smallEtaleDerivedModulePullback_map_eq B S hS hKL
    (coversTop_affineChartDiagramCharts B S hS f) fun i => ?_
  obtain ⟨-, V, q, hq, hV⟩ := i.2
  have sq := IsPullback.of_hasPullback f (chartToSpace B S hS Y V)
  have h := (RelativeDualizingPair.existsUnique_baseChange_hom D₁.toRelativeDualizingPair
    D₂.toRelativeDualizingPair (IsPullback.of_hasPullback f (chartToSpace B S hS Y V))
    (isAffineSpace_chartSpace B S hS Y V hV) (D₁.isAffineBaseChangePair _ _ _ _ _)
    (D₂.isAffineBaseChangePair _ _ _ _ _)).unique
    (RelativeDualizingPair.baseChange_hom D₁.toRelativeDualizingPair D₂.toRelativeDualizingPair
      sq d hd)
    (RelativeDualizingPair.baseChange_hom D₁.toRelativeDualizingPair D₂.toRelativeDualizingPair
      sq d' hd')
  have hψ : pullback.lift _ _ (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm ≫
      pullback.fst f (chartToSpace B S hS Y V) = chartToSpace B S hS X i.1 :=
    pullback.lift_fst _ _ _
  exact (compIso_congr_conj_map _ _ hψ d).symm.trans
    ((conj_map_congr_aux _ _ _ h).trans (compIso_congr_conj_map _ _ hψ d'))

/-- **Uniqueness of relative dualizing complexes, granted Stacks 0E5Y** (the argument of
Stacks 0E5Z). If `𝒪_X ⟶ R𝓗om(ω_j, ω_j)` is an isomorphism and `Rf_* ω_j` lies in `D^{≤ 0}` for
`j = 1, 2`, there is a unique isomorphism `e : ω₁ ≅ ω₂` with `τ₂ ∘ Rf_* e = τ₁`. -/
theorem existsUnique_iso_of_isIso_homothety
    (h₁ : IsIso (smallEtaleDerivedHomothety B S hS X D₁.ω))
    (h₂ : IsIso (smallEtaleDerivedHomothety B S hS X D₂.ω))
    (hle₁ : ((derivedModulePushforward B S hS f).obj D₁.ω).IsLE 0)
    (hle₂ : ((derivedModulePushforward B S hS f).obj D₂.ω).IsLE 0) :
    ∃! e : D₁.ω ≅ D₂.ω, (derivedModulePushforward B S hS f).map e.hom ≫ D₂.τ = D₁.τ := by
  obtain ⟨d, hd⟩ := exists_hom_baseChange_hom D₁ D₂ (isGE_smallEtaleDerivedSheafHom D₁ D₂ h₁)
  obtain ⟨d', hd'⟩ := exists_hom_baseChange_hom D₂ D₁ (isGE_smallEtaleDerivedSheafHom D₂ D₁ h₂)
  have t := RelativeDualizingPair.hom_of_forall_baseChange_hom D₁.toRelativeDualizingPair
    D₂.toRelativeDualizingPair hle₁ d hd
  have t' := RelativeDualizingPair.hom_of_forall_baseChange_hom D₂.toRelativeDualizingPair
    D₁.toRelativeDualizingPair hle₂ d' hd'
  refine ⟨⟨d, d', eq_of_hom D₁ D₁ (isGE_smallEtaleDerivedSheafHom D₁ D₁ h₁) _ _
      (map_comp_trace_aux _ t t') (map_id_trace_aux _ _),
    eq_of_hom D₂ D₂ (isGE_smallEtaleDerivedSheafHom D₂ D₂ h₂) _ _
      (map_comp_trace_aux _ t' t) (map_id_trace_aux _ _)⟩, t, fun e he => ?_⟩
  exact Iso.ext (eq_of_hom D₁ D₂ (isGE_smallEtaleDerivedSheafHom D₁ D₂ h₁) _ _ he t)

end RelativeDualizingComplex

end AlgebraicGeometry.Space

end
