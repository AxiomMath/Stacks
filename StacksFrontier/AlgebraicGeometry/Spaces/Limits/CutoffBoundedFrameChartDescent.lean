module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FrameChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFramedModuleDescent

/-!
# Trivializing charts of a module on a limit bounded by the cutoff come from a stage

Let `X = lim Xᵢ` be the limit of a cofiltered system bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no condition on the cofinality of the
cutoff, of quasi-compact quasi-separated algebraic spaces with affine transition morphisms, and
let `E` be an `𝒪_X`-module admitting frames locally on the small étale site of `X`. Then `E` is
the inverse image of a module on a stage with frames of the same sizes on a finite family of étale
charts covering that stage.

## Main results

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_stage_model_of_hasLocalFrames`: a module
  with local frames on the limit is the inverse image of a module with frames on finitely many
  étale charts covering a stage.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space.IsCutoffBoundedSystem

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hc : IsCutoffBoundedSystem B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-! ### Base change of a chart to a later stage, then to the limit -/

section Transition

variable {j j' : I} (g : j' ⟶ j) (T : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)

/-- On the base change to the limit of the base change of `T` to a later stage, the two
base-change projections followed by the structure morphism of `T` agree with the structure
morphism followed by the projection of the limit to the stage of `T`. -/
theorem limChartTransition_cond :
    yoneda.map (sbcProj (limitProjection B S hS D hc hD hAffine j')
        (rep_limitProjection B S hS D hc hD hAffine j')
        ((smallBaseChange B S hS (stageTransition B S hS D hD g)
          (rep_stageTransition B S hS D hD hAffine g)).obj T) ≫
      sbcProj (stageTransition B S hS D hD g) (rep_stageTransition B S hS D hD hAffine g) T) ≫
        T.obj.hom =
      ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j')
        (rep_limitProjection B S hS D hc hD hAffine j')).obj
        ((smallBaseChange B S hS (stageTransition B S hS D hD g)
          (rep_stageTransition B S hS D hD hAffine g)).obj T)).obj.hom ≫
        (limitProjection B S hS D hc hD hAffine j).hom := by
  rw [Functor.map_comp, Category.assoc, sbc_w, ← Category.assoc, sbc_w, Category.assoc]
  exact congrArg (_ ≫ ·) (limit.w D g)

/-- The comparison from the base change to the limit of the base change of `T` to a later stage,
to the base change of `T` to the limit. -/
def limChartTransition :
    (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j')
        (rep_limitProjection B S hS D hc hD hAffine j')).obj
        ((smallBaseChange B S hS (stageTransition B S hS D hD g)
          (rep_stageTransition B S hS D hD hAffine g)).obj T) ⟶
      (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j)
        (rep_limitProjection B S hS D hc hD hAffine j)).obj T :=
  sbcLift _ _ _ (limChartTransition_cond B S hS D hc hD hAffine g T)

end Transition

/-! ### The limit of the chart system as an étale chart of the limit -/

section ChartSystem

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
  (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

/-- The limit of the chart system, as an étale chart of the limit algebraic space. -/
def limitChart : SmallEtale B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1 :=
  ⟨CostructuredArrow.mk L.toLimit, presheaf_etale_toLimit L hf₀⟩

end ChartSystem

/-! ### Charts of a stage factoring through the chart system -/

section StageCharts

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
  (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

/-- **The base change to the limit of a chart of a stage maps to a neighbourhood it descends.**
If `A` is an étale chart of the limit over the limit `U` of the chart system, whose underlying
scheme is the base change along `U ⟶ Uₜ` of `X ⟶ Uₜ` (cartesian square `hpb`), then every chart
of the stage `t` given by a scheme `Z` mapping to `X` over `Uₜ` has base change to the limit
mapping to `A`. -/
theorem nonempty_limChart_stageChartOf_hom
    {A : SmallEtale B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1}
    (a : A ⟶ limitChart hc hD hAffine L hf₀) {t : Over i₀}
    {Z : BigFppfOver B S hS} (ν : Z ⟶ C.siteDiagram.obj t)
    (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)) {X : Scheme.{u}}
    (q : X ⟶ (BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj t))
    (ψ : (BigFppfOver.toScheme B S hS).obj A.1.left ⟶ X)
    (hpb : IsPullback ψ ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS _).map a)) q
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app t)))
    (κ : (BigFppfOver.toScheme B S hS).obj Z ⟶ X)
    (hκ : κ ≫ q = (BigFppfOver.toScheme B S hS).map ν) :
    Nonempty (limChart B S hS D hc hD hAffine (stageChartOf hD hf₀ ν hν) ⟶ A) := by
  let W := stageChartOf hD hf₀ ν hν
  let f := limitProjection B S hS D hc hD hAffine t.left
  let hf := rep_limitProjection B S hS D hc hD hAffine t.left
  let P := limChart B S hS D hc hD hAffine W
  have hw : P.1.hom ≫ limit.π D t.left =
      yoneda.map (sbcProj f hf W ≫ ν) ≫ C.stageMap t := by
    have e1 : yoneda.map (sbcProj f hf W) ≫ W.1.hom =
        yoneda.map (sbcProj f hf W) ≫ (yoneda.map ν ≫ C.stageMap t) := rfl
    exact (sbc_w f hf W).symm.trans (e1.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ C.stageMap t) (Functor.map_comp yoneda _ _).symm)))
  let μ : P.1.left ⟶ L.cone.pt :=
    yoneda.preimage ((L.isPullback_stage t).lift P.1.hom (yoneda.map (sbcProj f hf W ≫ ν)) hw)
  have hμ₁ : yoneda.map μ ≫ L.toLimit = P.1.hom := by
    rw [Functor.map_preimage]
    exact IsPullback.lift_fst _ _ _ _
  have hμ₂ : μ ≫ L.cone.π.app t = sbcProj f hf W ≫ ν := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact IsPullback.lift_snd _ _ _ _
  let p₁ := (BigFppfOver.toScheme B S hS).map (sbcProj f hf W) ≫ κ
  let p₂ := (BigFppfOver.toScheme B S hS).map μ
  have hcomp : p₁ ≫ q = p₂ ≫ (BigFppfOver.toScheme B S hS).map (L.cone.π.app t) :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ).trans
      ((Functor.map_comp _ _ _).symm.trans ((congrArg (BigFppfOver.toScheme B S hS).map
        hμ₂.symm).trans (Functor.map_comp _ _ _))))
  let m := hpb.lift p₁ p₂ hcomp
  have hm : m ≫ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map a) = p₂ :=
    hpb.lift_snd _ _ _
  let mS : P.1.left ⟶ A.1.left := Over.homMk (B.inclusion.preimage m) (by
    apply B.inclusion.map_injective
    calc B.inclusion.map (B.inclusion.preimage m ≫ A.1.left.hom)
        = m ≫ B.inclusion.map A.1.left.hom := by rw [Functor.map_comp, Functor.map_preimage]
      _ = m ≫ B.inclusion.map (a.hom.left.left ≫
            (limitChart hc hD hAffine L hf₀).1.left.hom) := by
          rw [Over.w a.hom.left]
      _ = (m ≫ B.inclusion.map a.hom.left.left) ≫
            B.inclusion.map (limitChart hc hD hAffine L hf₀).1.left.hom := by
          rw [Functor.map_comp, Category.assoc]
      _ = B.inclusion.map μ.left ≫
            B.inclusion.map (limitChart hc hD hAffine L hf₀).1.left.hom :=
          congrArg (· ≫ _) hm
      _ = B.inclusion.map P.1.left.hom :=
          (Functor.map_comp B.inclusion _ _).symm.trans (congrArg B.inclusion.map (Over.w μ)))
  have hmS : mS ≫ a.hom.left = μ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    change B.inclusion.map (B.inclusion.preimage m) ≫ _ = _
    rwa [Functor.map_preimage]
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk mS ?_)⟩
  rwa [← CostructuredArrow.w a.hom, ← Category.assoc, ← Functor.map_comp, hmS]

/-- **An affine étale chart over the limit of the chart system is dominated by the base change
of an affine étale chart of a stage**, factoring through the chart system, whose image at that
stage contains the image of a given point. -/
theorem exists_stage_chart
    {A : SmallEtale B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1}
    (a : A ⟶ limitChart hc hD hAffine L hf₀)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left))
    (w : (BigFppfOver.toScheme B S hS).obj A.1.left) :
    ∃ (t : Over i₀) (Z : BigFppfOver B S hS) (ν : Z ⟶ C.siteDiagram.obj t)
      (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      Nonempty (limChart B S hS D hc hD hAffine (stageChartOf hD hf₀ ν hν) ⟶ A) ∧
      (BigFppfOver.toScheme B S hS).map (L.cone.π.app t)
          ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map a) w) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map ν) := by
  have : ∀ {j k : Over i₀} (g : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom
      (C.schemeDiagram.map g) := fun g => C.isAffineHom_map g
  have : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  let α : (BigFppfOver.toScheme B S hS).obj A.1.left ⟶
      ((BigFppfOver.toScheme B S hS).mapCone L.cone).pt :=
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map a)
  have : Etale α := SmallEtale.etale_map B S hS _ a
  have : IsCofiltered (Over i₀) := inferInstance
  obtain ⟨t, X, q, ψ, hq, -, -, hpb⟩ := exists_isPullback_etale_of_etale C.schemeDiagram
    ((BigFppfOver.toScheme B S hS).mapCone L.cone) L.schemeIsLimit α
  let s₀ := (BigFppfOver.toScheme B S hS).map (L.cone.π.app t)
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map a) w)
  have hpt : q (ψ w) = s₀ := by
    have h := congrArg (fun g => g w) hpb.w
    simp only [Scheme.Hom.comp_apply] at h
    exact h
  let N : _root_.AlgebraicGeometry.EtaleNeighborhood ((BigFppfOver.toScheme B S hS).obj
      (C.siteDiagram.obj t)) s₀ :=
    { scheme := X, point := ψ w, toBase := q, etale_toBase := hq, map_point := hpt }
  obtain ⟨Zu, ν, κ, u', hZaff, -, hκ, hνet, -, hνu'⟩ :=
    exists_affine_siteObject_of_etaleNeighborhood B S hS (C.isAffine_obj t) N
  exact ⟨t, Zu, ν, hνet, hZaff,
    nonempty_limChart_stageChartOf_hom hc hD hAffine L hf₀ a ν hνet q ψ hpb κ hκ,
    u', hνu'⟩

end StageCharts

/-! ### Finitely many trivializing charts of the stages -/

section Finite

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
  (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

/-- **Finitely many affine étale charts of stages, factoring through the chart system, whose base
changes to the limit carry frames and whose images cover the limit of the chart system.** -/
theorem exists_finite_frame_stage_charts {P : ℕ → Prop}
    {E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2}
    (hE : HasLocalFrames P E) :
    ∃ (K : Type) (_ : Fintype K) (t : K → Over i₀) (Z : K → BigFppfOver B S hS)
      (ν : ∀ k, Z k ⟶ C.siteDiagram.obj (t k))
      (hν : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (ν k))),
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z k))) ∧
      (∀ k, ∃ n, P n ∧ ∃ e : Fin n → (sval E).obj (op (limChart B S hS D hc hD
        hAffine (stageChartOf hD hf₀ (ν k) (hν k)))), IsFrame (sval E) e) ∧
      ∀ u : (BigFppfOver.toScheme B S hS).obj L.cone.pt, ∃ k,
        (BigFppfOver.toScheme B S hS).map (L.cone.π.app (t k)) u ∈
          Set.range ((BigFppfOver.toScheme B S hS).map (ν k)) := by
  classical
  have hdata : ∀ u : (BigFppfOver.toScheme B S hS).obj L.cone.pt,
      ∃ (t : Over i₀) (Z : BigFppfOver B S hS) (ν : Z ⟶ C.siteDiagram.obj t)
        (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
        (∃ n, P n ∧ ∃ e : Fin n → (sval E).obj (op (limChart B S hS D hc hD
          hAffine (stageChartOf hD hf₀ ν hν))), IsFrame (sval E) e) ∧
        (BigFppfOver.toScheme B S hS).map (L.cone.π.app t) u ∈
          Set.range ((BigFppfOver.toScheme B S hS).map ν) := by
    intro u
    obtain ⟨A, a, w, hA, hw, n, hn, e, he⟩ :=
      exists_affine_frame_chart hE (limitChart hc hD hAffine L hf₀) u
    obtain ⟨t, Z, ν, hν, hZ, ⟨φ⟩, hr⟩ := exists_stage_chart hc hD hAffine L hf₀ a hA w
    exact ⟨t, Z, ν, hν, hZ, ⟨n, hn, _, he.restrict φ⟩, hw ▸ hr⟩
  choose t Z ν hν hZ hfr hr using hdata
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := L.isAffine_pt
  let O : (BigFppfOver.toScheme B S hS).obj L.cone.pt →
      Set ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := fun u =>
    (BigFppfOver.toScheme B S hS).map (L.cone.π.app (t u)) ⁻¹'
      Set.range ((BigFppfOver.toScheme B S hS).map (ν u))
  have hO : ∀ u, IsOpen (O u) := fun u => by
    have : Etale ((BigFppfOver.toScheme B S hS).map (ν u)) := hν u
    exact ((BigFppfOver.toScheme B S hS).map (ν u)).isOpenMap.isOpen_range.preimage
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app (t u))).continuous
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun u _ => Set.mem_iUnion.2 ⟨u, hr u⟩)
  let σ := F.equivFin.symm
  refine ⟨Fin F.card, inferInstance, fun k => t (σ k).1, fun k => Z (σ k).1, fun k => ν (σ k).1,
    fun k => hν (σ k).1, fun k => hZ (σ k).1, fun k => hfr (σ k).1, fun u => ?_⟩
  obtain ⟨k, hk, hu⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ u))
  obtain ⟨k', hk'⟩ := σ.surjective ⟨k, hk⟩
  exact ⟨k', by beta_reduce; rwa [hk']⟩

end Finite

/-! ### The descent of a module with local frames -/

section Descent

attribute [local instance] pointTopology

variable {B S hS D} (hZ : B.Contains (⊤_ Scheme.{u}))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hZ hQc hQs in
/-- **A module with local frames on the limit is the inverse image of a module with frames, of
the same sizes, on a finite family of étale charts covering a stage.** -/
theorem exists_stage_model_of_hasLocalFrames {P : ℕ → Prop}
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2)
    (hE : HasLocalFrames P E) :
    ∃ (i : I) (M : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2) (K : Type) (_ : Fintype K)
      (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD i).1) (n : K → ℕ),
      (∀ k, P (n k)) ∧ PointsCover W ∧
      (∀ k, ∃ e : Fin (n k) → (sval M).obj (op (W k)), IsFrame (sval M) e) ∧
      Nonempty (E ≅ (modulePullback B S hS
        (limitProjection B S hS D hc hD hAffine i)).obj M) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : CompactSpace (points B S hS (D.obj i₀)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ (hD i₀)).mp (hQc i₀)
  obtain ⟨Z₀, c, hZ₀, hcet, hcov⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS (D.obj i₀) (hD i₀) isCompact_univ
  let U₀ : BigAffineFppf B S hS := ⟨Z₀, hZ₀⟩
  let f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀ := c
  let C := affineChartSystem B S hS i₀ D U₀ f₀ hAffine
  obtain ⟨hSize, ⟨μ, hμ, hHomSize⟩, hB⟩ := id hc
  let L := C.limitBridgeOfBaseChangeSizeBounded hSize hμ hHomSize hB
  obtain ⟨K, _, t, Z, ν, hν, hZaff, hfr, hcover⟩ :=
    exists_finite_frame_stage_charts hc hD hAffine L hcet hE
  obtain ⟨s', g, hcov'⟩ := exists_stage_cover_of_finite L ν hν hcover
  let W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD s'.left).1 := fun k =>
    (smallBaseChange B S hS (stageTransition B S hS D hD (g k).left)
      (rep_stageTransition B S hS D hD hAffine (g k).left)).obj (stageChartOf hD hcet (ν k) (hν k))
  have hW : PointsCover W :=
    pointsCover_of_chartSystem_cover hD hAffine C hcet (fun y => hcov (Set.mem_univ y)) g ν hν hcov'
  have hWaff : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (W k).1.left) := fun k =>
    isAffine_smallBaseChange_obj B S hS (stageTransition B S hS D hD (g k).left)
      (rep_stageTransition B S hS D hD hAffine (g k).left) (hAffine (g k).left)
      (stageChartOf hD hcet (ν k) (hν k)) (hZaff k)
  have hWqc : ∀ k, IsQuasiCompactSpace B S hS (yoneda.obj (W k).1.left) := fun k =>
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hWaff k)
  have hWqs : ∀ k, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (W k).1.left) := fun k => by
    have := hWaff k
    exact isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ _ inferInstance
  choose n hn e he using hfr
  obtain ⟨s, M, hM, hiso⟩ := exists_stage_model_of_frames B S hS hZ D hc hD hAffine
    hQc hQs (j := s'.left) (W := W) hWqc hWqs hW E
    (e := fun k a => res (sval E) (limChartTransition B S hS D hc hD hAffine (g k).left
      (stageChartOf hD hcet (ν k) (hν k))) (e k a))
    (fun k => (he k).restrict _)
  exact ⟨s.left, M, K, inferInstance, fun k => laterStageChart B S hS D hD hAffine (W k) s, n, hn,
    pointsCover_smallBaseChange _ _ hW, hM, hiso⟩

end Descent

end AlgebraicGeometry.Space.IsCutoffBoundedSystem

end
