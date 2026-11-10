module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# An étale chart of a stage, base changed to the later stages and to the limit

Let `X = lim Xᵢ` be the limit of a cofiltered system of algebraic spaces with affine transition
morphisms and let `T` be an étale chart of a stage `X_j`.  Base change along the transition
morphisms and along the projection of the limit gives étale charts `T_s = T ×_{X_j} X_s` of the
later stages `s` and `T_∞ = T ×_{X_j} X` of the limit, related by canonical morphisms.  When `T`
is quasi-compact and quasi-separated, the regular functions on `T_∞` are the filtered colimit of
the regular functions on the `T_s`: this is Stacks 0CP4 for the affine line, applied to the
system of the `T_s`.

## Main definitions

* `AlgebraicGeometry.Space.limChart` and `AlgebraicGeometry.Space.laterStageChart`: `T_∞` and
  `T_s`.
* `AlgebraicGeometry.Space.limToStage` and `AlgebraicGeometry.Space.stageToStage`: the
  projections `T_∞ ⟶ T_s` and `T_{s'} ⟶ T_s`.
* `AlgebraicGeometry.Space.stageToLim`: the comparison `T_s ×_{X_s} X ⟶ T_∞`.
* `AlgebraicGeometry.Space.gpb`: pulling back regular functions along a morphism of the site.

## Main results

* `AlgebraicGeometry.Space.exists_gpb_limToStage_eq`: every regular function on `T_∞` comes
  from a stage.
* `AlgebraicGeometry.Space.exists_gpb_stageToStage_eq`: two regular functions on a stage which
  agree on `T_∞` agree on a later stage.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pulling back regular functions along a morphism of the big fppf site. -/
abbrev gpb {V V' : BigFppfOver B S hS} (g : V ⟶ V') :
    Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom

/-- Pulling back regular functions along a composite is the composite of the pullbacks. -/
theorem gpb_comp {V V' V'' : BigFppfOver B S hS} (g : V ⟶ V') (g' : V' ⟶ V'')
    (x : Γ((BigFppfOver.toScheme B S hS).obj V'', ⊤)) :
    gpb (g ≫ g') x = gpb g (gpb g' x) := by
  simp only [gpb, Functor.map_comp, op_comp]
  rfl

/-- Pulling back regular functions along the identity is the identity. -/
theorem gpb_id {V : BigFppfOver B S hS} (x : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    gpb (𝟙 V) x = x := by
  simp [gpb]

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

include hAffine in
/-- The projection from the limit to a stage is representable. -/
theorem rep_limitProjection (i : I) :
    yoneda.relativelyRepresentable (limitProjection B S hS D hSize hHomSize hD hAffine i).hom :=
  relativelyRepresentable_hom_of_isAffineHom B S hS _
    (isAffineHom_limitπ B S hS D hSize hHomSize hAffine i)

omit [IsCofiltered I] in
include hAffine in
/-- A transition morphism between stages is representable. -/
theorem rep_stageTransition {i j : I} (e : i ⟶ j) :
    yoneda.relativelyRepresentable (stageTransition B S hS D hD e).hom :=
  relativelyRepresentable_hom_of_isAffineHom B S hS _ (hAffine e)

variable {j : I} (T : SmallEtale B S hS (D.obj j))

/-- The base change of an étale chart of a stage to the limit. -/
abbrev limChart : SmallEtale B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1 :=
  (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j)
    (rep_limitProjection B S hS D hSize hHomSize hD hAffine j)).obj T

/-- The base change of an étale chart of a stage to a later stage. -/
abbrev laterStageChart (s : Over j) : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD
    s.left).1 :=
  (smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
    (rep_stageTransition B S hS D hD hAffine s.hom)).obj T

/-- The two morphisms from `T_∞` to the stage `X_j`, through `X_s` and through `T`, agree. -/
theorem limToStage_cond (s : Over j) :
    ((limChart B S hS D hSize hHomSize hD hAffine T).obj.hom ≫ limit.π D s.left) ≫
        (stageTransition B S hS D hD s.hom).hom =
      yoneda.map (sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) T) ≫
        T.obj.hom :=
  (Category.assoc _ _ _).trans ((congrArg _ (limit.w D s.hom)).trans
    (sbc_w (limitProjection B S hS D hSize hHomSize hD hAffine j)
      (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) T).symm)

/-- The projection of the base change to the limit onto the base change to a stage. -/
def limToStage (s : Over j) :
    (limChart B S hS D hSize hHomSize hD hAffine T).obj.left ⟶
      (laterStageChart B S hS D hD hAffine T s).obj.left :=
  (rep_stageTransition B S hS D hD hAffine s.hom).lift _ _
    (limToStage_cond B S hS D hSize hHomSize hD hAffine T s)

/-- The projection `T_∞ ⟶ T_s` commutes with the projections of `T_∞` and `T_s` to `T`. -/
@[reassoc]
theorem limToStage_proj (s : Over j) :
    limToStage B S hS D hSize hHomSize hD hAffine T s ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T =
      sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) T :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

/-- The projection `T_∞ ⟶ T_s` lies over the projection `X ⟶ X_s` of the limit. -/
@[reassoc]
theorem limToStage_chart (s : Over j) :
    yoneda.map (limToStage B S hS D hSize hHomSize hD hAffine T s) ≫
        (laterStageChart B S hS D hD hAffine T s).obj.hom =
      (limChart B S hS D hSize hHomSize hD hAffine T).obj.hom ≫ limit.π D s.left :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

omit [IsCofiltered I] in
/-- The two morphisms from `T_{s'}` to the stage `X_j`, through `X_s` and through `T`, agree. -/
theorem stageToStage_cond {s s' : Over j} (d : s' ⟶ s) :
    ((laterStageChart B S hS D hD hAffine T s').obj.hom ≫ D.map d.left) ≫
        (stageTransition B S hS D hD s.hom).hom =
      yoneda.map (sbcProj _ (rep_stageTransition B S hS D hD hAffine s'.hom) T) ≫ T.obj.hom :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((D.map_comp _ _).symm.trans
    (congrArg D.map (Over.w d)))).trans (sbc_w (stageTransition B S hS D hD s'.hom)
      (rep_stageTransition B S hS D hD hAffine s'.hom) T).symm)

/-- The transition morphism between the base changes to two stages. -/
def stageToStage {s s' : Over j} (d : s' ⟶ s) :
    (laterStageChart B S hS D hD hAffine T s').obj.left ⟶ (laterStageChart B S hS D hD hAffine T
        s).obj.left :=
  (rep_stageTransition B S hS D hD hAffine s.hom).lift _ _
    (stageToStage_cond B S hS D hD hAffine T d)

omit [IsCofiltered I] in
/-- The transition `T_{s'} ⟶ T_s` commutes with the projections of `T_{s'}` and `T_s` to `T`. -/
@[reassoc]
theorem stageToStage_proj {s s' : Over j} (d : s' ⟶ s) :
    stageToStage B S hS D hD hAffine T d ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T =
      sbcProj _ (rep_stageTransition B S hS D hD hAffine s'.hom) T :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

omit [IsCofiltered I] in
/-- The transition `T_{s'} ⟶ T_s` lies over the transition morphism `X_{s'} ⟶ X_s`. -/
@[reassoc]
theorem stageToStage_chart {s s' : Over j} (d : s' ⟶ s) :
    yoneda.map (stageToStage B S hS D hD hAffine T d) ≫ (laterStageChart B S hS D hD hAffine T
        s).obj.hom =
      (laterStageChart B S hS D hD hAffine T s').obj.hom ≫ D.map d.left :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

omit [IsCofiltered I] in /-- Composing a map into `T_{s'}` with `T_{s'} ⟶ T_s`. -/
  private theorem comp_stageToStage_eq {s s' : Over j} (d : s' ⟶ s) {A : BigFppfOver B S hS}
    {c : yoneda.obj A ⟶ D.obj s'.left} {p : A ⟶ T.obj.left}
    {w : A ⟶ (laterStageChart B S hS D hD hAffine T s').obj.left}
    {v : A ⟶ (laterStageChart B S hS D hD hAffine T s).obj.left}
    (hw₁ : yoneda.map w ≫ (laterStageChart B S hS D hD hAffine T s').obj.hom = c)
    (hw₂ : w ≫ sbcProj _ (rep_stageTransition B S hS D hD hAffine s'.hom) T = p)
    (hv₁ : yoneda.map v ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom = c ≫ D.map d.left)
    (hv₂ : v ≫ sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T = p) :
    w ≫ stageToStage B S hS D hD hAffine T d = v := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · erw [Functor.map_comp, Category.assoc, stageToStage_chart, ← Category.assoc, hw₁, hv₁]
    rfl
  · erw [Category.assoc, stageToStage_proj, hw₂, hv₂]

/-- The projection `T_∞ ⟶ T_{s'}` followed by the transition `T_{s'} ⟶ T_s` is the projection
`T_∞ ⟶ T_s`. -/
theorem limToStage_stageToStage {s s' : Over j} (d : s' ⟶ s) :
    limToStage B S hS D hSize hHomSize hD hAffine T s' ≫ stageToStage B S hS D hD hAffine T d =
      limToStage B S hS D hSize hHomSize hD hAffine T s :=
  comp_stageToStage_eq B S hS D hD hAffine T d
    (limToStage_chart B S hS D hSize hHomSize hD hAffine T s')
    (limToStage_proj B S hS D hSize hHomSize hD hAffine T s')
    (by erw [limToStage_chart, Category.assoc, limit.w])
    (limToStage_proj B S hS D hSize hHomSize hD hAffine T s)

/-- The base change to the limit of the base change to a stage. -/
abbrev stageLimChart (s : Over j) :
    SmallEtale B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1 :=
  (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s.left)
    (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)).obj
    (laterStageChart B S hS D hD hAffine T s)

/-- The two morphisms from `T_s ×_{X_s} X` to `X_j`, through `T` and through `X`, agree. -/
theorem stageToLim_cond (s : Over j) :
    yoneda.map (sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s) ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T) ≫ T.obj.hom =
      (stageLimChart B S hS D hSize hHomSize hD hAffine T s).obj.hom ≫
        (limitProjection B S hS D hSize hHomSize hD hAffine j).hom :=
  calc _ = yoneda.map (sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s)) ≫
        (yoneda.map (sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T) ≫ T.obj.hom) := by
        rw [Functor.map_comp, Category.assoc]
    _ = yoneda.map (sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s)) ≫ ((laterStageChart B S hS D hD hAffine T
            s).obj.hom ≫
          D.map s.hom) :=
        congrArg (_ ≫ ·) (sbc_w (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom) T)
    _ = (yoneda.map (sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T
            s)) ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom) ≫
          D.map s.hom := (Category.assoc _ _ _).symm
    _ = ((stageLimChart B S hS D hSize hHomSize hD hAffine T s).obj.hom ≫ limit.π D s.left) ≫
          D.map s.hom :=
        congrArg (· ≫ D.map s.hom) (sbc_w (limitProjection B S hS D hSize hHomSize hD hAffine
            s.left)
          (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
          (laterStageChart B S hS D hD hAffine T s))
    _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (limit.w D s.hom))

/-- The comparison of the base change to the limit of the base change to a stage with the base
change to the limit. -/
def stageToLim (s : Over j) :
    stageLimChart B S hS D hSize hHomSize hD hAffine T s ⟶
      limChart B S hS D hSize hHomSize hD hAffine T :=
  sbcLift _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) _
    (stageToLim_cond B S hS D hSize hHomSize hD hAffine T s)

/-- The comparison `T_s ×_{X_s} X ⟶ T_∞` followed by the projection to `T` is the projection
through `T_s`. -/
theorem stageToLim_proj (s : Over j) :
    (stageToLim B S hS D hSize hHomSize hD hAffine T s).hom.left ≫
        sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) T =
      sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
          (laterStageChart B S hS D hD hAffine T s) ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T :=
  sbcLift_proj _ _ _ _

/-- **The comparison followed by the projection to the stage is the projection.** -/
theorem stageToLim_limToStage (s : Over j) :
    (stageToLim B S hS D hSize hHomSize hD hAffine T s).hom.left ≫
        limToStage B S hS D hSize hHomSize hD hAffine T s =
      sbcProj _ (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s) := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · have h1 := limToStage_chart B S hS D hSize hHomSize hD hAffine T s
    have h2 := CostructuredArrow.w (stageToLim B S hS D hSize hHomSize hD hAffine T s).hom
    have h3 := sbc_w (limitProjection B S hS D hSize hHomSize hD hAffine s.left)
      (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
      (laterStageChart B S hS D hD hAffine T s)
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ limit.π D s.left) h2).trans h3.symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (limToStage_proj B S hS D hSize hHomSize hD hAffine T s)).trans
      (stageToLim_proj B S hS D hSize hHomSize hD hAffine T s))

omit [IsCofiltered I] in
/-- The transition morphisms between the base changes to the stages are compatible with
composition. -/
theorem stageToStage_comp {s s' s'' : Over j} (d : s' ⟶ s) (d' : s'' ⟶ s') :
    stageToStage B S hS D hD hAffine T (d' ≫ d) =
      stageToStage B S hS D hD hAffine T d' ≫ stageToStage B S hS D hD hAffine T d := by
  refine (comp_stageToStage_eq B S hS D hD hAffine T d
    (stageToStage_chart B S hS D hD hAffine T d') (stageToStage_proj B S hS D hD hAffine T d')
    ?_ (stageToStage_proj B S hS D hD hAffine T (d' ≫ d))).symm
  erw [stageToStage_chart, Over.comp_left, D.map_comp, Category.assoc]
  rfl

/-! ### Naturality in the chart -/

section Naturality

variable {T} {T' : SmallEtale B S hS (D.obj j)} (h : T ⟶ T')

omit [IsCofiltered I] in /-- Maps into the base changes at a stage are natural in the chart. -/
  private theorem comp_eq_comp_map_stage {s : Over j} {A A' : BigFppfOver B S hS} {m : A ⟶ A'}
    {c : yoneda.obj A ⟶ D.obj s.left} {c' : yoneda.obj A' ⟶ D.obj s.left}
    {pA : A ⟶ T.obj.left} {pA' : A' ⟶ T'.obj.left}
    {u : A ⟶ (laterStageChart B S hS D hD hAffine T s).obj.left}
    {u' : A' ⟶ (laterStageChart B S hS D hD hAffine T' s).obj.left}
    (hm₁ : yoneda.map m ≫ c' = c) (hm₂ : m ≫ pA' = pA ≫ h.hom.left)
    (hu₁ : yoneda.map u ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom = c)
    (hu₂ : u ≫ sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T = pA)
    (hu'₁ : yoneda.map u' ≫ (laterStageChart B S hS D hD hAffine T' s).obj.hom = c')
    (hu'₂ : u' ≫ sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T' = pA') :
    m ≫ u' = u ≫ ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom.left := by
  have h₁ := CostructuredArrow.w ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
    (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · erw [Functor.map_comp, Category.assoc, hu'₁, hm₁, Functor.map_comp, Category.assoc, h₁, hu₁]
  · erw [Category.assoc, hu'₂, hm₂, Category.assoc, smallBaseChange_map_proj, ← Category.assoc,
      hu₂]

/-- The projection `T_∞ ⟶ T_s` is natural in the chart `T`. -/
theorem limToStage_naturality (s : Over j) :
    ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine j)).map h).hom.left ≫
        limToStage B S hS D hSize hHomSize hD hAffine T' s =
      limToStage B S hS D hSize hHomSize hD hAffine T s ≫
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom.left := by
  refine comp_eq_comp_map_stage B S hS D hD hAffine h
    ?_ (smallBaseChange_map_proj (limitProjection B S hS D hSize hHomSize hD hAffine j)
      (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) h)
    (limToStage_chart B S hS D hSize hHomSize hD hAffine T s)
    (limToStage_proj B S hS D hSize hHomSize hD hAffine T s)
    (limToStage_chart B S hS D hSize hHomSize hD hAffine T' s)
    (limToStage_proj B S hS D hSize hHomSize hD hAffine T' s)
  erw [← Category.assoc, CostructuredArrow.w]

/-- The comparison `T_s ×_{X_s} X ⟶ T_∞` is natural in the chart `T`. -/
theorem stageToLim_naturality (s : Over j) :
    (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)).map
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h) ≫
        stageToLim B S hS D hSize hHomSize hD hAffine T' s =
      stageToLim B S hS D hSize hHomSize hD hAffine T s ≫
        (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j)
          (rep_limitProjection B S hS D hSize hHomSize hD hAffine j)).map h := by
  apply sbc_hom_ext
  have h1 := stageToLim_proj B S hS D hSize hHomSize hD hAffine T' s
  have h2 := stageToLim_proj B S hS D hSize hHomSize hD hAffine T s
  have h3 := smallBaseChange_map_proj (limitProjection B S hS D hSize hHomSize hD hAffine j)
    (rep_limitProjection B S hS D hSize hHomSize hD hAffine j) h
  have h4 := smallBaseChange_map_proj (stageTransition B S hS D hD s.hom)
    (rep_stageTransition B S hS D hD hAffine s.hom) h
  have h5 := smallBaseChange_map_proj (limitProjection B S hS D hSize hHomSize hD hAffine s.left)
    (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)
    ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom)).map h)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h5).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h4).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h.hom.left) h2).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).symm.trans
      (Category.assoc _ _ _).symm)))))))))

omit [IsCofiltered I] in
/-- The transition `T_{s'} ⟶ T_s` is natural in the chart `T`. -/
theorem stageToStage_naturality {s s' : Over j} (d : s' ⟶ s) :
    ((smallBaseChange B S hS (stageTransition B S hS D hD s'.hom)
        (rep_stageTransition B S hS D hD hAffine s'.hom)).map h).hom.left ≫
        stageToStage B S hS D hD hAffine T' d =
      stageToStage B S hS D hD hAffine T d ≫
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom.left := by
  refine comp_eq_comp_map_stage B S hS D hD hAffine h
    ?_ (smallBaseChange_map_proj (stageTransition B S hS D hD s'.hom)
      (rep_stageTransition B S hS D hD hAffine s'.hom) h)
    (stageToStage_chart B S hS D hD hAffine T d)
    (stageToStage_proj B S hS D hD hAffine T d)
    (stageToStage_chart B S hS D hD hAffine T' d)
    (stageToStage_proj B S hS D hD hAffine T' d)
  erw [← Category.assoc, CostructuredArrow.w]

end Naturality

set_option synthInstance.maxHeartbeats 400000 in
-- the `HasPullbacks` instance for presheaves on the big fppf site needs a deep instance search
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_StageChartSystem :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_StageChartSystem
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The system of base changes as a diagram of presheaves -/

/-- The diagram of the presheaf base changes of the chart `T` to the later stages. -/
abbrev stageChartDiagram : Over j ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post D ⋙ Over.pullback T.obj.hom) ⋙ Over.forget (yoneda.obj T.obj.left)

/-- The limit cone of `AlgebraicGeometry.Space.stageChartDiagram`: the presheaf base change of
`T` to the limit. -/
abbrev stageChartCone : Cone (stageChartDiagram B S hS D T) :=
  (Over.forget _).mapCone ((Over.pullback T.obj.hom).mapCone ((limit.cone D).overPost j))

/-- **The base change to the limit is the limit of the base changes to the stages.** -/
def stageChartConeIsLimit : IsLimit (stageChartCone B S hS D T) :=
  isLimitPullbackLimitOverPost B S hS D j T.obj.hom

omit [IsCofiltered I] in
/-- The leg of the limit cone at `s` lies over the projection of the limit to `X_s`. -/
theorem stageChartCone_π_fst (s : Over j) :
    (stageChartCone B S hS D T).π.app s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ limit.π D s.left :=
  pullback.lift_fst _ _ _

omit [IsCofiltered I] in
/-- The leg of the limit cone at `s` commutes with the projections to `T`. -/
theorem stageChartCone_π_snd (s : Over j) :
    (stageChartCone B S hS D T).π.app s ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

omit [IsCofiltered I] in
/-- A transition map of the diagram lies over the corresponding transition morphism of stages. -/
theorem stageChartDiagram_map_fst {s s' : Over j} (d : s' ⟶ s) :
    (stageChartDiagram B S hS D T).map d ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.map d.left :=
  pullback.lift_fst _ _ _

omit [IsCofiltered I] in
/-- A transition map of the diagram commutes with the projections to `T`. -/
theorem stageChartDiagram_map_snd {s s' : Over j} (d : s' ⟶ s) :
    (stageChartDiagram B S hS D T).map d ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The base change to a stage represents the presheaf base change. -/
def stageChartIso (s : Over j) :
    yoneda.obj (laterStageChart B S hS D hD hAffine T s).obj.left ≅ (stageChartDiagram B S hS D
        T).obj s :=
  ((rep_stageTransition B S hS D hD hAffine s.hom).isPullback T.obj.hom).isoPullback

/-- The base change to the limit represents the presheaf base change. -/
def limChartIso :
    yoneda.obj (limChart B S hS D hSize hHomSize hD hAffine T).obj.left ≅ (stageChartCone B S hS D
        T).pt :=
  ((rep_limitProjection B S hS D hSize hHomSize hD hAffine j).isPullback T.obj.hom).isoPullback

/-- A map of pullbacks over a common base that is compatible with maps between the representing
pullback squares is compatible with the canonical isomorphisms. -/
private theorem isoPullback_hom_comp_eq {C : Type*} [Category C] {A A' X X' Y Z : C}
    {f : X ⟶ Z} {f' : X' ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [HasPullback f' g]
    {a₁ : A ⟶ X} {a₂ : A ⟶ Y} {a₁' : A' ⟶ X'} {a₂' : A' ⟶ Y}
    (h : IsPullback a₁ a₂ f g) (h' : IsPullback a₁' a₂' f' g)
    {k : pullback f g ⟶ pullback f' g} {x : X ⟶ X'} {u : A ⟶ A'}
    (hk₁ : k ≫ pullback.fst _ _ = pullback.fst _ _ ≫ x)
    (hk₂ : k ≫ pullback.snd _ _ = pullback.snd _ _)
    (hu₁ : a₁ ≫ x = u ≫ a₁') (hu₂ : a₂ = u ≫ a₂') :
    h.isoPullback.hom ≫ k = u ≫ h'.isoPullback.hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hk₁, ← Category.assoc, h.isoPullback_hom_fst,
      h'.isoPullback_hom_fst, hu₁]
  · rw [Category.assoc, Category.assoc, hk₂, h.isoPullback_hom_snd, h'.isoPullback_hom_snd, hu₂]

/-- Under the representing isomorphisms, the leg of the limit cone at `s` is the projection
`T_∞ ⟶ T_s`. -/
theorem limChartIso_comp (s : Over j) :
    (limChartIso B S hS D hSize hHomSize hD hAffine T).hom ≫ (stageChartCone B S hS D T).π.app s =
      yoneda.map (limToStage B S hS D hSize hHomSize hD hAffine T s) ≫
        (stageChartIso B S hS D hD hAffine T s).hom := by
  exact isoPullback_hom_comp_eq _ _ (stageChartCone_π_fst B S hS D T s)
    (stageChartCone_π_snd B S hS D T s)
    (limToStage_chart B S hS D hSize hHomSize hD hAffine T s).symm
    ((congrArg yoneda.map (limToStage_proj B S hS D hSize hHomSize hD hAffine T s).symm).trans
      (Functor.map_comp yoneda _ _))

omit [IsCofiltered I] in
/-- Under the representing isomorphisms, a transition map of the diagram is the transition
`T_{s'} ⟶ T_s`. -/
theorem stageChartIso_comp {s s' : Over j} (d : s' ⟶ s) :
    (stageChartIso B S hS D hD hAffine T s').hom ≫ (stageChartDiagram B S hS D T).map d =
      yoneda.map (stageToStage B S hS D hD hAffine T d) ≫
        (stageChartIso B S hS D hD hAffine T s).hom := by
  exact isoPullback_hom_comp_eq _ _ (stageChartDiagram_map_fst B S hS D T d)
    (stageChartDiagram_map_snd B S hS D T d)
    (stageToStage_chart B S hS D hD hAffine T d).symm
    ((congrArg yoneda.map (stageToStage_proj B S hS D hD hAffine T d).symm).trans
      (Functor.map_comp yoneda _ _))

/-! ### Regular functions as morphisms to the affine line -/

omit [IsCofiltered I] in
variable {B S hS} in
/-- A regular function on an object of the site is a morphism to the affine line. -/
def fnEquiv (V : BigFppfOver B S hS) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ≃ (V ⟶ affineLineBigFppfOver B S hS) :=
  ((gammaAffineLineIso B S hS).app (op V)).toEquiv

variable {B S hS} in
/-- Under `fnEquiv`, pulling back a regular function along `g` is precomposition with `g`. -/
theorem fnEquiv_gpb {V V' : BigFppfOver B S hS} (g : V ⟶ V')
    (x : Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) :
    fnEquiv V (gpb g x) = g ≫ fnEquiv V' x := by
  have h := NatTrans.naturality_apply (gammaAffineLineIso B S hS).hom g.op x
  exact h

/-! ### Descent of regular functions -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  (hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T.obj.left))
  (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T.obj.left))

omit [IsCofiltered I] in
include hD in
/-- Each object of the diagram of base changes is an algebraic space. -/
theorem stageChartDiagram_alg (s : Over j) :
    IsAlgebraicSpace B S hS ((stageChartDiagram B S hS D T).obj s) :=
  isAlgebraicSpace_pullback B S hS _ _ (hD s.left) (isAlgebraicSpace_yoneda B S hS _) (hD j)

omit [IsCofiltered I] in
include hD hQc hQs hTqc in
/-- Each object of the diagram of base changes is quasi-compact. -/
theorem stageChartDiagram_qc (s : Over j) :
    IsQuasiCompactSpace B S hS ((stageChartDiagram B S hS D T).obj s) :=
  isQuasiCompactSpace_pullback B S hS hZ _ _ (hD s.left) (hD j) (hQc s.left) hTqc (hQs j)

omit [IsCofiltered I] in
include hAffine in
/-- The projection `T_s ⟶ T` of the presheaf base change is affine. -/
theorem stageChartDiagram_snd_affine (s : Over j) :
    IsAffineHom B S hS (pullback.snd (D.map s.hom) T.obj.hom) :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback (D.map s.hom) T.obj.hom) (hAffine s.hom)

omit [IsCofiltered I] in
include hD hAffine hTqs in
/-- Each object of the diagram of base changes is absolutely quasi-separated. -/
theorem stageChartDiagram_qs (s : Over j) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((stageChartDiagram B S hS D T).obj s) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (stageChartDiagram_alg B S hS D hD T s) hTqs
    (isQuasiSeparated_of_isAffineHom B S hS _ (stageChartDiagram_alg B S hS D hD T s)
      (isAlgebraicSpace_yoneda B S hS _) (stageChartDiagram_snd_affine B S hS D hAffine T s))

omit [IsCofiltered I] in
include hAffine in
/-- The transition maps of the diagram of base changes are affine. -/
theorem stageChartDiagram_affine {s s' : Over j} (d : s' ⟶ s) :
    IsAffineHom B S hS ((stageChartDiagram B S hS D T).map d) := by
  have t : IsPullback (pullback.snd _ _) (pullback.fst _ _) T.obj.hom (D.map s.hom) :=
    (IsPullback.of_hasPullback (D.map s.hom) T.obj.hom).flip
  have outer : IsPullback ((stageChartDiagram B S hS D T).map d ≫ pullback.snd _ _)
      (pullback.fst _ _) T.obj.hom (D.map d.left ≫ D.map s.hom) := by
    rw [stageChartDiagram_map_snd]
    change IsPullback (pullback.snd (D.map s'.hom) T.obj.hom)
      (pullback.fst (D.map s'.hom) T.obj.hom) T.obj.hom (D.map d.left ≫ D.map s.hom)
    rw [← D.map_comp, Over.w d]
    exact (IsPullback.of_hasPullback _ T.obj.hom).flip
  exact IsAffineHom.of_isPullback
    (IsPullback.of_right outer (stageChartDiagram_map_fst B S hS D T d) t).flip (hAffine d.left)

include hSize hHomSize hD hAffine in
/-- The cone point, the presheaf base change of `T` to the limit, is an algebraic space. -/
theorem stageChartCone_alg : IsAlgebraicSpace B S hS (stageChartCone B S hS D T).pt :=
  isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine)
    (isAlgebraicSpace_yoneda B S hS _) (hD j)

omit [IsCofiltered I] in
include hHomSize in
/-- The hom-sets of `Over j` are smaller than the cofinality of the cutoff. -/
theorem over_hom_size (s s' : Over j) : #(s ⟶ s') < B.cutoff.ord.cof :=
  (Cardinal.mk_le_of_injective (f := fun d : s ⟶ s' => d.left)
    (fun _ _ h => Over.OverMorphism.ext h)).trans_lt (hHomSize _ _)

include hSize hHomSize hD hAffine hZ hQc hQs hTqc hTqs in
/-- **Every regular function on the base change to the limit comes from a stage.** -/
theorem exists_gpb_limToStage_eq
    (y : Γ((BigFppfOver.toScheme B S hS).obj (limChart B S hS D hSize hHomSize hD hAffine
        T).obj.left, ⊤)) :
    ∃ (s : Over j) (x : Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine T s).obj.left, ⊤)),
      gpb (limToStage B S hS D hSize hHomSize hD hAffine T s) x = y := by
  let G := (limChartIso B S hS D hSize hHomSize hD hAffine T).inv ≫ yoneda.map (fnEquiv _ y)
  obtain ⟨s₀, t, s, a, a', h1, -⟩ := exists_stage_map_of_relativelyLimitPreserving B S hS hZ
    (stageChartDiagram B S hS D T) (stageChartCone B S hS D T) (stageChartConeIsLimit B S hS D T)
    (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize j) (over_hom_size B hHomSize)
    (stageChartDiagram_alg B S hS D hD T) (stageChartDiagram_qc B S hS D hD T hZ hQc hQs hTqc)
    (stageChartDiagram_qs B S hS D hD hAffine T hZ hTqs)
    (stageChartDiagram_affine B S hS D hAffine T)
    (stageChartCone_alg B S hS D hSize hHomSize hD hAffine T)
    (isAlgebraicSpace_yoneda B S hS (affineLineBigFppfOver B S hS))
    (isAlgebraicSpace_yoneda B S hS (baseTerminal B S hS))
    (yoneda.map (affineLineToBase B S hS)) (isLocallyOfFinitePresentation_affineLineToBase B S hS)
    G (Over.mk (𝟙 j)) ((baseTerminal_yonedaIsTerminal B S hS).from _)
    ((baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)
  let t' : yoneda.obj (laterStageChart B S hS D hD hAffine T s).obj.left ⟶
      yoneda.obj (affineLineBigFppfOver B S hS) :=
    (stageChartIso B S hS D hD hAffine T s).hom ≫ (stageChartDiagram B S hS D T).map a ≫ t
  refine ⟨s, (fnEquiv _).symm (yoneda.preimage t'), ?_⟩
  apply (fnEquiv _).injective
  rw [fnEquiv_gpb, Equiv.apply_symm_apply]
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_preimage]
  calc yoneda.map (limToStage B S hS D hSize hHomSize hD hAffine T s) ≫ t'
      = (limChartIso B S hS D hSize hHomSize hD hAffine T).hom ≫
          ((stageChartCone B S hS D T).π.app s ≫ (stageChartDiagram B S hS D T).map a ≫ t) := by
        simp only [t', ← Category.assoc, limChartIso_comp]
    _ = (limChartIso B S hS D hSize hHomSize hD hAffine T).hom ≫ G := by rw [h1]
    _ = _ := by simp only [G, Iso.hom_inv_id_assoc]

include hSize hHomSize hD hAffine hZ hQc hQs hTqc hTqs in
/-- **Two regular functions on a stage which agree on the base change to the limit agree on a
later stage.** -/
theorem exists_gpb_stageToStage_eq {s : Over j}
    (x₁ x₂ : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T
        s).obj.left, ⊤))
    (h : gpb (limToStage B S hS D hSize hHomSize hD hAffine T s) x₁ =
      gpb (limToStage B S hS D hSize hHomSize hD hAffine T s) x₂) :
    ∃ (s' : Over j) (d : s' ⟶ s), gpb (stageToStage B S hS D hD hAffine T d) x₁ =
      gpb (stageToStage B S hS D hD hAffine T d) x₂ := by
  let r : (stageChartDiagram B S hS D T).obj s ⟶ yoneda.obj (affineLineBigFppfOver B S hS) :=
    (stageChartIso B S hS D hD hAffine T s).inv ≫ yoneda.map (fnEquiv _ x₁)
  let r' : (stageChartDiagram B S hS D T).obj s ⟶ yoneda.obj (affineLineBigFppfOver B S hS) :=
    (stageChartIso B S hS D hD hAffine T s).inv ≫ yoneda.map (fnEquiv _ x₂)
  have hl : ∀ x, (limChartIso B S hS D hSize hHomSize hD hAffine T).hom ≫
      (stageChartCone B S hS D T).π.app s ≫ (stageChartIso B S hS D hD hAffine T s).inv ≫
        yoneda.map (fnEquiv _ x) =
      yoneda.map (fnEquiv _ (gpb (limToStage B S hS D hSize hHomSize hD hAffine T s) x)) := by
    intro x
    rw [fnEquiv_gpb, Functor.map_comp, ← Category.assoc, ← Category.assoc, limChartIso_comp,
      Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  obtain ⟨s', d, hd⟩ := exists_stage_eq_of_relativelyLimitPreserving B S hS hZ
    (stageChartDiagram B S hS D T) (stageChartCone B S hS D T) (stageChartConeIsLimit B S hS D T)
    (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize j) (over_hom_size B hHomSize)
    (stageChartDiagram_alg B S hS D hD T) (stageChartDiagram_qc B S hS D hD T hZ hQc hQs hTqc)
    (stageChartDiagram_qs B S hS D hD hAffine T hZ hTqs)
    (stageChartDiagram_affine B S hS D hAffine T)
    (stageChartCone_alg B S hS D hSize hHomSize hD hAffine T)
    (isAlgebraicSpace_yoneda B S hS (affineLineBigFppfOver B S hS))
    (isAlgebraicSpace_yoneda B S hS (baseTerminal B S hS))
    (yoneda.map (affineLineToBase B S hS)) (isLocallyOfFinitePresentation_affineLineToBase B S hS)
    s r r' (by
      apply (Iso.cancel_iso_hom_left (limChartIso B S hS D hSize hHomSize hD hAffine T) _ _).1
      simp only [r, r']
      rw [hl, hl, h])
    ((baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)
  refine ⟨s', d, ?_⟩
  apply (fnEquiv _).injective
  rw [fnEquiv_gpb, fnEquiv_gpb]
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  have e : ∀ x, yoneda.map (stageToStage B S hS D hD hAffine T d) ≫ yoneda.map (fnEquiv _ x) =
      (stageChartIso B S hS D hD hAffine T s').hom ≫ (stageChartDiagram B S hS D T).map d ≫
        (stageChartIso B S hS D hD hAffine T s).inv ≫ yoneda.map (fnEquiv _ x) := by
    intro x
    rw [← Category.assoc, stageChartIso_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e, e]
  exact congrArg ((stageChartIso B S hS D hD hAffine T s').hom ≫ ·) hd

end Descent

end AlgebraicGeometry.Space
