module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FramedModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Limits.EtaleChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart

/-!
# Trivializing charts of a module on a limit come from a stage

Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated algebraic
spaces with affine transition morphisms, and let `E` be an `𝒪_X`-module admitting frames locally
on the small étale site of `X`.  Choose an affine étale chart `U₀` of a stage `X_{i₀}`, surjective
on points, and its system of base changes `Uᵢ = U₀ ×_{X_{i₀}} Xᵢ`, whose limit `U` is an affine
scheme.  Every point of `U` has an affine étale neighbourhood on which `E` has a frame; such a
neighbourhood is étale over the limit `U` of the affine schemes `Uᵢ`, so by Stacks 01ZM and 07RP
(`AlgebraicGeometry.exists_isPullback_etale_of_etale`) it is the base change of a scheme étale
over some `Uᵢ`.

## Main definitions

* `AlgebraicGeometry.Space.limitChart`: the limit `U` of the chart system, as an étale chart of
  the limit algebraic space.
* `AlgebraicGeometry.Space.limChartTransition`: the comparison from the base change to the limit
  of the base change of a chart to a later stage, to the base change of the chart.

## Main results

* `AlgebraicGeometry.Space.exists_affine_frame_chart`: an affine étale neighbourhood, in `U`, of
  any point of `U`, on which `E` has a frame.
* `AlgebraicGeometry.Space.exists_stage_chart`: such a neighbourhood is dominated by the base
  change to the limit of an affine étale chart of a stage, factoring through the chart system.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-! ### Base change of a chart to a later stage, then to the limit -/

section Transition

variable {j j' : I} (g : j' ⟶ j) (T : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)

/-- The composite of the projection from the base change to the limit of the base change of `T`
along `g` to `T`, followed by the structure morphism of `T`, equals its structure morphism
followed by the projection of the limit to the stage `j`. -/
theorem limChartTransition_cond :
    yoneda.map (sbcProj (limitProjection B S hS D hSize hHomSize hD hAffine j')
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine j')
        ((smallBaseChange B S hS (stageTransition B S hS D hD g)
          (rep_stageTransition B S hS D hD hAffine g)).obj T) ≫
      sbcProj (stageTransition B S hS D hD g) (rep_stageTransition B S hS D hD hAffine g) T) ≫
        T.obj.hom =
      ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j')
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine j')).obj
        ((smallBaseChange B S hS (stageTransition B S hS D hD g)
          (rep_stageTransition B S hS D hD hAffine g)).obj T)).obj.hom ≫
        (limitProjection B S hS D hSize hHomSize hD hAffine j).hom := by
  rw [Functor.map_comp, Category.assoc, sbc_w, ← Category.assoc, sbc_w, Category.assoc]
  exact congrArg (_ ≫ ·) (limit.w D g)

/-- The comparison from the base change to the limit of the base change of `T` to a later stage,
to the base change of `T` to the limit. -/
def limChartTransition :
    (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j')
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine j')).obj
        ((smallBaseChange B S hS (stageTransition B S hS D hD g)
          (rep_stageTransition B S hS D hD hAffine g)).obj T) ⟶
      (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine j)).obj T :=
  sbcLift _ _ _ (limChartTransition_cond B S hS D hSize hHomSize hD hAffine g T)

end Transition

/-! ### The limit of the chart system as an étale chart of the limit -/

section ChartSystem

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
  (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

/-- Étaleness (as a presheaf morphism) of one leg of a pullback square is inherited from the
opposite leg. -/
private theorem presheaf_etale_of_isPullback
    {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : K ⟶ F} {snd : K ⟶ G} {f : F ⟶ H}
    {g : G ⟶ H} (h : IsPullback fst snd f g)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf snd := by
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_isPullback h hf

omit [IsCofiltered I] in
include hf₀ in
/-- The limit of the chart system is étale over the limit algebraic space when the chart `f₀` is
étale. -/
theorem presheaf_etale_toLimit :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf L.toLimit := by
  exact presheaf_etale_of_isPullback L.isPullback.flip hf₀

omit [IsCofiltered I] in
include hf₀ in
/-- Each member of the chart system is étale over its stage when the chart `f₀` is étale. -/
theorem presheaf_etale_stageMap (t : Over i₀) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (C.stageMap t) := by
  exact presheaf_etale_of_isPullback (C.isPullback t).flip hf₀

/-- The limit of the chart system, as an étale chart of the limit algebraic space. -/
def limitChart : SmallEtale B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1 :=
  ⟨CostructuredArrow.mk L.toLimit, presheaf_etale_toLimit L hf₀⟩

end ChartSystem

/-! ### Local frames -/

section LocalFrames

variable {B S hS}

/-- An `𝒪_X`-module **has local frames** of sizes satisfying `P` when every étale chart of `X` is
covered by charts over which the module has a frame of such a size. -/
def HasLocalFrames {X : AlgebraicSpaces B S hS} (P : ℕ → Prop) (E : Modules.{u, u} B S hS X.1 X.2) :
    Prop :=
  ∀ V : SmallEtale B S hS X.1, ∃ (ι : Type (u + 1)) (W : ι → SmallEtale B S hS X.1)
    (g : ∀ i, W i ⟶ V), Sieve.ofArrows W g ∈ SmallEtale.topology B S hS X.1 V ∧
      ∀ i, ∃ n, P n ∧ ∃ e : Fin n → (sval E).obj (op (W i)), IsFrame (sval E) e

/-- **An affine étale neighbourhood with a frame**, inside a given chart, of any point of it. -/
theorem exists_affine_frame_chart {X : AlgebraicSpaces B S hS} {P : ℕ → Prop}
    {E : Modules.{u, u} B S hS X.1 X.2} (hE : HasLocalFrames P E) (V : SmallEtale B S hS X.1)
    (v : (BigFppfOver.toScheme B S hS).obj V.1.left) :
    ∃ (A : SmallEtale B S hS X.1) (a : A ⟶ V) (w : (BigFppfOver.toScheme B S hS).obj A.1.left),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) ∧
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) w = v ∧
      ∃ n, P n ∧ ∃ e : Fin n → (sval E).obj (op A), IsFrame (sval E) e := by
  obtain ⟨ι, W, g, hcov, hfr⟩ := hE V
  obtain ⟨V', h, hR, z', hz'⟩ := exists_mem_sieve_scheme_point B S hS X.1 V hcov v
  obtain ⟨Y, h', g', hg', rfl⟩ := hR
  obtain ⟨i⟩ := hg'
  obtain ⟨T₀, ι₀, haff, w₀, hw₀⟩ := exists_affine_chart_at B S hS X.1 V' z'
  obtain ⟨n, hn, e, he⟩ := hfr i
  refine ⟨T₀, ι₀ ≫ h' ≫ g i, w₀, haff, ?_, n, hn, _, he.restrict (ι₀ ≫ h')⟩
  rwa [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw₀]

end LocalFrames

/-! ### Charts of a stage factoring through the chart system -/

section StageCharts

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
  (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

omit [IsCofiltered I] in
include hf₀ in
/-- An object of the site étale over a member of the chart system is étale over its stage when
the chart `f₀` is étale. -/
theorem presheaf_etale_yoneda_map_comp_stageMap {t : Over i₀} {Z : BigFppfOver B S hS}
    (ν : Z ⟶ C.siteDiagram.obj t) (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map ν ≫ C.stageMap t) := by
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  exact MorphismProperty.comp_mem _ _ _
    ((presheaf_yoneda_map_iff B S hS inferInstance ν).2 hν) (presheaf_etale_stageMap hf₀ t)

/-- The étale chart of a stage given by an object of the site étale over a member of the chart
system. -/
def stageChartOf {t : Over i₀} {Z : BigFppfOver B S hS} (ν : Z ⟶ C.siteDiagram.obj t)
    (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)) :
    SmallEtale B S hS (stageAlgebraicSpace B S hS D hD t.left).1 :=
  ⟨CostructuredArrow.mk (yoneda.map ν ≫ C.stageMap t),
    presheaf_etale_yoneda_map_comp_stageMap hf₀ ν hν⟩

/-- **The base change to the limit of a chart of a stage maps to a neighbourhood it descends.**
If `A` is an étale chart of the limit over the limit `U` of the chart system, whose underlying
scheme is the base change along `U ⟶ Uₜ` of `X ⟶ Uₜ` (cartesian square `hpb`), then every chart
of the stage `t` given by a scheme `Z` mapping to `X` over `Uₜ` has base change to the limit
mapping to `A`. -/
theorem nonempty_limChart_stageChartOf_hom
    {A : SmallEtale B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1}
    (a : A ⟶ limitChart hSize hHomSize hD hAffine L hf₀) {t : Over i₀}
    {Z : BigFppfOver B S hS} (ν : Z ⟶ C.siteDiagram.obj t)
    (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)) {X : Scheme.{u}}
    (q : X ⟶ (BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj t))
    (ψ : (BigFppfOver.toScheme B S hS).obj A.1.left ⟶ X)
    (hpb : IsPullback ψ ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS _).map a)) q
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app t)))
    (κ : (BigFppfOver.toScheme B S hS).obj Z ⟶ X)
    (hκ : κ ≫ q = (BigFppfOver.toScheme B S hS).map ν) :
    Nonempty (limChart B S hS D hSize hHomSize hD hAffine (stageChartOf hD hf₀ ν hν) ⟶ A) := by
  let W := stageChartOf hD hf₀ ν hν
  let f := limitProjection B S hS D hSize hHomSize hD hAffine t.left
  let hf := rep_limitProjection B S hS D hSize hHomSize hD hAffine t.left
  let P := limChart B S hS D hSize hHomSize hD hAffine W
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
            (limitChart hSize hHomSize hD hAffine L hf₀).1.left.hom) := by
          rw [Over.w a.hom.left]
      _ = (m ≫ B.inclusion.map a.hom.left.left) ≫
            B.inclusion.map (limitChart hSize hHomSize hD hAffine L hf₀).1.left.hom := by
          rw [Functor.map_comp, Category.assoc]
      _ = B.inclusion.map μ.left ≫
            B.inclusion.map (limitChart hSize hHomSize hD hAffine L hf₀).1.left.hom :=
          congrArg (· ≫ _) hm
      _ = B.inclusion.map P.1.left.hom :=
          (Functor.map_comp B.inclusion _ _).symm.trans (congrArg B.inclusion.map (Over.w μ)))
  have hmS : mS ≫ a.hom.left = μ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    show B.inclusion.map (B.inclusion.preimage m) ≫ _ = _
    rw [Functor.map_preimage]
    exact hm
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk mS ?_)⟩
  rwa [← CostructuredArrow.w a.hom, ← Category.assoc, ← Functor.map_comp, hmS]

/-- **An affine étale chart over the limit of the chart system is dominated by the base change
of an affine étale chart of a stage**, factoring through the chart system, whose image at that
stage contains the image of a given point. -/
theorem exists_stage_chart
    {A : SmallEtale B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1}
    (a : A ⟶ limitChart hSize hHomSize hD hAffine L hf₀)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left))
    (w : (BigFppfOver.toScheme B S hS).obj A.1.left) :
    ∃ (t : Over i₀) (Z : BigFppfOver B S hS) (ν : Z ⟶ C.siteDiagram.obj t)
      (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      Nonempty (limChart B S hS D hSize hHomSize hD hAffine (stageChartOf hD hf₀ ν hν) ⟶ A) ∧
      (BigFppfOver.toScheme B S hS).map (L.cone.π.app t)
          ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map a) w) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map ν) := by
  have : ∀ {j k : Over i₀} (g : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom
      (C.schemeDiagram.map g) := fun g => C.isAffineHom_map g
  have : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  let α : (BigFppfOver.toScheme B S hS).obj A.1.left ⟶
      ((BigFppfOver.toScheme B S hS).mapCone L.cone).pt :=
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map a)
  have : Etale α := SmallEtale.etale_map B S hS _ a
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
    nonempty_limChart_stageChartOf_hom hSize hHomSize hD hAffine L hf₀ a ν hνet q ψ hpb κ hκ,
    u', hνu'⟩

end StageCharts

/-! ### Covering a stage by charts -/

section Cover

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  (C : AffineChartSystem B S hS i₀ D U₀ f₀)

variable (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

/-- **Charts of the stages covering a member of the chart system cover the stage**, when the
chart `U₀` of the distinguished stage is surjective on points. -/
theorem pointsCover_of_chartSystem_cover
    (hcover : ∀ y₀ : points B S hS (D.obj i₀), y₀ ∈ Set.range (pointsMap B S hS _ f₀))
    {s' : Over i₀} {K : Type} {t : K → Over i₀} (g : ∀ k, s' ⟶ t k)
    {Z : K → BigFppfOver B S hS} (ν : ∀ k, Z k ⟶ C.siteDiagram.obj (t k))
    (hν : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (ν k)))
    (hcov : ∀ c' : (BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj s'), ∃ k,
      (BigFppfOver.toScheme B S hS).map (C.siteDiagram.map (g k)) c' ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (ν k))) :
    PointsCover (fun k => (smallBaseChange B S hS (stageTransition B S hS D hD (g k).left)
      (rep_stageTransition B S hS D hD hAffine (g k).left)).obj
        (stageChartOf hD hf₀ (ν k) (hν k))) := by
  intro y
  obtain ⟨z, hz⟩ := hcover (pointsMap B S hS _ (D.map s'.hom) y)
  obtain ⟨q, hq₁, -⟩ := exists_point_of_isPullback_presheaf B S hS (C.isPullback s') y z hz.symm
  obtain ⟨k, ζ, hζ⟩ := hcov (pointsToScheme B S hS (C.siteDiagram.obj s') q)
  obtain ⟨ζ', rfl⟩ := surjective_pointsToScheme B S hS (Z k) ζ
  have key : pointsMap B S hS _ (yoneda.map (ν k)) ζ' =
      pointsMap B S hS _ (yoneda.map (C.siteDiagram.map (g k))) q := by
    apply injective_pointsToScheme
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsMap_yoneda, hζ]
  have hw : pointsMap B S hS _ (stageChartOf hD hf₀ (ν k) (hν k)).1.hom ζ' =
      pointsMap B S hS _ (stageTransition B S hS D hD (g k).left).hom y := by
    show pointsMap B S hS _ (yoneda.map (ν k) ≫ C.stageMap (t k)) ζ' =
      pointsMap B S hS _ (D.map (g k).left) y
    rw [pointsMap_comp_apply, key, ← pointsMap_comp_apply, C.stageMap_naturality,
      pointsMap_comp_apply]
    exact congrArg (pointsMap B S hS _ (D.map (g k).left)) hq₁
  obtain ⟨r, hr, -⟩ := exists_point_of_isPullback_presheaf B S hS
    ((rep_stageTransition B S hS D hD hAffine (g k).left).isPullback
      (stageChartOf hD hf₀ (ν k) (hν k)).1.hom) y ζ' hw.symm
  exact ⟨k, r, hr⟩

end Cover

/-! ### Finitely many trivializing charts of the stages -/

section Finite

variable {B S hS D} {i₀ : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge)
  (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f₀)

/-- The preimage of the range of an étale morphism under any morphism to its target is open. -/
private theorem isOpen_preimage_range_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f] : IsOpen (g ⁻¹' Set.range f) :=
  f.isOpenMap.isOpen_range.preimage g.continuous

/-- **Finitely many affine étale charts of stages, factoring through the chart system, whose base
changes to the limit carry frames and whose images cover the limit of the chart system.** -/
theorem exists_finite_frame_stage_charts {P : ℕ → Prop}
    {E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2}
    (hE : HasLocalFrames P E) :
    ∃ (K : Type) (_ : Fintype K) (t : K → Over i₀) (Z : K → BigFppfOver B S hS)
      (ν : ∀ k, Z k ⟶ C.siteDiagram.obj (t k))
      (hν : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (ν k))),
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z k))) ∧
      (∀ k, ∃ n, P n ∧ ∃ e : Fin n → (sval E).obj (op (limChart B S hS D hSize hHomSize hD
        hAffine (stageChartOf hD hf₀ (ν k) (hν k)))), IsFrame (sval E) e) ∧
      ∀ u : (BigFppfOver.toScheme B S hS).obj L.cone.pt, ∃ k,
        (BigFppfOver.toScheme B S hS).map (L.cone.π.app (t k)) u ∈
          Set.range ((BigFppfOver.toScheme B S hS).map (ν k)) := by
  classical
  have hdata : ∀ u : (BigFppfOver.toScheme B S hS).obj L.cone.pt,
      ∃ (t : Over i₀) (Z : BigFppfOver B S hS) (ν : Z ⟶ C.siteDiagram.obj t)
        (hν : Etale ((BigFppfOver.toScheme B S hS).map ν)),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
        (∃ n, P n ∧ ∃ e : Fin n → (sval E).obj (op (limChart B S hS D hSize hHomSize hD
          hAffine (stageChartOf hD hf₀ ν hν))), IsFrame (sval E) e) ∧
        (BigFppfOver.toScheme B S hS).map (L.cone.π.app t) u ∈
          Set.range ((BigFppfOver.toScheme B S hS).map ν) := by
    intro u
    obtain ⟨A, a, w, hA, hw, n, hn, e, he⟩ :=
      exists_affine_frame_chart hE (limitChart hSize hHomSize hD hAffine L hf₀) u
    obtain ⟨t, Z, ν, hν, hZ, ⟨φ⟩, hr⟩ := exists_stage_chart hSize hHomSize hD hAffine L hf₀ a hA w
    rw [hw] at hr
    exact ⟨t, Z, ν, hν, hZ, ⟨n, hn, _, he.restrict φ⟩, hr⟩
  choose t Z ν hν hZ hfr hr using hdata
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := L.isAffine_pt
  let O : (BigFppfOver.toScheme B S hS).obj L.cone.pt →
      Set ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := fun u =>
    (BigFppfOver.toScheme B S hS).map (L.cone.π.app (t u)) ⁻¹'
      Set.range ((BigFppfOver.toScheme B S hS).map (ν u))
  have hO : ∀ u, IsOpen (O u) := fun u => by
    have := hν u
    exact isOpen_preimage_range_of_etale _ _
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun u _ => Set.mem_iUnion.2 ⟨u, hr u⟩)
  let σ := F.equivFin.symm
  refine ⟨Fin F.card, inferInstance, fun k => t (σ k).1, fun k => Z (σ k).1, fun k => ν (σ k).1,
    fun k => hν (σ k).1, fun k => hZ (σ k).1, fun k => hfr (σ k).1, fun u => ?_⟩
  obtain ⟨k, hk, hu⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ u))
  obtain ⟨k', hk'⟩ := σ.surjective ⟨k, hk⟩
  have key : ∀ x : F, x = ⟨k, hk⟩ → (BigFppfOver.toScheme B S hS).map (L.cone.π.app (t x.1)) u ∈
      Set.range ((BigFppfOver.toScheme B S hS).map (ν x.1)) := by
    rintro x rfl
    exact hu
  exact ⟨k', key (σ k') hk'⟩

/-- **At a later stage the member of the chart system is covered by the images of finitely many
étale charts of stages whose images cover the limit**, by Stacks 01Z4-type compactness
(Mathlib's `AlgebraicGeometry.exists_map_eq_top`). -/
theorem exists_stage_cover_of_finite {K : Type} [Finite K] {t : K → Over i₀}
    {Z : K → BigFppfOver B S hS} (ν : ∀ k, Z k ⟶ C.siteDiagram.obj (t k))
    (hν : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (ν k)))
    (hcover : ∀ u : (BigFppfOver.toScheme B S hS).obj L.cone.pt, ∃ k,
      (BigFppfOver.toScheme B S hS).map (L.cone.π.app (t k)) u ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (ν k))) :
    ∃ (s' : Over i₀) (g : ∀ k, s' ⟶ t k),
      ∀ c' : (BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj s'), ∃ k,
        (BigFppfOver.toScheme B S hS).map (C.siteDiagram.map (g k)) c' ∈
          Set.range ((BigFppfOver.toScheme B S hS).map (ν k)) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (Discrete.functor t)
  let e : ∀ k, c.pt ⟶ t k := fun k => c.π.app ⟨k⟩
  have hopen : ∀ k, IsOpen ((BigFppfOver.toScheme B S hS).map (C.siteDiagram.map (e k)) ⁻¹'
      Set.range ((BigFppfOver.toScheme B S hS).map (ν k))) := fun k => by
    have := hν k
    exact isOpen_preimage_range_of_etale _ _
  let Oo : (C.schemeDiagram.obj c.pt).Opens :=
    ⟨⋃ k, (BigFppfOver.toScheme B S hS).map (C.siteDiagram.map (e k)) ⁻¹'
      Set.range ((BigFppfOver.toScheme B S hS).map (ν k)), isOpen_iUnion hopen⟩
  have : ∀ {j k : Over i₀} (g : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom
      (C.schemeDiagram.map g) := fun g => C.isAffineHom_map g
  have : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  have hU : ((BigFppfOver.toScheme B S hS).mapCone L.cone).π.app c.pt ⁻¹ᵁ Oo = ⊤ := by
    refine eq_top_iff.2 (fun u _ => ?_)
    obtain ⟨k, hk⟩ := hcover u
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    have hw : L.cone.π.app c.pt ≫ C.siteDiagram.map (e k) = L.cone.π.app (t k) :=
      L.cone.w (e k)
    show (BigFppfOver.toScheme B S hS).map (C.siteDiagram.map (e k))
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app c.pt) u) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (ν k))
    rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hw]
  obtain ⟨s', e', he'⟩ := exists_map_eq_top C.schemeDiagram _ L.schemeIsLimit Oo hU
  refine ⟨s', fun k => e' ≫ e k, fun c' => ?_⟩
  have hc' : (C.schemeDiagram.map e') c' ∈ Oo := by
    show c' ∈ C.schemeDiagram.map e' ⁻¹ᵁ Oo
    rw [he']
    trivial
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hc'
  refine ⟨k, ?_⟩
  rwa [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply]

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
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
    (hE : HasLocalFrames P E) :
    ∃ (i : I) (M : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2) (K : Type) (_ : Fintype K)
      (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD i).1) (n : K → ℕ),
      (∀ k, P (n k)) ∧ PointsCover W ∧
      (∀ k, ∃ e : Fin (n k) → (sval M).obj (op (W k)), IsFrame (sval M) e) ∧
      Nonempty (E ≅ (modulePullback B S hS
        (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj M) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : CompactSpace (points B S hS (D.obj i₀)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ (hD i₀)).mp (hQc i₀)
  obtain ⟨Z₀, c, hZ₀, hc, hcov⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS (D.obj i₀) (hD i₀) isCompact_univ
  let U₀ : BigAffineFppf B S hS := ⟨Z₀, hZ₀⟩
  let f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀ := c
  let C := affineChartSystem B S hS i₀ D U₀ f₀ hAffine
  let L := C.limitBridge hSize hHomSize
  obtain ⟨K, _, t, Z, ν, hν, hZaff, hfr, hcover⟩ :=
    exists_finite_frame_stage_charts hSize hHomSize hD hAffine L hc hE
  obtain ⟨s', g, hcov'⟩ := exists_stage_cover_of_finite L ν hν hcover
  let W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD s'.left).1 := fun k =>
    (smallBaseChange B S hS (stageTransition B S hS D hD (g k).left)
      (rep_stageTransition B S hS D hD hAffine (g k).left)).obj (stageChartOf hD hc (ν k) (hν k))
  have hW : PointsCover W :=
    pointsCover_of_chartSystem_cover hD hAffine C hc (fun y => hcov (Set.mem_univ y)) g ν hν hcov'
  have hWaff : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (W k).1.left) := fun k =>
    isAffine_smallBaseChange_obj B S hS (stageTransition B S hS D hD (g k).left)
      (rep_stageTransition B S hS D hD hAffine (g k).left) (hAffine (g k).left)
      (stageChartOf hD hc (ν k) (hν k)) (hZaff k)
  have hWqc : ∀ k, IsQuasiCompactSpace B S hS (yoneda.obj (W k).1.left) := fun k =>
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hWaff k)
  have hWqs : ∀ k, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (W k).1.left) := fun k => by
    have := hWaff k
    exact isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ _ inferInstance
  choose n hn e he using hfr
  obtain ⟨s, M, hM, hiso⟩ := exists_stage_model_of_frames B S hS hZ D hSize hHomSize hD hAffine
    hQc hQs (j := s'.left) (W := W) hWqc hWqs hW E
    (e := fun k a => res (sval E) (limChartTransition B S hS D hSize hHomSize hD hAffine (g k).left
      (stageChartOf hD hc (ν k) (hν k))) (e k a))
    (fun k => (he k).restrict _)
  exact ⟨s.left, M, K, inferInstance, fun k => laterStageChart B S hS D hD hAffine (W k) s, n, hn,
    pointsCover_smallBaseChange _ _ hW, hM, hiso⟩

end Descent

end AlgebraicGeometry.Space
