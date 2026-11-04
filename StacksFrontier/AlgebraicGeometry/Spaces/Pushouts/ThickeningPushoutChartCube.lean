module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueCube
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangePushout

/-!
# The Milnor cube of rings over an affine chart diagram of `V' ⟶ Y'`

In the situation of Stacks 08KV — a thickening `i : X ⟶ X'`, an affine `f : X ⟶ Y`, the pushout
`Y' = Y ⨿_X X'` and a morphism `g : V' ⟶ Y'` — let `d` be a commuting square of affine étale
scheme charts over `g`, from a chart `W` of `V'` to a chart `W'` of `Y'`. The rings of functions
on the base changes of `W'` to `Y`, `X'` and `X` and of `W` to `V`, `U'` and `U`, with `Γ(W')` and
`Γ(W)`, form a cube of rings for Milnor patching (`Stacks.Pushout.IsMilnorCube`): the bottom face
is the fibre product `Γ(W') = Γ(W'_Y) ×_{Γ(W'_X)} Γ(W'_{X'})` of Stacks 07VX with
`Γ(W'_{X'}) ⟶ Γ(W'_X)` surjective, and the three faces through `Γ(W') ⟶ Γ(W)` are pushouts
because `W_V = W ×_{W'} W'_Y` and so on.

## Main results

* `AlgebraicGeometry.Space.PushoutModules.isMilnorCube_chart`: the cube.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.PushoutModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
    {V' : AlgebraicSpaces B S hS} (g : V' ⟶ pushout i f)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-! ### Representability of the legs -/

include hi hf in
/-- The leg `Y ⟶ Y'` of the pushout is representable by schemes. -/
theorem rep_inr : yoneda.relativelyRepresentable (pushout.inr i f).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_pushout_inr i f hi hf)

include hi hf in
/-- The leg `X' ⟶ Y'` of the pushout is representable by schemes. -/
theorem rep_inl : yoneda.relativelyRepresentable (pushout.inl i f).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_pushout_inl i f hi hf)

include hi hf in
/-- The affine morphism `f : X ⟶ Y` is representable by schemes. -/
theorem rep_f : yoneda.relativelyRepresentable f.hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ hf

include hi hf in
/-- The composite `X ⟶ X' ⟶ Y'` is affine. -/
theorem isAffineHom_i_inl : IsAffineHom B S hS (i ≫ pushout.inl i f).hom :=
  isAffineHom_comp B S hS _ _ (isAffineHom_of_isThickeningHom B S hS i hi)
    (isAffineHom_pushout_inl i f hi hf)

include hi hf in
/-- The composite `X ⟶ X' ⟶ Y'` is representable by schemes. -/
theorem rep_i_inl : yoneda.relativelyRepresentable (i ≫ pushout.inl i f).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_i_inl i f hi hf)

include hi hf in
/-- The composite `X ⟶ Y ⟶ Y'` is representable by schemes. -/
theorem rep_f_inr : yoneda.relativelyRepresentable (f ≫ pushout.inr i f).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (by
    rw [← pushout.condition]
    exact isAffineHom_i_inl i f hi hf)

/-! ### The three cartesian squares over `g` -/

/-- The base change `V = Y ×_{Y'} V'` of `g` along `Y ⟶ Y'` is a pullback square. -/
theorem isPullback_target :
    IsPullback (pullback.fst (pushout.inr i f) g) (targetRestriction i f g) (pushout.inr i f) g :=
  IsPullback.of_hasPullback _ _

/-- The base change `U' = X' ×_{Y'} V'` of `g` along `X' ⟶ Y'` is a pullback square. -/
theorem isPullback_ambient :
    IsPullback (pullback.fst (pushout.inl i f) g) (ambientRestriction i f g) (pushout.inl i f) g :=
  IsPullback.of_hasPullback _ _

/-- The square formed by `U = X ×_{Y'} V'`, `U ⟶ V ⟶ V'`, `X ⟶ X' ⟶ Y'` and `g` is a pullback. -/
theorem isPullback_common :
    IsPullback (pullback.fst (i ≫ pushout.inl i f) g)
      (commonToTarget i f g ≫ targetRestriction i f g) (i ≫ pushout.inl i f) g := by
  rw [commonToTarget_restriction]
  exact IsPullback.of_hasPullback _ _

/-! ### The chart diagrams of the cube -/

variable (d : ChartDiagram B S hS V'.1 (pushout i f).1 g.hom)

/-- The chart diagram `W_V ⟶ W'_Y` over `V ⟶ Y`. -/
abbrev cubeTargetDiagram :=
  cartesianChartDiagram B S hS (isPullback_target i f g) (rep_targetRestriction i f g hi hf)
    (rep_inr i f hi hf) d

/-- The chart diagram `W_{U'} ⟶ W'_{X'}` over `U' ⟶ X'`. -/
abbrev cubeAmbientDiagram :=
  cartesianChartDiagram B S hS (isPullback_ambient i f g) (rep_ambientRestriction i f g hi hf)
    (rep_inl i f hi hf) d

/-- The chart diagram `W_U ⟶ W'_X` over `U ⟶ X`. -/
abbrev cubeCommonDiagram :=
  cartesianChartDiagram B S hS (isPullback_common i f g) (rep_commonTargetComp i f g hi hf)
    (rep_i_inl i f hi hf) d

/-! ### The three faces through `Γ(W') ⟶ Γ(W)` -/

/-- For affine charts, `Γ(W_V)` is the pushout of `Γ(W) ⟵ Γ(W') ⟶ Γ(W'_Y)`. -/
theorem cube_pushD (hW : IsAffine (chartScheme d.U)) (hWy : IsAffine (chartScheme d.V)) :
    IsPushout (CommRingCat.ofHom (chartDiagramRestrict B S hS g d))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS (pushout.inr i f) (rep_inr i f hi hf) d.V))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS (targetRestriction i f g)
        (rep_targetRestriction i f g hi hf) d.U))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS _ (cubeTargetDiagram i f g hi hf d))) :=
  isPushout_cartesianChartDiagram B S hS _ _ _ d hW hWy
    (isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_pushout_inr i f hi hf) d.V hWy)

/-- For affine charts, `Γ(W_{U'})` is the pushout of `Γ(W) ⟵ Γ(W') ⟶ Γ(W'_{X'})`. -/
theorem cube_pushC' (hW : IsAffine (chartScheme d.U)) (hWy : IsAffine (chartScheme d.V)) :
    IsPushout (CommRingCat.ofHom (chartDiagramRestrict B S hS g d))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS (pushout.inl i f) (rep_inl i f hi hf) d.V))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS (ambientRestriction i f g)
        (rep_ambientRestriction i f g hi hf) d.U))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS _ (cubeAmbientDiagram i f g hi hf d))) :=
  isPushout_cartesianChartDiagram B S hS _ _ _ d hW hWy
    (isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_pushout_inl i f hi hf) d.V hWy)

/-- For affine charts, `Γ(W_U)` is the pushout of `Γ(W) ⟵ Γ(W') ⟶ Γ(W'_X)`, with the maps
restricting along the composites over `X ⟶ X' ⟶ Y'` and `U ⟶ V ⟶ V'`. -/
theorem cube_pushC_raw (hW : IsAffine (chartScheme d.U)) (hWy : IsAffine (chartScheme d.V)) :
    IsPushout (CommRingCat.ofHom (chartDiagramRestrict B S hS g d))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS (i ≫ pushout.inl i f)
        (rep_i_inl i f hi hf) d.V))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS
        (commonToTarget i f g ≫ targetRestriction i f g) (rep_commonTargetComp i f g hi hf) d.U))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS _ (cubeCommonDiagram i f g hi hf d))) :=
  isPushout_cartesianChartDiagram B S hS _ _ _ d hW hWy
    (isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_i_inl i f hi hf) d.V hWy)

/-! ### The ring maps of the cube -/

variable (W : SmallEtale B S hS V'.1)

/-- The restriction from `W_V` to `W_U`. -/
abbrev cubeED := cubeTargetRestrict (commonToTarget i f g) (targetRestriction i f g)
  (rep_commonToTarget i f g hi hf) (rep_targetRestriction i f g hi hf)
  (rep_commonTargetComp i f g hi hf) W

/-- The restriction from `W_{U'}` to `W_U`. -/
abbrev cubeEC' := cubeAmbientRestrict (commonToTarget i f g) (targetRestriction i f g)
  (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)
  (rep_commonToAmbient i f g hi hf) (rep_ambientRestriction i f g hi hf)
  (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf) W

variable (Wy : SmallEtale B S hS (pushout i f).1)

/-- The restriction from `W'_Y` to `W'_X`. -/
abbrev cubeTB := cubeAmbientRestrict i (pushout.inl i f) f (pushout.inr i f)
  pushout.condition.symm (rep_f i f hi hf) (rep_inr i f hi hf) (rep_i_inl i f hi hf)
  (rep_f_inr i f hi hf) Wy

/-- The restriction from `W'_{X'}` to `W'_X`. -/
abbrev cubeTA' :=
  cubeTargetRestrict i (pushout.inl i f) hi.isClosedImmersion.rep (rep_inl i f hi hf)
    (rep_i_inl i f hi hf) Wy

/-- The two restrictions `Γ(W) ⟶ Γ(W_U)`, through `Γ(W_V)` and through `Γ(W_{U'})`, agree. -/
theorem cube_top :
    (cubeED i f g hi hf W).comp (baseChangeChartRestrict B S hS (targetRestriction i f g)
        (rep_targetRestriction i f g hi hf) W) =
      (cubeEC' i f g hi hf W).comp (baseChangeChartRestrict B S hS (ambientRestriction i f g)
        (rep_ambientRestriction i f g hi hf) W) :=
  (cubeTargetRestrict_comp _ _ _ _ _ W).trans (cubeAmbientRestrict_comp _ _ _ _ _ _ _ _ _ W).symm

/-- For affine charts, `Γ(W_U)` is the pushout of `Γ(W) ⟵ Γ(W') ⟶ Γ(W'_X)`, with the maps
factored through `Γ(W'_Y)` and `Γ(W_V)`. -/
theorem cube_pushC (hW : IsAffine (chartScheme d.U)) (hWy : IsAffine (chartScheme d.V)) :
    IsPushout (CommRingCat.ofHom (chartDiagramRestrict B S hS g d))
      (CommRingCat.ofHom ((cubeTB i f hi hf d.V).comp
        (baseChangeChartRestrict B S hS (pushout.inr i f) (rep_inr i f hi hf) d.V)))
      (CommRingCat.ofHom ((cubeED i f g hi hf d.U).comp
        (baseChangeChartRestrict B S hS (targetRestriction i f g)
          (rep_targetRestriction i f g hi hf) d.U)))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS _ (cubeCommonDiagram i f g hi hf d))) := by
  rw [cubeAmbientRestrict_comp, cubeTargetRestrict_comp]
  exact cube_pushC_raw i f g hi hf d hW hWy

/-! ### The base of the cube: the fibre product of Stacks 07VX -/

/-- The chart `W'_X ⟶ W'_{X'}` over `i`. -/
abbrev cubeIDiagram :=
  targetDiagram i (pushout.inl i f) hi.isClosedImmersion.rep (rep_inl i f hi hf)
    (rep_i_inl i f hi hf) Wy

/-- The chart `W'_X ⟶ W'_Y` over `f`. -/
abbrev cubeFDiagram :=
  ambientDiagram i (pushout.inl i f) f (pushout.inr i f) pushout.condition.symm
    (rep_f i f hi hf) (rep_inr i f hi hf) (rep_i_inl i f hi hf) (rep_f_inr i f hi hf) Wy

/-- The chart `W'_X` is the base change of `W'_{X'}` along `i`. -/
theorem cube_isPullback_i :
    IsPullback (yoneda.map (cubeIDiagram i f hi hf Wy).g) ((rep_i_inl i f hi hf).fst Wy.1.hom)
      ((rep_inl i f hi hf).fst Wy.1.hom) i.hom := by
  have e : yoneda.map (cubeIDiagram i f hi hf Wy).g ≫
      yoneda.map ((rep_inl i f hi hf).snd Wy.1.hom) =
      yoneda.map ((rep_i_inl i f hi hf).snd Wy.1.hom) :=
    (yoneda.map_comp _ _).symm.trans (congrArg (fun k => yoneda.map k)
      (targetDiagram_g_comp _ _ _ _ _ Wy))
  have hbig := ((rep_i_inl i f hi hf).isPullback Wy.1.hom).flip
  rw [← e] at hbig
  exact IsPullback.of_right hbig (cubeIDiagram i f hi hf Wy).comm.symm
    ((rep_inl i f hi hf).isPullback Wy.1.hom).flip

/-- The chart `W'_X` is the base change of `W'_Y` along `f`. -/
theorem cube_isPullback_f :
    IsPullback (yoneda.map (cubeFDiagram i f hi hf Wy).g) ((rep_i_inl i f hi hf).fst Wy.1.hom)
      ((rep_inr i f hi hf).fst Wy.1.hom) f.hom := by
  have e : yoneda.map (cubeFDiagram i f hi hf Wy).g ≫
      yoneda.map ((rep_inr i f hi hf).snd Wy.1.hom) =
      yoneda.map ((rep_i_inl i f hi hf).snd Wy.1.hom) :=
    (yoneda.map_comp _ _).symm.trans (congrArg (fun k => yoneda.map k)
      (ambientDiagram_g_comp _ _ _ _ _ _ _ _ _ Wy))
  have e' : (i ≫ pushout.inl i f).hom = f.hom ≫ (pushout.inr i f).hom :=
    congrArg (fun k : X ⟶ pushout i f => k.hom) (pushout.condition (f := i) (g := f))
  have hbig₀ := ((rep_i_inl i f hi hf).isPullback Wy.1.hom).flip
  rw [← e] at hbig₀
  have hbig : IsPullback (yoneda.map (cubeFDiagram i f hi hf Wy).g ≫
      yoneda.map ((rep_inr i f hi hf).snd Wy.1.hom)) ((rep_i_inl i f hi hf).fst Wy.1.hom)
      Wy.1.hom (f.hom ≫ (pushout.inr i f).hom) :=
    IsPullback.of_iso hbig₀ (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (e'.trans (Category.id_comp _).symm))
  exact IsPullback.of_right hbig (cubeFDiagram i f hi hf Wy).comm.symm
    ((rep_inr i f hi hf).isPullback Wy.1.hom).flip

/-- The two routes `W'_X ⟶ W'` through `W'_{X'}` and through `W'_Y` agree. -/
theorem cube_hw₀ : (cubeIDiagram i f hi hf Wy).g ≫ (rep_inl i f hi hf).snd Wy.1.hom =
    (cubeFDiagram i f hi hf Wy).g ≫ (rep_inr i f hi hf).snd Wy.1.hom :=
  (targetDiagram_g_comp _ _ _ _ _ Wy).trans (ambientDiagram_g_comp _ _ _ _ _ _ _ _ _ Wy).symm

/-! ### The two side faces over `Γ(W_U)` -/

section Sides

/-- The two routes `W_U ⟶ W'_Y`. -/
theorem cube_sideD_g :
    (targetDiagram (commonToTarget i f g) (targetRestriction i f g)
        (rep_commonToTarget i f g hi hf) (rep_targetRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) d.U).g ≫ (cubeTargetDiagram i f g hi hf d).g =
      (cubeCommonDiagram i f g hi hf d).g ≫ (cubeFDiagram i f hi hf d.V).g := by
  refine (rep_inr i f hi hf).hom_ext ?_ ?_
  · have hct : (commonToTarget i f g).hom ≫ (pullback.fst (pushout.inr i f) g).hom =
        (pullback.fst (i ≫ pushout.inl i f) g).hom ≫ f.hom :=
      congrArg (fun k => k.hom) (commonToTarget_fst i f g)
    have l1 := cartesianChartDiagram_g_fst B S hS (isPullback_target i f g)
      (rep_targetRestriction i f g hi hf) (rep_inr i f hi hf) d
    have l2 := (targetDiagram (commonToTarget i f g) (targetRestriction i f g)
        (rep_commonToTarget i f g hi hf) (rep_targetRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) d.U).comm
    have r1 := cartesianChartDiagram_g_fst B S hS (isPullback_common i f g)
      (rep_commonTargetComp i f g hi hf) (rep_i_inl i f hi hf) d
    have r2 := (cubeFDiagram i f hi hf d.V).comm
    refine ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) l1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) l2.symm).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) hct))))))).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) r2.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r1))))).symm
  · have l1 := cartesianChartDiagram_g_snd B S hS (isPullback_target i f g)
      (rep_targetRestriction i f g hi hf) (rep_inr i f hi hf) d
    have r1 := cartesianChartDiagram_g_snd B S hS (isPullback_common i f g)
      (rep_commonTargetComp i f g hi hf) (rep_i_inl i f hi hf) d
    have l2 := targetDiagram_g_comp (commonToTarget i f g) (targetRestriction i f g)
        (rep_commonToTarget i f g hi hf) (rep_targetRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) d.U
    have r2 := ambientDiagram_g_comp i (pushout.inl i f) f (pushout.inr i f)
      pushout.condition.symm (rep_f i f hi hf) (rep_inr i f hi hf) (rep_i_inl i f hi hf)
      (rep_f_inr i f hi hf) d.V
    exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) l1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ d.g) l2)))).trans
      (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r2).trans r1)).symm)

/-- The two routes `W_U ⟶ W'_{X'}`. -/
theorem cube_sideC'_g :
    (ambientDiagram (commonToTarget i f g) (targetRestriction i f g)
        (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)
        (rep_commonToAmbient i f g hi hf) (rep_ambientRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf) d.U).g ≫
        (cubeAmbientDiagram i f g hi hf d).g =
      (cubeCommonDiagram i f g hi hf d).g ≫ (cubeIDiagram i f hi hf d.V).g := by
  refine (rep_inl i f hi hf).hom_ext ?_ ?_
  · have hct : (commonToAmbient i f g).hom ≫ (pullback.fst (pushout.inl i f) g).hom =
        (pullback.fst (i ≫ pushout.inl i f) g).hom ≫ i.hom :=
      congrArg (fun k => k.hom) (commonToAmbient_fst i f g)
    have l1 := cartesianChartDiagram_g_fst B S hS (isPullback_ambient i f g)
      (rep_ambientRestriction i f g hi hf) (rep_inl i f hi hf) d
    have l2 := (ambientDiagram (commonToTarget i f g) (targetRestriction i f g)
        (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)
        (rep_commonToAmbient i f g hi hf) (rep_ambientRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf) d.U).comm
    have r1 := cartesianChartDiagram_g_fst B S hS (isPullback_common i f g)
      (rep_commonTargetComp i f g hi hf) (rep_i_inl i f hi hf) d
    have r2 := (cubeIDiagram i f hi hf d.V).comm
    refine ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) l1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) l2.symm).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) hct))))))).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) r2.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r1))))).symm
  · have l1 := cartesianChartDiagram_g_snd B S hS (isPullback_ambient i f g)
      (rep_ambientRestriction i f g hi hf) (rep_inl i f hi hf) d
    have r1 := cartesianChartDiagram_g_snd B S hS (isPullback_common i f g)
      (rep_commonTargetComp i f g hi hf) (rep_i_inl i f hi hf) d
    have l2 := ambientDiagram_g_comp (commonToTarget i f g) (targetRestriction i f g)
        (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)
        (rep_commonToAmbient i f g hi hf) (rep_ambientRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf) d.U
    have r2 := targetDiagram_g_comp i (pushout.inl i f) hi.isClosedImmersion.rep
      (rep_inl i f hi hf) (rep_i_inl i f hi hf) d.V
    exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) l1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ d.g) l2)))).trans
      (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r2).trans r1)).symm)

/-- The two restrictions `Γ(W'_Y) ⟶ Γ(W_U)`, through `Γ(W_V)` and through `Γ(W'_X)`, agree. -/
theorem cube_sideD :
    (cubeED i f g hi hf d.U).comp
        (chartDiagramRestrict B S hS _ (cubeTargetDiagram i f g hi hf d)) =
      (chartDiagramRestrict B S hS _ (cubeCommonDiagram i f g hi hf d)).comp
        (cubeTB i f hi hf d.V) := by
  show ((BigFppfOver.toScheme B S hS).map (targetDiagram (commonToTarget i f g)
        (targetRestriction i f g) (rep_commonToTarget i f g hi hf)
        (rep_targetRestriction i f g hi hf) (rep_commonTargetComp i f g hi hf)
        d.U).g).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (cubeTargetDiagram i f g hi hf d).g).appTop.hom =
    ((BigFppfOver.toScheme B S hS).map (cubeCommonDiagram i f g hi hf d).g).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (cubeFDiagram i f hi hf d.V).g).appTop.hom
  exact (appTop_hom_comp _ _).trans ((congrArg (fun k => ((BigFppfOver.toScheme B S hS).map
    k).appTop.hom) (cube_sideD_g i f g hi hf d)).trans (appTop_hom_comp _ _).symm)

/-- The two restrictions `Γ(W'_{X'}) ⟶ Γ(W_U)`, through `Γ(W_{U'})` and through `Γ(W'_X)`,
agree. -/
theorem cube_sideC' :
    (cubeEC' i f g hi hf d.U).comp
        (chartDiagramRestrict B S hS _ (cubeAmbientDiagram i f g hi hf d)) =
      (chartDiagramRestrict B S hS _ (cubeCommonDiagram i f g hi hf d)).comp
        (cubeTA' i f hi hf d.V) := by
  show ((BigFppfOver.toScheme B S hS).map (ambientDiagram (commonToTarget i f g)
        (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
        (commonToAmbient_comp_eq i f g)
        (rep_commonToAmbient i f g hi hf) (rep_ambientRestriction i f g hi hf)
        (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf)
        d.U).g).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (cubeAmbientDiagram i f g hi hf d).g).appTop.hom =
    ((BigFppfOver.toScheme B S hS).map (cubeCommonDiagram i f g hi hf d).g).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map (cubeIDiagram i f hi hf d.V).g).appTop.hom
  exact (appTop_hom_comp _ _).trans ((congrArg (fun k => ((BigFppfOver.toScheme B S hS).map
    k).appTop.hom) (cube_sideC'_g i f g hi hf d)).trans (appTop_hom_comp _ _).symm)

end Sides

/-! ### The cube -/

include hi in
/-- For an affine chart `W'`, the restriction `Γ(W'_{X'}) ⟶ Γ(W'_X)` is surjective. -/
theorem cube_surj (hWy : IsAffine (chartScheme d.V)) :
    Function.Surjective (cubeTA' i f hi hf d.V) := by
  have hci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (cubeIDiagram i f hi hf d.V).g) :=
    hi.isClosedImmersion.property ((rep_inl i f hi hf).fst d.V.1.hom)
      ((rep_i_inl i f hi hf).fst d.V.1.hom) (cubeIDiagram i f hi hf d.V).g
      (cube_isPullback_i i f hi hf d.V).flip
  have haff : IsAffine (chartScheme ((smallBaseChange B S hS (pushout.inl i f)
      (rep_inl i f hi hf)).obj d.V)) :=
    isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_pushout_inl i f hi hf) d.V hWy
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X'.obj).obj (cubeIDiagram i f hi hf d.V).V)) := haff
  show Function.Surjective
    ((BigFppfOver.toScheme B S hS).map (cubeIDiagram i f hi hf d.V).g).appTop.hom
  exact Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)

/-- **The rings of functions over an affine chart diagram of `V' ⟶ Y'` form a cube for Milnor
patching.** -/
theorem isMilnorCube_chart (hW : IsAffine (chartScheme d.U)) (hWy : IsAffine (chartScheme d.V)) :
    Stacks.Pushout.IsMilnorCube
      (baseChangeChartRestrict B S hS (pushout.inr i f) (rep_inr i f hi hf) d.V)
      (baseChangeChartRestrict B S hS (pushout.inl i f) (rep_inl i f hi hf) d.V)
      (cubeTB i f hi hf d.V) (cubeTA' i f hi hf d.V)
      (chartDiagramRestrict B S hS g d)
      (chartDiagramRestrict B S hS _ (cubeTargetDiagram i f g hi hf d))
      (chartDiagramRestrict B S hS _ (cubeAmbientDiagram i f g hi hf d))
      (chartDiagramRestrict B S hS _ (cubeCommonDiagram i f g hi hf d))
      (baseChangeChartRestrict B S hS (targetRestriction i f g)
        (rep_targetRestriction i f g hi hf) d.U)
      (baseChangeChartRestrict B S hS (ambientRestriction i f g)
        (rep_ambientRestriction i f g hi hf) d.U)
      (cubeED i f g hi hf d.U) (cubeEC' i f g hi hf d.U) where
  base := by
    have hb := pushout_isPullback_appTop B S hS i f hi hf d.V.1.hom
      ((isEtale_iff_presheaf_of_yoneda B S hS d.V.1.hom).2 d.V.property)
      ((rep_inl i f hi hf).isPullback d.V.1.hom).flip
      ((rep_inr i f hi hf).isPullback d.V.1.hom).flip
      (cube_isPullback_i i f hi hf d.V) (cube_isPullback_f i f hi hf d.V)
      (cube_hw₀ i f hi hf d.V)
    exact hb
  surj := cube_surj i f g hi hf d hWy
  pushD := cube_pushD i f g hi hf d hW hWy
  pushC' := cube_pushC' i f g hi hf d hW hWy
  pushC := cube_pushC i f g hi hf d hW hWy
  top := cube_top i f g hi hf d.U
  sideD := cube_sideD i f g hi hf d
  sideC' := cube_sideC' i f g hi hf d

end AlgebraicGeometry.Space.PushoutModules

end
