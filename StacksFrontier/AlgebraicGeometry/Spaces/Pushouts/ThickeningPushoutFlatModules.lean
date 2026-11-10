module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutChartCube
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIsoOnCoveringCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartDiagramSectionsCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramIsoDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Adjunction.RestrictFullyFaithfulEquivalence

/-!
# Stacks 08KV: flat modules over a pushout along a thickening and an affine morphism

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over `S`,
let `Y' = Y ⨿_X X'` be their pushout (Stacks 07VX) and `g : V' ⟶ Y'` a morphism, with
`V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.  The comparison functor
`𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)` is an equivalence from the quasi-coherent
`𝒪_{V'}`-modules flat over `Y'` onto the triples `(𝒢, ℱ', φ)` of a quasi-coherent `𝒪_V`-module
flat over `Y`, a quasi-coherent `𝒪_{U'}`-module flat over `X'` and an isomorphism
`φ : (U ⟶ V)^*𝒢 ≅ (U ⟶ U')^*ℱ'`.

The quasi-inverse is the gluing functor `(V ⟶ V')_*𝒢 ×_{(U ⟶ V')_*ℱ} (U' ⟶ V')_*ℱ'`, the right
adjoint of the comparison functor (`CategoryTheory.TripleGluing.adjunction`).  On the sections over
an affine étale chart `W` of `V'` mapping to an affine étale chart `W'` of `Y'` the rings of
functions form a Milnor cube over `Γ(W') = Γ(W'_Y) ×_{Γ(W'_X)} Γ(W'_{X'})`
(`AlgebraicGeometry.Space.PushoutModules.isMilnorCube_chart`), and the unit and counit of the
adjunction are the unit and counit of the equivalence of More on Algebra, Lemma 07RW
(`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/ThickeningPushoutGlueCube.lean`): bijective for
modules flat over the base, and the glued module of relatively flat modules is flat.  Such charts
`W` cover `V'`, and their base changes cover `V` and `U'`.

The source writes "`ℱ'` … flat over `X`"; `ℱ'` lives on `U' = X' ×_{Y'} V'`, which maps to `X'`,
so the condition is flatness over `X'`, as in the scheme case Stacks 08KU.

## Main definitions

* `AlgebraicGeometry.Space.PushoutModules.FlatQuasicoherentOver`: quasi-coherent modules on `V'`
  flat over `Y'`.
* `AlgebraicGeometry.Space.PushoutModules.FlatQuasicoherentTriple`: the triples of the tag.
* `AlgebraicGeometry.Space.PushoutModules.flatQuasicoherentTriple_restrict`: the comparison
  functor lands in the triples of the tag.

## Main results

* `AlgebraicGeometry.Space.PushoutModules.isEquivalence_flatRestrictionFunctor`: **Stacks 08KV.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

/-! ### Base changes of the source charts of affine chart diagrams cover -/

/-- **The base changes of the source charts of the affine chart diagrams over `g` cover**: for a
representable `v : Z ⟶ X` and any `g : X ⟶ Y`, the charts `W ×_X Z`, `W` running over the affine
source charts of affine chart diagrams over `g`, cover the final object of the small étale site
of `Z`. -/
theorem coversTop_smallBaseChange_affineChartDiagram {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (v : Z ⟶ X)
    (hv : yoneda.relativelyRepresentable v.hom) :
    (SmallEtale.topology B S hS Z.1).CoversTop
      (fun W : {W : SmallEtale B S hS X.1 // IsAffine (chartScheme W) ∧
          ∃ d : ChartDiagram B S hS X.1 Y.1 g.hom, d.U = W ∧ IsAffine (chartScheme d.V)} =>
        (smallBaseChange B S hS v hv).obj W.1) :=
  GrothendieckTopology.coversTop_obj_subtype (smallBaseChange B S hS v hv)
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)
    (coversTop_smallBaseChange_obj B S hS v hv) _ fun U =>
      ⟨_, generate_affineChartDiagram_mem_topology B S hS g (fun _ => True) (fun _ _ => trivial) U,
        fun W k hk => ⟨hk.1, by
          obtain ⟨d, hd, hV, -⟩ := hk.2
          exact ⟨d, hd, hV⟩⟩⟩

namespace PushoutModules

/-- The quasi-coherent `𝒪_{V'}`-modules flat over `Y'`, for a morphism `g : V' ⟶ Y'`. -/
def FlatQuasicoherentOver {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {V' Y' : AlgebraicSpaces B S hS} (g : V' ⟶ Y') :
    ObjectProperty (Modules.{u, u} B S hS V'.1 V'.2) :=
  fun M => M.IsQuasicoherentOnSite ∧ IsFlatOver B S hS V'.2 g.hom M

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
    {V' : AlgebraicSpaces B S hS} (g : V' ⟶ pushout i f)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-! ### The two categories of the tag -/


/-- The triples of Stacks 08KV: a quasi-coherent `𝒪_V`-module flat over `Y`, a quasi-coherent
`𝒪_{U'}`-module flat over `X'` and an isomorphism of their pullbacks to `U`. -/
def FlatQuasicoherentTriple : ObjectProperty (TripleGluing.Triple
    (modulePullback B S hS (commonToTarget i f g))
    (modulePullback B S hS (commonToAmbient i f g))) :=
  fun T => T.target.IsQuasicoherentOnSite ∧
    IsFlatOver B S hS (targetSpace i f g).2 (pullback.fst (pushout.inr i f) g).hom T.target ∧
    T.ambient.IsQuasicoherentOnSite ∧
    IsFlatOver B S hS (ambientSpace i f g).2 (pullback.fst (pushout.inl i f) g).hom T.ambient

/-- The restriction of a quasi-coherent module flat over `Y'` is a triple of the tag. -/
theorem flatQuasicoherentTriple_restrict (M : Modules.{u, u} B S hS V'.1 V'.2)
    (hM : FlatQuasicoherentOver g M) :
    FlatQuasicoherentTriple i f g ((TripleGluing.restrictFunctor
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
      (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))).obj M) := by
  have hq := hM.1
  have hqt := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (targetRestriction i f g) M hq
  have hqa := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (ambientRestriction i f g) M hq
  exact ⟨hqt, isFlatOver_modulePullback B S hS (isPullback_target i f g).flip M hM.2,
    hqa, isFlatOver_modulePullback B S hS (isPullback_ambient i f g).flip M hM.2⟩

/-! ### Affineness of the base-changed charts -/

include hi hf in
/-- For a thickening `i` and an affine `f`, the composite `U ⟶ V ⟶ V'` of `commonToTarget` and
`targetRestriction` is affine. -/
theorem isAffineHom_commonTargetComp :
    IsAffineHom B S hS ((commonToTarget i f g) ≫ (targetRestriction i f g)).hom := by
  rw [commonToTarget_restriction]
  exact isAffineHom_commonRestriction i f g hi hf

/-- The base changes of an affine chart `d.U` along the three affine maps to `V'` are affine. -/
private theorem isAffine_smallBaseChange_obj_triple (d : ChartDiagram B S hS V'.1 (pushout i f).1
    g.hom) (hU : IsAffine (chartScheme d.U)) :
    IsAffine (chartScheme ((smallBaseChange B S hS _ (rep_targetRestriction i f g hi hf)).obj
      d.U)) ∧
    IsAffine (chartScheme ((smallBaseChange B S hS _ (rep_ambientRestriction i f g hi hf)).obj
      d.U)) ∧
    IsAffine (chartScheme ((smallBaseChange B S hS _ (rep_commonTargetComp i f g hi hf)).obj
      d.U)) :=
  ⟨isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_targetRestriction i f g hi hf) d.U hU,
    isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_ambientRestriction i f g hi hf) d.U hU,
    isAffine_smallBaseChange_obj B S hS _ _ (isAffineHom_commonTargetComp i f g hi hf) d.U hU⟩

/-! ### The glued module of a triple of the tag -/

include hi hf in
/-- **The glued module of a triple of the tag is quasi-coherent and flat over `Y'`.** -/
theorem flatQuasicoherentOver_glue (T : TripleGluing.Triple
    (modulePullback B S hS (commonToTarget i f g)) (modulePullback B S hS (commonToAmbient i f g)))
    (hT : FlatQuasicoherentTriple i f g T) :
    FlatQuasicoherentOver g ((TripleGluing.glueFunctor
      (qV := modulePushforward B S hS (targetRestriction i f g))
      (qA := modulePushforward B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport (commonToAmbient i f g) (ambientRestriction i f g)
      ((commonToTarget i f g) ≫ (targetRestriction i f g))
      (commonToAmbient_comp_eq i f g))).obj T) := by
  have hq := isQuasicoherentOnSite_glue (commonToTarget i f g) (targetRestriction i f g)
    (commonToAmbient i f g) (ambientRestriction i f g)
    (commonToAmbient_comp_eq i f g) T hT.1 hT.2.2.1
    (isAffineHom_targetRestriction i f g hi hf) (isAffineHom_ambientRestriction i f g hi hf)
    (isAffineHom_commonTargetComp i f g hi hf)
  refine ⟨hq, isFlatOver_of_forall_isAffine_chartDiagram B S hS g _ hq fun d hU hV => ?_⟩
  obtain ⟨hWV, hWU', hWU⟩ := isAffine_smallBaseChange_obj_triple i f g hi hf d hU
  have hYV := isAffine_smallBaseChange_obj B S hS _ (rep_inr i f hi hf)
    (isAffineHom_pushout_inr i f hi hf) d.V hV
  have hXV := isAffine_smallBaseChange_obj B S hS _ (rep_inl i f hi hf)
    (isAffineHom_pushout_inl i f hi hf) d.V hV
  have hGflat := (isFlatOverOnChartDiagram_iff_flat_sections B S hS _ T.target hT.1
    (cubeTargetDiagram i f g hi hf d) hWV hYV).1 (hT.2.1 _)
  have hFflat := (isFlatOverOnChartDiagram_iff_flat_sections B S hS _ T.ambient hT.2.2.1
    (cubeAmbientDiagram i f g hi hf d) hWU' hXV).1 (hT.2.2.2 _)
  exact (isFlatOverOnChartDiagram_iff_flat_sections B S hS g _ hq d hU hV).2
    (flat_glue_of_isMilnorCube (commonToTarget i f g) (targetRestriction i f g)
    (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)
    (rep_commonToTarget i f g hf) (rep_targetRestriction i f g hi hf)
    (rep_commonToAmbient i f g hi) (rep_ambientRestriction i f g hi hf)
    (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf) d.U T hT.1
    hT.2.2.1 hWV hWU' hWU
      (isMilnorCube_chart i f g hi hf d hU hV) hGflat hFflat)

/-! ### The unit and the counit -/

include hi hf in
/-- **The unit of the gluing adjunction is an isomorphism at a quasi-coherent module flat over
`Y'`.** -/
theorem isIso_unit_app (M : (FlatQuasicoherentOver g).FullSubcategory) :
    IsIso ((TripleGluing.adjunction (modulePullbackAdjunction B S hS (targetRestriction i f g))
      (modulePullbackAdjunction B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
      (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport_eq_rightComparison (commonToTarget i f g) (targetRestriction i f g)
      (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))).unit.app
      ((FlatQuasicoherentOver g).ι.obj M)) := by
  have hM := M.property
  refine isIso_of_bijective_affineChartDiagram B S hS g _ fun d hU hV => ?_
  obtain ⟨hWV, hWU', hWU⟩ := isAffine_smallBaseChange_obj_triple i f g hi hf d hU
  have hflat := (isFlatOverOnChartDiagram_iff_flat_sections B S hS g
    ((FlatQuasicoherentOver g).ι.obj M) hM.1 d hU hV).1 (hM.2 d)
  exact bijective_squareUnit_app_of_isMilnorCube (commonToTarget i f g) (targetRestriction i f g)
    (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)
    (rep_commonToTarget i f g hf) (rep_targetRestriction i f g hi hf)
    (rep_commonToAmbient i f g hi) (rep_ambientRestriction i f g hi hf)
    (rep_commonTargetComp i f g hi hf) (rep_commonAmbientComp i f g hi hf) d.U hWV hWU' hWU
    ((FlatQuasicoherentOver g).ι.obj M) hM.1 hU
    (isMilnorCube_chart i f g hi hf d hU hV) hflat

include hi hf in
/-- **The counit of the gluing adjunction is an isomorphism at a triple of the tag.** -/
theorem isIso_counit_app (T : (FlatQuasicoherentTriple i f g).FullSubcategory) :
    IsIso ((TripleGluing.adjunction (modulePullbackAdjunction B S hS (targetRestriction i f g))
      (modulePullbackAdjunction B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
      (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport_eq_rightComparison (commonToTarget i f g) (targetRestriction i f g)
      (commonToAmbient i f g) (ambientRestriction i f g)
      (commonToAmbient_comp_eq i f g))).counit.app ((FlatQuasicoherentTriple i f g).ι.obj T)) := by
  have hT : FlatQuasicoherentTriple i f g ((FlatQuasicoherentTriple i f g).ι.obj T) := T.property
  have hglue := (flatQuasicoherentOver_glue i f g hi hf
    ((FlatQuasicoherentTriple i f g).ι.obj T) hT).1
  have : IsIso ((TripleGluing.adjunction
      (modulePullbackAdjunction B S hS (targetRestriction i f g))
      (modulePullbackAdjunction B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
      (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport_eq_rightComparison (commonToTarget i f g) (targetRestriction i f g)
      (commonToAmbient i f g) (ambientRestriction i f g)
      (commonToAmbient_comp_eq i f g))).counit.app
      ((FlatQuasicoherentTriple i f g).ι.obj T)).target := by
    refine isIso_of_bijective_app_of_coversTop_of_isQuasicoherentOnSite B S hS (targetSpace i f g).2
      (coversTop_smallBaseChange_affineChartDiagram g (targetRestriction i f g)
      (rep_targetRestriction i f g hi hf))
      (fun W => isAffine_smallBaseChange_obj B S hS _ _
        (isAffineHom_targetRestriction i f g hi hf) W.1 W.2.1)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (targetRestriction i f g) _ hglue) hT.1 _
      fun W => ?_
    obtain ⟨W, hW, d, rfl, hV⟩ := W
    obtain ⟨hWV, hWU', hWU⟩ := isAffine_smallBaseChange_obj_triple i f g hi hf d hW
    exact bijective_squareCounit_target_app_of_isMilnorCube (commonToTarget i f g)
      (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
      (commonToAmbient_comp_eq i f g) (rep_commonToTarget i f g hf)
      (rep_targetRestriction i f g hi hf) (rep_commonToAmbient i f g hi)
      (rep_ambientRestriction i f g hi hf) (rep_commonTargetComp i f g hi hf)
      (rep_commonAmbientComp i f g hi hf) d.U ((FlatQuasicoherentTriple i f g).ι.obj T) hT.1
      hT.2.2.1 hWV hWU'
      hWU hglue hW (isMilnorCube_chart i f g hi hf d hW hV)
  have : IsIso ((TripleGluing.adjunction
      (modulePullbackAdjunction B S hS (targetRestriction i f g))
      (modulePullbackAdjunction B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
      (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport_eq_rightComparison (commonToTarget i f g) (targetRestriction i f g)
      (commonToAmbient i f g) (ambientRestriction i f g)
      (commonToAmbient_comp_eq i f g))).counit.app
      ((FlatQuasicoherentTriple i f g).ι.obj T)).ambient := by
    refine isIso_of_bijective_app_of_coversTop_of_isQuasicoherentOnSite B S hS
      (ambientSpace i f g).2
      (coversTop_smallBaseChange_affineChartDiagram g (ambientRestriction i f g)
      (rep_ambientRestriction i f g hi hf))
      (fun W => isAffine_smallBaseChange_obj B S hS _ _
        (isAffineHom_ambientRestriction i f g hi hf) W.1 W.2.1)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (ambientRestriction i f g) _ hglue)
      hT.2.2.1 _ fun W => ?_
    obtain ⟨W, hW, d, rfl, hV⟩ := W
    obtain ⟨hWV, hWU', hWU⟩ := isAffine_smallBaseChange_obj_triple i f g hi hf d hW
    exact bijective_squareCounit_ambient_app_of_isMilnorCube (commonToTarget i f g)
      (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
      (commonToAmbient_comp_eq i f g) (rep_commonToTarget i f g hf)
      (rep_targetRestriction i f g hi hf) (rep_commonToAmbient i f g hi)
      (rep_ambientRestriction i f g hi hf) (rep_commonTargetComp i f g hi hf)
      (rep_commonAmbientComp i f g hi hf) d.U ((FlatQuasicoherentTriple i f g).ι.obj T) hT.1
      hT.2.2.1 hWV hWU'
      hWU hglue hW (isMilnorCube_chart i f g hi hf d hW hV)
  exact TripleGluing.isIso_of_isIso_components _

/-! ### The equivalence -/

include hi hf in
/-- **Stacks 08KV, with the pushout given.**  The comparison functor
`𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)` is an equivalence from the quasi-coherent
`𝒪_{V'}`-modules flat over `Y'` onto the triples of the tag; a quasi-inverse is the gluing functor
`(𝒢, ℱ', φ) ↦ (V ⟶ V')_*𝒢 ×_{(U ⟶ V')_*ℱ} (U' ⟶ V')_*ℱ'`.

The functor is written out in the statement, as the lift to the two full subcategories of
`CategoryTheory.TripleGluing.restrictFunctor` at the canonical comparison
`AlgebraicGeometry.Space.PushoutModules.squareOverlap` of the two pullbacks to `U`. -/
theorem isEquivalence_flatRestrictionFunctor_of_hasPushout :
    ((((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
    (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g) (targetRestriction i f g)
    (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))))
      fun M => flatQuasicoherentTriple_restrict i f g M.obj M.property) :
      (FlatQuasicoherentOver g).FullSubcategory ⥤
        (FlatQuasicoherentTriple i f g).FullSubcategory)).IsEquivalence := by
  refine (TripleGluing.adjunction (modulePullbackAdjunction B S hS (targetRestriction i f g))
      (modulePullbackAdjunction B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
      (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport_eq_rightComparison (commonToTarget i f g) (targetRestriction i f g)
      (commonToAmbient i f g) (ambientRestriction i f g)
      (commonToAmbient_comp_eq i f g))).isEquivalence_of_restrictFullyFaithful
    (FlatQuasicoherentOver g).fullyFaithfulι (FlatQuasicoherentTriple i f g).fullyFaithfulι
    (R := ((FlatQuasicoherentOver g).lift ((FlatQuasicoherentTriple i f g).ι ⋙
    (TripleGluing.glueFunctor (qV := modulePushforward B S hS (targetRestriction i f g))
      (qA := modulePushforward B S hS (ambientRestriction i f g))
      (modulePullbackAdjunction B S hS (commonToTarget i f g))
      (modulePullbackAdjunction B S hS (commonToAmbient i f g))
      (modulePushforwardCompIso B S hS (commonToTarget i f g) (targetRestriction i f g))
      (compTransport (commonToAmbient i f g) (ambientRestriction i f g)
      ((commonToTarget i f g) ≫ (targetRestriction i f g)) (commonToAmbient_comp_eq i f g))))
      fun T => flatQuasicoherentOver_glue i f g hi hf T.obj T.property))
    ((FlatQuasicoherentTriple i f g).liftCompιIso _ _).symm
    ((FlatQuasicoherentOver g).liftCompιIso _ _).symm
    (isIso_unit_app i f g hi hf) ?_
  intro T
  exact isIso_counit_app i f g hi hf T

/-! ### Stacks 08KV -/

omit [HasPushout i f] in
include hi hf in
/-- **Stacks Project, Tag 08KV, the equivalence.**  Let `i : X ⟶ X'` be a thickening and
`f : X ⟶ Y` an affine morphism of algebraic spaces over `S`, let `Y' = Y ⨿_X X'` be their pushout
(Stacks 07VX) and let `g : V' ⟶ Y'` be a morphism, with `V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'`
and `U = X ×_{Y'} V'`.  The functor `𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)` is an
**equivalence of categories** from the quasi-coherent `𝒪_{V'}`-modules flat over `Y'` onto the
triples `(𝒢, ℱ', φ)` of a quasi-coherent `𝒪_V`-module `𝒢` flat over `Y`, a quasi-coherent
`𝒪_{U'}`-module `ℱ'` flat over `X'` and an isomorphism `φ : (U ⟶ V)^*𝒢 ≅ (U ⟶ U')^*ℱ'`.

The source writes "`ℱ'` … flat over `X`": `ℱ'` lives on `U' = X' ×_{Y'} V'`, which lies over
`X'`, so the condition is flatness over `X'`, as in the scheme case Stacks 08KU.  The pushout is
not assumed: it exists by Stacks 07VX
(`AlgebraicGeometry.Space.hasPushout_of_isThickeningHom_of_isAffineHom`), which is the instance
the statement binds.  The functor is written out as the lift to the two full subcategories of
`CategoryTheory.TripleGluing.restrictFunctor` at the canonical comparison
`AlgebraicGeometry.Space.PushoutModules.squareOverlap`; a quasi-inverse is the gluing functor
`(𝒢, ℱ', φ) ↦ (V ⟶ V')_*𝒢 ×_{(U ⟶ V')_*ℱ} (U' ⟶ V')_*ℱ'`
(`isEquivalence_flatRestrictionFunctor_of_hasPushout`). -/
@[stacks 08KV "the equivalence"]
theorem isEquivalence_flatRestrictionFunctor :
    letI := hasPushout_of_isThickeningHom_of_isAffineHom B S hS i f hi hf
    ∀ {V' : AlgebraicSpaces B S hS} (g : V' ⟶ pushout i f),
      ((((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
      (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g) (targetRestriction i f g)
      (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))))
        fun M => flatQuasicoherentTriple_restrict i f g M.obj M.property) :
        (FlatQuasicoherentOver g).FullSubcategory ⥤
        (FlatQuasicoherentTriple i f g).FullSubcategory)).IsEquivalence := by
  let := hasPushout_of_isThickeningHom_of_isAffineHom B S hS i f hi hf
  intro V' g
  exact isEquivalence_flatRestrictionFunctor_of_hasPushout i f g hi hf

end PushoutModules

end AlgebraicGeometry.Space

end
