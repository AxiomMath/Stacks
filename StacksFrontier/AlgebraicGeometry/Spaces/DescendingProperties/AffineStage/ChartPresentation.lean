module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage.SpecGlobalFunctions

/-!
# The charts of a descent situation and a presentation at a stage

The models of the global functions of the stages of a descent situation and of its affine
charts, the descent of the coordinates of a presentation over the limit to a stage, the
Cartesian square of Stacks 084U over the limit, and the passage from a presentation at a stage
to an affine stage.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ChartPresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_ChartPresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The models of the global functions and the charts of a descent situation -/

namespace DescentSituation

section ChartModels

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- The transition map of the directed system of the `u`-models of the rings of global functions
of the stages, as a ring homomorphism. -/
def modelTransition (i j : I) (h : i ≤ j) :
    globalFunctionsModel B S hS (D.stage i) →+* globalFunctionsModel B S hS (D.stage j) :=
  (stageModelEquiv D j).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (D.transition h)).comp (stageModelEquiv D i).toRingHom)

/-- The map from the `u`-model of the ring of global functions of a stage to that of the limit,
as a ring homomorphism. -/
def modelProjection (i : I) :
    globalFunctionsModel B S hS (D.stage i) →+* globalFunctionsModel B S hS D.limitSpace :=
  (limitModelEquiv D).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (D.projection i)).comp (stageModelEquiv D i).toRingHom)

/-- The `u`-models of the rings of global functions of the stages form a directed system, with
`AlgebraicGeometry.Space.DescentSituation.modelTransition` as transition map. -/
theorem directedSystem_modelTransition :
    DirectedSystem (fun i : I => globalFunctionsModel B S hS (D.stage i))
      (fun i j (h : i ≤ j) x => D.modelTransition i j h x) :=
  directedSystem_globalFunctionsModel D

/-- **Stacks 07SI for the structure sheaf on the `u`-models**, with both families read as ring
homomorphisms. -/
theorem isStagesColimit_modelProjection (hI : #I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit (fun i j (h : i ≤ j) x => D.modelTransition i j h x)
      (fun i x => D.modelProjection i x) :=
  isStagesColimit_globalFunctionsModel D hI

section Charts

variable {U₀ : BigAffineFppf B S hS}
  {chart : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.system.obj (op D.base)}
  (C : AffineChartSystem B S hS (op D.base) D.system U₀ chart)
  (hchart : IsEtaleChart B S hS (D.system.obj (op D.base)) (CostructuredArrow.mk chart))

/-- Restriction of the global functions of a stage to its chart, read on the `u`-model. -/
noncomputable def stageChartHom (i : D.toLimitSituation.Stages) :
    globalFunctionsModel B S hS (D.stage i.1) →+*
      Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op i), ⊤) :=
  (globalFunctionsChartRestriction B S hS (D.stage i.1)
      (D.toLimitSituation.stagesEtaleChart C hchart i)).comp
    (globalFunctionsModelEquiv B S hS (D.stage i.1)).toRingHom

/-- Restriction of the global functions of the limit to the limit chart, read on the
`u`-model. -/
noncomputable def limitChartHom (L : AffineChartSystem.LimitBridge C) :
    globalFunctionsModel B S hS D.limitSpace →+*
      Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) :=
  (globalFunctionsChartRestriction B S hS D.limitSpace
      (D.toLimitSituation.limitEtaleChart C L hchart)).comp
    (globalFunctionsModelEquiv B S hS D.limitSpace).toRingHom

/-- The projection of the limit chart to the chart of a stage is compatible with the maps of the
charts to the spaces. -/
private theorem yoneda_map_cone_π_comp_stageMap (L : AffineChartSystem.LimitBridge C)
    (i : D.toLimitSituation.Stages) :
    yoneda.map (L.cone.π.app
        ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op i)))
        ≫ C.stageMap
          ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op i))
      = D.toLimitSituation.limitChartToSpace C L
        ≫ D.toLimitSituation.π.app (op i.1) :=
  (L.toLimit_comp_limitπ
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op i))).symm.trans
    (((congrArg (fun z => L.toLimit ≫ z)
        (D.toLimitSituation.limitIso_hom_comp_π (op i.1))).symm).trans
      (Category.assoc _ _ _).symm)

/-- **Restriction to the limit chart intertwines the map to the model at the limit with
restriction along the projection of the limit chart to the chart of a stage.** This is the
stage-to-limit half of the coherence the descent of the coordinates consumes; the Cartesian
square of the chart system at the limit projection is what supplies the morphism of charts. -/
theorem appTop_stagesSchemeCone_π_stageChartHom (L : AffineChartSystem.LimitBridge C)
    (i : D.toLimitSituation.Stages)
    (x : globalFunctionsModel B S hS (D.stage i.1)) :
    (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app (op i)).appTop).hom
        (D.stageChartHom C hchart i x)
      = D.limitChartHom C hchart L (D.modelProjection i.1 x) := by
  have hcoh := globalFunctionsChartRestriction_globalFunctionsMap B S hS (D.projection i.1)
    (D.toLimitSituation.limitEtaleChart C L hchart)
    (D.toLimitSituation.stagesEtaleChart C hchart i)
    (L.cone.π.app
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op i)))
    (D.yoneda_map_cone_π_comp_stageMap C L i)
    (globalFunctionsModelEquiv B S hS (D.stage i.1) x)
  refine hcoh.symm.trans ?_
  exact congrArg (globalFunctionsChartRestriction B S hS D.limitSpace
      (D.toLimitSituation.limitEtaleChart C L hchart))
    ((limitModelEquiv D).apply_symm_apply _).symm

/-- **Restriction to the chart of a stage intertwines the transition of the models with
restriction along the transition of the charts.** This is the stage-to-stage half of the
coherence; the naturality square of the chart system supplies the morphism of charts. -/
theorem appTop_stagesSchemeDiagram_map_stageChartHom
    {i j : D.toLimitSituation.Stages} (h : i ≤ j)
    (x : globalFunctionsModel B S hS (D.stage i.1)) :
    (((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map (homOfLE h).op).appTop).hom
        (D.stageChartHom C hchart i x)
      = D.stageChartHom C hchart j (D.modelTransition i.1 j.1 h x) := by
  have hcoh := globalFunctionsChartRestriction_globalFunctionsMap B S hS (D.transition h)
    (D.toLimitSituation.stagesEtaleChart C hchart j)
    (D.toLimitSituation.stagesEtaleChart C hchart i)
    (C.siteDiagram.map
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.map (homOfLE h).op))
    (C.stageMap_naturality _)
    (globalFunctionsModelEquiv B S hS (D.stage i.1) x)
  refine hcoh.symm.trans ?_
  exact congrArg (globalFunctionsChartRestriction B S hS (D.stage j.1)
      (D.toLimitSituation.stagesEtaleChart C hchart j))
    ((stageModelEquiv D j.1).apply_symm_apply _).symm

/-- **The global functions on the charts of the stages form a directed system**, the charts of
the stages being the values of a functor. -/
theorem directedSystem_appTop_stagesSchemeDiagram :
    DirectedSystem (fun i : D.toLimitSituation.Stages =>
        (Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op i), ⊤) : Type u))
      (fun i j (h : i ≤ j) x =>
        (((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
          (homOfLE h).op).appTop).hom x) := by
  constructor
  · intro i x
    have h0 : (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
          ((homOfLE (le_refl i)).op : (op i : (D.toLimitSituation.Stages)ᵒᵖ) ⟶ op i)
        = 𝟙 _ :=
      (congrArg (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
        (Subsingleton.elim ((homOfLE (le_refl i)).op :
          (op i : (D.toLimitSituation.Stages)ᵒᵖ) ⟶ op i) (𝟙 (op i)))).trans
        ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map_id (op i))
    refine (congrArg (fun g :
        (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op i) ⟶
        (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op i) =>
      (Scheme.Hom.appTop g).hom x) h0).trans ?_
    rfl
  · intro k j i hij hjk x
    have h0 : (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
          ((homOfLE (hij.trans hjk)).op : (op k : (D.toLimitSituation.Stages)ᵒᵖ) ⟶ op i)
        = (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map (homOfLE hjk).op ≫
          (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map (homOfLE hij).op :=
      (congrArg (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
        (Subsingleton.elim ((homOfLE (hij.trans hjk)).op :
            (op k : (D.toLimitSituation.Stages)ᵒᵖ) ⟶ op i)
          ((homOfLE hjk).op ≫ (homOfLE hij).op))).trans
        ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map_comp _ _)
    refine Eq.trans ?_ (congrArg (fun g :
        (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op k) ⟶
        (LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op i) =>
      (Scheme.Hom.appTop g).hom x) h0).symm
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- **The canonical morphism from the limit to the spectrum of a model of its global functions,
composed with the spectrum of the transition of the models, is the projection to a stage followed
by the canonical morphism there.** Both sides restrict, on the limit chart, to the morphism of
schemes the `Γ`–`Spec` adjunction attaches to restriction of the global functions of the stage to
the chart of the limit, which is where the stage-to-limit coherence
`AlgebraicGeometry.Space.DescentSituation.appTop_stagesSchemeCone_π_stageChartHom` enters; and the
limit chart is surjective and étale, so restriction along it is injective on morphisms into the
functor of points of a scheme, which is a sheaf.

This is the identification of the bottom edge of the square of Stacks 084U at the limit with the
bottom edge of the pasted square, and it is what makes the limit square Cartesian over the
*stage's* spectrum in the proof of Stacks 07SQ. -/
theorem specPoints_comp_schemePointsMap_modelProjection
    (L : AffineChartSystem.LimitBridge C) (hchartSurj : IsSurjective B S hS chart)
    (m : D.toLimitSituation.Stages)
    {pA : D.limitSpace.obj ⟶ schemePoints B S hS
        (Spec (CommRingCat.of (globalFunctionsModel B S hS D.limitSpace)))}
    (hpA : yonedaEquiv ((D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫ pA)
      = specMapOfGlobalHom (globalFunctionsModel B S hS D.limitSpace)
          (D.limitChartHom C hchart L))
    {p : (D.stage m.1).obj ⟶ schemePoints B S hS
        (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))}
    (hp : yonedaEquiv ((D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom ≫ p)
      = specMapOfGlobalHom (globalFunctionsModel B S hS (D.stage m.1))
          (D.stageChartHom C hchart m)) :
    pA ≫ schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (D.modelProjection m.1)))
      = D.toLimitSituation.π.app (op m.1) ≫ p := by
  refine hom_ext_of_etale_surjective_chart B S hS D.limitAlgebraicSpace
    (isSheaf_schemePoints B S hS _)
    (D.toLimitSituation.limitEtaleChart C L hchart).obj.hom
    ((presheafSurjective_iff_isSurjective_yoneda B S hS D.limitSpace.obj
      D.limitAlgebraicSpace _ _).2
      (D.toLimitSituation.isSurjective_limitEtaleChart C L hchart hchartSurj))
    (D.toLimitSituation.limitEtaleChart C L hchart).property ?_
  apply yonedaEquiv.injective
  -- the left-hand side
  have hleft : yonedaEquiv ((D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫
        pA ≫ schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (D.modelProjection m.1))))
      = specMapOfGlobalHom (globalFunctionsModel B S hS (D.stage m.1))
          ((D.limitChartHom C hchart L).comp (D.modelProjection m.1)) := by
    refine (congrArg yonedaEquiv (Category.assoc _ _ _).symm).trans ?_
    refine (yonedaEquiv_comp_schemePointsMap B S hS _ _).trans ?_
    refine (congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom (D.modelProjection m.1)))
      hpA).trans ?_
    exact specMapOfGlobalHom_comp_Spec_map _ _ _ _
  -- the right-hand side
  have hcoh : (D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫
        D.toLimitSituation.π.app (op m.1)
      = yoneda.map (L.cone.π.app
          ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
        ≫ (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom :=
    (D.yoneda_map_cone_π_comp_stageMap C L m).symm
  have hright : yonedaEquiv ((D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫
        D.toLimitSituation.π.app (op m.1) ≫ p)
      = specMapOfGlobalHom (globalFunctionsModel B S hS (D.stage m.1))
          ((D.limitChartHom C hchart L).comp (D.modelProjection m.1)) := by
    have hstep : (D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫
          D.toLimitSituation.π.app (op m.1) ≫ p
        = yoneda.map (L.cone.π.app
            ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
          ≫ ((D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom ≫ p) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ p) hcoh).trans (Category.assoc _ _ _))
    refine (congrArg yonedaEquiv hstep).trans ?_
    refine (yonedaEquiv_naturality _ _).symm.trans ?_
    refine (congrArg (fun z => (BigFppfOver.toScheme B S hS).map
      (L.cone.π.app ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj
        (op m))) ≫ z) hp).trans ?_
    refine (comp_specMapOfGlobalHom _ _ _).trans ?_
    exact congrArg (specMapOfGlobalHom (globalFunctionsModel B S hS (D.stage m.1)))
      (RingHom.ext fun z =>
        D.appTop_stagesSchemeCone_π_stageChartHom C hchart L m z)
  exact hleft.trans hright.symm

/-- **The left-hand square of display 70.5.10.1 is Cartesian over the limit.** Over a terminal
base, if the limit of a descent situation is affine then both horizontal edges of the square of
Stacks 084U at the limit chart are isomorphisms — the lower one by Stacks 05Z1, the upper one
because the coordinates present the global functions of the chart — so the square is
Cartesian. -/
theorem isPullback_coordinateHom_limit (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) {n : ℕ}
    (glim : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS D.limitSpace))
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t (glim l) = 0)
    (hbij : Function.Bijective (coordinateHom glim (D.limitChartHom C hchart L) t hrel))
    {pA : D.limitSpace.obj ⟶ schemePoints B S hS
        (Spec (CommRingCat.of (globalFunctionsModel B S hS D.limitSpace)))}
    (hpAiso : IsIso pA)
    (hpA : yonedaEquiv ((D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫ pA)
      = specMapOfGlobalHom (globalFunctionsModel B S hS D.limitSpace)
          (D.limitChartHom C hchart L)) :
    IsPullback
      (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra glim)
          (coordinateHom glim (D.limitChartHom C hchart L) t hrel)) :
        yoneda.obj L.cone.pt ⟶ schemePoints B S hS
          (Spec (CommRingCat.of (presentationAlgebra glim))))
      (D.toLimitSituation.limitChartToSpace C L)
      (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom glim)))) pA := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := L.isAffine_pt
  have h1 : IsIso (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra glim)
      (coordinateHom glim (D.limitChartHom C hchart L) t hrel)) :
      yoneda.obj L.cone.pt ⟶ schemePoints B S hS
        (Spec (CommRingCat.of (presentationAlgebra glim)))) :=
    isIso_yonedaEquiv_symm_specMapOfGlobalHom B S hS hterminal L.cone.pt
      (presentationAlgebra glim) (coordinateHom glim (D.limitChartHom C hchart L) t hrel) hbij
  exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ h1 hpAiso
    ⟨(commSq_chart_specOfGlobalFunctions B S hS D.limitSpace
      (D.toLimitSituation.limitEtaleChart C L hchart)
      (globalFunctionsModel B S hS D.limitSpace)
      (globalFunctionsModelEquiv B S hS D.limitSpace) glim t hrel pA hpA).symm⟩

/-- **The descent map of the coordinates, read on the presentations.** The homomorphism out of
the presentation over a stage determined by the coordinates there, followed by restriction to the
limit chart, is the homomorphism out of the base-changed presentation over the limit determined
by the coordinates there, precomposed with the base-change map of the presentations.

Both sides are pinned by their action on the constants and on the classes of the variables: on
the constants this is the stage-to-limit coherence
`AlgebraicGeometry.Space.DescentSituation.appTop_stagesSchemeCone_π_stageChartHom`, and on the
variables it is the agreement of the coordinates. -/
theorem coordinateHom_comp_quotientMap (L : AffineChartSystem.LimitBridge C)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hyt : ∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
      (op m)).appTop).hom (y k) = t k)
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      ((fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)) l) = 0) :
    (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
          (D.limitChartHom C hchart L) t hrel).comp
        (Ideal.quotientMap
          (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)))
          (MvPolynomial.map (D.modelProjection m.1))
          (span_range_le_comap_map_span_range (D.modelProjection m.1) g'))
      = ((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
            (op m)).appTop).hom).comp
          (coordinateHom g' (D.stageChartHom C hchart m) y hyrel) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_))
  · change (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
        (D.limitChartHom C hchart L) t hrel)
          (Ideal.quotientMap _ (MvPolynomial.map (D.modelProjection m.1))
            (span_range_le_comap_map_span_range (D.modelProjection m.1) g')
            (Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.C a)))
      = (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app (op m)).appTop).hom
          ((coordinateHom g' (D.stageChartHom C hchart m) y hyrel)
            (Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.C a)))
    rw [Ideal.quotientMap_mk, MvPolynomial.map_C]
    refine (RingHom.congr_fun (coordinateHom_comp_presentationStructureHom
      (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
      (D.limitChartHom C hchart L) t hrel) (D.modelProjection m.1 a)).trans ?_
    refine ((congrArg (fun z => (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
        (op m)).appTop).hom z)
      (RingHom.congr_fun (coordinateHom_comp_presentationStructureHom g'
        (D.stageChartHom C hchart m) y hyrel) a)).trans
      (D.appTop_stagesSchemeCone_π_stageChartHom C hchart L m a)).symm
  · change (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
        (D.limitChartHom C hchart L) t hrel)
          (Ideal.quotientMap _ (MvPolynomial.map (D.modelProjection m.1))
            (span_range_le_comap_map_span_range (D.modelProjection m.1) g')
            (Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.X k)))
      = (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app (op m)).appTop).hom
          ((coordinateHom g' (D.stageChartHom C hchart m) y hyrel)
            (Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.X k)))
    rw [Ideal.quotientMap_mk, MvPolynomial.map_X]
    refine (coordinateHom_mk_X (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
      (D.limitChartHom C hchart L) t hrel k).trans ?_
    exact ((congrArg (fun z => (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
        (op m)).appTop).hom z)
      (coordinateHom_mk_X g' (D.stageChartHom C hchart m) y hyrel k)).trans (hyt k)).symm

/-- **The upper edge of display 70.5.10.1 over the limit, followed by the base change of the
presentations, is the upper edge over a stage restricted to the limit chart.** This is
`AlgebraicGeometry.Space.DescentSituation.coordinateHom_comp_quotientMap` read through the
`Γ`–`Spec` adjunction and the functors of points. -/
theorem specPoints_coordinateHom_comp_quotientMap (L : AffineChartSystem.LimitBridge C)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hyt : ∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
      (op m)).appTop).hom (y k) = t k)
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      ((fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)) l) = 0) :
    (yonedaEquiv.symm (specMapOfGlobalHom
          (presentationAlgebra fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
          (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
            (D.limitChartHom C hchart L) t hrel)) :
        yoneda.obj L.cone.pt ⟶ schemePoints B S hS (Spec (CommRingCat.of
          (presentationAlgebra fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)))))
        ≫ schemePointsMap B S hS (Spec.map (CommRingCat.ofHom
            (Ideal.quotientMap
              (Ideal.span (Set.range fun k =>
                MvPolynomial.map (D.modelProjection m.1) (g' k)))
              (MvPolynomial.map (D.modelProjection m.1))
              (span_range_le_comap_map_span_range (D.modelProjection m.1) g'))))
      = yoneda.map (L.cone.π.app
          ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
        ≫ yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
            (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp_schemePointsMap, Equiv.apply_symm_apply,
    specMapOfGlobalHom_comp_Spec_map, ← yonedaEquiv_naturality, schemePoints_map,
    Equiv.apply_symm_apply, comp_specMapOfGlobalHom]
  exact congrArg (specMapOfGlobalHom (presentationAlgebra g'))
    (D.coordinateHom_comp_quotientMap C hchart L m g' y hyrel t hyt hrel)

/-- **The limit chart is the fibre product of the limit with the spectrum of the presentation
over a stage.** Pasting the left-hand square of display 70.5.10.1 at the limit, Cartesian by
`AlgebraicGeometry.Space.DescentSituation.isPullback_coordinateHom_limit`, with the Cartesian
square of the base change of the presentation, which is
`AlgebraicGeometry.Space.isPushout_presentationAlgebra_baseChange` read through `Spec` and the
functors of points.

This is the Cartesian square the proof of Stacks 07SQ feeds to Stacks 084S. -/
theorem isPullback_toLimit_coordinateHom (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hchartSurj : IsSurjective B S hS chart)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hyt : ∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
      (op m)).appTop).hom (y k) = t k)
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      ((fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)) l) = 0)
    (hbij : Function.Bijective
      (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
        (D.limitChartHom C hchart L) t hrel))
    {pA : D.limitSpace.obj ⟶ schemePoints B S hS
        (Spec (CommRingCat.of (globalFunctionsModel B S hS D.limitSpace)))}
    (hpAiso : IsIso pA)
    (hpA : yonedaEquiv ((D.toLimitSituation.limitEtaleChart C L hchart).obj.hom ≫ pA)
      = specMapOfGlobalHom (globalFunctionsModel B S hS D.limitSpace)
          (D.limitChartHom C hchart L))
    {p : (D.stage m.1).obj ⟶ schemePoints B S hS
        (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))}
    (hp : yonedaEquiv ((D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom ≫ p)
      = specMapOfGlobalHom (globalFunctionsModel B S hS (D.stage m.1))
          (D.stageChartHom C hchart m)) :
    IsPullback L.toLimit
      (yoneda.map (L.cone.π.app
          ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
        ≫ yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
            (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)))
      (limit.π D.system (op m.1) ≫ p)
      (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) := by
  have hL := D.isPullback_coordinateHom_limit C hchart L hterminal
    (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)) t hrel hbij hpAiso hpA
  have hR : IsPullback
      (schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)))
        (MvPolynomial.map (D.modelProjection m.1))
        (span_range_le_comap_map_span_range (D.modelProjection m.1) g')))))
      (schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom
        fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)))))
      (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
      (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (D.modelProjection m.1)))) :=
    isPullback_schemePointsMap B S hS
      (((isPushout_presentationAlgebra_baseChange (D.modelProjection m.1) g'
        (span_range_le_comap_map_span_range (D.modelProjection m.1) g')).op).map Scheme.Spec)
  have hpaste := (hL.paste_horiz hR).flip
  rw [D.specPoints_coordinateHom_comp_quotientMap C hchart L m g' y hyrel t hyt hrel] at hpaste
  have h2 : D.toLimitSituation.limitIso.inv ≫ limit.π D.toLimitSituation.system (op m.1)
      = D.toLimitSituation.π.app (op m.1) := by
    rw [← D.toLimitSituation.limitIso_hom_comp_π (op m.1), Iso.inv_hom_id_assoc]
  refine hpaste.of_iso (Iso.refl _) D.toLimitSituation.limitIso.symm (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom,
      show D.toLimitSituation.limitChartToSpace C L
        = L.toLimit ≫ D.toLimitSituation.limitIso.hom from rfl]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => L.toLimit ≫ z)
        (Iso.hom_inv_id D.toLimitSituation.limitIso)).trans (Category.comp_id _))
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    refine (D.specPoints_comp_schemePointsMap_modelProjection C hchart L hchartSurj m
      hpA hp).trans ?_
    exact ((congrArg (fun z => z ≫ p) h2).symm).trans (Category.assoc _ _ _)
  · simp

/-- **The descent of display 70.5.10.1 and its conclusion.** Over a terminal base, given at a
stage `m` the square of Stacks 084U for a family `g` of `n` polynomials in `n` variables over the
`u`-model of the global functions of `m`, and given that over the limit that square is Cartesian,
some stage at or beyond `m` is an affine algebraic space.

The morphism of the display is a morphism descent system in the sense of Stacks 084W; it is an
isomorphism over the limit by
`AlgebraicGeometry.Space.MorphismDescentSystem.isIso_mapLimit_of_isPullback`, so Stacks 084S makes
it an isomorphism at some later stage `k`; and there the étale covering
`Spec A_m[x]/(g) ⟶ Spec A_m` descends affineness by
`AlgebraicGeometry.Space.MorphismDescentSystem.isAffineSpace_base_obj_of_isIso_mapAt`. -/
theorem exists_isAffineSpace_system_obj_of_isPullback (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hI : #I < B.cutoff.ord.cof)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    {p : (D.stage m.1).obj ⟶ schemePoints B S hS
      (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))}
    (hsq : (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom ≫ p
      = yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
          (coordinateHom g' (D.stageChartHom C hchart m) y hyrel))
        ≫ schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
    (hsrcPB : IsPullback L.toLimit
      (yoneda.map (L.cone.π.app
          ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
        ≫ yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
            (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)))
      (limit.π D.system (op m.1) ≫ p)
      (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    (hCont : B.Contains (Spec (CommRingCat.of (presentationAlgebra g'))))
    (haWsurj : IsSurjective B S hS ((schemePointsIso B S hS hterminal hCont).hom ≫
      schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    (haWetale : IsEtale B S hS ((schemePointsIso B S hS hterminal hCont).hom ≫
      schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    (hfpres : RingHom.FinitePresentation (presentationStructureHom g')) :
    ∃ i, m.1 ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  have ha : IsEtale B S hS (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      (D.toLimitSituation.stagesEtaleChart C hchart m).property
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))) :=
    C.isAffine_obj _
  have hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))) :=
    Scheme.compactSpace_of_isAffine _
  have hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))) :=
    inferInstance
  have hY₀alg : IsAlgebraicSpace B S hS (pullback p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))) :=
    isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS
      (CommRingCat.ofHom (presentationStructureHom g'))
      (RingHom.FiniteType.of_finitePresentation hfpres) (D.algebraicSpace m.1) p
  have hX₀fp : IsFinitePresentation B S hS
      (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom :=
    isFinitePresentation_etaleChart B S hS hZ (D.algebraicSpace m.1)
      (D.quasiSeparated m.1) hUqc hUqs ha
  have hY₀fp : IsFinitePresentation B S hS (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))) :=
    isFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS
      (CommRingCat.ofHom (presentationStructureHom g')) hfpres (D.algebraicSpace m.1) p
  set D' : DescentSituation B S hS hZ I := { D with base := m.1 } with hD'def
  set X₀ : Over (D'.system.obj (op D'.base)) :=
    Over.mk (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom with hX₀def
  set Y₀ : Over (D'.system.obj (op D'.base)) :=
    Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))) with hY₀def
  set f₀ : X₀ ⟶ Y₀ := Over.homMk (pullback.lift
      (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom
      (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
        (coordinateHom g' (D.stageChartHom C hchart m) y hyrel))) hsq)
      (pullback.lift_fst _ _ _) with hf₀def
  have hfp : IsLocallyOfFinitePresentation B S hS (Over.Hom.left f₀) := by
    refine isLocallyOfFinitePresentation_of_comp B S hS
      (isAlgebraicSpace_yoneda B S hS _) hY₀alg (D.algebraicSpace m.1)
      (Over.Hom.left f₀) Y₀.hom ?_
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hY₀fp.1)
    rw [Over.w f₀]
    exact hX₀fp.1
  set M := D'.morphismDescentSystem hI X₀ Y₀ (isAlgebraicSpace_yoneda B S hS _) hY₀alg
    hX₀fp hY₀fp f₀ with hMdef
  have hisoML : IsIso M.mapLimit :=
    MorphismDescentSystem.isIso_mapLimit_of_isPullback M p
      (schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
      (pullback.snd p _) (IsPullback.of_hasPullback p _)
      (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
        (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)))
      (pullback.lift_snd _ _ _)
      (L.isPullback_stage
        ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
      hsrcPB
  obtain ⟨k, hk, hkiso⟩ := D'.exists_isIso_mapAt_of_isIso_mapLimit hI X₀ Y₀
    (isAlgebraicSpace_yoneda B S hS _) hY₀alg hX₀fp hY₀fp f₀ hfp hisoML
  refine ⟨k, hk, ?_⟩
  have hsrcAff : IsAffineSpace B S hS (M.sourceAt k hk) :=
    (IsAffineHom.of_isPullback (M.sourceAt_isPullback k hk)
      (M.transition_affine _)).isAffineSpace_source
      (isAffineSpace_yoneda B S hS _ hWaff)
  have hZaff : IsAffineSpace B S hS (schemePoints B S hS
      (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))) :=
    isAffineSpace_schemePoints B S hS hterminal
      (contains_spec_globalFunctionsModel B S hS (D.stage m.1))
  have hqSq : IsPullback M.targetToBase
      (pullback.snd p (schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
        ≫ (schemePointsIso B S hS hterminal hCont).inv) p
      ((schemePointsIso B S hS hterminal hCont).hom ≫ schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) := by
    refine (IsPullback.of_hasPullback p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))).of_iso (Iso.refl _)
      (Iso.refl _) (schemePointsIso B S hS hterminal hCont).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp
  exact MorphismDescentSystem.isAffineSpace_base_obj_of_isIso_mapAt M p
    (show IsAffine ((BigFppfOver.toScheme B S hS).obj
        (terminalSiteObject B S hS hterminal hCont)) by
      rw [toScheme_terminalSiteObject]; infer_instance)
    ((schemePointsIso B S hS hterminal hCont).hom ≫ schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
    haWsurj haWetale hZaff.isAlgebraicSpace hZaff _ hqSq hk hsrcAff hkiso

/-- **Stacks 07SQ, from a presentation at a stage.** Over a terminal base, suppose the limit of a
descent situation is affine, and suppose at a stage `m` there is a family of `n` polynomials in
`n` variables over the `u`-model of the global functions of that stage which presents an étale
algebra with surjective spectrum, together with regular functions on the chart of `m`
annihilating it and agreeing at the limit with coordinates presenting the global functions of the
limit chart. Then some stage at or beyond `m` is an affine algebraic space.

The canonical morphisms to the spectra of the models are Stacks 05Z1, the square they sit in is
Stacks 084U, and that square is Cartesian over the limit by
`AlgebraicGeometry.Space.DescentSituation.isPullback_toLimit_coordinateHom`; the descent is then
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_isPullback`. -/
theorem exists_isAffineSpace_system_obj_of_presentation (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hchartSurj : IsSurjective B S hS chart)
    (hI : #I < B.cutoff.ord.cof) (hX : IsAffineSpace B S hS D.limitSpace.obj)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hyt : ∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
      (op m)).appTop).hom (y k) = t k)
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      ((fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)) l) = 0)
    (hbij : Function.Bijective
      (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
        (D.limitChartHom C hchart L) t hrel))
    (hg'E : Algebra.Etale (globalFunctionsModel B S hS (D.stage m.1))
      (presentationAlgebra g'))
    (hg'S : Function.Surjective (PrimeSpectrum.comap (presentationStructureHom g'))) :
    ∃ i, m.1 ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  obtain ⟨p, hp⟩ := exists_specMap_of_globalHom B S hS (D.stage m.1)
    (globalFunctionsModel B S hS (D.stage m.1))
    (globalFunctionsModelEquiv B S hS (D.stage m.1)).toRingHom
  obtain ⟨pA, hpAiso, hpA⟩ := exists_isIso_specMapOfGlobalHom_of_isAffineSpace B S hS hterminal
    D.limitSpace (globalFunctionsModel B S hS D.limitSpace)
    (contains_spec_globalFunctionsModel B S hS D.limitSpace)
    (globalFunctionsModelEquiv B S hS D.limitSpace) hX
  have hfpres : RingHom.FinitePresentation (presentationStructureHom g') :=
    finitePresentation_presentationStructureHom g'
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})).mpr
      (RingHom.FiniteType.of_finitePresentation hfpres)
  have hetaleSpec : AlgebraicGeometry.Etale
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale.{u})).mpr
      (RingHom.etale_algebraMap.mpr hg'E)
  have hsurjSpec : AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))) := ⟨hg'S⟩
  have haaEtale : IsEtale B S hS (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) :=
    isEtale_of_presheaf_etale B S hS (presheaf_inverseImage_schemePointsMap B S hS
      (@AlgebraicGeometry.Etale.{u}) _ hetaleSpec)
  have haaSurj : IsSurjective B S hS (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) :=
    isSurjective_of_presheafSurjective B S hS _ (presheaf_inverseImage_schemePointsMap B S hS
      (@AlgebraicGeometry.Surjective.{u}) _ hsurjSpec)
  have : Algebra.FinitePresentation (globalFunctionsModel B S hS (D.stage m.1))
      (presentationAlgebra g') := Algebra.FinitePresentation.quotient (fg_span_range g')
  have : Algebra.FiniteType (globalFunctionsModel B S hS (D.stage m.1))
      (presentationAlgebra g') := inferInstance
  have hCont : B.Contains (Spec (CommRingCat.of (presentationAlgebra g'))) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (globalFunctionsModel B S hS (D.stage m.1)) (presentationAlgebra g')
      (contains_spec_globalFunctionsModel B S hS (D.stage m.1))
  exact D.exists_isAffineSpace_system_obj_of_isPullback C hchart L hterminal hI m g' y hyrel
    (commSq_chart_specOfGlobalFunctions B S hS (D.stage m.1)
      (D.toLimitSituation.stagesEtaleChart C hchart m)
      (globalFunctionsModel B S hS (D.stage m.1))
      (globalFunctionsModelEquiv B S hS (D.stage m.1)) g' y hyrel p
      (hp (D.toLimitSituation.stagesEtaleChart C hchart m)))
    (D.isPullback_toLimit_coordinateHom C hchart L hterminal hchartSurj m g' y hyrel t hyt
      hrel hbij hpAiso (hpA (D.toLimitSituation.limitEtaleChart C L hchart))
      (hp (D.toLimitSituation.stagesEtaleChart C hchart m)))
    hCont
    (isSurjective_comp B S hS
      (isSurjective_of_isIso B S hS (schemePointsIso B S hS hterminal hCont).hom) haaSurj)
    (isEtale_comp B S hS
      (isEtale_of_isIso B S hS (schemePointsIso B S hS hterminal hCont).hom) haaEtale)
    hfpres

/-- **The coordinates and the relations of a presentation over the limit descend to a single
stage.** Let `q` be a family of `n` polynomials in `n` variables over the `u`-model of the ring
of global functions of a stage `j₀`, and let `t₁, …, tₙ` be regular functions on the limit chart
annihilating the family read over the limit. Then at some stage `m ≥ j₀` there are regular
functions on the chart of `m` annihilating the family read over `m`.

The coordinates are lifted to a stage by `Ring.exists_ge_forall_eq_of_directed` applied to the
colimit description of the regular functions on the charts, Stacks 01Z0 for the structure sheaf;
the relations, which then vanish at the limit, are forced to vanish at a later stage by
`Ring.exists_ge_forall_eq_zero_of_directed`. The two coherences
`AlgebraicGeometry.Space.DescentSituation.appTop_stagesSchemeCone_π_stageChartHom` and
`AlgebraicGeometry.Space.DescentSituation.appTop_stagesSchemeDiagram_map_stageChartHom` are what
carry the relations across the two squares: the first to see them vanish at the limit, the
second to read them at the later stage. -/
theorem exists_ge_eval₂_map_eq_zero (L : AffineChartSystem.LimitBridge C)
    (hI : #I < B.cutoff.ord.cof) (j₀ : D.toLimitSituation.Stages) {n : ℕ}
    (q : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage j₀.1)))
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      (MvPolynomial.map (D.modelProjection j₀.1) (q l)) = 0) :
    ∃ (m : D.toLimitSituation.Stages) (hm : j₀ ≤ m)
      (y : Fin n →
        Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤)),
      (∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
          (op m)).appTop).hom (y k) = t k) ∧
      ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l)) = 0 := by
  have : IsDirectedOrder I := inferInstance
  have hds := D.directedSystem_appTop_stagesSchemeDiagram C
  have hdsm := D.directedSystem_modelTransition
  have hcol := LimitSituation.isStagesColimit_chartAppTop D.toLimitSituation C L
  have hmodel := D.isStagesColimit_modelProjection hI
  obtain ⟨m, hm, y, hy⟩ := Ring.exists_ge_forall_eq_of_directed hcol.hφ hcol.hsurj t j₀
  have hvanish : ∀ l,
      ((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app (op m)).appTop).hom)
        (MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
          (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))) = 0 := by
    intro l
    rw [MvPolynomial.hom_eval₂]
    have h2 : ((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
            (op m)).appTop).hom).comp (D.stageChartHom C hchart m)
        = (D.limitChartHom C hchart L).comp (D.modelProjection m.1) :=
      RingHom.ext fun z => D.appTop_stagesSchemeCone_π_stageChartHom C hchart L m z
    have h3 : (fun k => (((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
        (op m)).appTop).hom)) (y k)) = t := funext hy
    rw [h2, h3]
    have h4 := MvPolynomial.eval₂_map (D.modelProjection m.1) t
      (D.limitChartHom C hchart L)
      (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
    have h5 : MvPolynomial.map (D.modelProjection m.1)
          (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
        = MvPolynomial.map (D.modelProjection j₀.1) (q l) :=
      MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q l)
    rw [← h4, h5]
    exact hrel l
  obtain ⟨m', hmm', hm'⟩ :=
    Ring.exists_ge_forall_eq_zero_of_directed hcol.hzero
      (fun l => MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))) hvanish
  refine ⟨m', hm.trans hmm', fun k =>
    ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
      (homOfLE hmm').op).appTop).hom) (y k),
    fun k => (hcol.hφ m m' hmm' (y k)).trans (hy k), fun l => ?_⟩
  have hmap : MvPolynomial.map (D.modelTransition j₀.1 m'.1 (hm.trans hmm')) (q l)
      = MvPolynomial.map (D.modelTransition m.1 m'.1 hmm')
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l)) :=
    (MvPolynomial.map_map_eq_map_of_directedSystem
      (f := fun i j (h : i ≤ j) => D.modelTransition i j h)
      (show j₀.1 ≤ m.1 from hm) (show m.1 ≤ m'.1 from hmm') (q l)).symm
  have hcomp : ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
          (homOfLE hmm').op).appTop).hom).comp (D.stageChartHom C hchart m)
      = (D.stageChartHom C hchart m').comp (D.modelTransition m.1 m'.1 hmm') :=
    RingHom.ext fun z =>
      D.appTop_stagesSchemeDiagram_map_stageChartHom C hchart hmm' z
  have h6 := MvPolynomial.eval₂_map (D.modelTransition m.1 m'.1 hmm')
    (fun k => ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
      (homOfLE hmm').op).appTop).hom) (y k))
    (D.stageChartHom C hchart m')
    (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
  rw [hmap, h6, ← hcomp, ← MvPolynomial.hom_eval₂]
  exact hm' l

end Charts

end ChartModels

end DescentSituation

end AlgebraicGeometry.Space

end
