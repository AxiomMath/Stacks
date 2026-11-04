module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# The chart correspondence: `f`-maps are maps into the direct image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `Q` be a sheaf of sets on the small étale site of `Y` and let `P` be a sheaf of
sets on the small étale site of `X`. An *`f`-map* `Q ⟶ P` (`AlgebraicGeometry.Space.FMap`) is a
family of maps of sections `Q(V) ⟶ P(U)`, one for each commutative square of étale scheme charts
over `f`, compatible with étale restriction of both charts. The `f`-maps are in bijection with
the homomorphisms `Q ⟶ f_*P` into the direct image, and with the homomorphisms `f⁻¹Q ⟶ P` out of
the inverse image.

The sections of `f_*P` over an étale scheme chart `V` of `Y` are the limit of the sections of `P`
over the étale scheme charts of `X` above the algebraic space `X ×_Y V`, and these charts are
exactly the chart diagrams over `V`.

## Main definitions

* `AlgebraicGeometry.Space.ranChartCone` and `AlgebraicGeometry.Space.ranChartIsLimit`: the cone
  of chart sections of a presheaf of sets on the small étale site of `X` over an étale algebraic
  space `W` over `X`, and the fact that it is a limit cone.
* `AlgebraicGeometry.Space.chartLift` is the cartesian form of a chart diagram: the morphism to
  `X ×_Y V` over `X` that the diagram determines, and
  `AlgebraicGeometry.Space.indexOfChartDiagram` is the corresponding object of the index
  category of the limit. `AlgebraicGeometry.Space.chartDiagramOfIndex` is the inverse
  construction.
* `AlgebraicGeometry.Space.fmapRan` and `AlgebraicGeometry.Space.ranFmap` are the two
  directions of the bijection, and `AlgebraicGeometry.Space.fmapRanEquiv` the bijection itself,
  in the Kan-extension form of the direct image;
  `AlgebraicGeometry.Space.fmapDirectImageEquiv` is the same in the form the morphism of ringed
  topoi carries.
* `AlgebraicGeometry.Space.presentationComparison` is the comparison from the Kan extension of
  `P` to a spaces-étale sheaf presenting `P`.
* `AlgebraicGeometry.Space.chartCorrespondence`: the bijection between `f`-maps and
  homomorphisms into the direct image, together with the fact that it satisfies
  `AlgebraicGeometry.Space.IsChartCorrespondence`.
* `AlgebraicGeometry.Space.fmapInverseImageEquiv`: the bijection between `f`-maps and
  homomorphisms out of the inverse image.

## Main results

* `AlgebraicGeometry.Space.chartLift_unique` and
  `AlgebraicGeometry.Space.indexOfChartDiagram_chartDiagramOfIndex`: chart diagrams over `V`
  and étale scheme charts of `X` above `X ×_Y V` are the same thing.
* `AlgebraicGeometry.Space.chartLift_naturality`: the cartesian form of a chart diagram is
  natural under restriction of both charts.
* `AlgebraicGeometry.Space.presentation_ranChartCone_π`: the chart projections of the Kan
  extension, read in a spaces-étale presentation, are restriction along the chart.
* `AlgebraicGeometry.Space.fmapRanApp_π` and `AlgebraicGeometry.Space.fmapRan_unique`: the
  forward direction of the bijection is the unique homomorphism whose chart projections are
  the components of the `f`-map.
* `AlgebraicGeometry.Space.fmapDirectImageEquiv_isChartCorrespondence`: the bijection
  `AlgebraicGeometry.Space.fmapDirectImageEquiv` satisfies
  `AlgebraicGeometry.Space.IsChartCorrespondence`.

## References

* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- Let `e : C ≌ D` be an equivalence and let `R` be a second right adjoint of `e.functor`.
Then the counit of that second adjunction, followed by an isomorphism presenting an object of
`D` as the image of an object `H` of `C`, is `e.functor` applied to the comparison
`R.obj P ⟶ H` built out of `CategoryTheory.Adjunction.rightAdjointUniq` and the inverse of the
unit of `e`. -/
theorem Equivalence.counit_comp_hom_eq_map_rightAdjointUniq {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (e : C ≌ D) {R : D ⥤ C} (adj : e.functor ⊣ R)
    (P : D) (H : C) (i : P ≅ e.functor.obj H) :
    adj.counit.app P ≫ i.hom =
      e.functor.map ((Adjunction.rightAdjointUniq e.toAdjunction adj).inv.app P ≫
        e.inverse.map i.hom ≫ e.unitInv.app H) := by
  have h3 : e.functor.map ((Adjunction.rightAdjointUniq e.toAdjunction adj).hom.app P) ≫
      adj.counit.app P = e.counit.app P :=
    Adjunction.rightAdjointUniq_hom_app_counit e.toAdjunction adj P
  have ha : e.functor.map ((Adjunction.rightAdjointUniq e.toAdjunction adj).inv.app P) ≫
      e.counit.app P = adj.counit.app P := by
    rw [← h3, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hb : e.functor.map (e.inverse.map i.hom) ≫ e.counit.app (e.functor.obj H) =
      e.counit.app P ≫ i.hom := e.counit.naturality i.hom
  simp only [CategoryTheory.Functor.map_comp]
  rw [← Equivalence.counit_app_functor, hb, ← Category.assoc, ha]

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The pointwise limit of chart sections, for an arbitrary sheaf -/

/-- The cone of chart sections of an arbitrary presheaf of sets on the small étale site of `X`
over an algebraic space `W` étale over `X`: its projections are restriction to the étale scheme
charts of `X` above `W`. -/
noncomputable abbrev ranChartCone (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (W : SpacesEtale B S hS X) :
    Cone (StructuredArrow.proj (op W) (comparisonFunctor B S hS X).op ⋙ F) :=
  (Functor.RightExtension.mk _
    ((comparisonFunctor B S hS X).op.ranCounit.app F)).coneAt (op W)

/-- The sections over `W` of the right Kan extension along the comparison functor are the limit
of the sections over the étale scheme charts of `X` above `W`. -/
noncomputable def ranChartIsLimit (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (W : SpacesEtale B S hS X) :
    IsLimit (ranChartCone B S hS X F W) :=
  (comparisonFunctor B S hS X).op.isPointwiseRightKanExtensionRanCounit F (op W)

/-- Restricting a section along a morphism of étale algebraic spaces over `X` and projecting to
a chart above the source is projecting to the same chart, regarded as a chart above the target
through that morphism. -/
theorem ranChartCone_π_map (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) {W W' : SpacesEtale B S hS X} (k : W' ⟶ W)
    (j : StructuredArrow (op W') (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj F).obj (op W)) :
    (ranChartCone B S hS X F W').π.app j
        (((comparisonFunctor B S hS X).op.ran.obj F).map k.op a) =
      (ranChartCone B S hS X F W).π.app (StructuredArrow.mk (k.op ≫ j.hom)) a := by
  simp only [Functor.RightExtension.coneAt_π_app, types_comp_apply,
    Functor.RightExtension.mk_left, Functor.RightExtension.mk_hom, StructuredArrow.mk_right,
    StructuredArrow.mk_hom_eq_self, ← Functor.map_comp_apply]

/-- Two sections over `W` of the right Kan extension agree as soon as all their chart
projections agree. -/
theorem ranChartCone_π_ext (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (W : SpacesEtale B S hS X)
    {a b : ((comparisonFunctor B S hS X).op.ran.obj F).obj (op W)}
    (h : ∀ j, (ranChartCone B S hS X F W).π.app j a =
      (ranChartCone B S hS X F W).π.app j b) :
    a = b :=
  (Types.isLimitEquivSections (ranChartIsLimit B S hS X F W)).injective
    (Subtype.ext (funext h))

/-- Equal étale scheme charts above `W` have the same chart projection, stated with `HEq`. -/
theorem ranChartCone_π_congr (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (W : SpacesEtale B S hS X)
    {j j' : StructuredArrow (op W) (comparisonFunctor B S hS X).op} (h : j = j')
    (a : ((comparisonFunctor B S hS X).op.ran.obj F).obj (op W)) :
    HEq ((ranChartCone B S hS X F W).π.app j a)
      ((ranChartCone B S hS X F W).π.app j' a) := by
  subst h
  rfl

/-! ### Chart diagrams and the cartesian index category -/

/-- Two chart diagrams over `f` with equal source charts, equal target charts and
heterogeneously equal vertical morphisms of schemes are equal. -/
theorem ChartDiagram.ext {f : X ⟶ Y} (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : d.U = d'.U) (hV : d.V = d'.V) (hg : HEq d.g d'.g) : d = d' := by
  obtain ⟨U, V, g, c⟩ := d
  obtain ⟨U', V', g', c'⟩ := d'
  subst hU hV
  obtain rfl := eq_of_heq hg
  rfl

/-- The chart diagram attached to an étale scheme chart of `X` above `X ×_Y V`: its vertical
morphism of schemes is `AlgebraicGeometry.Space.chartBaseChangeMap`, the Yoneda preimage of the
composite with the cartesian projection. -/
noncomputable def chartDiagramOfIndex (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := j.right.unop
  V := V
  g := chartBaseChangeMap B S hS f V j
  comm := by
    have hw := ((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj V)).w
    have hover : (SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
        ((spacesBaseChange B S hS f).functor.obj
          ((comparisonFunctor B S hS Y).obj V)).1.hom =
        ((comparisonFunctor B S hS X).obj j.right.unop).1.hom := Over.w _
    have key : ((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj V)) ≫
          ((comparisonFunctor B S hS Y).obj V).1.hom =
        ((comparisonFunctor B S hS X).obj j.right.unop).1.hom ≫ f := by
      rw [Category.assoc, hw, ← Category.assoc, hover]
    rw [yoneda_map_chartBaseChangeMap]
    exact (congrArg (fun q ↦ q.hom) key).symm

/-- The Yoneda morphism of a chart diagram, as a morphism of the algebraic spaces represented
by its two charts. -/
def chartDiagramSpaceMap (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj d.U) ⟶
      (SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj d.V) :=
  ObjectProperty.homMk (yoneda.map d.g)

/-- The commutativity of a chart diagram, read in the category of algebraic spaces. -/
theorem chartDiagramSpaceMap_w (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartDiagramSpaceMap B S hS f d ≫ ((comparisonFunctor B S hS Y).obj d.V).1.hom =
      ((comparisonFunctor B S hS X).obj d.U).1.hom ≫ f :=
  ObjectProperty.hom_ext _ d.comm.symm

/-- The cartesian form of a chart diagram: its source chart as an étale algebraic space above
`X ×_Y V`, through the morphism obtained from the commutativity of the diagram by the universal
property of the cartesian square `(AlgebraicGeometry.Space.spacesBaseChange B S hS f).isPullback`.
-/
noncomputable def chartLift (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (comparisonFunctor B S hS X).obj d.U ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj d.V) :=
  ObjectProperty.homMk (Over.homMk
    (((spacesBaseChange B S hS f).isPullback
        ((comparisonFunctor B S hS Y).obj d.V)).lift
      (chartDiagramSpaceMap B S hS f d)
      ((comparisonFunctor B S hS X).obj d.U).1.hom
      (chartDiagramSpaceMap_w B S hS f d))
    (((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj d.V)).lift_snd _ _ _))

/-- The cartesian form of a chart diagram followed by the cartesian projection is the Yoneda
morphism of the diagram. -/
theorem chartLift_projection (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f d) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V) =
      chartDiagramSpaceMap B S hS f d :=
  ((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS Y).obj d.V)).lift_fst _ _ _

/-- The cartesian form of a chart diagram is the *only* morphism to `X ×_Y V` over `X` whose
composite with the cartesian projection is the Yoneda morphism of the diagram. -/
theorem chartLift_unique (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj d.V))
    (hh : ((SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom = yoneda.map d.g) :
    h = chartLift B S hS f d := by
  refine (SpacesEtale.toSpaces B S hS X).map_injective ?_
  refine ((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS Y).obj d.V)).hom_ext ?_ ?_
  · rw [chartLift_projection]
    exact ObjectProperty.hom_ext _ hh
  · exact (Over.w _).trans (Over.w _).symm

/-- The étale scheme chart of `X` above `X ×_Y V` attached to a chart diagram over `V`: the
object of the index category of `AlgebraicGeometry.Space.ranChartIsLimit` which the chart
diagram names. -/
noncomputable def indexOfChartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    StructuredArrow (op (chartBaseChange B S hS f d.V))
      (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk (Y := op d.U) (chartLift B S hS f d).op

/-- The chart diagram attached to the cartesian form of a chart diagram is that chart
diagram. -/
theorem chartDiagramOfIndex_indexOfChartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartDiagramOfIndex B S hS f d.V (indexOfChartDiagram B S hS f d) = d := by
  refine ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq (yoneda.map_injective ?_))
  exact (yoneda_map_chartBaseChangeMap B S hS f d.V (indexOfChartDiagram B S hS f d)).trans
    (congrArg (fun q ↦ q.hom) (chartLift_projection B S hS f d))

/-- The cartesian form of the chart diagram attached to an étale scheme chart of `X` above
`X ×_Y V` is that chart: the two constructions are mutually inverse. -/
theorem indexOfChartDiagram_chartDiagramOfIndex (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op) :
    indexOfChartDiagram B S hS f (chartDiagramOfIndex B S hS f V j) = j := by
  have key : chartLift B S hS f (chartDiagramOfIndex B S hS f V j) = j.hom.unop :=
    (chartLift_unique B S hS f (chartDiagramOfIndex B S hS f V j) j.hom.unop
      (yoneda_map_chartBaseChangeMap B S hS f V j).symm).symm
  exact (congrArg StructuredArrow.mk (congrArg Quiver.Hom.op key)).trans
    (StructuredArrow.eq_mk j).symm

/-- The cartesian form of a chart diagram is the only morphism to `X ×_Y V` over `X` whose
composite with the cartesian projection is the Yoneda morphism of the diagram, read in the
category of algebraic spaces. -/
theorem chartLift_eq (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj d.V))
    (hh : (SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V) =
      chartDiagramSpaceMap B S hS f d) :
    h = chartLift B S hS f d :=
  chartLift_unique B S hS f d h (congrArg (fun q ↦ q.hom) hh)

/-- Chart diagrams are compatible with restriction of both charts: the cartesian form of a
chart diagram is natural in the diagram. -/
theorem chartLift_naturality (f : X ⟶ Y) (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hcond : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j) :
    chartLift B S hS f d' ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j) =
      (comparisonFunctor B S hS X).map i ≫ chartLift B S hS f d := by
  have hi : yoneda.map ((SmallEtale.toOver B S hS X.1).map i) ≫ d.U.1.hom = d'.U.1.hom :=
    CostructuredArrow.w i.hom
  let d'' : ChartDiagram B S hS X.1 Y.1 f.hom :=
    { U := d'.U
      V := d.V
      g := (SmallEtale.toOver B S hS X.1).map i ≫ d.g
      comm := by
        rw [← hi, Category.assoc, d.comm, CategoryTheory.Functor.map_comp, Category.assoc] }
  have hnat : (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)) ≫
      (spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj d.V) =
      (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d'.V) ≫
        (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map j) :=
    (spacesBaseChange B S hS f).projection.naturality ((comparisonFunctor B S hS Y).map j)
  have key : (SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f d' ≫
        (spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map j)) ≫
      (spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj d.V) =
      chartDiagramSpaceMap B S hS f d' ≫
        (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map j) := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hnat, ← Category.assoc,
      chartLift_projection]
  have key' : (SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map i ≫
        chartLift B S hS f d) ≫
      (spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj d.V) =
      (SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map i) ≫
        chartDiagramSpaceMap B S hS f d := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, chartLift_projection]
  refine Eq.trans (chartLift_eq B S hS f d'' _ (key.trans (ObjectProperty.hom_ext _ ?_)))
    (chartLift_eq B S hS f d'' _ (key'.trans (ObjectProperty.hom_ext _ ?_))).symm
  · refine Eq.trans (congrArg (fun q ↦ yoneda.map d'.g ≫ q)
      (toSpaces_comparisonFunctor_map_hom B S hS Y j)) ?_
    exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map hcond.symm)
  · refine Eq.trans (congrArg (fun q ↦ q ≫ yoneda.map d.g)
      (toSpaces_comparisonFunctor_map_hom B S hS X i)) ?_
    exact (yoneda.map_comp _ _).symm

/-! ### The bijection in the Kan-extension picture -/

/-- Two `f`-maps with the same components are equal. -/
@[ext]
theorem FMap.ext {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : F ⟶ G}
    {P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u} {Q : (SmallEtale B S hS G)ᵒᵖ ⥤ Type u}
    {ξ ξ' : FMap B S hS F G m P Q} (h : ξ.app = ξ'.app) : ξ = ξ' := by
  obtain ⟨a, ha⟩ := ξ
  obtain ⟨a', ha'⟩ := ξ'
  obtain rfl : a = a' := h
  rfl

/-- The components of an `f`-map at equal chart diagrams agree on heterogeneously equal
sections, stated with `HEq`. -/
theorem FMap.app_heq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : F ⟶ G}
    {P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u} {Q : (SmallEtale B S hS G)ᵒᵖ ⥤ Type u}
    (ξ : FMap B S hS F G m P Q) {d d' : ChartDiagram B S hS F G m} (h : d = d')
    {s : Q.obj (op d.V)} {s' : Q.obj (op d'.V)} (hs : HEq s s') :
    HEq (ξ.app d s) (ξ.app d' s') := by
  subst h
  obtain rfl := eq_of_heq hs
  rfl

section FixedData

variable (f : X ⟶ Y) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))

/-- The cone of the components of an `f`-map over an étale scheme chart `V` of `Y`: a section of
`Q` over `V` goes to the family of its images under the components of the `f`-map, one for each
étale scheme chart of `X` above `X ×_Y V`. -/
noncomputable def fmapChartCone (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj)
    (V : SmallEtale B S hS Y.1) :
    Cone (StructuredArrow.proj (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op ⋙ P.obj) where
  pt := Q.obj.obj (op V)
  π :=
    { app := fun j ↦ TypeCat.ofHom fun s ↦ ξ.app (chartDiagramOfIndex B S hS f V j) s
      naturality := fun j₁ j₂ φ ↦ by
        refine (Category.id_comp _).trans (ConcreteCategory.hom_ext _ _ fun s ↦ ?_)
        have hnat := ξ.naturality (chartDiagramOfIndex B S hS f V j₁)
          (chartDiagramOfIndex B S hS f V j₂) φ.right.unop (𝟙 V)
          ((chartBaseChangeMap_comp B S hS f V φ).symm.trans
            ((Category.comp_id (chartBaseChangeMap B S hS f V j₂)).symm.trans
              (congrArg (fun q ↦ chartBaseChangeMap B S hS f V j₂ ≫ q)
                ((SmallEtale.toOver B S hS Y.1).map_id V).symm))) s
        have h1 : (ConcreteCategory.hom (Q.obj.map (𝟙 V).op)) s = s := by simp
        exact (congrArg (ξ.app (chartDiagramOfIndex B S hS f V j₂)) h1.symm).trans
          (hnat.trans (congrArg
            (fun m ↦ (ConcreteCategory.hom (P.obj.map m))
              (ξ.app (chartDiagramOfIndex B S hS f V j₁) s))
            (Quiver.Hom.op_unop φ.right))) }

/-- The section of the direct image over an étale scheme chart `V` of `Y` attached to an
`f`-map and a section of `Q` over `V`: the limit of the family of images of that section under
the components of the `f`-map. -/
noncomputable def fmapRanApp (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj)
    (V : SmallEtale B S hS Y.1) (s : Q.obj.obj (op V)) :
    ((comparisonFunctor B S hS X).op.ran.obj P.obj).obj
      (op (chartBaseChange B S hS f V)) :=
  (ranChartIsLimit B S hS X P.obj (chartBaseChange B S hS f V)).lift
    (fmapChartCone B S hS f P Q ξ V) s

/-- The chart projections of `AlgebraicGeometry.Space.fmapRanApp` are the components of the
`f`-map. -/
theorem fmapRanApp_π (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op) (s : Q.obj.obj (op V)) :
    (ranChartCone B S hS X P.obj (chartBaseChange B S hS f V)).π.app j
        (fmapRanApp B S hS f P Q ξ V s) =
      ξ.app (chartDiagramOfIndex B S hS f V j) s :=
  ConcreteCategory.congr_hom
    ((ranChartIsLimit B S hS X P.obj (chartBaseChange B S hS f V)).fac
      (fmapChartCone B S hS f P Q ξ V) j) s

/-- The homomorphism from `Q` into the direct image of `P` attached to an `f`-map: over an étale
scheme chart `V` of `Y` it is `AlgebraicGeometry.Space.fmapRanApp`. -/
noncomputable def fmapRan (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) :
    Q ⟶ (smallEtaleDirectImageRan B S hS f).obj P :=
  ObjectProperty.homMk
    { app := fun A ↦ TypeCat.ofHom (fmapRanApp B S hS f P Q ξ A.unop)
      naturality := fun A A' g ↦ ConcreteCategory.hom_ext _ _ fun s ↦ by
        change fmapRanApp B S hS f P Q ξ A'.unop ((ConcreteCategory.hom (Q.obj.map g)) s) =
          (ConcreteCategory.hom (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
            ((spacesBaseChange B S hS f).functor.map
              ((comparisonFunctor B S hS Y).map g.unop)).op))
            (fmapRanApp B S hS f P Q ξ A.unop s)
        refine ranChartCone_π_ext B S hS X P.obj (chartBaseChange B S hS f A'.unop)
          (fun j ↦ ?_)
        rw [fmapRanApp_π, ranChartCone_π_map B S hS X P.obj
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map g.unop)) j, fmapRanApp_π]
        have hcond : (SmallEtale.toOver B S hS X.1).map (𝟙 j.right.unop) ≫
            (chartDiagramOfIndex B S hS f A.unop
              (StructuredArrow.mk (((spacesBaseChange B S hS f).functor.map
                ((comparisonFunctor B S hS Y).map g.unop)).op ≫ j.hom))).g =
            (chartDiagramOfIndex B S hS f A'.unop j).g ≫
              (SmallEtale.toOver B S hS Y.1).map g.unop := by
          simp only [CategoryTheory.Functor.map_id]
          exact chartBaseChangeMap_map B S hS f g.unop j
        have hnat := ξ.naturality
          (chartDiagramOfIndex B S hS f A.unop
            (StructuredArrow.mk (((spacesBaseChange B S hS f).functor.map
              ((comparisonFunctor B S hS Y).map g.unop)).op ≫ j.hom)))
          (chartDiagramOfIndex B S hS f A'.unop j) (𝟙 j.right.unop) g.unop hcond s
        have h1 : ∀ x : P.obj.obj j.right,
            (ConcreteCategory.hom (P.obj.map (𝟙 j.right.unop).op)) x = x := by simp
        exact (congrArg
          (fun m ↦ ξ.app (chartDiagramOfIndex B S hS f A'.unop j)
            ((ConcreteCategory.hom (Q.obj.map m)) s))
          (Quiver.Hom.op_unop g).symm).trans (hnat.trans (h1 _)) }

/-- `AlgebraicGeometry.Space.fmapRan` is the only homomorphism whose chart projections are the
components of the `f`-map. -/
theorem fmapRan_unique (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj)
    (ψ : Q ⟶ (smallEtaleDirectImageRan B S hS f).obj P)
    (h : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V))
        (comparisonFunctor B S hS X).op) (s : Q.obj.obj (op V)),
      (ranChartCone B S hS X P.obj (chartBaseChange B S hS f V)).π.app j
          (ψ.hom.app (op V) s) =
        ξ.app (chartDiagramOfIndex B S hS f V j) s) :
    ψ = fmapRan B S hS f P Q ξ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun A ↦
    ConcreteCategory.hom_ext _ _ fun s ↦ ?_))
  refine ranChartCone_π_ext B S hS X P.obj (chartBaseChange B S hS f A.unop) (fun j ↦ ?_)
  exact (h A.unop j s).trans (fmapRanApp_π B S hS f P Q ξ A.unop j s).symm

/-- The `f`-map attached to a homomorphism from `Q` into the direct image of `P`: the component
at a chart diagram is the chart projection, at the cartesian form of that diagram, of the
section of the direct image. -/
noncomputable def ranFmap (ψ : Q ⟶ (smallEtaleDirectImageRan B S hS f).obj P) :
    FMap B S hS X.1 Y.1 f.hom P.obj Q.obj where
  app := fun d s ↦ (ranChartCone B S hS X P.obj (chartBaseChange B S hS f d.V)).π.app
    (indexOfChartDiagram B S hS f d) (ψ.hom.app (op d.V) s)
  naturality := fun d d' i j hcond s ↦ by
    have hlift : ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map j)).op ≫
        (indexOfChartDiagram B S hS f d').hom =
        (indexOfChartDiagram B S hS f d).hom ≫
          (comparisonFunctor B S hS X).op.map i.op :=
      congrArg Quiver.Hom.op (chartLift_naturality B S hS f d d' i j hcond)
    have hstep : ∀ a : ((comparisonFunctor B S hS X).op.ran.obj P.obj).obj
          (op (chartBaseChange B S hS f d.V)),
        (ranChartCone B S hS X P.obj (chartBaseChange B S hS f d'.V)).π.app
            (indexOfChartDiagram B S hS f d')
            ((ConcreteCategory.hom (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
              ((spacesBaseChange B S hS f).functor.map
                ((comparisonFunctor B S hS Y).map j)).op)) a) =
          (ConcreteCategory.hom (P.obj.map i.op))
            ((ranChartCone B S hS X P.obj (chartBaseChange B S hS f d.V)).π.app
              (indexOfChartDiagram B S hS f d) a) := by
      intro a
      rw [ranChartCone_π_map B S hS X P.obj (W := chartBaseChange B S hS f d.V)
        (W' := chartBaseChange B S hS f d'.V)
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map j))
        (indexOfChartDiagram B S hS f d'), hlift]
      exact (congrArg (fun φ ↦ (ConcreteCategory.hom φ) a)
        ((ranChartCone B S hS X P.obj (chartBaseChange B S hS f d.V)).w
          (StructuredArrow.homMk (f := indexOfChartDiagram B S hS f d)
            (f' := StructuredArrow.mk ((indexOfChartDiagram B S hS f d).hom ≫
              (comparisonFunctor B S hS X).op.map i.op)) i.op rfl))).symm
    have hψ := congrArg (fun φ ↦ (ConcreteCategory.hom φ) s) (ψ.hom.naturality j.op)
    simp only [types_comp_apply] at hψ
    exact (congrArg
      (fun x ↦ (ranChartCone B S hS X P.obj (chartBaseChange B S hS f d'.V)).π.app
        (indexOfChartDiagram B S hS f d') x) hψ).trans
      (hstep (ψ.hom.app (op d.V) s))

/-- In the Kan-extension form of the direct image, `f`-maps from `Q` to `P` are exactly
homomorphisms from `Q` into the direct image of `P`; the two directions are
`AlgebraicGeometry.Space.fmapRan` and `AlgebraicGeometry.Space.ranFmap`. -/
noncomputable def fmapRanEquiv :
    FMap B S hS X.1 Y.1 f.hom P.obj Q.obj ≃
      (Q ⟶ (smallEtaleDirectImageRan B S hS f).obj P) where
  toFun := fmapRan B S hS f P Q
  invFun := ranFmap B S hS f P Q
  left_inv ξ := by
    refine FMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
    refine (fmapRanApp_π B S hS f P Q ξ d.V (indexOfChartDiagram B S hS f d) s).trans ?_
    exact eq_of_heq (FMap.app_heq B S hS ξ
      (chartDiagramOfIndex_indexOfChartDiagram B S hS f d) HEq.rfl)
  right_inv ψ := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun A ↦
      ConcreteCategory.hom_ext _ _ fun s ↦ ?_))
    refine ranChartCone_π_ext B S hS X P.obj (chartBaseChange B S hS f A.unop) (fun j ↦ ?_)
    refine Eq.trans (fmapRanApp_π B S hS f P Q (ranFmap B S hS f P Q ψ) A.unop j s) ?_
    exact eq_of_heq (ranChartCone_π_congr B S hS X P.obj (chartBaseChange B S hS f A.unop)
      (indexOfChartDiagram_chartDiagramOfIndex B S hS f A.unop j) (ψ.hom.app A s))

end FixedData

/-! ### The chart correspondence -/

/-- The comparison from the right Kan extension of `P` along the comparison functor to a
spaces-étale sheaf `H` presenting `P`: the comparison isomorphism of the quasi-inverse of the
comparison equivalence with the Kan extension, the presentation isomorphism carried to the
spaces-étale site, and the inverse of the unit of the comparison equivalence. -/
noncomputable def presentationComparison (X : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H) :
    (smallEtaleComparisonRan B S hS X).obj P ⟶ H :=
  (smallEtaleComparisonRanIso B S hS X).inv.app P ≫
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map i.hom ≫
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitInv.app H

/-- Restriction along the comparison functor takes
`AlgebraicGeometry.Space.presentationComparison` to the counit of the Kan-extension adjunction
followed by the presentation isomorphism. -/
theorem counit_comp_presentation (X : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H) :
    ((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app P ≫
        i.hom =
      (smallEtaleComparisonRestriction B S hS X).map
        (presentationComparison B S hS X P H i) :=
  Equivalence.counit_comp_hom_eq_map_rightAdjointUniq
    (smallEtaleComparisonRestriction B S hS X).asEquivalence _ P H i

/-- For a presentation of `P` by a sheaf `H` on the spaces-étale site, the chart projection of a
section of the Kan extension, pushed into `H` by the presentation, is the restriction along the
chart of the corresponding section of `H`. -/
theorem presentation_ranChartCone_π (X : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
    (W : SpacesEtale B S hS X)
    (j : StructuredArrow (op W) (comparisonFunctor B S hS X).op)
    (b : ((smallEtaleComparisonRan B S hS X).obj P).obj.obj (op W)) :
    i.hom.hom.app j.right ((ranChartCone B S hS X P.obj W).π.app j b) =
      H.obj.map j.hom ((presentationComparison B S hS X P H i).hom.app (op W) b) := by
  have hcounit : (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app P).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app P.obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  have hcz := congrArg (fun α : ((smallEtaleComparisonRestriction B S hS X).obj
        ((smallEtaleComparisonRan B S hS X).obj P)).obj ⟶ P.obj ↦
      (ConcreteCategory.hom (α.app j.right))
        ((ConcreteCategory.hom
          (((smallEtaleComparisonRan B S hS X).obj P).obj.map j.hom)) b)) hcounit
  refine Eq.trans ?_ (congrArg (fun φ ↦ (ConcreteCategory.hom φ) b)
    ((presentationComparison B S hS X P H i).hom.naturality j.hom))
  refine Eq.trans (congrArg (fun y ↦ (ConcreteCategory.hom (i.hom.hom.app j.right)) y)
    hcz.symm) ?_
  exact congrArg (fun m : (smallEtaleComparisonRestriction B S hS X).obj
        ((smallEtaleComparisonRan B S hS X).obj P) ⟶
        (smallEtaleComparisonRestriction B S hS X).obj H ↦
      (ConcreteCategory.hom (m.hom.app j.right))
        ((ConcreteCategory.hom
          (((smallEtaleComparisonRan B S hS X).obj P).obj.map j.hom)) b))
    (counit_comp_presentation B S hS X P H i)

/-- `f`-maps from `Q` to `P` are exactly homomorphisms from `Q` into the direct image
`AlgebraicGeometry.Space.smallEtaleDirectImage` of `P`: the bijection
`AlgebraicGeometry.Space.fmapRanEquiv` composed with
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`. -/
noncomputable def fmapDirectImageEquiv (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    FMap B S hS X.1 Y.1 f.hom P.obj Q.obj ≃
      (Q ⟶ (smallEtaleDirectImage B S hS f).obj P) :=
  (fmapRanEquiv B S hS f P Q).trans
    { toFun := fun ψ ↦ ψ ≫ (smallEtaleDirectImageRanIso B S hS f).inv.app P
      invFun := fun ψ ↦ ψ ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app P
      left_inv := fun ψ ↦ (Category.assoc _ _ _).trans
        ((congrArg (fun q ↦ ψ ≫ q)
          (Iso.inv_hom_id_app (smallEtaleDirectImageRanIso B S hS f) P)).trans
          (Category.comp_id ψ))
      right_inv := fun ψ ↦ (Category.assoc _ _ _).trans
        ((congrArg (fun q ↦ ψ ≫ q)
          (Iso.hom_inv_id_app (smallEtaleDirectImageRanIso B S hS f) P)).trans
          (Category.comp_id ψ)) }

/-- The bijection `AlgebraicGeometry.Space.fmapDirectImageEquiv` satisfies the sectionwise
characterization `AlgebraicGeometry.Space.IsChartCorrespondence`: through the geometric
comparison, restriction along the induced map to a cartesian spaces-étale chart computes the
component of the `f`-map at the chart diagram. -/
theorem fmapDirectImageEquiv_isChartCorrespondence (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    IsChartCorrespondence B S hS f P Q (fmapDirectImageEquiv B S hS f P Q) := by
  intro H i ξ d hmap hheq s
  obtain rfl : hmap = chartLift B S hS f d :=
    chartLift_unique B S hS f d hmap (eq_of_heq hheq)
  have hc : (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H =
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        smallEtaleComparisonRestriction B S hS Y).map
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitInv.app H) :=
    Category.comp_id _
  have h1 : ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        smallEtaleComparisonRestriction B S hS Y).map
          (presentationComparison B S hS X P H i) =
      (smallEtaleDirectImageRanIso B S hS f).inv.app P ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
        ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
          smallEtaleComparisonRestriction B S hS Y).map
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitInv.app H) :=
    (CategoryTheory.Functor.map_comp _ _ _).trans
      (congrArg (fun q ↦ (smallEtaleDirectImageRanIso B S hS f).inv.app P ≫ q)
        (CategoryTheory.Functor.map_comp _ _ _))
  have hψ : (fmapDirectImageEquiv B S hS f P Q) ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H =
      fmapRan B S hS f P Q ξ ≫
        ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
          smallEtaleComparisonRestriction B S hS Y).map
          (presentationComparison B S hS X P H i) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun q ↦ fmapRan B S hS f P Q ξ ≫ q)
        ((congrArg (fun q ↦ (smallEtaleDirectImageRanIso B S hS f).inv.app P ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫ q)
            hc).trans h1.symm))
  have hsec := congrArg (fun m : Q ⟶ (smallEtaleComparisonRestriction B S hS Y).obj
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H) ↦
      (ConcreteCategory.hom (m.hom.app (op d.V))) s) hψ
  have hπ : (ranChartCone B S hS X P.obj (chartBaseChange B S hS f d.V)).π.app
        (indexOfChartDiagram B S hS f d) (fmapRanApp B S hS f P Q ξ d.V s) =
      ξ.app d s :=
    (fmapRanApp_π B S hS f P Q ξ d.V (indexOfChartDiagram B S hS f d) s).trans
      (eq_of_heq (FMap.app_heq B S hS ξ
        (chartDiagramOfIndex_indexOfChartDiagram B S hS f d) HEq.rfl))
  refine Eq.trans ?_ (congrArg
    (fun y ↦ (ConcreteCategory.hom (H.obj.map (chartLift B S hS f d).op)) y) hsec.symm)
  refine Eq.trans (congrArg
    (fun y ↦ (ConcreteCategory.hom (i.hom.hom.app (op d.U))) y) hπ.symm) ?_
  exact presentation_ranChartCone_π B S hS X P H i (chartBaseChange B S hS f d.V)
    (indexOfChartDiagram B S hS f d) (fmapRanApp B S hS f P Q ξ d.V s)

/-- The *chart correspondence* of a morphism `f : X ⟶ Y` of algebraic spaces: a bijection
between the `f`-maps from a sheaf of sets `Q` on the small étale site of `Y` to a sheaf of sets
`P` on the small étale site of `X`, and the homomorphisms from `Q` into the direct image of `P`
along `AlgebraicGeometry.Space.smallEtaleRingedToposHom`, satisfying the sectionwise
characterization `AlgebraicGeometry.Space.IsChartCorrespondence`. -/
@[stacks 03G4 "f-maps are exactly maps into the direct image"]
noncomputable def chartCorrespondence (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    { e : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj ≃
        (Q ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj P) //
      IsChartCorrespondence B S hS f P Q e } :=
  ⟨fmapDirectImageEquiv B S hS f P Q,
    fmapDirectImageEquiv_isChartCorrespondence B S hS f P Q⟩

/-- `f`-maps from `Q` to `P` are exactly homomorphisms from the inverse image of `Q` into `P`,
the inverse image being that of `AlgebraicGeometry.Space.smallEtaleRingedToposHom`. -/
@[stacks 03G4 "f-maps are exactly maps out of the inverse image"]
noncomputable def fmapInverseImageEquiv (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    FMap B S hS X.1 Y.1 f.hom P.obj Q.obj ≃
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj Q ⟶ P) :=
  (fmapDirectImageEquiv B S hS f P Q).trans
    (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv Q P).symm)

end AlgebraicGeometry.Space

end
