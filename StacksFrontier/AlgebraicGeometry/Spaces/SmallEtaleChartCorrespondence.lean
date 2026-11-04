module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps of sheaves along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `F` be a sheaf of sets on the small étale site of `X` and `G` one on the small
étale site of `Y`. Three sets are canonically in bijection: the maps `G ⟶ f_{small, *}F`, the
maps `f_{small}^{-1}G ⟶ F`, and the `f`-maps `G ⟶ F` — the families of maps of sections
`G(V) ⟶ F(U)` indexed by the commutative diagrams of étale scheme charts over `f`, compatible
with further étale restriction of both charts. This file constructs those bijections.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramOfBaseChangeArrow` and
  `AlgebraicGeometry.Space.baseChangeArrowOfChartDiagram` are the two directions of the
  identification of arrows into the cartesian base change `X ×_Y V` with commutative diagrams of
  étale scheme charts.
* `AlgebraicGeometry.Space.comparisonSectionsIso` exhibits the sections of a spaces-étale
  sheaf over an object as the limit of its sections over the étale scheme charts mapping into
  that object.
* `AlgebraicGeometry.Space.fMapDescendedSection` is the section of the direct image attached
  to an `f`-map, `AlgebraicGeometry.Space.descendedHomPresheaf` the resulting map of
  presheaves — the presheaf of sections on `Y` need not be a sheaf — and
  `AlgebraicGeometry.Space.descendedHom` the map of sheaves it is when that presheaf is one;
  `AlgebraicGeometry.Space.fMapOfPushforwardHom` is the inverse construction and
  `AlgebraicGeometry.Space.descendedHomEquiv` the bijection they make up, for a sheaf on the
  small étale site of `X` presented as the restriction of a spaces-étale sheaf.

## Main results

* `AlgebraicGeometry.Space.fMapEquivPushforwardHom`: `f`-maps are canonically the maps into the
  small étale direct image.
* `AlgebraicGeometry.Space.fMapEquivInverseImageHom`: `f`-maps are canonically the maps out of
  the small étale inverse image, and the induced bijection with the maps into the direct image is
  the adjunction bijection of the morphism of topoi.
* `AlgebraicGeometry.Space.fMapEquivPushforwardHom_chart`: the bijection with the maps into the
  direct image is the canonical one. Transport a sheaf on the small étale site of `X` through an
  isomorphism with the restriction of a spaces-étale sheaf; then on a diagram of scheme charts
  the transported `f`-map is restriction of the section of the direct image along the induced
  arrow into the cartesian base change.

## Implementation notes

The sheaves here are valued in `Type (u + 1)`, the universe of the objects of the two étale
sites. Consequently `AlgebraicGeometry.Space.comparisonRestriction` is a second instantiation of
`AlgebraicGeometry.Space.smallEtaleComparisonRestriction`, which is pinned to the universe
`Type u` of the structure rings, and `AlgebraicGeometry.Space.comparisonSectionsIso` is, for an
arbitrary sheaf, the pointwise-limit description of the sections of the direct image that
`AlgebraicGeometry.Space.chartIsLimit` gives for the structure sheaf.

`AlgebraicGeometry.Space.descendedHomEquiv` is stated relative to a presentation of the
source sheaf as the restriction of a spaces-étale sheaf;
`AlgebraicGeometry.Space.fMapEquivPushforwardHom` is obtained from it by taking the preimage of
the source sheaf under the comparison equivalence, and `AlgebraicGeometry.Space.descendedHom_map`
makes that independent of the chosen presentation.

## References

* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### Arrows into the cartesian base change and diagrams of charts -/

/-- A commutative diagram of étale scheme charts over `f` is determined by its two charts and
its vertical morphism of schemes; the commutativity proof is not part of the datum. -/
theorem chartDiagram_mk_eq {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    {hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom}
    {hc' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V.1.hom} (hg : g = g') :
    (⟨U, V, g, hc⟩ : ChartDiagram B S hS X.1 Y.1 f.hom) = ⟨U, V, g', hc'⟩ := by
  cases hg
  rfl

/-- An `f`-map depends on the vertical morphism of each diagram of charts and not on the
proof that the diagram commutes. -/
theorem fMap_app_congr {P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type (u + 1)}
    {Q : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type (u + 1)}
    (ξ : FMap B S hS X.1 Y.1 f.hom P Q)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    {hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom}
    {hc' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V.1.hom}
    (hg : g = g') (s : Q.obj (op V)) :
    ξ.app ⟨U, V, g, hc⟩ s = ξ.app ⟨U, V, g', hc'⟩ s := by
  cases hg
  rfl

/-- An arrow from an étale scheme chart of `X` into the cartesian base change `X ×_Y V`
makes a commutative square with the structure morphisms of the two charts and `f`. -/
theorem chartBaseChangeMap_comm (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V) :
    U.1.hom ≫ f.hom =
      yoneda.map (chartBaseChangeMap B S hS f V (StructuredArrow.mk h.op)) ≫ V.1.hom := by
  have hw : (SpacesEtale.toSpaces B S hS X).map h ≫ (chartBaseChange B S hS f V).1.hom =
      ((comparisonFunctor B S hS X).obj U).1.hom := Over.w h.hom
  have key : ((comparisonFunctor B S hS X).obj U).1.hom ≫ f =
      ((SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj V)) ≫
        ((comparisonFunctor B S hS Y).obj V).1.hom := by
    rw [Category.assoc, ((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj V)).w, ← hw, Category.assoc]
  rw [yoneda_map_chartBaseChangeMap]
  exact congrArg (fun k ↦ k.hom) key

/-- The diagram of étale scheme charts over `f` attached to an arrow from a chart of the
source into the cartesian base change `X ×_Y V` of a chart `V` of the target: its vertical
morphism of schemes is `AlgebraicGeometry.Space.chartBaseChangeMap`, the Yoneda preimage of
the composite of the arrow with the cartesian projection. -/
noncomputable def chartDiagramOfBaseChangeArrow (U : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := U
  V := V
  g := chartBaseChangeMap B S hS f V (StructuredArrow.mk h.op)
  comm := chartBaseChangeMap_comm B S hS f U V h

/-- The vertical morphism of the diagram attached to an arrow into the cartesian base change
has, as its Yoneda morphism, the composite of the arrow with the cartesian projection. -/
theorem yoneda_map_chartDiagramOfBaseChangeArrow_g (U : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V) :
    yoneda.map (chartDiagramOfBaseChangeArrow B S hS f U V h).g =
      ((SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj V)).hom :=
  yoneda_map_chartBaseChangeMap B S hS f V (StructuredArrow.mk h.op)

/-- An arrow from a chart of the source into the cartesian base change `X ×_Y V` is
determined by the chartwise morphism it induces: it is a map into a fibre product whose two
projections are the Yoneda morphism of that chartwise morphism and the structure morphism of
the chart. -/
theorem chartBaseChangeMap_injective {U : SmallEtale B S hS X.1}
    {V : SmallEtale B S hS Y.1}
    {a b : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V}
    (hab : chartBaseChangeMap B S hS f V (StructuredArrow.mk a.op) =
      chartBaseChangeMap B S hS f V (StructuredArrow.mk b.op)) : a = b := by
  apply ObjectProperty.hom_ext
  apply (Over.forget X).map_injective
  refine ((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS Y).obj V)).hom_ext ?_ ?_
  · exact ObjectProperty.hom_ext _
      ((yoneda_map_chartBaseChangeMap B S hS f V (StructuredArrow.mk a.op)).symm.trans
        ((congrArg yoneda.map hab).trans
          (yoneda_map_chartBaseChangeMap B S hS f V (StructuredArrow.mk b.op))))
  · exact (Over.w a.hom).trans (Over.w b.hom).symm

/-- The square expressing that the Yoneda morphism of the vertical morphism of a diagram of
charts and the structure morphism of its source chart agree over `Y`. -/
theorem baseChangeArrow_w (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (ObjectProperty.homMk (yoneda.map d.g) :
        (SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj d.U) ⟶
          (SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj d.V)) ≫
        ((comparisonFunctor B S hS Y).obj d.V).1.hom =
      ((comparisonFunctor B S hS X).obj d.U).1.hom ≫ f := by
  exact ObjectProperty.hom_ext _ d.comm.symm

/-- The arrow into the cartesian base change `X ×_Y V` attached to a commutative diagram of
étale scheme charts over `f`: the map into the fibre product given by the Yoneda morphism of
the vertical morphism of schemes and the structure morphism of the source chart. -/
noncomputable def baseChangeArrowOfChartDiagram (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V :=
  ObjectProperty.homMk (Over.homMk
    (((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj d.V)).lift
        (ObjectProperty.homMk (yoneda.map d.g))
        ((comparisonFunctor B S hS X).obj d.U).1.hom (baseChangeArrow_w B S hS f d))
    (((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj d.V)).lift_snd _ _ (baseChangeArrow_w B S hS f d)))

/-- The arrow attached to a diagram of charts composed with the cartesian projection is the
Yoneda morphism of the vertical morphism of the diagram. -/
theorem yoneda_map_baseChangeArrowOfChartDiagram (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ((SpacesEtale.toSpaces B S hS X).map (baseChangeArrowOfChartDiagram B S hS f d) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom =
      yoneda.map d.g :=
  congrArg (fun k ↦ k.hom) (((spacesBaseChange B S hS f).isPullback
    ((comparisonFunctor B S hS Y).obj d.V)).lift_fst
      (ObjectProperty.homMk (yoneda.map d.g))
      ((comparisonFunctor B S hS X).obj d.U).1.hom (baseChangeArrow_w B S hS f d))

/-- An arrow into the cartesian base change whose composite with the cartesian projection is
the Yoneda morphism of a given diagram of charts induces that diagram. -/
theorem chartDiagramOfBaseChangeArrow_g_eq (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : ((SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom = yoneda.map d.g) :
    (chartDiagramOfBaseChangeArrow B S hS f d.U d.V h).g = d.g :=
  yoneda.map_injective
    ((yoneda_map_chartDiagramOfBaseChangeArrow_g B S hS f d.U d.V h).trans hh)

/-- An arrow into the cartesian base change whose composite with the cartesian projection is
the Yoneda morphism of a given diagram of charts is attached to that diagram. -/
theorem chartDiagramOfBaseChangeArrow_eq (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : ((SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom = yoneda.map d.g) :
    chartDiagramOfBaseChangeArrow B S hS f d.U d.V h = d :=
  chartDiagram_mk_eq B S hS f (chartDiagramOfBaseChangeArrow_g_eq B S hS f d h hh)

/-- The diagram attached to the arrow of a diagram has the same vertical morphism. -/
theorem chartDiagramOfBaseChangeArrow_baseChangeArrow_g
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartDiagramOfBaseChangeArrow B S hS f d.U d.V
        (baseChangeArrowOfChartDiagram B S hS f d)).g = d.g :=
  chartDiagramOfBaseChangeArrow_g_eq B S hS f d _
    (yoneda_map_baseChangeArrowOfChartDiagram B S hS f d)

/-- The two constructions are mutually inverse: the diagram attached to the arrow of a
diagram is that diagram. -/
theorem chartDiagramOfBaseChangeArrow_baseChangeArrow
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartDiagramOfBaseChangeArrow B S hS f d.U d.V
        (baseChangeArrowOfChartDiagram B S hS f d) = d :=
  chartDiagramOfBaseChangeArrow_eq B S hS f d _
    (yoneda_map_baseChangeArrowOfChartDiagram B S hS f d)

/-- The two constructions are mutually inverse: the arrow attached to the diagram of an arrow
is that arrow. -/
theorem baseChangeArrowOfChartDiagram_chartDiagram (U : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V) :
    baseChangeArrowOfChartDiagram B S hS f
        (chartDiagramOfBaseChangeArrow B S hS f U V h) = h :=
  chartBaseChangeMap_injective B S hS f
    (chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f
      (chartDiagramOfBaseChangeArrow B S hS f U V h))

/-- A square of arrows into cartesian base changes commutes exactly when the square of the
diagrams of charts they induce commutes. -/
theorem chartDiagram_square_iff {U U' : SmallEtale B S hS X.1}
    {V V' : SmallEtale B S hS Y.1}
    (h : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (h' : (comparisonFunctor B S hS X).obj U' ⟶ chartBaseChange B S hS f V')
    (i : U' ⟶ U) (j : V' ⟶ V) :
    (comparisonFunctor B S hS X).map i ≫ h =
        h' ≫ (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map j) ↔
      (SmallEtale.toOver B S hS X.1).map i ≫
          (chartDiagramOfBaseChangeArrow B S hS f U V h).g =
        (chartDiagramOfBaseChangeArrow B S hS f U' V' h').g ≫
          (SmallEtale.toOver B S hS Y.1).map j := by
  have hi : chartBaseChangeMap B S hS f V
        (StructuredArrow.mk ((comparisonFunctor B S hS X).map i ≫ h).op) =
      (SmallEtale.toOver B S hS X.1).map i ≫
        chartBaseChangeMap B S hS f V (StructuredArrow.mk h.op) :=
    chartBaseChangeMap_comp B S hS f V (j₁ := StructuredArrow.mk h.op)
      (j₂ := StructuredArrow.mk ((comparisonFunctor B S hS X).map i ≫ h).op)
      (StructuredArrow.homMk i.op rfl)
  have hj : chartBaseChangeMap B S hS f V
        (StructuredArrow.mk (h' ≫ (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map j)).op) =
      chartBaseChangeMap B S hS f V' (StructuredArrow.mk h'.op) ≫
        (SmallEtale.toOver B S hS Y.1).map j :=
    chartBaseChangeMap_map B S hS f j (StructuredArrow.mk h'.op)
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · have hi' := hi.symm
    rw [hc] at hi'
    exact hi'.trans hj
  · exact chartBaseChangeMap_injective B S hS f (hi.trans (hc.trans hj.symm))

/-! ### Sections of a spaces-étale sheaf as a limit over the scheme charts -/

section Sections

variable (Z : AlgebraicSpaces B S hS)
  (H : Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1)))

/-- The diagram of sections of a spaces-étale sheaf over the étale scheme charts mapping into
a given object étale over `Z`. -/
noncomputable abbrev chartSectionsDiagram (V : SpacesEtale B S hS Z) :
    StructuredArrow (op V) (comparisonFunctor B S hS Z).op ⥤ Type (u + 1) :=
  StructuredArrow.proj (op V) (comparisonFunctor B S hS Z).op ⋙
    (comparisonFunctor B S hS Z).op ⋙ H.obj

/-- The sections of a spaces-étale sheaf over an object `V` étale over `Z` are the limit of
its sections over the étale scheme charts mapping into `V`. -/
noncomputable def comparisonSectionsIso (V : SpacesEtale B S hS Z) :
    H.obj.obj (op V) ≅ limit (chartSectionsDiagram B S hS Z H V) := by
  have hfull : ((comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).Full := inferInstance
  have hfaithful : ((comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS Z.1)
      (SpacesEtale.topology B S hS Z)).Faithful := inferInstance
  have hunit : IsIso (((comparisonFunctor B S hS Z).sheafAdjunctionCocontinuous
      (Type (u + 1)) (SmallEtale.topology B S hS Z.1)
      (SpacesEtale.topology B S hS Z)).unit.app H) := inferInstance
  have hunit' : IsIso (((comparisonFunctor B S hS Z).op.ranAdjunction
      (Type (u + 1))).unit.app H.obj) := by
    rw [← (comparisonFunctor B S hS Z).sheafAdjunctionCocontinuous_unit_app_hom
      (Type (u + 1)) (SmallEtale.topology B S hS Z.1)
      (SpacesEtale.topology B S hS Z) H]
    exact Functor.map_isIso
      (sheafToPresheaf (SpacesEtale.topology B S hS Z) (Type (u + 1)))
      (((comparisonFunctor B S hS Z).sheafAdjunctionCocontinuous (Type (u + 1))
        (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).unit.app H)
  exact asIso ((((comparisonFunctor B S hS Z).op.ranAdjunction
      (Type (u + 1))).unit.app H.obj).app (op V)) ≪≫
    (comparisonFunctor B S hS Z).op.ranObjObjIsoLimit
      ((comparisonFunctor B S hS Z).op ⋙ H.obj) (op V)

/-- The comparison of sections with the chart limit is induced by the unit of the comparison
adjunction, so its projection to each chart is the canonical right Kan extension cone map. -/
theorem comparisonSectionsIso_hom_π (V : SpacesEtale B S hS Z)
    (k : StructuredArrow (op V) (comparisonFunctor B S hS Z).op) :
    (comparisonSectionsIso B S hS Z H V).hom ≫
        limit.π (chartSectionsDiagram B S hS Z H V) k =
      (((comparisonFunctor B S hS Z).op.ranAdjunction
        (Type (u + 1))).unit.app H.obj).app (op V) ≫
        ((comparisonFunctor B S hS Z).op.ran.obj
          ((comparisonFunctor B S hS Z).op ⋙ H.obj)).map k.hom ≫
        (((comparisonFunctor B S hS Z).op.ranCounit.app
          ((comparisonFunctor B S hS Z).op ⋙ H.obj)).app k.right) := by
  simp [comparisonSectionsIso, Category.assoc]

/-- The projection of the chart limit to a chart is restriction of sections along the
corresponding arrow: the counit of the right Kan extension cancels the unit. -/
theorem comparisonSectionsIso_restrict (V : SpacesEtale B S hS Z)
    (k : StructuredArrow (op V) (comparisonFunctor B S hS Z).op) :
    (comparisonSectionsIso B S hS Z H V).hom ≫
        limit.π (chartSectionsDiagram B S hS Z H V) k = H.obj.map k.hom := by
  have hn : H.obj.map k.hom ≫
        (((comparisonFunctor B S hS Z).op.ranAdjunction (Type (u + 1))).unit.app
          H.obj).app ((comparisonFunctor B S hS Z).op.obj k.right) =
      (((comparisonFunctor B S hS Z).op.ranAdjunction (Type (u + 1))).unit.app
          H.obj).app (op V) ≫
        ((comparisonFunctor B S hS Z).op.ran.obj
          ((comparisonFunctor B S hS Z).op ⋙ H.obj)).map k.hom :=
    (((comparisonFunctor B S hS Z).op.ranAdjunction (Type (u + 1))).unit.app
      H.obj).naturality k.hom
  rw [comparisonSectionsIso_hom_π, ← Category.assoc, ← hn, Category.assoc]
  exact (congrArg (fun t ↦ H.obj.map k.hom ≫ t)
    ((comparisonFunctor B S hS Z).op.ranCounit_app_app_ranAdjunction_unit_app_app
      H.obj k.right)).trans (Category.comp_id _)

/-- Two sections of a spaces-étale sheaf over an object étale over `Z` agree as soon as all
their restrictions to étale scheme charts agree: the sections are a limit over the charts. -/
theorem comparisonSections_ext (V : SpacesEtale B S hS Z)
    {s t : H.obj.obj (op V)}
    (h : ∀ (U : SmallEtale B S hS Z.1)
      (k : (comparisonFunctor B S hS Z).obj U ⟶ V),
      H.obj.map k.op s = H.obj.map k.op t) : s = t := by
  suffices he : (comparisonSectionsIso B S hS Z H V).hom s =
      (comparisonSectionsIso B S hS Z H V).hom t by
    simpa using congrArg (fun x ↦ (comparisonSectionsIso B S hS Z H V).inv x) he
  apply Types.limit_ext
  intro k
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    comparisonSectionsIso_restrict]
  simpa using h k.right.unop k.hom.unop

end Sections

/-! ### The map of sheaves attached to an `f`-map -/

/-- Restriction along the comparison functor, at the universe of the objects of the two étale
sites: the identification of the spaces-étale topos of an algebraic space with its small étale
topos. This is the forward functor of `AlgebraicGeometry.Space.smallEtaleToposEquiv`. -/
noncomputable abbrev comparisonRestriction (Z : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)) :=
  (comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type (u + 1))
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)

/-- The spaces-étale direct image along `f` followed by restriction to the étale scheme charts
of `Y`. -/
noncomputable abbrev spacesDirectImageRestriction :
    Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)) :=
  (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
    comparisonRestriction B S hS Y

section Descend

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
  (G : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type (u + 1))
  (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
  (i : F ≅ (comparisonRestriction B S hS X).obj H)
  (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G)

/-- The cone on the diagram of sections over the étale scheme charts above `X ×_Y V` whose
component at a chart is the `f`-map applied to the diagram of charts that chart determines.
Its limit is the sections of the direct image over `V`. -/
noncomputable def fMapDescendedSectionCone (V : SmallEtale B S hS Y.1) :
    Cone (chartSectionsDiagram B S hS X H (chartBaseChange B S hS f V)) where
  pt := G.obj (op V)
  π :=
    { app := fun k ↦ TypeCat.ofHom (fun s ↦ i.hom.hom.app k.right
        (ξ.app (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s))
      naturality := by
        intro k k' m
        apply TypeCat.homEquiv.injective
        funext s
        have hw : (comparisonFunctor B S hS X).map m.right.unop ≫ k.hom.unop =
            k'.hom.unop := congrArg Quiver.Hom.unop m.w
        have hc := (chartDiagram_square_iff B S hS f k.hom.unop k'.hom.unop
          m.right.unop (𝟙 V)).mp (by
            refine hw.trans ((Category.comp_id _).symm.trans
              (congrArg (fun a ↦ k'.hom.unop ≫ a) ?_))
            exact ((congrArg ((spacesBaseChange B S hS f).functor.map)
              ((comparisonFunctor B S hS Y).map_id V)).trans
                ((spacesBaseChange B S hS f).functor.map_id
                  ((comparisonFunctor B S hS Y).obj V))).symm)
        have hξ := ξ.naturality
          (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop)
          (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop)
          m.right.unop (𝟙 V) hc s
        have hGid : G.map (𝟙 V).op s = s :=
          ConcreteCategory.congr_hom (G.map_id (op V)) s
        have hξ' : ξ.app
              (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop) s =
            F.obj.map m.right (ξ.app
              (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s) :=
          (congrArg (ξ.app
            (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop))
              hGid).symm.trans hξ
        have hη := ConcreteCategory.congr_hom (i.hom.hom.naturality m.right)
          (ξ.app (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s)
        change i.hom.hom.app k'.right (ξ.app
            (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop) s) =
          H.obj.map ((comparisonFunctor B S hS X).op.map m.right)
            (i.hom.hom.app k.right (ξ.app
              (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s))
        exact (congrArg (fun t ↦ i.hom.hom.app k'.right t) hξ').trans hη }

/-- The section of the spaces-étale sheaf over `X ×_Y V` attached by an `f`-map to a section
over the étale scheme chart `V` of `Y`: the compatible family of the chartwise images, read
through the limit description of the sections over `X ×_Y V`. -/
noncomputable def fMapDescendedSection (V : SmallEtale B S hS Y.1) :
    G.obj (op V) → H.obj.obj (op (chartBaseChange B S hS f V)) := fun s ↦
  (comparisonSectionsIso B S hS X H (chartBaseChange B S hS f V)).inv
    (limit.lift (chartSectionsDiagram B S hS X H (chartBaseChange B S hS f V))
      (fMapDescendedSectionCone B S hS f F G H i ξ V) s)

/-- The descended section is, through the limit description of the sections over `X ×_Y V`,
the compatible family of the chartwise images. -/
theorem fMapDescendedSection_toLimit (V : SmallEtale B S hS Y.1) (s : G.obj (op V)) :
    (comparisonSectionsIso B S hS X H (chartBaseChange B S hS f V)).hom
        (fMapDescendedSection B S hS f F G H i ξ V s) =
      limit.lift (chartSectionsDiagram B S hS X H (chartBaseChange B S hS f V))
        (fMapDescendedSectionCone B S hS f F G H i ξ V) s := by
  simp [fMapDescendedSection]

/-- The restriction of the descended section to an étale scheme chart `U` of `X` above
`X ×_Y V` is the `f`-map applied to the diagram of charts that arrow determines. -/
theorem descendedSection_restrict (U : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (s : G.obj (op V)) :
    H.obj.map k.op (fMapDescendedSection B S hS f F G H i ξ V s) =
      i.hom.hom.app (op U)
        (ξ.app (chartDiagramOfBaseChangeArrow B S hS f U V k) s) := by
  calc H.obj.map k.op (fMapDescendedSection B S hS f F G H i ξ V s)
      = limit.π (chartSectionsDiagram B S hS X H (chartBaseChange B S hS f V))
          (StructuredArrow.mk k.op)
          ((comparisonSectionsIso B S hS X H (chartBaseChange B S hS f V)).hom
            (fMapDescendedSection B S hS f F G H i ξ V s)) :=
        (ConcreteCategory.congr_hom (comparisonSectionsIso_restrict B S hS X H
          (chartBaseChange B S hS f V) (StructuredArrow.mk k.op)) _).symm
    _ = limit.π (chartSectionsDiagram B S hS X H (chartBaseChange B S hS f V))
          (StructuredArrow.mk k.op)
          (limit.lift (chartSectionsDiagram B S hS X H (chartBaseChange B S hS f V))
            (fMapDescendedSectionCone B S hS f F G H i ξ V) s) := by
        rw [fMapDescendedSection_toLimit]
    _ = _ := ConcreteCategory.congr_hom
        (limit.lift_π (fMapDescendedSectionCone B S hS f F G H i ξ V)
          (StructuredArrow.mk k.op)) s

/-- The descended sections are compatible with étale restriction of the chart of `Y`: they
are the components of a map of sheaves. -/
theorem descendedSection_naturality {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V)
    (s : G.obj (op V)) :
    fMapDescendedSection B S hS f F G H i ξ V' (G.map j.op s) =
      H.obj.map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)).op
          (fMapDescendedSection B S hS f F G H i ξ V s) := by
  refine comparisonSections_ext B S hS X H _ (fun U k ↦ ?_)
  have hc := (chartDiagram_square_iff B S hS f
    (k ≫ (spacesBaseChange B S hS f).functor.map
      ((comparisonFunctor B S hS Y).map j)) k (𝟙 U) j).mp
      ((congrArg (fun a ↦ a ≫ k ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j))
          ((comparisonFunctor B S hS X).map_id U)).trans (Category.id_comp _))
  have hn := ξ.naturality
    (chartDiagramOfBaseChangeArrow B S hS f U V
      (k ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)))
    (chartDiagramOfBaseChangeArrow B S hS f U V' k) (𝟙 U) j hc s
  have hn' : ξ.app (chartDiagramOfBaseChangeArrow B S hS f U V' k)
        (G.map j.op s) =
      ξ.app (chartDiagramOfBaseChangeArrow B S hS f U V
        (k ≫ (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map j))) s :=
    hn.trans (ConcreteCategory.congr_hom (F.obj.map_id (op U)) _)
  have hr : H.obj.map k.op (H.obj.map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)).op
          (fMapDescendedSection B S hS f F G H i ξ V s)) =
      H.obj.map (k ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)).op
          (fMapDescendedSection B S hS f F G H i ξ V s) := by
    simp
  rw [hr, descendedSection_restrict, descendedSection_restrict]
  exact congrArg (fun x ↦ i.hom.hom.app (op U) x) hn'

/-- The map of presheaves into the direct image attached to an `f`-map out of a presheaf `G` on
the small étale site of `Y`: on sections over an étale scheme chart `V` of `Y` it is
`AlgebraicGeometry.Space.fMapDescendedSection`. -/
noncomputable def descendedHomPresheaf :
    G ⟶ ((spacesDirectImageRestriction B S hS f).obj H).obj where
  app V := TypeCat.ofHom (fMapDescendedSection B S hS f F G H i ξ V.unop)
  naturality := by
    intro V V' j
    ext s
    exact descendedSection_naturality B S hS f F G H i ξ j.unop s

end Descend

section DescendSheaf

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
  (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
  (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
  (i : F ≅ (comparisonRestriction B S hS X).obj H)
  (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj)

/-- The map of sheaves attached to an `f`-map: on sections over an étale scheme chart `V`
of `Y` it is `AlgebraicGeometry.Space.fMapDescendedSection`. -/
noncomputable def descendedHom : G ⟶ (spacesDirectImageRestriction B S hS f).obj H :=
  ⟨descendedHomPresheaf B S hS f F G.obj H i ξ⟩

end DescendSheaf

section Equiv

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
  (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
  (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
  (i : F ≅ (comparisonRestriction B S hS X).obj H)

/-- The `f`-map attached to a map of sheaves into the direct image: on a diagram of étale
scheme charts it is restriction of the section of the direct image along the arrow into the
cartesian base change that the diagram determines. -/
noncomputable def fMapOfPushforwardHom
    (ψ : G ⟶ (spacesDirectImageRestriction B S hS f).obj H) :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj where
  app d s := i.inv.hom.app (op d.U)
    (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
      (ψ.hom.app (op d.V) s))
  naturality d d' a b hab s := by
    have hs := (chartDiagram_square_iff B S hS f
      (baseChangeArrowOfChartDiagram B S hS f d)
      (baseChangeArrowOfChartDiagram B S hS f d') a b).mpr (by
        rw [chartDiagramOfBaseChangeArrow_baseChangeArrow_g,
          chartDiagramOfBaseChangeArrow_baseChangeArrow_g]
        exact hab)
    have key : H.obj.map (baseChangeArrowOfChartDiagram B S hS f d').op
          (H.obj.map ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map b)).op (ψ.hom.app (op d.V) s)) =
        H.obj.map ((comparisonFunctor B S hS X).map a).op
          (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
            (ψ.hom.app (op d.V) s)) := by
      refine (H.obj.map_comp_apply
        ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map b)).op
        (baseChangeArrowOfChartDiagram B S hS f d').op
        (ψ.hom.app (op d.V) s)).symm.trans (Eq.trans ?_
          (H.obj.map_comp_apply (baseChangeArrowOfChartDiagram B S hS f d).op
            ((comparisonFunctor B S hS X).map a).op (ψ.hom.app (op d.V) s)))
      exact congrArg
        (fun k : (comparisonFunctor B S hS X).obj d'.U ⟶ chartBaseChange B S hS f d.V ↦
          H.obj.map k.op (ψ.hom.app (op d.V) s)) hs.symm
    change i.inv.hom.app (op d'.U)
      (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d').op
        (ψ.hom.app (op d'.V) (G.obj.map b.op s))) =
      F.obj.map a.op (i.inv.hom.app (op d.U)
        (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
          (ψ.hom.app (op d.V) s)))
    rw [NatTrans.naturality_apply ψ.hom b.op s]
    refine Eq.trans (congrArg (fun y ↦ i.inv.hom.app (op d'.U) y) key) ?_
    exact NatTrans.naturality_apply i.inv.hom a.op _

/-- For a sheaf on the small étale site of `X` presented as the restriction of a spaces-étale
sheaf, the `f`-maps into it are the maps of sheaves into the direct image of that
spaces-étale sheaf. -/
noncomputable def descendedHomEquiv :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      (G ⟶ (spacesDirectImageRestriction B S hS f).obj H) where
  toFun := descendedHom B S hS f F G H i
  invFun := fMapOfPushforwardHom B S hS f F G H i
  left_inv ξ := by
    have happ : (fMapOfPushforwardHom B S hS f F G H i
        (descendedHom B S hS f F G H i ξ)).app = ξ.app := by
      funext d s
      change i.inv.hom.app (op d.U)
        (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
          (fMapDescendedSection B S hS f F G.obj H i ξ d.V s)) = _
      rw [descendedSection_restrict]
      have hx : ξ.app (chartDiagramOfBaseChangeArrow B S hS f d.U d.V
          (baseChangeArrowOfChartDiagram B S hS f d)) s = ξ.app d s := by
        obtain ⟨U, V, g, hc⟩ := d
        exact fMap_app_congr B S hS f ξ
          (chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f ⟨U, V, g, hc⟩) s
      rw [hx]
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (congrArg (fun k ↦ k.hom) i.hom_inv_id) (op d.U)) (ξ.app d s)
    have hext : ∀ (a b : FMap B S hS X.1 Y.1 f.hom F.obj G.obj), a.app = b.app → a = b := by
      intro a b
      cases a
      cases b
      intro hab
      cases hab
      rfl
    exact hext _ _ happ
  right_inv ψ := by
    apply Sheaf.hom_ext
    ext V s
    obtain ⟨V⟩ := V
    refine comparisonSections_ext B S hS X H _ (fun U k ↦ ?_)
    change H.obj.map k.op
      (fMapDescendedSection B S hS f F G.obj H i (fMapOfPushforwardHom B S hS f F G H i ψ)
        V s) = H.obj.map k.op (ψ.hom.app (op V) s)
    refine (descendedSection_restrict B S hS f F G.obj H i
      (fMapOfPushforwardHom B S hS f F G H i ψ) U V k s).trans ?_
    change i.hom.hom.app (op U)
      (i.inv.hom.app (op U)
        (H.obj.map (baseChangeArrowOfChartDiagram B S hS f
          (chartDiagramOfBaseChangeArrow B S hS f U V k)).op
            (ψ.hom.app (op V) s))) = _
    rw [baseChangeArrowOfChartDiagram_chartDiagram]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom) i.inv_hom_id) (op U)) _

/-- The map of sheaves attached to an `f`-map does not depend on the chosen presentation of
the source sheaf: a map of spaces-étale sheaves compatible with two presentations carries one
descended map to the other. -/
theorem descendedHom_map (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj)
    (H' : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (i' : F ≅ (comparisonRestriction B S hS X).obj H')
    (α : H ⟶ H') (hα : (comparisonRestriction B S hS X).map α = i.inv ≫ i'.hom) :
    descendedHom B S hS f F G H i ξ ≫ (spacesDirectImageRestriction B S hS f).map α =
      descendedHom B S hS f F G H' i' ξ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply TypeCat.homEquiv.injective
  funext s
  obtain ⟨V⟩ := V
  refine comparisonSections_ext B S hS X H' _ (fun U k ↦ ?_)
  show H'.obj.map k.op
    (α.hom.app _ (fMapDescendedSection B S hS f F G.obj H i ξ V s)) =
      H'.obj.map k.op (fMapDescendedSection B S hS f F G.obj H' i' ξ V s)
  have hn := ConcreteCategory.congr_hom (α.hom.naturality k.op)
    (fMapDescendedSection B S hS f F G.obj H i ξ V s)
  simp only [ConcreteCategory.comp_apply] at hn
  rw [← hn]
  refine (congrArg (fun t ↦ α.hom.app (op ((comparisonFunctor B S hS X).obj U)) t)
    (descendedSection_restrict B S hS f F G.obj H i ξ U V k s)).trans ?_
  refine Eq.trans ?_ (descendedSection_restrict B S hS f F G.obj H' i' ξ U V k s).symm
  have he : i.hom ≫ (comparisonRestriction B S hS X).map α = i'.hom := by
    rw [hα]
    simp
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun a ↦ a.hom) he) (op U)) _

end Equiv

/-! ### The bijections -/

section Main

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
  (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))

/-- A map on sections over every commutative pair of étale scheme charts over `f` is
equivalently a map of sheaves into the small étale direct image. -/
@[stacks 03G4 "parts (1) and (3)"]
noncomputable def fMapEquivPushforwardHom :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      (G ⟶ (smallToposMorphism B S hS f).pushforward.obj F) :=
  (descendedHomEquiv B S hS f F G ((comparisonRestriction B S hS X).objPreimage F)
      ((comparisonRestriction B S hS X).objObjPreimageIso F).symm).trans
    ((Iso.refl G).homCongr
      ((smallToposMorphism B S hS f).pushforward.mapIso
          ((comparisonRestriction B S hS X).objObjPreimageIso F).symm ≪≫
        (smallToposMorphism_comparison B S hS f).app
          ((comparisonRestriction B S hS X).objPreimage F)).symm)

/-- The map of sheaves that `AlgebraicGeometry.Space.fMapEquivPushforwardHom` attaches to an
`f`-map is, after the comparison `AlgebraicGeometry.Space.smallToposMorphism_comparison` at any
presentation `i` of the source sheaf, the descended map
`AlgebraicGeometry.Space.descendedHom`. -/
theorem fMapEquivPushforwardHom_comparison
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (i : F ≅ (comparisonRestriction B S hS X).obj H)
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj) :
    fMapEquivPushforwardHom B S hS f F G ξ ≫
        (smallToposMorphism B S hS f).pushforward.map i.hom ≫
        (smallToposMorphism_comparison B S hS f).hom.app H =
      descendedHom B S hS f F G H i ξ := by
  have hα : (comparisonRestriction B S hS X).map
        ((comparisonRestriction B S hS X).preimage
          (((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ i.hom)) =
      ((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ i.hom :=
    (comparisonRestriction B S hS X).map_preimage _
  have hnat : (smallToposMorphism B S hS f).pushforward.map
          ((comparisonRestriction B S hS X).map
            ((comparisonRestriction B S hS X).preimage
              (((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫
                i.hom))) ≫
        (smallToposMorphism_comparison B S hS f).hom.app H =
      (smallToposMorphism_comparison B S hS f).hom.app
          ((comparisonRestriction B S hS X).objPreimage F) ≫
        (spacesDirectImageRestriction B S hS f).map
          ((comparisonRestriction B S hS X).preimage
            (((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ i.hom)) :=
    (smallToposMorphism_comparison B S hS f).hom.naturality _
  show (𝟙 G ≫ descendedHom B S hS f F G
        ((comparisonRestriction B S hS X).objPreimage F)
        ((comparisonRestriction B S hS X).objObjPreimageIso F).symm ξ ≫
      ((smallToposMorphism_comparison B S hS f).inv.app
          ((comparisonRestriction B S hS X).objPreimage F) ≫
        (smallToposMorphism B S hS f).pushforward.map
          ((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv)) ≫
    (smallToposMorphism B S hS f).pushforward.map i.hom ≫
      (smallToposMorphism_comparison B S hS f).hom.app H = _
  simp only [Category.id_comp]
  calc _ = descendedHom B S hS f F G ((comparisonRestriction B S hS X).objPreimage F)
            ((comparisonRestriction B S hS X).objObjPreimageIso F).symm ξ ≫
          (smallToposMorphism_comparison B S hS f).inv.app
            ((comparisonRestriction B S hS X).objPreimage F) ≫
          (smallToposMorphism B S hS f).pushforward.map
            ((comparisonRestriction B S hS X).map
              ((comparisonRestriction B S hS X).preimage
                (((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫
                  i.hom))) ≫
          (smallToposMorphism_comparison B S hS f).hom.app H := by
        rw [hα, CategoryTheory.Functor.map_comp]
        simp only [Category.assoc]
    _ = descendedHom B S hS f F G ((comparisonRestriction B S hS X).objPreimage F)
            ((comparisonRestriction B S hS X).objObjPreimageIso F).symm ξ ≫
          (spacesDirectImageRestriction B S hS f).map
            ((comparisonRestriction B S hS X).preimage
              (((comparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫
                i.hom)) := by
        rw [hnat]
        simp
    _ = _ := descendedHom_map B S hS f F G
        ((comparisonRestriction B S hS X).objPreimage F)
        ((comparisonRestriction B S hS X).objObjPreimageIso F).symm ξ H i _ hα

/-- A map on sections over every commutative pair of étale scheme charts over `f` is
equivalently a map of sheaves out of the small étale inverse image. The bijection is the
composite of `AlgebraicGeometry.Space.fMapEquivPushforwardHom` with the adjunction bijection of
the morphism of small étale topoi. -/
@[stacks 03G4 "parts (2) and (3)"]
noncomputable def fMapEquivInverseImageHom :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      ((smallToposMorphism B S hS f).inverseImage.obj G ⟶ F) :=
  (fMapEquivPushforwardHom B S hS f F G).trans
    ((smallToposMorphism B S hS f).adj.homEquiv G F).symm

end Main

/-- The bijection `AlgebraicGeometry.Space.fMapEquivPushforwardHom` is the canonical one.
Transport a sheaf `F` on the small étale site of `X` through an isomorphism with the restriction
of a spaces-étale sheaf `H`; then on a diagram `d` of étale scheme charts over `f` the transported
`f`-map is restriction of the section of the direct image along any arrow from the chart of `X`
into the cartesian base change of the chart of `Y` whose composite with the cartesian projection
is the Yoneda morphism of the vertical morphism of `d`. -/
@[stacks 03G4 "canonical action on chart sections"]
theorem fMapEquivPushforwardHom_chart
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (i : F ≅ (comparisonRestriction B S hS X).obj H)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : ((SpacesEtale.toSpaces B S hS X).map h ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom = yoneda.map d.g)
    (s : G.obj.obj (op d.V)) :
    let ψ : G ⟶ (spacesDirectImageRestriction B S hS f).obj H :=
      fMapEquivPushforwardHom B S hS f F G ξ ≫
        (smallToposMorphism B S hS f).pushforward.map i.hom ≫
        (smallToposMorphism_comparison B S hS f).hom.app H
    (((sheafToPresheaf (SmallEtale.topology B S hS X.1)
      (Type (u + 1))).map i.hom).app (op d.U)) (ξ.app d s) =
      H.obj.map h.op
        (((sheafToPresheaf (SmallEtale.topology B S hS Y.1)
          (Type (u + 1))).map ψ).app (op d.V) s) := by
  dsimp only
  show i.hom.hom.app (op d.U) (ξ.app d s) = H.obj.map h.op
    ((fMapEquivPushforwardHom B S hS f F G ξ ≫
      (smallToposMorphism B S hS f).pushforward.map i.hom ≫
      (smallToposMorphism_comparison B S hS f).hom.app H).hom.app (op d.V) s)
  rw [fMapEquivPushforwardHom_comparison]
  show i.hom.hom.app (op d.U) (ξ.app d s) = H.obj.map h.op
    (fMapDescendedSection B S hS f F G.obj H i ξ d.V s)
  rw [descendedSection_restrict]
  congr 1
  obtain ⟨U, V, g, hc⟩ := d
  exact (fMap_app_congr B S hS f ξ
    (chartDiagramOfBaseChangeArrow_g_eq B S hS f ⟨U, V, g, hc⟩ h hh) s).symm

end AlgebraicGeometry.Space

end
