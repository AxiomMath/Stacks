module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondenceRingUniverse

/-!
# The chartwise formula for the structure map of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03G8 describes the structure map of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` on étale scheme charts: read as an `f`-map
through the chart correspondence
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse`, it sends a regular function on
an étale scheme chart `V` of `Y` to its pullback along the vertical morphism of schemes of any
commutative diagram of charts over `f` with lower chart `V`.  This file proves that.

The two inputs are the chart correspondence and the pointwise-limit description of the sections
of the direct image of the structure sheaf.  They are joined by presenting the sheaf of sets
underlying the structure sheaf of `X` as the restriction of its right Kan extension along the
comparison functor of Stacks 03G1 (`AlgebraicGeometry.Space.comparisonRanPresentation`).  At
that presentation the chart correspondence reads the structure map as the Kan-extension form
`AlgebraicGeometry.Space.structureSharpRanSet`, whose chart projections are the chartwise
pullbacks of regular functions by
`AlgebraicGeometry.Space.chartProjection_structureMapApp`.

## Main definitions

* `AlgebraicGeometry.Space.comparisonRanPresentation` presents a sheaf of sets on the small
  étale site as the restriction of its right Kan extension along the comparison functor of
  Stacks 03G1.
* `AlgebraicGeometry.Space.structureFMap` is the structure map of a morphism of algebraic
  spaces read as an `f`-map through the chart correspondence.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_chart`: **Stacks 03G8** — the structure map
  is pullback of regular functions along every commutative diagram of étale scheme charts.
* `AlgebraicGeometry.Space.pushforward_map_comparisonRanPresentation`: the geometric comparison
  of Stacks 03G2, part (3), transported along the Kan-extension presentation, is the
  Kan-extension comparison `AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` of the direct
  image.  This is what identifies the chart correspondence at that presentation with the
  Kan-extension form of the structure map.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {P Q : Sheaf J (Type w)}

/-- An equation between homomorphisms of sheaves of sets, read on sections.  This is the
sheaf-of-sets form of `SheafOfModules.hom_congr_app_apply`, and belongs beside
`CategoryTheory.Sheaf.hom_ext_sections`. -/
theorem hom_congr_app_apply {a b : P ⟶ Q} (h : a = b) (W : Cᵒᵖ) (x : P.obj.obj W) :
    a.hom.app W x = b.hom.app W x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m ↦ m.hom) h) W) x

/-- The inverse of an isomorphism of sheaves of sets undoes it on sections.  This is the
sheaf-of-sets form of `SheafOfModules.iso_inv_hom_app_apply`. -/
theorem iso_inv_hom_app_apply (e : P ≅ Q) (W : Cᵒᵖ) (x : P.obj.obj W) :
    e.inv.hom.app W (e.hom.hom.app W x) = x :=
  hom_congr_app_apply e.hom_inv_id W x

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every sheaf of sets on the small étale site of an algebraic space is the restriction of its
right Kan extension along the comparison functor of Stacks 03G1: the comparison restriction is
an equivalence, and the Kan extension is its quasi-inverse by
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso`. -/
noncomputable def comparisonRanPresentation (Z : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :
    P ≅ (smallEtaleComparisonRestriction B S hS Z).obj
      ((smallEtaleComparisonRan B S hS Z).obj P) :=
  ((smallEtaleComparisonRestriction B S hS Z).asEquivalence.counitIso.app P).symm ≪≫
    (smallEtaleComparisonRestriction B S hS Z).mapIso
      ((smallEtaleComparisonRanIso B S hS Z).app P)

/-- The inverse of the Kan-extension presentation is the counit of the Kan-extension
adjunction, so restriction along the presentation is the chart projection
`AlgebraicGeometry.Space.ranProj`. -/
theorem comparisonRanPresentation_inv (Z : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :
    (comparisonRanPresentation B S hS Z P).inv =
      (comparisonAdjunction B S hS Z).counit.app P :=
  restriction_map_ranIso_inv_comp_counitIso B S hS Z P

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The geometric comparison of Stacks 03G2, part (3), transported along the Kan-extension
presentation of the source sheaf, is the Kan-extension comparison of the direct image.  Both
sides are the direct image of the quasi-inverse comparison
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso`; the unit of the comparison equivalence
cancels against its counit. -/
theorem pushforward_map_comparisonRanPresentation
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
          (comparisonRanPresentation B S hS X F).hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
          ((smallEtaleComparisonRan B S hS X).obj F) =
      (smallEtaleDirectImageRanIso B S hS f).hom.app F := by
  have hnat : (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS X).map
          ((smallEtaleComparisonRanIso B S hS X).hom.app F)) ≫
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
        ((smallEtaleComparisonRan B S hS X).obj F) =
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F) ≫
        (smallEtaleComparisonRanIso B S hS X).hom.app F :=
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.naturality
      ((smallEtaleComparisonRanIso B S hS X).hom.app F)
  have htri : (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.inv.app F) ≫
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F) = 𝟙 _ := by
    simp
  have key : (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
        (comparisonRanPresentation B S hS X F).hom ≫
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
        ((smallEtaleComparisonRan B S hS X).obj F) =
      (smallEtaleComparisonRanIso B S hS X).hom.app F := by
    have e1 : (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
          (comparisonRanPresentation B S hS X F).hom =
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.inv.app F) ≫
          (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
            ((smallEtaleComparisonRestriction B S hS X).map
              ((smallEtaleComparisonRanIso B S hS X).hom.app F)) :=
      CategoryTheory.Functor.map_comp _ _ _
    refine Eq.trans (congrArg (fun m ↦ m ≫
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
        ((smallEtaleComparisonRan B S hS X).obj F)) e1) ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m ↦
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.inv.app F) ≫ m)
      hnat) ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun m ↦ m ≫ (smallEtaleComparisonRanIso B S hS X).hom.app F) htri)).trans
      (Category.id_comp _)
  change (spacesDirectImage B S hS f ⋙ smallEtaleComparisonRestriction B S hS Y).map
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
        (comparisonRanPresentation B S hS X F).hom) ≫
    ((spacesDirectImage B S hS f ⋙ smallEtaleComparisonRestriction B S hS Y).map
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
          ((smallEtaleComparisonRan B S hS X).obj F)) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  refine Eq.trans (CategoryTheory.Functor.map_comp
    (spacesDirectImage B S hS f ⋙ smallEtaleComparisonRestriction B S hS Y)
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
      (comparisonRanPresentation B S hS X F).hom)
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
      ((smallEtaleComparisonRan B S hS X).obj F))).symm ?_
  rw [key]
  rfl

/-- The structure map of a morphism of algebraic spaces read as an `f`-map through the chart
correspondence: the chartwise family of maps of sections that
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_chart` computes. -/
noncomputable def structureFMap :
    FMap B S hS X.1 Y.1 f.hom (structureSetSheaf B S hS X).obj
      (structureSetSheaf B S hS Y).obj :=
  (fMapEquivPushforwardHom_ringUniverse B S hS f (structureSetSheaf B S hS X)
      (structureSetSheaf B S hS Y)).symm
    ((smallEtaleRingedTopos B S hS Y).forgetRing.map
      (smallEtaleRingedToposHom B S hS f).fSharp)

/-- At the Kan-extension presentation of the source sheaf, the chart correspondence reads the
structure map of the morphism of small étale ringed topoi as the Kan-extension form
`AlgebraicGeometry.Space.structureSharpRanSet` of the structure map. -/
theorem descendedHomTypeU_structureFMap :
    descendedHomTypeU B S hS f (structureSetSheaf B S hS X) (structureSetSheaf B S hS Y)
        ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))
        (comparisonRanPresentation B S hS X (structureSetSheaf B S hS X))
        (structureFMap B S hS f) =
      structureSharpRanSet B S hS f := by
  have hcomp := fMapEquivPushforwardHom_ringUniverse_comparison B S hS f
    (structureSetSheaf B S hS X) (structureSetSheaf B S hS Y)
    ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))
    (comparisonRanPresentation B S hS X (structureSetSheaf B S hS X))
    (structureFMap B S hS f)
  have happ : (fMapEquivPushforwardHom_ringUniverse B S hS f (structureSetSheaf B S hS X)
      (structureSetSheaf B S hS Y)) (structureFMap B S hS f) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp :=
    (fMapEquivPushforwardHom_ringUniverse B S hS f (structureSetSheaf B S hS X)
      (structureSetSheaf B S hS Y)).apply_symm_apply _
  rw [happ, forgetRing_map_fSharp] at hcomp
  exact hcomp.symm.trans (Eq.trans (congrArg (fun m ↦ structureSharpSet B S hS f ≫ m)
    (pushforward_map_comparisonRanPresentation B S hS f (structureSetSheaf B S hS X)))
      (structureSharpSet_comp_ranIso B S hS f))

/-- Restriction of the Kan-extension form of the structure map to an étale scheme chart of `X`
above `X ×_Y V`, read through the counit of the Kan-extension adjunction, is pullback of
regular functions along the induced morphism of charts.  This is
`AlgebraicGeometry.Space.chartProjection_structureMapApp` with the chart projection unfolded to
the counit, which is how the chart correspondence sees it. -/
theorem counit_app_structureMapApp (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hkg : chartBaseChangeMap B S hS f V (StructuredArrow.mk (Y := op U) k.op) = g)
    (s : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    ((comparisonAdjunction B S hS X).counit.app (structureSetSheaf B S hS X)).hom.app (op U)
        (((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X)).obj.map k.op
          (structureMapApp B S hS f V s)) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map g)) s := by
  subst hkg
  exact chartProjection_structureMapApp B S hS f V (StructuredArrow.mk (Y := op U) k.op) s

/-- The structure map, read as an `f`-map through the chart correspondence, is pullback of
regular functions along the vertical morphism of schemes of the diagram of charts. -/
theorem structureFMap_app (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : (structureSetSheaf B S hS Y).obj.obj (op d.V)) :
    (structureFMap B S hS f).app d s =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s := by
  have hsec : fMapDescendedSectionTypeU B S hS f (structureSetSheaf B S hS X)
        (structureSetSheaf B S hS Y)
        ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))
        (comparisonRanPresentation B S hS X (structureSetSheaf B S hS X))
        (structureFMap B S hS f) d.V s =
      structureMapApp B S hS f d.V s :=
    congrArg (fun m ↦ m.hom.app (op d.V) s) (descendedHomTypeU_structureFMap B S hS f)
  have hres := descendedSectionTypeU_restrict B S hS f (structureSetSheaf B S hS X)
    (structureSetSheaf B S hS Y)
    ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))
    (comparisonRanPresentation B S hS X (structureSetSheaf B S hS X))
    (structureFMap B S hS f) d.U d.V (baseChangeArrowOfChartDiagram B S hS f d) s
  rw [hsec] at hres
  have hd : (structureFMap B S hS f).app
        (chartDiagramOfBaseChangeArrow B S hS f d.U d.V
          (baseChangeArrowOfChartDiagram B S hS f d)) s =
      (structureFMap B S hS f).app d s := by
    obtain ⟨U, V, g, hc⟩ := d
    exact FMap.app_congr B S hS f (structureFMap B S hS f)
      (chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f ⟨U, V, g, hc⟩) s
  rw [hd] at hres
  have hpull := counit_app_structureMapApp B S hS f d.U d.V
    (baseChangeArrowOfChartDiagram B S hS f d) d.g
    (chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f d) s
  refine ((Sheaf.iso_inv_hom_app_apply (comparisonRanPresentation B S hS X
      (structureSetSheaf B S hS X)) (op d.U)
      ((structureFMap B S hS f).app d s)).symm.trans (congrArg (fun y ↦
    (comparisonRanPresentation B S hS X (structureSetSheaf B S hS X)).inv.hom.app (op d.U) y)
      hres).symm).trans ?_
  exact Eq.trans (Sheaf.hom_congr_app_apply
    (comparisonRanPresentation_inv B S hS X (structureSetSheaf B S hS X)) (op d.U) _) hpull

/-- **Stacks 03G8, the chartwise formula for the structure homomorphism.** Read through the
chart correspondence as an `f`-map, the structure map of the morphism of small étale ringed
topoi sends a regular function on an étale scheme chart `V` of `Y` to its pullback along the
vertical morphism of schemes of any commutative diagram of étale scheme charts over `f` with
lower chart `V`. -/
theorem smallEtaleRingedToposHom_chart (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op d.V)) :
    let RX := smallEtaleRingedTopos B S hS X
    let RY := smallEtaleRingedTopos B S hS Y
    let ξ := (fMapEquivPushforwardHom_ringUniverse B S hS f
      (RX.forgetRing.obj RX.O) (RY.forgetRing.obj RY.O)).symm
        (RY.forgetRing.map (smallEtaleRingedToposHom B S hS f).fSharp)
    ξ.app d s =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s :=
  structureFMap_app B S hS f d s

end AlgebraicGeometry.Space

end
