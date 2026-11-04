module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt

/-!
# The structure maps over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `f : Z₁ ⟶ Z₂` a morphism of algebraic spaces
over `W` and `g : Y₁ ⟶ Y₂` one over `S`, matched by `εᵢ : Λ_h Zᵢ ≅ Yᵢ`. This file proves that the
structure map `g♯`, carried over to `Z₂` through the comparison of direct images of sheaves of
sets `AlgebraicGeometry.Space.smallerBaseSmallEtaleDirectImageIso`, is the structure map `f♯`
(Stacks 03G8), for an arbitrary `f`. With
`AlgebraicGeometry.Space.smallerBaseModulePushforwardIsoOfStructure` this gives the comparison
`g_* ⋙ (−)' ≅ (−)' ⋙ f_*` of the direct images of modules (Stacks 03D6, read through Stacks
04SG).

The identity is checked on the chart projections of the direct image along `f`
(`AlgebraicGeometry.Space.directImageChartProjection`), which are jointly injective. The
comparison of direct images carries the chart projection at an index `j` to the chart projection
of the direct image along `g` at an index `AlgebraicGeometry.Space.smallerBaseChartIndex` with
the same underlying morphism of schemes, and on the structure sheaves both chart projections are
pullbacks of regular functions along that morphism.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseChartIndex`: the chart of `Y₁` above `Y₁ ×_{Y₂} V`
  attached to a chart of `Z₁` above `Z₁ ×_{Z₂} V`.
* `AlgebraicGeometry.Space.smallerBaseModulePushforwardIso` and
  `AlgebraicGeometry.Space.smallerBasePushforwardModulesIso`: the direct images of modules commute
  with the change of base.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_app_eq_counit`: the chart projection
  through the counit of the comparison equivalence of Stacks 03G1.
* `AlgebraicGeometry.Space.directImageChartProjection_smallerBaseSmallEtaleDirectImageIso`: the
  comparison of direct images commutes with the chart projections.
* `AlgebraicGeometry.Space.chartBaseChangeMap_smallerBaseChartIndex`: the two indices have the
  same morphism of schemes.
* `AlgebraicGeometry.Space.smallerBaseStructureSharpLeft_eq_right`: the identity of the
  structure maps.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.ToposPullback

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

section Projection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The chart projection `AlgebraicGeometry.Space.directImageChartProjection` of the direct image
`AlgebraicGeometry.Space.smallEtaleDirectImage` is restriction along the indexing morphism
followed by the counit of the comparison equivalence of Stacks 03G1. -/
theorem directImageChartProjection_app_eq_counit (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    (directImageChartProjection B S hS f V j).app F a =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counit.app F).hom.app j.right
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.map
          j.hom a) := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction
    ((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) F
  have h' := congrArg (fun m => m.hom.app j.right
    (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.map j.hom a)) h
  refine Eq.trans ?_ h'
  show (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app F).hom.app
        j.right (((smallEtaleComparisonRan B S hS X).obj F).obj.map j.hom
          (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app _ a)) =
    (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app F).hom.app
        j.right (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app _
          (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.map
            j.hom a))
  rw [← NatTrans.naturality_apply ((smallEtaleComparisonRanIso B S hS X).hom.app F).hom j.hom a]

end Projection

section Conjugate

variable {A A' C C' : Type*} [Category* A] [Category* A'] [Category* C] [Category* C']

/-- For equivalences `E₁ : A ≌ A'` and `E₂ : C ≌ C'` and an isomorphism
`i : G ⋙ E₂.functor ≅ E₁.functor ⋙ K`, the conjugate isomorphism
`E₁.inverse ⋙ G ≅ K ⋙ E₂.inverse`, followed by the counit of `E₂`, is `i` followed by `K` of the
counit of `E₁`. -/
theorem inverseCompIso_isoCompInverse_hom_app_counit {E₁ : A ≌ A'} {E₂ : C ≌ C'} {G : A ⥤ C}
    {K : A' ⥤ C'} (i : G ⋙ E₂.functor ≅ E₁.functor ⋙ K) (X : A') :
    E₂.functor.map ((Iso.inverseCompIso (G := E₁) (H := K ⋙ E₂.inverse)
        (Iso.isoCompInverse (H := E₂) i)).hom.app X) ≫ E₂.counit.app (K.obj X) =
      i.hom.app (E₁.inverse.obj X) ≫ K.map (E₁.counit.app X) := by
  simp [Iso.inverseCompIso, Iso.isoCompInverse]

end Conjugate

section ChangeOfBase

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS)

/-- The comparison `AlgebraicGeometry.Space.smallerBaseComparisonRestrictionInverseIso` of the
inverse comparison equivalences of Stacks 03G1, followed by the counit over `Z`, is the change of
base of the counit over `Y`, through `AlgebraicGeometry.Space.smallerBaseComparisonRestrictionIso`:
the defining property of a conjugate. -/
theorem smallerBaseComparisonRestrictionInverseIso_hom_app_counit {Z : AlgebraicSpaces B W hW}
    {Y : AlgebraicSpaces B S hS} (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (smallEtaleComparisonRestriction B W hW Z).map
        ((smallerBaseComparisonRestrictionInverseIso B h ε).hom.app F) ≫
      (smallEtaleComparisonRestriction B W hW Z).asEquivalence.counit.app
        ((smallerBaseSheafRestriction B h ε).obj F) =
    (smallerBaseComparisonRestrictionIso B h ε).hom.app
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj F) ≫
      (smallerBaseSheafRestriction B h ε).map
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counit.app F) :=
  inverseCompIso_isoCompInverse_hom_app_counit
    (E₁ := (smallEtaleComparisonRestriction B S hS Y).asEquivalence)
    (E₂ := (smallEtaleComparisonRestriction B W hW Z).asEquivalence)
    (smallerBaseComparisonRestrictionIso B h ε) F

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)

/-- The index of a chart projection of the direct image along `g`, attached to one of the direct
image along `f`: an étale chart `T` of `Z₁` above `Z₁ ×_{Z₂} V` gives the étale chart `T` of `Y₁`
above `Y₁ ×_{Y₂} V`, through the comparison `AlgebraicGeometry.Space.smallerBaseComparisonIso`
of the comparison functors and the comparison
`AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeIso` of the base changes. -/
def smallerBaseChartIndex (V : SmallEtale B W hW Z₂.1)
    (j : StructuredArrow (op (chartBaseChange B W hW f V)) (comparisonFunctor B W hW Z₁).op) :
    StructuredArrow (op (chartBaseChange B S hS g
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)))
      (comparisonFunctor B S hS Y₁).op :=
  StructuredArrow.mk (Y := op ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.obj
      j.right.unop))
    ((smallerBaseComparisonIso B h ε₁).inv.app j.right.unop ≫
      (smallerBaseSpacesEtaleFunctor B h ε₁).map j.hom.unop ≫
      (smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app ((comparisonFunctor B W hW Z₂).obj V) ≫
      (spacesBaseChange B S hS g).functor.map ((smallerBaseComparisonIso B h ε₂).hom.app V)).op

/-- **The comparison of direct images commutes with the chart projections**: the chart
projection of the direct image along `f`, at the index `j`, of the comparison
`AlgebraicGeometry.Space.smallerBaseSmallEtaleDirectImageIso` of a section is the chart
projection of the direct image along `g`, at the index
`AlgebraicGeometry.Space.smallerBaseChartIndex`, of that section. -/
theorem directImageChartProjection_smallerBaseSmallEtaleDirectImageIso
    (F : Sheaf (SmallEtale.topology B S hS Y₁.1) (Type u)) (V : SmallEtale B W hW Z₂.1)
    (j : StructuredArrow (op (chartBaseChange B W hW f V)) (comparisonFunctor B W hW Z₁).op)
    (y : (smallEtaleDirectImage B S hS g ⋙ Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y₂.1)
      (op ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V))).obj F) :
    (directImageChartProjection B W hW f V j).app ((smallerBaseSheafRestriction B h ε₁).obj F)
        (((smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom.app F).hom.app (op V) y) =
      (directImageChartProjection B S hS g
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)
        (smallerBaseChartIndex B h ε₁ ε₂ hfg V j)).app F y := by
  refine Eq.trans (directImageChartProjection_app_eq_counit B W hW f V j _ _)
    (Eq.trans ?_ (directImageChartProjection_app_eq_counit B S hS g _
      (smallerBaseChartIndex B h ε₁ ε₂ hfg V j) F y).symm)
  have hτ : ((smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom.app F).hom.app (op V) y =
      ((smallerBaseComparisonRestrictionInverseIso B h ε₁).hom.app F).hom.app
        (op (chartBaseChange B W hW f V))
        (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
          ((smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app
            ((comparisonFunctor B W hW Z₂).obj V)).op
          (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
            ((spacesBaseChange B S hS g).functor.map
              ((smallerBaseComparisonIso B h ε₂).hom.app V)).op y)) := rfl
  rw [hτ]
  have hn := NatTrans.naturality_apply
    ((smallerBaseComparisonRestrictionInverseIso B h ε₁).hom.app F).hom j.hom
    (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
      ((smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app
        ((comparisonFunctor B W hW Z₂).obj V)).op
      (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
        ((spacesBaseChange B S hS g).functor.map
          ((smallerBaseComparisonIso B h ε₂).hom.app V)).op y))
  refine (congrArg (fun x => ((smallEtaleComparisonRestriction B W hW Z₁).asEquivalence.counit.app
      ((smallerBaseSheafRestriction B h ε₁).obj F)).hom.app j.right x) hn.symm).trans ?_
  refine (congrArg (fun m => m.hom.app j.right
    ((((smallerBaseSpacesEtaleFunctor B h ε₁).sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B W hW Z₁) (SpacesEtale.topology B S hS Y₁)).obj
      ((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F)).obj.map j.hom
        (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
          ((smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app
            ((comparisonFunctor B W hW Z₂).obj V)).op
          (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
            ((spacesBaseChange B S hS g).functor.map
              ((smallerBaseComparisonIso B h ε₂).hom.app V)).op y))))
    (smallerBaseComparisonRestrictionInverseIso_hom_app_counit B h ε₁ F)).trans ?_
  show ((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.counit.app F).hom.app _
      (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
        ((smallerBaseComparisonIso B h ε₁).inv.app j.right.unop).op
        (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
          ((smallerBaseSpacesEtaleFunctor B h ε₁).map j.hom.unop).op
          (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
            ((smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app
              ((comparisonFunctor B W hW Z₂).obj V)).op
            (((smallEtaleComparisonRestriction B S hS Y₁).asEquivalence.inverse.obj F).obj.map
              ((spacesBaseChange B S hS g).functor.map
                ((smallerBaseComparisonIso B h ε₂).hom.app V)).op y)))) = _
  simp only [smallerBaseChartIndex, StructuredArrow.mk_hom_eq_self, op_comp, Functor.map_comp]
  rfl

/-- **The chartwise morphism of the index `AlgebraicGeometry.Space.smallerBaseChartIndex` is the
chartwise morphism of `j`**, viewed over `S`: the lower-shriek extension does not change the
underlying schemes of the charts, and carries the cartesian projection along `f` to the one along
`g` (`AlgebraicGeometry.Space.smallerBaseSpacesBaseChangeObjIso_hom_projection`). -/
theorem chartBaseChangeMap_smallerBaseChartIndex (V : SmallEtale B W hW Z₂.1)
    (j : StructuredArrow (op (chartBaseChange B W hW f V)) (comparisonFunctor B W hW Z₁).op) :
    chartBaseChangeMap B S hS g ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)
        (smallerBaseChartIndex B h ε₁ ε₂ hfg V j) =
      (Over.map h).map (chartBaseChangeMap B W hW f V j) := by
  apply yoneda.map_injective
  refine (yoneda_map_chartBaseChangeMap B S hS g _ _).trans ?_
  have hy : yoneda.map ((Over.map h).map (chartBaseChangeMap B W hW f V j)) =
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h
          ((SmallEtale.toOver B W hW Z₁.1).obj j.right.unop)).inv ≫
        (OverShriek.relocalizePresheafFunctor h).map
          (yoneda.map (chartBaseChangeMap B W hW f V j)) ≫
        (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h
          ((SmallEtale.toOver B W hW Z₂.1).obj V)).hom := by
    rw [relocalizedYonedaIso_naturality, Iso.inv_hom_id_assoc]
  refine Eq.trans ?_ hy.symm
  refine Eq.trans ?_ (congrArg (fun m => (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h
          ((SmallEtale.toOver B W hW Z₁.1).obj j.right.unop)).inv ≫
        (OverShriek.relocalizePresheafFunctor h).map m ≫
        (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h
          ((SmallEtale.toOver B W hW Z₂.1).obj V)).hom)
    (yoneda_map_chartBaseChangeMap B W hW f V j).symm)
  have hproj : (SpacesEtale.toSpaces B S hS Y₁).map
        ((smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app
            ((comparisonFunctor B W hW Z₂).obj V) ≫
          (spacesBaseChange B S hS g).functor.map ((smallerBaseComparisonIso B h ε₂).hom.app V)) ≫
        (spacesBaseChange B S hS g).projection.app
          ((comparisonFunctor B S hS Y₂).obj
            ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)) =
      relocalizeSpaceMap h ((spacesBaseChange B W hW f).projection.app
          ((comparisonFunctor B W hW Z₂).obj V)) ≫
        (SpacesEtale.toSpaces B S hS Y₂).map ((smallerBaseComparisonIso B h ε₂).hom.app V) := by
    rw [Functor.map_comp, Category.assoc]
    have n : (SpacesEtale.toSpaces B S hS Y₁).map
          ((spacesBaseChange B S hS g).functor.map ((smallerBaseComparisonIso B h ε₂).hom.app V)) ≫
        (spacesBaseChange B S hS g).projection.app
          ((comparisonFunctor B S hS Y₂).obj
            ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)) =
        (spacesBaseChange B S hS g).projection.app
          ((smallerBaseSpacesEtaleFunctor B h ε₂).obj ((comparisonFunctor B W hW Z₂).obj V)) ≫
        (SpacesEtale.toSpaces B S hS Y₂).map ((smallerBaseComparisonIso B h ε₂).hom.app V) :=
      (spacesBaseChange B S hS g).projection.naturality
        ((smallerBaseComparisonIso B h ε₂).hom.app V)
    rw [n, ← Category.assoc]
    exact smallerBaseSpacesBaseChangeObjIso_hom_projection B h ε₁ ε₂ hfg _ =≫ _
  have hall : (SpacesEtale.toSpaces B S hS Y₁).map
        (smallerBaseChartIndex B h ε₁ ε₂ hfg V j).hom.unop ≫
        (spacesBaseChange B S hS g).projection.app
          ((comparisonFunctor B S hS Y₂).obj
            ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)) =
      (SpacesEtale.toSpaces B S hS Y₁).map
          ((smallerBaseComparisonIso B h ε₁).inv.app j.right.unop) ≫
        relocalizeSpaceMap h ((SpacesEtale.toSpaces B W hW Z₁).map j.hom.unop ≫
          (spacesBaseChange B W hW f).projection.app ((comparisonFunctor B W hW Z₂).obj V)) ≫
        (SpacesEtale.toSpaces B S hS Y₂).map ((smallerBaseComparisonIso B h ε₂).hom.app V) := by
    show (SpacesEtale.toSpaces B S hS Y₁).map
        ((smallerBaseComparisonIso B h ε₁).inv.app j.right.unop ≫
          (smallerBaseSpacesEtaleFunctor B h ε₁).map j.hom.unop ≫
          ((smallerBaseSpacesBaseChangeIso B h ε₁ ε₂ hfg).hom.app
            ((comparisonFunctor B W hW Z₂).obj V) ≫
          (spacesBaseChange B S hS g).functor.map ((smallerBaseComparisonIso B h ε₂).hom.app V))) ≫
        _ = _
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hproj,
      relocalizeSpaceMap_comp]
    exact congrArg (_ ≫ ·) (Category.assoc _ _ _).symm
  exact congrArg (fun m => m.hom) hall

/-- **The structure maps agree across the change of base**: `g♯` carried over to `Z₂` along the
comparison `AlgebraicGeometry.Space.smallerBaseSmallEtaleDirectImageIso` is `f♯`. Both are checked
on the chart projections of the direct image along `f`: there they are the pullbacks of a regular
function along the chartwise morphisms of `g` and of `f`, which are the same morphism of schemes
(`AlgebraicGeometry.Space.chartBaseChangeMap_smallerBaseChartIndex`). -/
theorem smallerBaseStructureSharpLeft_eq_right :
    smallerBaseStructureSharpLeft B h ε₁ ε₂ hfg = smallerBaseStructureSharpRight B h ε₁ ε₂ := by
  refine directImageChartProjection_ringSheafHom_ext B W hW f _ _ fun V j x => ?_
  have hL : (smallerBaseStructureSharpLeft B h ε₁ ε₂ hfg).hom.app (op V) x =
      ((smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg).hom.app
        (structureSetSheaf B S hS Y₁)).hom.app (op V)
        ((structureSharpSet B S hS g).hom.app
          (op ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)) x) := rfl
  have hR : (smallerBaseStructureSharpRight B h ε₁ ε₂).hom.app (op V) x =
      (pullbackRingSheafMap (SmallEtale.topology B W hW Z₂.1) (smallEtaleDirectImage B W hW f)
        (restrictionRingIso (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
          (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor
          (structureRingSheaf B S hS Y₁)).inv).hom.app (op V)
        ((structureSharpSet B W hW f).hom.app (op V) x) := rfl
  rw [hL, hR]
  refine (directImageChartProjection_smallerBaseSmallEtaleDirectImageIso B h ε₁ ε₂ hfg
    (structureSetSheaf B S hS Y₁) V j _).trans ?_
  refine (directImageChartProjection_structureSharpSet B S hS g _ _ x).trans ?_
  refine Eq.trans ?_ (directImageChartProjection_ringSheafMap B W hW f V j
    (restrictionRingIso (SmallEtale.topology B W hW Z₁.1) (SmallEtale.topology B S hS Y₁.1)
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor (structureRingSheaf B S hS Y₁)).inv
    ((structureSharpSet B W hW f).hom.app (op V) x)).symm
  show _ = (directImageChartProjection B W hW f V j).app (structureSetSheaf B W hW Z₁)
    ((structureSharpSet B W hW f).hom.app (op V) x)
  refine Eq.trans ?_ (directImageChartProjection_structureSharpSet B W hW f V j x).symm
  show (CategoryTheory.forget CommRingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap B S hS g ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V)
          (smallerBaseChartIndex B h ε₁ ε₂ hfg V j))).op) x =
    (CategoryTheory.forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B W hW).map
      (chartBaseChangeMap B W hW f V j)).op) x
  rw [chartBaseChangeMap_smallerBaseChartIndex]
  rfl

/-- **The direct images of modules commute with the change of base**, for an arbitrary morphism:
`g_* ⋙ (−)' ≅ (−)' ⋙ f_*` for the direct images of modules
`AlgebraicGeometry.Space.modulePushforward`. This is
`AlgebraicGeometry.Space.smallerBaseModulePushforwardIsoOfStructure` with the identity of the
structure maps `AlgebraicGeometry.Space.smallerBaseStructureSharpLeft_eq_right`. -/
def smallerBaseModulePushforwardIso :
    modulePushforward B S hS g ⋙ (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙ modulePushforward B W hW f :=
  smallerBaseModulePushforwardIsoOfStructure B h ε₁ ε₂ hfg
    (smallerBaseStructureSharpLeft_eq_right B h ε₁ ε₂ hfg)

/-- `AlgebraicGeometry.Space.smallerBaseModulePushforwardIso` for the direct images of modules of
the morphisms of small étale ringed topoi, which the derived direct images derive. -/
def smallerBasePushforwardModulesIso :
    (smallEtaleRingedToposHom B S hS g).pushforwardModules ⋙
        (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙
        (smallEtaleRingedToposHom B W hW f).pushforwardModules :=
  smallerBasePushforwardModulesIsoOfStructure B h ε₁ ε₂ hfg
    (smallerBaseStructureSharpLeft_eq_right B h ε₁ ε₂ hfg)

end ChangeOfBase

end AlgebraicGeometry.Space

end
