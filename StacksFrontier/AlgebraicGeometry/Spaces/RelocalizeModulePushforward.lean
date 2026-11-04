module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDirectImage

/-!
# Direct images of modules on algebraic spaces under relocalization

Let `g : T ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `T`, with lower-shriek extension `Λ f : Λ X ⟶ Λ Y` over `S`. Through the equivalences of
module categories `E_X`, `E_Y` of `AlgebraicGeometry.Space.relocalizeModulesEquivalence`, the
direct image of modules along `Λ f` is the direct image along `f`.

The direct images of sheaves of sets correspond by
`AlgebraicGeometry.Space.relocalizeDirectImageRanIso`; what remains is that the structure maps
`f♯` and `(Λ f)♯` of Stacks 03G8 correspond. Both are computed chart by chart: a regular function
on a chart `V` of `Y` goes to its pullbacks along the morphisms of schemes from the charts of `X`
above `X ×_Y V`, and the relocalized charts of `Λ X` above `Λ X ×_{Λ Y} V` have the same
underlying morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.chartBaseChangeMap_relocalizeChartIndex`: the chart morphisms of
  `Λ f` are those of `f`.
* `AlgebraicGeometry.Space.relocalizeDirectImageRanIso_structureSharpRan`: the structure maps
  correspond.
* `AlgebraicGeometry.Space.relocalizeModulePushforwardIso`:
  `(Λ f)_* ⋙ E_Y⁻¹ ≅ E_X⁻¹ ⋙ f_*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X Y : AlgebraicSpaces B T hT} (f : X ⟶ Y)

/-! ### Chart projections of the relocalized direct image -/

/-- An étale chart of `X` above `X ×_Y V` gives an étale chart of `Λ X` above
`Λ X ×_{Λ Y} V`, where `V` is read as a chart of `Λ Y`. -/
abbrev relocalizeChartIndex (V : SmallEtale B T hT Y.1)
    (j : StructuredArrow (op (chartBaseChange B T hT f V)) (comparisonFunctor B T hT X).op) :
    StructuredArrow (op (chartBaseChange B S hS (relocalizeHom B hT hS g f)
        ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V)))
      (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op :=
  (StructuredArrow.map ((NatIso.op (relocalizeChartBaseChangeIso B hT hS g f)).symm.hom.app
      (op V))).obj ((relocalizeRanIndex B hT hS g X (chartBaseChange B T hT f V)).obj j)

/-- The chart projections of the relocalized direct image: projecting the comparison
`AlgebraicGeometry.Space.relocalizeDirectImageRanIso` to a chart of `X` above `X ×_Y V` is
projecting to the corresponding chart of `Λ X`. -/
theorem relocalizeDirectImageRanIso_hom_π
    (G : Sheaf (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1) (Type u))
    (V : SmallEtale B T hT Y.1)
    (j : StructuredArrow (op (chartBaseChange B T hT f V)) (comparisonFunctor B T hT X).op)
    (a : ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G.obj).obj
      (op (chartBaseChange B S hS (relocalizeHom B hT hS g f)
        ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V)))) :
    (ranChartCone B T hT X ((SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙ G.obj)
        (chartBaseChange B T hT f V)).π.app j
        (((relocalizeDirectImageRanIso B hT hS g f).hom.app G).hom.app (op V) a) =
      (ranChartCone B S hS (relocalizeSpace B hT hS g X) G.obj
        (chartBaseChange B S hS (relocalizeHom B hT hS g f)
          ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V))).π.app
        (relocalizeChartIndex B hT hS g f V j) a := by
  have hfac := NatTrans.congr_app (relocalizeRanIso_hom_fac B hT hS g X G.obj) j.right
  have hnat := NatTrans.naturality (relocalizeRanIso B hT hS g X G.obj).hom j.hom
  have h₁ : ((relocalizeDirectImageRanIso B hT hS g f).hom.app G).hom.app (op V) a =
      (relocalizeRanIso B hT hS g X G.obj).hom.app (op (chartBaseChange B T hT f V))
        (((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G.obj).map
          ((NatIso.op (relocalizeChartBaseChangeIso B hT hS g f)).symm.hom.app (op V)) a) := rfl
  rw [h₁, ranChartCone_π_apply]
  refine (congrArg (((comparisonFunctor B T hT X).op.ranCounit.app
    ((SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙ G.obj)).app j.right)
      (typeHom_congr_apply hnat _).symm).trans ?_
  refine (typeHom_congr_apply hfac _).trans ?_
  simp only [relocalizeRanCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    types_comp_apply, types_id_apply, Functor.comp_map]
  rw [ranChartCone_π_apply]
  refine congrArg (((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ranCounit.app
    G.obj).app _) ?_
  have hm : (relocalizeChartIndex B hT hS g f V j).hom =
      (NatIso.op (relocalizeChartBaseChangeIso B hT hS g f)).symm.hom.app (op V) ≫
        (relocalizeSpacesEtale B hT hS g X).op.map j.hom ≫
          (relocalizeComparisonOpIso B hT hS g X).hom.app j.right := rfl
  rw [hm]
  exact ((FunctorToTypes.map_comp_apply _ _ _ a).trans
    (FunctorToTypes.map_comp_apply _ _ _ _)).symm

/-! ### The chart morphisms under relocalization -/

variable (X) in
/-- The comparison `e_X ⋙ cmp_{Λ X} ≅ cmp_X ⋙ Λ` is, on underlying presheaves, the comparison
`h_{j U} ≅ Λ h_U` of representable presheaves. -/
theorem toSpaces_relocalizeComparisonIso_hom_app (U : SmallEtale B T hT X.1) :
    ((SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map
        ((relocalizeComparisonIso B hT hS g X).hom.app U)).hom =
      (OverShriek.relocalizeYonedaIso g).inv.app U.obj.left :=
  rfl

variable (X) in
/-- The inverse comparison is, on underlying presheaves, `Λ h_U ≅ h_{j U}`. -/
theorem toSpaces_relocalizeComparisonIso_inv_app (U : SmallEtale B T hT X.1) :
    ((SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map
        ((relocalizeComparisonIso B hT hS g X).inv.app U)).hom =
      (OverShriek.relocalizeYonedaIso g).hom.app U.obj.left :=
  rfl

/-- The Beck–Chevalley comparison of base changes commutes with the cartesian projections:
`Λ (X ×_Y W) ≅ Λ X ×_{Λ Y} Λ W` followed by the projection to `Λ W` is `Λ` of the projection. -/
theorem relocalizeSpacesEtaleBaseChangeIso_hom_projection (W : SpacesEtale B T hT Y) :
    (SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map
        ((relocalizeSpacesEtaleBaseChangeIso B hT hS g f).hom.app W) ≫
      (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).projection.app
        ((relocalizeSpacesEtale B hT hS g Y).obj W) =
      (relocalizeSpacesFunctor B hT hS g).map
        ((spacesBaseChange B T hT f).projection.app W) :=
  PreservesPullback.iso_hom_fst (relocalizeSpacesFunctor B hT hS g) W.1.hom f

/-- The inverse of `AlgebraicGeometry.Space.relocalizeChartBaseChangeIso` followed by the
cartesian projection to the chart of `Λ Y` is `Λ` of the cartesian projection, read through the
comparison of representable presheaves. -/
theorem relocalizeChartBaseChangeIso_inv_projection (V : SmallEtale B T hT Y.1) :
    ((SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map
        ((relocalizeChartBaseChangeIso B hT hS g f).inv.app V)).hom ≫
      ((spacesBaseChange B S hS (relocalizeHom B hT hS g f)).projection.app
        ((comparisonFunctor B S hS (relocalizeSpace B hT hS g Y)).obj
          ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V))).hom =
      (OverShriek.relocalizePresheafFunctor g).map
          ((spacesBaseChange B T hT f).projection.app
            ((comparisonFunctor B T hT Y).obj V)).hom ≫
        ((SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g Y)).map
          ((relocalizeComparisonIso B hT hS g Y).inv.app V)).hom := by
  have hnat := (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).projection.naturality
    ((relocalizeComparisonIso B hT hS g Y).inv.app V)
  have hinv : (relocalizeChartBaseChangeIso B hT hS g f).inv.app V =
      (relocalizeSpacesEtaleBaseChangeIso B hT hS g f).hom.app
          ((comparisonFunctor B T hT Y).obj V) ≫
        (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).functor.map
          ((relocalizeComparisonIso B hT hS g Y).inv.app V) := by
    simp [relocalizeChartBaseChangeIso]
  have h₂ : ((spacesBaseChange B S hS (relocalizeHom B hT hS g f)).functor ⋙
        SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map
          ((relocalizeComparisonIso B hT hS g Y).inv.app V) ≫
        (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).projection.app
          ((comparisonFunctor B S hS (relocalizeSpace B hT hS g Y)).obj
            ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V)) =
      (spacesBaseChange B S hS (relocalizeHom B hT hS g f)).projection.app
          ((relocalizeSpacesEtale B hT hS g Y).obj ((comparisonFunctor B T hT Y).obj V)) ≫
        (SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g Y)).map
          ((relocalizeComparisonIso B hT hS g Y).inv.app V) := hnat
  rw [hinv, Functor.map_comp]
  show ((SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map _ ≫
    ((spacesBaseChange B S hS (relocalizeHom B hT hS g f)).functor ⋙
      SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map _ ≫ _).hom = _
  rw [h₂, ← Category.assoc, relocalizeSpacesEtaleBaseChangeIso_hom_projection]
  rfl

/-- **The chart morphisms of `Λ f` are those of `f`**: the morphism from a relocalized chart of
`X` to the chart `V` of `Λ Y` induced through `Λ X ×_{Λ Y} V` is `Λ` of the morphism induced
through `X ×_Y V`. -/
theorem chartBaseChangeMap_relocalizeChartIndex (V : SmallEtale B T hT Y.1)
    (j : StructuredArrow (op (chartBaseChange B T hT f V)) (comparisonFunctor B T hT X).op) :
    chartBaseChangeMap B S hS (relocalizeHom B hT hS g f)
        ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V)
        (relocalizeChartIndex B hT hS g f V j) =
      (Over.map g).map (chartBaseChangeMap B T hT f V j) := by
  apply yoneda.map_injective
  have hY := (Iso.eq_inv_comp ((OverShriek.relocalizeYonedaIso g).app _)).2
    ((OverShriek.relocalizeYonedaIso g).hom.naturality (chartBaseChangeMap B T hT f V j)).symm
  rw [Functor.comp_map, Functor.comp_map, yoneda_map_chartBaseChangeMap] at hY
  refine (yoneda_map_chartBaseChangeMap _ _ _ _ _ _).trans (Eq.trans ?_ hY.symm)
  have h₁ := relocalizeChartBaseChangeIso_inv_projection B hT hS g f V
  show (OverShriek.relocalizeYonedaIso g).inv.app j.right.unop.obj.left ≫
      (OverShriek.relocalizePresheafFunctor g).map
        ((SpacesEtale.toSpaces B T hT X).map j.hom.unop).hom ≫
      ((SpacesEtale.toSpaces B S hS (relocalizeSpace B hT hS g X)).map
        ((relocalizeChartBaseChangeIso B hT hS g f).inv.app V)).hom ≫
      ((spacesBaseChange B S hS (relocalizeHom B hT hS g f)).projection.app
        ((comparisonFunctor B S hS (relocalizeSpace B hT hS g Y)).obj
          ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V))).hom = _
  refine congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) h₁).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Functor.map_comp
    (OverShriek.relocalizePresheafFunctor g) ((SpacesEtale.toSpaces B T hT X).map j.hom.unop).hom
    ((spacesBaseChange B T hT f).projection.app ((comparisonFunctor B T hT Y).obj V)).hom).symm)

/-- Pullback of regular functions from a chart of `Λ Y` to a relocalized chart of `Λ X` is the
pullback for `f`: the chart morphisms are the same morphisms of schemes. -/
theorem chartPullback_relocalizeChartIndex (V : SmallEtale B T hT Y.1)
    (j : StructuredArrow (op (chartBaseChange B T hT f V)) (comparisonFunctor B T hT X).op)
    (x : ToType ((structureRingSheaf B T hT Y).obj.obj (op V))) :
    chartPullback B S hS (relocalizeHom B hT hS g f)
        ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj V)
        (relocalizeChartIndex B hT hS g f V j) x =
      chartPullback B T hT f V j x := by
  unfold chartPullback
  rw [chartBaseChangeMap_relocalizeChartIndex]
  rfl

/-- **The structure maps of `f` and `Λ f` agree under relocalization**: restricted along `e_Y`
and read through the comparison of direct images, the structure map `(Λ f)♯` is `f♯`, both in
their right Kan extension form and on underlying sheaves of sets. -/
theorem relocalizeDirectImageRanIso_structureSharpRan :
    (relocalizeSheafRestriction B hT hS g Y).map
        ((sheafCompose (SmallEtale.topology B S hS (relocalizeSpace B hT hS g Y).1)
          (forget RingCat.{u})).map (structureSharpRan B S hS (relocalizeHom B hT hS g f))) ≫
      (relocalizeDirectImageRanIso B hT hS g f).hom.app
        (structureSetSheaf B S hS (relocalizeSpace B hT hS g X)) =
    (sheafCompose (SmallEtale.topology B T hT Y.1) (forget RingCat.{u})).map
      (structureSharpRan B T hT f) := by
  apply Sheaf.hom_ext
  ext V x
  refine chartProjection_ext B T hT f V.unop (fun j => ?_)
  refine Eq.trans ?_ (chartProjection_structureMapApp B T hT f V.unop j x).symm
  refine (chartProjection_app_apply B T hT f V.unop j _).trans ?_
  refine (relocalizeDirectImageRanIso_hom_π B hT hS g f
    (structureSetSheaf B S hS (relocalizeSpace B hT hS g X)) V.unop j _).trans ?_
  refine (chartProjection_app_apply B S hS (relocalizeHom B hT hS g f) _
    (relocalizeChartIndex B hT hS g f V.unop j) _).symm.trans ?_
  exact (chartProjection_structureMapApp B S hS (relocalizeHom B hT hS g f) _
    (relocalizeChartIndex B hT hS g f V.unop j) x).trans
    (chartPullback_relocalizeChartIndex B hT hS g f V.unop j x)

/-! ### The direct image of modules -/

/-- The direct image of small étale sheaves of sets along `Λ f` preserves finite products. -/
instance preservesFiniteProducts_smallEtaleDirectImage_relocalizeHom :
    PreservesFiniteProducts (smallEtaleDirectImage B S hS (relocalizeHom B hT hS g f)) :=
  smallEtaleDirectImage_preservesFiniteProducts B S hS _

/-- The right Kan extension form of the direct image of small étale sheaves of sets along `Λ f`
preserves finite products. -/
instance preservesFiniteProducts_smallEtaleDirectImageRan_relocalizeHom :
    PreservesFiniteProducts (smallEtaleDirectImageRan B S hS (relocalizeHom B hT hS g f)) :=
  smallEtaleDirectImageRan_preservesFiniteProducts B S hS _

/-- **Direct images of sheaves of sets commute with relocalization**, for the direct image
`AlgebraicGeometry.Space.smallEtaleDirectImage` itself: `e_Y^* ∘ (Λ f)_* ≅ f_* ∘ e_X^*`. -/
def relocalizeDirectImageIso :
    smallEtaleDirectImage B S hS (relocalizeHom B hT hS g f) ⋙
        relocalizeSheafRestriction B hT hS g Y ≅
      relocalizeSheafRestriction B hT hS g X ⋙ smallEtaleDirectImage B T hT f :=
  Functor.isoWhiskerRight (smallEtaleDirectImageRanIso B S hS (relocalizeHom B hT hS g f)) _ ≪≫
    relocalizeDirectImageRanIso B hT hS g f ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleDirectImageRanIso B T hT f).symm

open Stacks.Sheaves.ToposPullback in
/-- The comparison of the transported structure sheaves of rings induced by
`AlgebraicGeometry.Space.relocalizeDirectImageIso`. -/
abbrev relocalizeDirectImageRingMap :
    pullbackRingSheaf (SmallEtale.topology B T hT Y.1)
        (smallEtaleDirectImage B S hS (relocalizeHom B hT hS g f) ⋙
          relocalizeSheafRestriction B hT hS g Y)
        (structureRingSheaf B S hS (relocalizeSpace B hT hS g X)) ⟶
      pullbackRingSheaf (SmallEtale.topology B T hT Y.1)
        (relocalizeSheafRestriction B hT hS g X ⋙ smallEtaleDirectImage B T hT f)
        (structureRingSheaf B S hS (relocalizeSpace B hT hS g X)) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B T hT Y.1)
    (structureRingSheaf B S hS (relocalizeSpace B hT hS g X))
    (relocalizeDirectImageIso B hT hS g f).hom

open Stacks.Sheaves.ToposPullback in
/-- The structure map `f♯` read with source the restricted structure sheaf of `Λ Y` and target
the direct image of the restricted structure sheaf of `Λ X`; these are the structure sheaves of
`Y` and `X` on the nose. -/
abbrev relocalizeStructureSharp :
    ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B T hT Y.1)
        (SmallEtale.topology B S hS (relocalizeSpace B hT hS g Y).1)).obj
        (structureRingSheaf B S hS (relocalizeSpace B hT hS g Y)) ⟶
      pullbackRingSheaf (SmallEtale.topology B T hT Y.1) (smallEtaleDirectImage B T hT f)
        (((SmallEtale.relocalize B hT hS g X.1 X.2).functor.sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B T hT X.1)
          (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1)).obj
          (structureRingSheaf B S hS (relocalizeSpace B hT hS g X))) :=
  structureSharp B T hT f

open Stacks.Sheaves.ToposPullback in
/-- **The structure maps of `f` and `Λ f` correspond under relocalization**, as morphisms into
the direct image of the structure sheaf of `Λ X` read on the small étale site of `Y`. -/
theorem squareRingMapLeft_structureSharp :
    squareRingMapLeft (SmallEtale.topology B T hT Y.1)
        (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1)
        (SmallEtale.topology B S hS (relocalizeSpace B hT hS g Y).1)
        (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor
        (smallEtaleDirectImage B S hS (relocalizeHom B hT hS g f))
        (structureRingSheaf B S hS (relocalizeSpace B hT hS g X))
        (structureSharp B S hS (relocalizeHom B hT hS g f)) ≫
      relocalizeDirectImageRingMap B hT hS g f =
    squareRingMapRight (SmallEtale.topology B T hT X.1) (SmallEtale.topology B T hT Y.1)
        (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1)
        (SmallEtale.topology B S hS (relocalizeSpace B hT hS g Y).1)
        (SmallEtale.relocalize B hT hS g X.1 X.2).functor
        (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor
        (smallEtaleDirectImage B T hT f)
        (structureRingSheaf B S hS (relocalizeSpace B hT hS g X))
        (relocalizeStructureSharp B hT hS g f) := by
  apply (sheafCompose (SmallEtale.topology B T hT Y.1) (forget RingCat.{u})).map_injective
  rw [Functor.map_comp, ringSheafMap_squareRingMapLeft, ringSheafMap_squareRingMapRight,
    ringSheafMap_pullbackRingSheafMapOfNatTrans]
  show (relocalizeSheafRestriction B hT hS g Y).map
      ((sheafCompose (SmallEtale.topology B S hS (relocalizeSpace B hT hS g Y).1)
        (forget RingCat.{u})).map (structureSharpRan B S hS (relocalizeHom B hT hS g f))) ≫
      (relocalizeSheafRestriction B hT hS g Y).map
        ((smallEtaleDirectImageRanIso B S hS (relocalizeHom B hT hS g f)).inv.app
          (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) ≫
      (relocalizeSheafRestriction B hT hS g Y).map
          ((smallEtaleDirectImageRanIso B S hS (relocalizeHom B hT hS g f)).hom.app
            (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) ≫
        (relocalizeDirectImageRanIso B hT hS g f).hom.app
            (structureSetSheaf B S hS (relocalizeSpace B hT hS g X)) ≫
          (smallEtaleDirectImageRanIso B T hT f).inv.app
            ((relocalizeSheafRestriction B hT hS g X).obj
              (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) =
    (sheafCompose (SmallEtale.topology B T hT Y.1) (forget RingCat.{u})).map
        (structureSharpRan B T hT f) ≫
      (smallEtaleDirectImageRanIso B T hT f).inv.app
        ((relocalizeSheafRestriction B hT hS g X).obj
          (structureSetSheaf B S hS (relocalizeSpace B hT hS g X)))
  have hcancel : (relocalizeSheafRestriction B hT hS g Y).map
        ((smallEtaleDirectImageRanIso B S hS (relocalizeHom B hT hS g f)).inv.app
          (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) ≫
      (relocalizeSheafRestriction B hT hS g Y).map
          ((smallEtaleDirectImageRanIso B S hS (relocalizeHom B hT hS g f)).hom.app
            (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) ≫
        (relocalizeDirectImageRanIso B hT hS g f).hom.app
            (structureSetSheaf B S hS (relocalizeSpace B hT hS g X)) ≫
          (smallEtaleDirectImageRanIso B T hT f).inv.app
            ((relocalizeSheafRestriction B hT hS g X).obj
              (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) =
      (relocalizeDirectImageRanIso B hT hS g f).hom.app
            (structureSetSheaf B S hS (relocalizeSpace B hT hS g X)) ≫
          (smallEtaleDirectImageRanIso B T hT f).inv.app
            ((relocalizeSheafRestriction B hT hS g X).obj
              (structureSetSheaf B S hS (relocalizeSpace B hT hS g X))) := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  exact (congrArg (_ ≫ ·) hcancel).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (relocalizeDirectImageRanIso_structureSharpRan B hT hS g f)))

open Stacks.Sheaves.ToposPullback in
/-- **The direct image of modules commutes with relocalization** (Stacks 03LU read through the
equivalences `E_X`, `E_Y` of `AlgebraicGeometry.Space.relocalizeModulesEquivalence`): for an
arbitrary morphism `f : X ⟶ Y` of algebraic spaces over `T`,
`E_Y⁻¹ ∘ (Λ f)_* ≅ f_* ∘ E_X⁻¹` as functors `Mod(𝒪_{Λ X}) ⥤ Mod(𝒪_Y)`. -/
def relocalizeModulePushforwardIso :
    modulePushforward B S hS (relocalizeHom B hT hS g f) ⋙
        (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).inverse ≅
      (relocalizeModulesEquivalence B hT hS g X.1 X.2).inverse ⋙ modulePushforward B T hT f :=
  pullbackModuleRestrictionSquareIso (SmallEtale.topology B T hT X.1)
    (SmallEtale.topology B T hT Y.1)
    (SmallEtale.topology B S hS (relocalizeSpace B hT hS g X).1)
    (SmallEtale.topology B S hS (relocalizeSpace B hT hS g Y).1)
    (SmallEtale.relocalize B hT hS g X.1 X.2).functor
    (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor
    (smallEtaleDirectImage B T hT f) (smallEtaleDirectImage B S hS (relocalizeHom B hT hS g f))
    (structureRingSheaf B S hS (relocalizeSpace B hT hS g X))
    (relocalizeDirectImageIso B hT hS g f) (relocalizeDirectImageRingMap B hT hS g f)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans _ _ _)
    (structureSharp B S hS (relocalizeHom B hT hS g f)) (relocalizeStructureSharp B hT hS g f)
    (squareRingMapLeft_structureSharp B hT hS g f)

end AlgebraicGeometry.Space

end
