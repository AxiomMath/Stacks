module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.CategoryTheory.SubfunctorFactor

/-!
# Dense open subspaces cut out by Zariski opens of an étale chart

Let `F` be a presheaf on the big fppf site of a scheme `S` and let `C` be an étale chart of
`F` whose chart morphism `φ : yoneda.obj U ⟶ F` is an open immersion of presheaves.  The
image of `φ` is then an open subspace of `F`, and the Zariski opens of the scheme `U` give a
supply of smaller open subspaces, the étale charts `AlgebraicGeometry.Space.openChart`.

This file is the bookkeeping that lets one pass between the three descriptions of such an
open piece — a subfunctor of `F`, a point set of `|F|`, and a Zariski open of the chart
scheme — and in particular transfers *density* between them in both directions.  It is used
to shrink a chart so that it lands inside a prescribed dense open subspace, the standard
manoeuvre when extending a rational construction over a dense open.

## Main definitions

* `AlgebraicGeometry.Space.chartRange` is the subfunctor of `F` cut out by an étale chart,
  namely the range of its chart morphism.
* `AlgebraicGeometry.Space.openChartGlobalSectionsIso` compares the regular functions on a
  Zariski-open chart with the sections of the structure sheaf of the chart scheme over the
  corresponding open.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_chartRange` and
  `AlgebraicGeometry.Space.range_pointsMap_ι_chartRange`: the range of an open immersion
  chart is an open subspace, with the expected point set.
* `AlgebraicGeometry.Space.exists_lift_of_range_pointsMap_subset` and
  `AlgebraicGeometry.Space.exists_hom_of_range_pointsMap_subset`: a morphism from a
  representable presheaf factors through an open subspace, respectively through an open
  immersion chart, as soon as it does so on point sets.
* `AlgebraicGeometry.Space.range_pointsMap_openChart`: the point set of a Zariski-open chart,
  as the image of the preimage of the open under the comparison map to the chart scheme.
* `AlgebraicGeometry.Space.denseRange_pointsMap_openChart`: a dense Zariski open of a chart
  with dense point set again has dense point set.
* `AlgebraicGeometry.Space.exists_dense_open_le_of_isDenseOpenSubspace`: every dense open
  subspace of `F` contains a Zariski-open chart cut out of `C` by a dense Zariski open of the
  chart scheme.

## Implementation notes

Every declaration here takes the étale chart `C` (or a morphism out of a representable
presheaf) as an explicit argument, and that argument already determines the ambient site data
`B`, `S`, `hS` and the presheaf `F`; those four are therefore left implicit, as they are for
`AlgebraicGeometry.Space.chartScheme`.

The hypothesis that the chart morphism is an open immersion is spelled
`AlgebraicGeometry.Space.IsOpenImmersion`, which unfolds to the relative-representability
property `MorphismProperty.presheaf` of the inverse image of
`AlgebraicGeometry.IsOpenImmersion` along `AlgebraicGeometry.BigFppfOver.toScheme`; this is
exactly the shape carried by
`AlgebraicGeometry.Space.CodimensionZeroPresentation.presheaf_isOpenImmersion_chart`.  No
hypothesis that `F` itself is an algebraic space is needed anywhere: the source of a chart
morphism is representable, hence an algebraic space, and that is all that
`AlgebraicGeometry.Space.isOpenSubspace_subfunctorRange` asks for.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The open subspace cut out by a chart -/

/-- The subfunctor of `F` cut out by an étale chart `C`: the range of the chart morphism
`yoneda.obj C.obj.left ⟶ F`.  When the chart morphism is an open immersion this is an open
subspace of `F`, by `AlgebraicGeometry.Space.isOpenSubspace_chartRange`. -/
def chartRange (C : SmallEtale B S hS F) : Subfunctor F :=
  Subfunctor.range C.1.hom

/-- The subfunctor cut out by an étale chart is by definition the range of its chart
morphism. -/
theorem chartRange_eq_range (C : SmallEtale B S hS F) :
    chartRange C = Subfunctor.range C.1.hom :=
  rfl

/-- **The image of an open immersion chart is an open subspace.**  The source of the chart
morphism is representable, hence an algebraic space, so this is
`AlgebraicGeometry.Space.isOpenSubspace_subfunctorRange`. -/
theorem isOpenSubspace_chartRange (C : SmallEtale B S hS F)
    (hC : IsOpenImmersion B S hS C.1.hom) :
    IsOpenSubspace B S hS (chartRange C) :=
  isOpenSubspace_subfunctorRange B S hS (isAlgebraicSpace_yoneda B S hS _) hC

/-- **The point set of the open subspace cut out by a chart** is the image of the point map
of the chart morphism. -/
theorem range_pointsMap_ι_chartRange (C : SmallEtale B S hS F)
    (hC : IsOpenImmersion B S hS C.1.hom) :
    Set.range (pointsMap B S hS (chartRange C).toFunctor (chartRange C).ι) =
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) :=
  have : Mono C.1.hom := mono_of_presheaf_isOpenImmersion hC
  range_pointsMap_ι_range B S hS C.1.hom

/-! ### Factoring a morphism through an open subspace -/

/-- **A morphism from a representable presheaf factors through an open subspace as soon as it
does so on point sets.**

The subspace `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by the point set of the
morphism contains its range, and is contained in `W` by
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`, since its own point set is that
point set. -/
theorem exists_lift_of_range_pointsMap_subset {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ F)
    {W : Subfunctor F} (hW : IsOpenSubspace B S hS W)
    (h : Set.range (pointsMap B S hS (yoneda.obj A) q) ⊆
      Set.range (pointsMap B S hS W.toFunctor W.ι)) :
    ∃ τ : yoneda.obj A ⟶ W.toFunctor, τ ≫ W.ι = q :=
  have hle : openSubspaceOfPoints B S hS F (Set.range (pointsMap B S hS (yoneda.obj A) q)) ≤ W :=
    le_of_range_pointsMap_ι_subset B S hS hW
      (by rw [range_pointsMap_ι_openSubspaceOfPoints]; exact h)
  ⟨Subfunctor.lift q ((range_le_openSubspaceOfPoints_range_pointsMap q).trans hle),
    Subfunctor.lift_ι _ _⟩

/-- **A morphism from a representable presheaf factors through an open immersion chart as
soon as it does so on point sets.**

The chart cuts out the open subspace `AlgebraicGeometry.Space.chartRange`, with point set the
image of the chart morphism, so
`AlgebraicGeometry.Space.exists_lift_of_range_pointsMap_subset` factors the morphism through
that subspace, and a section of the subspace over `A` is by definition a morphism
`A ⟶ C.obj.left` composing to the given one. -/
theorem exists_hom_of_range_pointsMap_subset (C : SmallEtale B S hS F)
    (hC : IsOpenImmersion B S hS C.1.hom) {A : BigFppfOver B S hS} (k : yoneda.obj A ⟶ F)
    (h : Set.range (pointsMap B S hS (yoneda.obj A) k) ⊆
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom)) :
    ∃ σ : A ⟶ C.obj.left, yoneda.map σ ≫ C.1.hom = k := by
  obtain ⟨τ, hτ⟩ := exists_lift_of_range_pointsMap_subset k (isOpenSubspace_chartRange C hC)
    (by rw [range_pointsMap_ι_chartRange C hC]; exact h)
  have hmem : yonedaEquiv k ∈ Set.range (C.1.hom.app (op A)) := by
    rw [← hτ, yonedaEquiv_comp]
    exact (yonedaEquiv τ).2
  obtain ⟨σ, hσ⟩ := hmem
  refine ⟨σ, yonedaEquiv.injective ?_⟩
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact hσ

/-! ### Zariski opens of a chart -/

/-- **The point set of the inclusion of a Zariski open of an object of the big fppf site of
`S`**: under the comparison bijection of `AlgebraicGeometry.Space.pointsToScheme` it is the
open itself. -/
theorem range_pointsMap_yoneda_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    Set.range (pointsMap B S hS (yoneda.obj (openSub A O)) (yoneda.map (openSubHom A O))) =
      pointsToScheme B S hS A ⁻¹' (O : Set ((BigFppfOver.toScheme B S hS).obj A)) := by
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom A O)) =
      (O : Set ((BigFppfOver.toScheme B S hS).obj A)) := by
    rw [toScheme_map_openSubHom]
    exact O.range_ι
  refine Set.eq_of_subset_of_subset ?_ fun w hw ↦ ?_
  · rintro y ⟨w, rfl⟩
    rw [Set.mem_preimage, pointsToScheme_pointsMap_yoneda, ← hrange]
    exact Set.mem_range_self _
  · refine mem_range_pointsMap_yoneda_map B S hS (openSubHom A O) w ?_
    rw [hrange]
    exact hw

/-- **The point set of a Zariski-open chart** is the image, under the point map of the
ambient chart, of the preimage of the open in the point space of the chart scheme. -/
theorem range_pointsMap_openChart (C : SmallEtale B S hS F) (O : (chartScheme C).Opens) :
    Set.range (pointsMap B S hS (yoneda.obj (openChart B S hS F C O).obj.left)
        (openChart B S hS F C O).1.hom) =
      pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom ''
        (pointsToScheme B S hS C.obj.left ⁻¹' (O : Set (chartScheme C))) := by
  show Set.range (pointsMap B S hS (yoneda.obj (openSub C.obj.left O))
    (yoneda.map (openSubHom C.obj.left O) ≫ C.1.hom)) = _
  rw [pointsMap_comp, Set.range_comp, range_pointsMap_yoneda_map_openSubHom]

/-! ### Transfer of density -/

/-- The comparison map from the points of a chart to its scheme is continuous. -/
private theorem continuous_pointsToScheme_chart (C : SmallEtale B S hS F) :
    Continuous (pointsToScheme B S hS C.obj.left) :=
  (schemePointsHomeomorph B S hS C.obj.left).continuous

/-- The comparison map from the points of a chart to its scheme is an open map. -/
private theorem isOpenMap_pointsToScheme_chart (C : SmallEtale B S hS F) :
    IsOpenMap (pointsToScheme B S hS C.obj.left) :=
  (schemePointsHomeomorph B S hS C.obj.left).isOpenMap

/-- **A dense Zariski open of a chart with dense point set again has dense point set.**

The point set of the Zariski-open chart is the image under the chart's point map of the
preimage of the open; the preimage of a dense set under the comparison homeomorphism to the
chart scheme is dense, and the image of a dense set under a continuous map with dense range
is dense. -/
theorem denseRange_pointsMap_openChart (C : SmallEtale B S hS F)
    (hdense : DenseRange (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))
    (O : (chartScheme C).Opens) (hO : Dense (O : Set (chartScheme C))) :
    DenseRange (pointsMap B S hS (yoneda.obj (openChart B S hS F C O).obj.left)
      (openChart B S hS F C O).1.hom) := by
  show Dense (Set.range (pointsMap B S hS (yoneda.obj (openChart B S hS F C O).obj.left)
    (openChart B S hS F C O).1.hom))
  rw [range_pointsMap_openChart]
  exact hdense.dense_image (continuous_pointsMap B S hS C.1.hom)
    (hO.preimage (isOpenMap_pointsToScheme_chart C))

/-- **A chart with dense point set can be shrunk into any dense open subspace, by a dense
Zariski open of its scheme.**

The preimage, under the point map of the chart, of the point set of the open subspace `W` is
open by continuity and dense because the point map is open with dense range; transported to
the chart scheme along the comparison homeomorphism it is a dense Zariski open `O`.  The point
set of the Zariski-open chart cut out by `O` is then contained in that of `W`, so the chart
morphism factors through `W` by
`AlgebraicGeometry.Space.exists_lift_of_range_pointsMap_subset`. -/
theorem exists_dense_open_le_of_isDenseOpenSubspace (C : SmallEtale B S hS F)
    (hC : IsOpenImmersion B S hS C.1.hom)
    (hdense : DenseRange (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))
    {W : Subfunctor F} (hWopen : IsOpenSubspace B S hS W)
    (hWdense : Dense (Set.range (pointsMap B S hS W.toFunctor W.ι))) :
    ∃ O : (chartScheme C).Opens, Dense (O : Set (chartScheme C)) ∧
      ∃ τ : yoneda.obj (openChart B S hS F C O).obj.left ⟶ W.toFunctor,
        τ ≫ W.ι = (openChart B S hS F C O).1.hom := by
  have hPdense : Dense (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom ⁻¹'
      Set.range (pointsMap B S hS W.toFunctor W.ι)) :=
    hWdense.preimage (isOpenMap_pointsMap_of_isOpenImmersion B S hS C.1.hom hC)
  have hPopen : IsOpen (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom ⁻¹'
      Set.range (pointsMap B S hS W.toFunctor W.ι)) :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hWopen.2).preimage
      (continuous_pointsMap B S hS C.1.hom)
  refine ⟨⟨pointsToScheme B S hS C.obj.left '' (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom ⁻¹'
    Set.range (pointsMap B S hS W.toFunctor W.ι)), isOpenMap_pointsToScheme_chart C _ hPopen⟩,
    (surjective_pointsToScheme B S hS C.obj.left).denseRange.dense_image
      (continuous_pointsToScheme_chart C) hPdense, ?_⟩
  refine exists_lift_of_range_pointsMap_subset _ hWopen ?_
  rw [range_pointsMap_openChart, Opens.coe_mk,
    Set.preimage_image_eq _ (injective_pointsToScheme B S hS C.obj.left)]
  exact Set.image_preimage_subset _ _

/-! ### Regular functions on a Zariski-open chart -/

/-- The regular functions on the Zariski-open chart cut out of `C` by an open `O` are the
global regular functions on the open subscheme `O`. -/
theorem structurePresheaf_obj_op_openChart (C : SmallEtale B S hS F)
    (O : (chartScheme C).Opens) :
    (structurePresheaf B S hS F).obj (op (openChart B S hS F C O)) = Γ(O.toScheme, ⊤) :=
  rfl

/-- **The regular functions on a Zariski-open chart are the sections of the structure sheaf of
the chart scheme over the open**, by Mathlib's `AlgebraicGeometry.Scheme.Opens.topIso`. -/
noncomputable def openChartGlobalSectionsIso (C : SmallEtale B S hS F)
    (O : (chartScheme C).Opens) :
    (structurePresheaf B S hS F).obj (op (openChart B S hS F C O)) ≅ Γ(chartScheme C, O) :=
  O.topIso

end AlgebraicGeometry.Space

end
