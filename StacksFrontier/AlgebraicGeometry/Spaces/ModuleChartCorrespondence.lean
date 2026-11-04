module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleImageData
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The chart correspondence for modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  `AlgebraicGeometry.Space.chartCorrespondence`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`) is Stacks 03G4 for sheaves of
*sets*: the `f`-maps of Stacks 03G3 from a sheaf `Q` on the small étale site of `Y` to a sheaf
`P` on the small étale site of `X` are exactly the homomorphisms `Q ⟶ f_*P`.  This file upgrades
that bijection to *modules*, which is what the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleImageData` describe as "that bijection
together with the compatibility of the two algebraic fields".

The upgrade is not an `extends`: `AlgebraicGeometry.Space.ModuleFMap` deliberately does not
extend `AlgebraicGeometry.Space.FMap`, because `FMap` is stated for presheaves of types while a
module is a presheaf of modules, so the two algebraic fields `map_add` and `map_smul` are added
alongside the set-level data rather than inherited.  Accordingly the content here is exactly the
two algebraic fields: *the bijection of Stacks 03G4 matches additive and semilinear maps of
sections with morphisms of modules*.

Both halves rest on one observation.  The sections of `f_*F` over an étale scheme chart `V`
of `Y` carry their module structure *transported* along the direct image of sheaves of sets, in
the sense of `CategoryTheory.Sheaf.moduleObjModule`, and
`AlgebraicGeometry.Space.chartProjection` is a natural transformation of
finite-product-preserving functors of sheaves of sets.  So
`CategoryTheory.Sheaf.moduleAddObj_naturality` and
`CategoryTheory.Sheaf.moduleSMulObj_naturality` say that a chart projection is additive and
semilinear over the chartwise pullback of regular functions, which is
`AlgebraicGeometry.Space.chartPullback`, and the chart projections jointly are injective because
the sections of the direct image are a limit over the charts.

## Main definitions

* `AlgebraicGeometry.Space.moduleSetSheaf` is the sheaf of sets underlying a module.
* `AlgebraicGeometry.Space.moduleChartProjection` is the projection of the sections of the direct
  image over an étale scheme chart `V` of `Y` to the sections over an étale scheme chart of `X`
  above `X ×_Y V`, as a natural transformation of finite-product-preserving functors of sheaves
  of sets.  It is `AlgebraicGeometry.Space.chartProjection` precomposed with the comparison
  `AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` of the direct image with its right Kan
  extension form.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp` is the canonical map of sections from a
  module to its direct image at a diagram of étale scheme charts, and
  `AlgebraicGeometry.Space.modulePushforwardCounit` is the linear map of sections along `f` it
  makes up.
* `AlgebraicGeometry.Space.ModuleFMap.toFMap` is the set-level `f`-map of Stacks 03G3 underlying
  a linear map of sections along `f`.
* `AlgebraicGeometry.Space.moduleFMapSetHom` is the set-level bijection
  `AlgebraicGeometry.Space.fmapDirectImageEquiv` of Stacks 03G4 applied to the `f`-map
  underlying a linear map of sections along `f`,
  `AlgebraicGeometry.Space.moduleFMapSection` its action on sections, and
  `AlgebraicGeometry.Space.moduleFMapHom` the morphism of `𝒪_Y`-modules it underlies.
* `AlgebraicGeometry.Space.modulePushforwardHomFMap` is the linear map of sections attached to a
  morphism of modules into the direct image, and
  `AlgebraicGeometry.Space.modulePushforwardHomEquiv` is the module-level chart correspondence
  the two make up.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardPresentation`: **the direct image of modules
  satisfies the chartwise universal property of Stacks 03LU**, that is, it inhabits
  `AlgebraicGeometry.Space.ModulePushforwardPresentation`.  Together with
  `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso` this pins the direct image of
  modules down by its universal property.
* `AlgebraicGeometry.Space.pushforwardModulesPresentation`: the direct image of modules of the
  morphism of ringed topoi of Stacks 03G8 satisfies the same universal property, because by
  `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` the two functors are
  equal.  This is the `ordinaryCanonical` field of
  `AlgebraicGeometry.Space.ModuleImageData`.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_add` and
  `AlgebraicGeometry.Space.modulePushforwardCounitApp_smul`: a chart projection of the direct
  image of modules is additive and semilinear over the chartwise pullback of regular functions.
  These two are the whole module-level content on the counit side;
  `AlgebraicGeometry.Space.moduleFMapSection_add` and
  `AlgebraicGeometry.Space.moduleFMapSection_smul` are the same content on the other side, and
  say that the homomorphism of Stacks 03G4 attached to a linear map of sections is a morphism of
  `𝒪_Y`-modules.
* `AlgebraicGeometry.Space.moduleChartProjection_ext`: a section of the direct image is
  determined by its chart projections.  This is what reduces both to the components.
* `AlgebraicGeometry.Space.moduleChartProjection_app_moduleFMapSection`: the chart projections
  of the homomorphism attached to a linear map of sections are the components of that linear
  map.
* `AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp`: a chart projection carries
  the structure map `f♯` of Stacks 03G8 to `AlgebraicGeometry.Space.chartPullback`, which is why
  the semilinearity coefficient is pullback of regular functions.
* `AlgebraicGeometry.Space.chartBaseChangeMap_indexOfChartDiagram`: the chart morphism which the
  cartesian form of a chart diagram induces is the vertical morphism of schemes of the diagram.

## Implementation notes

This file adds no new copy of the pointwise-limit apparatus.  The chart projection of an
arbitrary sheaf of sets, and the computation of it as the projection of the limit cone, are
`AlgebraicGeometry.Space.ranProj` and `AlgebraicGeometry.Space.ranProj_app_apply`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`), which are used here
through `AlgebraicGeometry.Space.chartProjection_eq_ranProj`; the limit itself is
`AlgebraicGeometry.Space.ranChartCone` and
`AlgebraicGeometry.Space.ranChartCone_π_ext`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondence.lean`).

The structure map of Stacks 03G8 enters this file in one place only:
`AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp` computes a chart projection
of `f♯` with `AlgebraicGeometry.Space.chartProjection_structureMapApp` and nothing else.

The private helper `chartMapPullback` exists only to make
`AlgebraicGeometry.Space.chartPullback` and `AlgebraicGeometry.Space.chartDiagramPullback`
visibly the same function of the vertical scheme morphism, so that `congrArg` can pass between
them; it is not a third notion of pullback of regular functions and is deliberately private.

Two elaboration constraints shape the proofs and are worth recording.  First,
instance search does not find the transported algebraic structures through the spelling
`(CategoryTheory.Sheaf.sectionsFunctor J W).obj (CategoryTheory.Sheaf.moduleSheaf R F)`, so
every statement here is phrased with the module `F.val.obj W` or the direct image
`((modulePushforward B S hS f).obj F).val.obj (op V)` — whose declared types carry the instances
— and the transported-operation lemmas of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullback.lean` are then applied up to
definitional equality, exactly as `AlgebraicGeometry.Space.structureMapApp_add` does for the
structure map.  Second, those lemmas must be given their site, their coefficient ring and their
two finite-product-preservation instances *explicitly*: the ring sheaf has to be presented as
`AlgebraicGeometry.Space.structureRingSheaf`, whose declared topology is
`AlgebraicGeometry.Space.SmallEtale.topology` on the nose, because presenting it as
`AlgebraicGeometry.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite` leaves the topology to be unified through a
semireducible projection and the elaborator then diverges on a universe constraint of the
sheafification instances.

The module universe is pinned to the universe `u` of the structure rings.  That is forced by the
declaration of the direct image and not by any proof here:
`AlgebraicGeometry.Space.modulePushforward`
(`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean`) is declared as a functor
`Modules.{u, u} ⥤ Modules.{u, u}`, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean` record why: the direct image of
modules applies the direct image of sheaves of *sets* to the sheaf underlying the module, and
that is available only at `u`.  Nothing in this file would need a different universe if that
changed.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The chart projections of the direct image of modules -/

/-- The sheaf of sets underlying a module on the small étale site of an algebraic space. -/
noncomputable abbrev moduleSetSheaf (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) F

/-- The projection of the sections of the direct image over an étale scheme chart `V` of `Y` to
the sections over an étale scheme chart of `X` above `X ×_Y V`, as a natural transformation of
finite-product-preserving functors of sheaves of sets.

This is `AlgebraicGeometry.Space.chartProjection` precomposed with the comparison
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` of the direct image of sheaves of sets
with its right Kan extension form, which is the form in which the pointwise limit over the
charts is available.  Being a natural transformation of finite-product-preserving functors is
exactly what makes it compatible with the transported algebraic operations. -/
noncomputable def moduleChartProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V) ⟶
      sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) j.right :=
  Functor.whiskerRight (smallEtaleDirectImageRanIso B S hS f).hom
      (sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) ≫
    chartProjection B S hS f V j

/-- The chart projection of the direct image is the projection of the limit cone, after the
comparison with the right Kan extension form of the direct image. -/
theorem moduleChartProjection_app (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app P x =
      (ranChartCone B S hS X P.obj (chartBaseChange B S hS f V)).π.app j
        (((smallEtaleDirectImageRanIso B S hS f).hom.app P).hom.app (op V) x) :=
  ranProj_app_apply B S hS X (chartBaseChange B S hS f V) P j _

/-- The chart projection of the direct image, **evaluated**: a plain function from the sections
of the direct image over the chart `V` of `Y` to the sections over the chart of `X` named by `j`.

The component of `AlgebraicGeometry.Space.moduleChartProjection` at a sheaf of sets is a
morphism of `Type u`, so its domain is spelled
`(smallEtaleDirectImage B S hS f ⋙ sectionsFunctor _ (op V)).obj P` and
`AlgebraicGeometry.Space.sectionsFunctor` is deliberately a semireducible `def`.  Reading that
hom as a function type and matching its domain with the sections
`((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)` is therefore an unfolding, and it is
one a consumer performs in whatever `isDefEq` first applies the component to a section.  This
declaration fixes the domain at that geometric spelling once and for all, so that a consumer
supplying a section whose own type has to be identified with it — a section of a module-side
direct image, say — performs that identification and nothing else. -/
noncomputable def moduleChartProjectionFun (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) : P.obj.obj j.right :=
  (moduleChartProjection B S hS f V j).app P x

/-- The evaluated chart projection is the component of the chart projection. -/
theorem moduleChartProjectionFun_eq (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    moduleChartProjectionFun B S hS f V j P x =
      (moduleChartProjection B S hS f V j).app P x :=
  rfl

/-- The component of the chart projection is the evaluated chart projection.

This is `AlgebraicGeometry.Space.moduleChartProjectionFun_eq` reversed, and it is a declaration
of its own rather than its `Eq.symm` because an equation takes its elaborated type from its left
hand side: a consumer that has a section typed module-side pays the identification with the
geometric spelling once in whichever of the two orientations it uses, and `Eq.symm` of the one
would pay it in both. -/
theorem moduleChartProjection_app_eq_fun (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app P x =
      moduleChartProjectionFun B S hS f V j P x :=
  rfl

/-- Two sections of the direct image over an étale scheme chart `V` of `Y` agree as soon as all
their chart projections agree: the sections are a limit over the étale scheme charts of `X`
above `X ×_Y V`. -/
theorem moduleChartProjection_ext (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {x y : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)}
    (h : ∀ j, (moduleChartProjection B S hS f V j).app P x =
      (moduleChartProjection B S hS f V j).app P y) :
    x = y := by
  have hinv : ∀ z : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V),
      ((smallEtaleDirectImageRanIso B S hS f).inv.app P).hom.app (op V)
        (((smallEtaleDirectImageRanIso B S hS f).hom.app P).hom.app (op V) z) = z := fun z ↦
    congrArg
      (fun m : (smallEtaleDirectImage B S hS f).obj P ⟶
          (smallEtaleDirectImage B S hS f).obj P ↦ m.hom.app (op V) z)
      (Iso.hom_inv_id_app (smallEtaleDirectImageRanIso B S hS f) P)
  refine ((hinv x).symm.trans ?_).trans (hinv y)
  refine congrArg
    (fun z ↦ ((smallEtaleDirectImageRanIso B S hS f).inv.app P).hom.app (op V) z) ?_
  refine ranChartCone_π_ext B S hS X P.obj (chartBaseChange B S hS f V) (fun j ↦ ?_)
  exact ((moduleChartProjection_app B S hS f V j P x).symm.trans (h j)).trans
    (moduleChartProjection_app B S hS f V j P y)

/-! ### The chartwise pullback of regular functions, in the two spellings -/

/-- Pullback of regular functions along a morphism of étale scheme charts over `f`.

This exists only so that `AlgebraicGeometry.Space.chartPullback` and
`AlgebraicGeometry.Space.chartDiagramPullback` are visibly one and the same function of the
vertical morphism of schemes; it is not a third notion. -/
private noncomputable def chartMapPullback (U : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V) :
    (structureSetSheaf B S hS Y).obj.obj (op V) ⟶
      (structureSetSheaf B S hS X).obj.obj (op U) :=
  (forget CommRingCat.{u}).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op)

/-- The chart morphism determined by a chart diagram is the vertical morphism of schemes of that
diagram: the cartesian form of the diagram is compatible with the cartesian projection. -/
theorem chartBaseChangeMap_indexOfChartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartBaseChangeMap B S hS f d.V (indexOfChartDiagram B S hS f d) = d.g :=
  yoneda.map_injective
    ((yoneda_map_chartBaseChangeMap B S hS f d.V (indexOfChartDiagram B S hS f d)).trans
      (congrArg (fun q ↦ q.hom) (chartLift_projection B S hS f d)))

/-- Pullback of regular functions along the chart morphism determined by a chart diagram is
pullback along the vertical morphism of schemes of that diagram. -/
theorem chartPullback_indexOfChartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op d.V)) :
    chartPullback B S hS f d.V (indexOfChartDiagram B S hS f d) r =
      chartDiagramPullback B S hS f d r :=
  congrArg (fun g ↦ chartMapPullback B S hS d.U d.V g r)
    (chartBaseChangeMap_indexOfChartDiagram B S hS f d)


/-! ### The chart projections and the structure map -/

/-- A chart projection of the direct image of the structure sheaf takes the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 to pullback of regular functions along the induced morphism
of charts.

This is `AlgebraicGeometry.Space.chartProjection_structureMapApp`, the chart formula for the
structure map, after cancelling the comparison of the direct image with its right Kan extension
form, which is the only thing the structure map is transported along. -/
theorem moduleChartProjection_app_structureSharp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        (((structureSharp B S hS f).hom.app (op V)).hom r) =
      chartPullback B S hS f V j r := by
  have hs : ((structureSharp B S hS f).hom.app (op V)).hom r =
      ((smallEtaleDirectImageRanIso B S hS f).inv.app
        (structureSetSheaf B S hS X)).hom.app (op V) (structureMapApp B S hS f V r) := rfl
  have hid : ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (structureSetSheaf B S hS X)).hom.app (op V)
      (((smallEtaleDirectImageRanIso B S hS f).inv.app
        (structureSetSheaf B S hS X)).hom.app (op V) (structureMapApp B S hS f V r)) =
      structureMapApp B S hS f V r :=
    congrArg (fun m : (smallEtaleDirectImageRan B S hS f).obj (structureSetSheaf B S hS X) ⟶
        (smallEtaleDirectImageRan B S hS f).obj (structureSetSheaf B S hS X) ↦
      m.hom.app (op V) (structureMapApp B S hS f V r))
      (Iso.inv_hom_id_app (smallEtaleDirectImageRanIso B S hS f)
        (structureSetSheaf B S hS X))
  rw [hs, moduleChartProjection_app, hid]
  exact (ranProj_app_apply B S hS X (chartBaseChange B S hS f V)
    (structureSetSheaf B S hS X) j _).symm.trans
    (chartProjection_structureMapApp B S hS f V j r)

/-! ### The counit: the canonical linear map of sections into the direct image -/

/-- The canonical map of sections from a module to its direct image, at a diagram of étale
scheme charts: the chart projection at the étale scheme chart of `X` above `X ×_Y V` which the
chart diagram names. -/
noncomputable def modulePushforwardCounitApp (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) : F.val.obj (op d.U) :=
  (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
    (moduleSetSheaf B S hS X F) x

/-- The canonical map of sections into the direct image is the set-level `f`-map that
`AlgebraicGeometry.Space.ranFmap` attaches to the comparison of the direct image with its right
Kan extension form.  This is what gives it its compatibility with restriction of both charts. -/
theorem modulePushforwardCounitApp_eq (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d x =
      (ranFmap B S hS f (moduleSetSheaf B S hS X F)
        ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X F))
        ((smallEtaleDirectImageRanIso B S hS f).hom.app
          (moduleSetSheaf B S hS X F))).app d x :=
  moduleChartProjection_app B S hS f d.V (indexOfChartDiagram B S hS f d)
    (moduleSetSheaf B S hS X F) x

/-- The canonical map of sections into the direct image is the evaluated chart projection
`AlgebraicGeometry.Space.moduleChartProjectionFun` at the index the chart diagram names.

This holds by `Eq.refl` and it is the crossing of the divide between the two spellings of the
sections of a direct image:  on the left the section is typed module-side, as an element of the
`ModuleCat` of sections of `f_*F`, and on the right geometrically, as a section of the direct
image of the underlying sheaf of sets.  It is its own declaration for exactly that reason, so
that no other step has to perform this identification alongside a second one. -/
theorem modulePushforwardCounitApp_eq_fun (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d x =
      moduleChartProjectionFun B S hS f d.V (indexOfChartDiagram B S hS f d)
        (moduleSetSheaf B S hS X F) x :=
  rfl

/-- The canonical map of sections into the direct image is compatible with étale restriction of
both charts. -/
theorem modulePushforwardCounitApp_naturality (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hcond : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d'
        (((modulePushforward B S hS f).obj F).val.map j.op x) =
      F.val.map i.op (modulePushforwardCounitApp B S hS f F d x) := by
  have h := (ranFmap B S hS f (moduleSetSheaf B S hS X F)
    ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X F))
    ((smallEtaleDirectImageRanIso B S hS f).hom.app
      (moduleSetSheaf B S hS X F))).naturality d d' i j hcond x
  refine Eq.trans (modulePushforwardCounitApp_eq B S hS f F d' _) (Eq.trans h ?_)
  exact congrArg (fun z : F.val.obj (op d.U) ↦ (F.val.map i.op) z)
    (modulePushforwardCounitApp_eq B S hS f F d x).symm

/-- A chart projection of the direct image of modules is additive. -/
private theorem moduleChartProjection_app_add (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x y : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    (show F.val.obj j.right from
        (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) (x + y)) =
      (show F.val.obj j.right from
          (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x) +
        (show F.val.obj j.right from
          (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) y) := by
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) := inferInstance
  have hQ : PreservesFiniteProducts (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1)
      j.right) := inferInstance
  refine Eq.trans (@moduleAddObj_naturality _ _ _ _
    (structureRingSheaf B S hS X) F _ hP _ hQ
    (moduleChartProjection B S hS f V j) x y) ?_
  exact sectionsFunctor_map_moduleAddHom (structureRingSheaf B S hS X) F j.right _ _

/-- A chart projection of the direct image of modules is semilinear over the chartwise pullback
of regular functions. -/
private theorem moduleChartProjection_app_smul (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V))
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) (r • x) =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj j.right from
          chartPullback B S hS f V j r) •
        (show F.val.obj j.right from
          (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x) := by
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) := inferInstance
  have hQ : PreservesFiniteProducts (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1)
      j.right) := inferInstance
  have hR : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget RingCat.{u}) := inferInstance
  have hA : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
  refine Eq.trans (@moduleSMulObj_naturality _ _ _ hR hA
    (structureRingSheaf B S hS X) F _ hP _ hQ
    (moduleChartProjection B S hS f V j)
    (show ((smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)).obj
      (structureSetSheaf B S hS X)) from
      ((structureSharp B S hS f).hom.app (op V)).hom r) x) ?_
  rw [moduleChartProjection_app_structureSharp]
  exact sectionsFunctor_map_moduleSMulHom (structureRingSheaf B S hS X) F j.right _ _

/-- **The canonical map of sections into the direct image is additive.**  The addition on the
sections of the direct image over an étale scheme chart `V` of `Y` is the one transported along
the direct image of sheaves of sets, and a chart projection is a natural transformation of
finite-product-preserving functors, so it respects it. -/
theorem modulePushforwardCounitApp_add (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x y : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d (x + y) =
      modulePushforwardCounitApp B S hS f F d x +
        modulePushforwardCounitApp B S hS f F d y :=
  moduleChartProjection_app_add B S hS f F d.V (indexOfChartDiagram B S hS f d) x y

/-- **The canonical map of sections into the direct image is semilinear over the chartwise
pullback of regular functions.**  The scalar action on the sections of the direct image over an
étale chart `V` of `Y` is the transported action read through the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X`, so a chart projection carries it to the action through
`AlgebraicGeometry.Space.chartDiagramPullback`. -/
theorem modulePushforwardCounitApp_smul (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op d.V))
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d (r • x) =
      chartDiagramPullback B S hS f d r • modulePushforwardCounitApp B S hS f F d x := by
  rw [← chartPullback_indexOfChartDiagram]
  exact moduleChartProjection_app_smul B S hS f F d.V (indexOfChartDiagram B S hS f d) r x

/-- The canonical map of sections into the direct image is natural in the module. -/
theorem modulePushforwardCounitApp_map (f : X ⟶ Y) {F F' : Modules.{u, u} B S hS X.1 X.2}
    (a : F ⟶ F') (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F' d
        (((modulePushforward B S hS f).map a).val.app (op d.V) x) =
      a.val.app (op d.U) (modulePushforwardCounitApp B S hS f F d x) :=
  Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
    ((Sheaf.moduleSheafFunctor
      (structureRingSheaf B S hS X)).map a) x

/-- **Stacks 03LU, the counit of the chartwise universal property.**  The canonical linear map
of sections along `f` from a module to its direct image. -/
noncomputable def modulePushforwardCounit (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    ModuleFMap B S hS f F ((modulePushforward B S hS f).obj F) where
  app := modulePushforwardCounitApp B S hS f F
  naturality := modulePushforwardCounitApp_naturality B S hS f F
  map_add := modulePushforwardCounitApp_add B S hS f F
  map_smul := modulePushforwardCounitApp_smul B S hS f F

/-! ### The homomorphism attached to a linear map of sections -/

/-- The `f`-map of sheaves of sets underlying a linear map of sections along `f`: a linear map
of sections is exactly such an `f`-map together with additivity and semilinearity. -/
def ModuleFMap.toFMap {f : X ⟶ Y} {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} (ξ : ModuleFMap B S hS f F G) :
    FMap B S hS X.1 Y.1 f.hom (moduleSetSheaf B S hS X F).obj
      (moduleSetSheaf B S hS Y G).obj where
  app := ξ.app
  naturality := ξ.naturality

/-- **Stacks 03G4 for modules, the underlying homomorphism of sheaves of sets.**  The
homomorphism into the direct image which the chart correspondence of Stacks 03G4 attaches to the
`f`-map underlying a linear map of sections along `f`.

This is the set-level bijection `AlgebraicGeometry.Space.fmapDirectImageEquiv` applied to
`AlgebraicGeometry.Space.ModuleFMap.toFMap`, and nothing else: no second construction is made
here, and the whole module-level content is the two algebraic fields that
`AlgebraicGeometry.Space.moduleFMapSection_add` and
`AlgebraicGeometry.Space.moduleFMapSection_smul` supply. -/
noncomputable def moduleFMapSetHom (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G) :
    moduleSetSheaf B S hS Y G ⟶
      (smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X F) :=
  fmapDirectImageEquiv B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
    (ModuleFMap.toFMap B S hS ξ)

/-- The section of the direct image of modules attached to a section of `G` by
`AlgebraicGeometry.Space.moduleFMapSetHom`. -/
noncomputable def moduleFMapSection (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G)
    (V : SmallEtale B S hS Y.1) (s : G.val.obj (op V)) :
    ((modulePushforward B S hS f).obj F).val.obj (op V) :=
  (moduleFMapSetHom B S hS f F G ξ).hom.app (op V) s

/-- The chart projections of `AlgebraicGeometry.Space.moduleFMapSection` are the components of
the linear map of sections: that is the property which characterizes it. -/
theorem moduleChartProjection_app_moduleFMapSection (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (ξ : ModuleFMap B S hS f F G) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (s : G.val.obj (op V)) :
    (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F)
        (moduleFMapSection B S hS f F G ξ V s) =
      ξ.app (chartDiagramOfIndex B S hS f V j) s := by
  have hc : moduleFMapSetHom B S hS f F G ξ ≫
      (smallEtaleDirectImageRanIso B S hS f).hom.app (moduleSetSheaf B S hS X F) =
      fmapRan B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
        (ModuleFMap.toFMap B S hS ξ) := by
    show (fmapRan B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
          (ModuleFMap.toFMap B S hS ξ) ≫
        (smallEtaleDirectImageRanIso B S hS f).inv.app (moduleSetSheaf B S hS X F)) ≫
        (smallEtaleDirectImageRanIso B S hS f).hom.app (moduleSetSheaf B S hS X F) = _
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have h2 : ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (moduleSetSheaf B S hS X F)).hom.app (op V)
      (moduleFMapSection B S hS f F G ξ V s) =
      fmapRanApp B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
        (ModuleFMap.toFMap B S hS ξ) V s :=
    congrArg (fun m : moduleSetSheaf B S hS Y G ⟶
        (smallEtaleDirectImageRan B S hS f).obj (moduleSetSheaf B S hS X F) ↦
      m.hom.app (op V) s) hc
  refine Eq.trans (moduleChartProjection_app B S hS f V j (moduleSetSheaf B S hS X F)
    (moduleFMapSection B S hS f F G ξ V s)) ?_
  refine Eq.trans (congrArg (fun z : ((comparisonFunctor B S hS X).op.ran.obj
      (moduleSetSheaf B S hS X F).obj).obj (op (chartBaseChange B S hS f V)) ↦
    (ranChartCone B S hS X (moduleSetSheaf B S hS X F).obj
      (chartBaseChange B S hS f V)).π.app j z) h2) ?_
  exact fmapRanApp_π B S hS f (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
    (ModuleFMap.toFMap B S hS ξ) V j s

/-- The homomorphism attached to a linear map of sections is additive: its chart projections are
the components of the linear map, those are additive, and a section of the direct image is
determined by its chart projections. -/
theorem moduleFMapSection_add (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G)
    (V : SmallEtale B S hS Y.1) (s t : G.val.obj (op V)) :
    moduleFMapSection B S hS f F G ξ V (s + t) =
      moduleFMapSection B S hS f F G ξ V s + moduleFMapSection B S hS f F G ξ V t := by
  refine moduleChartProjection_ext B S hS f V (moduleSetSheaf B S hS X F) (fun j ↦ ?_)
  refine Eq.trans (moduleChartProjection_app_moduleFMapSection B S hS f F G ξ V j (s + t)) ?_
  refine Eq.trans (ξ.map_add (chartDiagramOfIndex B S hS f V j) s t) ?_
  refine Eq.trans ?_ (moduleChartProjection_app_add B S hS f F V j _ _).symm
  rw [moduleChartProjection_app_moduleFMapSection, moduleChartProjection_app_moduleFMapSection]
  rfl

/-- The homomorphism attached to a linear map of sections is semilinear over the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X`, that is, a homomorphism of `𝒪_Y`-modules: its chart projections are the
components of the linear map, those are semilinear over the chartwise pullback of regular
functions, and a section of the direct image is determined by its chart projections. -/
theorem moduleFMapSection_smul (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G)
    (V : SmallEtale B S hS Y.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V))
    (s : G.val.obj (op V)) :
    moduleFMapSection B S hS f F G ξ V (r • s) =
      r • moduleFMapSection B S hS f F G ξ V s := by
  refine moduleChartProjection_ext B S hS f V (moduleSetSheaf B S hS X F) (fun j ↦ ?_)
  refine Eq.trans (moduleChartProjection_app_moduleFMapSection B S hS f F G ξ V j (r • s)) ?_
  refine Eq.trans (ξ.map_smul (chartDiagramOfIndex B S hS f V j) r s) ?_
  refine Eq.trans ?_ (moduleChartProjection_app_smul B S hS f F V j r _).symm
  rw [moduleChartProjection_app_moduleFMapSection]
  rfl

/-- The homomorphism attached to a linear map of sections is compatible with étale restriction
of the chart of `Y`: that is the naturality of
`AlgebraicGeometry.Space.moduleFMapSetHom`. -/
theorem moduleFMapSection_naturality (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G)
    {V W : SmallEtale B S hS Y.1} (g : W ⟶ V) (s : G.val.obj (op V)) :
    moduleFMapSection B S hS f F G ξ W (G.val.map g.op s) =
      ((modulePushforward B S hS f).obj F).val.map g.op
        (moduleFMapSection B S hS f F G ξ V s) := by
  show (moduleFMapSetHom B S hS f F G ξ).hom.app (op W)
      ((moduleSetSheaf B S hS Y G).obj.map g.op s) =
    ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X F)).obj.map g.op
      ((moduleFMapSetHom B S hS f F G ξ).hom.app (op V) s)
  exact ConcreteCategory.congr_hom
    ((moduleFMapSetHom B S hS f F G ξ).hom.naturality g.op) s

/-- **Stacks 03G4 for modules, (3) implies (1).**  The morphism of `𝒪_Y`-modules into the direct
image attached to a linear map of sections along `f`. -/
noncomputable def moduleFMapHom (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G) :
    G ⟶ (modulePushforward B S hS f).obj F where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (Y := ((modulePushforward B S hS f).obj F).val.obj V)
        { toFun := moduleFMapSection B S hS f F G ξ V.unop
          map_add' := moduleFMapSection_add B S hS f F G ξ V.unop
          map_smul' := moduleFMapSection_smul B S hS f F G ξ V.unop }
      naturality := fun g ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
        exact moduleFMapSection_naturality B S hS f F G ξ g.unop s }


/-! ### The chartwise universal property of the direct image of modules -/

/-- **Stacks 03LU, the universal correspondence.**  The linear map of sections along `f`
attached to a morphism of `𝒪_Y`-modules into the direct image: its component at a diagram of
étale scheme charts is the canonical map of sections of the direct image, composed with the
morphism. -/
noncomputable def modulePushforwardHomFMap (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (a : G ⟶ (modulePushforward B S hS f).obj F) :
    ModuleFMap B S hS f F G where
  app := fun d s ↦ modulePushforwardCounitApp B S hS f F d (a.val.app (op d.V) s)
  naturality := fun d d' i j hcond s ↦ by
    refine Eq.trans (congrArg (modulePushforwardCounitApp B S hS f F d')
      (PresheafOfModules.naturality_apply a.val j.op s)) ?_
    exact modulePushforwardCounitApp_naturality B S hS f F d d' i j hcond
      (a.val.app (op d.V) s)
  map_add := fun d s t ↦ by
    refine Eq.trans (congrArg (modulePushforwardCounitApp B S hS f F d)
      ((a.val.app (op d.V)).hom.map_add s t)) ?_
    exact modulePushforwardCounitApp_add B S hS f F d (a.val.app (op d.V) s)
      (a.val.app (op d.V) t)
  map_smul := fun d r s ↦ by
    refine Eq.trans (congrArg (modulePushforwardCounitApp B S hS f F d)
      ((a.val.app (op d.V)).hom.map_smul r s)) ?_
    exact modulePushforwardCounitApp_smul B S hS f F d r (a.val.app (op d.V) s)

/-- The `f`-map underlying the linear map of sections attached to a morphism of modules into the
direct image is the set-level `f`-map that the chart correspondence of Stacks 03G4 attaches to
that morphism. -/
theorem modulePushforwardHomFMap_toFMap (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (a : G ⟶ (modulePushforward B S hS f).obj F) :
    ModuleFMap.toFMap B S hS (modulePushforwardHomFMap B S hS f F G a) =
      (fmapDirectImageEquiv B S hS f (moduleSetSheaf B S hS X F)
          (moduleSetSheaf B S hS Y G)).symm
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map a) := by
  refine FMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  exact modulePushforwardCounitApp_eq B S hS f F d (a.val.app (op d.V) s)

/-- The homomorphism of sheaves of sets attached to the linear map of sections of a morphism of
modules into the direct image is that morphism: the two directions of the chart correspondence
of Stacks 03G4 are mutually inverse, and they carry the algebraic structure along. -/
theorem moduleFMapSetHom_modulePushforwardHomFMap (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (a : G ⟶ (modulePushforward B S hS f).obj F) :
    moduleFMapSetHom B S hS f F G (modulePushforwardHomFMap B S hS f F G a) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map a := by
  refine Eq.trans (congrArg (fun ξ : FMap B S hS X.1 Y.1 f.hom
      (moduleSetSheaf B S hS X F).obj (moduleSetSheaf B S hS Y G).obj ↦
    fmapDirectImageEquiv B S hS f (moduleSetSheaf B S hS X F)
      (moduleSetSheaf B S hS Y G) ξ)
    (modulePushforwardHomFMap_toFMap B S hS f F G a)) ?_
  exact (fmapDirectImageEquiv B S hS f (moduleSetSheaf B S hS X F)
    (moduleSetSheaf B S hS Y G)).apply_symm_apply _

/-- **Stacks 03LU, the chartwise universal property of the direct image of modules.**  The
morphisms of `𝒪_Y`-modules from `G` into the direct image of `F` are exactly the linear maps of
sections along `f` from `F` to `G`.

This is the module-level chart correspondence: the bijection of Stacks 03G4 on underlying
sheaves of sets, matched up with additivity and semilinearity on both sides. -/
noncomputable def modulePushforwardHomEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (G ⟶ (modulePushforward B S hS f).obj F) ≃ ModuleFMap B S hS f F G where
  toFun := modulePushforwardHomFMap B S hS f F G
  invFun := moduleFMapHom B S hS f F G
  left_inv a := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun V ↦ ?_))
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    exact congrArg (fun m : moduleSetSheaf B S hS Y G ⟶
        (smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X F) ↦ m.hom.app V s)
      (moduleFMapSetHom_modulePushforwardHomFMap B S hS f F G a)
  right_inv ξ := by
    refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
    refine Eq.trans (moduleChartProjection_app_moduleFMapSection B S hS f F G ξ d.V
      (indexOfChartDiagram B S hS f d) s) ?_
    exact eq_of_heq (FMap.app_heq B S hS (ModuleFMap.toFMap B S hS ξ)
      (chartDiagramOfIndex_indexOfChartDiagram B S hS f d) HEq.rfl)

/-- **Stacks 03LU: the direct image of modules satisfies the chartwise universal property of the
direct image.**  For a morphism `f : X ⟶ Y` of algebraic spaces,
`AlgebraicGeometry.Space.modulePushforward` — the direct image of `𝒪_X`-modules of Stacks 03D6,
part (1) along the structure map of Stacks 03G8 — carries a canonical linear map of sections
along `f` from every module to its direct image, and composing with it is a bijection between
morphisms of `𝒪_Y`-modules into the direct image and linear maps of sections along `f`.

Together with `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso` this determines the
direct image of modules up to a canonical isomorphism, so it is a characterization and not a
choice.  It is the `canonical` field of `AlgebraicGeometry.Space.ModuleImageData`. -/
noncomputable def modulePushforwardPresentation (f : X ⟶ Y) :
    ModulePushforwardPresentation B S hS f (modulePushforward B S hS f) where
  counit F := modulePushforwardCounit B S hS f F
  homEquiv F G := modulePushforwardHomEquiv B S hS f F G
  homEquiv_apply _ _ _ _ _ := rfl
  naturality a d s := modulePushforwardCounitApp_map B S hS f a d s

/-- **Stacks 03LU, the two models of the direct image of modules satisfy the same universal
property.**  The direct image of modules of the morphism of small étale ringed topoi of
Stacks 03G8 also satisfies the chartwise universal property, because by
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` it *is*
`AlgebraicGeometry.Space.modulePushforward`.

This is the `ordinaryCanonical` field of `AlgebraicGeometry.Space.ModuleImageData`. -/
noncomputable def pushforwardModulesPresentation (f : X ⟶ Y) :
    ModulePushforwardPresentation B S hS f
      (smallEtaleRingedToposHom B S hS f).pushforwardModules :=
  pushforwardModules_eq_modulePushforward B S hS f ▸ modulePushforwardPresentation B S hS f

end AlgebraicGeometry.Space

end
