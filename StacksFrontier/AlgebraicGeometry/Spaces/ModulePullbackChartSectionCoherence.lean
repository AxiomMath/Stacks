module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart

/-!
# The two coherences of the chart section of an inverse image

`AlgebraicGeometry.Space.modulePullbackChartSection` carries a section of an `𝒪_Y`-module `M`
over an étale scheme chart `d.V` of `Y` to a section of `f^*M` over an étale scheme chart `d.U`
of `X`, along a commuting diagram `d` of charts over a morphism `f : X ⟶ Y` of algebraic
spaces.  It had naturality in the module
(`AlgebraicGeometry.Space.modulePullbackChartSection_map`) and nothing else: no value along an
identity morphism and no value along a composite.  Those two values are what the functoriality
of the backward functor of Stacks 06WT needs, and this file is them.

**The identity law is proved.  The composite law is proved except for one step of spelling**,
which is isolated as `AlgebraicGeometry.Space.ModulePushforwardChartComponentCompResidue`; that
declaration's docstring says exactly what the step is, that both of its halves are theorems
here, and how each of the routes to it fails.

## Main results

* `AlgebraicGeometry.Space.modulePullbackIdIso_hom_app_val_app_modulePullbackChartSection`:
  **the chart section along an identity is restriction along the diagram.**  A chart diagram
  over `𝟙 X` is a morphism of étale charts of `X`
  (`AlgebraicGeometry.Space.chartMapOfIdChartDiagram`), and the unit law `(𝟙 X)^* ≅ 𝟭` of
  Stacks 03LU carries the chart section along `𝟙 X` to restriction of the section along that
  morphism of charts.  This is the identity coherence.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_modulePushforwardIdIso_inv_app`: its
  input for the direct image — the chart component of `(𝟙 X)_* ≅ 𝟭` is restriction along the
  diagram.  This is the step `modulePullbackIdIso` had no value for.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_smallToposMorphismTypeU_comp`: **the
  composition law of Stacks 03LU for the chart component of the direct image of modules** — on a
  chart diagram over `f ≫ g` which factors through an étale scheme chart of `Y`, the geometric
  comparison of Stacks 03G2, part (3), followed by the chart component along `f ≫ g`, is the
  composite of the two chart components.  This is the step the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartCorrespondenceComp.lean` record as the one
  that would give a chart formula for a composite, and it is the substantive half of the
  composite coherence.
* (`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app`, from
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`: the
  comparison of direct images of modules along a composite is that geometric comparison, on a
  section.)
* `AlgebraicGeometry.Space.homEquiv_comp_modulePushforwardCompIso_hom_app` and
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_hom_app_homEquiv`: the iterated adjoint
  transpose of `g^* ∘ f^* ≅ (f ≫ g)^*`, followed by the comparison of direct images, is the
  unit of the adjunction for `f ≫ g` — as morphisms and on a section.  This is the other half.
* `AlgebraicGeometry.Space.modulePullbackChartSection_comp_eq_unitSection`: a composite of
  chart sections, in the transported spelling the two halves are stated in.
* `AlgebraicGeometry.Space.ModulePushforwardChartComponentCompResidue`: **what is left.**

## Route

Both coherences are read on the *transported* spelling
`AlgebraicGeometry.Space.modulePullbackUnitSection` of the chart section, which
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection` identifies
with `modulePullbackChartSection`.  That spelling is built from
`AlgebraicGeometry.Space.modulePullbackAdjunction` and
`AlgebraicGeometry.Space.modulePushforwardCounitApp`, which are the two pieces
`modulePullbackIdIso` and `modulePullbackCompIso` are themselves built from, so each coherence
becomes a coherence of the direct image's chart component:
`AlgebraicGeometry.Space.val_app_modulePullbackUnitSection` moves the comparison of inverse
images out of the chart component and turns it into its adjoint transpose, and the value of that
transpose on a chart is what is computed here.

For the identity the computation is in three steps.
`AlgebraicGeometry.Space.modulePushforwardCounitApp_naturality` — the compatibility of the
chart component with restriction of both charts — reduces an arbitrary chart diagram over
`𝟙 X` to the one whose vertical morphism is the identity, namely the diagram of the index
`AlgebraicGeometry.Space.chartBaseChangeMap_id` computes.  At that diagram the chart component
is the chart projection at that index, which by
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIdIso_hom_app_apply` *is* the identification
of the direct image of sheaves of sets along an identity with the identity functor; and
`AlgebraicGeometry.Space.modulePushforwardIdIso_inv_app_val_app_apply` says the comparison of
direct images of modules is that identification on sections.  So the two cancel.

For the composite the computation goes through Stacks 03G4.  The chart components of the direct
image are the `f`-map which the chart correspondence attaches to the identity of the direct
image, so the geometric comparison of Stacks 03G2, part (3), is the `f ≫ g`-map it attaches to
that comparison; by `AlgebraicGeometry.Space.FMap.comp_unique` that `f ≫ g`-map is the composite
of the two, because each factor contributes an identity, and
`AlgebraicGeometry.Space.FMap.comp_app` is then its chart formula on a diagram that factors.
The module level adds nothing: the chart component of the direct image of modules is a chart
projection of the underlying sheaf of sets, which is what the set-level statement is about.

## Implementation notes

Every step that reads a composite on a section is taken through a named lemma stated at
variable arguments (`AlgebraicGeometry.Space.comp_val_app_apply`,
`AlgebraicGeometry.Space.val_app_modulePullbackUnitSection`,
`CategoryTheory.Sheaf.hom_congr_app_apply`), never by `rw` or `simp` inside an application at
the concrete types: at `AlgebraicGeometry.Space.smallEtaleRingedTopos` the composition of the
category of modules is reached only by unfolding the ringed site, and that does not terminate
in any budget.  That is the constraint recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean`, and it is why the
proofs below are term-mode chains and why several of them exist only to pay one identification
inside their own declaration — the elaborator's budget is per declaration.

The chart diagram at which the identity law is computed is written
`AlgebraicGeometry.Space.chartDiagramOfIndex` of the index of
`AlgebraicGeometry.Space.chartBaseChangeMap_id`, and *not*
`AlgebraicGeometry.Space.idChartDiagram`, although the two are equal
(`AlgebraicGeometry.Space.idDiagram_eq_idChartDiagram`).  The reason is that
`AlgebraicGeometry.Space.modulePushforwardCounitApp` is defined through
`AlgebraicGeometry.Space.indexOfChartDiagram` of its diagram, and the codomain of a chart
projection depends on its index, so transporting a value along an equality of *diagrams* needs
a `HEq`; written at `chartDiagramOfIndex` the index is given by
`AlgebraicGeometry.Space.indexOfChartDiagram_chartDiagramOfIndex` and no transport arises.

Nothing here raises a compiler limit or disables a linter, and no `@[stacks]` attribute is
placed or removed: the identity and composition laws of Stacks 03LU are carried by
`AlgebraicGeometry.Space.modulePullbackIdIso`,
`AlgebraicGeometry.Space.modulePushforwardIdIso`,
`AlgebraicGeometry.Space.modulePullbackCompIso` and
`AlgebraicGeometry.Space.modulePushforwardCompIso`, and what is added here is the value of those
laws on sections over a chart.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading a chart projection of the direct image through the Kan-extension form -/

/-- A chart projection of the direct image of modules is the set-level chart projection of the
Kan-extension form, taken after the comparison of the two forms.  This is the definition of
`AlgebraicGeometry.Space.moduleChartProjection`, stated on a section so that it can be used
without unfolding. -/
theorem moduleChartProjection_app_eq_chartProjection {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj F).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app F x =
      (chartProjection B S hS f V j).app F
        (((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom.app (op V) x) :=
  rfl

/-! ### The identity law -/

section Identity

variable (X : AlgebraicSpaces B S hS)

/-- The index at which the chart projections of the direct image along an identity compute the
identification with the identity functor: the inverse of the identity base-change comparison of
`AlgebraicGeometry.Space.spacesBaseChange_id`. -/
def idIndex (V : SmallEtale B S hS X.1) :
    StructuredArrow (op (chartBaseChange B S hS (𝟙 X) V))
      (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk ((spacesBaseChange_id B S hS X).inv.app
    ((comparisonFunctor B S hS X).obj V)).op

/-- The chart diagram over `𝟙 X` named by `AlgebraicGeometry.Space.idIndex`: by
`AlgebraicGeometry.Space.chartBaseChangeMap_id` its vertical morphism is the identity, so it is
the chart diagram at a single chart. -/
def idDiagram (V : SmallEtale B S hS X.1) : ChartDiagram B S hS X.1 X.1 (𝟙 X.1) :=
  chartDiagramOfIndex B S hS (𝟙 X) V (idIndex B S hS X V)

/-- The source chart of `AlgebraicGeometry.Space.idDiagram` is the chart it is built at. -/
theorem idDiagram_U (V : SmallEtale B S hS X.1) : (idDiagram B S hS X V).U = V := rfl

/-- The target chart of `AlgebraicGeometry.Space.idDiagram` is the chart it is built at. -/
theorem idDiagram_V (V : SmallEtale B S hS X.1) : (idDiagram B S hS X V).V = V := rfl

/-- **The vertical morphism of `AlgebraicGeometry.Space.idDiagram` is the identity.**  This is
`AlgebraicGeometry.Space.chartBaseChangeMap_id`, the chart morphism of an identity. -/
theorem idDiagram_g (V : SmallEtale B S hS X.1) :
    (idDiagram B S hS X V).g = 𝟙 ((SmallEtale.toOver B S hS X.1).obj V) :=
  chartBaseChangeMap_id B S hS X V

/-- `AlgebraicGeometry.Space.idDiagram` is the chart diagram at a single chart. -/
theorem idDiagram_eq_idChartDiagram (V : SmallEtale B S hS X.1) :
    idDiagram B S hS X V = idChartDiagram B S hS X V :=
  ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq (idDiagram_g B S hS X V))

/-- The index of `AlgebraicGeometry.Space.idDiagram` is the index it was built from: chart
diagrams over a morphism and étale charts above the base change are mutually inverse. -/
theorem indexOfChartDiagram_idDiagram (V : SmallEtale B S hS X.1) :
    indexOfChartDiagram B S hS (𝟙 X) (idDiagram B S hS X V) = idIndex B S hS X V :=
  indexOfChartDiagram_chartDiagramOfIndex B S hS (𝟙 X) V (idIndex B S hS X V)

/-- The morphism of étale charts a chart diagram over `𝟙 X` is has the vertical morphism of the
diagram as its morphism of schemes.  This is the definition of
`AlgebraicGeometry.Space.chartMapOfIdChartDiagram`. -/
theorem toOver_map_chartMapOfIdChartDiagram
    (d : ChartDiagram B S hS X.1 X.1 (𝟙 X.1)) :
    (SmallEtale.toOver B S hS X.1).map (chartMapOfIdChartDiagram B S hS X d) = d.g :=
  rfl

/-- **The chart projection of the identification `(𝟙 X)_* ≅ 𝟭` of sheaves of sets, at the index
of `AlgebraicGeometry.Space.chartBaseChangeMap_id`, undoes it.**  By
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIdIso_hom_app_apply` that chart projection
*is* the identification in its Kan-extension form, so this is one half of an isomorphism. -/
theorem chartProjection_idIndex_smallEtaleDirectImageRanIdIso_inv
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS X.1)
    (s : F.obj.obj (op V)) :
    (chartProjection B S hS (𝟙 X) V (idIndex B S hS X V)).app F
        (((smallEtaleDirectImageRanIdIso B S hS X).inv.app F).hom.app (op V) s) = s :=
  (smallEtaleDirectImageRanIdIso_hom_app_apply B S hS X F V
      (((smallEtaleDirectImageRanIdIso B S hS X).inv.app F).hom.app (op V) s)).symm.trans
    (Sheaf.hom_congr_app_apply
      (Iso.inv_hom_id_app (smallEtaleDirectImageRanIdIso B S hS X) F) (op V) s)

/-- The identification `(𝟙 X)_* ≅ 𝟭` of sheaves of sets is the comparison with the
Kan-extension form followed by the identification of that form with the identity functor, read
on a section.  This is its definition. -/
theorem smallEtaleDirectImageIdIso_inv_app_apply
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS X.1)
    (s : F.obj.obj (op V)) :
    ((smallEtaleDirectImageIdIso B S hS X).inv.app F).hom.app (op V) s =
      ((smallEtaleDirectImageRanIso B S hS (𝟙 X)).inv.app F).hom.app (op V)
        (((smallEtaleDirectImageRanIdIso B S hS X).inv.app F).hom.app (op V) s) :=
  rfl

/-- **The chart projection of the comparison of direct images of modules along an identity, at
the index of `AlgebraicGeometry.Space.chartBaseChangeMap_id`, undoes it.**  The comparison is
the identification of sheaves of sets on sections
(`AlgebraicGeometry.Space.modulePushforwardIdIso_inv_app_val_app_apply`), the chart projection
of the direct image is the set-level one after the comparison with the Kan-extension form, and
that comparison cancels against the one inside the identification. -/
theorem moduleChartProjection_idIndex_modulePushforwardIdIso_inv_app
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (s : M.val.obj (op V)) :
    (moduleChartProjection B S hS (𝟙 X) V (idIndex B S hS X V)).app
        (moduleSetSheaf B S hS X M)
        (((modulePushforwardIdIso B S hS X).inv.app M).val.app (op V) s) = s := by
  refine Eq.trans (moduleChartProjection_app_eq_chartProjection B S hS (𝟙 X) V
    (idIndex B S hS X V) (moduleSetSheaf B S hS X M) _) ?_
  refine Eq.trans (congrArg
    ((chartProjection B S hS (𝟙 X) V (idIndex B S hS X V)).app
      (moduleSetSheaf B S hS X M)) ?_)
    (chartProjection_idIndex_smallEtaleDirectImageRanIdIso_inv B S hS X
      (moduleSetSheaf B S hS X M) V s)
  refine Eq.trans (congrArg
    (((smallEtaleDirectImageRanIso B S hS (𝟙 X)).hom.app
      (moduleSetSheaf B S hS X M)).hom.app (op V))
    ((modulePushforwardIdIso_inv_app_val_app_apply B S hS X M (op V) s).trans
      (smallEtaleDirectImageIdIso_inv_app_apply B S hS X
        (moduleSetSheaf B S hS X M) V s))) ?_
  exact Sheaf.hom_congr_app_apply
    (Iso.inv_hom_id_app (smallEtaleDirectImageRanIso B S hS (𝟙 X))
      (moduleSetSheaf B S hS X M)) (op V) _

/-- **The chart component of the comparison of direct images of modules along an identity, at
the chart diagram with identity vertical morphism, undoes it.**  The chart component is by
definition the chart projection at the index of the diagram, which is the index of
`AlgebraicGeometry.Space.chartBaseChangeMap_id`. -/
theorem modulePushforwardCounitApp_idDiagram_modulePushforwardIdIso_inv_app
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (s : M.val.obj (op V)) :
    modulePushforwardCounitApp B S hS (𝟙 X) M (idDiagram B S hS X V)
        (((modulePushforwardIdIso B S hS X).inv.app M).val.app (op V) s) = s := by
  refine Eq.trans (moduleChartProjection_app B S hS (𝟙 X) V
    (indexOfChartDiagram B S hS (𝟙 X) (idDiagram B S hS X V))
    (moduleSetSheaf B S hS X M) _) ?_
  refine Eq.trans (eq_of_heq (ranChartCone_π_congr B S hS X
    (moduleSetSheaf B S hS X M).obj (chartBaseChange B S hS (𝟙 X) V)
    (indexOfChartDiagram_idDiagram B S hS X V) _)) ?_
  refine Eq.trans (moduleChartProjection_app B S hS (𝟙 X) V (idIndex B S hS X V)
    (moduleSetSheaf B S hS X M) _).symm ?_
  exact moduleChartProjection_idIndex_modulePushforwardIdIso_inv_app B S hS X M V s

/-- **The chart component of the comparison of direct images of modules along an identity is
restriction along the diagram.**  A chart diagram over `𝟙 X` is a morphism of étale charts of
`X`, and `AlgebraicGeometry.Space.modulePushforwardCounitApp_naturality` — the compatibility of
the chart component with restriction of both charts — carries the diagram at a single chart to
an arbitrary one along exactly that morphism. -/
theorem modulePushforwardCounitApp_modulePushforwardIdIso_inv_app
    (M : Modules.{u, u} B S hS X.1 X.2) (e : ChartDiagram B S hS X.1 X.1 (𝟙 X.1))
    (s : M.val.obj (op e.V)) :
    modulePushforwardCounitApp B S hS (𝟙 X) M e
        (((modulePushforwardIdIso B S hS X).inv.app M).val.app (op e.V) s)
      = M.val.map (chartMapOfIdChartDiagram B S hS X e).op s := by
  have h1 : (SmallEtale.toOver B S hS X.1).map (chartMapOfIdChartDiagram B S hS X e) ≫
        (idDiagram B S hS X e.V).g =
      (SmallEtale.toOver B S hS X.1).map (chartMapOfIdChartDiagram B S hS X e) :=
    (congrArg (fun m : (SmallEtale.toOver B S hS X.1).obj e.V ⟶
          (SmallEtale.toOver B S hS X.1).obj e.V ↦
        (SmallEtale.toOver B S hS X.1).map (chartMapOfIdChartDiagram B S hS X e) ≫ m)
      (idDiagram_g B S hS X e.V)).trans (Category.comp_id _)
  have h2 : e.g ≫ (SmallEtale.toOver B S hS X.1).map (𝟙 e.V) = e.g :=
    (congrArg (fun m ↦ e.g ≫ m)
        (CategoryTheory.Functor.map_id (SmallEtale.toOver B S hS X.1) e.V)).trans
      (Category.comp_id e.g)
  have hcond := h1.trans ((toOver_map_chartMapOfIdChartDiagram B S hS X e).trans h2.symm)
  have hnat := modulePushforwardCounitApp_naturality B S hS (𝟙 X) M
    (idDiagram B S hS X e.V) e (chartMapOfIdChartDiagram B S hS X e) (𝟙 e.V) hcond
    (((modulePushforwardIdIso B S hS X).inv.app M).val.app (op e.V) s)
  refine Eq.trans (Eq.trans (congrArg (modulePushforwardCounitApp B S hS (𝟙 X) M e)
    (congrArg (fun k ↦ (ConcreteCategory.hom k)
        (((modulePushforwardIdIso B S hS X).inv.app M).val.app (op e.V) s))
      (((modulePushforward B S hS (𝟙 X)).obj M).val.map_id (op e.V))).symm) hnat) ?_
  exact congrArg (fun z ↦ M.val.map (chartMapOfIdChartDiagram B S hS X e).op z)
    (modulePushforwardCounitApp_idDiagram_modulePushforwardIdIso_inv_app B S hS X M e.V s)

/-- **The chart section of an inverse image along an identity is restriction along the
diagram.**  A chart diagram `e` over `𝟙 X` is a morphism of étale charts of `X`
(`AlgebraicGeometry.Space.chartMapOfIdChartDiagram`), and the unit law `(𝟙 X)^* ≅ 𝟭` of
Stacks 03LU carries the chart section of a section `s` along `𝟙 X` to the restriction of `s`
along that morphism of charts.

This is the identity coherence of `AlgebraicGeometry.Space.modulePullbackChartSection`.  The
comparison of inverse images is moved out of the chart component by
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`, which replaces it by its adjoint
transpose; that transpose is the inverse of the comparison of direct images by
`AlgebraicGeometry.Space.homEquiv_modulePullbackIdIso_hom_app`; and its chart component is
restriction along the diagram by
`AlgebraicGeometry.Space.modulePushforwardCounitApp_modulePushforwardIdIso_inv_app`. -/
theorem modulePullbackIdIso_hom_app_val_app_modulePullbackChartSection
    (M : Modules.{u, u} B S hS X.1 X.2) (e : ChartDiagram B S hS X.1 X.1 (𝟙 X.1))
    (s : M.val.obj (op e.V)) :
    ((modulePullbackIdIso B S hS X).hom.app M).val.app (op e.U)
        (modulePullbackChartSection B S hS (𝟙 X) M e s)
      = M.val.map (chartMapOfIdChartDiagram B S hS X e).op s := by
  refine Eq.trans (congrArg
      (fun z ↦ ((modulePullbackIdIso B S hS X).hom.app M).val.app (op e.U) z)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (𝟙 X) M e s).symm) ?_
  refine Eq.trans (modulePullbackHomFMap_app B S hS (𝟙 X) M M
    ((modulePullbackIdIso B S hS X).hom.app M) e s).symm ?_
  refine Eq.trans (congrArg
    (fun m : M ⟶ (modulePushforward B S hS (𝟙 X)).obj M ↦
      modulePushforwardCounitApp B S hS (𝟙 X) M e (m.val.app (op e.V) s))
    (homEquiv_modulePullbackIdIso_hom_app B S hS X M)) ?_
  exact modulePushforwardCounitApp_modulePushforwardIdIso_inv_app B S hS X M e s

end Identity

/-! ### The composition law for the chart components of the direct image -/

/-! ### The residue: one step of spelling, and nothing else -/

/-- **The residue of the composite coherence of
`AlgebraicGeometry.Space.modulePullbackChartSection`.**

For `f : X ⟶ Y` and `g : Y ⟶ Z`, a chart diagram over `f` and one over `g` sharing their middle
chart, and a section `s` of an `𝒪_Z`-module `M` over the top chart: the composite of the two
chart components of the direct images, applied to the iterated adjoint transpose of the
comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU, is the chart component of the unit of the
adjunction for `f ≫ g`, that is the unit section at the composed chart diagram.

**Both halves of this are theorems of this file.**
`AlgebraicGeometry.Space.modulePushforwardCounitApp_smallToposMorphismTypeU_comp` says the
composite of the two chart components is the chart component along `f ≫ g` after the geometric
comparison of Stacks 03G2, part (3); and
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_hom_app_homEquiv` says that geometric
comparison carries the iterated transpose to the unit.  What is missing is only the step
joining them, which is a `congrArg` under the chart component — mathematically the congruence
of a function under an equality of its argument, and nothing more.

It is not available because the two sides of that equality are presented at the two spellings of
the sections of `(f ≫ g)_*`: the direct image of the underlying sheaf of sets, and the
underlying sheaf of the direct image of modules.  The two are the same type, and the repository
identifies them wherever a *statement* needs it (that is what
`AlgebraicGeometry.Space.counitSetFMap_app_eq` and
`modulePushforwardCounitApp_smallToposMorphismTypeU_comp` each pay once); what does not
terminate is deciding the identification while *also* unfolding a chart component applied to the
term.  Every route below fails at the default heartbeat budget:

* `congrArg` of the chart component, with the equation at the set spelling —
  `(deterministic) timeout at isDefEq`;
* the same with the equation re-read at the module spelling by a `show` ascription, as
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app'` does —
  `(deterministic) timeout at whnf`;
* writing the composite of the two chart components out as the right-hand side of a lemma of
  its own, so that the match is syntactic — `(deterministic) timeout at whnf` on that match,
  although the same step with the right-hand side left to unification goes through;
* the same again with the `congrArg` given an explicitly typed binder, and placed in a
  declaration of its own so that it has the whole budget — `(deterministic) timeout at whnf`;
* `rw` with either form — `Tactic rewrite failed: Did not find an occurrence of the pattern`,
  the pattern and the target differing only in that presentation;
* routing through `AlgebraicGeometry.Space.modulePushforwardCompIso` rather than the geometric
  comparison, so that no spelling changes — `(deterministic) timeout at whnf` on the chart
  component applied to a section of that comparison.

**Two of those failures need qualification, and the qualification is the useful part.**
The last of them is not absolute: the chart component along `f ≫ g` at a composed chart
diagram *can* be applied to a section of `modulePushforwardCompIso`, and the congruence under it
*is* available — but only in one shape, namely a lemma of its own whose equation of sections is a
**hypothesis** at the module spelling and whose two sections are variables.  In that shape
`congrArg` goes through and composes with
`modulePushforwardCounitApp_smallToposMorphismTypeU_comp`; what a raw `congrArg` cannot do, and
what the first four failures are really about, is the higher-order match against a goal whose
argument is a *set*-spelled term, or a `congrArg` of the `Eq.trans` of two equations.

What these routes show is a budget law rather than a single bad step: **one declaration
affords one identification between the two spellings, and nothing else in the same declaration.**
Splitting the composite coherence so that every step is at a variable morphism and a variable
section — which is the discipline the implementation notes below prescribe — reduces it to a
chain of eight steps of which seven elaborate; the eighth is the one that joins the chart
components to either input, and no arrangement of declarations was found that affords it.

**The budget law is sharper than that, and the sharpening locates the obstruction.**  The
identification can be tested on its own, by restating
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_hom_app_homEquiv` — an equation whose two
sides are the two spellings — twice over, verbatim:

* at an **abstract** chart, `(Wop : (SmallEtale B S hS Z.1)ᵒᵖ)`, the restatement elaborates with
  the budget barely touched;
* at the **concrete** chart `op W` of the composed chart diagram, the same restatement, proved
  from the abstract one, is `(deterministic) timeout at whnf`.

So the obstruction is not which lemmas are available.  It is that *instantiating any statement
which crosses the two spellings at a concrete chart* costs on the order of a whole declaration's
budget, because `op W` is a constructor application and the two sides can then be unfolded,
whereas a variable `Wop` leaves nothing to unfold and the identification is decided
structurally.  Four further arrangements confirm that reading, and each puts two
such instantiations in one declaration:

* the congruence under the chart component at the module spelling, with the two sections
  **variables**, does elaborate — that shape is available, as the refinement above says — but
  composing it with `modulePushforwardCounitApp_smallToposMorphismTypeU_comp` by `Eq.trans` does
  not: the two spellings of the shared middle term, each elaborated in its own declaration, are
  not syntactically equal, and `rw` with either reports `Did not find an occurrence of the
  pattern` on terms that print identically;
* re-orienting that equation so the module-spelled side is elaborated first, which puts the
  `Eq`'s type at the module spelling and makes the consumer's `congrArg` syntactic in principle,
  moves the timeout but does not remove it;
* giving the equation as a **hypothesis** of the consumer makes the consumer elaborate, which
  locates the whole remaining cost in producing that hypothesis at the
  concrete chart — which is the concrete restatement above, shown to be unaffordable;
* the unit section *is* the chart component at the unit of the adjunction by `rfl`
  (`AlgebraicGeometry.Space.modulePullbackUnitSection` unfolds to it at the composed diagram),
  so that half of the coherence costs nothing and is not where the budget goes.

**The refactor the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackCompCorrespondence.lean` name is
not a fix for this.**  Those notes ask for
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` to become a componentwise
natural isomorphism rather than an equality of functors, and they are right about what they are
about: the obstruction *there* is that `eqToHom` of that equality cannot be reduced, which is
what blocks carrying the associativity cocycle across to
`AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`.  The identification at issue *here* is
between the types

`((modulePushforward B S hS (f ≫ g)).obj F).val.obj Wop`  and
`((smallEtaleDirectImage B S hS (f ≫ g)).obj (moduleSetSheaf B S hS X F)).obj.obj Wop`,

and `Stacks.Sheaves.RingedToposModules.pushforwardModules` occurs in neither, so making its
comparison an isomorphism cannot make them syntactically equal.  The second half of that
prescription is a no-op outright: `AlgebraicGeometry.Space.Modules` is *already* declared over
this ring sheaf — it is `SheafOfModules.{m} (RingedSite.ringSheaf (smallEtaleRingedSite …))` and
`AlgebraicGeometry.Space.structureRingSheaf` is a reducible abbreviation for exactly that ring
sheaf, so the two spellings of the category are already interchangeable by unfolding.

What would remove this obstruction is therefore not that refactor but one of: a shape in which
the chart component of the direct image is declared at a single spelling of its argument, so
that no consumer ever crosses (this moves the cost to every consumer of
`AlgebraicGeometry.Space.modulePushforwardCounitApp`, of which there are many); or a statement of
the composite coherence quantified over the chart in opposite
form, so that the crossing is never instantiated at a constructor application. -/
def ModulePushforwardChartComponentCompResidue : Prop :=
  ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (s : M.val.obj (op W)),
    modulePushforwardCounitApp B S hS f ((modulePullback B S hS (f ≫ g)).obj M)
        ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g
          ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
          ⟨V, W, b, hb⟩ (((modulePullbackAdjunction B S hS g).homEquiv M
            ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
            ((modulePullbackAdjunction B S hS f).homEquiv
              ((modulePullback B S hS g).obj M) ((modulePullback B S hS (f ≫ g)).obj M)
              ((modulePullbackCompIso B S hS f g).hom.app M))).val.app (op W) s)) =
      modulePullbackUnitSection B S hS (f ≫ g) M
        (ChartDiagram.comp B S hS f g a b ha hb) s

section Composite

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The `f`-map of sheaves of sets whose components are the chart components of the direct
image: the one the chart correspondence of Stacks 03G4 attaches to the identity of the direct
image. -/
private def counitSetFMap (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    FMap B S hS X.1 Y.1 f.hom P.obj ((smallEtaleDirectImage B S hS f).obj P).obj :=
  ranFmap B S hS f P ((smallEtaleDirectImage B S hS f).obj P)
    ((smallEtaleDirectImageRanIso B S hS f).hom.app P)

/-- The chart correspondence of Stacks 03G4 carries the chart components of the direct image to
the identity of the direct image: they are its value there. -/
private theorem fmapDirectImageEquiv_counitSetFMap
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    fmapDirectImageEquiv B S hS f P ((smallEtaleDirectImage B S hS f).obj P)
        (counitSetFMap B S hS f P) =
      𝟙 ((smallEtaleDirectImage B S hS f).obj P) :=
  (congrArg (fmapDirectImageEquiv B S hS f P ((smallEtaleDirectImage B S hS f).obj P))
      (congrArg (ranFmap B S hS f P ((smallEtaleDirectImage B S hS f).obj P))
        (Category.id_comp ((smallEtaleDirectImageRanIso B S hS f).hom.app P)).symm)).trans
    ((fmapDirectImageEquiv B S hS f P
      ((smallEtaleDirectImage B S hS f).obj P)).apply_symm_apply _)

/-- The chart components of the direct image are the components of
`AlgebraicGeometry.Space.counitSetFMap`.  This is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_eq`, the identification of the chart
component with the chart projection of the Kan-extension comparison. -/
private theorem counitSetFMap_app_eq (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    (counitSetFMap B S hS f (moduleSetSheaf B S hS X F)).app d x =
      modulePushforwardCounitApp B S hS f F d x :=
  (modulePushforwardCounitApp_eq B S hS f F d x).symm

/-- The `f ≫ g`-map of sheaves of sets which the chart correspondence of Stacks 03G4 attaches
to the geometric comparison of Stacks 03G2, part (3). -/
private def compSetFMap (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    FMap B S hS X.1 Z.1 (f ≫ g).hom P.obj
      ((smallEtaleDirectImage B S hS g).obj
        ((smallEtaleDirectImage B S hS f).obj P)).obj :=
  (fmapDirectImageEquiv B S hS (f ≫ g) P
      ((smallEtaleDirectImage B S hS g).obj
        ((smallEtaleDirectImage B S hS f).obj P))).symm
    ((smallToposMorphismTypeU_comp B S hS f g).hom.app P)

/-- **`AlgebraicGeometry.Space.compSetFMap` is the composite of the two chart components.**  By
`AlgebraicGeometry.Space.FMap.comp_unique` a composite of `f`-maps is the only one whose
homomorphism into the direct image is the composite of the two homomorphisms with the geometric
comparison, and here each of the two factors contributes an identity. -/
private theorem compSetFMap_eq_comp (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    compSetFMap B S hS f g P =
      FMap.comp B S hS f g P ((smallEtaleDirectImage B S hS f).obj P)
        ((smallEtaleDirectImage B S hS g).obj
          ((smallEtaleDirectImage B S hS f).obj P))
        (counitSetFMap B S hS g ((smallEtaleDirectImage B S hS f).obj P))
        (counitSetFMap B S hS f P) := by
  refine FMap.comp_unique B S hS f g P _ _ _ _ _
    (((fmapDirectImageEquiv B S hS (f ≫ g) P _).apply_symm_apply
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app P)).trans ?_)
  rw [fmapDirectImageEquiv_counitSetFMap, fmapDirectImageEquiv_counitSetFMap,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.id_comp ((smallToposMorphismTypeU_comp B S hS f g).hom.app P)).symm

/-- The geometric comparison of Stacks 03G2, part (3), followed by a chart component of the
direct image along the composite, is a component of `AlgebraicGeometry.Space.compSetFMap`.
This is the definition of that `f ≫ g`-map: the chart correspondence is composition with the
chart projection. -/
private theorem counitSetFMap_comp_apply
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom)
    (y : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS f).obj P)).obj.obj (op d.V)) :
    (counitSetFMap B S hS (f ≫ g) P).app d
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app P).hom.app (op d.V) y) =
      (compSetFMap B S hS f g P).app d y :=
  rfl

/-- **The iterated adjoint transpose of the comparison of inverse images is the unit of the
adjunction for the composite**, up to the comparison of direct images.  This is
`AlgebraicGeometry.Space.homEquiv_modulePullbackCompIso_inv_app_comp` at the comparison itself,
where the two halves of the isomorphism cancel and the transpose of an identity is the unit. -/
theorem homEquiv_comp_modulePushforwardCompIso_hom_app
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackAdjunction B S hS g).homEquiv M
          ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
          ((modulePullbackAdjunction B S hS f).homEquiv
            ((modulePullback B S hS g).obj M) ((modulePullback B S hS (f ≫ g)).obj M)
            ((modulePullbackCompIso B S hS f g).hom.app M)) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS (f ≫ g)).obj M) =
      (modulePullbackAdjunction B S hS (f ≫ g)).unit.app M := by
  refine (homEquiv_modulePullbackCompIso_inv_app_comp B S hS f g M
    ((modulePullback B S hS (f ≫ g)).obj M)
    ((modulePullbackCompIso B S hS f g).hom.app M)).symm.trans ?_
  rw [Iso.inv_hom_id_app, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact Category.comp_id ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M)

/-- The iterated adjoint transpose of the comparison of inverse images, followed by the
comparison of direct images, is the unit of the adjunction for `f ≫ g` — on a section.  This is
`AlgebraicGeometry.Space.homEquiv_comp_modulePushforwardCompIso_hom_app` read through
`AlgebraicGeometry.Space.comp_val_app_apply`, in its own declaration so that the composite is
split once. -/
private theorem modulePushforwardCompIso_hom_app_val_app_homEquiv
    (M : Modules.{u, u} B S hS Z.1 Z.2) (Wop : (SmallEtale B S hS Z.1)ᵒᵖ)
    (s : M.val.obj Wop) :
    ((modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS (f ≫ g)).obj M)).val.app Wop
        (((modulePullbackAdjunction B S hS g).homEquiv M
          ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
          ((modulePullbackAdjunction B S hS f).homEquiv
            ((modulePullback B S hS g).obj M) ((modulePullback B S hS (f ≫ g)).obj M)
            ((modulePullbackCompIso B S hS f g).hom.app M))).val.app Wop s) =
      ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M).val.app Wop s :=
  (comp_val_app_apply B S hS
      ((modulePullbackAdjunction B S hS g).homEquiv M
        ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
        ((modulePullbackAdjunction B S hS f).homEquiv
          ((modulePullback B S hS g).obj M) ((modulePullback B S hS (f ≫ g)).obj M)
          ((modulePullbackCompIso B S hS f g).hom.app M)))
      ((modulePushforwardCompIso B S hS f g).hom.app
        ((modulePullback B S hS (f ≫ g)).obj M)) Wop s).symm.trans
    (congrArg
      (fun m : M ⟶ (modulePushforward B S hS (f ≫ g)).obj
          ((modulePullback B S hS (f ≫ g)).obj M) ↦ m.val.app Wop s)
      (homEquiv_comp_modulePushforwardCompIso_hom_app B S hS f g M))

/-- **The geometric comparison of Stacks 03G2, part (3), on the iterated adjoint transpose of
the comparison of inverse images, is the unit of the adjunction for `f ≫ g`.**  This is
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app_homEquiv` with the comparison
of direct images of modules replaced by the geometric one.

It is stated in this form, and the composition law of the chart component is consumed in the
form carrying the geometric comparison, because the comparison of direct images of *modules*
cannot be put under a chart component: elaborating
`modulePushforwardCounitApp … (((modulePushforwardCompIso …).hom.app _).val.app _ z)` exhausts
the `whnf` budget, which is the divergence the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` record for the
`eqToIso` factors of that comparison.  Here the comparison of modules occurs only inside the
two lemmas above, each of which elaborates on its own. -/
theorem smallToposMorphismTypeU_comp_hom_app_homEquiv
    (M : Modules.{u, u} B S hS Z.1 Z.2) (Wop : (SmallEtale B S hS Z.1)ᵒᵖ)
    (s : M.val.obj Wop) :
    ((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X ((modulePullback B S hS (f ≫ g)).obj M))).hom.app Wop
        (((modulePullbackAdjunction B S hS g).homEquiv M
            ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
            ((modulePullbackAdjunction B S hS f).homEquiv
              ((modulePullback B S hS g).obj M) ((modulePullback B S hS (f ≫ g)).obj M)
              ((modulePullbackCompIso B S hS f g).hom.app M))).val.app Wop s) =
      ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M).val.app Wop s :=
  (modulePushforwardCompIso_hom_app_val_app B S hS f g
      ((modulePullback B S hS (f ≫ g)).obj M) Wop
      (((modulePullbackAdjunction B S hS g).homEquiv M
            ((modulePushforward B S hS f).obj ((modulePullback B S hS (f ≫ g)).obj M))
            ((modulePullbackAdjunction B S hS f).homEquiv
              ((modulePullback B S hS g).obj M) ((modulePullback B S hS (f ≫ g)).obj M)
              ((modulePullbackCompIso B S hS f g).hom.app M))).val.app Wop s)).symm.trans
    (modulePushforwardCompIso_hom_app_val_app_homEquiv B S hS f g M Wop s)

section Factor

variable {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- **The chart formula for `AlgebraicGeometry.Space.compSetFMap`.**  On a chart diagram over
`f ≫ g` which factors through an étale scheme chart of `Y`, it is the composite of the two
chart components.  This is `AlgebraicGeometry.Space.FMap.comp_app`. -/
private theorem compSetFMap_app (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (s : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS f).obj P)).obj.obj (op W)) :
    (compSetFMap B S hS f g P).app (ChartDiagram.comp B S hS f g a b ha hb) s =
      (counitSetFMap B S hS f P).app ⟨U, V, a, ha⟩
        ((counitSetFMap B S hS g ((smallEtaleDirectImage B S hS f).obj P)).app
          ⟨V, W, b, hb⟩ s) :=
  (congrArg
      (fun θ : FMap B S hS X.1 Z.1 (f ≫ g).hom P.obj
          ((smallEtaleDirectImage B S hS g).obj
            ((smallEtaleDirectImage B S hS f).obj P)).obj ↦
        θ.app (ChartDiagram.comp B S hS f g a b ha hb) s)
      (compSetFMap_eq_comp B S hS f g P)).trans
    (FMap.comp_app B S hS f g a b ha hb P _ _ _ _ s)

/-- **The set-level composition law of the chart components of the direct image.**  On a chart
diagram over `f ≫ g` which factors through an étale scheme chart of `Y`, the geometric
comparison of Stacks 03G2, part (3), followed by the chart component along `f ≫ g`, is the
composite of the two chart components. -/
private theorem counitSetFMap_smallToposMorphismTypeU_comp
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (s : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS f).obj P)).obj.obj (op W)) :
    (counitSetFMap B S hS (f ≫ g) P).app (ChartDiagram.comp B S hS f g a b ha hb)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app P).hom.app (op W) s) =
      (counitSetFMap B S hS f P).app ⟨U, V, a, ha⟩
        ((counitSetFMap B S hS g ((smallEtaleDirectImage B S hS f).obj P)).app
          ⟨V, W, b, hb⟩ s) :=
  (counitSetFMap_comp_apply B S hS f g P (ChartDiagram.comp B S hS f g a b ha hb) s).trans
    (compSetFMap_app B S hS f g a b ha hb P s)

/-- **The chart component of the geometric comparison of Stacks 03G2, part (3), is the composite
of the two chart components of the direct images of modules.** -/
theorem modulePushforwardCounitApp_smallToposMorphismTypeU_comp
    (F : Modules.{u, u} B S hS X.1 X.2)
    (y : ((modulePushforward B S hS g).obj
      ((modulePushforward B S hS f).obj F)).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) F (ChartDiagram.comp B S hS f g a b ha hb)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X F)).hom.app (op W) y) =
      modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj F)
          ⟨V, W, b, hb⟩ y) := by
  refine Eq.trans (counitSetFMap_app_eq B S hS (f ≫ g) F
    (ChartDiagram.comp B S hS f g a b ha hb) _).symm ?_
  refine Eq.trans (counitSetFMap_smallToposMorphismTypeU_comp B S hS f g a b ha hb
    (moduleSetSheaf B S hS X F) y) ?_
  refine Eq.trans (counitSetFMap_app_eq B S hS f F ⟨U, V, a, ha⟩ _) ?_
  exact congrArg (modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩)
    (counitSetFMap_app_eq B S hS g ((modulePushforward B S hS f).obj F) ⟨V, W, b, hb⟩ y)

/-! ### The composite law for the chart section of an inverse image -/

/-- Both chart sections of the composite, in the transported spelling.  Split off so that the
two applications of
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection` are paid in
their own declaration. -/
theorem modulePullbackChartSection_comp_eq_unitSection
    (M : Modules.{u, u} B S hS Z.1 Z.2) (s : M.val.obj (op W)) :
    modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
        (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s) =
      modulePullbackUnitSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
        (modulePullbackUnitSection B S hS g M ⟨V, W, b, hb⟩ s) :=
  (congrArg
        (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩)
        (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M
          ⟨V, W, b, hb⟩ s).symm).trans
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f
      ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩ _).symm

end Factor

end Composite

end AlgebraicGeometry.Space

end
