module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicAffineOpenSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicDenseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions

/-!
# A rational function is a meromorphic function

Let `X` be an algebraic space over a scheme `S` satisfying the three hypotheses of Stacks
0ENA — every weakly associated point has codimension `0`, the irreducible components are
locally finite, and the codimension-zero points are representable by monomorphisms from
fields — and let `P` be a presentation of its schematic locus at the codimension-zero points.

This file builds the canonical ring homomorphism

`R(X) ⟶ Γ(X, 𝒦_X)`

from the rational functions of Stacks 0EMP to the meromorphic functions, and proves that it is
**injective**.

The construction rests on one observation: every dense open subspace of `X` contains a *generic
chart* for `P` in the sense of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.IsGenericChart`, namely a dense Zariski
open of the chart presenting the schematic locus.  A meromorphic function is determined by, and
may be prescribed as, its value at such a chart, so a rational function represented by a
morphism `ν` on a dense open subspace `W` is sent to the unique meromorphic function whose
value at a generic chart `C` inside `W` is the image in `𝒦_X(C)` of the coordinate of `ν`
at `C`.

## Main definitions

* `AlgebraicGeometry.Space.GenericChartIn` is a generic chart together with a factorization of
  its structure morphism through a given subfunctor of `X`, and
  `AlgebraicGeometry.Space.chosenGenericChart` is a choice of one inside a dense open subspace.
* `AlgebraicGeometry.Space.chartCoord` is the coordinate, at an étale chart lying in a
  subfunctor `W`, of a morphism from `W` to the relative affine line.
* `AlgebraicGeometry.Space.chartToMeromorphic` is the component at an étale chart of the
  canonical map `𝒪_X ⟶ 𝒦_X`.
* `AlgebraicGeometry.Space.meromorphicOfPartial` is the meromorphic function attached to a
  partial map to the relative affine line, `AlgebraicGeometry.Space.rationalToMeromorphic` the
  induced map on the quotient, and
  `AlgebraicGeometry.Space.rationalToMeromorphicRingHom` that map as a ring homomorphism.

## Main results

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.isGenericChart_openChart_schematicChart`:
  a dense Zariski open of the chart presenting the schematic locus is a generic chart.
* `AlgebraicGeometry.Space.nonempty_genericChartIn` and
  `AlgebraicGeometry.Space.exists_isGenericChart_factoring`: every dense open subspace contains
  a generic chart.
* `AlgebraicGeometry.Space.meromorphicOfPartial_val` and
  `AlgebraicGeometry.Space.rationalToMeromorphic_val`: the value of the attached meromorphic
  function at *every* étale chart lying in the domain is the coordinate of the representative
  there.
* `AlgebraicGeometry.Space.injective_rationalToMeromorphic`: the canonical map from the rational
  functions to the meromorphic functions is injective.

## Implementation notes

The data produced by shrinking a chart into a dense open subspace is packaged as the structure
`AlgebraicGeometry.Space.GenericChartIn` rather than returned as an iterated existential: the
construction of `AlgebraicGeometry.Space.meromorphicOfPartial` has to *choose* that data and
then refer to four of its components, which through `Exists.choose` would mean four nested
`choose_spec` projections at every use.  The existential form is recorded as
`AlgebraicGeometry.Space.exists_isGenericChart_factoring`.  The structure carries two properties
beyond being a generic chart — that the structure morphism is an open immersion and that its
point set is dense — because both come out of the construction and both are needed for
injectivity, where the subfunctor cut out by the chart has to be exhibited as a dense open
subspace.

`AlgebraicGeometry.Space.chartCoord` does not take the factorization equation as an argument,
only the factorizing morphism: the coordinate makes sense without it, and the equation is what
makes the morphism *unique*, by `AlgebraicGeometry.Space.factor_unique`.  That uniqueness is the
engine of `AlgebraicGeometry.Space.val_eq_chartCoord`: the two ways of mapping `U ×_X C` into
the domain — through `U` and through the generic chart `C` — agree because the inclusion of the
domain is a monomorphism, which is why the value at an arbitrary chart `U` is forced by the
value at `C`.

The ring structure on `AlgebraicGeometry.Space.rationalFunctions` is available only through the
characterization `AlgebraicGeometry.Space.rationalFunctionsRing`, which for representatives on
a common dense open subspace supplies a representative of the sum and of the product whose
coordinates are the pointwise sum and product.  The ring axioms are therefore checked by
comparing the two sides at a single generic chart, where
`AlgebraicGeometry.Space.CodimensionZeroPresentation.IsGenericChart.bijective_val_genericChart`
makes that comparison faithful.  Note that the instance on
`AlgebraicGeometry.Space.rationalFunctions` *is* the ring produced by that characterization, so
its `Exists.choose_spec` does speak about the instance; even so each ring axiom first transports
its statement to an explicit representative and only then rewrites, so that the operations
coming from `choose_spec` are never matched syntactically against the ones in the goal.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0EMM](https://stacks.math.columbia.edu/tag/0EMM)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Zariski opens of an open immersion chart -/

/-- The inclusion of a Zariski open of an object of the big fppf site of `S` is an open
immersion of presheaves. -/
theorem isOpenImmersion_yoneda_map_openSubHom (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    IsOpenImmersion B S hS (yoneda.map (openSubHom A O)) := by
  refine presheaf_yoneda_map_of_inverseImage B S hS inferInstance (openSubHom A O) ?_
  rw [toScheme_map_openSubHom]
  exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion O.ι)

/-- A Zariski-open chart of an open immersion chart is again an open immersion chart. -/
theorem isOpenImmersion_openChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (C : SmallEtale B S hS F) (hC : IsOpenImmersion B S hS C.1.hom)
    (O : (chartScheme C).Opens) :
    IsOpenImmersion B S hS (openChart B S hS F C O).1.hom := by
  show IsOpenImmersion B S hS (yoneda.map (openSubHom C.obj.left O) ≫ C.1.hom)
  exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_yoneda_map_openSubHom _ O) hC

namespace CodimensionZeroPresentation

/-! ### The schematic chart is dense and an open immersion -/

section Schematic

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : CodimensionZeroPresentation B S hS X)

/-- The point set of the chart presenting the dense open subspace is dense. -/
theorem denseRange_pointsMap_chart :
    DenseRange (pointsMap B S hS (yoneda.obj P.scheme) P.chart) := by
  show Dense (Set.range (pointsMap B S hS (yoneda.obj P.scheme) P.chart))
  rw [show pointsMap B S hS (yoneda.obj P.scheme) P.chart =
      pointsMap B S hS P.sub.toFunctor P.sub.ι ∘
        pointsMap B S hS (yoneda.obj P.scheme) P.iso.hom from
    pointsMap_comp B S hS (yoneda.obj P.scheme) P.iso.hom P.sub.ι,
    Set.range_comp, (pointsMap_surjective_of_isIso B S hS P.iso.hom).range_eq, Set.image_univ]
  exact P.denseRange

/-- The structure morphism of the schematic chart is an open immersion. -/
theorem isOpenImmersion_schematicChart : IsOpenImmersion B S hS (P.schematicChart).1.hom := by
  rw [schematicChart_hom]
  exact P.presheaf_isOpenImmersion_chart

/-- The point set of the schematic chart is dense. -/
theorem denseRange_pointsMap_schematicChart :
    DenseRange (pointsMap B S hS (yoneda.obj (P.schematicChart).obj.left)
      (P.schematicChart).1.hom) :=
  P.denseRange_pointsMap_chart

end Schematic

/-! ### Dense Zariski opens of the schematic chart are generic charts -/

section Generic

variable {X : AlgebraicSpaces B S hS} (P : CodimensionZeroPresentation B S hS X.1)

/-- **A dense Zariski open of the schematic chart is a generic chart.** -/
theorem isGenericChart_openChart_schematicChart
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (Ω : (chartScheme P.schematicChart).Opens)
    (hΩ : Dense (Ω : Set (chartScheme P.schematicChart))) :
    P.IsGenericChart (openChart B S hS X.1 P.schematicChart Ω) := by
  set C := openChart B S hS X.1 P.schematicChart Ω with hC
  have hOI : IsOpenImmersion B S hS C.1.hom :=
    isOpenImmersion_openChart P.schematicChart P.isOpenImmersion_schematicChart Ω
  have hdense : DenseRange (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) :=
    denseRange_pointsMap_openChart P.schematicChart P.denseRange_pointsMap_schematicChart Ω hΩ
  have hdense' :
      Dense (Set.range (pointsMap B S hS (chartRange C).toFunctor (chartRange C).ι)) := by
    rw [range_pointsMap_ι_chartRange C hOI]
    exact hdense
  refine ⟨mono_of_presheaf_isOpenImmersion hOI, fun y hy => ?_⟩
  refine exists_hom_of_range_pointsMap_subset C hOI (P.fromSpecStalk hy) ?_
  rintro _ ⟨w, rfl⟩
  rw [P.pointsMap_fromSpecStalk hy X.2 w, ← range_pointsMap_ι_chartRange C hOI]
  exact mem_range_pointsMap_ι_of_localRingDimension_eq_zero B S hS X.2 hfin
    (isOpenSubspace_chartRange C hOI) hdense' y hy

end Generic

end CodimensionZeroPresentation

/-! ### Generic charts inside a dense open subspace -/

variable {X : AlgebraicSpaces B S hS}

/-- **A generic chart contained in a dense open subspace.**  The data of a generic chart for a
presentation `P` of the schematic locus at the codimension-zero points, together with a
factorization of its structure morphism through a given subfunctor of `X`. -/
structure GenericChartIn (P : CodimensionZeroPresentation B S hS X.1) (W : Subfunctor X.1) where
  /-- The underlying étale chart. -/
  chart : SmallEtale B S hS X.1
  /-- It is a generic chart for the presentation. -/
  isGenericChart : P.IsGenericChart chart
  /-- Its structure morphism is an open immersion. -/
  isOpenImmersion : IsOpenImmersion B S hS chart.1.hom
  /-- Its point set is dense. -/
  denseRange : DenseRange (pointsMap B S hS (yoneda.obj chart.obj.left) chart.1.hom)
  /-- The factorization of its structure morphism through the subfunctor. -/
  factor : yoneda.obj chart.obj.left ⟶ W.toFunctor
  /-- The factorization does factor the structure morphism. -/
  factor_comp : factor ≫ W.ι = chart.1.hom

/-- **Every dense open subspace contains a generic chart.** -/
theorem nonempty_genericChartIn (P : CodimensionZeroPresentation B S hS X.1)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) {W : Subfunctor X.1}
    (hW : IsDenseOpenSubspace B S hS X.2 W) : Nonempty (GenericChartIn P W) := by
  obtain ⟨Ω, hΩ, τ, hτ⟩ := exists_dense_open_le_of_isDenseOpenSubspace P.schematicChart
    P.isOpenImmersion_schematicChart P.denseRange_pointsMap_schematicChart hW.1 hW.2
  exact ⟨⟨openChart B S hS X.1 P.schematicChart Ω,
    P.isGenericChart_openChart_schematicChart hfin Ω hΩ,
    isOpenImmersion_openChart P.schematicChart P.isOpenImmersion_schematicChart Ω,
    denseRange_pointsMap_openChart P.schematicChart P.denseRange_pointsMap_schematicChart Ω hΩ,
    τ, hτ⟩⟩

/-- **Every dense open subspace contains a generic chart**, in existential form. -/
theorem exists_isGenericChart_factoring (P : CodimensionZeroPresentation B S hS X.1)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) {W : Subfunctor X.1}
    (hW : IsDenseOpenSubspace B S hS X.2 W) :
    ∃ (C : SmallEtale B S hS X.1) (_ : P.IsGenericChart C)
      (_ : IsOpenImmersion B S hS C.1.hom)
      (_ : DenseRange (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))
      (τ : yoneda.obj C.obj.left ⟶ W.toFunctor), τ ≫ W.ι = C.1.hom :=
  let D := (nonempty_genericChartIn P hfin hW).some
  ⟨D.chart, D.isGenericChart, D.isOpenImmersion, D.denseRange, D.factor, D.factor_comp⟩

/-! ### The coordinate of a rational function at a chart -/

/-- A factorization of a morphism from a representable presheaf through a subfunctor is
unique, the inclusion of a subfunctor being a monomorphism. -/
theorem factor_unique {W : Subfunctor X.1} {A : BigFppfOver B S hS}
    {τ τ' : yoneda.obj A ⟶ W.toFunctor} (h : τ ≫ W.ι = τ' ≫ W.ι) : τ = τ' :=
  (cancel_mono W.ι).mp h

/-- **The coordinate at an étale chart of a morphism from a subfunctor of `X` to the relative
affine line**, for a chart whose structure morphism factors through that subfunctor. -/
noncomputable def chartCoord {W : Subfunctor X.1} (ν : W.toFunctor ⟶ affineLineFunctor B S hS)
    (U : SmallEtale B S hS X.1) (τ : yoneda.obj U.obj.left ⟶ W.toFunctor) :
    (structurePresheaf B S hS X.1).obj (op U) :=
  affineLineCoordinate B S hS (op U.obj.left) (ν.app (op U.obj.left) (yonedaEquiv τ))

/-- **The coordinate of a rational function is compatible with restriction of charts.** -/
theorem structurePresheaf_map_chartCoord {W : Subfunctor X.1}
    (ν : W.toFunctor ⟶ affineLineFunctor B S hS) {U U' : SmallEtale B S hS X.1} (g : U' ⟶ U)
    (τ : yoneda.obj U.obj.left ⟶ W.toFunctor) :
    ((structurePresheaf B S hS X.1).map g.op).hom (chartCoord ν U τ) =
      chartCoord ν U' (yoneda.map g.hom.left ≫ τ) := by
  rw [chartCoord, chartCoord, ← yonedaEquiv_naturality, NatTrans.naturality_apply,
    affineLineCoordinate_map]
  rfl

/-- Restricting a representative to a smaller dense open subspace does not change its class. -/
theorem toRationalMap_homOfLe_comp {U W : Subfunctor X.1}
    (hU : IsDenseOpenSubspace B S hS X.2 U) (hW : IsDenseOpenSubspace B S hS X.2 W)
    (h : W ≤ U) (ν : U.toFunctor ⟶ affineLineFunctor B S hS) :
    PartialMap.toRationalMap B S hS
        (⟨W, hW, Subfunctor.homOfLe h ≫ ν⟩ :
          PartialMap B S hS X.2 (affineLineFunctor B S hS)) =
      PartialMap.toRationalMap B S hS ⟨U, hU, ν⟩ :=
  (PartialMap.toRationalMap_eq_iff B S hS).mpr ⟨W, hW, le_rfl, h, rfl⟩

/-- **Two rational functions are the classes of representatives on one dense open
subspace.** -/
theorem exists_common_rep (x y : rationalFunctions B S hS X.2) :
    ∃ (W : Subfunctor X.1) (hW : IsDenseOpenSubspace B S hS X.2 W)
      (νx νy : W.toFunctor ⟶ affineLineFunctor B S hS),
      PartialMap.toRationalMap B S hS
          (⟨W, hW, νx⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)) = x ∧
        PartialMap.toRationalMap B S hS
          (⟨W, hW, νy⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)) = y := by
  obtain ⟨fx, hfx⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨fy, hfy⟩ := RationalMap.exists_rep B S hS y
  obtain ⟨W, hW, hWx, hWy⟩ := exists_isDenseOpenSubspace_le B S hS X.2
    fx.dense_open_domain fy.dense_open_domain
  exact ⟨W, hW, Subfunctor.homOfLe hWx ≫ fx.hom, Subfunctor.homOfLe hWy ≫ fy.hom,
    (toRationalMap_homOfLe_comp fx.dense_open_domain hW hWx fx.hom).trans hfx,
    (toRationalMap_homOfLe_comp fy.dense_open_domain hW hWy fy.hom).trans hfy⟩

/-! ### The meromorphic function attached to a partial map -/

/-- The component at an étale chart of the canonical map `𝒪_X ⟶ 𝒦_X`. -/
noncomputable abbrev chartToMeromorphic (U : SmallEtale B S hS X.1) :
    (structurePresheaf B S hS X.1).obj (op U) →+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) :=
  ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom

/-- The canonical map `𝒪_X ⟶ 𝒦_X` is natural in the chart. -/
theorem chartToMeromorphic_naturality {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (x : (structurePresheaf B S hS X.1).obj (op U)) :
    chartToMeromorphic V (((structurePresheaf B S hS X.1).map g.op).hom x) =
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map g.op).hom (chartToMeromorphic U x) :=
  ConcreteCategory.congr_hom
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.naturality g.op) x

section Meromorphic

variable (P : CodimensionZeroPresentation B S hS X.1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

include hfin in
/-- A chosen generic chart inside a dense open subspace. -/
noncomputable def chosenGenericChart {W : Subfunctor X.1}
    (hW : IsDenseOpenSubspace B S hS X.2 W) : GenericChartIn P W :=
  (nonempty_genericChartIn P hfin hW).some

include hwa hfin in
/-- **A meromorphic function whose value at a generic chart is the coordinate of a morphism to
the relative affine line has that same description at every chart lying in the domain of the
morphism.**

The two sides agree after restriction to `U ×_X C`, which is injective by
`CodimensionZeroPresentation.IsGenericChart.bijective_meromorphicFunctionSheaf_map_prodFst`; there
both become the coordinate at `U ×_X C`, because the two factorizations of the structure morphism
of `U ×_X C` through the subfunctor agree. -/
theorem val_eq_chartCoord {W : Subfunctor X.1} (ν : W.toFunctor ⟶ affineLineFunctor B S hS)
    (D : GenericChartIn P W) (m : MeromorphicFunction B S hS X.1 X.2)
    (hm : m.val (op D.chart) = chartToMeromorphic D.chart (chartCoord ν D.chart D.factor))
    (U : SmallEtale B S hS X.1) (τ : yoneda.obj U.obj.left ⟶ W.toFunctor)
    (hτ : τ ≫ W.ι = U.1.hom) :
    m.val (op U) = chartToMeromorphic U (chartCoord ν U τ) := by
  have hfac : yoneda.map (SmallEtale.prodSnd B S hS X.1 U D.chart).hom.left ≫ D.factor =
      yoneda.map (SmallEtale.prodFst B S hS X.1 U D.chart).hom.left ≫ τ := by
    refine factor_unique ?_
    rw [Category.assoc, Category.assoc, D.factor_comp, hτ]
    exact (CodimensionZeroPresentation.map_prodFst_comp_hom U D.chart).symm
  refine (D.isGenericChart.bijective_meromorphicFunctionSheaf_map_prodFst hwa hfin U).injective ?_
  show ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
        (SmallEtale.prodFst B S hS X.1 U D.chart).op).hom (m.val (op U)) =
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
        (SmallEtale.prodFst B S hS X.1 U D.chart).op).hom
          (chartToMeromorphic U (chartCoord ν U τ))
  rw [meromorphicFunction_val_naturality m (SmallEtale.prodFst B S hS X.1 U D.chart),
    ← meromorphicFunction_val_naturality m (SmallEtale.prodSnd B S hS X.1 U D.chart), hm,
    ← chartToMeromorphic_naturality, ← chartToMeromorphic_naturality,
    structurePresheaf_map_chartCoord, structurePresheaf_map_chartCoord, hfac]

include P hwa hfin in
/-- **The meromorphic function attached to a partial map to the relative affine line**: the
unique meromorphic function whose value at the chosen generic chart inside the domain is the
coordinate of the partial map there. -/
noncomputable def meromorphicOfPartial
    (f : PartialMap B S hS X.2 (affineLineFunctor B S hS)) :
    MeromorphicFunction B S hS X.1 X.2 :=
  ((chosenGenericChart P hfin f.dense_open_domain).isGenericChart.genericChartSectionsRingEquiv
      hwa hfin).symm
    (chartToMeromorphic (chosenGenericChart P hfin f.dense_open_domain).chart
      (chartCoord f.hom (chosenGenericChart P hfin f.dense_open_domain).chart
        (chosenGenericChart P hfin f.dense_open_domain).factor))

/-- The defining property of
`AlgebraicGeometry.Space.meromorphicOfPartial` at the chosen generic chart. -/
theorem meromorphicOfPartial_val_chosenChart
    (f : PartialMap B S hS X.2 (affineLineFunctor B S hS)) :
    (meromorphicOfPartial P hwa hfin f).val
        (op (chosenGenericChart P hfin f.dense_open_domain).chart) =
      chartToMeromorphic (chosenGenericChart P hfin f.dense_open_domain).chart
        (chartCoord f.hom (chosenGenericChart P hfin f.dense_open_domain).chart
          (chosenGenericChart P hfin f.dense_open_domain).factor) :=
  ((chosenGenericChart P hfin f.dense_open_domain).isGenericChart.genericChartSectionsRingEquiv
    hwa hfin).apply_symm_apply _

/-- **The value of `AlgebraicGeometry.Space.meromorphicOfPartial` at every étale chart lying in
the domain of the partial map** is the coordinate of the partial map at that chart. -/
theorem meromorphicOfPartial_val (f : PartialMap B S hS X.2 (affineLineFunctor B S hS))
    (U : SmallEtale B S hS X.1) (τ : yoneda.obj U.obj.left ⟶ f.domain.toFunctor)
    (hτ : τ ≫ f.domain.ι = U.1.hom) :
    (meromorphicOfPartial P hwa hfin f).val (op U) =
      chartToMeromorphic U (chartCoord f.hom U τ) :=
  val_eq_chartCoord P hwa hfin f.hom (chosenGenericChart P hfin f.dense_open_domain) _
    (meromorphicOfPartial_val_chosenChart P hwa hfin f) U τ hτ

/-- **Equivalent partial maps have the same meromorphic function.**  A generic chart inside the
common dense open subspace lies in both domains, and the coordinates of the two partial maps
there agree, so the two meromorphic functions have the same value at that chart. -/
theorem meromorphicOfPartial_congr
    {f g : PartialMap B S hS X.2 (affineLineFunctor B S hS)}
    (h : PartialMap.Equivalent B S hS f g) :
    meromorphicOfPartial P hwa hfin f = meromorphicOfPartial P hwa hfin g := by
  obtain ⟨W, hW, hWf, hWg, heq⟩ := h
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin hW
  have hfac : ∀ {V : Subfunctor X.1} (hV : W ≤ V),
      (D.factor ≫ Subfunctor.homOfLe hV) ≫ V.ι = D.chart.1.hom := fun hV => by
    rw [Category.assoc, Subfunctor.homOfLe_ι, D.factor_comp]
  refine (D.isGenericChart.bijective_val_genericChart hwa hfin).injective ?_
  show (meromorphicOfPartial P hwa hfin f).val (op D.chart) =
    (meromorphicOfPartial P hwa hfin g).val (op D.chart)
  rw [meromorphicOfPartial_val P hwa hfin f D.chart (D.factor ≫ Subfunctor.homOfLe hWf) (hfac hWf),
    meromorphicOfPartial_val P hwa hfin g D.chart (D.factor ≫ Subfunctor.homOfLe hWg) (hfac hWg)]
  refine congrArg (chartToMeromorphic D.chart) ?_
  rw [chartCoord, chartCoord]
  refine congrArg (affineLineCoordinate B S hS (op D.chart.obj.left)) ?_
  rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, Category.assoc, heq]

include P hwa hfin in
/-- **The canonical map from the rational functions on `X` to the meromorphic functions on
`X`.** -/
noncomputable def rationalToMeromorphic :
    rationalFunctions B S hS X.2 → MeromorphicFunction B S hS X.1 X.2 :=
  Quotient.lift (meromorphicOfPartial P hwa hfin)
    fun _ _ h => meromorphicOfPartial_congr P hwa hfin h

/-- `AlgebraicGeometry.Space.rationalToMeromorphic` computes the meromorphic function of a
representative. -/
theorem rationalToMeromorphic_toRationalMap
    (f : PartialMap B S hS X.2 (affineLineFunctor B S hS)) :
    rationalToMeromorphic P hwa hfin (PartialMap.toRationalMap B S hS f) =
      meromorphicOfPartial P hwa hfin f :=
  rfl

/-- **The value of `AlgebraicGeometry.Space.rationalToMeromorphic` at every étale chart lying in
the domain of a representative.** -/
theorem rationalToMeromorphic_val (f : PartialMap B S hS X.2 (affineLineFunctor B S hS))
    (U : SmallEtale B S hS X.1) (τ : yoneda.obj U.obj.left ⟶ f.domain.toFunctor)
    (hτ : τ ≫ f.domain.ι = U.1.hom) :
    (rationalToMeromorphic P hwa hfin (PartialMap.toRationalMap B S hS f)).val (op U) =
      chartToMeromorphic U (chartCoord f.hom U τ) :=
  meromorphicOfPartial_val P hwa hfin f U τ hτ

/-! ### The ring homomorphism and its injectivity -/

/-- **The value at a chart lying in `W` of the meromorphic function of a representative defined
on a dense open subspace `W`.** -/
theorem val_rationalToMeromorphic_mk {W : Subfunctor X.1}
    (hW : IsDenseOpenSubspace B S hS X.2 W) (ν : W.toFunctor ⟶ affineLineFunctor B S hS)
    (U : SmallEtale B S hS X.1) (τ : yoneda.obj U.obj.left ⟶ W.toFunctor)
    (hτ : τ ≫ W.ι = U.1.hom) :
    (rationalToMeromorphic P hwa hfin (PartialMap.toRationalMap B S hS
        (⟨W, hW, ν⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)))).val (op U) =
      chartToMeromorphic U
        (affineLineCoordinate B S hS (op U.obj.left) (ν.app (op U.obj.left) (yonedaEquiv τ))) :=
  rationalToMeromorphic_val P hwa hfin
    (⟨W, hW, ν⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)) U τ hτ

/-- The value at a generic chart of `rationalToMeromorphic` of a class with representative `ν`. -/
private theorem val_rationalToMeromorphic_chart
    (P : CodimensionZeroPresentation B S hS X.1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) {x : rationalFunctions B S hS X.2}
    {W : Subfunctor X.1} {hW : IsDenseOpenSubspace B S hS X.2 W}
    {ν : W.toFunctor ⟶ affineLineFunctor B S hS}
    (hx : PartialMap.toRationalMap B S hS
      (⟨W, hW, ν⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)) = x)
    (D : GenericChartIn P W) :
    (rationalToMeromorphic P hwa hfin x).val (op D.chart) =
      chartToMeromorphic D.chart
        (affineLineCoordinate B S hS (op D.chart.obj.left)
          (ν.app (op D.chart.obj.left) (yonedaEquiv D.factor))) := by
  subst hx
  exact val_rationalToMeromorphic_mk P hwa hfin hW ν D.chart D.factor D.factor_comp

/-- **`AlgebraicGeometry.Space.rationalToMeromorphic` is additive.** -/
theorem rationalToMeromorphic_add (x y : rationalFunctions B S hS X.2) :
    rationalToMeromorphic P hwa hfin (x + y) =
      rationalToMeromorphic P hwa hfin x + rationalToMeromorphic P hwa hfin y := by
  obtain ⟨W, hW, νx, νy, hx, hy⟩ := exists_common_rep x y
  obtain ⟨a, m, ha, hm, hadd, hmul⟩ := (rationalFunctionsRing B S hS X.2).choose_spec.1 W hW νx νy
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin hW
  have hsum : PartialMap.toRationalMap B S hS
      (⟨W, hW, a⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)) = x + y := by
    rw [← hx, ← hy]
    exact hadd
  refine (D.isGenericChart.bijective_val_genericChart hwa hfin).injective ?_
  show (rationalToMeromorphic P hwa hfin (x + y)).val (op D.chart) =
    (rationalToMeromorphic P hwa hfin x).val (op D.chart) +
      (rationalToMeromorphic P hwa hfin y).val (op D.chart)
  rw [val_rationalToMeromorphic_chart P hwa hfin hsum D,
    val_rationalToMeromorphic_chart P hwa hfin hx D,
    val_rationalToMeromorphic_chart P hwa hfin hy D,
    ha (op D.chart.obj.left) (yonedaEquiv D.factor)]
  exact map_add _ _ _

/-- **`AlgebraicGeometry.Space.rationalToMeromorphic` is multiplicative.** -/
theorem rationalToMeromorphic_mul (x y : rationalFunctions B S hS X.2) :
    rationalToMeromorphic P hwa hfin (x * y) =
      rationalToMeromorphic P hwa hfin x * rationalToMeromorphic P hwa hfin y := by
  obtain ⟨W, hW, νx, νy, hx, hy⟩ := exists_common_rep x y
  obtain ⟨a, m, ha, hm, hadd, hmul⟩ := (rationalFunctionsRing B S hS X.2).choose_spec.1 W hW νx νy
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin hW
  have hprod : PartialMap.toRationalMap B S hS
      (⟨W, hW, m⟩ : PartialMap B S hS X.2 (affineLineFunctor B S hS)) = x * y := by
    rw [← hx, ← hy]
    exact hmul
  refine (D.isGenericChart.bijective_val_genericChart hwa hfin).injective ?_
  show (rationalToMeromorphic P hwa hfin (x * y)).val (op D.chart) =
    (rationalToMeromorphic P hwa hfin x).val (op D.chart) *
      (rationalToMeromorphic P hwa hfin y).val (op D.chart)
  rw [val_rationalToMeromorphic_chart P hwa hfin hprod D,
    val_rationalToMeromorphic_chart P hwa hfin hx D,
    val_rationalToMeromorphic_chart P hwa hfin hy D,
    hm (op D.chart.obj.left) (yonedaEquiv D.factor)]
  exact map_mul _ _ _

/-- **`AlgebraicGeometry.Space.rationalToMeromorphic` sends zero to zero.** -/
theorem rationalToMeromorphic_zero : rationalToMeromorphic P hwa hfin 0 = 0 := by
  obtain ⟨z, o, hz, ho, hzero, hone⟩ := (rationalFunctionsRing B S hS X.2).choose_spec.2.1 ⊤
    (isDenseOpenSubspace_top B S hS X.2)
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin (isDenseOpenSubspace_top B S hS X.2)
  refine (D.isGenericChart.bijective_val_genericChart hwa hfin).injective ?_
  show (rationalToMeromorphic P hwa hfin 0).val (op D.chart) =
    (0 : MeromorphicFunction B S hS X.1 X.2).val (op D.chart)
  rw [val_rationalToMeromorphic_chart P hwa hfin hzero D,
    hz (op D.chart.obj.left) (yonedaEquiv D.factor)]
  exact map_zero _

/-- **`AlgebraicGeometry.Space.rationalToMeromorphic` sends one to one.** -/
theorem rationalToMeromorphic_one : rationalToMeromorphic P hwa hfin 1 = 1 := by
  obtain ⟨z, o, hz, ho, hzero, hone⟩ := (rationalFunctionsRing B S hS X.2).choose_spec.2.1 ⊤
    (isDenseOpenSubspace_top B S hS X.2)
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin (isDenseOpenSubspace_top B S hS X.2)
  refine (D.isGenericChart.bijective_val_genericChart hwa hfin).injective ?_
  show (rationalToMeromorphic P hwa hfin 1).val (op D.chart) =
    (1 : MeromorphicFunction B S hS X.1 X.2).val (op D.chart)
  rw [val_rationalToMeromorphic_chart P hwa hfin hone D,
    ho (op D.chart.obj.left) (yonedaEquiv D.factor)]
  exact map_one _

include P hwa hfin in
/-- **The canonical ring homomorphism from the rational functions on `X` to the meromorphic
functions on `X`.** -/
noncomputable def rationalToMeromorphicRingHom :
    rationalFunctions B S hS X.2 →+* MeromorphicFunction B S hS X.1 X.2 where
  toFun := rationalToMeromorphic P hwa hfin
  map_one' := rationalToMeromorphic_one P hwa hfin
  map_mul' := rationalToMeromorphic_mul P hwa hfin
  map_zero' := rationalToMeromorphic_zero P hwa hfin
  map_add' := rationalToMeromorphic_add P hwa hfin

/-- **The canonical map from the rational functions on `X` to the meromorphic functions on `X`
is injective.**

Two rational functions with the same image have representatives on a common dense open
subspace `W`; at a generic chart `C` inside `W` their coordinates have the same image in
`𝒦_X(C)`, hence agree because `𝒪_X(C) ⟶ 𝒦_X(C)` is injective and an affine-line-valued point is
determined by its coordinate.  The two representatives therefore agree on the dense open
subspace cut out by `C`, the chart being a monomorphism. -/
theorem injective_rationalToMeromorphic :
    Function.Injective (rationalToMeromorphic P hwa hfin) := by
  intro x y hxy
  obtain ⟨W, hW, νx, νy, hx, hy⟩ := exists_common_rep x y
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin hW
  have := D.isGenericChart.mono
  have hval := (val_rationalToMeromorphic_chart P hwa hfin hx D).symm.trans
    ((congrArg (fun m => m.val (op D.chart)) hxy).trans
      (val_rationalToMeromorphic_chart P hwa hfin hy D))
  have hcoord : νx.app (op D.chart.obj.left) (yonedaEquiv D.factor) =
      νy.app (op D.chart.obj.left) (yonedaEquiv D.factor) :=
    affineLineCoordinate_injective B S hS (op D.chart.obj.left)
      (injective_toMeromorphicFunctionSheaf_app B S hS X hwa hfin D.chart hval)
  have hZdense : Dense (Set.range (pointsMap B S hS (Subfunctor.range D.chart.1.hom).toFunctor
      (Subfunctor.range D.chart.1.hom).ι)) := by
    have h := range_pointsMap_ι_chartRange D.chart D.isOpenImmersion
    rw [chartRange_eq_range] at h
    rw [h]
    exact D.denseRange
  have hZ : IsDenseOpenSubspace B S hS X.2 (Subfunctor.range D.chart.1.hom) :=
    ⟨isOpenSubspace_chartRange D.chart D.isOpenImmersion, hZdense⟩
  have hι : inv (Subfunctor.toRange D.chart.1.hom) ≫ D.chart.1.hom =
      (Subfunctor.range D.chart.1.hom).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι D.chart.1.hom).symm
  have hle : Subfunctor.range D.chart.1.hom ≤ W :=
    Subfunctor.le_of_comp_eq_ι (inv (Subfunctor.toRange D.chart.1.hom) ≫ D.factor) (by
      rw [Category.assoc, D.factor_comp]
      exact hι)
  have hfactor : Subfunctor.toRange D.chart.1.hom ≫ Subfunctor.homOfLe hle = D.factor := by
    refine factor_unique ?_
    rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι, D.factor_comp]
  have heq : Subfunctor.homOfLe hle ≫ νx = Subfunctor.homOfLe hle ≫ νy := by
    refine (cancel_epi (Subfunctor.toRange D.chart.1.hom)).mp ?_
    rw [← Category.assoc, ← Category.assoc, hfactor]
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_comp, hcoord]
  rw [← hx, ← hy, PartialMap.toRationalMap_eq_iff]
  exact ⟨Subfunctor.range D.chart.1.hom, hZ, hle, hle, heq⟩

end Meromorphic

end AlgebraicGeometry.Space

end
