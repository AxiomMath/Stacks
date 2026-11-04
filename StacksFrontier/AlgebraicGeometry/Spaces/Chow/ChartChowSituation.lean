module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionAntitone

/-!
# The base situation of chapter 42 on an étale chart of a good algebraic space

In Situation 0EDT the base is an algebraic space, whereas the cycle theory of chapter 42 —
Stacks 02QL, `Stacks.Chow.ChowSituation` — is developed over a *scheme* base equipped with a
dimension function on its topological space. An étale chart `φ : h_V ⟶ X` of a good algebraic
space `X/B` carries all three ingredients of that situation on the chart scheme `V`:

* `V` is locally Noetherian, because local Noetherianity of a good algebraic space is an
  étale-local scheme property;
* `V` is universally catenary in the scheme sense of Stacks 02J8, which is
  `AlgebraicGeometry.Space.isUniversallyCatenary_chart_of_isUniversallyCatenary` applied to
  `X`, itself universally catenary over the base by Stacks 0ED8;
* `δ_{X/B} ∘ φ` is a dimension function on `V`, which is
  `AlgebraicGeometry.Space.exists_dimensionFunction_comp_chart` applied to the dimension
  function `AlgebraicGeometry.Space.deltaDimensionFunction` of Stacks 0EDN.

Taking the structure morphism of the chart over the base of the resulting situation to be the
identity, the relative dimension function of Stacks 02JW attached to it *is* the chosen
dimension function, so no comparison of δ-functions is needed: by
`AlgebraicGeometry.Space.relativeDimension_id_chartChowSituation` the relative dimension at a
point `v` of the chart is `δ_{X/B}(φ v)`, and by
`AlgebraicGeometry.Space.deltaDimension_eq_relativeDimension_id_chartChowSituation` the
δ-dimension of an integral closed subspace of `X` is that relative dimension at any point of
the chart over its generic point.

Both the chart and the surjectivity of its structure morphism are data of an algebraic space,
not extra hypotheses: `AlgebraicGeometry.Space.atlasChowSituation` is the situation on the
chart that the defining atlas of an algebraic space supplies.

## Main definitions

* `AlgebraicGeometry.Space.chartChowSituation`: the base situation of Stacks 02QL on the chart
  scheme of a surjective étale chart of a good algebraic space.
* `AlgebraicGeometry.Space.atlasChowSituation`: that situation at the defining atlas.

## Main results

* `AlgebraicGeometry.Space.chartChowSituation_dimensionFunction_apply`: its dimension function
  is `δ_{X/B} ∘ φ`.
* `AlgebraicGeometry.Space.relativeDimension_id_chartChowSituation`: the relative dimension
  function of Stacks 02JW of the chart over itself is `δ_{X/B} ∘ φ`.

## References

* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0ED8](https://stacks.math.columbia.edu/tag/0ED8)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (V : SmallEtale D.site D.base D.base_mem X)

/-! ### The ingredients on the chart -/

include sX hX in
/-- **A good algebraic space over the base is universally catenary**, by Stacks 0ED8: it is
locally of finite type over the base, and the base is universally catenary. -/
theorem isUniversallyCatenary_of_isGood :
    IsUniversallyCatenary D.site D.base D.base_mem X :=
  isUniversallyCatenary_of_isLocallyOfFiniteType D.site D.base D.base_mem D.isAlgebraicSpace
    hX.1 D.universallyCatenary sX hX.2.2

include sX hX in
/-- **The scheme of an étale chart of a good algebraic space is universally catenary** in the
scheme sense of Stacks 02J8: the space is universally catenary by Stacks 0ED8, and
`AlgebraicGeometry.Space.isUniversallyCatenary_chart_of_isUniversallyCatenary` reads that on an
étale chart whose scheme is locally Noetherian. -/
theorem isUniversallyCatenary_chartScheme_of_isGood :
    @Scheme.IsUniversallyCatenary (chartScheme V)
      (isLocallyNoetherian_chartScheme_of_isGood D sX hX V) :=
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V.obj.left) :=
    isLocallyNoetherian_chartScheme_of_isGood D sX hX V
  isUniversallyCatenary_chart_of_isUniversallyCatenary D.site D.base D.base_mem hX.1
    (isUniversallyCatenary_of_isGood D sX hX) V.obj.left V.obj.hom
    (isEtale_of_presheaf_etale D.site D.base D.base_mem V.property)

include hX in
/-- **`δ_{X/B}` read on a surjective étale chart is a dimension function on the chart scheme.**
This is `AlgebraicGeometry.Space.exists_dimensionFunction_comp_chart` at the dimension function
`AlgebraicGeometry.Space.deltaDimensionFunction` of Stacks 0EDN. -/
theorem exists_dimensionFunction_deltaValue_chartScheme
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom) :
    ∃ d : DimensionFunction (chartScheme V),
      ∀ v, d v = D.deltaValue sX (chartSchemeToPoints D.site D.base D.base_mem X V v) :=
  let ⟨d, hd⟩ := exists_dimensionFunction_comp_chart D.site D.base D.base_mem hs V.property
    hX.1 (isDecentSpace_of_isGood D sX hX) (isUniversallyCatenary_of_isGood D sX hX)
    (deltaDimensionFunction D sX hX) (isLocallyNoetherian_chartScheme_of_isGood D sX hX V)
  ⟨d, fun v => ((hd v).trans (deltaDimensionFunction_apply D sX hX _)).trans
    (congrArg (D.deltaValue sX)
      (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm D.site D.base D.base_mem X
        V v).symm)⟩

/-! ### The base situation on the chart -/

include sX hX in
/-- **The base situation of Stacks 02QL on a surjective étale chart of a good algebraic
space.** The chart scheme of a surjective étale chart `φ : h_V ⟶ X` of a good algebraic space
`X/B`, with its local Noetherianity, its universal catenarity in the scheme sense of
Stacks 02J8, and the dimension function `δ_{X/B} ∘ φ` of Stacks 0EDN. -/
def chartChowSituation
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom) :
    Stacks.Chow.ChowSituation.{u} where
  S := chartScheme V
  isLocallyNoetherian := isLocallyNoetherian_chartScheme_of_isGood D sX hX V
  isUniversallyCatenary := isUniversallyCatenary_chartScheme_of_isGood D sX hX V
  dimensionFunction := (exists_dimensionFunction_deltaValue_chartScheme D sX hX V hs).choose

variable
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)

/-- The base scheme of the situation on the chart is the chart scheme. -/
@[simp]
theorem chartChowSituation_S :
    (chartChowSituation D sX hX V hs).S = chartScheme V :=
  rfl

/-- **The dimension function of the situation on the chart is `δ_{X/B} ∘ φ`.** -/
theorem chartChowSituation_dimensionFunction_apply (v : chartScheme V) :
    (chartChowSituation D sX hX V hs).dimensionFunction v =
      D.deltaValue sX (chartSchemeToPoints D.site D.base D.base_mem X V v) :=
  (exists_dimensionFunction_deltaValue_chartScheme D sX hX V hs).choose_spec v

/-- **The relative dimension of Stacks 02JW of the chart over itself is `δ_{X/B} ∘ φ`.**
Taking the structure morphism of the chart scheme over the base of the situation on the chart
to be the identity, the relative dimension function of Stacks 02JW is the chosen dimension
function, hence `δ_{X/B} ∘ φ`. -/
theorem relativeDimension_id_chartChowSituation
    (v : (chartChowSituation D sX hX V hs).S) :
    Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartChowSituation D sX hX V hs).S) v =
      D.deltaValue sX (chartSchemeToPoints D.site D.base D.base_mem X V v) :=
  (Stacks.Chow.relativeDimension_id _ v).trans
    (chartChowSituation_dimensionFunction_apply D sX hX V hs v)

/-- **The δ-dimension of an integral closed subspace, read on the chart.** At a point of the
chart over the generic point of `|Z|`, the relative dimension function of Stacks 02JW attached
to the situation on the chart takes the value `dim_δ(Z)`. -/
theorem deltaDimension_eq_relativeDimension_id_chartChowSituation
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (v : (chartChowSituation D sX hX V hs).S)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem) :
    deltaDimension D sX Z =
      Stacks.Chow.relativeDimension (chartChowSituation D sX hX V hs).dimensionFunction
        (𝟙 (chartChowSituation D sX hX V hs).S) v := by
  rw [relativeDimension_id_chartChowSituation D sX hX V hs v, hv]
  rfl

/-! ### The situation at the defining atlas -/

/-- The étale chart of an algebraic space supplied by its defining atlas. -/
def atlasSmallEtale (hsp : IsAlgebraicSpace D.site D.base D.base_mem X) :
    SmallEtale D.site D.base D.base_mem X :=
  ⟨CostructuredArrow.mk (atlasHom D.site D.base D.base_mem ⟨X, hsp⟩),
    atlasHom_etale D.site D.base D.base_mem ⟨X, hsp⟩⟩

/-- **The base situation of Stacks 02QL at the defining atlas of a good algebraic space.** No
choice of chart is needed: the atlas of `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` is
surjective and étale. -/
def atlasChowSituation : Stacks.Chow.ChowSituation.{u} :=
  chartChowSituation D sX hX (atlasSmallEtale D hX.1)
    (atlasHom_surjective D.site D.base D.base_mem ⟨X, hX.1⟩)

/-- The base scheme of the situation at the defining atlas is the scheme of the atlas. -/
@[simp]
theorem atlasChowSituation_S :
    (atlasChowSituation D sX hX).S = chartScheme (atlasSmallEtale D hX.1) :=
  rfl

/-- **The dimension function of the situation at the defining atlas is `δ_{X/B}` read on the
atlas.** -/
theorem atlasChowSituation_dimensionFunction_apply
    (v : chartScheme (atlasSmallEtale D hX.1)) :
    (atlasChowSituation D sX hX).dimensionFunction v =
      D.deltaValue sX
        (chartSchemeToPoints D.site D.base D.base_mem X (atlasSmallEtale D hX.1) v) :=
  chartChowSituation_dimensionFunction_apply D sX hX _ _ v

end AlgebraicGeometry.Space

end
