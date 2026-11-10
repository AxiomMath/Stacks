module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleOfHomLinearIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBaseChangePresieve
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeChartRingTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePushforwardCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine

/-!
# The direct image of the pulled-back coefficient is a tensor product

Let `D` be the cartesian square of **Stacks 073J**,

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

a square of algebraic spaces over a scheme `S` of a big fppf site `B`, let `𝓕` be its
quasi-coherent coefficient on `X` and `𝓕' = (g')^*𝓕` its inverse image on `X'`, and suppose the
two bases are affine algebraic spaces, with étale charts `V₀` and `V₀'` presenting them as
affine schemes.  Their coordinate rings are

  `A = Γ(chartScheme V₀, ⊤)`,    `B = Γ(chartScheme V₀', ⊤)`,

so that `Y = Spec A` and `Y' = Spec B`.  This file proves the identification

  `g'_*𝓕'  ≅  𝓕 ⊗_{\underline{A}} \underline{B}`

of the second part of [Stacks Project, Tag 073K] — "moreover we have
`g'_*𝓕_B = 𝓕 ⊗_{\underline{A}} \underline{B}`" — where `\underline{A}` and `\underline{B}` are
the constant sheaves of rings and the right-hand side is
`AlgebraicGeometry.Space.tensorByBaseChartModule`.  **Nothing is assumed of `X`**, and flatness
of `g` is not used: this step of the source's proof is the chartwise computation
`g'_*𝓕'(U) = 𝓕'(U ×_X X') = 𝓕(U) ⊗_A B` over the affine charts of `X`, and flatness enters
Stacks 073K only afterwards, in the dévissage along a presentation of `B`.

## Main definitions

* `AlgebraicGeometry.Space.geometricCoefficientMap`: the coefficient map `\underline{A} ⟶ 𝒪_X`
  of an affine base in its *geometric* spelling, pullback of regular functions along
  `AlgebraicGeometry.Space.baseChartHom`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorHom`: **the ring comparison**
  `𝒪_X(U) ⊗_A B ⟶ 𝒪_{X'}(U ×_X X')`, the `𝒪_X(U)`-linear extension of pullback of regular
  functions from `V₀'`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear`: **the comparison of
  sections over a chart**, `𝓕(U) ⊗_{𝒪_X(U)} (𝒪_X(U) ⊗_A B) ⟶ 𝓕'(U ×_X X')`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorComparison`: **the comparison
  `𝓕 ⊗_{\underline{A}} \underline{B} ⟶ g'_*𝓕'` at the level of presheaves.**

## Main results

* `AlgebraicGeometry.Space.baseChartCoefficientMap_eq`: the two spellings of the coefficient map
  of an affine base agree.
* `AlgebraicGeometry.Space.BaseChangeDiagram.bijective_chartRingTensorHom` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.bijective_pushforwardTensorAppLinear`: the two
  comparisons are bijective over an affine chart.
* `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorIso` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorChartIso`:
  **`𝓕 ⊗_{\underline{A}} \underline{B} ≅ g'_*𝓕'`**, for the tensor functor taken at the
  geometric coefficient map and at `AlgebraicGeometry.Space.baseChartCoefficientMap`
  respectively.

## Implementation notes

*The comparison is built, not assumed.*  Over a chart `U` of `X` it is the composite of three
linear maps: the symmetry of the tensor product, the ring comparison
`AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorHom` tensored with `𝓕(U)`, and the
base-change comparison `AlgebraicGeometry.Space.modulePullbackChartBaseChange` of the inverse
image over the chart diagram
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartDiagram`.  Being a composite it needs
no linearity proof; it is natural in `U` because each factor is, and bijective over an affine
chart because each factor is there — the last one by
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`,
which is the only place quasi-coherence of `𝓕` is used.  The gluing is
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom` over the affine charts,
which generate covering sieves of every étale chart.

*Why the coefficient map is respelled.*  The ring identification
`AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquivChart` is stated over
`AlgebraicGeometry.Space.baseChartAlgebra`, the `A`-algebra structure on `𝒪_X(U)` given by `Γ`
of the morphism of schemes `AlgebraicGeometry.Space.baseChartHom`, whereas
`AlgebraicGeometry.Space.baseChartCoefficientMap` goes round through the global regular
functions of `Y` and of `X`.  The two are equal but not definitionally so, and the algebra
structures a tensor product is formed over must agree definitionally for two statements to be
about the same object.  `AlgebraicGeometry.Space.geometricCoefficientMap` is the first
spelling, over which the whole construction is carried out; the chart-square formula
`AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartDiagram` for the comparison of
**Stacks 0732** identifies it with the second, and the result is transported at the end.

*Three spellings of the ring of functions on a chart.*  `Γ(chartScheme U, ⊤)`,
`AlgebraicGeometry.Space.chartRing` and the sections of the structure presheaf are
definitionally equal, including their `CommRing` instances, but instance search crosses between
them for none of the algebra and module structures involved.  Each statement below fixes one
spelling and reintroduces the structures it needs by an ascribed `letI`, as
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackCartesianAffineCharts.lean` does; the
ascription is where the definitional equality is checked, once.

*Why the naturality of the comparison is split over four declarations.*  Its proof is an
induction over two nested tensor products whose terms mention the whole tensor functor, and the
`rfl` steps that reconcile the spellings are not cheap; carried out in one declaration it
exhausts the heartbeat budget.  Each of the two inductions, the pure-tensor case and the
assembled morphism therefore has a declaration of its own.

No declaration here carries a `stacks` tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The diagram of étale charts over `f : X ⟶ Y` formed by a chart `U` of `X`, a chart `V₀` of
`Y` presenting `Y` as a scheme, and `AlgebraicGeometry.Space.baseChartHom`. -/
def baseChartHomDiagram (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom]
    (U : SmallEtale B S hS X.1) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := U
  V := V₀
  g := baseChartHom B S hS f V₀ U
  comm := (yoneda_map_baseChartHom_comp B S hS f V₀ U).symm

/-- **The coefficient map of an affine base is pullback of regular functions along
`AlgebraicGeometry.Space.baseChartHom`.**

`AlgebraicGeometry.Space.baseChartRingHom` goes round through the global regular functions of
`Y` and of `X`; the chart-square formula
`AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartDiagram` for the comparison of
Stacks 0732 evaluates that composite on the chart diagram
`AlgebraicGeometry.Space.baseChartHomDiagram` as `Γ` of its vertical morphism of schemes. -/
theorem baseChartRingHom_apply (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) [IsIso V₀.obj.hom] (U : SmallEtale B S hS X.1)
    (a : baseChartRing B S hS Y V₀) :
    baseChartRingHom B S hS f hV₀ (op U) a =
      ((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS f V₀ U)).appTop.hom a := by
  have hs : ((globalSectionsChartRingEquiv B S hS Y hV₀).symm a).1 (op V₀) = a :=
    (globalSectionsChartRingEquiv B S hS Y hV₀).apply_symm_apply a
  have key : ((globalSectionsRingHomSite B S hS f)
        ((globalSectionsChartRingEquiv B S hS Y hV₀).symm a)).1 (op U) =
      chartDiagramPullback B S hS f (baseChartHomDiagram B S hS f V₀ U)
        (((globalSectionsChartRingEquiv B S hS Y hV₀).symm a).1 (op V₀)) :=
    globalSectionsRingHomSite_val_chartDiagram B S hS f _ (baseChartHomDiagram B S hS f V₀ U)
  rw [hs] at key
  exact key

/-- `AlgebraicGeometry.Space.baseChartHom` is natural in the chart: the structure morphism of a
chart `U'` over `V₀` is the one of `U` precomposed with any morphism `U' ⟶ U` of charts. -/
theorem toOver_map_comp_baseChartHom (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1)
    [IsIso V₀.obj.hom] {U U' : SmallEtale B S hS X.1} (h : U' ⟶ U) :
    (SmallEtale.toOver B S hS X.1).map h ≫ baseChartHom B S hS f V₀ U =
      baseChartHom B S hS f V₀ U' := by
  apply yoneda.map_injective
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map h) ≫ U.obj.hom = U'.obj.hom :=
    CostructuredArrow.w h.hom
  rw [Functor.map_comp, yoneda_map_baseChartHom, yoneda_map_baseChartHom, ← Category.assoc, hw]

/-- **The coefficient map of an affine base, in its geometric spelling**: the morphism of
presheaves of commutative rings `\underline{A} ⟶ 𝒪_X` whose value over a chart `U` is pullback
of regular functions along `AlgebraicGeometry.Space.baseChartHom`.

It is `AlgebraicGeometry.Space.baseChartCoefficientMap`
(`AlgebraicGeometry.Space.baseChartCoefficientMap_eq`), but its values are *definitionally* the
algebra structures `AlgebraicGeometry.Space.baseChartAlgebra` over which the ring identification
at a base-changed chart is stated, which the other spelling is not. -/
def geometricCoefficientMap (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom] :
    Stacks.TensorByBaseModule.constantRingPresheaf (C := SmallEtale B S hS X.1)
        (baseChartRing B S hS Y V₀) ⟶ (structureSheaf B S hS X.1 X.2).obj where
  app U := CommRingCat.ofHom
    (((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS f V₀ U.unop)).appTop.hom)
  naturality {U W} g := by
    refine (Category.id_comp _).trans (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    conv_lhs => rw [← toOver_map_comp_baseChartHom B S hS f V₀ g.unop]
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

/-- The two spellings of the coefficient map of an affine base agree. -/
theorem baseChartCoefficientMap_eq (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) [IsIso V₀.obj.hom] :
    baseChartCoefficientMap B S hS f hV₀ = geometricCoefficientMap B S hS f V₀ :=
  NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun a => baseChartRingHom_apply B S hS f hV₀ U.unop a))

namespace BaseChangeDiagram

variable {B S hS} (D : BaseChangeDiagram B S hS)
  (hg' : yoneda.relativelyRepresentable D.g'.hom)
  (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]
  (U : SmallEtale B S hS D.X.1)

/-- The `A`-algebra structure on the functions of a chart `U` of `X`, in the spelling
`AlgebraicGeometry.Space.chartRing` over which the sections of an `𝒪_X`-module are a module.
This is `AlgebraicGeometry.Space.baseChartAlgebra`; only the spelling of the target differs, and
instance search does not cross between the two. -/
@[instance_reducible]
def chartBaseAlgebra : Algebra (baseChartRing B S hS D.Y V₀)
    (chartRing B S hS D.X.1 D.X.2 U) :=
  baseChartAlgebra B S hS D.f V₀ U

/-- The `A`-algebra structure on the functions of the base-changed chart, in the `chartRing`
spelling. -/
@[instance_reducible]
def chartBaseChangeAlgebra : Algebra (baseChartRing B S hS D.Y V₀)
    (chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U)) :=
  D.baseChangeChartAlgebra hg' V₀ U

/-- The `𝒪_X(U)`-algebra structure on the functions of the base-changed chart, in the
`chartRing` spelling.  It is the one the chart diagram
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartDiagram` carries. -/
@[instance_reducible]
def chartBaseChangeChartAlgebra : Algebra (chartRing B S hS D.X.1 D.X.2 U)
    (chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U)) :=
  D.baseChangeChartChartAlgebra hg' U

/-- Pullback of regular functions from the chart `V₀'` of `Y'` to the chart of `X'` lying over
`U`, along the structure morphism of that chart over `V₀'`. -/
def baseChangeChartBaseHom : baseChartRing B S hS D.Y' V₀' →+*
    chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U) :=
  ((BigFppfOver.toScheme B S hS).map
    (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U))).appTop.hom

/-- **The first commuting triangle as a scalar tower**: the `A`-algebra structure on the
functions of the base-changed chart is the `𝒪_X(U)`-algebra structure restricted along
`A ⟶ 𝒪_X(U)`. -/
theorem isScalarTower_baseChangeChart :
    letI := D.chartBaseAlgebra V₀ U
    letI := D.chartBaseChangeAlgebra hg' V₀ U
    letI := D.chartBaseChangeChartAlgebra hg' U
    IsScalarTower (baseChartRing B S hS D.Y V₀) (chartRing B S hS D.X.1 D.X.2 U)
      (chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U)) :=
  let := D.chartBaseAlgebra V₀ U
  let := D.chartBaseChangeAlgebra hg' V₀ U
  let := D.chartBaseChangeChartAlgebra hg' U
  IsScalarTower.of_algebraMap_eq fun a =>
    (D.appTop_baseChangeChart_projection hg' V₀ U a).symm

/-- **The second commuting triangle**: pullback of regular functions from `V₀'` to the
base-changed chart is `A`-linear. -/
def baseChangeChartBaseLinear :
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.chartBaseChangeAlgebra hg' V₀ U
    (baseChartRing B S hS D.Y' V₀') →ₗ[baseChartRing B S hS D.Y V₀]
      chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U) :=
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  letI := D.chartBaseChangeAlgebra hg' V₀ U
  { toFun := D.baseChangeChartBaseHom hg' V₀' U
    map_add' := map_add _
    map_smul' := fun a b => by
      change D.baseChangeChartBaseHom hg' V₀' U
          (algebraMap (baseChartRing B S hS D.Y V₀) _ a * b) =
        algebraMap (baseChartRing B S hS D.Y V₀) _ a * D.baseChangeChartBaseHom hg' V₀' U b
      rw [map_mul]
      exact congrArg (fun y => y * D.baseChangeChartBaseHom hg' V₀' U b)
        (D.appTop_baseChangeChart_base hg' V₀ V₀' U a) }

/-- **The comparison `𝒪_X(U) ⊗_A B ⟶ 𝒪_{X'}(U ×_X X')`**: the `𝒪_X(U)`-linear extension of
pullback of regular functions from `V₀'`.  It carries `c ⊗ b` to the product of the pullback of
`c` along the cartesian projection with the pullback of `b` along the structure morphism over
`V₀'`, and it is bijective over an affine chart
(`AlgebraicGeometry.Space.BaseChangeDiagram.bijective_chartRingTensorHom`). -/
def chartRingTensorHom :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.chartBaseChangeChartAlgebra hg' U
    chartRing B S hS D.X.1 D.X.2 U ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀') →ₗ[chartRing B S hS D.X.1 D.X.2 U]
      chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U) :=
  letI := D.chartBaseAlgebra V₀ U
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  letI := D.chartBaseChangeAlgebra hg' V₀ U
  letI := D.chartBaseChangeChartAlgebra hg' U
  haveI := D.isScalarTower_baseChangeChart hg' V₀ U
  (D.baseChangeChartBaseLinear hg' V₀ V₀' U).liftBaseChange
    (chartRing B S hS D.X.1 D.X.2 U)

/-- The comparison carries `c ⊗ b` to `c` acting on the pullback of `b`, that is, to the product
of the pullback of `c` along the cartesian projection with the pullback of `b`. -/
theorem chartRingTensorHom_tmul (c : chartRing B S hS D.X.1 D.X.2 U)
    (b : baseChartRing B S hS D.Y' V₀') :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.chartBaseChangeChartAlgebra hg' U
    D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b) =
      c • D.baseChangeChartBaseHom hg' V₀' U b := rfl

/-- **The comparison `𝒪_X(U) ⊗_A B ⟶ 𝒪_{X'}(U ×_X X')` is bijective over an affine chart.**

It is the ring identification
`AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquivChart`: both are additive and
agree on `c ⊗ b`, where the first is the product of the two pullbacks by construction and the
second is so by
`AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquiv_tmul`. -/
theorem bijective_chartRingTensorHom [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    [IsAffine (chartScheme U)] :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    Function.Bijective (D.chartRingTensorHom hg' V₀ V₀' U) := by
  let := D.chartBaseAlgebra V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.chartBaseChangeAlgebra hg' V₀ U
  let := D.chartBaseChangeChartAlgebra hg' U
  have := D.isScalarTower_baseChangeChart hg' V₀ U
  let e : chartRing B S hS D.X.1 D.X.2 U ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀') ≃ₐ[chartRing B S hS D.X.1 D.X.2 U]
      chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U) :=
    D.chartRingTensorAlgEquivChart hg' V₀ V₀' U
  have h : D.chartRingTensorHom hg' V₀ V₀' U = e.toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun c b => by
      rw [D.chartRingTensorHom_tmul hg' V₀ V₀' U c b, Algebra.smul_def]
      exact (D.chartRingTensorAlgEquiv_tmul hg' V₀ V₀' U c b).symm
  rw [h]
  exact e.bijective

/-- The `𝒪_X(U)`-module structure on the sections of `(g')^*𝓕` over the base-changed chart, by
restriction of scalars along the cartesian projection.  This is the module structure the
sections of the direct image `g'_*(g')^*𝓕` over `U` carry. -/
@[instance_reducible]
def pushforwardSectionsModule : Module (chartRing B S hS D.X.1 D.X.2 U)
    (((modulePullback B S hS D.g').obj D.F).val.obj (op (D.baseChangeChart hg' U))) :=
  modulePullbackChartSectionModule B S hS D.g' D.F (D.baseChangeChartDiagram hg' U)

/-- The two scalar actions on the sections of `(g')^*𝓕` over the base-changed chart form a
tower. -/
theorem isScalarTower_pushforwardSections :
    letI := D.chartBaseChangeChartAlgebra hg' U
    letI := D.pushforwardSectionsModule hg' U
    IsScalarTower (chartRing B S hS D.X.1 D.X.2 U)
      (chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U))
      (((modulePullback B S hS D.g').obj D.F).val.obj (op (D.baseChangeChart hg' U))) :=
  modulePullbackChart_isScalarTower B S hS D.g' D.F (D.baseChangeChartDiagram hg' U)

/-- **The comparison of sections over a chart `U`**: the `𝒪_X(U)`-linear map
`𝓕(U) ⊗_{𝒪_X(U)} (𝒪_X(U) ⊗_A B) ⟶ 𝓕'(U ×_X X')` carrying `s ⊗ (c ⊗ b)` to the product of the
pullbacks of `c` and of `b` times the chart component of the unit of `(g')^* ⊣ g'_*` at `s`.

It is the comparison `𝒪_X(U) ⊗_A B ⟶ 𝒪_{X'}(U ×_X X')` tensored with `𝓕(U)`, followed by the
base-change comparison of the inverse image over the chart diagram. -/
def pushforwardTensorAppLinear :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.pushforwardSectionsModule hg' U
    (D.F.val.obj (op U) ⊗[chartRing B S hS D.X.1 D.X.2 U]
        (chartRing B S hS D.X.1 D.X.2 U ⊗[baseChartRing B S hS D.Y V₀]
          (baseChartRing B S hS D.Y' V₀'))) →ₗ[chartRing B S hS D.X.1 D.X.2 U]
      (((modulePullback B S hS D.g').obj D.F).val.obj (op (D.baseChangeChart hg' U))) := by
  letI := D.chartBaseAlgebra V₀ U
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  letI := D.chartBaseChangeChartAlgebra hg' U
  letI := D.pushforwardSectionsModule hg' U
  haveI := D.isScalarTower_pushforwardSections hg' U
  let base : chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U)
        ⊗[chartRing B S hS D.X.1 D.X.2 U] (D.F.val.obj (op U)) →ₗ[
          chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U)]
      (((modulePullback B S hS D.g').obj D.F).val.obj (op (D.baseChangeChart hg' U))) :=
    modulePullbackChartBaseChange B S hS D.g' D.F (D.baseChangeChartDiagram hg' U)
  exact LinearMap.restrictScalars (chartRing B S hS D.X.1 D.X.2 U) base ∘ₗ
    LinearMap.rTensor (D.F.val.obj (op U)) (D.chartRingTensorHom hg' V₀ V₀' U) ∘ₗ
    (TensorProduct.comm (chartRing B S hS D.X.1 D.X.2 U) (D.F.val.obj (op U))
      (chartRing B S hS D.X.1 D.X.2 U ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀'))).toLinearMap

/-- The comparison of sections carries `s ⊗ (c ⊗ b)` to the product of the two pullbacks acting
on the chart component of the unit at `s`. -/
theorem pushforwardTensorAppLinear_tmul (s : D.F.val.obj (op U))
    (c : chartRing B S hS D.X.1 D.X.2 U) (b : baseChartRing B S hS D.Y' V₀') :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.chartBaseChangeChartAlgebra hg' U
    letI := D.pushforwardSectionsModule hg' U
    letI := chartDiagramAlgebra B S hS D.g' (D.baseChangeChartDiagram hg' U)
    D.pushforwardTensorAppLinear hg' V₀ V₀' U
        (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U] (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b)) =
      modulePullbackChartBaseChange B S hS D.g' D.F (D.baseChangeChartDiagram hg' U)
        (D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b) ⊗ₜ s) := rfl

/-- **The comparison of sections is bijective over an affine chart.**

Its three factors are: the symmetry of the tensor product; the ring comparison
`AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorHom`, bijective over an affine chart
by `AlgebraicGeometry.Space.BaseChangeDiagram.bijective_chartRingTensorHom`, tensored with
`𝓕(U)`; and the base-change comparison of the inverse image, bijective over a diagram of affine
charts by
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`,
which is where quasi-coherence of `𝓕` is used.  The scheme of the base-changed chart is affine by
`AlgebraicGeometry.Space.BaseChangeDiagram.isAffine_chartScheme_baseChangeChart`. -/
theorem bijective_pushforwardTensorAppLinear [IsAffine (chartScheme V₀)]
    [IsAffine (chartScheme V₀')] [IsAffine (chartScheme U)] :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.pushforwardSectionsModule hg' U
    Function.Bijective (D.pushforwardTensorAppLinear hg' V₀ V₀' U) := by
  let := D.chartBaseAlgebra V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.chartBaseChangeChartAlgebra hg' U
  let := D.pushforwardSectionsModule hg' U
  have := D.isScalarTower_pushforwardSections hg' U
  have hbase : Function.Bijective
      (modulePullbackChartBaseChange B S hS D.g' D.F (D.baseChangeChartDiagram hg' U)) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS D.g' D.F
      D.isQuasicoherent (D.baseChangeChartDiagram hg' U)
      (D.isAffine_chartScheme_baseChangeChart hg' V₀ V₀' U) ‹IsAffine (chartScheme U)›
  let eγ := LinearEquiv.ofBijective (D.chartRingTensorHom hg' V₀ V₀' U)
    (D.bijective_chartRingTensorHom hg' V₀ V₀' U)
  have hrt : Function.Bijective
      (LinearMap.rTensor (D.F.val.obj (op U)) (D.chartRingTensorHom hg' V₀ V₀' U)) :=
    (LinearEquiv.rTensor (D.F.val.obj (op U)) eγ).bijective
  exact hbase.comp (hrt.comp
    (TensorProduct.comm (chartRing B S hS D.X.1 D.X.2 U) (D.F.val.obj (op U))
      (chartRing B S hS D.X.1 D.X.2 U ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀'))).bijective)

/-- The morphism of base-changed charts induced by a morphism `k : U' ⟶ U` of charts of `X`. -/
def baseChangeChartMap {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U) :
    D.baseChangeChart hg' U' ⟶ D.baseChangeChart hg' U :=
  (smallBaseChange B S hS D.g' hg').map k

/-- The square of charts over `g'` attached to a morphism `k : U' ⟶ U` of charts of `X`: the
cartesian projections commute with base change of the chart. -/
theorem toOver_map_baseChange_comp_projection {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U) :
    (SmallEtale.toOver B S hS D.X'.1).map (D.baseChangeChartMap hg' k) ≫
        D.baseChangeChartProjection hg' U =
      D.baseChangeChartProjection hg' U' ≫ (SmallEtale.toOver B S hS D.X.1).map k :=
  (smallBaseChangeProjection B S hS D.g' hg').naturality k

/-- Restriction of regular functions along the morphism of base-changed charts induced by a
morphism `k : U' ⟶ U` of charts of `X`. -/
def baseChangeChartRestrict {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U) :
    chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U) →+*
      chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U') :=
  chartRestrict (hF := D.X'.2) (D.baseChangeChartMap hg' k)

/-- Restricting along the cartesian projection and then to the base-changed chart over `U'` is
restricting to `U'` and then along its cartesian projection: the cartesian square, read on
regular functions. -/
theorem baseChangeChartRestrict_algebraMap {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U)
    (x : chartRing B S hS D.X.1 D.X.2 U) :
    letI := D.chartBaseChangeChartAlgebra hg' U
    letI := D.chartBaseChangeChartAlgebra hg' U'
    D.baseChangeChartRestrict hg' k
        (algebraMap (chartRing B S hS D.X.1 D.X.2 U)
          (chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U)) x) =
      algebraMap (chartRing B S hS D.X.1 D.X.2 U')
        (chartRing B S hS D.X'.1 D.X'.2 (D.baseChangeChart hg' U'))
        (chartRestrict (hF := D.X.2) k x) := by
  have h2 : ((BigFppfOver.toScheme B S hS).map (D.baseChangeChartProjection hg' U)).appTop ≫
        ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS D.X'.1).map (D.baseChangeChartMap hg' k))).appTop =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS D.X.1).map k)).appTop ≫
        ((BigFppfOver.toScheme B S hS).map (D.baseChangeChartProjection hg' U')).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Functor.map_comp,
      ← Functor.map_comp, D.toOver_map_baseChange_comp_projection hg' k]
  exact congrArg (fun m => (CommRingCat.Hom.hom m) x) h2

/-- Pullback of a regular function from `V₀'` is compatible with restriction of the chart. -/
theorem baseChangeChartRestrict_baseHom {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U)
    (b : baseChartRing B S hS D.Y' V₀') :
    D.baseChangeChartRestrict hg' k (D.baseChangeChartBaseHom hg' V₀' U b) =
      D.baseChangeChartBaseHom hg' V₀' U' b := by
  have h2 : ((BigFppfOver.toScheme B S hS).map
          (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U))).appTop ≫
        ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS D.X'.1).map (D.baseChangeChartMap hg' k))).appTop =
      ((BigFppfOver.toScheme B S hS).map
        (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U'))).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Functor.map_comp,
      toOver_map_comp_baseChartHom B S hS D.f' V₀' (D.baseChangeChartMap hg' k)]
  exact congrArg (fun m => (CommRingCat.Hom.hom m) b) h2

/-- **The ring comparison is natural in the chart.**  The two squares it is built from are the
cartesian one,
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartRestrict_algebraMap`, and the
compatibility of the structure morphisms over `V₀'`,
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartRestrict_baseHom`. -/
theorem baseChangeChartRestrict_chartRingTensorHom {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U)
    (c : chartRing B S hS D.X.1 D.X.2 U) (b : baseChartRing B S hS D.Y' V₀') :
    letI := D.chartBaseAlgebra V₀ U
    letI := D.chartBaseAlgebra V₀ U'
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    D.baseChangeChartRestrict hg' k
        (D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b)) =
      D.chartRingTensorHom hg' V₀ V₀' U'
        (chartRestrict (hF := D.X.2) k c ⊗ₜ[baseChartRing B S hS D.Y V₀] b) := by
  let := D.chartBaseAlgebra V₀ U
  let := D.chartBaseAlgebra V₀ U'
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.chartBaseChangeChartAlgebra hg' U
  let := D.chartBaseChangeChartAlgebra hg' U'
  change D.baseChangeChartRestrict hg' k (c • D.baseChangeChartBaseHom hg' V₀' U b) =
    chartRestrict (hF := D.X.2) k c • D.baseChangeChartBaseHom hg' V₀' U' b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, D.baseChangeChartRestrict_baseHom hg' V₀' k b,
    D.baseChangeChartRestrict_algebraMap hg' k c]

/-- The chart component of the unit of `(g')^* ⊣ g'_*` over the base-changed chart lying over
`U`: the canonical section of `(g')^*𝓕` over `U ×_X X'` attached to a section of `𝓕` over
`U`. -/
def unitSection (s : D.F.val.obj (op U)) :
    ((modulePullback B S hS D.g').obj D.F).val.obj (op (D.baseChangeChart hg' U)) :=
  modulePullbackChartSection B S hS D.g' D.F (D.baseChangeChartDiagram hg' U) s

/-- The unit section is natural under restriction of the chart. -/
theorem map_unitSection {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U)
    (s : D.F.val.obj (op U)) :
    ((modulePullback B S hS D.g').obj D.F).val.map (D.baseChangeChartMap hg' k).op
        (D.unitSection hg' U s) =
      D.unitSection hg' U' (D.F.val.map k.op s) :=
  ((modulePullbackChartFMap_app B S hS D.g' D.F (D.baseChangeChartDiagram hg' U')
        (D.F.val.map k.op s)).symm.trans
    (((modulePullbackChartFMap B S hS D.g' D.F).naturality
        (D.baseChangeChartDiagram hg' U) (D.baseChangeChartDiagram hg' U')
        (D.baseChangeChartMap hg' k) k
        (D.toOver_map_baseChange_comp_projection hg' k) s).trans
      (congrArg (((modulePullback B S hS D.g').obj D.F).val.map
          (D.baseChangeChartMap hg' k).op)
        (modulePullbackChartFMap_app B S hS D.g' D.F
          (D.baseChangeChartDiagram hg' U) s)))).symm

/-- The coordinate ring `B` of `Y'` as a module over the coordinate ring `A` of `Y`, through the
structure morphism of the chart `V₀'` over `V₀`. -/
def baseModule : ModuleCat.{u} (baseChartRing B S hS D.Y V₀) :=
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  ModuleCat.of (baseChartRing B S hS D.Y V₀) (baseChartRing B S hS D.Y' V₀')

/-- **The comparison of sections is natural in the chart**, on pure tensors.

Three inputs: the direct image restricts by restricting upstairs, so the scalar and the section
restrict separately (`PresheafOfModules.map_smul`); the scalar part is
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartRestrict_chartRingTensorHom`; and the
section part is the naturality of the chart component of the unit,
`AlgebraicGeometry.Space.modulePullbackChartFMap`, over the cartesian square of charts. -/
theorem pushforwardTensorAppLinear_naturality_tmul {U U' : SmallEtale B S hS D.X.1} (k : U' ⟶ U)
    (s : D.F.val.obj (op U)) (c : chartRing B S hS D.X.1 D.X.2 U)
    (b : baseChartRing B S hS D.Y' V₀') :
    letI := D.chartBaseAlgebra V₀ U
    letI := D.chartBaseAlgebra V₀ U'
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    ((modulePullback B S hS D.g').obj D.F).val.map (D.baseChangeChartMap hg' k).op
        (D.pushforwardTensorAppLinear hg' V₀ V₀' U
          (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U] (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b))) =
      D.pushforwardTensorAppLinear hg' V₀ V₀' U'
        (D.F.val.map k.op s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U']
          (chartRestrict (hF := D.X.2) k c ⊗ₜ[baseChartRing B S hS D.Y V₀] b)) := by
  let := D.chartBaseAlgebra V₀ U
  let := D.chartBaseAlgebra V₀ U'
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.chartBaseChangeChartAlgebra hg' U
  let := D.chartBaseChangeChartAlgebra hg' U'
  let := D.pushforwardSectionsModule hg' U
  let := D.pushforwardSectionsModule hg' U'
  change ((modulePullback B S hS D.g').obj D.F).val.map (D.baseChangeChartMap hg' k).op
      (D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b) •
        D.unitSection hg' U s) =
    D.chartRingTensorHom hg' V₀ V₀' U'
        (chartRestrict (hF := D.X.2) k c ⊗ₜ[baseChartRing B S hS D.Y V₀] b) •
      D.unitSection hg' U' (D.F.val.map k.op s)
  refine Eq.trans (PresheafOfModules.map_smul
    (M := ((modulePullback B S hS D.g').obj D.F).val) (D.baseChangeChartMap hg' k).op
    (D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b))
    (D.unitSection hg' U s)) ?_
  rw [D.map_unitSection hg' k s,
    ← D.baseChangeChartRestrict_chartRingTensorHom hg' V₀ V₀' k c b]
  rfl

section Comparison

/-- The direct image `g'_*𝓕'` of the pulled-back coefficient along the projection `g'`. -/
abbrev pushforwardPulledBack : Modules.{u, u} B S hS D.X.1 D.X.2 :=
  (smallBaseChangeModulePushforward B S hS D.g' hg').obj D.pulledBack

/-- The presheaf `U ↦ 𝓕(U) ⊗_{𝒪_X(U)} (𝒪_X(U) ⊗_A B)` whose sheafification is
`𝓕 ⊗_{\underline{A}} \underline{B}`. -/
abbrev tensorPresheaf : PresheafOfModules
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      (structureSheaf B S hS D.X.1 D.X.2).obj) :=
  (Stacks.TensorByBaseModule.tensorByBaseModulePresheafOfHom
    (baseChartRing B S hS D.Y V₀) (SmallEtale.topology B S hS D.X.1)
    (structureSheaf B S hS D.X.1 D.X.2) D.F
    (geometricCoefficientMap B S hS D.f V₀)).obj (D.baseModule V₀ V₀')

/-- The direct image `g'_*𝓕'` read as a presheaf of `𝒪_X`-modules, in the shape the gluing step
consumes. -/
abbrev pushforwardPresheaf : PresheafOfModules
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      (structureSheaf B S hS D.X.1 D.X.2).obj) :=
  (PresheafOfModules.restrictScalars
      (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
        (structureSheaf B S hS D.X.1 D.X.2)).obj)).obj
    ((SheafOfModules.forget _).obj (D.pushforwardPulledBack hg'))

/-- The comparison of sections over a chart, as a morphism of the modules of sections. -/
def pushforwardTensorApp (W : (SmallEtale B S hS D.X.1)ᵒᵖ) :
    (D.tensorPresheaf V₀ V₀').obj W ⟶ (D.pushforwardPresheaf hg').obj W :=
  ModuleCat.ofHom (D.pushforwardTensorAppLinear hg' V₀ V₀' W.unop)

/-- The naturality square of the comparison, on a pure tensor `s ⊗ (c ⊗ b)`. -/
theorem pushforwardTensorApp_naturality_tmul_tmul {W W' : (SmallEtale B S hS D.X.1)ᵒᵖ}
    (h : W ⟶ W') (s : D.F.val.obj W)
    (c : (structureSheaf B S hS D.X.1 D.X.2).obj.obj W) (b : D.baseModule V₀ V₀') :
    letI := ((geometricCoefficientMap B S hS D.f V₀).app W).hom.toAlgebra
    ((D.tensorPresheaf V₀ V₀').map h ≫
          (ModuleCat.restrictScalars
              ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
                (structureSheaf B S hS D.X.1 D.X.2).obj).map h).hom).map
            (D.pushforwardTensorApp hg' V₀ V₀' W')).hom (s ⊗ₜ (c ⊗ₜ b)) =
      (D.pushforwardTensorApp hg' V₀ V₀' W ≫ (D.pushforwardPresheaf hg').map h).hom
        (s ⊗ₜ (c ⊗ₜ b)) :=
  (D.pushforwardTensorAppLinear_naturality_tmul hg' V₀ V₀' h.unop s c b).symm

/-- The naturality square of the comparison, on a tensor `s ⊗ n`. -/
theorem pushforwardTensorApp_naturality_tmul {W W' : (SmallEtale B S hS D.X.1)ᵒᵖ} (h : W ⟶ W')
    (s : D.F.val.obj W)
    (n : ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (geometricCoefficientMap B S hS D.f V₀)).obj
      ((Stacks.TensorByBaseModule.constantModulePresheaf
        (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀'))).obj W) :
    ((D.tensorPresheaf V₀ V₀').map h ≫
          (ModuleCat.restrictScalars
              ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
                (structureSheaf B S hS D.X.1 D.X.2).obj).map h).hom).map
            (D.pushforwardTensorApp hg' V₀ V₀' W')).hom (s ⊗ₜ n) =
      (D.pushforwardTensorApp hg' V₀ V₀' W ≫ (D.pushforwardPresheaf hg').map h).hom
        (s ⊗ₜ n) := by
  let := ((geometricCoefficientMap B S hS D.f V₀).app W).hom.toAlgebra
  let : Module (((structureSheaf B S hS D.X.1 D.X.2).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj W) (D.F.val.obj W) :=
    (D.F.val.obj W).isModule
  let : Module ((Stacks.TensorByBaseModule.constantRingPresheaf
        (C := SmallEtale B S hS D.X.1) (baseChartRing B S hS D.Y V₀)).obj W)
      (((Stacks.TensorByBaseModule.constantModulePresheaf
        (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀')).obj W) :=
    (((Stacks.TensorByBaseModule.constantModulePresheaf
      (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀')).obj W).isModule
  let : Module (((structureSheaf B S hS D.X.1 D.X.2).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj W)
      ((structureSheaf B S hS D.X.1 D.X.2).obj.obj W ⊗[
          (Stacks.TensorByBaseModule.constantRingPresheaf
            (C := SmallEtale B S hS D.X.1) (baseChartRing B S hS D.Y V₀)).obj W]
        (((Stacks.TensorByBaseModule.constantModulePresheaf
          (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀')).obj W)) :=
    (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (geometricCoefficientMap B S hS D.f V₀)).obj
      ((Stacks.TensorByBaseModule.constantModulePresheaf
        (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀'))).obj W).isModule
  induction n using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((congrArg _ (TensorProduct.tmul_add (R := ((structureSheaf B S hS D.X.1 D.X.2).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj W) s x y)).trans (map_add _ _ _)).trans
      ((congrArg₂ (· + ·) hx hy).trans
        (((congrArg _ (TensorProduct.tmul_add (R := ((structureSheaf B S hS D.X.1 D.X.2).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u}).obj W) s x y)).trans (map_add _ _ _)).symm))
  | tmul c b => exact D.pushforwardTensorApp_naturality_tmul_tmul hg' V₀ V₀' h s c b

/-- **The naturality square of the comparison.** -/
theorem pushforwardTensorApp_naturality {W W' : (SmallEtale B S hS D.X.1)ᵒᵖ} (h : W ⟶ W') :
    (D.tensorPresheaf V₀ V₀').map h ≫
        (ModuleCat.restrictScalars
            ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
              (structureSheaf B S hS D.X.1 D.X.2).obj).map h).hom).map
          (D.pushforwardTensorApp hg' V₀ V₀' W') =
      D.pushforwardTensorApp hg' V₀ V₀' W ≫ (D.pushforwardPresheaf hg').map h := by
  exact ModuleCat.hom_ext (TensorProduct.ext' fun s n =>
    D.pushforwardTensorApp_naturality_tmul hg' V₀ V₀' h s n)

/-- **The comparison `𝓕 ⊗_{\underline{A}} \underline{B} ⟶ g'_*𝓕'`, at the level of
presheaves.**  Over a chart `U` it is
`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear`. -/
def pushforwardTensorComparison :
    D.tensorPresheaf V₀ V₀' ⟶ D.pushforwardPresheaf hg' where
  app W := D.pushforwardTensorApp hg' V₀ V₀' W
  naturality {_ _} h := D.pushforwardTensorApp_naturality hg' V₀ V₀' h

/-- **The direct image of the pulled-back coefficient is the coefficient tensored by `B`.**

This is the identification `g'_*𝓕' = 𝓕 ⊗_{\underline{A}} \underline{B}` of the second part of
[Stacks Project, Tag 073K], for the cartesian square of Stacks 073J whose two bases are affine
algebraic spaces, with `A` and `B` their coordinate rings at the charts `V₀` and `V₀'`.

The comparison is checked on the sections over the *affine* charts of `X`, where both sides are
computed by Descent, Proposition 03DX(2), and glued by
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom`: the affine charts over an
étale chart generate a covering sieve.  Nothing is assumed of `X`. -/
def pushforwardTensorIso [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] :
    (Stacks.TensorByBaseModule.tensorByBaseModuleOfHom
        (baseChartRing B S hS D.Y V₀) (SmallEtale.topology B S hS D.X.1)
        (structureSheaf B S hS D.X.1 D.X.2) D.F
        (geometricCoefficientMap B S hS D.f V₀)).obj (D.baseModule V₀ V₀') ≅
      D.pushforwardPulledBack hg' :=
  Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom
    (baseChartRing B S hS D.Y V₀) (SmallEtale.topology B S hS D.X.1)
    (structureSheaf B S hS D.X.1 D.X.2) D.F (geometricCoefficientMap B S hS D.f V₀)
    (D.baseModule V₀ V₀') (D.pushforwardPulledBack hg')
    (D.pushforwardTensorComparison hg' V₀ V₀')
    (fun W => IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj W))
    (fun V => SmallEtale.generate_affineChartPresieve_mem B S hS D.X.1 V)
    (fun W hW => by
      have : IsAffine (chartScheme W) := hW
      exact D.bijective_pushforwardTensorAppLinear hg' V₀ V₀' W)

/-- **`g'_*𝓕' ≅ 𝓕 ⊗_{\underline{A}} \underline{B}`**, for the tensor functor
`AlgebraicGeometry.Space.tensorByBaseChartModule` built from the coefficient map
`AlgebraicGeometry.Space.baseChartCoefficientMap` of the affine base.

It is `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorIso` transported along
`AlgebraicGeometry.Space.baseChartCoefficientMap_eq`, the two spellings of that coefficient map
being equal. -/
def pushforwardTensorChartIso (hV₀ : IsTerminal V₀) [IsAffine (chartScheme V₀)]
    [IsAffine (chartScheme V₀')] :
    (tensorByBaseChartModule B S hS D.f hV₀ D.F).obj (D.baseModule V₀ V₀') ≅
      D.pushforwardPulledBack hg' :=
  eqToIso (congrArg (fun θ => (Stacks.TensorByBaseModule.tensorByBaseModuleOfHom
      (baseChartRing B S hS D.Y V₀) (SmallEtale.topology B S hS D.X.1)
      (structureSheaf B S hS D.X.1 D.X.2) D.F θ).obj (D.baseModule V₀ V₀'))
    (baseChartCoefficientMap_eq B S hS D.f hV₀)) ≪≫ D.pushforwardTensorIso hg' V₀ V₀'

end Comparison

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
