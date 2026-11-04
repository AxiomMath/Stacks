module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeTopSectionsLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators

/-!
# Module pullback is cartesian on affine charts of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, let `G` be an `𝒪_Y`-module on the small étale site of `Y`, and let

      U ---ψ---> V
      |          |
      v          v
      X ---f---> Y

be a commutative diagram of étale scheme charts, that is, an
`AlgebraicGeometry.Space.ChartDiagram`.  Pullback of regular functions along `ψ` makes `𝒪_X(U)`
an algebra over `𝒪_Y(V)`, and the unit of the Stacks 03LU adjunction `f^* ⊣ f_*`, read through
the chartwise universal property of the direct image, carries a section of `G` over `V` to a
section of `f^*G` over `U` semilinearly over that ring map.  So the unit section has a canonical
`𝒪_X(U)`-linear extension

  `𝒪_X(U) ⊗_{𝒪_Y(V)} G(V) ⟶ (f^*G)(U)`,

**the base change comparison over the square**, and this file constructs it.  The main result is
that for `G` quasi-coherent and both charts affine the two sides are isomorphic as
`𝒪_X(U)`-modules: module pullback is cartesian on affine charts.

This is the two-space analogue of `AlgebraicGeometry.Space.sectionsBaseChange` and of
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, which compare the sections of one module
over two charts of *one* algebraic space; the scalar bookkeeping is the same, with
`AlgebraicGeometry.Space.chartDiagramPullback` in the role of
`AlgebraicGeometry.Space.chartRestrict` and the unit section in the role of restriction of
sections.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramSectionsModule` is the `𝒪_Y(V)`-module structure on the
  sections of an `𝒪_X`-module over `U` given by the square, over the `𝒪_Y(V)`-algebra structure
  `AlgebraicGeometry.Space.chartDiagramAlgebra` on `𝒪_X(U)`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FittingIdealPullback.lean`).
* `AlgebraicGeometry.Space.modulePullbackUnitFMap` is the unit section of
  `AlgebraicGeometry.Space.modulePullbackUnitSection` packaged as the canonical linear map of
  sections along `f` out of `G` into `f^*G`, and
  `AlgebraicGeometry.Space.modulePullbackUnitLinear` is its value at one square as an
  `𝒪_Y(V)`-linear map `G(V) →ₗ (f^*G)(U)`.
* `AlgebraicGeometry.Space.modulePullbackSectionsBaseChange` is the base change comparison
  `𝒪_X(U) ⊗_{𝒪_Y(V)} G(V) →ₗ[𝒪_X(U)] (f^*G)(U)`.

## Main results

* `AlgebraicGeometry.Space.chartDiagramSections_isScalarTower`: the two scalar actions on the
  sections over `U` are compatible, which is what makes the comparison exist.
* `AlgebraicGeometry.Space.modulePullbackUnitLinear_apply` and
  `AlgebraicGeometry.Space.modulePullbackUnitLinear_naturality`: the linear map is the unit
  section, and it is compatible with étale restriction of both charts.
* `AlgebraicGeometry.Space.modulePullbackSectionsBaseChange_tmul` and
  `AlgebraicGeometry.Space.modulePullbackSectionsBaseChange_one_tmul` evaluate the comparison,
  and `AlgebraicGeometry.Space.range_modulePullbackSectionsBaseChange` computes its range as the
  `𝒪_X(U)`-span of the unit sections, whence
  `AlgebraicGeometry.Space.modulePullbackSectionsBaseChange_surjective_iff_span_eq_top`.
* `AlgebraicGeometry.Space.nonempty_modulePullbackSectionsBaseChange_linearEquiv`: **for `G`
  quasi-coherent and both charts affine, `𝒪_X(U) ⊗_{𝒪_Y(V)} G(V)` and `(f^*G)(U)` are isomorphic
  as `𝒪_X(U)`-modules.**

## Implementation notes

`chartDiagramAlgebra` and `chartDiagramSectionsModule` depend on the square, so they cannot be
instances; they are `@[instance_reducible]` definitions, to be introduced by `letI` at each use,
exactly as `AlgebraicGeometry.Space.chartAlgebra` and
`AlgebraicGeometry.Space.chartSectionsModule` are.  With them in scope the comparison is
Mathlib's `LinearMap.liftBaseChange`.

**The semilinear map the comparison extends is canonical and is not invented here.**  It is the
transpose of the identity of `f^*G` under the Stacks 03LU chartwise universal property of the
direct image: `AlgebraicGeometry.Space.modulePullbackHomFMap` applied to `𝟙 (f^*G)`, whose values
are the unit sections `AlgebraicGeometry.Space.modulePullbackUnitSection` by
`AlgebraicGeometry.Space.modulePullbackHomFMap_app`.  Its additivity and its semilinearity over
`AlgebraicGeometry.Space.chartDiagramPullback` are the two algebraic fields of
`AlgebraicGeometry.Space.ModuleFMap`, so no new computation is needed to form the linear
extension.

**The two spellings of the ring of functions on a chart agree on the nose.**  The comparison is
stated over `AlgebraicGeometry.Space.chartRing`, the sections of the `RingCat`-valued structure
sheaf of the small étale ringed site, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean`; the scheme-side input below is stated
over `Γ(chartScheme U, ⊤)`, spelled in `CommRingCat`.  The two are definitionally equal
*including their `CommRing` instances* — `AlgebraicGeometry.Space.chartRing_commRing` is built so
that its `Ring` field is the one the module sections are modules over — and
`AlgebraicGeometry.Space.chartDiagramPullback` is definitionally
`AlgebraicGeometry.Scheme.Hom.appTop` of the vertical morphism of schemes, so
`chartDiagramAlgebra` is definitionally the algebra structure that
`ModuleCat.extendScalars` uses.  The proof below is therefore carried out entirely in the `Γ`
spelling and transferred by a single definitional check; what it cannot do is let *instance
search* cross between the spellings, which is why the `Γ`-spelled algebra is reintroduced by
`letI` and why every step of the chain of linear equivalences is ascribed before being composed.
Without the ascriptions `LinearEquiv.trans` reads the two coefficient rings as different and asks
for a `RingHomCompTriple`.

**Only the existence of an isomorphism is produced, not bijectivity of the comparison map.**  The
chain of identifications is: the sections of `G` over `V` are the global sections of its chart
restriction (`AlgebraicGeometry.Space.restrictToChartTopLinearEquiv` composed with
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`, both canonical); the global
sections of a Zariski pullback of a quasi-coherent module between affine schemes are the base
change of its global sections (`Stacks.AlgebraicGeometry.ModuleLimits.bcTop`, which is canonical
and is normalised on `1 ⊗ a` by
`Stacks.AlgebraicGeometry.ModuleLimits.bcTop_hom_one_tmul`); and the Zariski pullback along `ψ`
of the chart restriction of `G` is the chart restriction of `f^*G`, which is the base-change
identity of Stacks 060S in the form
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_modulePullback_square`.  **That last step
is where canonicity is lost**: the isomorphism there is obtained from the counit of an equivalence
of categories, so the file proving it produces only its existence, and consequently the composite
cannot be identified with
`AlgebraicGeometry.Space.modulePullbackSectionsBaseChange`.  Upgrading the conclusion to
bijectivity of the comparison map would need a canonical comparison
`ψ^*(G|_V) ⟶ (f^*G)|_U` of chart restrictions, which the tree does not have; it is not supplied
here and the statement below does not claim it.

No declaration here carries a `stacks` tag.  The pullback clause of Stacks 060S that is used is
already covered in the tree, and the sections-level statement proved here is an input to the
consumers of that clause rather than an assertion of a tag.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public section

open CategoryTheory Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The scalars attached to a commutative diagram of charts -/

/-- The vertical morphism of regular functions of a diagram of charts is the global sections of
its vertical morphism of schemes.  This is what lets the scheme-side base change of global
sections be read with the scalars of the diagram. -/
theorem chartDiagramPullback_hom (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartDiagramPullback B S hS f d).hom =
      (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map d.g)).hom := rfl

/-- The `𝒪_Y(V)`-module structure on the sections of an `𝒪_X`-module over `U` given by
restriction of scalars along a commutative diagram of étale scheme charts.  Not an instance: it
depends on the diagram. -/
@[instance_reducible]
noncomputable def chartDiagramSectionsModule (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Module (chartRing B S hS Y.1 Y.2 d.V) (M.val.obj (op d.U)) :=
  Module.compHom _ (chartDiagramPullback B S hS f d).hom

/-- An element of `𝒪_Y(V)` acts on the sections over `U` through its image in `𝒪_X(U)` under the
vertical morphism of the diagram. -/
theorem chartDiagramSectionsModule_smul (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (r : chartRing B S hS Y.1 Y.2 d.V)
    (x : M.val.obj (op d.U)) :
    letI := chartDiagramSectionsModule B S hS f M d
    r • x = (chartDiagramPullback B S hS f d).hom r • x := rfl

/-- The two scalar actions on the sections over `U` are compatible: the `𝒪_Y(V)`-action is the
`𝒪_X(U)`-action restricted along the vertical morphism of the diagram. -/
theorem chartDiagramSections_isScalarTower (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartDiagramSectionsModule B S hS f M d
    IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U)
      (M.val.obj (op d.U)) :=
  let := chartDiagramAlgebra B S hS f d
  let := chartDiagramSectionsModule B S hS f M d
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-! ### The unit section as a semilinear map of sections -/

/-- The canonical linear map of sections along `f` from `G` into its inverse image: the transpose
of the identity of `f^*G` under the Stacks 03LU chartwise universal property of the direct
image.

Its values are the unit sections of
`AlgebraicGeometry.Space.modulePullbackUnitSection`; packaging them this way is what supplies
their additivity and their semilinearity over
`AlgebraicGeometry.Space.chartDiagramPullback`. -/
noncomputable def modulePullbackUnitFMap (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ModuleFMap B S hS f ((modulePullback B S hS f).obj G) G :=
  modulePullbackHomFMap B S hS f G ((modulePullback B S hS f).obj G) (𝟙 _)

/-- The values of the canonical linear map of sections along `f` are the unit sections. -/
theorem modulePullbackUnitFMap_app (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)) :
    (modulePullbackUnitFMap B S hS f G).app d s =
      modulePullbackUnitSection B S hS f G d s :=
  modulePullbackHomFMap_app B S hS f G ((modulePullback B S hS f).obj G) (𝟙 _) d s

/-- The unit section at a commutative diagram of étale scheme charts, as an `𝒪_Y(V)`-linear map
`G(V) ⟶ (f^*G)(U)`. -/
noncomputable def modulePullbackUnitLinear (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramSectionsModule B S hS f ((modulePullback B S hS f).obj G) d
    (G.val.obj (op d.V) : Type u) →ₗ[chartRing B S hS Y.1 Y.2 d.V]
      (((modulePullback B S hS f).obj G).val.obj (op d.U) : Type u) :=
  letI := chartDiagramSectionsModule B S hS f ((modulePullback B S hS f).obj G) d
  { toFun := (modulePullbackUnitFMap B S hS f G).app d
    map_add' := (modulePullbackUnitFMap B S hS f G).map_add d
    map_smul' := fun r s => (modulePullbackUnitFMap B S hS f G).map_smul d r s }

/-- The values of the unit section, as an `𝒪_Y(V)`-linear map, are the unit sections. -/
theorem modulePullbackUnitLinear_apply (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)) :
    modulePullbackUnitLinear B S hS f G d s = modulePullbackUnitSection B S hS f G d s :=
  modulePullbackUnitFMap_app B S hS f G d s

/-- The unit section is compatible with étale restriction of both charts of the diagram. -/
theorem modulePullbackUnitLinear_naturality (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d d' : ChartDiagram B S hS X.1 Y.1 f.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (s : G.val.obj (op d.V)) :
    modulePullbackUnitLinear B S hS f G d' (G.val.map j.op s) =
      ((modulePullback B S hS f).obj G).val.map i.op
        (modulePullbackUnitLinear B S hS f G d s) :=
  (modulePullbackUnitFMap B S hS f G).naturality d d' i j h s

/-! ### The base change comparison over a commutative diagram of charts -/

/-- **The base change comparison over a commutative diagram of étale scheme charts**: the
`𝒪_X(U)`-linear extension `𝒪_X(U) ⊗_{𝒪_Y(V)} G(V) ⟶ (f^*G)(U)` of the unit section.

This is the canonical comparison map, the unit section being the transpose of the identity of
`f^*G`; `AlgebraicGeometry.Space.nonempty_modulePullbackSectionsBaseChange_linearEquiv` proves
that the two sides are isomorphic when `G` is quasi-coherent and both charts are affine, but see
the implementation notes for why that result is not stated as bijectivity of this map. -/
noncomputable def modulePullbackSectionsBaseChange (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    TensorProduct (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U)
        (G.val.obj (op d.V)) →ₗ[chartRing B S hS X.1 X.2 d.U]
      (((modulePullback B S hS f).obj G).val.obj (op d.U) : Type u) :=
  letI := chartDiagramAlgebra B S hS f d
  letI := chartDiagramSectionsModule B S hS f ((modulePullback B S hS f).obj G) d
  haveI := chartDiagramSections_isScalarTower B S hS f ((modulePullback B S hS f).obj G) d
  LinearMap.liftBaseChange _ (modulePullbackUnitLinear B S hS f G d)

/-- The base change comparison sends `b ⊗ s` to `b` times the unit section of `s`. -/
theorem modulePullbackSectionsBaseChange_tmul (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (b : chartRing B S hS X.1 X.2 d.U)
    (s : G.val.obj (op d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    modulePullbackSectionsBaseChange B S hS f G d (TensorProduct.tmul _ b s) =
      b • modulePullbackUnitLinear B S hS f G d s := rfl

/-- The base change comparison sends `1 ⊗ s` to the unit section of `s`. -/
theorem modulePullbackSectionsBaseChange_one_tmul (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : G.val.obj (op d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    modulePullbackSectionsBaseChange B S hS f G d
        (TensorProduct.tmul _ (1 : chartRing B S hS X.1 X.2 d.U) s) =
      modulePullbackUnitSection B S hS f G d s :=
  let := chartDiagramAlgebra B S hS f d
  (one_smul (chartRing B S hS X.1 X.2 d.U) (modulePullbackUnitLinear B S hS f G d s)).trans
    (modulePullbackUnitLinear_apply B S hS f G d s)

/-- The image of the base change comparison is the `𝒪_X(U)`-submodule generated by the unit
sections. -/
theorem range_modulePullbackSectionsBaseChange (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    LinearMap.range (modulePullbackSectionsBaseChange B S hS f G d) =
      Submodule.span (chartRing B S hS X.1 X.2 d.U)
        (Set.range fun s : G.val.obj (op d.V) => modulePullbackUnitLinear B S hS f G d s) :=
  let := chartDiagramAlgebra B S hS f d
  let := chartDiagramSectionsModule B S hS f ((modulePullback B S hS f).obj G) d
  have := chartDiagramSections_isScalarTower B S hS f ((modulePullback B S hS f).obj G) d
  LinearMap.range_liftBaseChange _ (modulePullbackUnitLinear B S hS f G d)

/-- The base change comparison is surjective exactly when the unit sections generate the sections
of `f^*G` over `U`. -/
theorem modulePullbackSectionsBaseChange_surjective_iff_span_eq_top (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Surjective (modulePullbackSectionsBaseChange B S hS f G d) ↔
      Submodule.span (chartRing B S hS X.1 X.2 d.U)
        (Set.range fun s : G.val.obj (op d.V) =>
          modulePullbackUnitLinear B S hS f G d s) = ⊤ := by
  let _ := chartDiagramAlgebra B S hS f d
  rw [← LinearMap.range_eq_top, range_modulePullbackSectionsBaseChange]

/-! ### Cartesian on affine charts -/

/-- The sections of a module over a chart are the global sections of its chart restriction to the
chart scheme, linearly over the global functions on the chart scheme. -/
private def sectionsLinearEquivRestrictToChartScheme (Z : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (A : SmallEtale B S hS Z.1) :
    (M.val.obj (op A) : Type u) ≃ₗ[Γ(chartScheme A, ⊤)]
      ((restrictToChartScheme B S hS Z.1 Z.2 M A).val.obj
        (op (⊤ : (chartScheme A).Opens)) : Type u) :=
  (restrictToChartTopLinearEquiv B S hS Z M A).trans
    (show ((restrictToChart B S hS Z.2 M A).val.obj
          (op (⊤ : (chartScheme A).Opens)) : Type u) ≃ₗ[Γ(chartScheme A, ⊤)]
        ((restrictToChartScheme B S hS Z.1 Z.2 M A).val.obj
          (op (⊤ : (chartScheme A).Opens)) : Type u) from
      Stacks.SheafOfModules.sectionsLinearEquivOfIso
        (restrictToChartIsoRestrictToChartScheme B S hS Z.2 M A) ⊤)

/-- **Module pullback is cartesian on affine charts.**  For a morphism `f : X ⟶ Y` of algebraic
spaces, a quasi-coherent `𝒪_Y`-module `G` and a commutative diagram of étale scheme charts whose
chart `U` of `X` and chart `V` of `Y` are both affine, the sections of `f^*G` over `U` are the
base change of the sections of `G` over `V`:

  `𝒪_X(U) ⊗_{𝒪_Y(V)} G(V) ≃ₗ[𝒪_X(U)] (f^*G)(U)`.

Three identifications compose to this.  The sections of `G` over `V` are the global sections of
its chart restriction, and likewise for `f^*G` over `U`
(`AlgebraicGeometry.Space.restrictToChartTopLinearEquiv` and
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`).  The Zariski pullback along
the vertical morphism of the diagram of the chart restriction of `G` is the chart restriction of
`f^*G`, which is the base-change identity of Stacks 060S,
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_modulePullback_square`.  And on affine
schemes the global sections of a Zariski pullback of a quasi-coherent module are the base change
of its global sections, `Stacks.AlgebraicGeometry.ModuleLimits.bcTop`; affineness of both charts
is used exactly there.

Only the existence of an isomorphism is asserted, because the Stacks 060S step provides only the
existence of an isomorphism of chart restrictions; see the implementation notes. -/
theorem nonempty_modulePullbackSectionsBaseChange_linearEquiv (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    Nonempty (TensorProduct (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U)
        (G.val.obj (op d.V)) ≃ₗ[chartRing B S hS X.1 X.2 d.U]
      (((modulePullback B S hS f).obj G).val.obj (op d.U) : Type u)) := by
  let _ := chartDiagramAlgebra B S hS f d
  have := hU
  have := hV
  let : Algebra Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤) :=
    (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map d.g)).hom.toAlgebra
  have : (restrictToChartScheme B S hS Y.1 Y.2 G d.V).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS Y G hG d.V
  obtain ⟨e₁⟩ := nonempty_restrictToChartScheme_modulePullback_square B S hS f G hG
    d.U d.V d.g d.comm
  -- the sections of `G` over `V` are the global sections of its chart restriction, and likewise
  -- for `f^*G` over `U`
  let eV := sectionsLinearEquivRestrictToChartScheme B S hS Y G d.V
  let eU := sectionsLinearEquivRestrictToChartScheme B S hS X ((modulePullback B S hS f).obj G) d.U
  -- the base-change identity of Stacks 060S at the diagram
  let eP : ((((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map d.g)).obj
        (restrictToChartScheme B S hS Y.1 Y.2 G d.V)).val.obj
          (op (⊤ : (chartScheme d.U).Opens))) : Type u) ≃ₗ[Γ(chartScheme d.U, ⊤)]
      ((restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) d.U).val.obj
        (op (⊤ : (chartScheme d.U).Opens)) : Type u) :=
    Stacks.SheafOfModules.sectionsLinearEquivOfIso e₁.symm ⊤
  -- the scheme-side base change of global sections between affine schemes
  let eBC : TensorProduct Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)
        ((restrictToChartScheme B S hS Y.1 Y.2 G d.V).val.obj
          (op (⊤ : (chartScheme d.V).Opens)) : Type u)
      ≃ₗ[Γ(chartScheme d.U, ⊤)]
        ((((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map d.g)).obj
          (restrictToChartScheme B S hS Y.1 Y.2 G d.V)).val.obj
            (op (⊤ : (chartScheme d.U).Opens))) : Type u) :=
    (Stacks.AlgebraicGeometry.ModuleLimits.bcTop
      ((BigFppfOver.toScheme B S hS).map d.g)
      (restrictToChartScheme B S hS Y.1 Y.2 G d.V)).toLinearEquiv
  let eT : TensorProduct Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)
        (G.val.obj (op d.V) : Type u)
      ≃ₗ[Γ(chartScheme d.U, ⊤)]
        TensorProduct Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)
          ((restrictToChartScheme B S hS Y.1 Y.2 G d.V).val.obj
            (op (⊤ : (chartScheme d.V).Opens)) : Type u) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl Γ(chartScheme d.U, ⊤) Γ(chartScheme d.U, ⊤)) eV
  let e := eT.trans (eBC.trans (eP.trans eU.symm))
  exact ⟨e⟩

end AlgebraicGeometry.Space

end

end
