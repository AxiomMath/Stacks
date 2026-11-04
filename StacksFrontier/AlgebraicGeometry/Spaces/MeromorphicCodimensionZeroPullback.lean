module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The direct image at a codimension-zero point of the inverse image of a module

Let `X` be an algebraic space over a scheme `S` with a presentation `P` of its schematic locus
at the codimension-zero points, let `η` be such a point and let `F` be an `𝒪_X`-module. The
contribution `j_{η, *}j_η^*F` of `η` to the sheaf of meromorphic *sections* of `F` is the direct
image, along small-chart base change, of the inverse image `j_η^*F` of Stacks 03LU. Its sections
over an étale chart `U` of `X` are the sections of `j_η^*F` over the base-changed chart
`U ×_X Spec(𝒪_{X, η})`.

## Main definitions

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointChartDiagram`: the diagram of
  étale charts `(U ×_X Spec(𝒪_{X, η}), U)` over `j_η`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointPullback`: `j_η^*F`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointSectionModule`:
  `j_{η, *}j_η^*F` as an `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointSectionModule_obj`: the
  sections of `j_{η, *}j_η^*F` over an étale chart `U` of `X` are the sections of `j_η^*F` over
  `U ×_X Spec(𝒪_{X, η})`.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {x : points B S hS X.1}
    (hx : localRingDimension B S hS x = 0)

/-- **The diagram of étale charts `(U ×_X Spec(𝒪_{X, η}), U)` over `j_η`.** Its commuting square
is the cartesian square defining the base-changed chart. -/
noncomputable def genericPointChartDiagram (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS (P.specStalkSpace hx).1 X.1 (P.genericMorphism hx X.2).hom where
  U := P.genericPointChart hx U
  V := U
  g := P.genericPointProjection hx U
  comm := ((P.representable_genericMorphism hx).isPullback U.1.hom).w

/-- **The inverse image `j_η^*F`** of an `𝒪_X`-module at a point of codimension `0`. -/
noncomputable def genericPointPullback (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2 :=
  (modulePullback B S hS (P.genericMorphism hx X.2)).obj F

/-- **The contribution `j_{η, *}j_η^*F` of a codimension-zero point to the meromorphic sections
of `F`**, as an `𝒪_X`-module: the direct image along small-chart base change of the inverse
image of `F`. -/
noncomputable def genericPointSectionModule (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (smallBaseChangeModulePushforward B S hS (P.genericMorphism hx X.2)
    (P.representable_genericMorphism hx)).obj (P.genericPointPullback hx F)

/-- **The sections of `j_{η, *}j_η^*F` over an étale chart `U` of `X` are the sections of `j_η^*F`
over the base-changed chart `U ×_X Spec(𝒪_{X, η})`**, as types. -/
theorem genericPointSectionModule_obj (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) :
    ((P.genericPointSectionModule hx F).val.obj (op U) : Type u) =
      ((P.genericPointPullback hx F).val.obj (op (P.genericPointChart hx U)) : Type u) :=
  rfl

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
