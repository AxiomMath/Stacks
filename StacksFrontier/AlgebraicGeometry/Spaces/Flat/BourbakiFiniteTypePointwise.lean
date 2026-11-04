module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramTensorComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceTensorPullbackLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.BourbakiFiniteTypeGeneralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel

/-!
# Bourbaki's formula at a point of an algebraic space

Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `x` be a point of `|X|` with image `y` in `|Y|`, let `𝓕` be a finite
type quasi-coherent `𝒪_X`-module and let `𝓖` be a quasi-coherent `𝒪_Y`-module.  If `𝓕` is flat
at `x` over `Y`, then

`x ∈ WeakAss_X(𝓕 ⊗_{𝒪_X} f^*𝓖) ↔ y ∈ WeakAss_Y(𝓖) and x ∈ Ass_{X/Y}(𝓕)`.

This is Stacks 0CVK, and it is proved here under exactly those hypotheses, by the source's own
argument: choose a commuting square of étale scheme charts over `f` through `x`, transport the
four conditions to that square, and cite the case of schemes, Stacks 05IH.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType`:
  **Stacks 0CVK**, with no hypothesis beyond the tag's own.

## Implementation notes

The inputs of the reduction are the following.

* the square itself, through an arbitrary point of `|X|`, is
  `AlgebraicGeometry.Space.exists_chartDiagram_chartSchemeToPoints_eq`;
* the transport of the two sides between the square and the algebraic space is
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram`,
  whose two inputs are discharged below;
* its first input, the comparison `(𝓕 ⊗_{𝒪_X} f^*𝓖)|_U ≅ 𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`, is
  `AlgebraicGeometry.Space.nonempty_restrictToChart_tensor_modulePullback_chartDiagram`;
* its second input, the identification of the Zariski relative assassin of Stacks 05AT of the
  chart morphism with the relative weak assassin of Stacks 0CV0, is the conjunction of
  `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram`
  and `AlgebraicGeometry.Space.mem_relativeWeaklyAssociatedPoints_chartDiagram`; the second
  lands in the relative weak assassin of Stacks 05AV, which is the relative assassin because
  the chart morphism is locally of finite type by
  `AlgebraicGeometry.Space.locallyOfFiniteType_chartDiagramSchemeMap`, so that Stacks 05F2,
  `AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin`, applies;
* quasi-coherence of `𝓕 ⊗_{𝒪_X} f^*𝓖` on the small étale site, which the transport needs on the
  left-hand side, is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj_modulePullback_of_isQuasicoherentOnSite`
  because the pullback `f^*𝓖` is quasi-coherent by Stacks 03GA with no hypothesis on `f`, and a
  tensor product of quasi-coherent modules is quasi-coherent by Stacks 03M1(5);
* the Zariski biconditional on the square is the unconditional form of the scheme case,
  `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType`, the `@[stacks
  05IH]` site, which asks for the chart morphism to be locally of finite type and for the chart
  restrictions to be quasi-coherent and, on the source, of finite type — nothing about finite
  presentation, finitely generated maximal ideals or projectivity of a stalk.  The chart
  restrictions are quasi-coherent by Stacks 03DL(6) in the form
  `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, and the source one is of finite
  type by `AlgebraicGeometry.Space.isFiniteType_restrictToChart`, whose finite-type input is the
  categorical form of Stacks 03DL(5) and comes from the tag's own finite-type hypothesis through
  `Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType`;
* the chart-level flatness the scheme case consumes is derived from the tag's own flatness
  hypothesis by `AlgebraicGeometry.Space.isFlatOverAt_chartDiagram_of_mem_flatLocus`, which is
  Stacks 05VU.

Flatness at `x` is `AlgebraicGeometry.Space.IsFlatOverAtPoint`, the pointwise form of
Stacks 05VV, which is the shape in which the source hypothesises it; it is the same condition as
membership of `x` in `AlgebraicGeometry.Space.flatLocus`, both being the existence of one
commuting square of étale scheme charts through `x` on which the chart restriction is flat over
the target chart.  Finite type is `SheafOfModules.IsFiniteType`, quasi-coherence is
`SheafOfModules.IsQuasicoherentOnSite` of Stacks 03DL(6), and the two sets are
`AlgebraicGeometry.Space.weaklyAssociatedPoints` of Stacks 0CTX and
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints` of Stacks 0CV0 — the latter being the
set the source writes `Ass_{X/Y}(𝓕)`, the fibres of `f` being locally Noetherian by
Stacks 0CUY.  The tensor product is `AlgebraicGeometry.Space.modulesMonoidalCategory`, the
tensor product of Stacks 01CA on the small étale ringed site; the module universe is that of the
structure rings, the universe at which it and Stacks 0CTW both exist.

The right-hand side is stated with the base condition first.
A consumer wanting the order of the source, `Ass_{X/Y}(𝓕)` first — for instance
`AlgebraicGeometry.Space.IsBourbakiFormulaAtFlatPoints` of
`StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedTensorPullbackFiniteType`, the pointwise
hypothesis of Stacks 0CVL — gets it by `and_comm`.

## References

* [Stacks Project, Tag 0CVK](https://stacks.math.columbia.edu/tag/0CVK)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `x` be a point of `|X|`, let `𝓕` be a finite type quasi-coherent
`𝒪_X`-module and let `𝓖` be a quasi-coherent `𝒪_Y`-module.  If `𝓕` is flat at `x` over `Y`, then
`x` is weakly associated to `𝓕 ⊗_{𝒪_X} f^*𝓖` if and only if the image of `x` is weakly associated
to `𝓖` and `x` lies in the relative weak assassin `WeakAss_{X/Y}(𝓕)` of Stacks 0CV0 — which, the
fibres of `f` being locally Noetherian by Stacks 0CUY, is the set the source writes
`Ass_{X/Y}(𝓕)`.

This is the source's proof.  A commuting square of étale scheme charts over `f` through `x`
exists by `AlgebraicGeometry.Space.exists_chartDiagram_chartSchemeToPoints_eq`; on it the two
sides of the formula become the Zariski conditions of the scheme case by
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram`,
whose comparison of `(𝓕 ⊗_{𝒪_X} f^*𝓖)|_U` with `𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)` is
`AlgebraicGeometry.Space.nonempty_restrictToChart_tensor_modulePullback_chartDiagram` and whose
identification of the relative assassins is the two chart-diagram comparisons of
`StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin`
joined by Stacks 05F2, available because the chart morphism inherits local finite type from `f`.
The chart restrictions are quasi-coherent and, on the source, of finite type, the chart morphism
is locally of finite type, and the chart restriction of `𝓕` is flat over the target chart at the
chart point by Stacks 05VU; so the scheme case,
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType`, applies with no
further hypothesis. -/
@[stacks 0CVK]
theorem isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] [G.IsQuasicoherentOnSite]
    (x : points B S hS X.1)
    (hflat : IsFlatOverAtPoint B S hS X.2 f.hom F x) :
    IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G) x ↔
      (IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x) ∧
        x ∈ relativeWeaklyAssociatedPoints B S hS f F) := by
  obtain ⟨d, w, rfl⟩ := exists_chartDiagram_chartSchemeToPoints_eq B S hS f x
  have : (F ⊗ (modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_tensorObj_modulePullback_of_isQuasicoherentOnSite B S hS f F G
  obtain ⟨cmp⟩ := nonempty_restrictToChart_tensor_modulePullback_chartDiagram B S hS f F G
    inferInstance inferInstance inferInstance d
  have : LocallyOfFiniteType (chartDiagramSchemeMap B S hS f d) :=
    locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have : (chartDiagramRestrictSource B S hS f F d).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F inferInstance d.U
  have : (chartDiagramRestrictSource B S hS f F d).IsFiniteType :=
    isFiniteType_restrictToChart B S hS X F inferInstance
      (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType F inferInstance) d.U
  have : (chartDiagramRestrictTarget B S hS f G d).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS Y G inferInstance d.V
  have hrel : w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
        (chartDiagramRestrictSource B S hS f F d) ↔
      IsRelativeWeaklyAssociatedPoint B S hS f F (chartSchemeToPoints B S hS X.1 d.U w) := by
    refine ⟨isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram B S hS f F
      inferInstance d w, fun hx => ?_⟩
    rw [← _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d)]
    exact mem_relativeWeaklyAssociatedPoints_chartDiagram B S hS f F inferInstance d w hx
  exact isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram B S hS f F G d w cmp
    (Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d)
      (chartDiagramRestrictTarget B S hS f G d) w
      (isFlatOverAt_chartDiagram_of_mem_flatLocus B S hS f F d w hflat)) hrel

end AlgebraicGeometry.Space

end
