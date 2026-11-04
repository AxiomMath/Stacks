module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartSchemeBourbakiTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent

/-!
# Bourbaki's formula for a flat finite type module on an algebraic space, through a chart

Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `x` be a point of `X` with image `y`, let `𝓕` be a quasi-coherent
`𝒪_X`-module of finite type and let `𝓖` be a quasi-coherent `𝒪_Y`-module. Stacks 0CVK asserts
that if `𝓕` is flat at `x` over `Y`, then

`x ∈ WeakAss_X(𝓕 ⊗_{𝒪_X} f^*𝓖) ↔ y ∈ WeakAss_Y(𝓖) and x ∈ Ass_{X/Y}(𝓕)`.

This file runs the reduction of the source: on a commuting square of étale scheme charts over
`f` through `x` it applies the scheme case, Stacks 05IH, and transports the result back with
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram`.
Flatness is assumed at `x` in the sense of Stacks 05VV (membership of
`AlgebraicGeometry.Space.flatLocus`), and the chart-level flatness the scheme case consumes is
derived from it by the chart independence of Stacks 05VU.

The two biconditionals here also assume, in a hypothesis `hchart` on some chart diagram through
`x`, chart-level conditions the tag does not impose. The tag under exactly its own hypotheses is
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType`.

## Main results

* `AlgebraicGeometry.Space.locallyOfFiniteType_chartDiagramSchemeMap`: a morphism of algebraic
  spaces locally of finite type induces a morphism locally of finite type on the chart schemes
  of every chart diagram.
* `AlgebraicGeometry.Space.isFlatOverAt_chartDiagram_of_mem_flatLocus`: a module flat over `Y` at
  a point of `|X|` in the sense of Stacks 05VV has, on every chart diagram, a chart restriction
  flat over the target chart at every point of the source chart over that point (Stacks 05VU).
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_projective_stalk`:
  the biconditional of Stacks 0CVK under `hchart`, with a projective chart stalk.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finite_stalk`:
  the same with a chart stalk finite over the local ring of the target chart.

## Implementation notes

On a chart diagram `d`, with morphism of chart schemes `q : U ⟶ V` and a point `w` of `U` over
`x`, `hchart` asks for a finitely generated maximal ideal of the local ring of `V` at `q w`; an
isomorphism between the chart restriction of `𝓕 ⊗_{𝒪_X} f^*𝓖` and `𝓕|_U ⊗_{𝒪_U} q^*(𝓖|_V)`;
the agreement at `w` of the Zariski relative assassin of Stacks 05AV with the étale relative
weak assassin of Stacks 0CV0 at `x`; finite presentation of `q` and of `𝓕|_U`; and projectivity
(resp. finiteness) of the chart stalk of `𝓕`. The hypothesis `hpb` gives quasi-coherence of
`f^*𝓖` (Stacks 03GA).

The sets `AlgebraicGeometry.Space.weaklyAssociatedPoints` of Stacks 0CTX and
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints` of Stacks 0CV0 are `WeakAss_X` and
`WeakAss_{X/Y}`; they agree with the sets the source writes `Ass` because the fibres of `f` are
locally Noetherian (Stacks 0CUY).

## References

* [Stacks Project, Tag 0CVK](https://stacks.math.columbia.edu/tag/0CVK)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- A morphism of algebraic spaces which is locally of finite type induces a morphism of chart
schemes which is locally of finite type, on every chart diagram (Stacks 03XF (1)). -/
theorem locallyOfFiniteType_chartDiagramSchemeMap (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    LocallyOfFiniteType (chartDiagramSchemeMap B S hS f d) :=
  hf _ _ d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property d.comm.symm

/-- The point of an algebraic space cut out by a point of one of its étale scheme charts is the
same whether read by `AlgebraicGeometry.Space.pointOfEtaleChart` or by
`AlgebraicGeometry.Space.chartSchemeToPoints`. -/
private theorem pointOfEtaleChart_eq_chartSchemeToPoints
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS Z) (u : chartScheme U) :
    pointOfEtaleChart B S hS U u = chartSchemeToPoints B S hS Z U u :=
  (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS Z U u).symm

/-- Let `𝓕` be a quasi-coherent `𝒪_X`-module which is flat over `Y` at a point `x` of `|X|` in
the sense of Stacks 05VV, that is `x ∈ AlgebraicGeometry.Space.flatLocus`. Then on every chart
diagram `d` for `f`, at every point `w` of the source chart scheme over `x`, the chart
restriction `𝓕|_U` is flat over the target chart at `w` (Stacks 05VU). -/
theorem isFlatOverAt_chartDiagram_of_mem_flatLocus (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U)
    (hw : chartSchemeToPoints B S hS X.1 d.U w ∈ flatLocus B S hS X.2 f.hom F) :
    IsFlatOverAt (chartDiagramSchemeMap B S hS f d).toLRSHom.toShHom
      (chartDiagramRestrictSource B S hS f F d) w := by
  have h : IsFlatOverAtOnChartDiagram B S hS X.2 F d w :=
    (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d w).2
      (by rw [pointOfEtaleChart_eq_chartSchemeToPoints]; exact hw)
  exact h

/-- Bourbaki's formula of Stacks 0CVK, through a chart. Let `f : X ⟶ Y` be locally of finite
type, let `𝓕` be a quasi-coherent `𝒪_X`-module of finite type flat over `Y` at `x`, and let `𝓖`
be a quasi-coherent `𝒪_Y`-module. Under `hpb` and the chart-level conditions `hchart` on some
chart diagram through `x`, with a projective chart stalk of `𝓕`, `x` is weakly associated to
`𝓕 ⊗_{𝒪_X} f^*𝓖` exactly when its image is weakly associated to `𝓖` and
`x ∈ WeakAss_{X/Y}(𝓕)`. -/
theorem isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_projective_stalk (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hpb : HasLocalInverseImagePresentations B S hS f) [G.IsQuasicoherentOnSite]
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] (x : points B S hS X.1)
    (hflat : x ∈ flatLocus B S hS X.2 f.hom F)
    (hchart : ∃ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U),
      chartSchemeToPoints B S hS X.1 d.U w = x ∧
      (IsLocalRing.maximalIdeal ((chartScheme d.V).presheaf.stalk
        (chartDiagramSchemeMap B S hS f d w))).FG ∧
      Nonempty (restrictToChart B S hS X.2 (F ⊗ (modulePullback B S hS f).obj G) d.U ≅
        chartDiagramTensorPullback B S hS f F G d) ∧
      (w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
            (chartDiagramRestrictSource B S hS f F d) ↔
          IsRelativeWeaklyAssociatedPoint B S hS f F x) ∧
      LocallyOfFinitePresentation (chartDiagramSchemeMap B S hS f d) ∧
      (chartDiagramRestrictSource B S hS f F d).IsFinitePresentation ∧
      (let N := TopCat.Presheaf.stalk (C := Ab.{u})
            (chartDiagramRestrictSource B S hS f F d).val.presheaf w;
          letI : Module ((chartScheme d.V).presheaf.stalk
              (chartDiagramSchemeMap B S hS f d w)) N :=
            Module.compHom N ((chartDiagramSchemeMap B S hS f d).stalkMap w).hom;
          Module.Projective ((chartScheme d.V).presheaf.stalk
            (chartDiagramSchemeMap B S hS f d w)) N)) :
    IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G) x ↔
      (IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x) ∧
        x ∈ relativeWeaklyAssociatedPoints B S hS f F) := by
  obtain ⟨d, w, rfl, hfgV, ⟨cmp⟩, hrel, hlfp, hfp, hproj⟩ := hchart
  have := hlfp
  have := hfp
  have _ : LocallyOfFiniteType (chartDiagramSchemeMap B S hS f d) :=
    locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have := isQuasicoherentOnSite_tensorObj_modulePullback B S hS f hpb F G
  exact isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram B S hS f F G d w
    cmp
    (Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_projective_stalk
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d)
      (chartDiagramRestrictTarget B S hS f G d) w
      (isFlatOverAt_chartDiagram_of_mem_flatLocus B S hS f F d w hflat) hfgV hproj) hrel

/-- The same as
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_projective_stalk`,
with projectivity of the chart stalk of `𝓕` replaced by its finiteness over the local ring of
the target chart. -/
theorem isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finite_stalk (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hpb : HasLocalInverseImagePresentations B S hS f) [G.IsQuasicoherentOnSite]
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] (x : points B S hS X.1)
    (hflat : x ∈ flatLocus B S hS X.2 f.hom F)
    (hchart : ∃ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U),
      chartSchemeToPoints B S hS X.1 d.U w = x ∧
      (IsLocalRing.maximalIdeal ((chartScheme d.V).presheaf.stalk
        (chartDiagramSchemeMap B S hS f d w))).FG ∧
      Nonempty (restrictToChart B S hS X.2 (F ⊗ (modulePullback B S hS f).obj G) d.U ≅
        chartDiagramTensorPullback B S hS f F G d) ∧
      (w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
            (chartDiagramRestrictSource B S hS f F d) ↔
          IsRelativeWeaklyAssociatedPoint B S hS f F x) ∧
      LocallyOfFinitePresentation (chartDiagramSchemeMap B S hS f d) ∧
      (chartDiagramRestrictSource B S hS f F d).IsFinitePresentation ∧
      (let N := TopCat.Presheaf.stalk (C := Ab.{u})
            (chartDiagramRestrictSource B S hS f F d).val.presheaf w;
          letI : Module ((chartScheme d.V).presheaf.stalk
              (chartDiagramSchemeMap B S hS f d w)) N :=
            Module.compHom N ((chartDiagramSchemeMap B S hS f d).stalkMap w).hom;
          Module.Finite ((chartScheme d.V).presheaf.stalk
            (chartDiagramSchemeMap B S hS f d w)) N)) :
    IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G) x ↔
      (IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x) ∧
        x ∈ relativeWeaklyAssociatedPoints B S hS f F) := by
  obtain ⟨d, w, rfl, hfgV, ⟨cmp⟩, hrel, hlfp, hfp, hfin⟩ := hchart
  have := hlfp
  have := hfp
  have _ : LocallyOfFiniteType (chartDiagramSchemeMap B S hS f d) :=
    locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have := isQuasicoherentOnSite_tensorObj_modulePullback B S hS f hpb F G
  exact isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram B S hS f F G d w
    cmp
    (Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finite_stalk
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d)
      (chartDiagramRestrictTarget B S hS f G d) w
      (isFlatOverAt_chartDiagram_of_mem_flatLocus B S hS f F d w hflat) hfgV hfin) hrel

end AlgebraicGeometry.Space

end
