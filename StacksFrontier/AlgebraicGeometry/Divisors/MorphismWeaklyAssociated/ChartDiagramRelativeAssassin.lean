module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTarget
public import
  StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionRepresented

/-!
# The Zariski relative assassin on a chart diagram and the relative weak assassin

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `𝓕` be a quasi-coherent
`𝒪_X`-module and let `d` be a commuting square of étale scheme charts over `f`, with source
chart `U`, target chart `V` and vertical morphism of chart schemes `q : U ⟶ V`. A point `w` of
`U` lying in the Zariski relative assassin `Ass_{U/V}(𝓕|_U)` of Stacks 05AT then cuts out a
point of the relative weak assassin `WeakAss_{X/Y}(𝓕)` of Stacks 0CV0, and conversely a point
of `U` cutting out a point of `WeakAss_{X/Y}(𝓕)` lies in the relative weak assassin
`WeakAss_{U/V}(𝓕|_U)` of Stacks 05AV.

## Main results

* `AlgebraicGeometry.relativeWeaklyAssociatedPoints_congr`: isomorphic `𝒪_X`-modules have the same
  relative weak assassin.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram`:
  the first implication above.
* `AlgebraicGeometry.Space.mem_relativeWeaklyAssociatedPoints_chartDiagram`: the converse, the
  implication (5) ⟹ (2) of Stacks 0CUZ at an arbitrary chart square.

## References

* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 0589](https://stacks.math.columbia.edu/tag/0589)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Isomorphic `𝒪_X`-modules have the same relative weak assassin of Stacks 05AV. -/
theorem relativeWeaklyAssociatedPoints_congr {X S : Scheme.{u}} (f : X ⟶ S)
    {F F' : X.Modules} (e : F ≅ F') :
    relativeWeaklyAssociatedPoints f F = relativeWeaklyAssociatedPoints f F' :=
  Set.iUnion_congr fun s ↦ congrArg _ (Set.ext fun t ↦
    Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso
      ((Scheme.Modules.pullback (f.fiberι s)).mapIso e) t)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The square of a chart diagram, with the source chart replaced by the represented space, commutes
over `f`. -/
private theorem representedSpaceMap_comp_chartToSpace_eq (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    representedSpaceMap B S hS d.g ≫ chartToSpace B S hS Y d.V =
      chartToSpace B S hS X d.U ≫ f :=
  ObjectProperty.hom_ext _ d.comm.symm

/-- Restricting to the chart and passing to the represented chart module do not change the
relative weak assassin of the chart morphism. -/
private theorem relativeWeaklyAssociatedPoints_chartDiagramRestrictSource_eq (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) =
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        (chartDiagramSchemeMap B S hS f d)
        (representedChartModule B S hS
          ((modulePullback B S hS (chartToSpace B S hS X d.U)).obj F)) :=
  _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints_congr
    (chartDiagramSchemeMap B S hS f d)
    (restrictToChartIsoChartSpaceIdEtaleChart B S hS X d.U F hF)

/-- A point of the Zariski relative assassin of a chart diagram lies in the relative weak
assassin of Stacks 0CV0. Let `d` be a commuting square of étale scheme charts over
`f : X ⟶ Y` with vertical morphism of chart schemes `q`, and let `𝓕` be a quasi-coherent
`𝒪_X`-module. A point `w` of the source chart scheme lying in the relative assassin
`Ass_{U/V}(𝓕|_U)` of Stacks 05AT cuts out a point of `WeakAss_{X/Y}(𝓕)`. -/
theorem isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U)
    (hw : w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
      (chartDiagramRestrictSource B S hS f F d)) :
    IsRelativeWeaklyAssociatedPoint B S hS f F (chartSchemeToPoints B S hS X.1 d.U w) := by
  set N := (modulePullback B S hS (chartToSpace B S hS X d.U)).obj F
  have hNqc : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X d.U) F hF
  set w' := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).symm w
  have hw'scheme : pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U) w' = w :=
    (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).apply_symm_apply w
  have hmem : pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U) w' ∈
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        (chartDiagramSchemeMap B S hS f d) (representedChartModule B S hS N) := by
    rw [hw'scheme,
      ← relativeWeaklyAssociatedPoints_chartDiagramRestrictSource_eq B S hS f F hF d]
    exact _root_.AlgebraicGeometry.relativeAssassin_subset_relativeWeaklyAssociatedPoints
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) hw
  have hrep := isRelativeWeaklyAssociatedPoint_of_mem_relativeWeaklyAssociatedPoints
    B S hS d.g N hNqc w' hmem
  have htarget := isRelativeWeaklyAssociatedPoint_comp_of_isEtale B S hS
    (representedSpaceMap B S hS d.g) (chartToSpace B S hS Y d.V)
    (isEtale_chartToSpace B S hS Y d.V) N hrep
  rw [representedSpaceMap_comp_chartToSpace_eq B S hS f d] at htarget
  have hsrc := (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS
    (chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS X d.U) f F w').1 htarget
  exact (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 d.U w) ▸ hsrc

/-- Let `d` be a commuting square of étale scheme charts over `f : X ⟶ Y` with vertical morphism
of chart schemes `q`, and let `𝓕` be a quasi-coherent `𝒪_X`-module. If a point `w` of the source
chart scheme cuts out a point of the relative weak assassin `WeakAss_{X/Y}(𝓕)` of Stacks 0CV0,
then `w` lies in the relative weak assassin `WeakAss_{U/V}(𝓕|_U)` of Stacks 05AV of the chart
morphism. -/
theorem mem_relativeWeaklyAssociatedPoints_chartDiagram (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U)
    (hw : IsRelativeWeaklyAssociatedPoint B S hS f F (chartSchemeToPoints B S hS X.1 d.U w)) :
    w ∈ _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) := by
  set N := (modulePullback B S hS (chartToSpace B S hS X d.U)).obj F
  have hNqc : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X d.U) F hF
  set w' := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).symm w
  have hw'scheme : pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U) w' = w :=
    (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj d.U)).apply_symm_apply w
  have hw2 : IsRelativeWeaklyAssociatedPoint B S hS f F
      (pointsMap B S hS (chartSpace B S hS X d.U).1
        (chartToSpace B S hS X d.U).hom w') := by
    exact (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 d.U w) ▸ hw
  have hsrc : IsRelativeWeaklyAssociatedPoint B S hS
      (chartToSpace B S hS X d.U ≫ f) N w' :=
    (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS
      (chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS X d.U) f F w').2 hw2
  rw [← representedSpaceMap_comp_chartToSpace_eq B S hS f d] at hsrc
  have hrep := isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale B S hS
    (representedSpaceMap B S hS d.g) (chartToSpace B S hS Y d.V)
    (isEtale_chartToSpace B S hS Y d.V) N hsrc
  have hmem := (isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints
    B S hS d.g N hNqc w').1 hrep
  rwa [relativeWeaklyAssociatedPoints_chartDiagramRestrictSource_eq B S hS f F hF d,
    ← hw'scheme]

end AlgebraicGeometry.Space

end
