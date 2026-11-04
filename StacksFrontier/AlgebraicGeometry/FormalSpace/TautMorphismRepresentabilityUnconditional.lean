module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableAfterSourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautChartRepresentability

/-!
# Taut ring maps and representability by algebraic spaces, with no hypotheses

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S`. **Stacks 0ANK** says that the
following are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has `U ⟶ V` given by a taut continuous homomorphism of
   countably indexed weakly admissible topological rings;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uᵢ ⟶ Vⱼ` given by such a taut map;
3. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Uᵢ ⟶ Vᵢ` given by such a taut map;
4. `f` is representable by algebraic spaces.

This file states that equivalence with none of the five inputs that
`AlgebraicGeometry.FormalSpace.isTaut_tfae_isRepresentableByAlgebraicSpaces` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/TautMorphismRepresentability.lean` carries as
hypotheses; it lies downstream of the results discharging them.

## Main results

* `tfae_isTautOnEveryAffineEtaleDiagram_isRepresentableByAlgebraicSpaces`: **Stacks 0ANK**, with
  no hypotheses beyond those of the source.

## Implementation notes

The cycle is `(1) ⟹ (2) ⟹ (3) ⟹ (4) ⟹ (1)`, as in
`StacksFrontier/AlgebraicGeometry/FormalSpace/TautMorphismRepresentability.lean`, with the five
inputs of the source discharged as follows. The étale case of Stacks 0AJH, which the first two
rest on, is `AlgebraicGeometry.FormalSpace.representableEtaleOverAffineIsFormal`.

* Stacks 0AJ3, for the fibre product `V ×_Y X` of a chart of the target with `f` in the step
  (1) ⟹ (2), is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_etale`
  from the étale case of Stacks 0AJH.
* The implication (2) ⟹ (1) of Stacks 0AKX for countable indexing, which makes the charts of
  condition (3) countably indexed and so presented by rings of the class, is
  `hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`.
* The equivalence of conditions (1) and (3) of Stacks 0AN5 on countably indexed charts is
  `isRepresentableByAlgebraicSpacesULift_iff_hasTautOnAffineChartMap`.
* Stacks 0AQ0 enters only the step (4) ⟹ (1), which is
  `isTautOnEveryAffineEtaleDiagram_of_isRepresentableByAlgebraicSpaces`.
* The implication (5) ⟹ (1) of Stacks 0AN4, in the step (3) ⟹ (4), is
  `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp`: each
  composite `Uᵢ ⟶ X ⟶ Y` is `Uᵢ ⟶ Vᵢ ⟶ Y`, representable by algebraic spaces by Stacks 0AN5 and
  Stacks 0APY, and representability descends along the étale covering `{Uᵢ ⟶ X}`.

## References

* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ANK.** Let `f : X ⟶ Y` be a morphism of locally countably indexed formal
algebraic spaces over `S`. The following are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has `U ⟶ V` given by a taut continuous homomorphism of
   countably indexed weakly admissible topological rings;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uᵢ ⟶ Vⱼ` given by such a taut map;
3. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Uᵢ ⟶ Vᵢ` given by such a taut map;
4. `f` is representable by algebraic spaces. -/
@[stacks 0ANK]
theorem tfae_isTautOnEveryAffineEtaleDiagram_isRepresentableByAlgebraicSpaces
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y) :
    List.TFAE
      [ IsTautOnEveryAffineEtaleDiagram B S hS f,
        IsTautAfterTargetCover B S hS f,
        IsTautAfterSourceCover B S hS f,
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom ] := by
  have hEt : RepresentableEtaleOverAffineIsFormal B S hS :=
    representableEtaleOverAffineIsFormal B S hS
  have h0AKX : ∀ {Z : FppfSheaf B S hS}, IsLocallyCountablyIndexed B S hS Z →
      HasAffineEtaleChartProperty B S hS Z (IsCountablyIndexed B S hS) := fun hZ ↦
    (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem B S hS _ hZ.1 _
      (Or.inl rfl)).2 hZ.2
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f hY.1
      (fun V v hV hv ↦
        isFormalAlgebraicSpace_pullback_chart_of_etale B S hS hEt hX.1 hY.1 V v hV hv) h
  tfae_have 2 → 3 := fun h ↦
    hasPropertyAfterSourceCover_of_afterTargetCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f h
  tfae_have 3 → 4 := by
    rintro ⟨I, U, a, hUcover, hfac⟩
    choose W b t hWaffine hWetale hWsquare hWproperty using hfac
    refine isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp B S hS f hX.1.1 hY.1 U a
      hUcover.2.1 hUcover.2.2 fun i ↦ ?_
    rw [hWsquare i]
    refine Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ ?_ (hWetale i).1
    exact (isRepresentableByAlgebraicSpacesULift_iff_hasTautOnAffineChartMap B S hS (t i)
      (h0AKX hX (U i) (a i) (hUcover.1 i) (hUcover.2.1 i))
      (h0AKX hY (W i) (b i) (hWaffine i) (hWetale i))).2 (hWproperty i)
  tfae_have 4 → 1 := fun hf ↦
    isTautOnEveryAffineEtaleDiagram_of_isRepresentableByAlgebraicSpaces B S hS f hY.1 hf
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
