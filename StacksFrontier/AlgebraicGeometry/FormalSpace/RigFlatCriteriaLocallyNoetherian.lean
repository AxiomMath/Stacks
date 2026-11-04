module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagramNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.RingTheory.Rig.FlatIsLocal
public import StacksFrontier.RingTheory.Rig.FlatIsLocalRefined

/-!
# Rig-flatness of a morphism of locally Noetherian formal algebraic spaces is étale local

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. Stacks 0GGY says that the following are
equivalent:

1. `f` is rig-flat (Definition 0GGX);
2. every commutative square whose verticals are affine charts of `X` and `Y` representable by
   algebraic spaces and étale carries a rig-flat arrow of `WAdm^Noeth` on its top side;
3. there are an affine étale covering `{Yⱼ ⟶ Y}` and affine étale coverings
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` such that each `Xⱼᵢ ⟶ Yⱼ` comes from a rig-flat map of `WAdm^Noeth`;
4. there are an affine étale covering `{Xᵢ ⟶ X}` and factorizations `Xᵢ ⟶ Yᵢ ⟶ Y` through
   affine formal algebraic spaces representable étale over `Y` such that each `Xᵢ ⟶ Yᵢ` comes
   from a rig-flat map of `WAdm^Noeth`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigFlatOnCharts_iff_hasPropertyOnAffineChartMap`: the chart
  condition `IsRigFlatOnCharts` of conditions (3) and (4) is the chart condition of Stacks 0ANG
  for the class `WAdm^Noeth` and rig-flatness.
* `AlgebraicGeometry.FormalSpace.isRigFlat_tfae_of_isLocallyNoetherian`: **Stacks 0GGY**.

## Implementation notes

As in the source, (1) ⟺ (2) is Definition 0GGX
(`AlgebraicGeometry.FormalSpace.isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`), and the
equivalence of (2), (3) and (4) is the variant of Stacks 0ANG for locally Noetherian formal
algebraic spaces (Remark 0ANI) applied to rig-flatness, a local property of arrows of
`WAdm^Noeth` by Stacks 0GGU (`Rig.rigFlat_isLocalNoetherian`, with the invariance under
isomorphisms `Rig.rigFlat_isomorphismInvariant`):

* (2) ⟹ (3) is
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`,
  with Stacks 0AJ3 supplied by
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`;
* (3) ⟹ (4) is
  `AlgebraicGeometry.FormalSpace.hasRigFlatSourceCovering_of_hasRigFlatTargetCovering`;
* (4) ⟹ (2) is
  `FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian`.

## References

* [Stacks Project, Tag 0GGY](https://stacks.math.columbia.edu/tag/0GGY)
* [Stacks Project, Tag 0GGX](https://stacks.math.columbia.edu/tag/0GGX)
* [Stacks Project, Tag 0GGU](https://stacks.math.columbia.edu/tag/0GGU)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chart condition `IsRigFlatOnCharts` of conditions (3) and (4) of Stacks 0GGY is the
chart condition of Stacks 0ANG for the class `WAdm^Noeth` of Noetherian adic topological rings
and the property "rig-flat". -/
theorem isRigFlatOnCharts_iff_hasPropertyOnAffineChartMap {U V : FppfSheaf B S hS}
    (t : U ⟶ V) :
    IsRigFlatOnCharts B S hS t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          Rig.RingHom.IsRigFlat φ) t := by
  constructor
  · intro h A R _ _ _ _ _ _ _ _ ⟨hAadic, hAnoeth⟩ ⟨hRadic, hRnoeth⟩ hA D E eU eV g hg
    exact h A R hAadic hRadic hA D E eU eV g hg
  · intro h A R _ _ _ _ _ _ _ _ _ _ hAadic hRadic hA D E eU eV g hg
    exact h A R ⟨hAadic, inferInstance⟩ ⟨hRadic, inferInstance⟩ hA D E eU eV g hg

/-- **Stacks 0GGY.** For a morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces
over `S`, the following are equivalent: `f` is rig-flat (Definition 0GGX); every commutative
square whose verticals are affine formal algebraic spaces representable étale over `X` and `Y`
carries a rig-flat arrow of `WAdm^Noeth` on its top side; there are an affine étale covering of
`Y` and affine étale coverings of the fibre products of its members with `X` whose members map
to the corresponding chart of `Y` by rig-flat maps of `WAdm^Noeth`; there is an affine étale
covering of `X` whose members factor through affine formal algebraic spaces representable étale
over `Y` by rig-flat maps of `WAdm^Noeth`. -/
@[stacks 0GGY]
theorem isRigFlat_tfae_of_isLocallyNoetherian {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [IsRigFlat B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
          (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
            [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
            Rig.RingHom.IsRigFlat φ) f,
        HasRigFlatTargetCovering B S hS f,
        HasRigFlatSourceCovering B S hS f] := by
  tfae_have 1 ↔ 2 := isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram f
  tfae_have 2 → 3 := fun h ↦ by
    obtain ⟨J, V, v, hV, hcharts⟩ := hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
      _ _ f hY.1
      (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
        v' f hY.1 hV' hX.1) h
    refine ⟨J, V, v, hV, fun j ↦ ?_⟩
    obtain ⟨I, U, w, hU, hP⟩ := hcharts j
    exact ⟨I, U, w, hU, fun i ↦
      (isRigFlatOnCharts_iff_hasPropertyOnAffineChartMap B S hS _).mpr (hP i)⟩
  tfae_have 3 → 4 := hasRigFlatSourceCovering_of_hasRigFlatTargetCovering B S hS f
  tfae_have 4 → 2 := fun ⟨I, U, a, hU, hfac⟩ ↦
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian B S hS _
      Rig.rigFlat_isLocalNoetherian Rig.rigFlat_isomorphismInvariant f hX hY
      ⟨I, U, a, hU, fun i ↦ by
        obtain ⟨V, b, t, hV, hb, hcomm, ht⟩ := hfac i
        exact ⟨V, b, t, hV, hb, hcomm,
          (isRigFlatOnCharts_iff_hasPropertyOnAffineChartMap B S hS t).mp ht⟩⟩
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
