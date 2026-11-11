module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagramNoetherian
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined

/-!
# Flatness of a morphism of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCD** says that the following
four conditions are equivalent:

1. `f` is flat (Definition 0GCC);
2. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   flat map in `WAdm^{Noeth}`;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` corresponding to a flat map
   in `WAdm^{Noeth}`;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space representable by algebraic spaces
   and étale over `Y` and `Xᵢ ⟶ Yᵢ` corresponding to a flat map in `WAdm^{Noeth}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFlat_tfae_of_isLocallyNoetherian`: **Stacks 0GCD**.

## Implementation notes

The source's proof reads: (1) and (2) agree by Definition 0GCC, and the rest is Remark 0ANI —
the variant of Stacks 0ANG for morphisms of locally Noetherian formal algebraic spaces — applied
to flatness, which is a local property of arrows of `WAdm^{Noeth}` by Stacks 0GC9. The four legs
used below are each proved in the library with no further input:

* (1) ⟺ (2) is `AlgebraicGeometry.FormalSpace.isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`,
  which only repackages the binders of Definition 0GCC.
* (2) ⟹ (3) is
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`, whose
  fibre-product input is Stacks 0AJ3 for a chart of the target,
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`.
* (3) ⟹ (4) is `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_afterTargetCover`.
* (4) ⟹ (2) is
  `FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian`
  (Remark 0ANI, condition (3) of Stacks 0ANG implies condition (1)), which carries out the
  refinement of the covering against a square and the reading of the locality axioms through
  Stacks 0AN8 and Stacks 0AN9 itself. The local property is
  `TopologicalRing.flat_isLocalNoetherian` (Stacks 0GC9) and its invariance under isomorphism of
  source and target is `TopologicalRing.flat_isomorphismInvariant`.

The local Noetherianity of `X` and `Y` enters twice: through the underlying formal algebraic
spaces in Stacks 0AJ3, and through the Noetherian adic presentations of the charts in Remark
0ANI.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0GC9](https://stacks.math.columbia.edu/tag/0GC9)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GCD.** For a morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces
over `S` the following are equivalent:

1. `f` is flat in the sense of Definition 0GCC;
2. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` carries a flat map of Noetherian adic topological rings on
   `U ⟶ V`;
3. there are an affine étale covering `{Yⱼ ⟶ Y}` and affine étale coverings `{Xⱼᵢ ⟶ Yⱼ ×_Y X}`
   with each `Xⱼᵢ ⟶ Yⱼ` corresponding to a flat map of Noetherian adic topological rings;
4. there are an affine étale covering `{Xᵢ ⟶ X}` and factorizations `Xᵢ ⟶ Yᵢ ⟶ Y` through
   affine formal algebraic spaces representable étale over `Y` with each `Xᵢ ⟶ Yᵢ`
   corresponding to a flat map of Noetherian adic topological rings.

As in the source, (1) and (2) agree by Definition 0GCC, and (2), (3), (4) are the three
conditions of the Noetherian variant of Stacks 0ANG (Remark 0ANI) for flatness, a local property
of arrows of `WAdm^{Noeth}` by Stacks 0GC9. The only hypotheses are those of the source, that
`X` and `Y` are locally Noetherian (Stacks 0AKY); the inputs that
`AlgebraicGeometry.FormalSpace.isFlat_tfae` takes as hypotheses are all proved here. -/
@[stacks 0GCD "all four conditions, for a morphism of locally Noetherian formal algebraic \
spaces as in the source; Stacks 0AJ3, the refinement of Remark 0ANI and the locality of \
flatness (Stacks 0GC9) are proved, not assumed"]
theorem isFlat_tfae_of_isLocallyNoetherian {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [IsFlat B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f] := by
  tfae_have 1 ↔ 2 := isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f hY.1
    (fun _ v hV _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v f hY.1 hV hX.1) h
  tfae_have 3 → 4 := hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f
  tfae_have 4 → 2 :=
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian B S hS
      TopologicalRing.IsFlatHom TopologicalRing.flat_isLocalNoetherian
      (TopologicalRing.flat_isomorphismInvariant TopologicalRing.IsNoetherianAdic) f hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
