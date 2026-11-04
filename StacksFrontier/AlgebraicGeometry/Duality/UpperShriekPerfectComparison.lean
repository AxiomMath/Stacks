module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekComparisonCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# The comparison `μ_{f,K}` for a perfect morphism

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a perfect morphism of `FTS S`. The map
`μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ⟶ f^!K` of [Stacks, Tag 0B6T] is an isomorphism for every
`K ∈ D⁺_QCoh(𝒪_Y)`; this is part (e) of [Stacks, Tag 0B6U].

## Main results

* `Stacks.Duality.isIso_upperShriekCompareWithPullback`: for a perfect `f`, the map `μ_{f,K}` is
  an isomorphism for every `K ∈ D⁺_QCoh(𝒪_Y)`.
* `Stacks.Duality.nonempty_upperShriek_iso_pullback_tensor`: for a perfect `f` and
  `K ∈ D⁺_QCoh(𝒪_Y)`, `Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K`.

## References

* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0B6T](https://stacks.math.columbia.edu/tag/0B6T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-- Let `S` be a Noetherian scheme and `f : X ⟶ Y` a perfect morphism of `FTS S`. Then the map
`μ_{f,K} : Lf^*K ⊗ᴸ_{𝒪_X} f^!𝒪_Y ⟶ f^!K`, `Stacks.Duality.upperShriekCompareWithPullbackCanonical`,
is an isomorphism for all `K ∈ D⁺_QCoh(𝒪_Y)`. Here `f^!` and `μ_{f,K}` are computed at an
arbitrary compactification `j`. -/
@[stacks 0B6U "part (e)"]
theorem isIso_upperShriekCompareWithPullback [Perfect f.left]
    (j : CompactificationOf (Over.mk f.left)) (K : quasiCoherentDerivedCategory Y.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (upperShriekCompareWithPullbackCanonical f j K) :=
  (isIso_upperShriekCompareWithPullback_iff f j K).2 (isIso_map_comparisonMap_of_perfect f j K hK)

/-- For a perfect morphism `f` of `FTS S` and `K ∈ D⁺_QCoh(𝒪_Y)`, there is an isomorphism
`Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K`, where `f^!` is computed at an arbitrary compactification `j`. -/
theorem nonempty_upperShriek_iso_pullback_tensor [Perfect f.left]
    (j : CompactificationOf (Over.mk f.left)) (K : quasiCoherentDerivedCategory Y.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    Nonempty (((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K)).obj
          ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)) ≅
        (upperShriek f j).obj K) :=
  have := isIso_upperShriekCompareWithPullback f j K hK
  ⟨asIso (upperShriekCompareWithPullbackCanonical f j K)⟩

end Stacks.Duality

end
