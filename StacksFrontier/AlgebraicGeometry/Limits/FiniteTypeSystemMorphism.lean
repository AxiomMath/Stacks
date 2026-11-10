module

public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemLimit

/-!
# Tag 0CNR: morphisms of the systems of finite type models over a limit

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms and let `f : X ⟶ Y` be a morphism of schemes quasi-separated and of finite
type over `S`. Given good diagrams for `X ⟶ S` and `Y ⟶ S` (Tag 0CNN), the schemes `X` and `Y`
are the limits of the associated systems `(X_i)` and `(Y_i)` of scheme-theoretic images
(Tag 0CNQ). This file records that `f` is then induced by a morphism of those systems on a
sufficiently late common tail, uniquely at sufficiently late stages.

This is Stacks Tag 0CNR. The mathematics is in
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystem.lean`, where it is stated with
Tag 0CNQ for the source good diagram as an explicit hypothesis; that file is below the proof of
Tag 0CNQ in the import order, so this module exists only to discharge the hypothesis.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt`: Tag 0CNR, existence.
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_eq_morphismAt`: Tag 0CNR, eventual
  uniqueness.

## No hypothesis on the index

The two results below carry no condition relating the index universe to the universe of the
schemes — no cofinality hypothesis, and in particular not
`CategoryTheory.FinallySmall.{u} I`. The two
halves of Tag 01ZC, which are what the proof descends along, do need such a condition in general
(over `Ordinal.{u}` there is a system of nonempty affine schemes with affine transitions whose
limit is empty, `StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean`); they do not
need it for the system of scheme-theoretic images of a good diagram, because the projections
`X ⟶ X_{i'}` out of that limit are scheme-theoretically dominant. See the module docstring of
`StacksFrontier/AlgebraicGeometry/Limits/SmallDominantIndex.lean`.

Nor does `eventually_eq_morphismAt` carry instance hypotheses on `pX`: quasi-compactness,
quasi-separatedness and
local finiteness of type of `pX` are consequences of the existence of the good diagram `GX`, and
are derived inside the proof.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **Stacks Project, Tag 0CNR, existence.** A morphism of schemes over the limit is
realized by a morphism of the systems of images on a sufficiently late common tail. -/
@[stacks 0CNR "existence"]
theorem exists_morphismAt (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY) :
    ∃ (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀),
      Nonempty (MorphismAt D f GX GY i₀ hX hY) :=
  exists_morphismAt_of_isLimit D f hf GX GY (GoodDiagram.isLimit_imageCone D pX GX)

/-- **Stacks Project, Tag 0CNR, eventual uniqueness.** Two system morphisms inducing the same
limit morphism agree at every sufficiently late stage. -/
@[stacks 0CNR "eventual uniqueness"]
theorem eventually_eq_morphismAt (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_hi : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)) (_hj : i₃ ≤ unop j.left),
        F.maps.app j = G.maps.app j :=
  have _ := GX.quasiCompact_toLimit
  have _ := GX.locallyOfFiniteType_toLimit
  have _ := GX.quasiSeparated_toLimit
  eventually_eq_morphismAt_of_isLimit D f GX GY i₀ hX hY F G
    (GoodDiagram.isLimit_imageCone D pX GX)

end LimitNoetherianSituation

end AlgebraicGeometry
