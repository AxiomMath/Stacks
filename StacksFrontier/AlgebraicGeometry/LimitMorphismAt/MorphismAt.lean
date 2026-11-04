module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.ImageSystem

/-!
# Uniqueness of a morphism between the image systems of two good diagrams, separated case

A morphism `f : X ⟶ Y` of schemes over the limit `S`, together with good diagrams for `X` and
for `Y`, gives two inverse systems of scheme-theoretic images. What it means for `f` to be
induced by a morphism of those systems on a common tail is
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt`, of
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystem.lean`. This file proves that such a
morphism is unique as soon as the model of the target is separated.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.app_eq`: two such morphisms agree at
  every stage, *immediately* and not merely eventually, provided the model of the target good
  diagram is separated over its stage and the stage map of the source is quasi-compact.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ext_of_isSeparated`: the same conclusion
  as an equality of the two natural transformations.

## Route

Uniqueness is `AlgebraicGeometry.eq_of_isSchemeTheoreticallyDominant` applied with `p` the cone
leg `X ⟶ X_{i'}`, which has trivial kernel by
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isSchemeTheoreticallyDominant_π`, and
with the separated morphism `Y_{i'} ⟶ S_{i'}`. The first axiom of `MorphismAt` supplies the
agreement over `S_{i'}` and the second the agreement after `p`, so no constructibility or
Noetherian argument is needed in this case. The source's own uniqueness statement, which assumes
nothing about the model, needs both: the equalizer is then only locally closed, and one has to
pass to a later stage for it to absorb the transition map; that argument is
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_of_exists_eq_app` of
`StacksFrontier/AlgebraicGeometry/GoodDiagramLimit/Uniqueness.lean`.

## Universe situation

The index type is at a universe `v` independent of the scheme universe `u`, as in
`Situation.lean` and `ImageSystem.lean`.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR), the statement of what is
  being asserted to exist and to be eventually unique.

## Not done here

Existence of a morphism of systems is
`AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt_of_isLimit` of
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystem.lean`, and the eventual-uniqueness
half of Stacks 0CNR with no hypothesis on the models is
`AlgebraicGeometry.LimitNoetherianSituation.eventually_eq_morphismAt_of_isLimit` there. What is
proved here is the separated case of uniqueness, in which the conclusion holds at every stage
rather than eventually.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

namespace MorphismAt

variable {D : LimitNoetherianSituation.{v, u} I} {X Y : Scheme.{u}}
  {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme} {f : X ⟶ Y}
  {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
  {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}

/-- **Uniqueness of a morphism of image systems, separated case.** If the model of the target
good diagram is separated over its stage, then two morphisms of image systems inducing the same
morphism `f` on the limits agree at every stage above `i₀` — not merely at all sufficiently late
stages, as Stacks 0CNR asserts in general. -/
theorem app_eq [IsSeparated GY.modelMap] (F F' : MorphismAt D f GX GY i₀ hX hY)
    (j : Over (op i₀))
    [QuasiCompact (GX.stageMap ((Over.map (homOfLE hX).op).obj j))] :
    F.maps.app j = F'.maps.app j :=
  eq_of_isSchemeTheoreticallyDominant
    (GX.isSchemeTheoreticallyDominant_π ((Over.map (homOfLE hX).op).obj j))
    (GY.isSeparated_imageι_comp_fst ((Over.map (homOfLE hY).op).obj j))
    ((F.over_base j).trans (F'.over_base j).symm)
    ((F.induces j).trans (F'.induces j).symm)

/-- In the separated case the two morphisms of image systems are equal, not merely equal at each
stage. -/
theorem ext_of_isSeparated [IsSeparated GY.modelMap] (F F' : MorphismAt D f GX GY i₀ hX hY)
    (hqc : ∀ j : Over (op i₀),
      QuasiCompact (GX.stageMap ((Over.map (homOfLE hX).op).obj j))) :
    F.maps = F'.maps := by
  ext j
  have := hqc j
  exact F.app_eq F' j

end MorphismAt

end AlgebraicGeometry.LimitNoetherianSituation
