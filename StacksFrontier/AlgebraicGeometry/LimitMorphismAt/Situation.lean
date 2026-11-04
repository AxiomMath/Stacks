module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.NoetherianSystem
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteTypeModel

/-!
# Good diagrams over a limit of Noetherian schemes with affine transitions

Let `S = lim S_i` be a directed limit of Noetherian schemes with affine transition morphisms, as
packaged by `AlgebraicGeometry.LimitNoetherianSituation`. This file introduces the scheme `S_i`
at a stage of the system and the projection `S ⟶ S_i`, and computes the two projections of the
morphism `X ⟶ S ×_{S_i} W` induced by a good diagram
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram`.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.stage` and
  `AlgebraicGeometry.LimitNoetherianSituation.proj`: the scheme `S_i` at a stage of the system
  and the projection `S ⟶ S_i` from the limit.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.induced_fst` and
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.induced_snd`: the two projections of
  the induced morphism `X ⟶ S ×_{S_i} W` of a good diagram are `f` and `X ⟶ W`.

## Implementation notes

The finite-type, quasi-compactness and closed-immersion fields of a good diagram are made
instances. The transition morphism `S_{i'} ⟶ S_i` for `i ≤ i'` is the image under `system` of
the morphism `op i' ⟶ op i` of the opposite preorder, and the limit together with its
projections is a `CategoryTheory.Limits.Cone` with an `IsLimit`. The index type `I : Type v`
lives in a universe independent of the scheme universe `u`.

`stage` and `proj` are `abbrev`s, so they are reducibly `D.system.obj (op i)` and
`D.limitCone.π.app (op i)`, and a statement written in either spelling is the same statement.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM).
* [Stacks Project, Tag 0CNP](https://stacks.math.columbia.edu/tag/0CNP).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- The scheme `S_i` at a stage of the system. -/
abbrev stage (D : LimitNoetherianSituation.{v, u} I) (i : I) : Scheme.{u} :=
  D.system.obj (op i)

/-- The projection `S ⟶ S_i` from the limit to a stage. -/
abbrev proj (D : LimitNoetherianSituation.{v, u} I) (i : I) : D.limitScheme ⟶ D.stage i :=
  D.limitCone.π.app (op i)

namespace GoodDiagram

variable {D : LimitNoetherianSituation.{v, u} I} {X : Scheme.{u}} {f : X ⟶ D.limitScheme}

attribute [instance] GoodDiagram.locallyOfFiniteType GoodDiagram.quasiCompact
  GoodDiagram.isClosedImmersion

/-- The first projection of the induced morphism `X ⟶ S ×_{S_i} W` of a good diagram is `f`. -/
lemma induced_fst (G : GoodDiagram D f) :
    G.induced ≫ pullback.fst (D.proj G.index) G.modelMap = f :=
  pullback.lift_fst _ _ _

/-- The second projection of the induced morphism `X ⟶ S ×_{S_i} W` of a good diagram is the
morphism `X ⟶ W` to the model. -/
lemma induced_snd (G : GoodDiagram D f) :
    G.induced ≫ pullback.snd (D.proj G.index) G.modelMap = G.toModel :=
  pullback.lift_snd _ _ _

end GoodDiagram

end LimitNoetherianSituation

end AlgebraicGeometry
