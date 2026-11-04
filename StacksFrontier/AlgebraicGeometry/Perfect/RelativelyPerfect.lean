module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The relative descent situation

Fix a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms and a chosen limit, and over one fixed stage a flat morphism of finite
presentation. Its pullbacks to later stages and to the limit form the relative descent
situation.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation` packages the inverse system, its limit, and the
  flat finitely presented morphism at the fixed stage.
* `AlgebraicGeometry.RelativeDescentSituation.schemeAt` and
  `AlgebraicGeometry.RelativeDescentSituation.limitScheme` are its base changes to a later stage
  and to the limit.
* `AlgebraicGeometry.RelativeDescentSituation.transition` and
  `AlgebraicGeometry.RelativeDescentSituation.projection` are the canonical morphisms between
  these base changes.
* `AlgebraicGeometry.RelativeDescentSituation.toFixedStage` and
  `AlgebraicGeometry.RelativeDescentSituation.limitToFixedStage` are the canonical maps to `X₀`.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

/-- The relative descent situation: a directed inverse limit of
quasi-compact, quasi-separated schemes with affine transition maps, together with a flat
morphism of finite presentation over a fixed stage. -/
@[stacks 0DI6]
structure RelativeDescentSituation (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)] where
  /-- The directed inverse system, its chosen limit, and its fixed index. -/
  descent : DescentSituation.{v, u} I
  /-- The scheme `X₀` over the fixed stage `S₀`. -/
  X₀ : Over (descent.system.obj (op descent.base))
  /-- The morphism `X₀ ⟶ S₀` is flat. -/
  flat : Flat X₀.hom
  /-- The morphism `X₀ ⟶ S₀` is of finite presentation. -/
  finitePresentation : FinitePresentation X₀.hom

namespace RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]

/-- The tail of the index set consisting of stages at or beyond the fixed stage. -/
abbrev LaterIndex (D : RelativeDescentSituation.{v, u} I) := {i : I // D.descent.base ≤ i}

/-- The transition morphism `Sᵢ ⟶ S₀` for a stage at or beyond the fixed stage. -/
abbrev baseMap (D : RelativeDescentSituation.{v, u} I) (i : D.LaterIndex) :
    D.descent.system.obj (op i.1) ⟶ D.descent.system.obj (op D.descent.base) :=
  D.descent.system.map (homOfLE i.2).op

/-- The scheme `Xᵢ = Sᵢ ×_{S₀} X₀`. -/
abbrev schemeAt (D : RelativeDescentSituation.{v, u} I) (i : D.LaterIndex) : Scheme.{u} :=
  pullback D.X₀.hom (D.baseMap i)

/-- The base change `Xᵢ = Sᵢ ×_{S₀} X₀`, regarded as a scheme over `Sᵢ`. -/
def overAt (D : RelativeDescentSituation.{v, u} I) (i : D.LaterIndex) :
    Over (D.descent.system.obj (op i.1)) :=
  Over.mk (pullback.snd D.X₀.hom (D.baseMap i))

/-- The canonical morphism `f_{i0} : Xᵢ ⟶ X₀`. -/
abbrev toFixedStage (D : RelativeDescentSituation.{v, u} I) (i : D.LaterIndex) :
    D.schemeAt i ⟶ D.X₀.left :=
  pullback.fst D.X₀.hom (D.baseMap i)

/-- The scheme `X = S ×_{S₀} X₀`. -/
abbrev limitScheme (D : RelativeDescentSituation.{v, u} I) : Scheme.{u} :=
  pullback D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base))

/-- The base change `X = S ×_{S₀} X₀`, regarded as a scheme over the limit `S`. -/
def overLimit (D : RelativeDescentSituation.{v, u} I) : Over D.descent.limitCone.pt :=
  Over.mk (pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)))

/-- The canonical morphism `f₀ : X ⟶ X₀`. -/
abbrev limitToFixedStage (D : RelativeDescentSituation.{v, u} I) :
    D.limitScheme ⟶ D.X₀.left :=
  pullback.fst D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base))

/-- The canonical transition morphism `f_{ji} : Xⱼ ⟶ Xᵢ` for `i ≤ j`. -/
def transition (D : RelativeDescentSituation.{v, u} I) {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.schemeAt j ⟶ D.schemeAt i :=
  pullback.lift (pullback.fst D.X₀.hom (D.baseMap j))
    (pullback.snd D.X₀.hom (D.baseMap j) ≫ D.descent.system.map (homOfLE h).op)
    (by
      rw [Category.assoc, ← D.descent.system.map_comp,
        Subsingleton.elim ((homOfLE h).op ≫ (homOfLE i.2).op) (homOfLE j.2).op]
      exact pullback.condition)

/-- The canonical projection `fᵢ : X ⟶ Xᵢ`. -/
def projection (D : RelativeDescentSituation.{v, u} I) (i : D.LaterIndex) :
    D.limitScheme ⟶ D.schemeAt i :=
  pullback.lift (pullback.fst D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)))
    (pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) ≫
      D.descent.limitCone.π.app (op i.1))
    (by
      rw [Category.assoc, D.descent.limitCone.w (homOfLE i.2).op]; exact pullback.condition)

end RelativeDescentSituation

end AlgebraicGeometry
