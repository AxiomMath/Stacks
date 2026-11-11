module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# The situation for descending properties of morphisms along a limit of schemes

A morphism-descent situation is a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, together with a chosen limit, a chosen index `0`, and a
morphism `f₀ : X₀ ⟶ Y₀` of quasi-compact and quasi-separated schemes over the scheme `S₀` sitting
at that index. No smallness condition is imposed on the index type.

Every stage is asked to be quasi-compact and quasi-separated, a hypothesis Situation 081D puts on
`S₀` only; Situation 081D is `AlgebraicGeometry.MorphismLimitSituation` (in
`StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.LimitSituation`), whose restriction to
the stages `i ≥ 0` is a situation of this kind.

## Main definitions

* `AlgebraicGeometry.MorphismDescentSituation` bundles the directed inverse system of schemes with
  affine transition morphisms, its chosen limit, and a morphism of quasi-compact and
  quasi-separated schemes over the scheme at the chosen index.
* `AlgebraicGeometry.MorphismDescentSituation.stageSource`,
  `AlgebraicGeometry.MorphismDescentSituation.stageTarget` and
  `AlgebraicGeometry.MorphismDescentSituation.stageHom` are the base change of the morphism to a
  later stage of the system.
* `AlgebraicGeometry.MorphismDescentSituation.limitSource`,
  `AlgebraicGeometry.MorphismDescentSituation.limitTarget` and
  `AlgebraicGeometry.MorphismDescentSituation.limitHom` are the base change of the morphism to the
  limit of the system.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- A directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms, equipped with a chosen limit cone and a chosen index, together with a morphism of
quasi-compact and quasi-separated schemes over the scheme at that index.

This asks every stage `S_i` to be quasi-compact and quasi-separated, which Situation 081D does not:
081D assumes this only of `S₀`. Situation 081D itself is
`AlgebraicGeometry.MorphismLimitSituation`, and its restriction to the cofinal stages `i ≥ 0`
(`AlgebraicGeometry.MorphismLimitSituation.toMorphismDescentSituation`) is a structure of this
kind with the same `S`, `f₀`, `f_i` and `f`. -/
structure MorphismDescentSituation (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)]
    extends DescentSituation.{v, u} I where
  /-- The scheme `X₀`, given as a scheme over `S₀`. -/
  source : Over (system.obj (op base))
  /-- The scheme `Y₀`, given as a scheme over `S₀`. -/
  target : Over (system.obj (op base))
  /-- The morphism `f₀ : X₀ ⟶ Y₀` of schemes over `S₀`. -/
  hom : source ⟶ target
  /-- `X₀` is quasi-compact. -/
  quasiCompact_source : CompactSpace source.left
  /-- `X₀` is quasi-separated. -/
  quasiSeparated_source : QuasiSeparatedSpace source.left
  /-- `Y₀` is quasi-compact. -/
  quasiCompact_target : CompactSpace target.left
  /-- `Y₀` is quasi-separated. -/
  quasiSeparated_target : QuasiSeparatedSpace target.left

namespace MorphismDescentSituation

attribute [instance] quasiCompact_source quasiSeparated_source quasiCompact_target
  quasiSeparated_target

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation.{v, u} I)

/-- The scheme `S₀` at the chosen index of the system. -/
abbrev baseScheme : Scheme.{u} := D.system.obj (op D.base)

/-- The scheme `S`, the chosen limit of the system. -/
abbrev limitScheme : Scheme.{u} := D.limitCone.pt

/-- The transition morphism `S_i ⟶ S₀` from a stage later than the chosen index. -/
abbrev stageMap (i : I) (h : D.base ≤ i) : D.system.obj (op i) ⟶ D.baseScheme :=
  D.system.map (Quiver.Hom.op (homOfLE h))

/-- The scheme `X_i`, the base change of `X₀` to the stage `S_i`. -/
noncomputable abbrev stageSource (i : I) (h : D.base ≤ i) : Scheme.{u} :=
  ((Over.pullback (D.stageMap i h)).obj D.source).left

/-- The scheme `Y_i`, the base change of `Y₀` to the stage `S_i`. -/
noncomputable abbrev stageTarget (i : I) (h : D.base ≤ i) : Scheme.{u} :=
  ((Over.pullback (D.stageMap i h)).obj D.target).left

/-- The morphism `f_i : X_i ⟶ Y_i`, the base change of `f₀` to the stage `S_i`. -/
noncomputable abbrev stageHom (i : I) (h : D.base ≤ i) : D.stageSource i h ⟶ D.stageTarget i h :=
  ((Over.pullback (D.stageMap i h)).map D.hom).left

/-- The canonical projection `S ⟶ S₀` from the limit to the scheme at the chosen index. -/
abbrev limitProjection : D.limitScheme ⟶ D.baseScheme := D.limitCone.π.app (op D.base)

/-- The scheme `X`, the base change of `X₀` to the limit `S`. -/
noncomputable abbrev limitSource : Scheme.{u} :=
  ((Over.pullback D.limitProjection).obj D.source).left

/-- The scheme `Y`, the base change of `Y₀` to the limit `S`. -/
noncomputable abbrev limitTarget : Scheme.{u} :=
  ((Over.pullback D.limitProjection).obj D.target).left

/-- The morphism `f : X ⟶ Y`, the base change of `f₀` to the limit `S`. -/
noncomputable abbrev limitHom : D.limitSource ⟶ D.limitTarget :=
  ((Over.pullback D.limitProjection).map D.hom).left

end MorphismDescentSituation

end AlgebraicGeometry
