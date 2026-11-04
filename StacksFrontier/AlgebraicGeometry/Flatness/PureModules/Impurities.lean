module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksCore.Tactic.StacksAttribute

/-!
# Impurities of a finite type quasi-coherent module along a fibre

The notion of purity of a module along a fibre is phrased in terms of *impurities*. The data
these are defined from is a finite type morphism of schemes, a finite type quasi-coherent
module on its source and a point of its target — a *pre-pure situation* — together with a base
change of the morphism, a specialization over the chosen point and a point of the base change
above the generalization. Such a diagram is an impurity when its chosen point is in the
relative assassin of the pulled-back module and its closure misses the fibre over the
specialized point.

## Main definitions

* `AlgebraicGeometry.PrePureSituation` bundles the morphism, the module, the finiteness and
  quasi-coherence hypotheses, and the chosen point of the base.
* `AlgebraicGeometry.ImpurityDiagram` is the diagram used to define an impurity.
* `AlgebraicGeometry.ImpurityDiagram.pulledBack` is the module `ℱ_T` of the source.
* `AlgebraicGeometry.IsImpurity` says that an impurity diagram defines an impurity.

## Implementation notes

Following Mathlib, a morphism of finite type is represented by the two properties
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`, and finiteness
and quasi-coherence of the module by the corresponding `SheafOfModules` typeclasses.

The base change `X_T` is recorded as an arbitrary cartesian square rather than a chosen
categorical pullback: that retains exactly the data and the cartesian property of the displayed
diagram while avoiding dependence on a particular choice of pullback object. The fibre `X_t` is
the range of its canonical morphism into `X_T`, and `IsImpurity` is an abbreviation so that
clients can use the APIs for the relative assassin, the closure and the fibres directly.

## References

* [Stacks Project, Tag 05FW](https://stacks.math.columbia.edu/tag/05FW)
* [Stacks Project, Tag 05IX](https://stacks.math.columbia.edu/tag/05IX)
* [Stacks Project, Tag 05IY](https://stacks.math.columbia.edu/tag/05IY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 05FW.** The standing pre-pure situation: a finite type morphism
`X ⟶ S`, a finite type quasi-coherent module on `X`, and a point of `S`. -/
@[stacks 05FW] structure PrePureSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The finite type morphism. -/
  f : X ⟶ S
  /-- The morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType f]
  /-- The morphism is quasi-compact. -/
  [quasiCompact : QuasiCompact f]
  /-- The finite type quasi-coherent module on `X`. -/
  F : X.Modules
  /-- The module is of finite type. -/
  [isFiniteType : F.IsFiniteType]
  /-- The module is quasi-coherent. -/
  [isQuasicoherent : F.IsQuasicoherent]
  /-- The chosen point of the base. -/
  s : S

attribute [instance] PrePureSituation.locallyOfFiniteType PrePureSituation.quasiCompact
  PrePureSituation.isFiniteType PrePureSituation.isQuasicoherent

/-- **Stacks Project, Tag 05IX.** A base-change diagram together with a specialization over the
chosen point of a pre-pure situation and a point above its generalization. -/
@[stacks 05IX] structure ImpurityDiagram (P : PrePureSituation.{u}) where
  /-- The scheme used to change the base. -/
  T : Scheme.{u}
  /-- The base-change morphism. -/
  g : T ⟶ P.S
  /-- The point specializing to `t`. -/
  t' : T
  /-- The point above the distinguished point `P.s`. -/
  t : T
  /-- The specified specialization `t' ⤳ t`. -/
  specializes : t' ⤳ t
  /-- The point `t` maps to the distinguished point of the base. -/
  mapsToChosenPoint : g.base t = P.s
  /-- The base change of `P.X` along `g`. -/
  X_T : Scheme.{u}
  /-- The projection of the base change to `P.X`. -/
  toX : X_T ⟶ P.X
  /-- The projection of the base change to `T`. -/
  toT : X_T ⟶ T
  /-- The displayed square is cartesian. -/
  isPullback : IsPullback toX toT P.f g
  /-- The chosen point of the base change. -/
  xi : X_T
  /-- The chosen point lies above `t'`. -/
  xi_liesOver : toT.base xi = t'

/-- The pullback `ℱ_T` of the module `ℱ` to the base change `X_T`. -/
noncomputable abbrev ImpurityDiagram.pulledBack (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) : D.X_T.Modules := (Scheme.Modules.pullback D.toX).obj P.F

/-- **Stacks Project, Tag 05IY.** An impurity diagram defines an impurity when its chosen point
belongs to the relative assassin of the pulled-back module and its closure is disjoint from the
fibre over the specialized point. -/
@[stacks 05IY] abbrev IsImpurity (P : PrePureSituation.{u}) (D : ImpurityDiagram P) : Prop :=
  D.xi ∈ Stacks.Divisors.relativeAssassin D.toT (D.pulledBack P) ∧
    closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) = ∅

end AlgebraicGeometry
