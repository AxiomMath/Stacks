module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleAffineSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitClauseTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyLimitStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# The faithfulness clause of the pullback system of modules of a limit of algebraic spaces

Let `X = lim X_i` be the limit of a cofiltered system of algebraic spaces over `S` with affine
transition morphisms.  The categories of modules on the stages and on the limit, with the inverse
images between them, form the `Stacks.ModuleColimit.PullbackSystem`
`AlgebraicGeometry.Space.limitModulePullbackSystem`.  This file proves its faithfulness clause
(the faithfulness clause of the colimit assertion of Stacks 07V7) for quasi-compact stages.

## Main results

* `AlgebraicGeometry.Space.limitModulePullbackSystem_faithfulness`: the faithfulness clause.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local irreducible] modulePullback modulePullbackTriangle

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- **The faithfulness clause of the limit pullback system**, for quasi-compact stages. -/
theorem limitModulePullbackSystem_faithfulness
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    (limitModulePullbackSystem B S hS D hSize hHomSize hD hAffine).Faithfulness :=
  fun k M N hM hN φ ψ h =>
    eventually_eq_of_modulePullback_limitProjection_eq B S hS D hSize hHomSize hD hAffine
      (eventualModuleMapEqOverAffineSystem B S hS) k (hqc k) M N
      hM hN φ ψ h

end AlgebraicGeometry.Space

end
