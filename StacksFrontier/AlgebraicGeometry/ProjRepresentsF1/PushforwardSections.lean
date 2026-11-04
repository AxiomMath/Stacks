module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardGradedAlgebraSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictPullbackBridge

/-!
# The direct image of a sheaf of graded algebras along a morphism of schemes, on sections

A morphism of schemes `f : T ⟶ S` is a morphism of ringed spaces,
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom f`, and Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f` **is** the ringed-space
adjunction `Stacks.RingedSpace.pullbackAdjunction` of that morphism — the same term, by `rfl`.
This file records that, and reads the two section formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardGradedAlgebraSections` at a morphism of
schemes, where the open `f ⁻¹ᵁ U` and the section type `Γ(-, U)` have their scheme notation.

Both are what the bridge from Tag 01O4's pair to Section 01NS's quadruple needs: the map `ψ` of
a pair is stated with the multiplication of the tensor algebra over `f ⁻¹ᵁ U`, and the
multiplicativity of a homomorphism into `f_*T(L)` is stated with the multiplication of
`f_*T(L)` over `U`.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackPushforwardAdjunction_eq`: the
  pullback–pushforward adjunction of a morphism of schemes is the pullback–pushforward
  adjunction of the underlying morphism of ringed spaces.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pushforwardGradedAlgebra_mul_app` and
  `pushforwardGradedAlgebra_one_eval`: **the multiplication and the unit of `f_*A` on local
  sections over `U` are those of `A` read over `f ⁻¹ᵁ U`**, at a morphism of schemes.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackMonoidalSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

variable {T S : Scheme.{u}} (f : T ⟶ S)

/-- **The pullback functor of a morphism of schemes is the pullback functor of the underlying
morphism of ringed spaces.** -/
alias pullback_eq_pullbackFunctor :=
  Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor

/-- **The pushforward functor of a morphism of schemes is the pushforward functor of the
underlying morphism of ringed spaces.** -/
theorem pushforward_eq_pushforwardFunctor :
    Scheme.Modules.pushforward f = pushforwardFunctor (ringedSpaceHom f) :=
  rfl

/-- **The pullback–pushforward adjunction of a morphism of schemes is the pullback–pushforward
adjunction of the underlying morphism of ringed spaces.** In particular their hom-set bijections
agree, which is what lets an adjoint transpose written with one be consumed by a lemma stated
with the other. -/
theorem pullbackPushforwardAdjunction_eq :
    Scheme.Modules.pullbackPushforwardAdjunction f = pullbackAdjunction (ringedSpaceHom f) :=
  rfl

/-- **The multiplication of `f_*A` on two local sections over `U` is the multiplication of `A`
read over `f ⁻¹ᵁ U`**, for a morphism of schemes. This is
`Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_mul_app` at `ringedSpaceHom f`. -/
theorem pushforwardGradedAlgebra_mul_app
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)) (i j : ℤ)
    (U : S.Opens)
    (x : Γ((Scheme.Modules.pushforward f).obj (A.piece i), U))
    (y : Γ((Scheme.Modules.pushforward f).obj (A.piece j), U)) :
    ((Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra (ringedSpaceHom f) A).mul
        i j).app (op U) x y =
      (A.mul i j).app (op (f ⁻¹ᵁ U)) x y :=
  Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_mul_app (ringedSpaceHom f) A i j
    (op U) x y

/-- **The unit of `f_*A` over `U` is the unit of `A` read over `f ⁻¹ᵁ U`**, for a morphism of
schemes. -/
theorem pushforwardGradedAlgebra_one_eval
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
    (U : S.Opens) :
    (Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra (ringedSpaceHom f) A).one.eval
        (op U) =
      A.one.eval (op (f ⁻¹ᵁ U)) :=
  Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_one_eval (ringedSpaceHom f) A (op U)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
