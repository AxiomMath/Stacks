module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Algebra.TrivSqZeroExtKernel
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraLiftData
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# The augmentation of a square-zero base object is the scalar part

The objects of `𝒞_Λ` at which the tangent space of a deformation category is evaluated are the
finite-dimensional square-zero extensions `k[V]` of Stacks 06IB, realised here as
`Deformation.artinianSquareZeroExtensionFunctor` applied to a finitely generated `k`-module `V`.
Their carrier is `TrivSqZeroExt k V`, and the one fact a lift over such a base needs about its
base morphism is that it is the scalar part `TrivSqZeroExt.fst`.

With that, every hypothesis the lifting results of
`StacksFrontier/RingTheory/GradedAlgebra/LiftPresentation.lean` make about the augmentation
`ε : A →ₐ[k] k` and its square-zero ideal `I` is available from
`StacksFrontier/Algebra/TrivSqZeroExtKernel.lean`: `ε` is `TrivSqZeroExt.fstHom`, `I` is its
kernel, `I` is square zero, `ε` splits the extension, and `I` is `V`.

## Main results

* `Deformation.Examples.squareZeroBase_hom_eq_fst`: the base morphism of a morphism of `𝒞_Λ`
  out of a square-zero extension into the residue-field object is the scalar part.

## Implementation notes

`Module kᵐᵒᵖ V` and `IsCentralScalar k V` are installed as `local instance`s, as
`StacksFrontier/Deformation/TangentSpace/Functor.lean` and
`StacksFrontier/Deformation/Examples/Linear/FiniteProjectiveTangentSpace.lean` already do: they are
what makes `TrivSqZeroExt k V` a commutative ring, and the square-zero extension functor is
built in their presence.

## References

* [Stacks Project, Tag 06IB](https://stacks.math.columbia.edu/tag/06IB)
* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The right action of a field on a module over it, needed to see a square-zero extension of
the field by that module as a commutative ring. -/
local instance squareZeroBaseModuleMulOpposite (M : ModuleCat.{w} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

/-- The left and right actions of a field on a module over it agree. -/
local instance squareZeroBaseIsCentralScalar (M : ModuleCat.{w} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

/-- **The base morphism of a morphism out of a square-zero extension is the scalar part.** For
`A = k[V]` the residue-field identification of `A` sends the class of `a` to `a.fst`, so the
compatibility condition of `𝒞_Λ` forces the morphism into the residue-field object to be
`TrivSqZeroExt.fst`.

This is the only fact about the square-zero base that the lifting results need: it identifies
the augmentation `ε` with `TrivSqZeroExt.fstHom`, after which
`StacksFrontier/Algebra/TrivSqZeroExtKernel.lean` supplies the square-zero ideal, the splitting and
the identification of the ideal with `V`. -/
theorem squareZeroBase_hom_eq_fst (V : FGModuleCat.{w} k)
    (f : (artinianSquareZeroExtensionFunctor Λ k).obj V ⟶ residueFieldBase Λ k)
    (a : (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    f.hom a = TrivSqZeroExt.fst a :=
  (hom_residueFieldBase_eq_residue f a).trans
    (squareZeroExtensionArtinian_residue Λ k V a)

end Deformation.Examples

end
