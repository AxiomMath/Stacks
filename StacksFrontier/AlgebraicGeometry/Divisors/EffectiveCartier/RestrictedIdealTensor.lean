module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence

/-!
# The multiplication of two ideal sheaves, restricted to a closed subscheme

Let `C ⊆ X` be a closed subscheme with inclusion `i`, and let `I` and `J` be closed subschemes of
`X` with `J` an effective Cartier divisor.  Multiplication of the two ideal sheaves is an
isomorphism `ℐ_I ⊗_{𝒪_X} ℐ_J ≅ ℐ_{I · J}`, by
`Stacks.Divisors.idealTensorMulIso`, and the pullback along `i` is monoidal for the tensor
product sheaf, by `Stacks.PullbackSheafTensor.sheafTensorComparisonIso` — the comparison of
[Stacks, Tag 01CD], which is invertible.  Composing the two restricts the multiplication to `C`:

`i^*ℐ_I ⊗_{𝒪_C} i^*ℐ_J ≅ i^*ℐ_{I · J}`.

On global sections this is a multiplication

`Γ(C, i^*ℐ_I) × Γ(C, i^*ℐ_J) ⟶ Γ(C, i^*ℐ_{I · J})`,

which is what relates the graded pieces of the projection-kernel filtration of an ideal sheaf in
*different* degrees: `Γ(C, i^*ℐ_{D ^ m})` is the degree-`m` piece, by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom`.

## Which spelling the statements use

`Mod(𝒪_Z)` carries the monoidal structure whose tensor product is the tensor product sheaf of
[Stacks, Tag 01CA] and, at the `AlgebraicGeometry.Scheme.Modules` spelling of the same category,
no `MonoidalCategory` instance that instance search can retrieve: the instance is stated over
`Stacks.RingedSpace.structureRingSheaf` and is `@[instance_reducible] local` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal`.  The statements below
therefore name the functor `Stacks.RingedSpace.pullbackFunctor` rather than
`AlgebraicGeometry.Scheme.Modules.pullback`.  The two are the same functor — `rfl`, as are the
types of their sections — so a consumer written at the `Scheme.Modules` spelling, which is the
one `Stacks.Divisors.addEffectiveCartierDivisorSections` and the sections of the thickenings use,
crosses with no transport at all.

## What this does not give, and where the rest is

Nothing here says that the multiplication is compatible with the injections of
[Stacks, Tag 0C4T]: that the product of a section of `i^*ℐ_{D ^ m}` with one of `i^*ℐ_{D ^ n}`
is the symbol of the product of two lifts.  That compatibility — not this isomorphism — is what
the degree-one generation `Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂` of [Stacks, Tag 0C2K] needs, and it is proved
downstream, as
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections` of
`StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`: for `u` and `v` lifts of two
symbols to the ambient thickening, the symbol of `u v` is the `restrictedIdealMulSections` of
the two symbols.  Crossing from there to the twists of `𝐏¹_k` is the other half, and it is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.prodTwistSection_restrictedIdealMulSections` of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`.  With the
two, all four clauses of [Stacks, Tag 0C2K] are unconditional for an exceptional curve of the
first kind, in `StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveMonomialData.lean`.
Nothing here carries a `@[stacks]` attribute.

## Main definitions

* `Stacks.Divisors.restrictedIdealTensorMulIso` — **`i^*ℐ_I ⊗_{𝒪_C} i^*ℐ_J ≅ i^*ℐ_{I · J}`.**
* `Stacks.Divisors.restrictedIdealMulSections` — that isomorphism on global sections, as a
  multiplication of a section of `i^*ℐ_I` by a section of `i^*ℐ_J`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

universe u

namespace Stacks.Divisors

/-! The monoidal structure on `Mod(𝒪_Z)` whose tensor product is the tensor product sheaf of
[Stacks, Tag 01CA] is `Stacks.PullbackSheafTensor.monoidalSheafTensor`, imported above; instance
search cannot retrieve it, for the reason recorded in that module's docstring, so it is named here
as a local instance to make the notation `⊗` below refer to it. -/
attribute [local instance] Stacks.PullbackSheafTensor.monoidalSheafTensor

variable {X : Scheme.{u}}

/-- **The multiplication of two ideal sheaves, restricted to a closed subscheme**:
`i^*ℐ_I ⊗_{𝒪_C} i^*ℐ_J ≅ i^*ℐ_{I · J}` for `i : C ⟶ X` the inclusion of a closed subscheme and
`J` an effective Cartier divisor.  It is the comparison of [Stacks, Tag 01CD] read backwards —
`i^*ℐ_I ⊗ i^*ℐ_J ≅ i^*(ℐ_I ⊗ ℐ_J)` — followed by the pullback of
`Stacks.Divisors.idealTensorMulIso`. -/
def restrictedIdealTensorMulIso (C I J : X.IdealSheafData) (hJ : IsEffectiveCartierDivisor J) :
    (pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I) ⊗
        (pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J) ≅
      (pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist (I * J)) :=
  (Stacks.PullbackSheafTensor.sheafTensorComparisonIso C.subschemeι.toLRSHom.toShHom
      (idealSheafOfModules I) (idealSheafOfModules J)).symm ≪≫
    (pullbackFunctor C.subschemeι.toLRSHom.toShHom).mapIso (idealTensorMulIso I J hJ)

/-- **The product of a global section of `𝒪_X(-I)|_C` with one of `𝒪_X(-J)|_C`**, a global
section of `𝒪_X(-(I + J))|_C`: the pure tensor of the two, read through
`Stacks.Divisors.restrictedIdealTensorMulIso`. -/
def restrictedIdealMulSections (C I J : X.IdealSheafData) (hJ : IsEffectiveCartierDivisor J)
    (a : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I),
      (⊤ : C.subscheme.Opens)))
    (b : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J),
      (⊤ : C.subscheme.Opens))) :
    Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist (I * J)),
      (⊤ : C.subscheme.Opens)) :=
  ((restrictedIdealTensorMulIso C I J hJ).hom.val.app (op (⊤ : C.subscheme.Opens))).hom
    (toTensorSheafSection C.subscheme.toRingedSpace
      ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
      ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J))
      (op (⊤ : C.subscheme.Opens)) (a ⊗ₜ b))

/-- The pullback functor of `Stacks.RingedSpace.pullbackFunctor` is
`AlgebraicGeometry.Scheme.Modules.pullback`, and `Stacks.Divisors.negativeTwist` is
`Stacks.Divisors.idealSheafOfModules`: a consumer written at either spelling may use the
statements above with no transport. -/
theorem pullbackFunctor_obj_negativeTwist (C I : X.IdealSheafData) :
    (pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I) =
      (Scheme.Modules.pullback C.subschemeι).obj (idealSheafOfModules I) :=
  rfl

end Stacks.Divisors

end
