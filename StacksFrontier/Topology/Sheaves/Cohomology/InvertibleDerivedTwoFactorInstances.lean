module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedTwoFactorWitness
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjectsInvertibility

/-!
# The orthogonality and the invertibility of a sum, at a decomposition with two nonzero factors

`ProductDecomposition.isZero_derivedTensor_toOXMod_of_ne` and
`isInvertibleObject_sigma_toOXMod_unit` are universally quantified over a
`ProductDecomposition X` and carry no further hypothesis.  Instantiated at
`ProductDecomposition.oneFactorDecomposition` the first is discharged because one of the two
modules is zero and the second says only that `𝒪_X[0]` is invertible, so neither instance
exhibits the content of the statement.

This file instantiates both at
`Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.twoFactorDecomposition`, whose degree-zero
and degree-one factors are *not* zero objects
(`TwoFactorWitness.not_isZero_toOXMod_unit_zero`, `...not_isZero_toOXMod_unit_one`) — so the
vanishing of the derived tensor product below is not the vanishing of a tensor product with a
zero object, and `⨁_n 𝒪_n[-n]` is `𝒪_0[0] ⊕ 𝒪_1[-1]` rather than a shift of the unit.

## Main results

* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.isZero_derivedTensor_factor_zero_one`:
  the off-diagonal orthogonality at the pair `1 ≠ 0`, for arbitrary modules over the two
  factors.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.isZero_derivedTensor_unit_zero_one`:
  the same for the two factors themselves — the two nonzero `𝒪_X`-modules.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.isInvertibleObject_sigma_twoFactor`:
  the invertibility of `⨁_n 𝒪_n[-n]` at this decomposition.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.isZero_derivedTensor_witness` and
  `...isInvertibleObject_sigma_witness`: the two statements at the closed instance
  `TwoFactorWitness.witnessDecomposition`, every parameter instantiated from declarations that
  assume nothing.

None of these is a clause of Stacks 0FPG — they are instances of statements proved elsewhere,
recorded to settle whether those statements have non-degenerate instances — so none carries a
`@[stacks]` attribute.

## Implementation notes

The derived-category model is pinned by `HasDerivedCategory.standard`, which for the category of
`𝒪_X`-modules on a `RingedSpace.{u, u}` is `HasDerivedCategory.{u + 1}`; that is the second
universe argument everywhere below.  `IsInvertibleObject` needs its ringed space given by name
rather than inferred from the coproduct: left to unification the universes default to `1` and the
statement does not elaborate.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.InvertibleDerived.TwoFactorWitness

attribute [local instance 10000] HasDerivedCategory.standard

variable {T : TopCat.{u}} (p₀ p₁ : T) (R S : CommRingCat.{u})

/-- **The off-diagonal orthogonality at a decomposition with two nonzero factors.** For an
arbitrary module `L` over the degree-zero factor and an arbitrary module `L'` over the
degree-one factor, both read as `𝒪_X`-modules and placed in degree zero, the derived tensor
product vanishes.

This is `ProductDecomposition.isZero_derivedTensor_toOXMod_of_ne` at `m = 1`, `n = 0` and at a
decomposition for which neither factor is zero, so — unlike every instance formed from
`ProductDecomposition.oneFactorDecomposition` — the conclusion is not reached because one of the
two modules is zero. -/
theorem isZero_derivedTensor_factor_zero_one
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((twoFactorDecomposition p₀ p₁ R S).factor 0)))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((twoFactorDecomposition p₀ p₁ R S).factor 1))) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, u + 1}
      (twoFactorSpace p₀ p₁ R S)
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) 0).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod 0).obj L))
      ((DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) 0).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod 1).obj L'))) :=
  (twoFactorDecomposition p₀ p₁ R S).isZero_derivedTensor_toOXMod_of_ne.{u, u + 1}
    one_ne_zero L L'

/-- **The off-diagonal orthogonality of the two factors themselves.** `𝒪_0[0] ⊗^𝐋 𝒪_1[0] = 0`,
where `𝒪_0` and `𝒪_1` are the two factors read as `𝒪_X`-modules and neither is a zero object
(`not_isZero_toOXMod_unit_zero`, `not_isZero_toOXMod_unit_one`). -/
theorem isZero_derivedTensor_unit_zero_one :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, u + 1}
      (twoFactorSpace p₀ p₁ R S)
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) 0).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((twoFactorDecomposition p₀ p₁ R S).factor 0)))))
      ((DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) 0).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod 1).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((twoFactorDecomposition p₀ p₁ R S).factor 1)))))) :=
  isZero_derivedTensor_factor_zero_one p₀ p₁ R S _ _

/-- **The sum `⨁_n 𝒪_n[-n]` is an invertible object of `D(𝒪_X)` at a decomposition with two
nonzero factors.** Here the sum is `𝒪_0[0] ⊕ 𝒪_1[-1]` with both summands nonzero, so this is not
the invertibility of a shift of the unit. -/
theorem isInvertibleObject_sigma_twoFactor :
    letI : HasCoproducts.{u} (DerivedModules (twoFactorSpace p₀ p₁ R S).sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsInvertibleObject.{u, u + 1} (X := twoFactorSpace p₀ p₁ R S) (∐ fun n : ℤ =>
      (DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) n).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((twoFactorDecomposition p₀ p₁ R S).factor n))))) :=
  isInvertibleObject_sigma_toOXMod_unit.{u, u + 1} (twoFactorDecomposition p₀ p₁ R S)

/-! ### The diagonal term does not vanish

The off-diagonal orthogonality is not a statement that happens to hold of every pair: at the same
decomposition the *diagonal* derived tensor product `𝒪_0[0] ⊗^𝐋 𝒪_0[0]` is nonzero.  So the
hypothesis `m ≠ n` of `ProductDecomposition.isZero_derivedTensor_toOXMod_of_ne` is load-bearing
here, and the vanishing above is a fact about the decomposition and not about the ambient
category.
-/

/-- Placing an object in degree zero reflects zero objects: the composite of the single functor
with the degree-zero homology functor is the identity. -/
theorem isZero_of_isZero_singleFunctor_obj {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (M : A)
    (h : IsZero ((DerivedCategory.singleFunctor A 0).obj M)) : IsZero M :=
  IsZero.of_iso ((DerivedCategory.homologyFunctor A 0).map_isZero h)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (C := A) 0).app M).symm

/-- **The diagonal derived tensor product of the degree-zero factor with itself is not zero.**
It is isomorphic to the factor itself (`ProductDecomposition.derivedTensorIso_toOXMod_unit`),
which is not a zero object (`not_isZero_toOXMod_unit_zero`).

Together with `isZero_derivedTensor_unit_zero_one` this is the measurement that the off-diagonal
orthogonality has content at this decomposition: the same two objects, paired on the diagonal,
do not have vanishing derived tensor product. -/
theorem not_isZero_derivedTensor_diagonal [Nontrivial R] :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, u + 1}
      (twoFactorSpace p₀ p₁ R S)
    ¬ IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) 0).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((twoFactorDecomposition p₀ p₁ R S).factor 0)))))
      ((DerivedCategory.singleFunctor (Mod (twoFactorSpace p₀ p₁ R S).sheaf) 0).obj
        (((twoFactorDecomposition p₀ p₁ R S).toOXMod 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((twoFactorDecomposition p₀ p₁ R S).factor 0)))))) := by
  let := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, u + 1}
    (twoFactorSpace p₀ p₁ R S)
  intro h
  exact not_isZero_toOXMod_unit_zero p₀ p₁ R S
    (isZero_of_isZero_singleFunctor_obj _ (IsZero.of_iso h
      (ProductDecomposition.derivedTensorIso_toOXMod_unit.{u, u + 1}
        (twoFactorDecomposition p₀ p₁ R S) 0).symm))

/-! ### The two statements at the closed instance -/

/-- The off-diagonal orthogonality of the two factors at `witnessDecomposition`, every parameter
instantiated from declarations that assume nothing. -/
theorem isZero_derivedTensor_witness :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, u + 1}
      witnessSpace.{u}
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod witnessSpace.{u}.sheaf) 0).obj
        ((witnessDecomposition.{u}.toOXMod 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (witnessDecomposition.{u}.factor 0)))))
      ((DerivedCategory.singleFunctor (Mod witnessSpace.{u}.sheaf) 0).obj
        ((witnessDecomposition.{u}.toOXMod 1).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (witnessDecomposition.{u}.factor 1)))))) :=
  isZero_derivedTensor_unit_zero_one _ _ _ _

/-- The diagonal derived tensor product at `witnessDecomposition` is not zero, with nothing
assumed. -/
theorem not_isZero_derivedTensor_diagonal_witness :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, u + 1}
      witnessSpace.{u}
    ¬ IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod witnessSpace.{u}.sheaf) 0).obj
        ((witnessDecomposition.{u}.toOXMod 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (witnessDecomposition.{u}.factor 0)))))
      ((DerivedCategory.singleFunctor (Mod witnessSpace.{u}.sheaf) 0).obj
        ((witnessDecomposition.{u}.toOXMod 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (witnessDecomposition.{u}.factor 0)))))) :=
  not_isZero_derivedTensor_diagonal _ _ _ _

/-- The invertibility of `⨁_n 𝒪_n[-n]` at `witnessDecomposition`, every parameter instantiated
from declarations that assume nothing. -/
theorem isInvertibleObject_sigma_witness :
    letI : HasCoproducts.{u} (DerivedModules witnessSpace.{u}.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsInvertibleObject.{u, u + 1} (X := witnessSpace.{u}) (∐ fun n : ℤ =>
      (DerivedCategory.singleFunctor (Mod witnessSpace.{u}.sheaf) n).obj
        ((witnessDecomposition.{u}.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (witnessDecomposition.{u}.factor n))))) :=
  isInvertibleObject_sigma_twoFactor _ _ _ _

end Stacks.Cohomology.InvertibleDerived.TwoFactorWitness

end
