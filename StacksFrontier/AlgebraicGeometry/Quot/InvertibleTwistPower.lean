module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPow

/-!
# Twisting by a tensor power of an invertible module on an algebraic space

Let `X` be an algebraic space and `L` an invertible `𝒪_X`-module. For an integer `n` the tensor
power `L^{⊗ n}` of Tag 01CU is again invertible, and its own tensor powers are those of `L` at
the multiples of `n`:

`(L^{⊗ n})^{⊗ m} ≅ L^{⊗ n m}`.

This is the identity behind Stacks 0DP8: replacing `L` by `L^{⊗ n}` in the twisted Euler
characteristics `m ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ m})` reindexes them along `m ↦ n m`. Both sides are
stated here on the small étale ringed site of `X`, at the spelling of
`AlgebraicGeometry.Space.invertibleTensorPower`, and also for the objects
`AlgebraicGeometry.Space.invertibleTwistObject` of `D(𝒪_X)` to which Stacks 0DNF specialises
Situation 0DNC.

## Main results

* `AlgebraicGeometry.Space.isInvertible_invertibleTensorPower`: `L^{⊗ n}` is invertible.
* `AlgebraicGeometry.Space.invertibleTensorPowerTensorPowerIso`: `(L^{⊗ n})^{⊗ m} ≅ L^{⊗ n m}`.
* `AlgebraicGeometry.Space.invertibleTwistObjectTensorPowerIso`: the same comparison for the
  objects of `D(𝒪_X)` indexing the twisted numerical invariants.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Every integer tensor power of an invertible module on an algebraic space is invertible
(Tag 01CU), in the spelling `AlgebraicGeometry.Space.invertibleTensorPower` uses. -/
instance isInvertible_invertibleTensorPower (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property
      (invertibleTensorPower B S hS F hF L n) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (@Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) n)

/-- **Tensor powers of a tensor power** on an algebraic space: `(L^{⊗ n})^{⊗ m} ≅ L^{⊗ n m}`. -/
def invertibleTensorPowerTensorPowerIso (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n m : ℤ) :
    invertibleTensorPower B S hS F hF (invertibleTensorPower B S hS F hF L n) m ≅
      invertibleTensorPower B S hS F hF L (n * m) :=
  @Stacks.SheafOfModules.Invertible.tensorPowerTensorPowerIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) n m

/-- The comparison `(L^{⊗ n})^{⊗ m} ≅ L^{⊗ n m}` for the objects of `D(𝒪_X)` indexing the
twisted numerical invariants of Stacks 0DNF. -/
def invertibleTwistObjectTensorPowerIso (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n m : ℤ) :
    invertibleTwistObject B S hS F hF (invertibleTensorPower B S hS F hF L n) m ≅
      invertibleTwistObject B S hS F hF L (n * m) :=
  (DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).mapIso
    (invertibleTensorPowerTensorPowerIso B S hS F hF L n m)

end AlgebraicGeometry.Space

end
