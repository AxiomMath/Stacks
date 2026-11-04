module

public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleTwistPower
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerPolynomial

/-!
# Twisted Euler characteristics with respect to a tensor power

Let `X` be a proper algebraic space over a field `k`, let `𝓕` be an `𝒪_X`-module and let `L` be
an invertible `𝒪_X`-module. The twisted Euler characteristics of `𝓕` with respect to the
invertible module `L^{⊗ n}` are those with respect to `L`, read at the multiples of `n`:

`χ(X, 𝓕 ⊗ (L^{⊗ n})^{⊗ m}) = χ(X, 𝓕 ⊗ L^{⊗ n m})`.

## Main results

* `AlgebraicGeometry.Space.twistStepTensorPowerIso`: `𝓕 ⊗ (L^{⊗ n})^{⊗ m} ≅ 𝓕 ⊗ L^{⊗ n m}` on
  any algebraic space.
* `AlgebraicGeometry.Space.eulerCharacteristic_twistedModuleUlift_tensorPower`: the identity
  above, for the Euler characteristic `AlgebraicGeometry.Space.eulerCharacteristic` of
  Stacks 0DN1 and the twists `AlgebraicGeometry.Space.twistedModuleUlift`.

## References

* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

section Twist

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Twisting by the `m`-th power of `L^{⊗ n}` is twisting by the `(n m)`-th power of `L`:
`M ⊗ (L^{⊗ n})^{⊗ m} ≅ M ⊗ L^{⊗ n m}`. -/
def twistStepTensorPowerIso (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n m : ℤ) (M : Modules.{u, u} B S hS F hF) :
    twistStep B S hS F hF (invertibleTensorPower B S hS F hF L n) m M ≅
      twistStep B S hS F hF L (n * m) M :=
  @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _
    _ _ _ _ (Iso.refl M) (invertibleTensorPowerTensorPowerIso B S hS F hF L n m)

/-- The single twist `M ⊗ L^{⊗ m}` of `AlgebraicGeometry.Space.twistedModule`, for a family of
one invertible module, is one twisting step. -/
theorem twistedModule_const_one (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (m : ℤ) (M : Modules.{u, u} B S hS F hF) :
    twistedModule B S hS F hF M (fun _ : Fin 1 => L) (fun _ => m) =
      twistStep B S hS F hF L m M :=
  rfl

end Twist

section Euler

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk)

/-- On a proper algebraic space over a field, the twisted Euler characteristics of a module `𝓕`
with respect to `L^{⊗ n}` are those with respect to `L` at the multiples of `n`:

`χ(X, 𝓕 ⊗ (L^{⊗ n})^{⊗ m}) = χ(X, 𝓕 ⊗ L^{⊗ n m})`. -/
theorem eulerCharacteristic_twistedModuleUlift_tensorPower
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (M : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (L : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property L]
    (n m : ℤ)
    [IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M
        (fun _ : Fin 1 => invertibleTensorPower B (Spec (.of k)) hk X.1 X.2 L n) (fun _ => m))]
    [IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M (fun _ : Fin 1 => L)
        (fun _ => n * m))] :
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M
            (fun _ : Fin 1 => invertibleTensorPower B (Spec (.of k)) hk X.1 X.2 L n)
            (fun _ => m)) =
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 M (fun _ : Fin 1 => L)
            (fun _ => n * m)) :=
  eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf
    (twistedModuleUliftIsoOfIso.{u, w} B (Spec (.of k)) hk X.1 X.2 M
      (fun _ : Fin 1 => invertibleTensorPower B (Spec (.of k)) hk X.1 X.2 L n) (fun _ => m)
      (fun _ : Fin 1 => L) (fun _ => n * m)
      (twistStepTensorPowerIso B (Spec (.of k)) hk X.1 X.2 L n m M))

end Euler

end AlgebraicGeometry.Space

end
