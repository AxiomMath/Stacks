module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep

/-!
# Tensor powers distribute over tensor products

`(A ⊗ B) ^⊗ ν ≅ A ^⊗ ν ⊗ B ^⊗ ν` for two invertible `𝒪_X`-modules and `ν ≥ 0`.

## Main definitions

* `Stacks.AmplePullbackPart1.natTensorPowCongr`: `A ≅ A'` implies `A ^⊗ n ≅ A' ^⊗ n`, for the
  `Stacks.TensorPowers.natTensorPow` powers of a monoidal category.
* `Stacks.AmplePullbackPart1.tensorMuIso`: the middle-four interchange
  `(A ⊗ B) ⊗ (K ⊗ N) ≅ (A ⊗ K) ⊗ (B ⊗ N)` of a braided monoidal category, as an isomorphism.
* `Stacks.AmplePullbackPart1.natTensorPowTensorIso`: `(A ⊗ B) ^⊗ n ≅ A ^⊗ n ⊗ B ^⊗ n` in a
  braided monoidal category.
* `Stacks.AmplePullbackPart1.tensorIsoTensorModules`: the monoidal tensor product of `X.Modules`
  is isomorphic to `Stacks.RelativeVeryAmple.tensorModules`.
* `Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule`: the power
  `Stacks.TensorPowers.natTensorPow` and the integer power `Stacks.Ample.tensorPowModule` agree in
  nonnegative degree, as an isomorphism.
* `Stacks.AmplePullbackPart1.tensorPowModuleTensorIso`: `(A ⊗ B) ^⊗ ν ≅ A ^⊗ ν ⊗ B ^⊗ ν` with
  `Stacks.Ample.tensorPowModule` for the powers and `Stacks.RelativeVeryAmple.tensorModules` for
  the products.

## Main results

* `Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules`: the tensor product
  `Stacks.RelativeVeryAmple.tensorModules X A B` of invertible `𝒪_X`-modules is invertible.

## Implementation notes

The isomorphism is built on `Stacks.TensorPowers.natTensorPow`, whose successor law holds by
`rfl`, in an arbitrary braided monoidal category, and is transported to
`Stacks.Ample.tensorPowModule` along the equality of the two powers in nonnegative degree. The
monoidal and braided structures on `X.Modules` are local instances.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.TensorPowers (natTensorPow)

universe v u

namespace Stacks.AmplePullbackPart1

/-! ### The categorical statement -/

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- `A ≅ A'` implies `A ^⊗ n ≅ A' ^⊗ n`, for the natural-number tensor powers of a monoidal
category. By induction: the zeroth powers are both the monoidal unit, and the step tensors the
inductive hypothesis with the given isomorphism. -/
def natTensorPowCongr {A A' : C} (e : A ≅ A') :
    (n : ℕ) → natTensorPow A n ≅ natTensorPow A' n
  | 0 => Iso.refl _
  | n + 1 => natTensorPowCongr e n ⊗ᵢ e

variable [BraidedCategory C]

/-- The middle-four interchange `(A ⊗ B) ⊗ (K ⊗ N) ≅ (A ⊗ K) ⊗ (B ⊗ N)` of a braided monoidal
category, as an isomorphism with components `CategoryTheory.MonoidalCategory.tensorμ` and
`CategoryTheory.MonoidalCategory.tensorδ`. -/
def tensorMuIso (A B K N : C) : (A ⊗ B) ⊗ (K ⊗ N) ≅ (A ⊗ K) ⊗ (B ⊗ N) where
  hom := tensorμ A B K N
  inv := tensorδ A B K N

/-- **Tensor powers distribute over tensor products**: `(A ⊗ B) ^⊗ n ≅ A ^⊗ n ⊗ B ^⊗ n` in any
braided monoidal category. In degree zero it is the inverse of the left unitor; in degree `n + 1`
it tensors the isomorphism in degree `n` with `A ⊗ B` and then applies
`Stacks.AmplePullbackPart1.tensorMuIso`. -/
def natTensorPowTensorIso (A B : C) :
    (n : ℕ) → natTensorPow (A ⊗ B) n ≅ natTensorPow A n ⊗ natTensorPow B n
  | 0 => (λ_ (𝟙_ C)).symm
  | n + 1 =>
      (natTensorPowTensorIso A B n ⊗ᵢ Iso.refl (A ⊗ B)) ≪≫ tensorMuIso _ _ _ _

end Categorical

/-! ### On a scheme -/

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable (X : Scheme.{u}) (A B : X.Modules)

/-- The monoidal tensor product of `X.Modules` is isomorphic to
`Stacks.RelativeVeryAmple.tensorModules`: this is `AlgebraicGeometry.SheafOfModules.tensorIso` at
the scheme-level monoidal instance. -/
def tensorIsoTensorModules : (A ⊗ B : X.Modules) ≅ Stacks.RelativeVeryAmple.tensorModules X A B :=
  AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B

/-- The tensor product `Stacks.RelativeVeryAmple.tensorModules X A B` of invertible
`𝒪_X`-modules is invertible. -/
instance isInvertibleModule_tensorModules [IsInvertibleModule X A] [IsInvertibleModule X B] :
    IsInvertibleModule X (Stacks.RelativeVeryAmple.tensorModules X A B) :=
  letI : IsInvertibleModule X (A ⊗ B) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_tensor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B
  Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ (tensorIsoTensorModules X A B)

variable [IsInvertibleModule X A] [IsInvertibleModule X B]

/-- The tensor power `natTensorPow A n` and the integer tensor power `tensorPowModule X A n` agree
in nonnegative degree, as an isomorphism: the `eqToIso` of the equality
`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`. -/
def natTensorPowIsoTensorPowModule (n : ℕ) :
    (natTensorPow A n : X.Modules) ≅ tensorPowModule X A (n : ℤ) :=
  eqToIso (Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A n)

/-- `(A ⊗ B) ^⊗ ν ≅ A ^⊗ ν ⊗ B ^⊗ ν` for `ν ≥ 0`, where the powers are
`Stacks.Ample.tensorPowModule` and the products are `Stacks.RelativeVeryAmple.tensorModules`: the
isomorphism `Stacks.AmplePullbackPart1.natTensorPowTensorIso` conjugated by
`Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule` and
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`. -/
def tensorPowModuleTensorIso (ν : ℕ) :
    tensorPowModule X (Stacks.RelativeVeryAmple.tensorModules X A B) (ν : ℤ) ≅
      Stacks.RelativeVeryAmple.tensorModules X (tensorPowModule X A (ν : ℤ))
        (tensorPowModule X B (ν : ℤ)) :=
  (natTensorPowIsoTensorPowModule X (Stacks.RelativeVeryAmple.tensorModules X A B) ν).symm ≪≫
    natTensorPowCongr (tensorIsoTensorModules X A B).symm ν ≪≫
    natTensorPowTensorIso A B ν ≪≫
    (natTensorPowIsoTensorPowModule X A ν ⊗ᵢ natTensorPowIsoTensorPowModule X B ν) ≪≫
    tensorIsoTensorModules X (tensorPowModule X A (ν : ℤ)) (tensorPowModule X B (ν : ℤ))

end Scheme

end Stacks.AmplePullbackPart1

end
