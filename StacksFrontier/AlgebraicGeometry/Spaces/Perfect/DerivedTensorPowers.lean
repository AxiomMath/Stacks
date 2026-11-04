module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.CategoryTheory.Monoidal.BifunctorIntegerPowers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallDerivedDual

/-!
# Tensor powers with integer exponents in the derived category of an algebraic space

Let `X` be an algebraic space and let `E_1, …, E_r` be objects of `D(𝒪_X)`, the derived category
of sheaves of modules on the small étale site of `X`. For `n ∈ ℤ^{⊕ r}` Stacks 0DNE considers the
object

`E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`

of `D(𝒪_X)`, where `⊗` is the derived tensor product and, for a negative exponent, `E^{⊗ n}` is
the `(-n)`-fold derived tensor power of the dual `E^∨ = RSheafHom(E, 𝒪_X)`; for a perfect `E` the
dual is perfect and is the dual of `E` in the sense of monoidal categories, so this is the usual
meaning of a negative tensor power. This file defines the dual, the integer tensor powers and the
products of integer tensor powers.

## Main definitions

* `AlgebraicGeometry.Space.derivedDual`: the dual `E^∨ = RSheafHom(E, 𝒪_X)` of an object of
  `D(𝒪_X)`.
* `AlgebraicGeometry.Space.derivedTensorPower`: the integer tensor power `E^{⊗ n}`.
* `AlgebraicGeometry.Space.derivedTensorPowerProduct`: the object
  `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`, which for `r` perfect objects is the index map
  `ℤ^{⊕ r} ⟶ D(𝒪_X)` of Stacks 0DNE.

## Main results

* `AlgebraicGeometry.Space.derivedTensorPower_natCast` and
  `AlgebraicGeometry.Space.derivedTensorPower_neg_natCast`: the non-negative powers are tensor
  powers of `E`, the negative ones tensor powers of `E^∨`.
* `AlgebraicGeometry.Space.derivedTensorPowerProduct_mem`: a property of objects of `D(𝒪_X)`
  containing `𝒪_X`, every `E_j` and every `E_j^∨` and stable under the derived tensor product
  holds for every `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`.

## Implementation notes

The small étale site of `X` has its objects one universe above its morphisms, while the derived
internal Hom of this library is constructed on a ringed site all three of whose universes agree.
The dual is therefore `AlgebraicGeometry.RingedSite.essentiallySmallDerivedDual`: the dual
computed on a small model of the site, carried back along the equivalence of derived categories
which restriction to the small model induces.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

alias essentiallySmall_smallEtaleRingedSite_C := instEssentiallySmallSmallEtaleRingedSite

/-- **The derived dual** `E^∨ = RSheafHom(E, 𝒪_X)` of an object of `D(𝒪_X)` for an algebraic
space `X`. -/
def derivedDual (E : DerivedCategory (Modules.{u, u} B S hS F hF)) :
    DerivedCategory (Modules.{u, u} B S hS F hF) :=
  RingedSite.essentiallySmallDerivedDual (smallEtaleRingedSite B S hS F hF) E

/-- **The integer tensor power** `E^{⊗ n}` of an object of `D(𝒪_X)`: the `n`-fold derived tensor
power of `E` for `n ≥ 0`, and the `(-n)`-fold derived tensor power of the dual `E^∨` for
`n < 0`. -/
def derivedTensorPower (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (n : ℤ) :
    DerivedCategory (Modules.{u, u} B S hS F hF) :=
  (Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedSite B S hS F hF)).intTensorPow
    (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF)) E
    (derivedDual B S hS F hF E) n

/-- **The object `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`** of `D(𝒪_X)` attached to objects
`E_1, …, E_r` and to `n ∈ ℤ^{⊕ r}`; for perfect `E_j` this is the index map `ℤ^{⊕ r} ⟶ D(𝒪_X)`
of Stacks 0DNE. -/
def derivedTensorPowerProduct {r : ℕ} (E : Fin r → DerivedCategory (Modules.{u, u} B S hS F hF))
    (n : Fin r → ℤ) : DerivedCategory (Modules.{u, u} B S hS F hF) :=
  (Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedSite B S hS F hF)).multiTensorPow
    (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF)) E
    (fun j ↦ derivedDual B S hS F hF (E j)) n

variable {B S hS F hF}

/-- The power `E^{⊗ n}` for `n ≥ 0` is the `n`-fold derived tensor power of `E`. -/
theorem derivedTensorPower_natCast (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (n : ℕ) :
    derivedTensorPower B S hS F hF E n =
      (Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS F hF)).tensorList
        (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF))
        (List.replicate n E) :=
  rfl

/-- The power `E^{⊗ (-n)}` for `n > 0` is the `n`-fold derived tensor power of the dual. -/
theorem derivedTensorPower_neg_natCast (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    {n : ℕ} (hn : 0 < n) :
    derivedTensorPower B S hS F hF E (-n) =
      (Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS F hF)).tensorList
        (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF))
        (List.replicate n (derivedDual B S hS F hF E)) :=
  Functor.intTensorPow_neg_natCast _ _ _ _ hn

/-- The power `E^{⊗ 0}` is the structure sheaf. -/
@[simp]
theorem derivedTensorPower_zero (E : DerivedCategory (Modules.{u, u} B S hS F hF)) :
    derivedTensorPower B S hS F hF E 0 =
      RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF) :=
  rfl

/-- The power `E^{⊗ 1}` is `E`. -/
@[simp]
theorem derivedTensorPower_one (E : DerivedCategory (Modules.{u, u} B S hS F hF)) :
    derivedTensorPower B S hS F hF E 1 = E :=
  rfl

/-- The power `E^{⊗ (-1)}` is the dual `E^∨`. -/
@[simp]
theorem derivedTensorPower_neg_one (E : DerivedCategory (Modules.{u, u} B S hS F hF)) :
    derivedTensorPower B S hS F hF E (-1) = derivedDual B S hS F hF E :=
  rfl

/-- The product of integer tensor powers is the tensor product of the list of the powers
`E_j^{⊗ n_j}`. -/
theorem derivedTensorPowerProduct_eq {r : ℕ}
    (E : Fin r → DerivedCategory (Modules.{u, u} B S hS F hF)) (n : Fin r → ℤ) :
    derivedTensorPowerProduct B S hS F hF E n =
      (Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS F hF)).tensorList
        (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF))
        (List.ofFn fun j ↦ derivedTensorPower B S hS F hF (E j) (n j)) :=
  rfl

/-- A property of objects of `D(𝒪_X)` which holds for `𝒪_X`, for every `E_j` and for every dual
`E_j^∨`, and which is stable under the derived tensor product, holds for every object
`E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`. -/
theorem derivedTensorPowerProduct_mem (P : DerivedCategory (Modules.{u, u} B S hS F hF) → Prop)
    (hone : P (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF)))
    (hT : ∀ A A', P A → P A' →
      P (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS F hF)).obj A).obj A'))
    {r : ℕ} {E : Fin r → DerivedCategory (Modules.{u, u} B S hS F hF)} (hE : ∀ j, P (E j))
    (hE' : ∀ j, P (derivedDual B S hS F hF (E j))) (n : Fin r → ℤ) :
    P (derivedTensorPowerProduct B S hS F hF E n) :=
  Functor.multiTensorPow_mem _ _ P hone hT hE hE' n

end AlgebraicGeometry.Space

end
