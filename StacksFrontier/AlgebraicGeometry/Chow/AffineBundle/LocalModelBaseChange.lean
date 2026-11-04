module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelUniversal

/-!
# The local model of an affine bundle commutes with base change

The local model `B[z₁, z₂]/(z₁z₂ - f)` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModel` is presented by two generators whose
product is `f`, so its formation commutes with any base change `B → C`: the local model over `C`
of the image of `f` is `C ⊗_B` the local model over `B` of `f`.

This is the statement that makes the fibres of `Spec(B[z₁, z₂]/(z₁z₂ - f)) → Spec B` computable:
the fibre over a prime `p` is the local model over the residue field `κ(p)` of the image of `f`
there, which is a punctured affine line when `f ∉ p` and a pair of affine lines crossing at the
origin when `f ∈ p`.

## Main definitions

* `Stacks.AffineBundle.baseChangeEquiv` — **the `C`-algebra isomorphism
  `C ⊗_B B[z₁, z₂]/(z₁z₂ - f) ≅ C[z₁, z₂]/(z₁z₂ - f_C)`.**

## Main results

* `Stacks.AffineBundle.baseChangeEquiv_tmul_coord_zero` and
  `baseChangeEquiv_tmul_coord_one` — the isomorphism matches up the two coordinates.

## Implementation notes

Both directions are built by the universal property
`Stacks.AffineBundle.lift`, and the two round trips are checked by
`Stacks.AffineBundle.algHom_ext` on one side and `Algebra.TensorProduct.ext` on the other; no
monomial bookkeeping is needed. The forward map is `Algebra.TensorProduct.lift` of the structure
map of `C` and of the lift sending the coordinates over `B` to the coordinates over `C`.

The defining relation transports because `algebraMap B (LocalModel C f_C) f` and
`algebraMap C (LocalModel C f_C) f_C` agree, which is `IsScalarTower.algebraMap_apply`, and
because `1 ⊗ f` and `f_C ⊗ 1` agree in `C ⊗_B LocalModel B f`, which is the `B`-bilinearity of the
tensor product.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.AffineBundle

variable (B : Type u) [CommRing B] (f : B) (C : Type u) [CommRing C] [Algebra B C]

/-- The image in `C` of the element cutting out the local model. -/
abbrev baseChangeElt : C := algebraMap B C f

/-- The defining relation of the local model over `C`, read over `B`: the two coordinates over `C`
multiply to the image of `f` from `B`. -/
theorem coord_mul_coord_algebraMap_base :
    coord C (baseChangeElt B f C) 0 * coord C (baseChangeElt B f C) 1 =
      algebraMap B (LocalModel C (baseChangeElt B f C)) f := by
  rw [coord_zero_mul_coord_one, IsScalarTower.algebraMap_apply B C]

/-- In `C ⊗_B B[z₁, z₂]/(z₁z₂ - f)` the image of `f` from `B` and the image of its image in `C`
agree. -/
theorem tmul_algebraMap_eq :
    (1 : C) ⊗ₜ[B] (algebraMap B (LocalModel B f) f) =
      algebraMap C (C ⊗[B] LocalModel B f) (baseChangeElt B f C) := by
  have h : (1 : C) ⊗ₜ[B] (algebraMap B (LocalModel B f) f) =
      (f • (1 : C)) ⊗ₜ[B] (1 : LocalModel B f) := by
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h, Algebra.smul_def, mul_one, Algebra.TensorProduct.algebraMap_apply, baseChangeElt]
  rfl

/-- The two coordinates of the local model over `B`, pushed into `C ⊗_B B[z₁, z₂]/(z₁z₂ - f)`,
multiply to the image of `f_C`. -/
theorem tmul_coord_mul_tmul_coord :
    ((1 : C) ⊗ₜ[B] coord B f 0) * ((1 : C) ⊗ₜ[B] coord B f 1) =
      algebraMap C (C ⊗[B] LocalModel B f) (baseChangeElt B f C) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, coord_zero_mul_coord_one, tmul_algebraMap_eq]

/-- The comparison map from the local model over `C` into the base change. -/
def baseChangeInv :
    LocalModel C (baseChangeElt B f C) →ₐ[C] C ⊗[B] LocalModel B f :=
  lift C (baseChangeElt B f C) ((1 : C) ⊗ₜ[B] coord B f 0) ((1 : C) ⊗ₜ[B] coord B f 1)
    (tmul_coord_mul_tmul_coord B f C)

/-- The comparison map from the base change onto the local model over `C`. -/
def baseChangeHom :
    C ⊗[B] LocalModel B f →ₐ[C] LocalModel C (baseChangeElt B f C) :=
  Algebra.TensorProduct.lift (Algebra.ofId C (LocalModel C (baseChangeElt B f C)))
    (lift B f (coord C (baseChangeElt B f C) 0) (coord C (baseChangeElt B f C) 1)
      (coord_mul_coord_algebraMap_base B f C))
    (fun _ _ => Commute.all _ _)

/-- The comparison map from the base change sends `c ⊗ x` to `c` times the image of `x` under the
map from the local model over `B` that sends each coordinate to the matching coordinate over
`C`. -/
@[simp] theorem baseChangeHom_tmul (c : C) (x : LocalModel B f) :
    baseChangeHom B f C (c ⊗ₜ[B] x) =
      algebraMap C _ c *
        lift B f (coord C (baseChangeElt B f C) 0) (coord C (baseChangeElt B f C) 1)
          (coord_mul_coord_algebraMap_base B f C) x :=
  rfl

/-- The comparison map out of the local model over `C` sends the first coordinate to the first
coordinate of the base change. -/
@[simp] theorem baseChangeInv_coord_zero :
    baseChangeInv B f C (coord C (baseChangeElt B f C) 0) = (1 : C) ⊗ₜ[B] coord B f 0 :=
  lift_coord_zero _ _ _ _ _

/-- The comparison map out of the local model over `C` sends the second coordinate to the second
coordinate of the base change. -/
@[simp] theorem baseChangeInv_coord_one :
    baseChangeInv B f C (coord C (baseChangeElt B f C) 1) = (1 : C) ⊗ₜ[B] coord B f 1 :=
  lift_coord_one _ _ _ _ _

/-- **The local model commutes with base change**: the local model over `C` of the image of `f` is
`C ⊗_B` the local model over `B` of `f`. -/
def baseChangeEquiv :
    C ⊗[B] LocalModel B f ≃ₐ[C] LocalModel C (baseChangeElt B f C) :=
  AlgEquiv.ofAlgHom (baseChangeHom B f C) (baseChangeInv B f C)
    (algHom_ext C (baseChangeElt B f C) (by simp) (by simp))
    (Algebra.TensorProduct.ext
      (AlgHom.ext fun c => by
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
          baseChangeHom_tmul, map_one, mul_one, AlgHom.coe_id, id_eq]
        rw [baseChangeInv, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
        rfl)
      (algHom_ext B f (by simp) (by simp)))

/-- The base change isomorphism carries the first coordinate to the first coordinate. -/
@[simp] theorem baseChangeEquiv_tmul_coord_zero :
    baseChangeEquiv B f C ((1 : C) ⊗ₜ[B] coord B f 0) = coord C (baseChangeElt B f C) 0 := by
  rw [baseChangeEquiv, AlgEquiv.ofAlgHom_apply, baseChangeHom_tmul, map_one, one_mul,
    lift_coord_zero]

/-- The base change isomorphism carries the second coordinate to the second coordinate. -/
@[simp] theorem baseChangeEquiv_tmul_coord_one :
    baseChangeEquiv B f C ((1 : C) ⊗ₜ[B] coord B f 1) = coord C (baseChangeElt B f C) 1 := by
  rw [baseChangeEquiv, AlgEquiv.ofAlgHom_apply, baseChangeHom_tmul, map_one, one_mul,
    lift_coord_one]

end Stacks.AffineBundle

end
