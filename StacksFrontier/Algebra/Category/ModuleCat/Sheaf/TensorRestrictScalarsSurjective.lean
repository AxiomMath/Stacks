module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsLax

/-!
# The comparison on sections for a surjective ring map

Let `φ : R → A` be a **surjective** homomorphism of commutative rings and let `M`, `N` be
`A`-modules.  The comparison `M ⊗_R N → M ⊗_A N` of
`Stacks.SheafOfModules.TensorRestrictScalars.sectionComparison`, which carries `m ⊗_R n` to
`m ⊗_A n`, is then the inverse of an isomorphism Mathlib already has.

This is Mathlib's `TensorProduct.equivOfCompatibleSMul`, whose hypothesis
`TensorProduct.CompatibleSMul` is supplied by
`TensorProduct.CompatibleSMul.of_algebraMap_surjective` in one direction and by the scalar tower
in the other.  Mathlib's equivalence goes the other way, `M ⊗_A N ≃ M ⊗_R N`, and the
identification of its inverse with the comparison holds by `rfl` on a pure tensor, both maps being
the identity on the entries.

## Main results

* `Stacks.SheafOfModules.TensorRestrictScalars.sectionComparison_tmul_eq_equivOfCompatibleSMul`:
  **the comparison is the inverse of Mathlib's equivalence on a pure tensor**, by `rfl`.  Pure
  tensors generate, so this determines the comparison and identifies it with an equivalence.

## Implementation notes

**Why the `letI` block is repeated in every statement.**  `TensorProduct.CompatibleSMul` and
`TensorProduct.equivOfCompatibleSMul` need the `R`-module structure on `M` and `N` as instances on
the carrier types, together with the scalar towers; the structure `ModuleCat.restrictScalars φ`
puts on its value is `Module.compHom _ φ`, so supplying it that way — and not through
`Algebra.toModule` of `φ.toAlgebra` — is what makes the comparison of the two maps hold by `rfl`.
This is the same discipline as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MixedBaseChangeTensor`.

**What this does and does not give.**  It is the *sectionwise* half of the invertibility of
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison` at a surjective morphism of sheaves of
commutative rings.  The presheaf-level and sheaf-level halves — naturality in the object of the
site and the passage through sheafification — are not here.  The sheaf-level statement for the
projection of a product presentation is obtained by a different route, which needs none of this:
see `Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars₂` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorMonoidal`.

Nothing here is a clause of a Stacks tag, so no declaration carries the project tag.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* `Mathlib.LinearAlgebra.TensorProduct.Basic`, for `TensorProduct.equivOfCompatibleSMul`.
* `Mathlib.LinearAlgebra.TensorProduct.Associator`, for
  `TensorProduct.CompatibleSMul.of_algebraMap_surjective`.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace Stacks.SheafOfModules.TensorRestrictScalars

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (P Q : ModuleCat.{u} A)

/-- **The comparison on sections is the inverse of Mathlib's `equivOfCompatibleSMul` on a pure
tensor**, and this holds by `rfl`: both maps send `m ⊗_R n` to `m ⊗_A n`. -/
public theorem sectionComparison_tmul_eq_equivOfCompatibleSMul (h : Function.Surjective φ)
    (p : ↥P) (q : ↥Q) :
    letI : Algebra R A := φ.toAlgebra
    letI : Module R ↥P := Module.compHom _ φ
    letI : Module R ↥Q := Module.compHom _ φ
    letI : IsScalarTower R A ↥P := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : IsScalarTower R A ↥Q := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : TensorProduct.CompatibleSMul R A ↥P ↥Q :=
      TensorProduct.CompatibleSMul.of_algebraMap_surjective (R := R) (A := A) ↥P ↥Q h
    sectionComparison φ P Q (p ⊗ₜ[R] q) =
      (TensorProduct.equivOfCompatibleSMul R A A ↥P ↥Q).symm (p ⊗ₜ[R] q) := rfl

end Stacks.SheafOfModules.TensorRestrictScalars

end
