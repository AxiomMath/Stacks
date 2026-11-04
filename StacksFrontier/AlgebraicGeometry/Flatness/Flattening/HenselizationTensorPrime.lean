module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic

/-!
# The distinguished prime of `A^h ⊗_A B`

Let `A → B` be a local homomorphism of local rings and let `A^h` be a henselization of `A`.
The residue field map of `A → A^h` is bijective
(`IsLocalRing.IsHenselization.residueField_map_bijective`), so `A^h` maps to `κ(A)` and hence to
`κ(B)`; together with the residue map `B → κ(B)` this gives a surjection `A^h ⊗_A B → κ(B)`. Its
kernel is the maximal ideal `𝔪_B ⊗ A^h + B ⊗ 𝔪_{A^h}` of `A^h ⊗_A B`, and its contractions to
`B` and to `A^h` are their maximal ideals.

## Main definitions

* `Stacks.ResidueFibre.toResidueFieldTensor`: the surjection `A^h ⊗_A B → κ(B)`.
* `Stacks.ResidueFibre.tensorPrime`: its kernel, a maximal ideal of `A^h ⊗_A B`.

## Main results

* `Stacks.ResidueFibre.tensorPrime_comap_right`: `tensorPrime` contracts to the maximal ideal
  of `B`.
* `Stacks.ResidueFibre.tensorPrime_comap_left`: `tensorPrime` contracts to the maximal ideal
  of `A^h`.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u v

open IsLocalRing TensorProduct

namespace Stacks.ResidueFibre

section Henselization

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
variable (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
  [IsLocalRing.IsHenselization A (ResidueField A) Ah]

/-- The identification of the residue field of `A` with that of a henselization of `A`. -/
noncomputable def residueEquiv : ResidueField A ≃+* ResidueField Ah :=
  letI : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  RingEquiv.ofBijective (ResidueField.map (algebraMap A Ah))
    IsLocalRing.IsHenselization.residueField_map_bijective

/-- The map from a henselization of `A` to the residue field of a local `A`-algebra `B`,
obtained from the identification of the residue field of the henselization with that of
`A`. -/
noncomputable def toResidueField : Ah →+* ResidueField B :=
  letI : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  (ResidueField.map (algebraMap A B)).comp
    ((residueEquiv (A := A) Ah).symm.toRingHom.comp (residue Ah))

/-- The map to the residue field of `B` extends the one from `A`. -/
theorem toResidueField_comp (a : A) :
    toResidueField (A := A) (B := B) Ah (algebraMap A Ah a) =
      algebraMap A (ResidueField B) a := by
  let : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  change (ResidueField.map (algebraMap A B))
      ((residueEquiv (A := A) Ah).symm (residue Ah (algebraMap A Ah a))) = _
  rw [show residue Ah (algebraMap A Ah a) =
      ResidueField.map (algebraMap A Ah) (residue A a) from
    (IsLocalRing.ResidueField.map_residue _ _).symm,
    show (ResidueField.map (algebraMap A Ah)) (residue A a) =
      (residueEquiv (A := A) Ah) (residue A a) from rfl, RingEquiv.symm_apply_apply,
    IsLocalRing.ResidueField.map_residue, IsScalarTower.algebraMap_apply A B (ResidueField B)]
  rfl

/-- The `A`-algebra map `A^h ⊗_A B → κ(B)` given by `toResidueField` on `A^h` and the residue
map on `B`. -/
noncomputable def toResidueFieldTensor : Ah ⊗[A] B →ₐ[A] ResidueField B :=
  Algebra.TensorProduct.lift
    { toResidueField (A := A) (B := B) Ah with commutes' := toResidueField_comp Ah }
    (IsScalarTower.toAlgHom A B (ResidueField B)) fun _ _ => .all _ _

/-- The map `A^h ⊗_A B → κ(B)` is surjective. -/
theorem toResidueFieldTensor_surjective :
    Function.Surjective (toResidueFieldTensor (A := A) (B := B) Ah) :=
  (IsLocalRing.residue_surjective (R := B)).forall.2 fun b ↦
    ⟨1 ⊗ₜ b, by simp [toResidueFieldTensor]⟩

/-- On `a ⊗ 1`, the map `A^h ⊗_A B → κ(B)` agrees with `toResidueField`. -/
theorem toResidueFieldTensor_tmul_left (a : Ah) :
    toResidueFieldTensor (A := A) (B := B) Ah (a ⊗ₜ 1) =
      toResidueField (A := A) (B := B) Ah a := by
  simp [toResidueFieldTensor]

/-- The kernel of `toResidueFieldTensor`, an ideal of `A^h ⊗_A B`. -/
noncomputable def tensorPrime : Ideal (Ah ⊗[A] B) :=
  RingHom.ker (toResidueFieldTensor (A := A) (B := B) Ah).toRingHom

/-- The ideal `tensorPrime` of `A^h ⊗_A B` is maximal. -/
instance tensorPrime_isMaximal : (tensorPrime (A := A) (B := B) Ah).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (toResidueFieldTensor_surjective Ah)

/-- The ideal `tensorPrime` lies over the maximal ideal of `B`. -/
theorem tensorPrime_comap_right :
    (tensorPrime (A := A) (B := B) Ah).comap (algebraMap B (Ah ⊗[A] B)) =
      IsLocalRing.maximalIdeal B := by
  ext b
  change toResidueFieldTensor (A := A) (B := B) Ah (1 ⊗ₜ b) = 0 ↔ _
  simp [toResidueFieldTensor, IsLocalRing.residue_eq_zero_iff]

/-- The ideal `tensorPrime` lies over the maximal ideal of the henselization `A^h`. -/
theorem tensorPrime_comap_left :
    (tensorPrime (A := A) (B := B) Ah).comap (algebraMap Ah (Ah ⊗[A] B)) =
      IsLocalRing.maximalIdeal Ah := by
  let : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  ext a
  have hval : toResidueFieldTensor (A := A) (B := B) Ah (algebraMap Ah (Ah ⊗[A] B) a) =
      (ResidueField.map (algebraMap A B))
        ((residueEquiv (A := A) Ah).symm (residue Ah a)) := by
    rw [show algebraMap Ah (Ah ⊗[A] B) a = a ⊗ₜ 1 from rfl,
      toResidueFieldTensor_tmul_left]
    rfl
  change toResidueFieldTensor (A := A) (B := B) Ah (algebraMap Ah (Ah ⊗[A] B) a) = 0 ↔ _
  rw [hval, map_eq_zero_iff _ (ResidueField.map (algebraMap A B)).injective,
    map_eq_zero_iff _ (residueEquiv (A := A) Ah).symm.injective, IsLocalRing.residue_eq_zero_iff]

end Henselization

end Stacks.ResidueFibre

end
