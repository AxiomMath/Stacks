module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.CarrierMapPushout

/-!
# Extension of scalars on the algebra of a free algebra structure

Let `m` be a free `d`-dimensional algebra structure over a ring `R` and let `f : R →+* S` be a
ring homomorphism. Extending the structure constants along `f` gives the structure
`AlgebraicGeometry.FiniteFreeAlgebra.map f m` over `S`, and its algebra is the extension of
scalars of the algebra of `m`: coordinatewise application of `f` is a ring homomorphism
`Carrier m →+* Carrier (map f m)` which presents the target as `S ⊗[R] Carrier m`.

Geometrically this says that the cover
`AlgebraicGeometry.FiniteFreeAlgebra.specCover (map f m)` is the base change of
`AlgebraicGeometry.FiniteFreeAlgebra.specCover m` along `Spec f`, which is what makes the covers
parametrised by the scheme of structure constants of **Stacks 05YM** a family: the cover attached
to a point of that scheme is the base change along the point of the cover attached to the
universal structure.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.tensorAlgEquiv`: the algebra of the extended
  structure is `S ⊗[R] Carrier m`, as an isomorphism of `S`-algebras.

The coordinatewise extension of scalars
`AlgebraicGeometry.FiniteFreeAlgebra.Carrier.mapRingHom` and the fibre-product statement
`AlgebraicGeometry.FiniteFreeAlgebra.isPullback_specCover_map` are those of
`StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.CarrierMapPushout`.

## Implementation notes

The algebra isomorphism is built from the two standard bases rather than from a universal
property. Both `Carrier m` and `Carrier (map f m)` are free on the `d` standard basis vectors by
`AlgebraicGeometry.FiniteFreeAlgebra.Carrier.basis`, so `Module.Basis.baseChange` lifts the first
to an `S`-basis of `S ⊗[R] Carrier m` and `Module.Basis.equiv` matches it with the second.
Multiplicativity is then checked on the generators of the tensor product, where it reduces to
multiplicativity of `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.mapRingHom` — that is, to the
fact that `f` carries the structure constants of `m` to those of `map f m`, which holds by
definition.

No `@[stacks]` attribute is placed here. The tag that states what the scheme of structure
constants represents is **Stacks 05YM**, proved at
`AlgebraicGeometry.FiniteFreeAlgebra.representation`; this is base-change compatibility of the
cover attached to a structure, which that tag does not assert.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]

namespace Carrier

/-- Coordinatewise extension of scalars commutes with the two structure maps. -/
theorem mapRingHom_algebraMap (f : R →+* S) (m : FiniteFreeAlgebra R d) (r : R) :
    mapRingHom f m (algebraMap R (Carrier m) r) = algebraMap S (Carrier (map f m)) (f r) :=
  Carrier.ext fun k => by
    rw [mapRingHom_apply, algebraMap_coord, algebraMap_coord]
    split <;> simp

end Carrier

section Tensor

variable [Algebra R S]

namespace Carrier

/-- The underlying `S`-linear equivalence of
`AlgebraicGeometry.FiniteFreeAlgebra.Carrier.tensorAlgEquiv`: the standard basis of the algebra
of `m`, lifted to the base change, matched with the standard basis of the algebra of the extended
structure. -/
noncomputable def tensorLinearEquiv (m : FiniteFreeAlgebra R d) :
    S ⊗[R] Carrier m ≃ₗ[S] Carrier (map (algebraMap R S) m) :=
  ((Carrier.basis m).baseChange S).equiv (Carrier.basis (map (algebraMap R S) m))
    (Equiv.refl (Fin d))

/-- The base change of the standard basis is sent to the standard basis. -/
@[simp] theorem tensorLinearEquiv_basisVector (m : FiniteFreeAlgebra R d) (i : Fin d) :
    tensorLinearEquiv (S := S) m ((1 : S) ⊗ₜ[R] basisVector m i) =
      basisVector (map (algebraMap R S) m) i := by
  have h : ((Carrier.basis m).baseChange S) i = (1 : S) ⊗ₜ[R] basisVector m i := by
    rw [Module.Basis.baseChange_apply, Carrier.basis_apply]
  rw [← h, tensorLinearEquiv, Module.Basis.equiv_apply, Equiv.refl_apply, Carrier.basis_apply]

/-- **On elements of the algebra of `m`, the comparison with the base change is coordinatewise
extension of scalars.** -/
theorem tensorLinearEquiv_one_tmul (m : FiniteFreeAlgebra R d) (x : Carrier m) :
    tensorLinearEquiv (S := S) m ((1 : S) ⊗ₜ[R] x) =
      mapRingHom (algebraMap R S) m x := by
  have hx : (1 : S) ⊗ₜ[R] x =
      ∑ i : Fin d, algebraMap R S (x i) • ((1 : S) ⊗ₜ[R] basisVector m i) := by
    conv_lhs => rw [← sum_smul_basisVector x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  rw [hx, map_sum]
  simp only [map_smul, tensorLinearEquiv_basisVector]
  conv_rhs => rw [← sum_smul_basisVector (mapRingHom (algebraMap R S) m x)]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The comparison with the base change, on a general generator of the tensor product. -/
theorem tensorLinearEquiv_tmul (m : FiniteFreeAlgebra R d) (s : S) (x : Carrier m) :
    tensorLinearEquiv (S := S) m (s ⊗ₜ[R] x) = s • mapRingHom (algebraMap R S) m x := by
  have h : s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, tensorLinearEquiv_one_tmul]

/-- **The algebra of the extended structure is the extension of scalars of the algebra.** For
`f : R →+* S` the algebra of `map f m` is `S ⊗[R] Carrier m`, as `S`-algebras, with the
comparison sending `1 ⊗ x` to the coordinatewise image of `x`. -/
noncomputable def tensorAlgEquiv (m : FiniteFreeAlgebra R d) :
    S ⊗[R] Carrier m ≃ₐ[S] Carrier (map (algebraMap R S) m) :=
  AlgEquiv.ofLinearEquiv (tensorLinearEquiv m)
    (by
      rw [Algebra.TensorProduct.one_def, tensorLinearEquiv_one_tmul, map_one])
    (fun z w => by
      induction z with
      | add z₁ z₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
      | tmul s x =>
        induction w with
        | add w₁ w₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
        | tmul t y =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, tensorLinearEquiv_tmul,
            tensorLinearEquiv_tmul, tensorLinearEquiv_tmul, map_mul,
            smul_mul_smul_comm])

/-- The comparison `tensorAlgEquiv` sends `1 ⊗ x` to the coordinatewise image of `x`. -/
@[simp] theorem tensorAlgEquiv_one_tmul (m : FiniteFreeAlgebra R d) (x : Carrier m) :
    tensorAlgEquiv (S := S) m ((1 : S) ⊗ₜ[R] x) = mapRingHom (algebraMap R S) m x :=
  tensorLinearEquiv_one_tmul m x

end Carrier

end Tensor

/-- `Spec` of an isomorphism of rings. -/
noncomputable def specIsoOfRingEquiv {A C : Type u} [CommRing A] [CommRing C] (e : A ≃+* C) :
    Spec (.of C) ≅ Spec (.of A) where
  hom := Spec.map (ofHom (e : A →+* C))
  inv := Spec.map (ofHom (e.symm : C →+* A))
  hom_inv_id := by
    rw [← Spec.map_comp, show ofHom (e.symm : C →+* A) ≫ ofHom (e : A →+* C) =
      CategoryStruct.id (CommRingCat.of C) from
      CommRingCat.hom_ext (RingHom.ext fun x => e.apply_symm_apply x), Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, show ofHom (e : A →+* C) ≫ ofHom (e.symm : C →+* A) =
      CategoryStruct.id (CommRingCat.of A) from
      CommRingCat.hom_ext (RingHom.ext fun x => e.symm_apply_apply x), Spec.map_id]

end AlgebraicGeometry.FiniteFreeAlgebra

end
