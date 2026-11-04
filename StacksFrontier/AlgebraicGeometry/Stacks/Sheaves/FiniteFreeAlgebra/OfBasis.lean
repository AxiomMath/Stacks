module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Spectrum

/-!
# The structure constants of an algebra in a basis whose first vector is the unit

Let `A` be a commutative algebra over a commutative ring `R` which is free of rank `d` on a
basis whose first vector is `1`. The coordinates of the products of pairs of basis vectors form
a free `d`-dimensional algebra structure over `R`, and `A` is isomorphic as an `R`-algebra to
the algebra of that structure. Consequently `Spec A`, as a scheme over `Spec R`, is isomorphic
to the spectrum of a free `d`-dimensional structure.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.ofBasis`: the structure constants of `A` in such a
  basis.
* `AlgebraicGeometry.FiniteFreeAlgebra.algEquivCarrierOfBasis`: the resulting isomorphism of
  `R`-algebras.
* `AlgebraicGeometry.FiniteFreeAlgebra.specOverIsoSpecCoverOfBasis`: the resulting isomorphism
  of schemes over `Spec R`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.ofBasis_coeff`: the structure constants are the
  coordinates of the products of pairs of basis vectors.

## Implementation notes

Associativity and the unit law of the structure constants come from the expansion of the
coordinates of a product `x * b k` in the basis, which is the content of the private lemmas of
this file; commutativity is commutativity of `A`. The isomorphism of algebras is the coordinate
isomorphism of the basis, whose unitality is the hypothesis on the first basis vector and whose
multiplicativity is the same expansion carried out in both factors.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The coordinates of a product, expanded in the basis in both factors. -/
private theorem repr_mul (b : Module.Basis (Fin d) R A) (x y : A) (l : Fin d) :
    b.repr (x * y) l = ∑ i, ∑ j, b.repr x i * b.repr y j * b.repr (b i * b j) l := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  rw [Finset.sum_mul_sum]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, smul_mul_smul_comm,
    map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

omit [NeZero d] in
/-- The coordinates of a product with a basis vector, expanded in the basis. -/
private theorem repr_mul_basis (b : Module.Basis (Fin d) R A) (x : A) (k l : Fin d) :
    b.repr (x * b k) l = ∑ p, b.repr x p * b.repr (b p * b k) l := by
  rw [repr_mul]
  simp [Finsupp.single_apply]

/-- The free `d`-dimensional algebra structure of a commutative `R`-algebra `A` that is free of
rank `d` on a basis whose first vector is the unit: the coordinates of the products of pairs of
basis vectors. -/
noncomputable def ofBasis (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) :
    FiniteFreeAlgebra R d where
  coeff i j k := b.repr (b i * b j) k
  assoc i j k t := by
    rw [← repr_mul_basis b (b i * b j) k t]
    have h := repr_mul_basis b (b j * b k) i t
    rw [show b j * b k * b i = b i * b j * b k by rw [mul_comm, mul_assoc]] at h
    rw [h]
    exact Finset.sum_congr rfl fun l _ => by
      rw [mul_comm (b l) (b i)]; exact mul_comm _ _
  comm i j k := by rw [mul_comm]
  unit_coeff i j := by
    rw [hb, mul_one, b.repr_self_apply]

/-- The structure constants of `ofBasis b hb` are the coordinates in `b` of the products of pairs
of basis vectors. -/
@[simp] theorem ofBasis_coeff (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) (i j k : Fin d) :
    (ofBasis b hb).coeff i j k = b.repr (b i * b j) k := rfl

/-- The coordinate isomorphism of a basis whose first vector is the unit, as an `R`-linear
equivalence onto the algebra of the structure constants of that basis. -/
noncomputable def coordEquivOfBasis (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) :
    A ≃ₗ[R] Carrier (ofBasis b hb) :=
  b.equivFun.trans (Carrier.coordLinearEquiv (ofBasis b hb)).symm

/-- The `k`-th coordinate of the image of `x` under `coordEquivOfBasis b hb` is the `k`-th
coordinate of `x` in the basis `b`. -/
@[simp] theorem coordEquivOfBasis_apply (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) (x : A)
    (k : Fin d) : coordEquivOfBasis b hb x k = b.repr x k := rfl

/-- An algebra that is free of rank `d` on a basis whose first vector is the unit is isomorphic,
as an `R`-algebra, to the algebra of the structure constants of that basis. -/
@[stacks 05YQ "transport of the multiplication along a basis whose first vector is the unit, \
over an affine base"]
noncomputable def algEquivCarrierOfBasis (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) :
    A ≃ₐ[R] Carrier (ofBasis b hb) :=
  AlgEquiv.ofLinearEquiv (coordEquivOfBasis b hb)
    (Carrier.ext fun k => by
      rw [coordEquivOfBasis_apply, Carrier.one_apply, ← hb, b.repr_self_apply]
      exact if_congr eq_comm rfl rfl)
    (fun x y => Carrier.ext fun k => by
      rw [coordEquivOfBasis_apply, Carrier.mul_apply, repr_mul b x y k]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl)

/-- The spectrum of an algebra that is free of rank `d` on a basis whose first vector is the
unit is the spectrum of a free `d`-dimensional structure, as a scheme over the base. -/
noncomputable def specOverIsoSpecCoverOfBasis (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) :
    specOver R A ≅ specCover (ofBasis b hb) :=
  specOverMapIso (algEquivCarrierOfBasis b hb).symm

end AlgebraicGeometry.FiniteFreeAlgebra

end
