module

public import StacksFrontier.RingTheory.DeRham.LaurentResidue
public import StacksFrontier.RingTheory.DeRham.LogPolesComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The residue of a Laurent algebra does not depend on the trivialization

Let `R` be a commutative ring, `A` an `R`-algebra and `A[T;T⁻¹]` the Laurent polynomial algebra
over `A`, graded by the exponent of `T`.  The elements `1` and `dlog T` freely generate the
weight-zero relative de Rham forms as a right module over `Ω^•_{A/R}`, and the residue is
`Res (ω' + dlog T ∧ ω) = ω`.

That description is attached to the coordinate `T`.  In the geometric situation of Stacks 0FUF
the coordinate is the choice of a generator `s` of an invertible module over an affine open, and
no such choice is global: two generators differ by a unit `g` of the ring, and
`dlog (g s) = g⁻¹ dg + dlog s`.  This file proves the corresponding statement for the Laurent
algebra.

The coordinates are the units `u` of `A[T;T⁻¹]` that are homogeneous of weight one; these are
exactly the elements `a T` for `a` a unit of `A`, and they are the Laurent-algebra form of the
datum `s ∈ L(U)` of the Stacks proof.  For every one of them `1` and `dlog u` again freely
generate the weight-zero forms, with the *same* residue: the two decompositions of a weight-zero
form differ only in the summand pulled back from `A`.  A unit `a Tⁿ` has coefficient `a` a unit
of `A`, so the inverse of a weight-one unit is automatically homogeneous of weight `-1`.

## Main definitions

* `LaurentDeRham.weightOneUnit`: **the coordinate attached to a unit `a` of `A`**, the unit
  `a T` of `A[T;T⁻¹]`.

## Main results

* `LaurentDeRham.isUnit_of_isUnit_single`: a monomial `a Tⁿ` is a unit of `A[T;T⁻¹]` only if
  `a` is a unit of `A`.
* `LaurentDeRham.exists_weightOneUnit_eq`: **the weight-one units are the `a T`.**  A unit of
  `A[T;T⁻¹]` homogeneous of weight one is `LaurentDeRham.weightOneUnit` of a unit of `A`.
* `LaurentDeRham.dlogUnit_weightOneUnit`: **`dlog (a T) = a⁻¹ da + dlog T`**, and
  `LaurentDeRham.dlogUnit_weightOneUnit_one`, its case `a = 1`, which says that `dlog T` is the
  logarithmic differential of the coordinate attached to `1`.
* `LaurentDeRham.wedgeLeft_dlogUnit_mem_weightComponent`: `dlog u ∧ ω` is a weight-zero form for
  every weight-one unit `u` and every form `ω` pulled back from `A`.
* `LaurentDeRham.residue_mapExteriorPower_add_wedgeLeft_dlogUnit`: **the defining formula of the
  residue holds for every coordinate**, `Res (ω' + dlog u ∧ ω) = ω`.
* `LaurentDeRham.exists_of_mem_weightComponent_succ_dlogUnit`: **`1` and `dlog u` generate the
  weight-zero forms** for every coordinate `u`.
* `LaurentDeRham.eq_of_mapExteriorPower_add_wedgeLeft_dlogUnit`: **the residue is independent of
  the coordinate.**  If one weight-zero form is written `ω₁' + dlog u ∧ ω₁` and
  `ω₂' + dlog v ∧ ω₂` for two coordinates `u` and `v`, then `ω₁ = ω₂`.
* `LaurentDeRham.residueHom_f_succ_apply_of_dlogUnit`: the morphism of complexes
  `LaurentDeRham.residueHom`, the second map of the short exact sequence
  `LaurentDeRham.residueShortComplex`, is the residue read in any coordinate.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
-/

open KaehlerDifferential LaurentPolynomial

@[expose] public section

noncomputable section

universe u

namespace LaurentDeRham

/-! ### The coordinates of the Laurent algebra -/

section Coordinate

variable {A : Type u} [CommRing A]

/-- **The coordinate attached to a unit `a` of `A`**: the unit `a T` of `A[T;T⁻¹]`.  It is
homogeneous of weight one and its inverse `a⁻¹ T⁻¹` is homogeneous of weight `-1`, and these are
all such units. -/
def weightOneUnit (a : Aˣ) : A[T;T⁻¹]ˣ where
  val := C (a : A) * T 1
  inv := C (↑a⁻¹ : A) * T (-1)
  val_inv := by
    rw [mul_mul_mul_comm, ← map_mul, ← T_add, a.mul_inv, add_neg_cancel, map_one, T_zero,
      one_mul]
  inv_val := by
    rw [mul_mul_mul_comm, ← map_mul, ← T_add, a.inv_mul, neg_add_cancel, map_one, T_zero,
      one_mul]

/-- The underlying element of the unit `weightOneUnit a` is `a T`. -/
@[simp]
theorem weightOneUnit_val (a : Aˣ) : (weightOneUnit a : A[T;T⁻¹]) = C (a : A) * T 1 := rfl

/-- The inverse of the unit `weightOneUnit a` is `a⁻¹ T⁻¹`. -/
@[simp]
theorem weightOneUnit_inv (a : Aˣ) :
    (↑(weightOneUnit a)⁻¹ : A[T;T⁻¹]) = C (↑a⁻¹ : A) * T (-1) := rfl

/-- **A monomial is a unit of `A[T;T⁻¹]` only if its coefficient is a unit of `A`.** -/
theorem isUnit_of_isUnit_single {n : ℤ} {a : A}
    (h : IsUnit (AddMonoidAlgebra.single n a : A[T;T⁻¹])) : IsUnit a := by
  have hev : LaurentPolynomial.eval₂ (RingHom.id A) (1 : Aˣ)
      (AddMonoidAlgebra.single n a : A[T;T⁻¹]) = a := by
    rw [single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
    simp
  simpa [hev] using h.map (LaurentPolynomial.eval₂ (RingHom.id A) (1 : Aˣ))

end Coordinate

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- A coordinate is homogeneous of weight one. -/
theorem weightOneUnit_mem_weightGrading (a : Aˣ) :
    (weightOneUnit a : A[T;T⁻¹]) ∈ weightGrading R A 1 := by
  rw [weightOneUnit_val, ← single_eq_C_mul_T]
  exact single_mem_weightGrading R A 1 (a : A)

/-- The inverse of a coordinate is homogeneous of weight `-1`. -/
theorem weightOneUnit_inv_mem_weightGrading (a : Aˣ) :
    (↑(weightOneUnit a)⁻¹ : A[T;T⁻¹]) ∈ weightGrading R A (-1) := by
  rw [weightOneUnit_inv, ← single_eq_C_mul_T]
  exact single_mem_weightGrading R A (-1) (↑a⁻¹ : A)

/-- **The weight-one units of `A[T;T⁻¹]` are the `a T` with `a` a unit of `A`**: a unit
homogeneous of weight one is a coordinate. -/
theorem exists_weightOneUnit_eq {v : A[T;T⁻¹]ˣ}
    (hv : (v : A[T;T⁻¹]) ∈ weightGrading R A 1) :
    ∃ a : Aˣ, weightOneUnit a = v := by
  obtain ⟨a, ha⟩ := exists_single_of_mem_weightGrading R A hv
  obtain ⟨b, hb⟩ := isUnit_of_isUnit_single (n := 1) (a := a) (ha ▸ v.isUnit)
  refine ⟨b, Units.ext ?_⟩
  rw [weightOneUnit_val, ← single_eq_C_mul_T, hb]
  exact ha

/-! ### The logarithmic differential of a coordinate -/

/-- **`dlog (a T) = a⁻¹ da + dlog T`**: the logarithmic differential of a coordinate differs from
that of `T` by a form pulled back from `A`. -/
theorem dlogUnit_weightOneUnit (a : Aˣ) :
    Stacks.LogPoles.dlogUnit R (weightOneUnit a) =
      map R R A A[T;T⁻¹] (Stacks.LogPoles.dlogUnit R a) + dlogT R A := by
  have hsmul : ∀ (c : A) (z : Ω[A[T;T⁻¹]⁄R]), (C c : A[T;T⁻¹]) • z = c • z := fun c z ↦ by
    rw [C_eq_algebraMap, algebraMap_smul]
  have hmap : map R R A A[T;T⁻¹] (Stacks.LogPoles.dlogUnit R a) =
      (C (↑a⁻¹ : A) : A[T;T⁻¹]) • D R A[T;T⁻¹] (C (a : A)) := by
    rw [Stacks.LogPoles.dlogUnit, map_smul, map_incl_D, hsmul]
  have hc1 : (C (↑a⁻¹ : A) * T (-1)) * (C (a : A)) = (T (-1) : A[T;T⁻¹]) := by
    rw [mul_right_comm, ← map_mul, a.inv_mul, map_one, one_mul]
  have hc2 : (C (↑a⁻¹ : A) * T (-1)) * (T 1 : A[T;T⁻¹]) = C (↑a⁻¹ : A) := by
    rw [mul_assoc, ← T_add, neg_add_cancel, T_zero, mul_one]
  rw [Stacks.LogPoles.dlogUnit, hmap, dlogT, weightOneUnit_val, weightOneUnit_inv,
    Derivation.leibniz, smul_add, smul_smul, smul_smul, hc1, hc2]
  exact add_comm _ _

/-- `dlog` of the coordinate attached to the unit `1` is `dlog T`. -/
@[simp]
theorem dlogUnit_weightOneUnit_one :
    Stacks.LogPoles.dlogUnit R (weightOneUnit (1 : Aˣ)) = dlogT R A := by
  rw [dlogUnit_weightOneUnit, Stacks.LogPoles.dlogUnit, Units.val_one,
    Derivation.map_one_eq_zero, smul_zero, map_zero, zero_add]

/-! ### The residue read in an arbitrary coordinate -/

/-- Rewriting `dlog (a T) ∧ ω` as the pullback of `dlog a ∧ ω` plus `dlog T ∧ ω`. -/
private theorem wedgeLeft_dlogUnit_weightOneUnit (a : Aˣ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R (weightOneUnit a)) p
        (mapExteriorPower R A A[T;T⁻¹] p ω) =
      mapExteriorPower R A A[T;T⁻¹] (p + 1)
          (exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R a) p ω) +
        exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω) := by
  rw [dlogUnit_weightOneUnit, exteriorPower.wedgeLeft_add, LinearMap.add_apply,
    ← mapExteriorPower_wedgeLeft]

/-- `dlog u ∧ ω` is a weight-zero form for every coordinate `u` and every `ω` pulled back from
`A`. -/
theorem wedgeLeft_dlogUnit_mem_weightComponent (a : Aˣ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R (weightOneUnit a)) p
        (mapExteriorPower R A A[T;T⁻¹] p ω) ∈ weightComponent R A 0 (p + 1) := by
  rw [wedgeLeft_dlogUnit_weightOneUnit]
  exact Submodule.add_mem _ (mapExteriorPower_mem_weightComponent R A (p + 1) _)
    (wedgeLeft_dlogT_mem_weightComponent R A p ω)

/-- **The defining formula of the residue holds in every coordinate**:
`Res (ω' + dlog u ∧ ω) = ω` for every unit `u` of `A[T;T⁻¹]` homogeneous of weight one. -/
@[stacks 0FUF "the local computation: the residue formula holds for every trivialization, not
only for the coordinate T"]
theorem residue_mapExteriorPower_add_wedgeLeft_dlogUnit {v : A[T;T⁻¹]ˣ}
    (hv : (v : A[T;T⁻¹]) ∈ weightGrading R A 1) (p : ℕ)
    (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    residue R A p (mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
        exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p
          (mapExteriorPower R A A[T;T⁻¹] p ω)) = ω := by
  obtain ⟨a, rfl⟩ := exists_weightOneUnit_eq R A hv
  rw [wedgeLeft_dlogUnit_weightOneUnit, ← add_assoc, ← map_add,
    residue_mapExteriorPower_add_wedgeLeft]

/-- **`1` and `dlog u` generate the weight-zero forms** for every coordinate `u`: a weight-zero
form of positive degree is `ω' + dlog u ∧ ω` with `ω'` and `ω` pulled back from `A`. -/
@[stacks 0FUF "the local computation: 1 and dlog u generate the weight-zero forms for every
trivialization, not only for the coordinate T"]
theorem exists_of_mem_weightComponent_succ_dlogUnit {v : A[T;T⁻¹]ˣ}
    (hv : (v : A[T;T⁻¹]) ∈ weightGrading R A 1) {p : ℕ}
    {x : ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightComponent R A 0 (p + 1)) :
    ∃ (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R]))),
      x = mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
        exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p
          (mapExteriorPower R A A[T;T⁻¹] p ω) := by
  obtain ⟨a, rfl⟩ := exists_weightOneUnit_eq R A hv
  obtain ⟨ω', ω, hx⟩ := exists_of_mem_weightComponent_succ R A hx
  refine ⟨ω' - exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R a) p ω, ω, ?_⟩
  rw [wedgeLeft_dlogUnit_weightOneUnit, ← add_assoc, ← map_add, sub_add_cancel]
  exact hx

/-- **The residue does not depend on the coordinate.**  If a weight-zero form is written
`ω₁' + dlog u ∧ ω₁` in one coordinate and `ω₂' + dlog v ∧ ω₂` in another, then `ω₁ = ω₂`: both
are its residue. -/
@[stacks 0FUF "the local computation: the residue is independent of the trivialization"]
theorem eq_of_mapExteriorPower_add_wedgeLeft_dlogUnit {v w : A[T;T⁻¹]ˣ}
    (hv : (v : A[T;T⁻¹]) ∈ weightGrading R A 1)
    (hw : (w : A[T;T⁻¹]) ∈ weightGrading R A 1) {p : ℕ}
    {ω₁' ω₂' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))} {ω₁ ω₂ : ↥(⋀[A]^p (Ω[A⁄R]))}
    (h : mapExteriorPower R A A[T;T⁻¹] (p + 1) ω₁' +
          exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p
            (mapExteriorPower R A A[T;T⁻¹] p ω₁) =
        mapExteriorPower R A A[T;T⁻¹] (p + 1) ω₂' +
          exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R w) p
            (mapExteriorPower R A A[T;T⁻¹] p ω₂)) :
    ω₁ = ω₂ :=
  ((residue_mapExteriorPower_add_wedgeLeft_dlogUnit R A hv p ω₁' ω₁).symm.trans
      (congrArg (residue R A p) h)).trans
    (residue_mapExteriorPower_add_wedgeLeft_dlogUnit R A hw p ω₂' ω₂)

/-- **The residue morphism of the residue sequence reads off the `dlog u`-component in every
coordinate.**  The morphism `LaurentDeRham.residueHom` sends a weight-zero form
`ω' + dlog u ∧ ω` to `ω`, for every unit `u` of `A[T;T⁻¹]` homogeneous of weight one. -/
theorem residueHom_f_succ_apply_of_dlogUnit {v : A[T;T⁻¹]ˣ}
    (hv : (v : A[T;T⁻¹]) ∈ weightGrading R A 1) (p : ℕ)
    (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R])))
    (x : ↥(weightComponent R A 0 (p + 1)))
    (hx : (x : ⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R])) =
      mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
        exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p
          (mapExteriorPower R A A[T;T⁻¹] p ω)) :
    ((residueHom R A).f (p + 1)).hom x = ω := by
  rw [residueHom_f_succ_apply, hx]
  exact residue_mapExteriorPower_add_wedgeLeft_dlogUnit R A hv p ω' ω

end LaurentDeRham

end

end
