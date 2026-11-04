module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# The Poincaré lemma for a polynomial algebra

Let `R` be a commutative ring and `A` an `R`-algebra containing `ℚ`.  This file proves that the
inclusion of de Rham complexes `Ω^•_{A/R} → Ω^•_{A[X]/R}` is a homotopy equivalence, with
homotopy inverse the map induced by evaluation at `0`.

The proof is the classical one.  The degree-one decomposition
`Ω[A[X]⁄R] ≅ (A[X] ⊗_A Ω[A⁄R]) ⊕ A[X] dX` of `PolynomialDeRham.kaehlerProdEquiv`, the splitting
of the exterior powers of a module with a free rank-one summand, and the compatibility of
exterior powers with base change combine into
`Ω^{p+1}_{A[X]/R} ≅ (A[X] ⊗_A Ω^{p+1}_{A/R}) ⊕ (A[X] dX ⊗_A Ω^p_{A/R})`.
A form of degree `p + 1` is therefore uniquely `g ω + dX ∧ (g' ω')`, evaluation at `0` sends it
to `g(0) ω`, and the homotopy sends it to `(∫ g') ω'`, where `∫` is the antiderivative
`Polynomial.integral`.  The homotopy identity then comes down to `∫ (dg/dX) = g - g(0)`.

## Main definitions

* `PolynomialDeRham.deRhamProdEquiv`: the degreewise decomposition
  `Ω^{p+1}_{A[X]/R} ≅ (A[X] ⊗_A Ω^{p+1}_{A/R}) × (A[X] ⊗_A Ω^p_{A/R})`, with
  `PolynomialDeRham.deRhamProdZeroEquiv` the degenerate case `p = 0`.
* `PolynomialDeRham.integralPow`: antidifferentiation in `X` of the `dX`-free part of a form.
* `PolynomialDeRham.inclHomotopyMap`: the homotopy operator `Ω^{p+1}_{A[X]/R} → Ω^p_{A[X]/R}`,
  which sends `g ω + dX ∧ (g' ω')` to `(∫ g') ω'`.
* `PolynomialDeRham.inclHomotopy`: the homotopy from the identity of `Ω^•_{A[X]/R}` to the
  composite `Ω^•_{A[X]/R} → Ω^•_{A/R} → Ω^•_{A[X]/R}`.
* `PolynomialDeRham.inclHomotopyEquiv`: **the Poincaré lemma**, the homotopy equivalence
  `Ω^•_{A/R} ≃ Ω^•_{A[X]/R}`.
* `exteriorPower.mapEquiv`: the exterior power of a linear equivalence.

## Main results

* `KaehlerDifferential.deRhamDifferential_smul`: the Leibniz rule
  `d (b ξ) = d b ∧ ξ + b dξ` for the de Rham differential.
* `KaehlerDifferential.deRhamDifferential_wedgeLeft_D`: `d` anticommutes with `d b ∧ ·`.
* `KaehlerDifferential.D_algebraMap_rat`: a derivation of a `ℚ`-algebra kills the rationals.
* `PolynomialDeRham.coeffDerivation_integral`: antidifferentiation in `X` commutes with
  differentiation of the coefficients.
* `PolynomialDeRham.quasiIso_incl`: `Ω^•_{A/R} → Ω^•_{A[X]/R}` is a quasi-isomorphism.

## Implementation notes

The homotopy operator is not `A[X]`-linear, so it cannot be produced by `exteriorPower.map`.
It is assembled from the three `A[X]`-linear halves of the decomposition — the contraction
`exteriorPower.contraction (PolynomialDeRham.pderivX R A)` against the `dX`-component, the
exterior power `PolynomialDeRham.coeffProjPow` of the coefficient component, and the exterior
power `PolynomialDeRham.mapBaseChangePow` of the base-change inclusion — conjugating
`Polynomial.integral` by `ExteriorAlgebra.exteriorPowerBaseChange` in between.

The properties of `PolynomialDeRham.integralPow` are proved before the local `Algebra A[X] A`
instance of evaluation at `0` is enabled: with that instance `A[X] ⊗_A Ω[A⁄R]` carries two
`A[X]`-actions and the elementary rewrites for the tensor product no longer apply.

## References

* [Stacks 0FUI](https://stacks.math.columbia.edu/tag/0FUI), the Poincaré lemma
-/

open CategoryTheory Function Polynomial

open scoped TensorProduct

@[expose] public section

noncomputable section

universe u

namespace exteriorPower

section WedgeLeft

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Wedging by the zero vector is the zero map. -/
@[simp]
theorem wedgeLeft_zero (n : ℕ) : wedgeLeft (R := R) (M := M) 0 n = 0 := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, wedgeLeft_ιMulti, LinearMap.zero_apply]
  exact (ιMulti R (n + 1)).map_coord_zero 0 (by simp)

/-- Wedging by a vector is additive in the vector. -/
theorem wedgeLeft_add (e e' : M) (n : ℕ) :
    wedgeLeft (R := R) (e + e') n = wedgeLeft e n + wedgeLeft e' n := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, wedgeLeft_ιMulti, LinearMap.add_apply]
  rw [show (Fin.cons (e + e') v : Fin (n + 1) → M) =
      Function.update (Fin.cons e v) 0 (e + e') from by
    funext i; refine Fin.cases ?_ ?_ i <;> simp]
  rw [(ιMulti R (n + 1)).map_update_add]
  congr 1 <;> congr 1 <;> funext i <;> refine Fin.cases ?_ ?_ i <;> simp

/-- Wedging by a vector is homogeneous in the vector. -/
theorem wedgeLeft_smul (c : R) (e : M) (n : ℕ) :
    wedgeLeft (R := R) (c • e) n = c • wedgeLeft e n := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, wedgeLeft_ιMulti, LinearMap.smul_apply]
  rw [show (Fin.cons (c • e) v : Fin (n + 1) → M) =
      Function.update (Fin.cons e v) 0 (c • e) from by
    funext i; refine Fin.cases ?_ ?_ i <;> simp]
  rw [(ιMulti R (n + 1)).map_update_smul (Fin.cons e v) 0 c e]
  congr 2
  funext i; refine Fin.cases ?_ ?_ i <;> simp

/-- Wedging by a vector is natural: pushing forward along `f` and wedging by `e` is wedging by
`f e` and pushing forward. -/
theorem map_comp_wedgeLeft' (f : M →ₗ[R] N) (e : M) (n : ℕ) :
    map (n + 1) f ∘ₗ wedgeLeft e n = wedgeLeft (f e) n ∘ₗ map n f := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, comp_apply,
    wedgeLeft_ιMulti, map_apply_ιMulti]
  congr 1
  funext i; refine Fin.cases ?_ ?_ i <;> simp

/-- Contraction is natural: contracting the image of `f` against `φ` is the image of the
contraction against `φ ∘ f`. -/
theorem contraction_comp_map' (φ : N →ₗ[R] R) (f : M →ₗ[R] N) (n : ℕ) :
    contraction φ n ∘ₗ map (n + 1) f = map n f ∘ₗ contraction (φ ∘ₗ f) n := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, comp_apply, map_apply_ιMulti,
    contraction_ιMulti, map_sum, map_zsmul, map_smul, LinearMap.comp_apply]
  rfl

/-- If `φ` kills both `e` and the image of `f`, then contracting against `φ` annihilates
`e ∧ f_*(·)`. -/
theorem contraction_comp_wedgeLeft_comp_map_eq_zero (φ : N →ₗ[R] R) (f : M →ₗ[R] N) (e : N)
    (he : φ e = 0) (hf : φ ∘ₗ f = 0) (n : ℕ) :
    contraction φ n ∘ₗ wedgeLeft e n ∘ₗ map n f = 0 := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  have hf' (m : M) : φ (f m) = 0 := by
    rw [← LinearMap.comp_apply, hf, LinearMap.zero_apply]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, comp_apply,
    map_apply_ιMulti, wedgeLeft_ιMulti, contraction_ιMulti, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  refine Fin.cases ?_ ?_ i
  · simp [he]
  · intro j; simp [hf']

/-- The Koszul identity when `φ e = 0`: contraction against `φ` and wedging by `e`
anticommute. -/
theorem contraction_comp_wedgeLeft_eq_neg (φ : M →ₗ[R] R) (e : M) (he : φ e = 0) (n : ℕ) :
    contraction φ (n + 1) ∘ₗ wedgeLeft e (n + 1) = -(wedgeLeft e n ∘ₗ contraction φ n) := by
  have h := contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction φ e n
  rw [he, zero_smul] at h
  exact (eq_sub_of_add_eq h).trans (zero_sub _)

/-- If `φ e = 0`, then `ι_φ (e ∧ x) = -(e ∧ ι_φ x)`. -/
theorem contraction_wedgeLeft_of_apply_eq_zero (φ : M →ₗ[R] R) (e : M) (he : φ e = 0) (n : ℕ)
    (x : ↥(⋀[R]^(n + 1) M)) :
    contraction φ (n + 1) (wedgeLeft e (n + 1) x) = -wedgeLeft e n (contraction φ n x) :=
  LinearMap.congr_fun (contraction_comp_wedgeLeft_eq_neg φ e he n) x

/-- Wedging twice by the same vector gives zero: `e ∧ e ∧ x = 0`. -/
theorem wedgeLeft_wedgeLeft (e : M) (n : ℕ) (x : ↥(⋀[R]^n M)) :
    wedgeLeft (R := R) e (n + 1) (wedgeLeft e n x) = 0 :=
  LinearMap.congr_fun (wedgeLeft_comp_wedgeLeft e n) x

/-- The exterior power of a linear equivalence. -/
def mapEquiv (e : M ≃ₗ[R] N) (n : ℕ) : ⋀[R]^n M ≃ₗ[R] ⋀[R]^n N :=
  LinearEquiv.ofLinearMap (map n e.toLinearMap) (map n e.symm.toLinearMap)
    (by rw [← map_comp]; simp) (by rw [← map_comp]; simp)

/-- `exteriorPower.mapEquiv e n` acts as `exteriorPower.map n e`. -/
@[simp]
theorem mapEquiv_apply (e : M ≃ₗ[R] N) (n : ℕ) (x : ↥(⋀[R]^n M)) :
    mapEquiv e n x = map n e.toLinearMap x := rfl

/-- The inverse of `exteriorPower.mapEquiv e n` acts as `exteriorPower.map n e.symm`. -/
@[simp]
theorem mapEquiv_symm_apply (e : M ≃ₗ[R] N) (n : ℕ) (y : ↥(⋀[R]^n N)) :
    (mapEquiv e n).symm y = map n e.symm.toLinearMap y := rfl

end WedgeLeft

section Tower

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- `exteriorPower.mapTower` is compatible with wedging by a vector. -/
theorem mapTower_comp_wedgeLeft (f : M →ₗ[R] N) (e : M) (n : ℕ) :
    mapTower (S := S) (n + 1) f ∘ₗ wedgeLeft e n =
      (wedgeLeft (f e) n).restrictScalars R ∘ₗ mapTower (S := S) n f := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, comp_apply,
    wedgeLeft_ιMulti, mapTower_ιMulti, LinearMap.coe_restrictScalars]
  congr 1
  funext i; refine Fin.cases ?_ ?_ i <;> simp

end Tower

end exteriorPower

namespace KaehlerDifferential

section Rat

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

/-- A derivation of a `ℚ`-algebra kills the rationals: the denominator of `q` is a unit, and
multiplying `d q` by it gives the differential of an integer. -/
theorem D_algebraMap_rat (q : ℚ) : D R A (algebraMap ℚ A q) = 0 := by
  have hden : ((q.den : A)) • D R A (algebraMap ℚ A q) = 0 := by
    have hq : algebraMap ℚ A q * (q.den : A) = (q.num : A) := by
      rw [← map_natCast (algebraMap ℚ A) q.den, ← map_mul, ← map_intCast (algebraMap ℚ A) q.num]
      exact congrArg _ (by exact_mod_cast q.mul_den_eq_num)
    have h := (D R A).leibniz (algebraMap ℚ A q) ((q.den : A))
    rw [hq, Derivation.map_intCast, Derivation.map_natCast, smul_zero, zero_add] at h
    exact h.symm
  have hu : algebraMap ℚ A ((q.den : ℚ)⁻¹) * (q.den : A) = 1 := by
    rw [← map_natCast (algebraMap ℚ A) q.den, ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  calc D R A (algebraMap ℚ A q)
      = (1 : A) • D R A (algebraMap ℚ A q) := (one_smul A _).symm
    _ = algebraMap ℚ A ((q.den : ℚ)⁻¹) • ((q.den : A) • D R A (algebraMap ℚ A q)) := by
        rw [smul_smul, hu]
    _ = 0 := by rw [hden, smul_zero]

/-- The universal derivation of a `ℚ`-algebra is `ℚ`-linear. -/
theorem D_rat_smul (c : ℚ) (a : A) : D R A (c • a) = c • D R A a := by
  rw [Algebra.smul_def, Derivation.leibniz, D_algebraMap_rat, smul_zero, add_zero,
    algebraMap_smul]

end Rat

section Leibniz

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The Leibniz rule for the de Rham differential: `d (b ξ) = d b ∧ ξ + b dξ`. -/
theorem deRhamDifferential_smul (p : ℕ) (b : B) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    deRhamDifferential (A := A) p (b • ξ) =
      exteriorPower.wedgeLeft (D A B b) p ξ + b • deRhamDifferential (A := A) p ξ := by
  refine LinearMap.congr_fun (LinearMap.ext_on
    (Crystalline.span_range_smul_ιMulti_eq_top (R := A) (D A B) (span_range_derivation A B) p)
    (f := (deRhamDifferential (A := A) p) ∘ₗ
      (DistribSMul.toLinearMap A (⋀[B]^p (Ω[B⁄A])) b))
    (g := (exteriorPower.wedgeLeft (D A B b) p).restrictScalars A +
      (DistribSMul.toLinearMap A (⋀[B]^(p + 1) (Ω[B⁄A])) b) ∘ₗ deRhamDifferential (A := A) p)
    ?_) ξ
  rintro _ ⟨v, rfl⟩
  have htail : (fun i : Fin p ↦ D A B (Function.update v 0 (b * v 0) i.succ)) =
      fun i : Fin p ↦ D A B (v i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  have hupd : (fun i ↦ D A B (Function.update v 0 (b * v 0) i)) =
      Function.update (fun j ↦ D A B (v j)) 0 (D A B (b * v 0)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  have hcons : (Fin.cons (D A B b) (fun i ↦ D A B (v i.succ)) : Fin (p + 1) → Ω[B⁄A]) =
      Function.update (fun j ↦ D A B (v j)) 0 (D A B b) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  have hleft : deRhamDifferential (A := A) p
      ((b * v 0) • exteriorPower.ιMulti B p fun i ↦ D A B (v i.succ)) =
      b • exteriorPower.ιMulti B (p + 1) (fun j ↦ D A B (v j)) +
        v 0 • exteriorPower.ιMulti B (p + 1)
          (Function.update (fun j ↦ D A B (v j)) 0 (D A B b)) := by
    have h := deRhamDifferential_smul_ιMulti_D (A := A) p (Function.update v 0 (b * v 0))
    rw [Function.update_self, htail, hupd] at h
    rw [h, Derivation.leibniz, (exteriorPower.ιMulti B (p + 1)).map_update_add,
      (exteriorPower.ιMulti B (p + 1)).map_update_smul,
      (exteriorPower.ιMulti B (p + 1)).map_update_smul,
      Function.update_eq_self 0 (fun j ↦ D A B (v j))]
  simp only [LinearMap.coe_comp, comp_apply, LinearMap.add_apply, LinearMap.coe_restrictScalars,
    DistribSMul.toLinearMap_apply, smul_smul, hleft, map_smul,
    exteriorPower.wedgeLeft_ιMulti, hcons, deRhamDifferential_smul_ιMulti_D]
  abel

/-- The de Rham differential anticommutes with wedging by an exact one-form. -/
theorem deRhamDifferential_wedgeLeft_D (p : ℕ) (b : B) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    deRhamDifferential (A := A) (p + 1) (exteriorPower.wedgeLeft (D A B b) p ξ) =
      -exteriorPower.wedgeLeft (D A B b) (p + 1) (deRhamDifferential (A := A) p ξ) := by
  have h := deRhamDifferential_comp_self (A := A) p (b • ξ)
  rw [deRhamDifferential_smul, map_add, deRhamDifferential_smul,
    deRhamDifferential_comp_self p ξ, smul_zero, add_zero] at h
  exact (eq_sub_of_add_eq h).trans (zero_sub _)

end Leibniz

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The maps induced by a tower `A → B` are compatible with wedging by a one-form. -/
theorem mapExteriorPower_wedgeLeft (p : ℕ) (α : Ω[A⁄R]) (ω : ⋀[A]^p (Ω[A⁄R])) :
    mapExteriorPower R A B (p + 1) (exteriorPower.wedgeLeft α p ω) =
      exteriorPower.wedgeLeft (map R R A B α) p (mapExteriorPower R A B p ω) :=
  LinearMap.congr_fun (exteriorPower.mapTower_comp_wedgeLeft (S := B) (map R R A B) α p) ω

end KaehlerDifferential

namespace PolynomialDeRham

open KaehlerDifferential

/-! ### The degreewise decomposition -/

section Splitting

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The coefficient component of a relative `p`-form of `A[X]` over `R`: the `p`-th exterior
power of `PolynomialDeRham.coeffProj`. -/
def coeffProjPow (p : ℕ) :
    ⋀[A[X]]^p (Ω[A[X]⁄R]) →ₗ[A[X]] ⋀[A[X]]^p (A[X] ⊗[A] Ω[A⁄R]) :=
  exteriorPower.map p (coeffProj R A)

/-- The base-change inclusion in degree `p`: the `p`-th exterior power of
`KaehlerDifferential.mapBaseChange`. -/
def mapBaseChangePow (p : ℕ) :
    ⋀[A[X]]^p (A[X] ⊗[A] Ω[A⁄R]) →ₗ[A[X]] ⋀[A[X]]^p (Ω[A[X]⁄R]) :=
  exteriorPower.map p (mapBaseChange R A A[X])

/-- The coefficient component is a left inverse of the base-change inclusion in degree `p`. -/
theorem coeffProjPow_comp_mapBaseChangePow (p : ℕ) :
    coeffProjPow R A p ∘ₗ mapBaseChangePow R A p = LinearMap.id := by
  rw [coeffProjPow, mapBaseChangePow, ← exteriorPower.map_comp,
    show (coeffProj R A) ∘ₗ (mapBaseChange R A A[X]) = LinearMap.id from
      LinearMap.ext (coeffProj_mapBaseChange R A), exteriorPower.map_id]

/-- A `dX`-free form has vanishing `dX`-contraction. -/
theorem contraction_comp_mapBaseChangePow (p : ℕ) :
    exteriorPower.contraction (pderivX R A) p ∘ₗ mapBaseChangePow R A (p + 1) = 0 :=
  exteriorPower.contraction_comp_map _ _ (LinearMap.ext (pderivX_mapBaseChange R A)) p

/-- A form divisible by `dX` has vanishing coefficient component. -/
theorem coeffProjPow_comp_wedgeLeft (p : ℕ) :
    coeffProjPow R A (p + 1) ∘ₗ exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p = 0 :=
  exteriorPower.map_comp_wedgeLeft _ _ (coeffProj_D_X R A) p

/-- Contracting against the `dX`-component undoes wedging by `dX` on `dX`-free forms. -/
theorem contraction_wedgeLeft_mapBaseChangePow (p : ℕ) :
    exteriorPower.contraction (pderivX R A) p ∘ₗ
        exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p ∘ₗ mapBaseChangePow R A p =
      mapBaseChangePow R A p :=
  exteriorPower.contraction_comp_wedgeLeft_comp_map _ _ _ (pderivX_D_X R A)
    (LinearMap.ext (pderivX_mapBaseChange R A)) p

/-- Contracting against the `dX`-component annihilates the wedge of a `dX`-free one-form with a
`dX`-free form. -/
theorem contraction_wedgeLeft_mapBaseChange_comp (ζ : A[X] ⊗[A] Ω[A⁄R]) (p : ℕ) :
    exteriorPower.contraction (pderivX R A) p ∘ₗ
        exteriorPower.wedgeLeft (mapBaseChange R A A[X] ζ) p ∘ₗ mapBaseChangePow R A p = 0 :=
  exteriorPower.contraction_comp_wedgeLeft_comp_map_eq_zero _ _ _ (pderivX_mapBaseChange R A ζ)
    (LinearMap.ext (pderivX_mapBaseChange R A)) p

/-- The Koszul identity for the splitting `Ω[A[X]⁄R] ≅ (A[X] ⊗_A Ω[A⁄R]) ⊕ A[X] dX`. -/
theorem contraction_comp_wedgeLeft_add (p : ℕ) :
    exteriorPower.contraction (pderivX R A) (p + 1) ∘ₗ
        exteriorPower.wedgeLeft (D R A[X] (X : A[X])) (p + 1) +
      exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p ∘ₗ
        exteriorPower.contraction (pderivX R A) p = LinearMap.id := by
  rw [exteriorPower.contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction,
    pderivX_D_X, one_smul]

/-- The coefficient component of the base-change inclusion of `y` is `y`. -/
theorem coeffProjPow_mapBaseChangePow (p : ℕ)
    (y : ↥(⋀[A[X]]^p (A[X] ⊗[A] Ω[A⁄R]))) :
    coeffProjPow R A p (mapBaseChangePow R A p y) = y :=
  LinearMap.congr_fun (coeffProjPow_comp_mapBaseChangePow R A p) y

/-- The `dX`-contraction of a `dX`-free form of degree `p + 1` vanishes. -/
theorem contraction_mapBaseChangePow (p : ℕ)
    (y : ↥(⋀[A[X]]^(p + 1) (A[X] ⊗[A] Ω[A⁄R]))) :
    exteriorPower.contraction (pderivX R A) p (mapBaseChangePow R A (p + 1) y) = 0 :=
  LinearMap.congr_fun (contraction_comp_mapBaseChangePow R A p) y

/-- Contracting `dX ∧ y` against the `dX`-component gives `y` for a `dX`-free form `y`. -/
theorem contraction_wedgeLeft_mapBaseChangePow_apply (p : ℕ)
    (y : ↥(⋀[A[X]]^p (A[X] ⊗[A] Ω[A⁄R]))) :
    exteriorPower.contraction (pderivX R A) p (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
        (mapBaseChangePow R A p y)) = mapBaseChangePow R A p y :=
  LinearMap.congr_fun (contraction_wedgeLeft_mapBaseChangePow R A p) y

/-- The first component of `PolynomialDeRham.kaehlerProdEquiv` is
`PolynomialDeRham.coeffProj`. -/
theorem fst_comp_kaehlerProdEquiv :
    LinearMap.fst A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X] ∘ₗ (kaehlerProdEquiv R A).toLinearMap =
      coeffProj R A := rfl

/-- The second component of `PolynomialDeRham.kaehlerProdEquiv` is
`PolynomialDeRham.pderivX`. -/
theorem snd_comp_kaehlerProdEquiv :
    LinearMap.snd A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X] ∘ₗ (kaehlerProdEquiv R A).toLinearMap =
      pderivX R A := rfl

/-- On the first summand, the inverse of `PolynomialDeRham.kaehlerProdEquiv` is
`KaehlerDifferential.mapBaseChange`. -/
theorem kaehlerProdEquiv_symm_comp_inl :
    (kaehlerProdEquiv R A).symm.toLinearMap ∘ₗ
        LinearMap.inl A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X] = mapBaseChange R A A[X] :=
  LinearMap.ext fun ξ ↦ by simp [kaehlerProdEquiv_symm_apply]

/-- The inverse of `PolynomialDeRham.kaehlerProdEquiv` sends `(0, 1)` to `dX`. -/
theorem kaehlerProdEquiv_symm_zero_one :
    (kaehlerProdEquiv R A).symm.toLinearMap ((0, 1) : (A[X] ⊗[A] Ω[A⁄R]) × A[X]) =
      D R A[X] (X : A[X]) := by
  show (kaehlerProdEquiv R A).symm (0, 1) = _
  rw [kaehlerProdEquiv_symm_apply]
  simp

/-- **The degreewise decomposition of the de Rham complex of `A[X]`**:
`Ω^{p+1}_{A[X]/R} ≅ (A[X] ⊗_A Ω^{p+1}_{A/R}) ⊕ (A[X] dX ⊗_A Ω^p_{A/R})`.  The first component is
the coefficient component and the second is the `dX`-component. -/
def deRhamProdEquiv (p : ℕ) :
    ⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]) ≃ₗ[A[X]]
      (A[X] ⊗[A] ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) × (A[X] ⊗[A] ↥(⋀[A]^p (Ω[A⁄R]))) :=
  (exteriorPower.mapEquiv (kaehlerProdEquiv R A) (p + 1)).trans
    ((exteriorPower.prodRightEquiv A[X] (A[X] ⊗[A] Ω[A⁄R]) p).trans
      ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) (p + 1)).symm.prodCongr
        (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p).symm))

/-- In degree zero the decomposition is `Ω^0_{A[X]/R} ≅ A[X] ⊗_A Ω^0_{A/R}`: there is no
`dX`-component. -/
def deRhamProdZeroEquiv :
    ⋀[A[X]]^0 (Ω[A[X]⁄R]) ≃ₗ[A[X]] A[X] ⊗[A] ↥(⋀[A]^0 (Ω[A⁄R])) :=
  (exteriorPower.mapEquiv (kaehlerProdEquiv R A) 0).trans
    ((exteriorPower.prodRightZeroEquiv A[X] (A[X] ⊗[A] Ω[A⁄R])).trans
      (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) 0).symm)

/-- The components of `PolynomialDeRham.deRhamProdEquiv p x` are the coefficient component of
`x` and the coefficient component of its `dX`-contraction. -/
@[simp]
theorem deRhamProdEquiv_apply (p : ℕ) (x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) :
    deRhamProdEquiv R A p x =
      ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) (p + 1)).symm
          (coeffProjPow R A (p + 1) x),
        (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p).symm
          (coeffProjPow R A p (exteriorPower.contraction (pderivX R A) p x))) := by
  have h1 : exteriorPower.map (p + 1) (LinearMap.fst A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X])
      (exteriorPower.map (p + 1) (kaehlerProdEquiv R A).toLinearMap x) =
      coeffProjPow R A (p + 1) x := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, fst_comp_kaehlerProdEquiv, coeffProjPow]
  have h2 : exteriorPower.map p (LinearMap.fst A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X])
      (exteriorPower.contraction (LinearMap.snd A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X]) p
        (exteriorPower.map (p + 1) (kaehlerProdEquiv R A).toLinearMap x)) =
      coeffProjPow R A p (exteriorPower.contraction (pderivX R A) p x) := by
    rw [← LinearMap.comp_apply (exteriorPower.contraction _ p), exteriorPower.contraction_comp_map',
      snd_comp_kaehlerProdEquiv, LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← exteriorPower.map_comp, fst_comp_kaehlerProdEquiv, coeffProjPow]
  rw [← h1, ← h2]
  rfl

/-- The inverse of `PolynomialDeRham.deRhamProdEquiv p` sends `(ζ, η)` to the sum of the
base-change inclusion of `ζ` and `dX` wedged with the base-change inclusion of `η`. -/
@[simp]
theorem deRhamProdEquiv_symm_apply (p : ℕ) (ζ : A[X] ⊗[A] ↥(⋀[A]^(p + 1) (Ω[A⁄R])))
    (η : A[X] ⊗[A] ↥(⋀[A]^p (Ω[A⁄R]))) :
    (deRhamProdEquiv R A p).symm (ζ, η) =
      mapBaseChangePow R A (p + 1)
          (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) (p + 1) ζ) +
        exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p (mapBaseChangePow R A p
          (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p η)) := by
  have key (y : ↥(⋀[A[X]]^(p + 1) (A[X] ⊗[A] Ω[A⁄R])))
      (z : ↥(⋀[A[X]]^p (A[X] ⊗[A] Ω[A⁄R]))) :
      exteriorPower.map (p + 1) (kaehlerProdEquiv R A).symm.toLinearMap
        (exteriorPower.map (p + 1) (LinearMap.inl A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X]) y +
          exteriorPower.wedgeLeft ((0, 1) : (A[X] ⊗[A] Ω[A⁄R]) × A[X]) p
            (exteriorPower.map p (LinearMap.inl A[X] (A[X] ⊗[A] Ω[A⁄R]) A[X]) z)) =
        mapBaseChangePow R A (p + 1) y +
          exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p (mapBaseChangePow R A p z) := by
    rw [map_add]
    congr 1
    · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, kaehlerProdEquiv_symm_comp_inl,
        mapBaseChangePow]
    · rw [← LinearMap.comp_apply, exteriorPower.map_comp_wedgeLeft', LinearMap.comp_apply,
        kaehlerProdEquiv_symm_zero_one]
      congr 1
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, kaehlerProdEquiv_symm_comp_inl,
        mapBaseChangePow]
  exact key _ _

/-- In degree zero every relative form is `dX`-free. -/
theorem mapBaseChangePow_comp_coeffProjPow_zero :
    mapBaseChangePow R A 0 ∘ₗ coeffProjPow R A 0 = LinearMap.id := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, comp_apply,
    coeffProjPow, mapBaseChangePow, exteriorPower.map_apply_ιMulti, LinearMap.id_coe, id_eq]
  congr 1
  funext i
  exact i.elim0

/-- A form of degree zero is the base-change inclusion of its coefficient component. -/
theorem mapBaseChangePow_coeffProjPow_zero (x : ↥(⋀[A[X]]^0 (Ω[A[X]⁄R]))) :
    mapBaseChangePow R A 0 (coeffProjPow R A 0 x) = x :=
  LinearMap.congr_fun (mapBaseChangePow_comp_coeffProjPow_zero R A) x

/-- The `dX`-contraction of a relative form is `dX`-free. -/
theorem mapBaseChangePow_coeffProjPow_contraction (p : ℕ)
    (x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) :
    mapBaseChangePow R A p (coeffProjPow R A p
        (exteriorPower.contraction (pderivX R A) p x)) =
      exteriorPower.contraction (pderivX R A) p x := by
  have hsplit := (deRhamProdEquiv R A p).symm_apply_apply x
  rw [deRhamProdEquiv_apply, deRhamProdEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at hsplit
  have h := congrArg (exteriorPower.contraction (pderivX R A) p) hsplit
  rwa [map_add, contraction_mapBaseChangePow, contraction_wedgeLeft_mapBaseChangePow_apply,
    zero_add] at h

/-- Every relative form of positive degree is the sum of its coefficient part and `dX` wedged
with its `dX`-contraction. -/
theorem mapBaseChangePow_coeffProjPow_add_wedgeLeft_contraction (p : ℕ)
    (x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) :
    mapBaseChangePow R A (p + 1) (coeffProjPow R A (p + 1) x) +
        exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
          (exteriorPower.contraction (pderivX R A) p x) = x := by
  have hsplit := (deRhamProdEquiv R A p).symm_apply_apply x
  rwa [deRhamProdEquiv_apply, deRhamProdEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, mapBaseChangePow_coeffProjPow_contraction] at hsplit

/-- The pullback `Ω^p_{A/R} → Ω^p_{A[X]/R}` factors through the base-change inclusion. -/
theorem mapExteriorPower_eq_mapBaseChangePow (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A A[X] p ω =
      mapBaseChangePow R A p
        (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p ((1 : A[X]) ⊗ₜ[A] ω)) := by
  refine LinearMap.congr_fun (exteriorPower.linearMap_ext
    (f := mapExteriorPower R A A[X] p)
    (g := (mapBaseChangePow R A p).restrictScalars A ∘ₗ
      ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p).toLinearMap.restrictScalars A)
        ∘ₗ TensorProduct.mk A A[X] (↥(⋀[A]^p (Ω[A⁄R]))) 1)
    (AlternatingMap.ext fun v ↦ ?_)) ω
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, TensorProduct.mk_apply,
    mapExteriorPower_ιMulti, ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, one_smul,
    mapBaseChangePow, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, mapBaseChange_tmul, one_smul]

/-- The base-change inclusion of `g ⊗ ω` is `g` times the pullback of `ω`. -/
theorem mapBaseChangePow_baseChange_tmul (p : ℕ) (g : A[X]) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapBaseChangePow R A p
        (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p (g ⊗ₜ[A] ω)) =
      g • mapExteriorPower R A A[X] p ω := by
  rw [show (g ⊗ₜ[A] ω : A[X] ⊗[A] ↥(⋀[A]^p (Ω[A⁄R]))) = g • ((1 : A[X]) ⊗ₜ[A] ω) from by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul, ← mapExteriorPower_eq_mapBaseChangePow]

/-- A form pulled back from `Ω^{p+1}_{A/R}` is `dX`-free. -/
theorem contraction_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) :
    exteriorPower.contraction (pderivX R A) p (mapExteriorPower R A A[X] (p + 1) ω) = 0 := by
  rw [mapExteriorPower_eq_mapBaseChangePow, contraction_mapBaseChangePow]

/-- Contracting against the `dX`-component undoes wedging by `dX` on a pulled-back form. -/
theorem contraction_wedgeLeft_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.contraction (pderivX R A) p (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
        (mapExteriorPower R A A[X] p ω)) = mapExteriorPower R A A[X] p ω := by
  rw [mapExteriorPower_eq_mapBaseChangePow, contraction_wedgeLeft_mapBaseChangePow_apply]

/-- Contracting against the `dX`-component annihilates a `dX`-free one-form wedged with a
pulled-back form. -/
theorem contraction_wedgeLeft_mapBaseChange_mapExteriorPower (p : ℕ) (ζ : A[X] ⊗[A] Ω[A⁄R])
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.contraction (pderivX R A) p
        (exteriorPower.wedgeLeft (mapBaseChange R A A[X] ζ) p
          (mapExteriorPower R A A[X] p ω)) = 0 := by
  rw [mapExteriorPower_eq_mapBaseChangePow]
  exact LinearMap.congr_fun (contraction_wedgeLeft_mapBaseChange_comp R A ζ p) _

/-- The differential of a polynomial, in the degree-one decomposition. -/
theorem D_eq_mapBaseChange_coeffDerivation_add (q : A[X]) :
    D R A[X] q =
      mapBaseChange R A A[X] (coeffDerivation R A q) + derivative q • D R A[X] (X : A[X]) := by
  have h := mapBaseChange_coeffProj_add_pderivX_smul R A (D R A[X] q)
  rw [coeffProj_D, pderivX_D] at h
  exact h.symm

/-- The differential of `g ω` for `ω` pulled back from `Ω^p_{A/R}`, in the decomposition: the
`dX`-component is `dg/dX`. -/
theorem deRhamDifferential_smul_mapExteriorPower (p : ℕ) (g : A[X])
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    deRhamDifferential (A := R) p (g • mapExteriorPower R A A[X] p ω) =
      exteriorPower.wedgeLeft (mapBaseChange R A A[X] (coeffDerivation R A g)) p
          (mapExteriorPower R A A[X] p ω) +
        derivative g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
          (mapExteriorPower R A A[X] p ω) +
        g • mapExteriorPower R A A[X] (p + 1) (deRhamDifferential (A := R) p ω) := by
  rw [deRhamDifferential_smul, D_eq_mapBaseChange_coeffDerivation_add,
    exteriorPower.wedgeLeft_add, exteriorPower.wedgeLeft_smul, LinearMap.add_apply,
    LinearMap.smul_apply, mapExteriorPower_deRhamDifferential]

/-- Two `R`-linear maps out of `Ω^p_{A[X]/R}` agree on the base-change inclusion of `A[X] ⊗_A
Ω^p_{A/R}` as soon as they agree on the forms `g ω` with `ω` pulled back from `Ω^p_{A/R}`. -/
private theorem eq_on_mapBaseChangePow_of_forall_smul {N : Type*} [AddCommGroup N] [Module R N]
    (p : ℕ) (F G : ⋀[A[X]]^p (Ω[A[X]⁄R]) →ₗ[R] N)
    (h : ∀ (g : A[X]) (ω : ↥(⋀[A]^p (Ω[A⁄R]))),
      F (g • mapExteriorPower R A A[X] p ω) = G (g • mapExteriorPower R A A[X] p ω))
    (ζ : A[X] ⊗[A] ↥(⋀[A]^p (Ω[A⁄R]))) :
    F (mapBaseChangePow R A p (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p ζ)) =
      G (mapBaseChangePow R A p (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p ζ)) := by
  induction ζ using TensorProduct.induction_on with
  | zero => simp
  | tmul g ω => rw [mapBaseChangePow_baseChange_tmul]; exact h g ω
  | add ζ η hζ hη => simp only [map_add, hζ, hη]

end Splitting

/-! ### Antidifferentiation along `X` -/

section Integral

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

/-- Antidifferentiation in `X` commutes with differentiation of the coefficients. -/
theorem coeffDerivation_integral (q : A[X]) :
    coeffDerivation R A (integral q) =
      LinearMap.rTensor (Ω[A⁄R]) (integral (A := A)) (coeffDerivation R A q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
      have hsm : ((n : ℚ) + 1)⁻¹ • D R A a = algebraMap ℚ A (((n : ℚ) + 1)⁻¹) • D R A a :=
        (algebraMap_smul A _ _).symm
      rw [integral_monomial, coeffDerivation_monomial, coeffDerivation_monomial,
        LinearMap.rTensor_tmul, D_rat_smul, hsm, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
      congr 1
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial, X_pow_eq_monomial, integral_monomial,
        Algebra.smul_def, mul_one]

/-- Antidifferentiation in `X` of the `dX`-free part of a relative `p`-form: in the
decomposition `Ω^p_{A[X]/R} ≅ (A[X] ⊗_A Ω^p_{A/R}) ⊕ (A[X] dX ⊗_A Ω^{p-1}_{A/R})` it applies
`Polynomial.integral` to the polynomial factor of the first summand and kills the second. -/
def integralPow (p : ℕ) : ⋀[A[X]]^p (Ω[A[X]⁄R]) →ₗ[R] ⋀[A[X]]^p (Ω[A[X]⁄R]) :=
  (mapBaseChangePow R A p).restrictScalars R ∘ₗ
    ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p).toLinearMap.restrictScalars R ∘ₗ
      ((LinearMap.rTensor (↥(⋀[A]^p (Ω[A⁄R]))) (integral (A := A))).restrictScalars R ∘ₗ
        ((ExteriorAlgebra.exteriorPowerBaseChange A A[X]
              (Ω[A⁄R]) p).symm.toLinearMap.restrictScalars R ∘ₗ
          (coeffProjPow R A p).restrictScalars R)))

/-- `PolynomialDeRham.integralPow` applies `Polynomial.integral` to the polynomial factor of the
coefficient component of a form. -/
theorem integralPow_apply (p : ℕ) (x : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))) :
    integralPow R A p x =
      mapBaseChangePow R A p (ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p
        (LinearMap.rTensor (↥(⋀[A]^p (Ω[A⁄R]))) (integral (A := A))
          ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p).symm
            (coeffProjPow R A p x)))) := rfl

/-- On a form pulled back from `Ω^p_{A/R}` and scaled by a polynomial, antidifferentiation acts
on the polynomial. -/
theorem integralPow_smul_mapExteriorPower (p : ℕ) (g : A[X]) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    integralPow R A p (g • mapExteriorPower R A A[X] p ω) =
      integral g • mapExteriorPower R A A[X] p ω := by
  have hcoeff : coeffProjPow R A p (g • mapExteriorPower R A A[X] p ω) =
      ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p (g ⊗ₜ[A] ω) := by
    rw [mapExteriorPower_eq_mapBaseChangePow, ← map_smul, coeffProjPow_mapBaseChangePow,
      ← map_smul]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [integralPow_apply, hcoeff, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul,
    mapBaseChangePow_baseChange_tmul]

/-- Antidifferentiation in `X` is compatible with wedging by a `dX`-free one-form. -/
theorem integralPow_wedgeLeft_mapBaseChange (p : ℕ) (ζ : A[X] ⊗[A] Ω[A⁄R])
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    integralPow R A (p + 1) (exteriorPower.wedgeLeft (mapBaseChange R A A[X] ζ) p
        (mapExteriorPower R A A[X] p ω)) =
      exteriorPower.wedgeLeft
        (mapBaseChange R A A[X] (LinearMap.rTensor (Ω[A⁄R]) (integral (A := A)) ζ)) p
        (mapExteriorPower R A A[X] p ω) := by
  induction ζ using TensorProduct.induction_on with
  | zero => simp
  | tmul g α =>
      have hw (q : A[X]) : exteriorPower.wedgeLeft (mapBaseChange R A A[X] (q ⊗ₜ[A] α)) p
          (mapExteriorPower R A A[X] p ω) =
          q • mapExteriorPower R A A[X] (p + 1) (exteriorPower.wedgeLeft α p ω) := by
        rw [mapBaseChange_tmul, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
          mapExteriorPower_wedgeLeft]
      rw [hw, integralPow_smul_mapExteriorPower, LinearMap.rTensor_tmul, hw]
  | add ζ η hζ hη =>
      simp only [map_add, exteriorPower.wedgeLeft_add, LinearMap.add_apply, hζ, hη]

/-- The homotopy operator of the Poincaré lemma: in the decomposition
`Ω^{p+1}_{A[X]/R} ≅ (A[X] ⊗_A Ω^{p+1}_{A/R}) ⊕ (A[X] dX ⊗_A Ω^p_{A/R})` it sends
`g ω + dX ∧ (g' ω')` to `(∫ g') ω'`. -/
def inclHomotopyMap (p : ℕ) :
    ⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]) →ₗ[R] ⋀[A[X]]^p (Ω[A[X]⁄R]) :=
  integralPow R A p ∘ₗ (exteriorPower.contraction (pderivX R A) p).restrictScalars R

/-- The homotopy operator is antidifferentiation of the `dX`-contraction. -/
theorem inclHomotopyMap_apply (p : ℕ) (x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) :
    inclHomotopyMap R A p x =
      integralPow R A p (exteriorPower.contraction (pderivX R A) p x) := rfl

/-- The homotopy operator kills the forms pulled back from `Ω^{p+1}_{A/R}`. -/
theorem inclHomotopyMap_smul_mapExteriorPower (p : ℕ) (g : A[X])
    (ω : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) :
    inclHomotopyMap R A p (g • mapExteriorPower R A A[X] (p + 1) ω) = 0 := by
  rw [inclHomotopyMap_apply, map_smul, contraction_mapExteriorPower, smul_zero, map_zero]

/-- The homotopy identity on the forms pulled back from `Ω^p_{A/R}`: the homotopy operator
applied to `d (g ω)` recovers `g ω` minus its value at `X = 0`. -/
theorem inclHomotopyMap_deRhamDifferential_smul (p : ℕ) (g : A[X])
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    inclHomotopyMap R A p (deRhamDifferential (A := R) p
        (g • mapExteriorPower R A A[X] p ω)) =
      (g - C (g.coeff 0)) • mapExteriorPower R A A[X] p ω := by
  have hK : exteriorPower.contraction (pderivX R A) p (deRhamDifferential (A := R) p
      (g • mapExteriorPower R A A[X] p ω)) =
      derivative g • mapExteriorPower R A A[X] p ω := by
    rw [deRhamDifferential_smul_mapExteriorPower, map_add, map_add, map_smul, map_smul,
      contraction_wedgeLeft_mapBaseChange_mapExteriorPower, contraction_wedgeLeft_mapExteriorPower,
      contraction_mapExteriorPower, smul_zero, zero_add, add_zero]
  rw [inclHomotopyMap_apply, hK, integralPow_smul_mapExteriorPower, integral_derivative]

/-- The homotopy identity on the forms divisible by `dX`: there the homotopy operator alone
accounts for the whole form. -/
theorem inclHomotopy_comm_wedgeLeft (p : ℕ) (g : A[X]) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    inclHomotopyMap R A (p + 1) (deRhamDifferential (A := R) (p + 1)
        (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
          (mapExteriorPower R A A[X] p ω))) +
      deRhamDifferential (A := R) p (inclHomotopyMap R A p
        (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
          (mapExteriorPower R A A[X] p ω))) =
      g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
        (mapExteriorPower R A A[X] p ω) := by
  have hh : inclHomotopyMap R A p (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
      (mapExteriorPower R A A[X] p ω)) = integral g • mapExteriorPower R A A[X] p ω := by
    rw [inclHomotopyMap_apply, map_smul, contraction_wedgeLeft_mapExteriorPower,
      integralPow_smul_mapExteriorPower]
  have hdh : deRhamDifferential (A := R) p (inclHomotopyMap R A p
      (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
        (mapExteriorPower R A A[X] p ω))) =
      exteriorPower.wedgeLeft
          (mapBaseChange R A A[X] (coeffDerivation R A (integral g))) p
          (mapExteriorPower R A A[X] p ω) +
        g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
          (mapExteriorPower R A A[X] p ω) +
        integral g • mapExteriorPower R A A[X] (p + 1)
          (deRhamDifferential (A := R) p ω) := by
    rw [hh, deRhamDifferential_smul_mapExteriorPower, derivative_integral]
  have hdy : deRhamDifferential (A := R) (p + 1)
      (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
        (mapExteriorPower R A A[X] p ω)) =
      exteriorPower.wedgeLeft (mapBaseChange R A A[X] (coeffDerivation R A g)) (p + 1)
          (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
            (mapExteriorPower R A A[X] p ω)) -
        g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) (p + 1)
          (mapExteriorPower R A A[X] (p + 1) (deRhamDifferential (A := R) p ω)) := by
    rw [deRhamDifferential_smul, D_eq_mapBaseChange_coeffDerivation_add,
      exteriorPower.wedgeLeft_add, exteriorPower.wedgeLeft_smul, LinearMap.add_apply,
      LinearMap.smul_apply, exteriorPower.wedgeLeft_wedgeLeft, smul_zero, add_zero,
      deRhamDifferential_wedgeLeft_D, ← mapExteriorPower_deRhamDifferential, smul_neg,
      ← sub_eq_add_neg]
  have hKdy : exteriorPower.contraction (pderivX R A) (p + 1)
      (deRhamDifferential (A := R) (p + 1)
        (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
          (mapExteriorPower R A A[X] p ω))) =
      -exteriorPower.wedgeLeft (mapBaseChange R A A[X] (coeffDerivation R A g)) p
          (mapExteriorPower R A A[X] p ω) -
        g • mapExteriorPower R A A[X] (p + 1) (deRhamDifferential (A := R) p ω) := by
    rw [hdy, map_sub, map_smul,
      exteriorPower.contraction_wedgeLeft_of_apply_eq_zero (pderivX R A) _
        (pderivX_mapBaseChange R A (coeffDerivation R A g)) p]
    simp only [contraction_wedgeLeft_mapExteriorPower]
  have step1 : inclHomotopyMap R A (p + 1) (deRhamDifferential (A := R) (p + 1)
      (g • exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p
        (mapExteriorPower R A A[X] p ω))) =
      -exteriorPower.wedgeLeft
          (mapBaseChange R A A[X] (coeffDerivation R A (integral g))) p
          (mapExteriorPower R A A[X] p ω) -
        integral g • mapExteriorPower R A A[X] (p + 1)
          (deRhamDifferential (A := R) p ω) := by
    rw [inclHomotopyMap_apply, hKdy, map_sub, map_neg, integralPow_wedgeLeft_mapBaseChange,
      integralPow_smul_mapExteriorPower, coeffDerivation_integral]
  rw [step1, hdh]
  abel

end Integral

/-! ### The Poincaré lemma -/

section EvalZero

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

attribute [local instance] algebraEvalZero isScalarTowerEvalZero

omit [Algebra ℚ A] in
/-- Evaluation at `0` followed by the inclusion sends `g ω` to `g(0) ω`. -/
theorem mapExteriorPower_evalZero_smul (p : ℕ) (g : A[X]) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A A[X] p (mapExteriorPower R A[X] A p
        (g • mapExteriorPower R A A[X] p ω)) =
      C (g.coeff 0) • mapExteriorPower R A A[X] p ω := by
  have hsmul : g • ω = (g.coeff 0) • ω := by
    rw [← algebraMap_smul A g ω, coeff_zero_eq_eval_zero]
    rfl
  rw [map_smul, mapExteriorPower_evalZero, hsmul, LinearMap.map_smul_of_tower,
    ← algebraMap_smul A[X] (g.coeff 0) (mapExteriorPower R A A[X] p ω)]
  rfl

omit [Algebra ℚ A] in
/-- Evaluation at `0` kills every form divisible by `dX`. -/
theorem mapExteriorPower_evalZero_wedgeLeft (p : ℕ) (ξ : ↥(⋀[A[X]]^p (Ω[A[X]⁄R]))) :
    mapExteriorPower R A[X] A (p + 1) (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p ξ) = 0 := by
  have h : mapExteriorPower R A[X] A (p + 1)
      (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p ξ) =
      exteriorPower.wedgeLeft (map R R A[X] A (D R A[X] (X : A[X]))) p
        (mapExteriorPower R A[X] A p ξ) :=
    LinearMap.congr_fun
      (exteriorPower.mapTower_comp_wedgeLeft (S := A) (map R R A[X] A) (D R A[X] (X : A[X])) p) ξ
  rw [h, map_evalZero_D_X, exteriorPower.wedgeLeft_zero, LinearMap.zero_apply]

/-- The homotopy identity in degree zero. -/
theorem inclHomotopy_comm_zero (x : ↥(⋀[A[X]]^0 (Ω[A[X]⁄R]))) :
    inclHomotopyMap R A 0 (deRhamDifferential (A := R) 0 x) +
        mapExteriorPower R A A[X] 0 (mapExteriorPower R A[X] A 0 x) = x := by
  set F : ⋀[A[X]]^0 (Ω[A[X]⁄R]) →ₗ[R] ⋀[A[X]]^0 (Ω[A[X]⁄R]) :=
    inclHomotopyMap R A 0 ∘ₗ (deRhamDifferential (A := R) 0) +
      (mapExteriorPower R A A[X] 0).restrictScalars R ∘ₗ
        (mapExteriorPower R A[X] A 0).restrictScalars R with hF
  have hFapply (y : ↥(⋀[A[X]]^0 (Ω[A[X]⁄R]))) :
      F y = inclHomotopyMap R A 0 (deRhamDifferential (A := R) 0 y) +
        mapExteriorPower R A A[X] 0 (mapExteriorPower R A[X] A 0 y) := by
    rw [hF]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, comp_apply, LinearMap.coe_restrictScalars]
  have h := eq_on_mapBaseChangePow_of_forall_smul R A 0 F LinearMap.id
    (fun g ω ↦ by
      rw [LinearMap.id_apply, hFapply, inclHomotopyMap_deRhamDifferential_smul,
        mapExteriorPower_evalZero_smul, ← add_smul, sub_add_cancel])
    ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) 0).symm (coeffProjPow R A 0 x))
  rwa [LinearEquiv.apply_symm_apply, mapBaseChangePow_coeffProjPow_zero, LinearMap.id_apply,
    hFapply] at h

/-- The homotopy identity in positive degree. -/
theorem inclHomotopy_comm_succ (p : ℕ) (x : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) :
    inclHomotopyMap R A (p + 1) (deRhamDifferential (A := R) (p + 1) x) +
        deRhamDifferential (A := R) p (inclHomotopyMap R A p x) +
        mapExteriorPower R A A[X] (p + 1) (mapExteriorPower R A[X] A (p + 1) x) = x := by
  set F : ⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]) →ₗ[R] ⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]) :=
    inclHomotopyMap R A (p + 1) ∘ₗ (deRhamDifferential (A := R) (p + 1)) +
      ((deRhamDifferential (A := R) p) ∘ₗ inclHomotopyMap R A p +
        (mapExteriorPower R A A[X] (p + 1)).restrictScalars R ∘ₗ
          (mapExteriorPower R A[X] A (p + 1)).restrictScalars R) with hF
  have hFapply (y : ↥(⋀[A[X]]^(p + 1) (Ω[A[X]⁄R]))) :
      F y = inclHomotopyMap R A (p + 1) (deRhamDifferential (A := R) (p + 1) y) +
        deRhamDifferential (A := R) p (inclHomotopyMap R A p y) +
        mapExteriorPower R A A[X] (p + 1) (mapExteriorPower R A[X] A (p + 1) y) := by
    rw [hF]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, comp_apply, LinearMap.coe_restrictScalars]
    abel
  have hbc1 := eq_on_mapBaseChangePow_of_forall_smul R A (p + 1) F LinearMap.id
    (fun g ω ↦ by
      rw [LinearMap.id_apply, hFapply, inclHomotopyMap_deRhamDifferential_smul,
        inclHomotopyMap_smul_mapExteriorPower, map_zero, add_zero,
        mapExteriorPower_evalZero_smul, ← add_smul, sub_add_cancel])
  have hbc2 := eq_on_mapBaseChangePow_of_forall_smul R A p
    (F ∘ₗ (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p).restrictScalars R)
    ((exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p).restrictScalars R)
    (fun g ω ↦ by
      rw [LinearMap.comp_apply, LinearMap.coe_restrictScalars, hFapply,
        mapExteriorPower_evalZero_wedgeLeft, map_zero, add_zero,
        map_smul (exteriorPower.wedgeLeft (D R A[X] (X : A[X])) p)]
      exact inclHomotopy_comm_wedgeLeft R A p g ω)
  have hsplit := mapBaseChangePow_coeffProjPow_add_wedgeLeft_contraction R A p x
  have h1 := hbc1 ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) (p + 1)).symm
    (coeffProjPow R A (p + 1) x))
  have h2 := hbc2 ((ExteriorAlgebra.exteriorPowerBaseChange A A[X] (Ω[A⁄R]) p).symm
    (coeffProjPow R A p (exteriorPower.contraction (pderivX R A) p x)))
  rw [LinearEquiv.apply_symm_apply, LinearMap.id_apply] at h1
  rw [LinearEquiv.apply_symm_apply, mapBaseChangePow_coeffProjPow_contraction,
    LinearMap.comp_apply, LinearMap.coe_restrictScalars] at h2
  have hFx := congrArg F hsplit
  rw [map_add, h1, h2, hsplit, hFapply] at hFx
  exact hFx.symm

/-- The homotopy of the Poincaré lemma: the identity of `Ω^•_{A[X]/R}` is homotopic to the
composite of evaluation at `0` with the inclusion, by the operator sending
`g ω + dX ∧ (g' ω')` to `(∫ g') ω'`. -/
def inclHomotopy :
    Homotopy (𝟙 (deRhamComplex R A[X])) (evalZero R A ≫ incl R A) where
  hom i j :=
    if h : j + 1 = i then
      (eqToHom (by rw [h]) :
          (deRhamComplex R A[X]).X i ⟶ (deRhamComplex R A[X]).X (j + 1)) ≫
        ModuleCat.ofHom (inclHomotopyMap R A j)
    else 0
  zero _ _ w := by rw [dite_eq_right]; exact w
  comm i := by
    match i with
    | 0 =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex, add_zero]
        ext x
        simp only [deRhamComplex_X, HomologicalComplex.id_f, ModuleCat.hom_id, Nat.reduceAdd,
          deRhamComplex_d, zero_add, ↓reduceDIte, HomologicalComplex.comp_f]
        exact (inclHomotopy_comm_zero R A x).symm
    | (p + 1) =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        ext x
        simp only [deRhamComplex_X, HomologicalComplex.id_f, ModuleCat.hom_id, deRhamComplex_d,
          ↓reduceDIte, Category.assoc, HomologicalComplex.comp_f]
        exact (inclHomotopy_comm_succ R A p x).symm

/-- **The Poincaré lemma for a polynomial algebra**: over a `ℚ`-algebra the inclusion
`Ω^•_{A/R} → Ω^•_{A[X]/R}` is a homotopy equivalence, with homotopy inverse the map induced by
evaluation at `0`. -/
@[stacks 0FUI "the affine case: the de Rham complex is unchanged by adjoining a variable"]
def inclHomotopyEquiv : HomotopyEquiv (deRhamComplex R A) (deRhamComplex R A[X]) where
  hom := incl R A
  inv := evalZero R A
  homotopyHomInvId := Homotopy.ofEq (incl_comp_evalZero R A)
  homotopyInvHomId := (inclHomotopy R A).symm

/-- The inclusion `Ω^•_{A/R} → Ω^•_{A[X]/R}` is a quasi-isomorphism. -/
@[stacks 0FUI "the affine case, as a quasi-isomorphism"]
instance quasiIso_incl : QuasiIso (incl R A) :=
  (inclHomotopyEquiv R A).quasiIso_hom

end EvalZero

end PolynomialDeRham
