module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.GradedComponents
public import StacksFrontier.RingTheory.DeRham.LaurentHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# The residue sequence of a Laurent polynomial algebra

Let `R` be a commutative ring, `A` an `R`-algebra and `A[T;T⁻¹]` the Laurent polynomial algebra
over `A`, graded by the exponent of `T`.  The de Rham complex of `A[T;T⁻¹]` over `R` inherits that
grading, and its weight-zero part sits in a short exact sequence of complexes

`0 → Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1] → 0`,

the *residue sequence*.  Its first map is the pullback of forms along `A → A[T;T⁻¹]` and its second
is the residue.

The mathematics is the local computation of Stacks 0FUF.  The logarithmic differential `dlog T` and
the constant `1` freely generate `Ω^•_{A[T;T⁻¹]/R,0}` as a right module over `Ω^•_{A/R}`: a
weight-zero relative `p`-form is uniquely `ω' + dlog T ∧ ω` with `ω'` and `ω` pulled back from
`Ω^p_{A/R}` and `Ω^{p-1}_{A/R}`, and the residue is `Res (ω' + dlog T ∧ ω) = ω`.  Since
`d(ω' + dlog T ∧ ω) = d(ω') − dlog T ∧ d(ω)`, the residue is a morphism of complexes exactly when
the shift `Ω^•_{A/R}[-1]` is given the differential `−d`, which is the sign convention of Stacks
011G.

## Main definitions

* `LaurentDeRham.weightGrading`: the grading of `A[T;T⁻¹]` by the exponent of `T`.
* `LaurentDeRham.weightComponent`: the weight-`g` component of `Ω^p_{A[T;T⁻¹]/R}`, namely the
  graded component of differential forms of Stacks 0FU9 for that grading.
* `LaurentDeRham.weightForms`: the explicit description `Tᵍ ω' + Tᵍ dlog T ∧ ω` of the weight-`g`
  forms, built from `LaurentDeRham.weightPullback` and `LaurentDeRham.weightDlog`.
* `LaurentDeRham.deRhamComplexWeightZero`: the weight-zero de Rham complex
  `Ω^•_{A[T;T⁻¹]/R,0}`, as a `CochainComplex (ModuleCat R) ℕ`.
* `LaurentDeRham.deRhamComplexShift`: the shift `Ω^•_{A/R}[-1]`, with `Ω^{p-1}_{A/R}` in degree
  `p`, zero in degree zero and differential `−d`.
* `LaurentDeRham.pullbackRetract`: the retraction of the pullback `Ω^p_{A/R} → Ω^p_{A[T;T⁻¹]/R}`.
* `LaurentDeRham.residue`: the residue `ω' + dlog T ∧ ω ↦ ω` of a relative form.
* `LaurentDeRham.incl` and `LaurentDeRham.residueHom`: the two maps of complexes
  `Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0}` and `Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1]`.
* `LaurentDeRham.residueShortComplex`: the residue sequence, as a short complex of complexes.

## Main results

* `LaurentDeRham.weightComponent_eq_weightForms`: the weight-`g` component of `Ω^p_{A[T;T⁻¹]/R}`
  consists exactly of the forms `Tᵍ ω' + Tᵍ dlog T ∧ ω` pulled back from `A`.
* `LaurentDeRham.exists_of_mem_weightComponent_succ`: its weight-zero case, that `1` and
  `dlog T` generate the weight-zero forms over `Ω^•_{A/R}`.
* `LaurentDeRham.residue_mapExteriorPower_add_wedgeLeft`: the defining formula
  `Res (ω' + dlog T ∧ ω) = ω`.
* `LaurentDeRham.deRhamDifferential_wedgeLeft_dlogT`: `d (dlog T ∧ ξ) = −dlog T ∧ dξ`.
* `LaurentDeRham.deRhamComplexShift_d_succ`: the differential of the shifted complex is `−d`.
* `LaurentDeRham.residue_deRhamDifferential`: the residue intertwines `d` with `−d`, so it is a
  morphism of complexes.
* `LaurentDeRham.shortExact_residueShortComplex`: **the residue sequence is short exact**.

## Implementation notes

The weight-zero part of `Ω^p_{A[T;T⁻¹]/R}` is *defined* as a graded component in the sense of
Stacks 0FU9, `KaehlerDifferential.gradedDifferentialFormComponent`, taken for the grading of
`A[T;T⁻¹]` by `T`-exponent; the explicit description as the forms `ω' + dlog T ∧ ω` is then a
theorem, `weightComponent_eq_weightForms`, so that only one notion of weight occurs.  That theorem
is proved in both directions by reduction to the homogeneous generators
`a₀ ⋅ da₁ ∧ ⋯ ∧ da_p`: the inclusion of the explicit forms into the component rewrites a generator
of `Ω^p_{A/R}` as a homogeneous generator of `Ω^p_{A[T;T⁻¹]/R}` with degree vector `(g, 0, …, 0)`,
respectively `(g-1, 1, 0, …, 0)` for the `dlog T` part, while the reverse inclusion is an
induction over the number of wedge factors, whose steps are that the explicit forms are stable
under multiplication by a monomial and under wedging by the differential of a monomial.  No
expansion of a wedge of sums is needed.

The shifted complex is built by hand as an `ℕ`-indexed cochain complex rather than obtained from
Mathlib's `CochainComplex.shiftFunctor`, which is available only for `ℤ`-indexed complexes while
`KaehlerDifferential.deRhamComplex` is indexed by `ℕ`.  Nothing is lost: the shift by `-1` of a
complex concentrated in nonnegative degrees is again concentrated in nonnegative degrees, with
zero in degree zero.  The two facts that make the construction honest are recorded separately,
`deRhamComplexShift_X_succ` and `deRhamComplexShift_d_succ`: the degree-`p+1` term is
`Ω^p_{A/R}` and the differential is `−d`.  With the opposite sign the residue would not be a
morphism of complexes.

Short exactness is proved degreewise, through
`HomologicalComplex.shortExact_of_degreewise_shortExact`; in each degree the three conditions are
the splitting of the pullback by `pullbackRetract`, the surjectivity of the residue on
`dlog T ∧ ω`, and the explicit description of the weight-zero forms.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF), the residue sequence of
  the complement of the zero section of a line bundle; what is proved here is its local
  computation
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the grading of the de
  Rham complex of a graded algebra
* [Stacks Project, Tag 011G](https://stacks.math.columbia.edu/tag/011G), the shift of a complex
  and its sign
-/

open CategoryTheory Function KaehlerDifferential LaurentPolynomial

open scoped TensorProduct ZeroObject

@[expose] public section

noncomputable section

universe u

namespace KaehlerDifferential

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The pullback `Ω^p_{A/R} → Ω^p_{B/R}` along a tower `R → A → B` factors through base change:
it is the `p`-th exterior power of `KaehlerDifferential.mapBaseChange`, evaluated at `1 ⊗ ω`. -/
theorem mapExteriorPower_eq_map_mapBaseChange (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A B p ω =
      exteriorPower.map p (mapBaseChange R A B)
        (ExteriorAlgebra.exteriorPowerBaseChange A B (Ω[A⁄R]) p ((1 : B) ⊗ₜ[A] ω)) := by
  refine LinearMap.congr_fun (exteriorPower.linearMap_ext
    (f := mapExteriorPower R A B p)
    (g := (exteriorPower.map p (mapBaseChange R A B)).restrictScalars A ∘ₗ
      ((ExteriorAlgebra.exteriorPowerBaseChange A B (Ω[A⁄R]) p).toLinearMap.restrictScalars A)
        ∘ₗ TensorProduct.mk A B (↥(⋀[A]^p (Ω[A⁄R]))) 1)
    (AlternatingMap.ext fun v ↦ ?_)) ω
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, TensorProduct.mk_apply,
    mapExteriorPower_ιMulti, ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, one_smul,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, mapBaseChange_tmul, one_smul]

end KaehlerDifferential

namespace exteriorPower

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Wedging by the negative of a vector. -/
theorem wedgeLeft_neg (e : M) (n : ℕ) : wedgeLeft (R := R) (-e) n = -wedgeLeft e n := by
  have h := wedgeLeft_add (R := R) e (-e) n
  rw [add_neg_cancel, wedgeLeft_zero] at h
  refine LinearMap.ext fun x ↦ ?_
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.add_apply, LinearMap.zero_apply] at hx
  rw [LinearMap.neg_apply]
  exact eq_neg_of_add_eq_zero_right hx.symm

/-- Wedging by two vectors in succession anticommutes. -/
theorem wedgeLeft_wedgeLeft_comm (e f : M) (n : ℕ) (x : ↥(⋀[R]^n M)) :
    wedgeLeft e (n + 1) (wedgeLeft f n x) = -wedgeLeft f (n + 1) (wedgeLeft e n x) := by
  have h : wedgeLeft (R := R) (e + f) (n + 1) (wedgeLeft (e + f) n x) = 0 :=
    wedgeLeft_wedgeLeft (e + f) n x
  rw [wedgeLeft_add, wedgeLeft_add, LinearMap.add_apply, LinearMap.add_apply, map_add, map_add,
    wedgeLeft_wedgeLeft, wedgeLeft_wedgeLeft, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end exteriorPower

namespace LaurentDeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-! ### The weight grading -/

/-- The weight grading of a Laurent polynomial algebra: the degree-`n` part of `A[T;T⁻¹]` is the
`R`-submodule `A Tⁿ` of the monomials of exponent `n`. -/
def weightGrading : ℤ → Submodule R A[T;T⁻¹] :=
  fun n ↦ Submodule.restrictScalars R (AddMonoidAlgebra.grade A n)

/-- The monomial `a Tⁿ` has weight `n`. -/
theorem single_mem_weightGrading (n : ℤ) (a : A) :
    (AddMonoidAlgebra.single n a : A[T;T⁻¹]) ∈ weightGrading R A n :=
  AddMonoidAlgebra.single_mem_grade n a

/-- A constant has weight zero. -/
theorem C_mem_weightGrading (a : A) : (C a : A[T;T⁻¹]) ∈ weightGrading R A 0 := by
  rw [← single_eq_C]
  exact single_mem_weightGrading R A 0 a

/-- The power `Tⁿ` has weight `n`. -/
theorem T_mem_weightGrading (n : ℤ) : (T n : A[T;T⁻¹]) ∈ weightGrading R A n :=
  single_mem_weightGrading R A n 1

/-- A Laurent polynomial of weight `n` is a monomial of exponent `n`. -/
theorem exists_single_of_mem_weightGrading {n : ℤ} {q : A[T;T⁻¹]}
    (hq : q ∈ weightGrading R A n) : ∃ a : A, (AddMonoidAlgebra.single n a : A[T;T⁻¹]) = q := by
  obtain ⟨a, ha⟩ := (AddMonoidAlgebra.mem_grade_iff' A n q).mp hq
  exact ⟨a, by rw [← ha, AddMonoidAlgebra.lsingle_apply]⟩

/-- The weight-`g` component of the relative `p`-forms of `A[T;T⁻¹]` over `R`, the grading of
differential forms of Stacks 0FU9 taken for the weight grading of `A[T;T⁻¹]`. -/
def weightComponent (g : ℤ) (p : ℕ) : Submodule R (⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])) :=
  gradedDifferentialFormComponent (weightGrading R A) p g

/-! ### The explicit description of the weight components -/

/-- A form of weight `g` pulled back from `Ω^p_{A/R}`: the map `ω ↦ Tᵍ ω`. -/
def weightPullback (g : ℤ) (p : ℕ) :
    ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[R] ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])) :=
  DistribSMul.toLinearMap R (↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) (T g : A[T;T⁻¹]) ∘ₗ
    (mapExteriorPower R A A[T;T⁻¹] p).restrictScalars R

/-- `Tᵍ` times the pullback of `ω`. -/
theorem weightPullback_apply (g : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A g p ω = (T g : A[T;T⁻¹]) • mapExteriorPower R A A[T;T⁻¹] p ω := rfl

/-- A form of weight `g` divisible by `dlog T`: the map `ω ↦ Tᵍ dlog T ∧ ω`. -/
def weightDlog (g : ℤ) (p : ℕ) :
    ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[R] ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R])) :=
  DistribSMul.toLinearMap R (↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R]))) (T g : A[T;T⁻¹]) ∘ₗ
    (exteriorPower.wedgeLeft (dlogT R A) p).restrictScalars R ∘ₗ
      (mapExteriorPower R A A[T;T⁻¹] p).restrictScalars R

/-- `Tᵍ` times `dlog T` wedged with the pullback of `ω`. -/
theorem weightDlog_apply (g : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDlog R A g p ω = (T g : A[T;T⁻¹]) •
      exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω) := rfl

/-- The forms `Tᵍ ω' + Tᵍ dlog T ∧ ω` with `ω'` and `ω` pulled back from `A`.  In degree zero
there is no `dlog T` summand.  This is the explicit description of the weight-`g` component
`LaurentDeRham.weightComponent`. -/
def weightForms (g : ℤ) : (p : ℕ) → Submodule R (⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))
  | 0 => LinearMap.range (weightPullback R A g 0)
  | p + 1 => LinearMap.range (weightPullback R A g (p + 1)) ⊔
      LinearMap.range (weightDlog R A g p)

/-- In degree zero the weight-`g` forms are the pullbacks scaled by `Tᵍ`. -/
theorem weightForms_zero (g : ℤ) :
    weightForms R A g 0 = LinearMap.range (weightPullback R A g 0) := rfl

/-- In positive degree the weight-`g` forms are `Tᵍ ω' + Tᵍ dlog T ∧ ω`. -/
theorem weightForms_succ (g : ℤ) (p : ℕ) :
    weightForms R A g (p + 1) = LinearMap.range (weightPullback R A g (p + 1)) ⊔
      LinearMap.range (weightDlog R A g p) := rfl

/-- A pullback scaled by `Tᵍ` has weight `g`. -/
theorem weightPullback_mem_weightForms (g : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A g p ω ∈ weightForms R A g p := by
  cases p with
  | zero => exact ⟨ω, rfl⟩
  | succ n => exact Submodule.mem_sup_left ⟨ω, rfl⟩

/-- `Tᵍ dlog T` wedged with a pullback has weight `g`. -/
theorem weightDlog_mem_weightForms (g : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDlog R A g p ω ∈ weightForms R A g (p + 1) :=
  Submodule.mem_sup_right ⟨ω, rfl⟩

/-- Every weight-`g` form of positive degree is `Tᵍ ω' + Tᵍ dlog T ∧ ω`. -/
theorem exists_of_mem_weightForms_succ {g : ℤ} {p : ℕ}
    {x : ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightForms R A g (p + 1)) :
    ∃ (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R]))),
      x = weightPullback R A g (p + 1) ω' + weightDlog R A g p ω := by
  rw [weightForms_succ, Submodule.mem_sup] at hx
  obtain ⟨y, ⟨ω', rfl⟩, z, ⟨ω, rfl⟩, rfl⟩ := hx
  exact ⟨ω', ω, rfl⟩

/-- Every weight-`g` form of degree zero is `Tᵍ ω'`. -/
theorem exists_of_mem_weightForms_zero {g : ℤ}
    {x : ↥(⋀[A[T;T⁻¹]]^0 (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightForms R A g 0) :
    ∃ ω' : ↥(⋀[A]^0 (Ω[A⁄R])), x = weightPullback R A g 0 ω' := by
  obtain ⟨ω', rfl⟩ := hx
  exact ⟨ω', rfl⟩

/-! ### The weight components are the explicitly described forms -/

/-- A monomial acts on a relative form as `Tⁿ` times its coefficient. -/
theorem single_smul_pow (n : ℤ) (a : A) (p : ℕ)
    (x : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) :
    (AddMonoidAlgebra.single n a : A[T;T⁻¹]) • x = (T n : A[T;T⁻¹]) • (a • x) := by
  rw [single_eq_C_mul_T, mul_comm, mul_smul, C_eq_algebraMap, algebraMap_smul]

/-- Powers of the variable act on relative forms through their product. -/
theorem T_smul_T_smul_pow (m n : ℤ) (p : ℕ) (x : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) :
    (T m : A[T;T⁻¹]) • (T n : A[T;T⁻¹]) • x = (T (m + n) : A[T;T⁻¹]) • x := by
  rw [smul_smul, ← T_add]

/-- The differential of the monomial `a Tⁿ`, in the degree-one splitting: its coefficient part is
`Tⁿ d a` and its `dlog T`-part is `n a Tⁿ`. -/
theorem D_single (n : ℤ) (a : A) :
    D R A[T;T⁻¹] (AddMonoidAlgebra.single n a) =
      (T n : A[T;T⁻¹]) • map R R A A[T;T⁻¹] (D R A a) +
        (AddMonoidAlgebra.single n (n • a) : A[T;T⁻¹]) • dlogT R A := by
  have h : (AddMonoidAlgebra.single n (n • a) : A[T;T⁻¹]) • dlogT R A =
      (C a : A[T;T⁻¹]) • (n • ((T n : A[T;T⁻¹]) • dlogT R A)) := by
    rw [single_eq_C_mul_T, map_zsmul, smul_mul_assoc, smul_assoc, mul_smul, smul_comm]
  rw [single_eq_C_mul_T, Derivation.leibniz, D_T, ← map_incl_D, h]
  exact add_comm _ _

/-- A monomial scaling of a weight-`g` pullback is a weight-`n + g` pullback. -/
theorem single_smul_weightPullback (g n : ℤ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    (AddMonoidAlgebra.single n a : A[T;T⁻¹]) • weightPullback R A g p ω =
      weightPullback R A (n + g) p (a • ω) := by
  rw [weightPullback_apply, weightPullback_apply, single_smul_pow,
    smul_comm a (T g : A[T;T⁻¹]), T_smul_T_smul_pow, LinearMap.map_smul_of_tower]

/-- A monomial scaling of a weight-`g` `dlog T`-form is a weight-`n + g` `dlog T`-form. -/
theorem single_smul_weightDlog (g n : ℤ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    (AddMonoidAlgebra.single n a : A[T;T⁻¹]) • weightDlog R A g p ω =
      weightDlog R A (n + g) p (a • ω) := by
  rw [weightDlog_apply, weightDlog_apply, single_smul_pow, smul_comm a (T g : A[T;T⁻¹]),
    T_smul_T_smul_pow, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]

/-- Wedging a weight-`g` pullback by the differential of a monomial of weight `n` gives a
weight-`n + g` form. -/
theorem wedgeLeft_D_single_weightPullback (g n : ℤ) (a : A) (p : ℕ)
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (D R A[T;T⁻¹] (AddMonoidAlgebra.single n a)) p
        (weightPullback R A g p ω) =
      weightPullback R A (n + g) (p + 1) (exteriorPower.wedgeLeft (D R A a) p ω) +
        weightDlog R A (n + g) p ((n • a) • ω) := by
  have h1 : exteriorPower.wedgeLeft ((T n : A[T;T⁻¹]) • map R R A A[T;T⁻¹] (D R A a)) p
      (weightPullback R A g p ω) =
      weightPullback R A (n + g) (p + 1) (exteriorPower.wedgeLeft (D R A a) p ω) := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightPullback_apply, map_smul,
      T_smul_T_smul_pow, weightPullback_apply, mapExteriorPower_wedgeLeft]
  have h2 : exteriorPower.wedgeLeft
      ((AddMonoidAlgebra.single n (n • a) : A[T;T⁻¹]) • dlogT R A) p
      (weightPullback R A g p ω) = weightDlog R A (n + g) p ((n • a) • ω) := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightPullback_apply, map_smul,
      single_smul_pow, smul_comm ((n : ℤ) • a) (T g : A[T;T⁻¹]), T_smul_T_smul_pow,
      weightDlog_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
  rw [D_single, exteriorPower.wedgeLeft_add, LinearMap.add_apply, h1, h2]

/-- Wedging a weight-`g` `dlog T`-form by the differential of a monomial of weight `n` gives a
weight-`n + g` form. -/
theorem wedgeLeft_D_single_weightDlog (g n : ℤ) (a : A) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (D R A[T;T⁻¹] (AddMonoidAlgebra.single n a)) (p + 1)
        (weightDlog R A g p ω) =
      weightDlog R A (n + g) (p + 1) (-exteriorPower.wedgeLeft (D R A a) p ω) := by
  have h1 : exteriorPower.wedgeLeft ((T n : A[T;T⁻¹]) • map R R A A[T;T⁻¹] (D R A a)) (p + 1)
      (weightDlog R A g p ω) =
      weightDlog R A (n + g) (p + 1) (-exteriorPower.wedgeLeft (D R A a) p ω) := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightDlog_apply, map_smul,
      T_smul_T_smul_pow, exteriorPower.wedgeLeft_wedgeLeft_comm, weightDlog_apply, map_neg,
      map_neg, mapExteriorPower_wedgeLeft, smul_neg]
  have h2 : exteriorPower.wedgeLeft
      ((AddMonoidAlgebra.single n (n • a) : A[T;T⁻¹]) • dlogT R A) (p + 1)
      (weightDlog R A g p ω) = 0 := by
    rw [exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, weightDlog_apply, map_smul,
      exteriorPower.wedgeLeft_wedgeLeft, smul_zero, smul_zero]
  rw [D_single, exteriorPower.wedgeLeft_add, LinearMap.add_apply, h1, h2, add_zero]

/-- The weight components are closed under multiplication by a monomial. -/
theorem single_smul_mem_weightForms {g : ℤ} (n : ℤ) (a : A) {p : ℕ}
    {x : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightForms R A g p) :
    (AddMonoidAlgebra.single n a : A[T;T⁻¹]) • x ∈ weightForms R A (n + g) p := by
  cases p with
  | zero =>
      obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
      rw [single_smul_weightPullback]
      exact weightPullback_mem_weightForms R A (n + g) 0 _
  | succ q =>
      obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ R A hx
      rw [smul_add, single_smul_weightPullback, single_smul_weightDlog]
      exact Submodule.add_mem _ (weightPullback_mem_weightForms R A (n + g) (q + 1) _)
        (weightDlog_mem_weightForms R A (n + g) q _)

/-- The weight components are closed under wedging by the differential of a monomial. -/
theorem wedgeLeft_D_single_mem_weightForms {g : ℤ} (n : ℤ) (a : A) {p : ℕ}
    {x : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightForms R A g p) :
    exteriorPower.wedgeLeft (D R A[T;T⁻¹] (AddMonoidAlgebra.single n a)) p x ∈
      weightForms R A (n + g) (p + 1) := by
  cases p with
  | zero =>
      obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
      rw [wedgeLeft_D_single_weightPullback]
      exact Submodule.add_mem _ (weightPullback_mem_weightForms R A (n + g) 1 _)
        (weightDlog_mem_weightForms R A (n + g) 0 _)
  | succ q =>
      obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ R A hx
      rw [map_add, wedgeLeft_D_single_weightPullback, wedgeLeft_D_single_weightDlog]
      exact Submodule.add_mem _ (Submodule.add_mem _
        (weightPullback_mem_weightForms R A (n + g) (q + 2) _)
        (weightDlog_mem_weightForms R A (n + g) (q + 1) _))
        (weightDlog_mem_weightForms R A (n + g) (q + 1) _)

/-- A differential monomial in Laurent monomials of prescribed weights lies in the weight
component of the sum of their exponents. -/
theorem smul_ιMulti_D_mem_weightComponent (p : ℕ) (w : Fin (p + 1) → ℤ)
    (q : Fin (p + 1) → A[T;T⁻¹]) (hq : ∀ i, q i ∈ weightGrading R A (w i)) :
    q 0 • exteriorPower.ιMulti A[T;T⁻¹] p (fun i ↦ D R A[T;T⁻¹] (q i.succ)) ∈
      weightComponent R A (∑ i, w i) p :=
  homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
    (weightGrading R A) p w (fun i ↦ ⟨q i, hq i⟩) _ rfl

/-- A differential monomial with coefficient `a Tᵏ` and remaining factors the monomials `qᵢ` of
weight `wᵢ` lies in the component of weight `k + ∑ wᵢ`. -/
theorem single_smul_ιMulti_D_mem_weightComponent (p : ℕ) (k : ℤ) (a : A) (w : Fin p → ℤ)
    (q : Fin p → A[T;T⁻¹]) (hq : ∀ i, q i ∈ weightGrading R A (w i)) :
    (AddMonoidAlgebra.single k a : A[T;T⁻¹]) •
        exteriorPower.ιMulti A[T;T⁻¹] p (fun i ↦ D R A[T;T⁻¹] (q i)) ∈
      weightComponent R A (k + ∑ i, w i) p := by
  have h := smul_ιMulti_D_mem_weightComponent R A p (Fin.cons k w)
    (Fin.cons (AddMonoidAlgebra.single k a) q)
    (Fin.cases (single_mem_weightGrading R A k a) hq)
  rw [Fin.sum_univ_succ] at h
  simpa only [Fin.cons_zero, Fin.cons_succ] using h

/-- A linear map out of `Ω^p_{A/R}` sends everything into a submodule once it does so on the
generators `a₀ da₁ ∧ ⋯ ∧ da_p`. -/
private theorem mem_of_forall_smul_ιMulti_D_mem {M : Type*} [AddCommGroup M] [Module R M] {p : ℕ}
    (f : ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[R] M) (N : Submodule R M)
    (h : ∀ b : Fin (p + 1) → A, f (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) ∈ N)
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) : f ω ∈ N := by
  have htop : (⊤ : Submodule R ↥(⋀[A]^p (Ω[A⁄R]))) ≤ Submodule.comap f N := by
    rw [← Crystalline.span_range_smul_ιMulti_eq_top (R := R) (D R A)
      (span_range_derivation R A) p, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact h b
  exact htop Submodule.mem_top

/-- A pullback scaled by `Tᵍ` lies in the weight-`g` component. -/
theorem weightPullback_mem_weightComponent (g : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A g p ω ∈ weightComponent R A g p := by
  have hgen : ∀ b : Fin (p + 1) → A,
      weightPullback R A g p (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) ∈
        weightComponent R A g p := by
    intro b
    have hmem := single_smul_ιMulti_D_mem_weightComponent R A p g (b 0) (fun _ ↦ 0)
      (fun i ↦ C (b i.succ)) fun i ↦ C_mem_weightGrading R A (b i.succ)
    rw [show g + ∑ _i : Fin p, (0 : ℤ) = g from by simp] at hmem
    rw [weightPullback_apply, map_smul, mapExteriorPower_ιMulti, ← single_smul_pow]
    simp only [map_incl_D]
    exact hmem
  exact mem_of_forall_smul_ιMulti_D_mem R A (weightPullback R A g p) _ hgen ω

/-- `Tᵍ dlog T` wedged with a pullback lies in the weight-`g` component. -/
theorem weightDlog_mem_weightComponent (g : ℤ) (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDlog R A g p ω ∈ weightComponent R A g (p + 1) := by
  have hgen : ∀ b : Fin (p + 1) → A,
      weightDlog R A g p (b 0 • exteriorPower.ιMulti A p fun i ↦ D R A (b i.succ)) ∈
        weightComponent R A g (p + 1) := by
    intro b
    have hmem := single_smul_ιMulti_D_mem_weightComponent R A (p + 1) (g - 1) (b 0)
      (Fin.cons 1 fun _ ↦ 0) (Fin.cons (T 1) fun j ↦ C (b j.succ))
      (Fin.cases (T_mem_weightGrading R A 1) fun j ↦ C_mem_weightGrading R A (b j.succ))
    rw [show g - 1 + ∑ i : Fin (p + 1), (Fin.cons 1 fun _ ↦ 0 : Fin (p + 1) → ℤ) i = g from by
      simp [Fin.sum_univ_succ]] at hmem
    have hfun := Fin.comp_cons (D R A[T;T⁻¹]) (T 1) fun j ↦ C (b j.succ)
    simp only [Function.comp_def] at hfun
    rw [hfun] at hmem
    rw [weightDlog_apply, map_smul, LinearMap.map_smul_of_tower, dlogT,
      exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, mapExteriorPower_ιMulti,
      exteriorPower.wedgeLeft_ιMulti, smul_comm (b 0) (T (-1) : A[T;T⁻¹]),
      T_smul_T_smul_pow, ← sub_eq_add_neg, ← single_smul_pow]
    simp only [map_incl_D]
    exact hmem
  exact mem_of_forall_smul_ιMulti_D_mem R A (weightDlog R A g p) _ hgen ω

/-- The explicitly described forms have the stated weight. -/
theorem weightForms_le_weightComponent (g : ℤ) (p : ℕ) :
    weightForms R A g p ≤ weightComponent R A g p := by
  cases p with
  | zero =>
      rw [weightForms_zero, LinearMap.range_le_iff_comap, eq_top_iff]
      exact fun ω _ ↦ weightPullback_mem_weightComponent R A g 0 ω
  | succ q =>
      rw [weightForms_succ]
      refine sup_le ?_ ?_ <;> rw [LinearMap.range_le_iff_comap, eq_top_iff]
      · exact fun ω _ ↦ weightPullback_mem_weightComponent R A g (q + 1) ω
      · exact fun ω _ ↦ weightDlog_mem_weightComponent R A g q ω

/-- A wedge of differentials of monomials has the weight given by the sum of their exponents. -/
theorem ιMulti_D_single_mem_weightForms (p : ℕ) :
    ∀ (n : Fin p → ℤ) (c : Fin p → A),
      exteriorPower.ιMulti A[T;T⁻¹] p
          (fun i ↦ D R A[T;T⁻¹] (AddMonoidAlgebra.single (n i) (c i))) ∈
        weightForms R A (∑ i, n i) p := by
  induction p with
  | zero =>
      intro n c
      have hkey : exteriorPower.ιMulti A[T;T⁻¹] 0
          (fun i ↦ D R A[T;T⁻¹] (AddMonoidAlgebra.single (n i) (c i))) =
          weightPullback R A 0 0 (exteriorPower.ιMulti A 0 fun i ↦ D R A (c i)) := by
        rw [weightPullback_apply, mapExteriorPower_ιMulti, T_zero, one_smul]
        congr 1
        funext i
        exact i.elim0
      rw [show (∑ i : Fin 0, n i) = 0 from by simp, hkey]
      exact weightPullback_mem_weightForms R A 0 0 _
  | succ q ih =>
      intro n c
      have hcons := (Fin.cons_self_tail fun i ↦
        D R A[T;T⁻¹] (AddMonoidAlgebra.single (n i) (c i))).symm
      rw [hcons, ← exteriorPower.wedgeLeft_ιMulti, Fin.sum_univ_succ]
      exact wedgeLeft_D_single_mem_weightForms R A (n 0) (c 0)
        (ih (fun i ↦ n i.succ) fun i ↦ c i.succ)

/-- Every form of weight `g` is of the explicitly described shape. -/
theorem weightComponent_le_weightForms (g : ℤ) (p : ℕ) :
    weightComponent R A g p ≤ weightForms R A g p := by
  rw [weightComponent, gradedDifferentialFormComponent_le_iff]
  intro degree a hg
  choose c hc using fun i ↦ exists_single_of_mem_weightGrading R A (a i).2
  have hsum : g = degree 0 + ∑ i : Fin p, degree i.succ := by rw [hg, Fin.sum_univ_succ]
  rw [hsum]
  simp only [← hc]
  exact single_smul_mem_weightForms R A (degree 0) (c 0)
    (ιMulti_D_single_mem_weightForms R A p (fun i ↦ degree i.succ) fun i ↦ c i.succ)

/-- **The weight components of the de Rham complex of `A[T;T⁻¹]`, explicitly**: a relative form of
weight `g` is uniquely `Tᵍ ω' + Tᵍ dlog T ∧ ω` with `ω'` and `ω` pulled back from `A`. -/
@[stacks 0FUF "the local computation: 1 and dlog T generate the weight-zero forms"]
theorem weightComponent_eq_weightForms (g : ℤ) (p : ℕ) :
    weightComponent R A g p = weightForms R A g p :=
  le_antisymm (weightComponent_le_weightForms R A g p) (weightForms_le_weightComponent R A g p)

/-! ### The weight-zero forms -/

/-- A pullback has weight zero. -/
theorem weightPullback_zero_apply (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightPullback R A 0 p ω = mapExteriorPower R A A[T;T⁻¹] p ω := by
  rw [weightPullback_apply, T_zero, one_smul]

/-- `dlog T` wedged with a pullback has weight zero. -/
theorem weightDlog_zero_apply (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    weightDlog R A 0 p ω =
      exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω) := by
  rw [weightDlog_apply, T_zero, one_smul]

/-- A form pulled back from `Ω^p_{A/R}` has weight zero. -/
theorem mapExteriorPower_mem_weightComponent (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    mapExteriorPower R A A[T;T⁻¹] p ω ∈ weightComponent R A 0 p := by
  rw [← weightPullback_zero_apply]
  exact weightPullback_mem_weightComponent R A 0 p ω

/-- `dlog T` wedged with a form pulled back from `Ω^p_{A/R}` has weight zero. -/
theorem wedgeLeft_dlogT_mem_weightComponent (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω) ∈
      weightComponent R A 0 (p + 1) := by
  rw [← weightDlog_zero_apply]
  exact weightDlog_mem_weightComponent R A 0 p ω

/-- Every weight-zero form of degree zero is pulled back from `Ω^0_{A/R}`. -/
theorem exists_of_mem_weightComponent_zero {x : ↥(⋀[A[T;T⁻¹]]^0 (Ω[A[T;T⁻¹]⁄R]))}
    (hx : x ∈ weightComponent R A 0 0) :
    ∃ ω' : ↥(⋀[A]^0 (Ω[A⁄R])), x = mapExteriorPower R A A[T;T⁻¹] 0 ω' := by
  rw [weightComponent_eq_weightForms] at hx
  obtain ⟨ω', rfl⟩ := exists_of_mem_weightForms_zero R A hx
  exact ⟨ω', weightPullback_zero_apply R A 0 ω'⟩

/-- **Every weight-zero form of positive degree is `ω' + dlog T ∧ ω`** with `ω'` and `ω` pulled
back from `A`: the local computation of Stacks 0FUF. -/
theorem exists_of_mem_weightComponent_succ {p : ℕ}
    {x : ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightComponent R A 0 (p + 1)) :
    ∃ (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R]))),
      x = mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
        exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω) := by
  rw [weightComponent_eq_weightForms] at hx
  obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightForms_succ R A hx
  exact ⟨ω', ω, by rw [weightPullback_zero_apply, weightDlog_zero_apply]⟩

/-! ### The residue -/

/-- The constant term of a Laurent polynomial, as an `A`-linear map. -/
def constCoeff : A[T;T⁻¹] →ₗ[A] A :=
  Finsupp.lapply 0 ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv A).toLinearMap

/-- The constant term of `1` is `1`. -/
@[simp]
theorem constCoeff_one : constCoeff A (1 : A[T;T⁻¹]) = 1 := by
  rw [constCoeff, ← single_zero_one_eq_one]
  simp

/-- The constant term of the Laurent coefficient of a tensor. -/
def constCoeffTensor (p : ℕ) :
    A[T;T⁻¹] ⊗[A] ↥(⋀[A]^p (Ω[A⁄R])) →ₗ[A] ↥(⋀[A]^p (Ω[A⁄R])) :=
  (TensorProduct.lid A ↥(⋀[A]^p (Ω[A⁄R]))).toLinearMap ∘ₗ
    LinearMap.rTensor ↥(⋀[A]^p (Ω[A⁄R])) (constCoeff A)

/-- The constant term of `1 ⊗ ω` is `ω`. -/
@[simp]
theorem constCoeffTensor_one_tmul (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    constCoeffTensor R A p ((1 : A[T;T⁻¹]) ⊗ₜ[A] ω) = ω := by
  rw [constCoeffTensor]
  simp

/-- The retraction of the pullback `Ω^p_{A/R} → Ω^p_{A[T;T⁻¹]/R}`: the coefficient component of a
form, with the constant term taken in its Laurent variable. -/
def pullbackRetract (p : ℕ) :
    ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])) →ₗ[R] ↥(⋀[A]^p (Ω[A⁄R])) :=
  (constCoeffTensor R A p).restrictScalars R ∘ₗ
    ((ExteriorAlgebra.exteriorPowerBaseChange A A[T;T⁻¹]
        (Ω[A⁄R]) p).symm.toLinearMap.restrictScalars R ∘ₗ
      (coeffProjPow R A p).restrictScalars R)

/-- The coefficient component of a pullback is `1 ⊗ ω`. -/
theorem coeffProjPow_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    coeffProjPow R A p (mapExteriorPower R A A[T;T⁻¹] p ω) =
      ExteriorAlgebra.exteriorPowerBaseChange A A[T;T⁻¹] (Ω[A⁄R]) p ((1 : A[T;T⁻¹]) ⊗ₜ[A] ω) := by
  have h : exteriorPower.map p (mapBaseChange R A A[T;T⁻¹]) = mapBaseChangePow R A p := rfl
  rw [mapExteriorPower_eq_map_mapBaseChange, h, coeffProjPow_mapBaseChangePow]

/-- The retraction undoes the pullback. -/
@[simp]
theorem pullbackRetract_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    pullbackRetract R A p (mapExteriorPower R A A[T;T⁻¹] p ω) = ω := by
  rw [pullbackRetract]
  simp only [LinearMap.coe_comp, comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    coeffProjPow_mapExteriorPower, LinearEquiv.symm_apply_apply, constCoeffTensor_one_tmul]

/-- A form pulled back from `Ω^{p+1}_{A/R}` has no `dlog T`-component. -/
@[simp]
theorem contraction_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) :
    exteriorPower.contraction (dlogProj R A) p
      (mapExteriorPower R A A[T;T⁻¹] (p + 1) ω) = 0 := by
  have h : exteriorPower.map (p + 1) (mapBaseChange R A A[T;T⁻¹]) = mapBaseChangePow R A (p + 1) :=
    rfl
  rw [mapExteriorPower_eq_map_mapBaseChange, h, contraction_mapBaseChangePow]

/-- Contracting against the `dlog T`-component undoes wedging by `dlog T` on a pullback. -/
@[simp]
theorem contraction_wedgeLeft_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    exteriorPower.contraction (dlogProj R A) p (exteriorPower.wedgeLeft (dlogT R A) p
        (mapExteriorPower R A A[T;T⁻¹] p ω)) = mapExteriorPower R A A[T;T⁻¹] p ω := by
  have h : exteriorPower.map p (mapBaseChange R A A[T;T⁻¹]) = mapBaseChangePow R A p := rfl
  rw [mapExteriorPower_eq_map_mapBaseChange, h, contraction_wedgeLeft_mapBaseChangePow_apply]

/-- **The residue of a relative form**: the `dlog T`-component of `ω' + dlog T ∧ ω` is `ω`.  It is
defined on all of `Ω^{p+1}_{A[T;T⁻¹]/R}` by contracting against `dlog T` and retracting the
pullback, and on the weight-zero part it is the residue map of Stacks 0FUF. -/
def residue (p : ℕ) :
    ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R])) →ₗ[R] ↥(⋀[A]^p (Ω[A⁄R])) :=
  pullbackRetract R A p ∘ₗ (exteriorPower.contraction (dlogProj R A) p).restrictScalars R

/-- The residue is the retraction of the `dlog T`-contraction. -/
theorem residue_apply (p : ℕ) (x : ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R]))) :
    residue R A p x =
      pullbackRetract R A p (exteriorPower.contraction (dlogProj R A) p x) := rfl

/-- **The defining formula of the residue**: `Res (ω' + dlog T ∧ ω) = ω`. -/
@[stacks 0FUF "the local computation: the defining formula for the residue"]
theorem residue_mapExteriorPower_add_wedgeLeft (p : ℕ) (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R])))
    (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    residue R A p (mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
        exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω)) = ω := by
  rw [residue_apply, map_add, contraction_mapExteriorPower, contraction_wedgeLeft_mapExteriorPower,
    zero_add, pullbackRetract_mapExteriorPower]

/-- The residue kills the pullbacks. -/
@[simp]
theorem residue_mapExteriorPower (p : ℕ) (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) :
    residue R A p (mapExteriorPower R A A[T;T⁻¹] (p + 1) ω') = 0 := by
  rw [residue_apply, contraction_mapExteriorPower, map_zero]

/-- The residue of `dlog T ∧ ω` is `ω`. -/
@[simp]
theorem residue_wedgeLeft_mapExteriorPower (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    residue R A p (exteriorPower.wedgeLeft (dlogT R A) p
      (mapExteriorPower R A A[T;T⁻¹] p ω)) = ω := by
  rw [residue_apply, contraction_wedgeLeft_mapExteriorPower, pullbackRetract_mapExteriorPower]

/-! ### The differential of a weight-zero form -/

/-- **The de Rham differential anticommutes with `dlog T ∧ ·`**: this is the sign that the shift
in the residue sequence carries.  Unlike `dlog T`, the one-form `d T` is exact, and the identity
is deduced from the anticommutation for exact one-forms and `d(T⁻¹) = -T⁻¹ dlog T`. -/
theorem deRhamDifferential_wedgeLeft_dlogT (p : ℕ)
    (ξ : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) :
    deRhamDifferential (A := R) (p + 1) (exteriorPower.wedgeLeft (dlogT R A) p ξ) =
      -exteriorPower.wedgeLeft (dlogT R A) (p + 1) (deRhamDifferential (A := R) p ξ) := by
  have hy : ∀ (q : ℕ) (η : ↥(⋀[A[T;T⁻¹]]^q (Ω[A[T;T⁻¹]⁄R]))),
      exteriorPower.wedgeLeft (dlogT R A) q η =
        (T (-1) : A[T;T⁻¹]) • exteriorPower.wedgeLeft (D R A[T;T⁻¹] (T 1)) q η := fun q η ↦ by
    rw [← T_smul_dlogT, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, smul_smul, ← T_add,
      show (-1 : ℤ) + 1 = 0 from by ring, T_zero, one_smul]
  have h1 : exteriorPower.wedgeLeft (D R A[T;T⁻¹] (T (-1))) (p + 1)
      (exteriorPower.wedgeLeft (D R A[T;T⁻¹] (T 1)) p ξ) = 0 := by
    rw [D_T_neg_one, exteriorPower.wedgeLeft_neg, LinearMap.neg_apply,
      exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, ← T_smul_dlogT,
      exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, map_smul,
      exteriorPower.wedgeLeft_wedgeLeft, smul_zero, smul_zero, neg_zero]
  rw [hy p ξ, deRhamDifferential_smul, h1, zero_add, deRhamDifferential_wedgeLeft_D, smul_neg,
    ← hy]

/-- The differential of a weight-zero form `ω' + dlog T ∧ ω`, in the same shape:
`d(ω' + dlog T ∧ ω) = dω' − dlog T ∧ dω`. -/
theorem deRhamDifferential_mapExteriorPower_add_wedgeLeft (p : ℕ)
    (ω' : ↥(⋀[A]^(p + 1) (Ω[A⁄R]))) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    deRhamDifferential (A := R) (p + 1) (mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
        exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω)) =
      mapExteriorPower R A A[T;T⁻¹] (p + 2)
          (deRhamDifferential (A := R) (p + 1) ω') +
        exteriorPower.wedgeLeft (dlogT R A) (p + 1) (mapExteriorPower R A A[T;T⁻¹] (p + 1)
          (-deRhamDifferential (A := R) p ω)) := by
  rw [map_add, ← mapExteriorPower_deRhamDifferential, deRhamDifferential_wedgeLeft_dlogT,
    ← mapExteriorPower_deRhamDifferential, map_neg, map_neg]

/-- The de Rham differential preserves weight zero. -/
theorem deRhamDifferential_mem_weightComponent (p : ℕ)
    {x : ↥(⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightComponent R A 0 p) :
    deRhamDifferential (A := R) p x ∈ weightComponent R A 0 (p + 1) := by
  cases p with
  | zero =>
      obtain ⟨ω', rfl⟩ := exists_of_mem_weightComponent_zero R A hx
      rw [← mapExteriorPower_deRhamDifferential]
      exact mapExteriorPower_mem_weightComponent R A 1 _
  | succ q =>
      obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightComponent_succ R A hx
      rw [deRhamDifferential_mapExteriorPower_add_wedgeLeft]
      exact Submodule.add_mem _ (mapExteriorPower_mem_weightComponent R A (q + 2) _)
        (wedgeLeft_dlogT_mem_weightComponent R A (q + 1) _)

/-- The residue of the differential of a weight-zero form of degree zero vanishes: a weight-zero
`0`-form is pulled back from `A`, and so is its differential. -/
theorem residue_deRhamDifferential_zero {x : ↥(⋀[A[T;T⁻¹]]^0 (Ω[A[T;T⁻¹]⁄R]))}
    (hx : x ∈ weightComponent R A 0 0) :
    residue R A 0 (deRhamDifferential (A := R) 0 x) = 0 := by
  obtain ⟨ω', rfl⟩ := exists_of_mem_weightComponent_zero R A hx
  rw [← mapExteriorPower_deRhamDifferential, residue_mapExteriorPower]

/-- **The residue intertwines the de Rham differential with `−d`**, the differential of the
shifted complex: `Res (d ξ) = −d (Res ξ)` on weight-zero forms. -/
theorem residue_deRhamDifferential (p : ℕ)
    {x : ↥(⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R]))} (hx : x ∈ weightComponent R A 0 (p + 1)) :
    residue R A (p + 1) (deRhamDifferential (A := R) (p + 1) x) =
      -deRhamDifferential (A := R) p (residue R A p x) := by
  obtain ⟨ω', ω, rfl⟩ := exists_of_mem_weightComponent_succ R A hx
  rw [deRhamDifferential_mapExteriorPower_add_wedgeLeft,
    residue_mapExteriorPower_add_wedgeLeft, residue_mapExteriorPower_add_wedgeLeft]

/-! ### The residue sequence of complexes -/

/-- The de Rham differential on weight-zero forms. -/
def deRhamDifferentialWeightZero (p : ℕ) :
    ↥(weightComponent R A 0 p) →ₗ[R] ↥(weightComponent R A 0 (p + 1)) :=
  (deRhamDifferential (A := R) p).restrict fun _ hx ↦
    deRhamDifferential_mem_weightComponent R A p hx

/-- The differential on weight-zero forms is the de Rham differential. -/
@[simp]
theorem coe_deRhamDifferentialWeightZero (p : ℕ) (x : ↥(weightComponent R A 0 p)) :
    (deRhamDifferentialWeightZero R A p x : ⋀[A[T;T⁻¹]]^(p + 1) (Ω[A[T;T⁻¹]⁄R])) =
      deRhamDifferential (A := R) p x := rfl

/-- The de Rham differential of weight-zero forms squares to zero. -/
theorem deRhamDifferentialWeightZero_comp_self (p : ℕ) :
    (deRhamDifferentialWeightZero R A (p + 1)).comp (deRhamDifferentialWeightZero R A p) = 0 :=
  LinearMap.ext fun x ↦ by
    refine Subtype.ext ?_
    exact deRhamDifferential_comp_self (A := R) p x.1

/-- **The weight-zero de Rham complex** `Ω^•_{A[T;T⁻¹]/R,0}`: the subcomplex of
`Ω^•_{A[T;T⁻¹]/R}` of the forms of weight zero for the grading of `A[T;T⁻¹]` by `T`-exponent. -/
def deRhamComplexWeightZero : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R ↥(weightComponent R A 0 p))
    (fun p ↦ ModuleCat.ofHom (deRhamDifferentialWeightZero R A p))
    fun p ↦ ModuleCat.hom_ext (deRhamDifferentialWeightZero_comp_self R A p)

/-- The degree-`p` term of the weight-zero de Rham complex is the weight-zero part of
`Ω^p_{A[T;T⁻¹]/R}`. -/
@[simp]
theorem deRhamComplexWeightZero_X (p : ℕ) :
    (deRhamComplexWeightZero R A).X p = ModuleCat.of R ↥(weightComponent R A 0 p) := rfl

/-- The arrow of the weight-zero de Rham complex out of degree `p` is the de Rham
differential. -/
@[simp]
theorem deRhamComplexWeightZero_d (p : ℕ) :
    (deRhamComplexWeightZero R A).d p (p + 1) =
      ModuleCat.ofHom (deRhamDifferentialWeightZero R A p) := by
  apply CochainComplex.of_d

/-- The degree-`p` term of the shifted complex `Ω^•_{A/R}[-1]`: zero in degree zero and
`Ω^{p-1}_{A/R}` in positive degree. -/
def deRhamShiftX : ℕ → ModuleCat.{u} R
  | 0 => 0
  | p + 1 => ModuleCat.of R ↥(⋀[A]^p (Ω[A⁄R]))

/-- The differential of the shifted complex `Ω^•_{A/R}[-1]`: minus the de Rham differential, the
sign that the shift of Stacks 011G carries. -/
def deRhamShiftD : (p : ℕ) → (deRhamShiftX R A p ⟶ deRhamShiftX R A (p + 1))
  | 0 => 0
  | p + 1 => ModuleCat.ofHom (-deRhamDifferential (A := R) (B := A) p)

/-- **The shift `Ω^•_{A/R}[-1]`** of the de Rham complex: `Ω^{p-1}_{A/R}` in degree `p`, zero in
degree zero, and differential `−d`. -/
def deRhamComplexShift : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (deRhamShiftX R A) (deRhamShiftD R A) fun p ↦ by
    cases p with
    | zero => rw [show deRhamShiftD R A 0 = 0 from rfl, Limits.zero_comp]
    | succ q =>
        rw [show deRhamShiftD R A (q + 1) =
            ModuleCat.ofHom (-deRhamDifferential (A := R) (B := A) q) from rfl,
          show deRhamShiftD R A (q + 1 + 1) =
            ModuleCat.ofHom (-deRhamDifferential (A := R) (B := A) (q + 1)) from rfl]
        refine ModuleCat.hom_ext (show (-deRhamDifferential (A := R) (B := A) (q + 1)).comp
            (-deRhamDifferential (A := R) (B := A) q) = 0 from LinearMap.ext fun x ↦ ?_)
        simpa using deRhamDifferential_comp_self (A := R) q x

/-- The shifted complex vanishes in degree zero. -/
theorem deRhamComplexShift_X_zero : (deRhamComplexShift R A).X 0 = 0 := rfl

/-- The degree-`p+1` term of the shifted complex is `Ω^p_{A/R}`. -/
theorem deRhamComplexShift_X_succ (p : ℕ) :
    (deRhamComplexShift R A).X (p + 1) = ModuleCat.of R ↥(⋀[A]^p (Ω[A⁄R])) := rfl

/-- **The differential of the shifted complex is `−d`.** -/
@[simp]
theorem deRhamComplexShift_d_succ (p : ℕ) :
    (deRhamComplexShift R A).d (p + 1) (p + 1 + 1) =
      ModuleCat.ofHom (-deRhamDifferential (A := R) (B := A) p) := by
  apply CochainComplex.of_d

/-- The shifted complex has no arrow out of degree zero. -/
@[simp]
theorem deRhamComplexShift_d_zero : (deRhamComplexShift R A).d 0 1 = 0 :=
  CochainComplex.of_d (deRhamShiftX R A) (deRhamShiftD R A) 0

/-- **The inclusion `Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0}`**: a form pulled back from `A` has weight
zero, and the pullback commutes with the de Rham differentials. -/
def incl : deRhamComplex R A ⟶ deRhamComplexWeightZero R A :=
  CochainComplex.ofHom
    (fun p ↦ ModuleCat.ofHom (((mapExteriorPower R A A[T;T⁻¹] p).restrictScalars R).codRestrict
      (weightComponent R A 0 p) (mapExteriorPower_mem_weightComponent R A p)))
    fun p ↦ by
      ext ω
      simp only [deRhamComplex_d, deRhamComplexWeightZero_d]
      refine Subtype.ext ?_
      exact (mapExteriorPower_deRhamDifferential R A A[T;T⁻¹] p ω).symm

/-- The inclusion is the pullback of forms in every degree. -/
@[simp]
theorem incl_f_apply (p : ℕ) (ω : ↥(⋀[A]^p (Ω[A⁄R]))) :
    ((incl R A).f p).hom ω =
      (⟨mapExteriorPower R A A[T;T⁻¹] p ω, mapExteriorPower_mem_weightComponent R A p ω⟩ :
        ↥(weightComponent R A 0 p)) := rfl

/-- The degreewise residue: zero in degree zero, and the residue of a weight-zero form in
positive degree. -/
def residueF : (p : ℕ) → ((deRhamComplexWeightZero R A).X p ⟶ (deRhamComplexShift R A).X p)
  | 0 => 0
  | p + 1 => ModuleCat.ofHom ((residue R A p).comp (weightComponent R A 0 (p + 1)).subtype)

/-- **The residue map of complexes** `Res : Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1]`, which sends
`ω' + dlog T ∧ ω` to `ω`. -/
def residueHom : deRhamComplexWeightZero R A ⟶ deRhamComplexShift R A :=
  CochainComplex.ofHom (residueF R A) fun p ↦ by
    cases p with
    | zero =>
        ext x
        simp only [deRhamComplexWeightZero_d, show residueF R A 0 = 0 from rfl,
          Limits.zero_comp]
        exact (residue_deRhamDifferential_zero R A x.2).symm
    | succ q =>
        ext x
        simp only [deRhamComplexWeightZero_d, deRhamComplexShift_d_succ]
        exact (residue_deRhamDifferential R A q x.2).symm

/-- The residue map of complexes is the residue in every positive degree. -/
@[simp]
theorem residueHom_f_succ_apply (p : ℕ) (x : ↥(weightComponent R A 0 (p + 1))) :
    ((residueHom R A).f (p + 1)).hom x = residue R A p x := rfl

/-- The residue kills the forms pulled back from `A`, so the composite
`Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1]` vanishes. -/
theorem incl_comp_residueHom : incl R A ≫ residueHom R A = 0 := by
  ext p : 1
  cases p with
  | zero => exact (Limits.isZero_zero (ModuleCat.{u} R)).eq_of_tgt _ _
  | succ q =>
      ext ω
      exact residue_mapExteriorPower R A q ω

/-- **The residue sequence** `0 → Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1] → 0`, as a short
complex of cochain complexes of `R`-modules. -/
def residueShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (incl R A) (residueHom R A) (incl_comp_residueHom R A)

/-- The inclusion is injective in every degree, being split by the retraction
`LaurentDeRham.pullbackRetract` of the pullback. -/
theorem injective_incl_f (p : ℕ) : Function.Injective ((incl R A).f p).hom := fun ω₁ ω₂ h ↦ by
  have h' : mapExteriorPower R A A[T;T⁻¹] p ω₁ = mapExteriorPower R A A[T;T⁻¹] p ω₂ :=
    congrArg (fun y : ↥(weightComponent R A 0 p) ↦
      (y : ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R]))) h
  exact ((pullbackRetract_mapExteriorPower R A p ω₁).symm.trans
    (congrArg (pullbackRetract R A p) h')).trans (pullbackRetract_mapExteriorPower R A p ω₂)

/-- The residue is surjective in every positive degree: it sends `dlog T ∧ ω` to `ω`. -/
theorem surjective_residueHom_f_succ (p : ℕ) :
    Function.Surjective ((residueHom R A).f (p + 1)).hom := fun ω ↦
  ⟨⟨exteriorPower.wedgeLeft (dlogT R A) p (mapExteriorPower R A A[T;T⁻¹] p ω),
      wedgeLeft_dlogT_mem_weightComponent R A p ω⟩,
    residue_wedgeLeft_mapExteriorPower R A p ω⟩

/-- The residue sequence is short exact in every degree. -/
theorem shortExact_map_eval_residueShortComplex (p : ℕ) :
    ((residueShortComplex R A).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) p)).ShortExact := by
  cases p with
  | zero =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro x _
        obtain ⟨ω', hω'⟩ := exists_of_mem_weightComponent_zero R A x.2
        exact ⟨ω', Subtype.ext hω'.symm⟩
      · exact (ModuleCat.mono_iff_injective _).mpr (injective_incl_f R A 0)
      · exact ⟨fun g h _ ↦ (Limits.isZero_zero (ModuleCat.{u} R)).eq_of_src g h⟩
  | succ q =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        obtain ⟨ω', ω, hx'⟩ := exists_of_mem_weightComponent_succ R A x.2
        have hω : ω = 0 := by
          have hres : residue R A q x.1 = 0 := hx
          rw [hx', residue_mapExteriorPower_add_wedgeLeft] at hres
          exact hres
        refine ⟨ω', Subtype.ext ?_⟩
        rw [hx', hω, map_zero, map_zero, add_zero]
        rfl
      · exact (ModuleCat.mono_iff_injective _).mpr (injective_incl_f R A (q + 1))
      · exact (ModuleCat.epi_iff_surjective _).mpr (surjective_residueHom_f_succ R A q)

/-- **The residue short exact sequence of complexes** of Stacks 0FUF, in its affine form:
`0 → Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1] → 0`.  The first map is the pullback of forms
along `A → A[T;T⁻¹]`, the second is the residue `ω' + dlog T ∧ ω ↦ ω`, and the shift carries the
differential `−d`. -/
@[stacks 0FUF "the affine local case: the residue short exact sequence for A[T;T⁻¹] over R"]
theorem shortExact_residueShortComplex : (residueShortComplex R A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (shortExact_map_eval_residueShortComplex R A)

end LaurentDeRham

end

end
