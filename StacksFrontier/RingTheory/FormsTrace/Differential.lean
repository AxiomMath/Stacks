module

public import StacksFrontier.RingTheory.FormsTrace.Nice
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso

/-!
# Trace maps on forms commute with the de Rham differential

Let `A → B` be finite projective and let `Θ^p : Ω^p_B → Ω^p_A` be a family satisfying
`Stacks.FormsTrace.IsFormsTrace` which is linear over the forms of `A`
(`Stacks.FormsTrace.IsWedgeLinear`). If there is a nice element `h`
(`Stacks.FormsTrace.IsNiceElement`), then `Θ` is a map of de Rham complexes as soon as its
degree-one instance

`Θ¹(d b) = d (Trace_{B/A}(b))`, `b ∈ B`,

holds.

## Main results

* `Stacks.FormsTrace.wedgeLeft_eq_neg_one_pow_smul_wedgeMul`: `e ∧ x = (-1)^p x ∧ e`.
* `Stacks.FormsTrace.IsWedgeLinear.apply_wedgeLeft_map`: `Θ(f^*ω ∧ η) = ω ∧ Θ(η)`.
* `Stacks.FormsTrace.IsFormsTrace.commutesWithD_of_isNiceElement`: `Θ` commutes with `d`, given
  its degree-one instance.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u v

namespace Stacks.FormsTrace

/-- Left wedge multiplication by a vector is right wedge multiplication up to the sign
`(-1)^p`: `e ∧ x = (-1)^p · x ∧ e` for `x` of degree `p`. -/
theorem wedgeLeft_eq_neg_one_pow_smul_wedgeMul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e : M) (p : ℕ) (x : ⋀[R]^p M) :
    exteriorPower.wedgeLeft e p x =
      (-1 : R) ^ p • exteriorPower.wedgeMul p 1 x ⟨ExteriorAlgebra.ι R e,
        exteriorPower.ι_mem_degreeOne e⟩ := by
  refine Subtype.ext ?_
  rw [exteriorPower.coe_wedgeLeft, SetLike.val_smul, exteriorPower.coe_wedgeMul_comm p 1,
    exteriorPower.wedgeMul_apply_coe, Algebra.smul_def, ← mul_assoc, map_pow, map_neg, map_one,
    ← pow_add, mul_one, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A family of maps on forms commutes with a transport of degrees. -/
theorem apply_degCongr (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]) {m n : ℕ}
    (h : m = n) (x : ⋀[B]^m Ω[B⁄ℤ]) :
    Θ n (exteriorPower.degCongr h x) = exteriorPower.degCongr h (Θ m x) := by
  subst h
  rfl

/-- The one-form `d a` pulls back to `d (f a)`, read in the first exterior power. -/
theorem formsMap_one_ι (ω : Ω[A⁄ℤ]) :
    formsMap A B 1 ⟨ExteriorAlgebra.ι A ω, exteriorPower.ι_mem_degreeOne ω⟩ =
      ⟨ExteriorAlgebra.ι B (KaehlerDifferential.map ℤ ℤ A B ω),
        exteriorPower.ι_mem_degreeOne _⟩ :=
  Subtype.ext (by rw [ExteriorAlgebra.powMapₛₗ_coe, ExteriorAlgebra.mapₛₗ_ι]; rfl)

/-- For a family linear over the forms of `A`, `Θ(f^*ω ∧ η) = ω ∧ Θ(η)` for a one-form `ω` of
`A`. -/
theorem IsWedgeLinear.apply_wedgeLeft_map {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]}
    (hW : IsWedgeLinear A B Θ) (ω : Ω[A⁄ℤ]) (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    Θ (p + 1) (exteriorPower.wedgeLeft (KaehlerDifferential.map ℤ ℤ A B ω) p η) =
      exteriorPower.wedgeLeft ω p (Θ p η) := by
  rw [exteriorPower.wedgeLeft_eq_wedgeMul, exteriorPower.wedgeLeft_eq_wedgeMul, apply_degCongr,
    ← formsMap_one_ι, hW]

variable [Module.Finite A B] [Module.Projective A B]

/-- For a family linear over the forms of `A`, if `Θ¹(d b) = d Trace(b)`, then
`Θ(d b ∧ f^*ω) = d Trace(b) ∧ ω`. -/
theorem IsWedgeLinear.apply_wedgeLeft_D_formsMap
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hW : IsWedgeLinear A B Θ) {b : B}
    (h1 : Θ 1 ⟨ExteriorAlgebra.ι B (D ℤ B b), exteriorPower.ι_mem_degreeOne _⟩ =
      ⟨ExteriorAlgebra.ι A (D ℤ A (trace A B b)), exteriorPower.ι_mem_degreeOne _⟩)
    (p : ℕ) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    Θ (p + 1) (exteriorPower.wedgeLeft (D ℤ B b) p (formsMap A B p ω)) =
      exteriorPower.wedgeLeft (D ℤ A (trace A B b)) p ω := by
  rw [wedgeLeft_eq_neg_one_pow_smul_wedgeMul, wedgeLeft_eq_neg_one_pow_smul_wedgeMul,
    show ((-1 : B) ^ p) = algebraMap A B ((-1) ^ p) by simp, algebraMap_smul, map_smul, hW, h1]

/-- The degree-one instance `Θ¹(d b) = d Trace(b)` of compatibility with `d`. -/
def DegreeOneD (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]) : Prop :=
  ∀ b : B, Θ 1 ⟨ExteriorAlgebra.ι B (D ℤ B b), exteriorPower.ι_mem_degreeOne _⟩ =
    ⟨ExteriorAlgebra.ι A (D ℤ A (trace A B b)), exteriorPower.ι_mem_degreeOne _⟩

/-- Given the degree-one instance and wedge-linearity, `Θ` commutes with `d` on `b · f^*ω`:
`Θ(d(b · f^*ω)) = d(Θ(b · f^*ω))`. -/
theorem IsFormsTrace.deRhamDifferential_smul_formsMap
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ)
    (hW : IsWedgeLinear A B Θ) (h1 : DegreeOneD Θ) (p : ℕ) (b : B) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    Θ (p + 1) (deRhamDifferential p (b • formsMap A B p ω)) =
      deRhamDifferential p (Θ p (b • formsMap A B p ω)) := by
  rw [hΘ, deRhamDifferential_smul (A := ℤ), map_add,
    IsWedgeLinear.apply_wedgeLeft_D_formsMap hW (h1 b), ← formsMap_deRhamDifferential, hΘ,
    deRhamDifferential_smul (A := ℤ)]

/-- Given the degree-one instance `Θ¹(d b) = d Trace(b)` and wedge-linearity, `Θ` commutes with
`d` on combinations of pulled back forms. -/
theorem IsFormsTrace.deRhamDifferential_of_mem_pulledBackSpan
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ)
    (hW : IsWedgeLinear A B Θ) (h1 : DegreeOneD Θ)
    {p : ℕ} {x : ⋀[B]^p Ω[B⁄ℤ]} (hx : x ∈ pulledBackSpan A B p) :
    Θ (p + 1) (deRhamDifferential p x) = deRhamDifferential p (Θ p x) := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  rw [map_finsuppSum, map_finsuppSum, map_finsuppSum, map_finsuppSum]
  exact Finsupp.sum_congr fun ω _ => hΘ.deRhamDifferential_smul_formsMap hW h1 p _ ω

/-- If there is a nice element, a family satisfying `IsFormsTrace`, linear over the forms of `A`
and with `Θ¹(d b) = d Trace(b)`, commutes with the de Rham differentials. -/
theorem IsFormsTrace.commutesWithD_of_isNiceElement {h : A} (hh : IsNiceElement A B h)
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ)
    (hW : IsWedgeLinear A B Θ) (h1 : DegreeOneD Θ) : CommutesWithD A B Θ := by
  obtain ⟨N, hN⟩ := hh.exists_pow_smul_mem_pulledBackSpan
  intro p η
  set a : A := (h ^ N) ^ p
  have key := hΘ.deRhamDifferential_of_mem_pulledBackSpan hW h1 (hN p η)
  have hsmul : a • η = algebraMap A B a • η := (algebraMap_smul B a η).symm
  rw [hsmul, deRhamDifferential_smul (A := ℤ), map_add, ← KaehlerDifferential.map_D ℤ ℤ A B,
    hW.apply_wedgeLeft_map, algebraMap_smul, map_smul, ← hsmul, map_smul,
    deRhamDifferential_smul (A := ℤ)] at key
  refine (hh.regular (p + 1)).pow (N * p) ?_
  show h ^ (N * p) • _ = h ^ (N * p) • _
  rw [pow_mul]
  exact add_left_cancel key

end Stacks.FormsTrace

end
