module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import StacksCore.RingTheory.IsQuadraticExtension
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.AdjoinRoot

/-!
# The degree and separability of the quadratic algebra of a node

For a Noetherian nodal local algebra `A` over a field, the closed fibre of its normalization —
the quadratic algebra `Stacks.Curves.quadraticAlgebra A` — is a separable algebra of degree two
over the residue field `κ` of `A`.

## Main results

* `Stacks.Curves.isSeparable_quadraticAlgebra_of_isNodalAlgebra`: the quadratic algebra of a
  node is separable over the residue field.
* `Stacks.Curves.finrank_quadraticAlgebra_of_isNodalAlgebra`: its degree is two.

## References

* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra k A]

omit [IsNoetherianRing A] in
/-- A nodal local algebra has elements `x`, `y` of the maximal ideal whose classes form a basis of
the cotangent space, and a nondegenerate quadratic relation `a x² + b x y + c y² ∈ 𝔪³` whose
leading coefficient `a` is a unit. -/
theorem exists_nodalQuadraticRelation_nonzero (hA : IsNodalAlgebra k A) :
    ∃ (x y : maximalIdeal A)
      (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
      (a b c : A),
      e ⟨0⟩ = (maximalIdeal A).toCotangent x ∧
      e ⟨1⟩ = (maximalIdeal A).toCotangent y ∧
      residue A a ≠ 0 ∧ residue A (4 * a * c - b ^ 2) ≠ 0 ∧
      a * x.1 ^ 2 + b * x.1 * y.1 + c * y.1 ^ 2 ∈ (maximalIdeal A) ^ 3 := by
  classical
  obtain ⟨x, y, e, a, b, c, hx, hy, hdisc, hrel⟩ :=
    (hasNodalQuadraticRelation_iff_exists_basis A).mp hA.2.2
  rcases ne_or_eq (residue A a) 0 with ha | ha0
  · exact ⟨x, y, e, a, b, c, hx, hy, ha, hdisc, hrel⟩
  rcases ne_or_eq (residue A c) 0 with hc | hc0
  · let e' := e.reindex (Equiv.swap (⟨0⟩ : BinaryIndex (ResidueField A)) ⟨1⟩)
    refine ⟨y, x, e', c, b, a, ?_, ?_, hc, ?_, ?_⟩
    · simpa [e'] using hy
    · simpa [e'] using hx
    · convert hdisc using 2
      ring
    · convert hrel using 1
      ring
  have hb : residue A b ≠ 0 := fun hb0 => hdisc (by simp [ha0, hb0, hc0])
  let t : CotangentSpace A ≃ₗ[ResidueField A] CotangentSpace A :=
    LinearEquiv.transvection (f := e.coord ⟨1⟩) (v := -e ⟨0⟩) (by simp)
  let e' := e.map t
  refine ⟨x, y - x, e', a + b + c, b + 2 * c, c, ?_, ?_, ?_, ?_, ?_⟩
  · change t (e ⟨0⟩) = _
    simpa [t, LinearMap.transvection.apply] using hx
  · change t (e ⟨1⟩) = _
    rw [map_sub, ← hx, ← hy]
    simp [t, LinearMap.transvection.apply, sub_eq_add_neg]
  · simpa [ha0, hc0] using hb
  · convert hdisc using 2
    ring
  · convert hrel using 1
    simp only [Submodule.coe_sub]
    ring

omit [IsNoetherianRing A] in
/-- For `a ≠ 0`, `κ[X]/(a X² + b X + c)` is isomorphic to the quadratic algebra `κ[ω]` with
`ω² = -c/a + (-b/a) ω`. -/
theorem quadraticAdjoinRoot_equiv (a b c : ResidueField A) (ha : a ≠ 0) :
    let f : Polynomial (ResidueField A) :=
      Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c
    Nonempty (AdjoinRoot f ≃ₐ[ResidueField A]
      QuadraticAlgebra (ResidueField A) (-(c / a)) (-(b / a))) := by
  let f : Polynomial (ResidueField A) :=
    Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c
  have hf : f ≠ 0 := fun h => by simpa [f, ha] using congrArg (Polynomial.coeff · 2) h
  let pb₁ : PowerBasis (ResidueField A) (AdjoinRoot f) := AdjoinRoot.powerBasis hf
  let pb₂ : PowerBasis (ResidueField A)
      (QuadraticAlgebra (ResidueField A) (-(c / a)) (-(b / a))) :=
    QuadraticAlgebra.powerBasis (-(c / a)) (-(b / a))
  have hmin : minpoly (ResidueField A) pb₁.gen =
      minpoly (ResidueField A) pb₂.gen := by
    have hlc : f.leadingCoeff = a := by simp [f, ha]
    rw [AdjoinRoot.minpoly_powerBasis_gen hf, QuadraticAlgebra.minpoly_omega, hlc]
    ext (_ | _ | _ | n) <;> simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] <;> field_simp
  exact ⟨pb₁.equivOfMinpoly pb₂ hmin⟩

/-- `K[ω]` with `ω² = a + bω` is separable over `K` when `b² + 4a ≠ 0`, in every
characteristic. -/
theorem quadraticAlgebra_isSeparable_of_discriminant {K : Type*} [Field K]
    (a b : K) (hdisc : b ^ 2 + 4 * a ≠ 0) :
    Algebra.IsSeparable K (QuadraticAlgebra K a b) := by
  by_cases htwo : (2 : K) = 0
  · let : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo
    rw [QuadraticAlgebra.isSeparable_iff_omega,
      QuadraticAlgebra.isSeparable_omega_iff_of_char_two]
    have hfour : (4 : K) = 0 := CharP.ofNat_eq_zero' K 2 4 (by norm_num)
    exact isUnit_iff_ne_zero.mpr fun hb => hdisc (by simp [hb, hfour])
  · let : NeZero (2 : K) := ⟨htwo⟩
    rw [QuadraticAlgebra.isSeparable_iff_omega,
      QuadraticAlgebra.isSeparable_omega_iff_of_two_ne_zero]
    exact isUnit_iff_ne_zero.mpr hdisc

/-- The quadratic algebra of a node is isomorphic over the residue field to `κ[ω]` with
`ω² = -c/a + (-b/a) ω`, for some `a ≠ 0`, `b`, `c` with `4 a c - b² ≠ 0`. -/
theorem quadraticAlgebra_equiv_quadraticAlgebra (hA : IsNodalAlgebra k A) :
    ∃ a b c : ResidueField A, a ≠ 0 ∧ 4 * a * c - b ^ 2 ≠ 0 ∧
      Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A]
        QuadraticAlgebra (ResidueField A) (-(c / a)) (-(b / a))) := by
  obtain ⟨x, y, e, a, b, c, hx, hy, ha, hdisc, hrel⟩ :=
    exists_nodalQuadraticRelation_nonzero k A hA
  obtain ⟨e₁⟩ := quadraticAlgebra_equiv_adjoinRoot k A hA x y e hx hy a b c ha hdisc hrel
  obtain ⟨e₂⟩ := quadraticAdjoinRoot_equiv A (residue A a) (residue A b) (residue A c) ha
  refine ⟨residue A a, residue A b, residue A c, ha, ?_, ⟨e₁.trans e₂⟩⟩
  simpa only [map_sub, map_mul, map_pow, map_ofNat] using hdisc

/-- The quadratic algebra of a nodal local ring is separable over its residue field. -/
@[stacks 0CBT "degree_separable"]
public theorem isSeparable_quadraticAlgebra_of_isNodalAlgebra (hA : IsNodalAlgebra k A) :
    Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) := by
  obtain ⟨a, b, c, ha, hdisc, ⟨e⟩⟩ := quadraticAlgebra_equiv_quadraticAlgebra k A hA
  have hquad : (-(b / a)) ^ 2 + 4 * (-(c / a)) ≠ 0 := by
    intro h
    field_simp [ha] at h
    exact hdisc (by linear_combination -h)
  exact (AlgEquiv.Algebra.isSeparable_iff e).mpr
    (quadraticAlgebra_isSeparable_of_discriminant (-(c / a)) (-(b / a)) hquad)

/-- The quadratic algebra of a nodal local ring is a finite module over its residue field. -/
public theorem finite_quadraticAlgebra_of_isNodalAlgebra (hA : IsNodalAlgebra k A) :
    Module.Finite (ResidueField A) (quadraticAlgebra A) := by
  obtain ⟨a, b, c, ha, hdisc, ⟨e⟩⟩ := quadraticAlgebra_equiv_quadraticAlgebra k A hA
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- The quadratic algebra of a nodal local ring has degree two over its residue field. -/
@[stacks 0CBT "degree_separable"]
public theorem finrank_quadraticAlgebra_of_isNodalAlgebra (hA : IsNodalAlgebra k A) :
    Module.finrank (ResidueField A) (quadraticAlgebra A) = 2 := by
  obtain ⟨a, b, c, ha, hdisc, ⟨e⟩⟩ := quadraticAlgebra_equiv_quadraticAlgebra k A hA
  exact e.toLinearEquiv.finrank_eq.trans (Algebra.IsQuadraticExtension.finrank_eq_two _ _)

end Stacks.Curves

end
