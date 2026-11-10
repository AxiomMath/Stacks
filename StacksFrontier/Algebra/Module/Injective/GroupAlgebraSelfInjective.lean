module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Group algebras over self-injective rings are self-injective

Let `A` be a commutative ring which is injective as a module over itself and `H` a finite group.
Then the group algebra `A[H]` is injective as a left module over itself. Given a left ideal `I`
and an `A[H]`-linear map `f : I → A[H]`, the `A`-linear map `x ↦ f(x)(1)` extends, by injectivity
of `A`, to an `A`-linear map `g : A[H] → A`, and `F(r) = ∑_h g(h⁻¹ r) h` is an `A[H]`-linear
extension of `f`: this is the Frobenius form `(x, y) ↦ (x y)(1)` of `A[H]` at work.

Consequently every finite projective `A[H]`-module is injective (a retract of a finite free
module). For `A = ℤ/ℓⁿ` this is the self-injectivity of `(ℤ/ℓⁿ)[H]` used for the perfectness of
`RΓ_c(U_k̄, D(A[H]))` and in Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `MonoidAlgebra.baer_self`: Baer's criterion for `A[H]` over itself.
* `MonoidAlgebra.injective_self`: `A[H]` is a self-injective ring.
* `Module.injective_of_finite_projective_of_injective_self`: over a self-injective ring, finite
  projective modules are injective.
* `MonoidAlgebra.injective_of_finite_projective`: finite projective `A[H]`-modules are
  injective.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace MonoidAlgebra

variable {A : Type u} [CommRing A] {H : Type v}

/-- An element of a finite group algebra is the sum of its coefficients. -/
theorem sum_single_coeff [Fintype H] (x : MonoidAlgebra A H) :
    ∑ h : H, single h (x.coeff h) = x := by
  classical
  ext g
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]

/-- The coefficient of `h` is the coefficient of `1` in `h⁻¹ x`. -/
theorem coeff_one_single_inv_mul [Group H] (x : MonoidAlgebra A H) (h : H) :
    (single h⁻¹ (1 : A) * x).coeff 1 = x.coeff h := by
  rw [coeff_single_mul_apply, one_mul, inv_inv, mul_one]

/-- The `A[H]`-linear map `r ↦ ∑_h g(h⁻¹ r) h` attached to an `A`-linear form `g` on `A[H]`. -/
noncomputable def frobeniusLift [Group H] [Fintype H] (g : MonoidAlgebra A H →ₗ[A] A) :
    MonoidAlgebra A H →ₗ[MonoidAlgebra A H] MonoidAlgebra A H where
  toFun r := ∑ h : H, single h (g (single h⁻¹ (1 : A) * r))
  map_add' r s := by
    simp only [mul_add, map_add, single_add, Finset.sum_add_distrib]
  map_smul' s r := by
    change ∑ h : H, single h (g (single h⁻¹ (1 : A) * (s * r))) =
      s * ∑ h : H, single h (g (single h⁻¹ (1 : A) * r))
    induction s using MonoidAlgebra.induction_on with
    | of x =>
      calc ∑ h : H, single h (g (single h⁻¹ (1 : A) * (of A H x * r)))
          = ∑ h : H, single (x * h) (g (single (x * h)⁻¹ (1 : A) * (of A H x * r))) :=
            (Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => rfl).symm
        _ = ∑ h : H, of A H x * single h (g (single h⁻¹ (1 : A) * r)) := by
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [MonoidAlgebra.of_apply, single_mul_single, one_mul, ← mul_assoc, single_mul_single,
              mul_one, mul_inv_rev, inv_mul_cancel_right]
        _ = of A H x * ∑ h : H, single h (g (single h⁻¹ (1 : A) * r)) := (Finset.mul_sum ..).symm
    | add s t hs ht =>
      simp only [add_mul, mul_add, map_add, single_add, Finset.sum_add_distrib, hs, ht]
    | smul a s hs =>
      simp only [smul_mul_assoc, mul_smul_comm, map_smul, ← smul_single, ← Finset.smul_sum, hs]

/-- The value of `frobeniusLift g` at `r` is `∑_h g(h⁻¹ r) h`. -/
theorem frobeniusLift_apply [Group H] [Fintype H] (g : MonoidAlgebra A H →ₗ[A] A)
    (r : MonoidAlgebra A H) :
    frobeniusLift g r = ∑ h : H, single h (g (single h⁻¹ (1 : A) * r)) := rfl

/-- **Baer's criterion for a group algebra over a self-injective ring.** -/
theorem baer_self [Group H] [Finite H] (hA : Module.Baer A A) :
    Module.Baer (MonoidAlgebra A H) (MonoidAlgebra A H) := by
  have := Fintype.ofFinite H
  intro I f
  let τ : MonoidAlgebra A H →ₗ[A] A :=
    { toFun := fun x => x.coeff 1
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp }
  obtain ⟨g, hg⟩ := hA.extension_property ((I.subtype).restrictScalars A) Subtype.val_injective
    (τ ∘ₗ (f.restrictScalars A))
  refine ⟨frobeniusLift g, fun x hx => ?_⟩
  rw [frobeniusLift_apply]
  conv_rhs => rw [← sum_single_coeff (f ⟨x, hx⟩)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hmem : single h⁻¹ (1 : A) * x ∈ I := I.smul_mem _ hx
  have := LinearMap.congr_fun hg ⟨_, hmem⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype] at this
  congr 1
  change g (single h⁻¹ (1 : A) * x) = (f ⟨x, hx⟩).coeff h
  rw [this]
  change (f (single h⁻¹ (1 : A) • ⟨x, hx⟩)).coeff 1 = _
  rw [f.map_smul, smul_eq_mul, coeff_one_single_inv_mul]

/-- **A group algebra over a self-injective ring is self-injective.** -/
theorem injective_self [Group H] [Finite H] (hA : Module.Baer A A) :
    Module.Injective (MonoidAlgebra A H) (MonoidAlgebra A H) :=
  (baer_self hA).injective

end MonoidAlgebra

namespace Module

/-- **Over a self-injective ring, finite projective modules are injective**: such a module is a
retract of a finite free module, which is a finite product of copies of the ring. -/
theorem injective_of_finite_projective_of_injective_self (R : Type u) [Ring R]
    (hR : ∀ (n : ℕ), Module.Injective R (Fin n → ULift.{max u w} R))
    (P : Type (max u w)) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] :
    Module.Injective R P := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  let e : (Fin n → ULift.{max u w} R) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.piCongrRight fun _ => ULift.moduleEquiv
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (π ∘ₗ e.toLinearMap) LinearMap.id
    (hπ.comp e.surjective)
  refine ⟨fun X Y _ _ _ _ i hi g => ?_⟩
  obtain ⟨h, hh⟩ := (hR n).out i hi (s ∘ₗ g)
  refine ⟨π ∘ₗ e.toLinearMap ∘ₗ h, fun x => ?_⟩
  have := hh x
  simp only [LinearMap.coe_comp, Function.comp_apply] at this ⊢
  rw [this]
  exact LinearMap.congr_fun hs (g x)

end Module

namespace MonoidAlgebra

variable {A : Type u} [CommRing A] {H : Type v} [Group H] [Finite H]

/-- **Over a group algebra of a finite group over a self-injective ring, finite projective
modules are injective.** -/
theorem injective_of_finite_projective (hA : Module.Baer A A) (P : Type (max u v w))
    [AddCommGroup P] [Module (MonoidAlgebra A H) P] [Module.Finite (MonoidAlgebra A H) P]
    [Module.Projective (MonoidAlgebra A H) P] : Module.Injective (MonoidAlgebra A H) P := by
  have : Module.Injective (MonoidAlgebra A H) (ULift.{max u v w} (MonoidAlgebra A H)) :=
    Module.ulift_injective_of_injective _ (injective_self hA)
  exact Module.injective_of_finite_projective_of_injective_self (MonoidAlgebra A H)
    (fun _ => inferInstance) P

end MonoidAlgebra

