module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a presentation through a square-zero extension

Let `P → B` be a polynomial presentation of an `A`-algebra and let `B' → B` be a surjection of
`A`-algebras whose kernel has square zero. The presentation map lifts to `B'`, and the
restriction of that lift to the relation ideal `J` consequently induces a `B`-linear map from
`J / J²` to the kernel of `B' → B`.

Together with the naive cotangent complex `J / J² → B ⊗[P] Ω[P⁄A]`, whose differential is
Mathlib's `Algebra.Extension.cotangentComplex`, this is the elementary input to the deformation
theory of a square-zero extension.

## Main definitions

* `Algebra.Extension.squareZeroKerModule`: the kernel of a square-zero extension, as a module
  over the quotient.

## Main results

* `Algebra.Generators.exists_lift_and_cotangentMap_to_squareZeroKernel`: the lifted map of
  presentations, together with the induced map from the conormal module to the square-zero
  kernel.

## Implementation notes

A polynomial presentation is `Algebra.Generators`; its associated surjection is `P.toExtension`.
An extension `E : Algebra.Extension A B` packages the surjection `B' → B`, and a homomorphism
`f : P.toExtension.Hom E` is exactly an `A`-algebra lift commuting with the maps to `B`. The
square-zero hypothesis makes `E.ker` a `B`-module: multiplication by `b` is multiplication by
any chosen lift of `b`, here the section `E.σ`. The scalar law is independent of that choice
because `E.ker` annihilates itself. The displayed equality in the main result says that the
resulting linear map on `J / J²` is precisely the factorization of the restriction of the lifted
algebra map to `J`.

Mathlib's `Algebra.Extension.cotangentComplex` is defined for every surjective map of
`A`-algebras, slightly more generally than the polynomial presentations the source uses, and it
writes the scalar extension in the canonically equivalent order `B ⊗[P] Ω[P⁄A]`.

## References

* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
-/

@[expose] public section

open MvPolynomial

universe u v w

namespace Algebra.Extension

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The natural module structure on the kernel of a square-zero extension. A scalar in the
quotient acts by multiplication by any lift of it. -/
@[instance_reducible]
noncomputable def squareZeroKerModule (E : Algebra.Extension A B)
    (hE : E.ker ^ 2 = ⊥) : Module B E.ker := by
  have annihilates (x y : E.ker) : x.1 * y.1 = 0 := by
    have hxy : x.1 * y.1 ∈ E.ker ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul x.2 y.2
    rw [hE, Ideal.mem_bot] at hxy
    exact hxy
  refine
    { smul := fun b x ↦ E.σ b • x
      one_smul := fun x ↦ Subtype.ext <| by
        change E.σ 1 * x.1 = x.1
        have hz : (E.σ 1 - 1 : E.Ring) ∈ E.ker := by simp
        exact sub_eq_zero.mp (by simpa [sub_mul] using (annihilates ⟨E.σ 1 - 1, hz⟩ x))
      mul_smul := fun b c x ↦ Subtype.ext <| by
        change E.σ (b * c) * x.1 = E.σ b * (E.σ c * x.1)
        have hz : (E.σ (b * c) - E.σ b * E.σ c : E.Ring) ∈ E.ker := by simp
        exact sub_eq_zero.mp (by simpa [sub_mul, mul_assoc] using
          (annihilates ⟨E.σ (b * c) - E.σ b * E.σ c, hz⟩ x))
      smul_add := fun b x y ↦ Subtype.ext (mul_add (E.σ b) x.1 y.1)
      smul_zero := fun b ↦ Subtype.ext (mul_zero (E.σ b))
      add_smul := fun b c x ↦ Subtype.ext <| by
        change E.σ (b + c) * x.1 = E.σ b * x.1 + E.σ c * x.1
        have hz : (E.σ (b + c) - (E.σ b + E.σ c) : E.Ring) ∈ E.ker := by simp
        exact sub_eq_zero.mp (by simpa [sub_mul, add_mul] using
          (annihilates ⟨E.σ (b + c) - (E.σ b + E.σ c), hz⟩ x))
      zero_smul := fun x ↦ Subtype.ext <| by
        change E.σ 0 * x.1 = 0
        have hz : E.σ 0 ∈ E.ker := by simp
        exact annihilates ⟨E.σ 0, hz⟩ x }

end Algebra.Extension

namespace Algebra.Generators

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A polynomial presentation of an algebra lifts through every square-zero extension, and the
restriction of the lift to the relation ideal factors `B`-linearly through `J / J²`. -/
@[stacks 0GPU "lift_and_factor"]
theorem exists_lift_and_cotangentMap_to_squareZeroKernel
    {ι : Type w} (P : Algebra.Generators A B ι) (E : Algebra.Extension A B)
    (hE : E.ker ^ 2 = ⊥) :
    letI := Algebra.Extension.squareZeroKerModule E hE
    ∃ (f : P.toExtension.Hom E) (l : P.toExtension.Cotangent →ₗ[B] E.ker),
      ∀ x : P.toExtension.ker,
        (l (Algebra.Extension.Cotangent.mk x) : E.Ring) = f.toRingHom x := by
  let := Algebra.Extension.squareZeroKerModule E hE
  let g : P.Ring →ₐ[A] E.Ring := MvPolynomial.aeval (E.σ ∘ P.val)
  have hg : (IsScalarTower.toAlgHom A E.Ring B).comp g =
      (IsScalarTower.toAlgHom A B B).comp (IsScalarTower.toAlgHom A P.Ring B) := by
    ext i
    simp [g, P.algebraMap_apply]
  let f : P.toExtension.Hom E := Algebra.Extension.Hom.ofAlgHom g hg
  have annihilates (x y : E.ker) : x.1 * y.1 = 0 := by
    simpa only [← pow_two, hE, Ideal.mem_bot] using Ideal.mul_mem_mul x.2 y.2
  have mem (x : P.toExtension.ker) : f.toRingHom x.1 ∈ E.ker := by
    change algebraMap E.Ring B (f.toRingHom x.1) = 0
    rw [f.algebraMap_toRingHom]
    exact x.2
  let k : P.toExtension.ker →+ E.ker :=
    { toFun := fun x ↦ ⟨f.toRingHom x.1, mem x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add f.toRingHom x.1 y.1)
      map_zero' := Subtype.ext (map_zero f.toRingHom) }
  have hk (x y : P.toExtension.ker) : k (x * y) = 0 :=
    Subtype.ext <| (map_mul f.toRingHom x.1 y.1).trans
      (annihilates ⟨f.toRingHom x.1, mem x⟩ ⟨f.toRingHom y.1, mem y⟩)
  let q : P.toExtension.ker.Cotangent →+ E.ker :=
    QuotientAddGroup.lift _ k fun x hx ↦ by
      simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
      exact Submodule.smul_induction_on hx (fun r hr y _ ↦ hk ⟨r, hr⟩ y)
        fun x y hx hy ↦ by simp only [map_add, hx, hy, add_zero]
  let l : P.toExtension.Cotangent →ₗ[B] E.ker :=
    { toFun := fun x ↦ q x.val
      map_add' := fun x y ↦ q.map_add x.val y.val
      map_smul' := fun b x ↦ by
        obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
        apply Subtype.ext
        change f.toRingHom (P.toExtension.σ b * y.1) = E.σ b * f.toRingHom y.1
        rw [map_mul]
        have hz : (f.toRingHom (P.toExtension.σ b) - E.σ b : E.Ring) ∈ E.ker := by
          change algebraMap E.Ring B (f.toRingHom (P.toExtension.σ b) - E.σ b) = 0
          rw [map_sub, f.algebraMap_toRingHom, sub_eq_zero, E.algebraMap_σ]
          exact P.toExtension.algebraMap_σ b
        exact sub_eq_zero.mp (by simpa [sub_mul] using
          (annihilates ⟨f.toRingHom (P.toExtension.σ b) - E.σ b, hz⟩
            ⟨f.toRingHom y.1, mem y⟩)) }
  exact ⟨f, l, fun _ ↦ rfl⟩

end Algebra.Generators

end
