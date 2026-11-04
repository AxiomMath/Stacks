module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.RingTheory.GradedAlgebra.NoetherianModel

/-!
# A graded surjection identifies the quotient by its kernel with its target

Let `f : 𝒜 →+*ᵍ ℬ` be a homomorphism of graded algebras which is surjective and carries each
graded piece of the source *onto* the graded piece of the target of the same degree, and let `J`
be its kernel. The induced map `A ⧸ J → B` is then an isomorphism of graded rings, where `A ⧸ J`
carries the grading by the images of the graded pieces.

## Main definitions

* `Stacks.GradedModel.quotientKerLift`: the induced map on the quotient by the kernel.
* `Stacks.GradedModel.quotientKerGradedHom` and `Stacks.GradedModel.quotientKerGradedInv`: that
  map and its inverse, as homomorphisms of graded rings.

## Main results

* `Stacks.GradedModel.bijective_quotientKerLift`: the induced map is bijective.
* `Stacks.GradedModel.quotientKerGradedInv_comp_hom` and
  `Stacks.GradedModel.quotientKerGradedHom_comp_inv`: the two are mutually inverse.
* `Stacks.GradedModel.quotientKerGradedHom_algebraMap`: the identification is a homomorphism of
  algebras over the base ring.

## Implementation notes

The two directions are produced as homomorphisms of graded rings rather than as a bundled
isomorphism, because Mathlib has no bundled isomorphism of graded rings and the consumers —
`AlgebraicGeometry.Proj.isIso_map` and
`Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse` — ask for a pair of
mutually inverse homomorphisms.
-/

@[expose] public noncomputable section

namespace Stacks.GradedModel

open Graded

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}
  (f : 𝒜 →+*ᵍ ℬ) {J : Ideal A} (hJ : RingHom.ker f.toRingHom = J)

/-- The map induced on the quotient by the kernel. -/
def quotientKerLift : (A ⧸ J) →+* B :=
  Ideal.Quotient.lift J f.toRingHom fun a ha => by
    rw [← RingHom.mem_ker, hJ]
    exact ha

/-- The induced map sends the class of `a` to `f a`. -/
@[simp]
theorem quotientKerLift_mk (a : A) :
    quotientKerLift f hJ (Ideal.Quotient.mk J a) = f a := rfl

/-- The map induced on the quotient by the kernel is bijective when `f` is surjective. -/
theorem bijective_quotientKerLift (hsurj : Function.Surjective f) :
    Function.Bijective (quotientKerLift f hJ) := by
  refine ⟨?_, fun y => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotientKerLift_mk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJ ▸ RingHom.mem_ker.mpr hx)
  · obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk J a, rfl⟩

/-- The quotient by the kernel, identified with the target. -/
def quotientKerEquiv (hsurj : Function.Surjective f) : (A ⧸ J) ≃+* B :=
  RingEquiv.ofBijective _ (bijective_quotientKerLift f hJ hsurj)

/-- The identification sends the class of `a` to `f a`. -/
@[simp]
theorem quotientKerEquiv_mk (hsurj : Function.Surjective f) (a : A) :
    quotientKerEquiv f hJ hsurj (Ideal.Quotient.mk J a) = f a := rfl

/-- The identification of the quotient by the kernel with the target, as a homomorphism of
graded rings. -/
def quotientKerGradedHom (_hsurj : Function.Surjective f) :
    quotientGrading 𝒜 J →+*ᵍ ℬ where
  __ := quotientKerLift f hJ
  map_mem := by
    rintro i x ⟨a, ha, rfl⟩
    exact map_mem f ha

/-- The graded identification sends the class of `a` to `f a`. -/
@[simp]
theorem quotientKerGradedHom_mk (hsurj : Function.Surjective f) (a : A) :
    quotientKerGradedHom f hJ hsurj (Ideal.Quotient.mk J a) = f a := rfl

/-- The inverse identification, as a homomorphism of graded rings. This is where the hypothesis
that `f` carries each graded piece onto the graded piece of the same degree is used: a
homogeneous element of the target is the image of a homogeneous element of the same degree, whose
class is therefore homogeneous of that degree. -/
def quotientKerGradedInv (hsurj : Function.Surjective f)
    (honto : ∀ i, ∀ y ∈ ℬ i, ∃ a ∈ 𝒜 i, f a = y) :
    ℬ →+*ᵍ quotientGrading 𝒜 J where
  __ := (quotientKerEquiv f hJ hsurj).symm.toRingHom
  map_mem := by
    intro i y hy
    obtain ⟨a, ha, rfl⟩ := honto i y hy
    change (quotientKerEquiv f hJ hsurj).symm (f a) ∈ _
    rw [← quotientKerEquiv_mk f hJ hsurj a, RingEquiv.symm_apply_apply]
    exact mk_mem_quotientGrading ha

/-- `quotientKerGradedInv` is a left inverse of `quotientKerGradedHom`. -/
theorem quotientKerGradedInv_comp_hom (hsurj : Function.Surjective f)
    (honto : ∀ i, ∀ y ∈ ℬ i, ∃ a ∈ 𝒜 i, f a = y) :
    (quotientKerGradedInv f hJ hsurj honto).comp (quotientKerGradedHom f hJ hsurj) =
      GradedRingHom.id (quotientGrading 𝒜 J) :=
  GradedRingHom.ext fun x => (quotientKerEquiv f hJ hsurj).symm_apply_apply x

/-- `quotientKerGradedInv` is a right inverse of `quotientKerGradedHom`. -/
theorem quotientKerGradedHom_comp_inv (hsurj : Function.Surjective f)
    (honto : ∀ i, ∀ y ∈ ℬ i, ∃ a ∈ 𝒜 i, f a = y) :
    (quotientKerGradedHom f hJ hsurj).comp (quotientKerGradedInv f hJ hsurj honto) =
      GradedRingHom.id ℬ :=
  GradedRingHom.ext fun y => (quotientKerEquiv f hJ hsurj).apply_symm_apply y

/-- The identification respects the base ring, provided `f` does. -/
theorem quotientKerGradedHom_algebraMap (hsurj : Function.Surjective f)
    (hf0 : ∀ r : R, f (algebraMap R A r) = algebraMap R B r) (r : R) :
    quotientKerGradedHom f hJ hsurj (algebraMap R (A ⧸ J) r) = algebraMap R B r := by
  rw [show algebraMap R (A ⧸ J) r = Ideal.Quotient.mk J (algebraMap R A r) from rfl,
    quotientKerGradedHom_mk, hf0]

end Stacks.GradedModel

end
