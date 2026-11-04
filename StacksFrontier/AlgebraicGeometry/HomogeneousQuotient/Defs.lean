module

public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The internal grading on a quotient by a homogeneous ideal

Let `A` be a commutative `R`-algebra carrying an internal grading `𝒜 : ι → Submodule R A`, and
let `I` be a homogeneous ideal of `A`. This file puts an internal grading on the quotient ring
`A ⧸ I`, whose degree-`i` piece is the image of `𝒜 i`, and shows that it makes `A ⧸ I` a graded
ring.

The decomposition is the module-level one, `Submodule.quotientGrading.decomposition`, applied to
the `R`-submodule underlying `I`; the multiplicative axioms `SetLike.GradedOne` and
`SetLike.GradedMul` hold because `Ideal.Quotient.mk` is a ring homomorphism and `𝒜` is
multiplicatively graded.

## Main definitions

* `Stacks.RingTheory.HomogeneousQuotient.quotientGrading`: the family of `R`-submodules of
  `A ⧸ I.toIdeal` whose degree-`i` member is the image of `𝒜 i`.

## Main results

* `Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff`: an element of the quotient is
  of degree `i` exactly when it is the class of an element of `𝒜 i`.
* `Stacks.RingTheory.HomogeneousQuotient.quotientGrading.decomposition`: the quotient is the
  direct sum of its graded pieces.
* `Stacks.RingTheory.HomogeneousQuotient.quotientGrading.gradedRing`: the resulting
  `GradedRing` instance, which is simultaneously a `GradedAlgebra` instance since
  `GradedAlgebra` abbreviates `GradedRing` for a family of submodules.

## Implementation notes

The grading is a family of `Submodule R _` rather than of `AddSubgroup _`, so that the
module-level decomposition `Submodule.quotientGrading.decomposition` applies. The quotients
`A ⧸ I.toIdeal` and `A ⧸ I.toIdeal.restrictScalars R` are the same type.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
-/

@[expose] public section

open DirectSum

universe u v w

namespace Stacks.RingTheory.HomogeneousQuotient

variable {ι : Type v} {R : Type u} {A : Type w} [DecidableEq ι] [AddMonoid ι]
  [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (I : HomogeneousIdeal 𝒜)

/-- A homogeneous ideal is homogeneous as an `R`-submodule: every graded component of a member
is again a member. -/
theorem restrictScalars_isHomogeneous (i : ι) (a : A)
    (ha : a ∈ I.toIdeal.restrictScalars R) :
    (DirectSum.decompose 𝒜 a i : A) ∈ I.toIdeal.restrictScalars R :=
  I.is_homogeneous' i ha

/-- The grading induced on `A ⧸ I` by a grading `𝒜` of `A` and a homogeneous ideal `I`: the
degree-`i` piece is the image of `𝒜 i` under the quotient map. -/
def quotientGrading (i : ι) : Submodule R (A ⧸ I.toIdeal) :=
  Submodule.quotientGrading 𝒜 (I.toIdeal.restrictScalars R) i

/-- An element of `A ⧸ I` has degree `i` exactly when it is the class of an element of `𝒜 i`. -/
theorem mem_quotientGrading_iff {i : ι} {x : A ⧸ I.toIdeal} :
    x ∈ quotientGrading 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I.toIdeal a = x := by
  simp [quotientGrading, Submodule.quotientGrading]
  rfl

/-- The class of a degree-`i` element of `A` has degree `i` in `A ⧸ I`. -/
theorem quotientGrading_mk_mem {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I.toIdeal a ∈ quotientGrading 𝒜 I i :=
  (mem_quotientGrading_iff 𝒜 I).2 ⟨a, ha, rfl⟩

/-- The quotient of a graded ring by a homogeneous ideal is the direct sum of the images of the
graded pieces. -/
noncomputable instance quotientGrading.decomposition :
    DirectSum.Decomposition (quotientGrading 𝒜 I) :=
  Submodule.quotientGrading.decomposition 𝒜 (I.toIdeal.restrictScalars R)
    (restrictScalars_isHomogeneous 𝒜 I)

/-- The identity of `A ⧸ I` has degree zero, because it is the class of the identity of `A`. -/
instance quotientGrading.gradedOne : SetLike.GradedOne (quotientGrading 𝒜 I) where
  one_mem := by simpa using quotientGrading_mk_mem 𝒜 I (SetLike.one_mem_graded 𝒜)

/-- Degrees add under multiplication in `A ⧸ I`, because `Ideal.Quotient.mk` is multiplicative
and degrees add in `A`. -/
instance quotientGrading.gradedMul : SetLike.GradedMul (quotientGrading 𝒜 I) where
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := (mem_quotientGrading_iff 𝒜 I).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_quotientGrading_iff 𝒜 I).1 hy
    rw [← map_mul]
    exact quotientGrading_mk_mem 𝒜 I (SetLike.mul_mem_graded ha hb)

/-- The quotient of a graded ring by a homogeneous ideal is a graded ring. Since
`GradedAlgebra` abbreviates `GradedRing` for a family of submodules, this is also the
`GradedAlgebra (quotientGrading 𝒜 I)` instance. -/
noncomputable instance quotientGrading.gradedRing : GradedRing (quotientGrading 𝒜 I) where

end Stacks.RingTheory.HomogeneousQuotient

end
