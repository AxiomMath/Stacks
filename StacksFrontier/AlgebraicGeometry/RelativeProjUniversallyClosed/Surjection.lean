module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.DegreeZeroConditions

/-!
# The degree-zero conditions pass along a surjection of graded algebras

Let `ψ : A ⟶ B` be a homomorphism of sheaf-level graded `𝒪_S`-algebras which is surjective on
the graded rings of sections over an affine open `U` (or, more generally, a surjective
homomorphism of graded rings compatible with maps from a base ring). Then `Γ(U, B)` is of finite
type over `Γ(U, B)₀` as soon as `Γ(U, A)` is of finite type over `Γ(U, A)₀`, and
`Γ(S, U) → Γ(U, B)₀` is integral as soon as `Γ(S, U) → Γ(U, A)₀` is: the degree-zero part of `ψ`
is surjective and carries the structure map of `A` to that of `B`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed.finiteType_degreeZero_of_surjective`
  and `…isIntegral_degreeZero_of_surjective`: for a surjective homomorphism of graded rings.
* `Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed.isFiniteTypeOverDegreeZero_of_surjective`
  and `…isIntegralInDegreeZero_of_surjective`: for a homomorphism of sheaf-level graded algebras
  surjective on sections over every affine open.

## References

* [Stacks Project, Tag 07ZZ](https://stacks.math.columbia.edu/tag/07ZZ)
-/

@[expose] public section

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed

section GradedRing

variable {R A B σ τ : Type*} [CommRing R] [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
  [AddSubgroupClass σ A] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜]
  [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

/-- The degree-zero part of a surjective graded ring homomorphism is surjective. -/
theorem gradedZeroRingHom_surjective (hf : Function.Surjective f) :
    Function.Surjective f.gradedZeroRingHom := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hf y
  refine ⟨DirectSum.decompose 𝒜 x 0, Subtype.ext ?_⟩
  change f (DirectSum.decompose 𝒜 x 0 : A) = y
  rw [GradedRingHom.map_directSumDecompose, hx, DirectSum.decompose_of_mem_same _ hy]

/-- Finite type over the degree-zero part passes along a surjective graded ring homomorphism. -/
theorem finiteType_degreeZero_of_surjective (hf : Function.Surjective f)
    (h : Algebra.FiniteType (𝒜 0) A) : Algebra.FiniteType (ℬ 0) B := by
  have hA : (algebraMap (𝒜 0) A).FiniteType := RingHom.finiteType_algebraMap.mpr h
  have hcomp := hA.comp_surjective (f := algebraMap (𝒜 0) A) (g := f.toRingHom) hf
  have he : f.toRingHom.comp (algebraMap (𝒜 0) A) =
      (algebraMap (ℬ 0) B).comp f.gradedZeroRingHom := RingHom.ext fun _ => rfl
  rw [he] at hcomp
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hcomp)

/-- Integrality of a map into the degree-zero part passes along a surjective graded ring
homomorphism compatible with the maps from the base ring. -/
theorem isIntegral_degreeZero_of_surjective (hf : Function.Surjective f) (a : R →+* A)
    (b : R →+* B) (ha : ∀ r, a r ∈ 𝒜 0) (hb : ∀ r, b r ∈ ℬ 0) (hab : ∀ r, f (a r) = b r)
    (h : ((GradedRing.projZeroRingHom' 𝒜).comp a).IsIntegral) :
    ((GradedRing.projZeroRingHom' ℬ).comp b).IsIntegral := by
  have he : f.gradedZeroRingHom.comp ((GradedRing.projZeroRingHom' 𝒜).comp a) =
      (GradedRing.projZeroRingHom' ℬ).comp b := by
    refine RingHom.ext fun r => Subtype.ext ?_
    change f (DirectSum.decompose 𝒜 (a r) 0 : A) = (DirectSum.decompose ℬ (b r) 0 : B)
    rw [DirectSum.decompose_of_mem_same _ (ha r), DirectSum.decompose_of_mem_same _ (hb r)]
    exact hab r
  rw [← he]
  exact RingHom.IsIntegral.trans _ _ h
    (RingHom.isIntegral_of_surjective _ (gradedZeroRingHom_surjective f hf))

end GradedRing

section SheafGradedAlgebra

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- `B` is of finite type over `B₀` if `A` is of finite type over `A₀` and `ψ` is surjective on
sections over every affine open. -/
theorem isFiniteTypeOverDegreeZero_of_surjective
    (hψ : ∀ U : S.Opens, IsAffineOpen U → Function.Surjective (ψ.sectionRingHom U))
    (h : A.IsFiniteTypeOverDegreeZero) : B.IsFiniteTypeOverDegreeZero := fun U hU =>
  finiteType_degreeZero_of_surjective (ψ.sectionHom U) (hψ U hU) (h U hU)

/-- `𝒪_S → B₀` is integral if `𝒪_S → A₀` is integral and `ψ` is surjective on sections over every
affine open. -/
theorem isIntegralInDegreeZero_of_surjective
    (hψ : ∀ U : S.Opens, IsAffineOpen U → Function.Surjective (ψ.sectionRingHom U))
    (h : A.IsIntegralInDegreeZero) : B.IsIntegralInDegreeZero := fun U hU =>
  isIntegral_degreeZero_of_surjective (ψ.sectionHom U) (hψ U hU) (A.strHom U) (B.strHom U)
    (A.strHom_mem U) (B.strHom_mem U) (ProjBundleSurjection.sectionHom_strHom ψ U) (h U hU)

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed

end
