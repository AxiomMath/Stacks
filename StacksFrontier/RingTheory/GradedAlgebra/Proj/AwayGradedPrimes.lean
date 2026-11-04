module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.AwayGradedRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `ℤ`-graded primes of `A[1/f]` and the affine chart `Spec A₍f₎`

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a nonnegatively graded ring and `f ∈ 𝒜 d` homogeneous of positive
degree. `A[1/f]` is `ℤ`-graded, and `f` is a homogeneous unit of positive degree there, so the
comparison map `q ↦ q ∩ (A[1/f])₀` from the space of `ℤ`-graded primes of `A[1/f]` to the
spectrum of the degree-zero part is a homeomorphism.

The degree-zero part of `A[1/f]` is the image of the degree-zero localization `A₍f₎`, and this
file identifies the two as rings, so that the comparison map becomes a homeomorphism onto
`Spec A₍f₎` — the right-hand horizontal arrow of the diagram of
[Stacks, Tag 01M4] part (1)(f).

## Main results

* `Stacks.ProjStandardOpenBaseChange.gradeZeroSubringEquivAway`: the degree-zero subring of
  `A[1/f]` is `A₍f₎`.
* `Stacks.ProjStandardOpenBaseChange.gradedPrimesAwayToSpec`: the comparison map from the
  `ℤ`-graded primes of `A[1/f]` to `Spec A₍f₎`.
* `Stacks.ProjStandardOpenBaseChange.isHomeomorph_gradedPrimesAwayToSpec`: it is a
  homeomorphism.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

namespace Stacks.ProjStandardOpenBaseChange

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {d : ℕ}

/-- The image of the degree-zero localization `A₍f₎` in `A[1/f]` lies in degree `0`. -/
public theorem algebraMap_mem_twistAway_zero (hf : f ∈ 𝒜 d) (c : Away 𝒜 f) :
    algebraMap (Away 𝒜 f) (Localization.Away f) c ∈ twistAway 𝒜 f d 0 := by
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf c
  rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  refine (mem_twistAway_iff_exists 𝒜 hf 0 _).mpr ⟨m, a, ?_, rfl⟩
  rw [add_zero, integerGrading_natCast]
  exact (mem_homogeneousSubmodule (S := A) 𝒜 _ a).mpr (by simpa [smul_eq_mul] using ha)

/-- Every degree-zero element of `A[1/f]` comes from the degree-zero localization `A₍f₎`. -/
public theorem exists_away_of_mem_twistAway_zero (hf : f ∈ 𝒜 d) {z : Localization.Away f}
    (hz : z ∈ twistAway 𝒜 f d 0) :
    ∃ c : Away 𝒜 f, algebraMap (Away 𝒜 f) (Localization.Away f) c = z := by
  obtain ⟨m, a, ha, rfl⟩ := (mem_twistAway_iff_exists 𝒜 hf 0 z).mp hz
  rw [add_zero, integerGrading_natCast] at ha
  refine ⟨Away.mk 𝒜 hf m a (by
    simpa [smul_eq_mul] using (mem_homogeneousSubmodule (S := A) 𝒜 _ a).mp ha), ?_⟩
  rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk]

section GradedRing

variable [GradedRing (twistAway 𝒜 f d)]

/-- **The degree-zero subring of `A[1/f]` is the degree-zero localization `A₍f₎`.** -/
@[ega "II 2.2.7" "special case"]
public def gradeZeroSubringEquivAway (hf : f ∈ 𝒜 d) :
    Away 𝒜 f ≃+* gradeZeroSubring (twistAway 𝒜 f d) :=
  RingEquiv.ofBijective
    ((algebraMap (Away 𝒜 f) (Localization.Away f)).codRestrict
      (gradeZeroSubring (twistAway 𝒜 f d)) fun c => algebraMap_mem_twistAway_zero 𝒜 hf c)
    ⟨fun c c' h => by
      have h' : algebraMap (Away 𝒜 f) (Localization.Away f) c =
          algebraMap (Away 𝒜 f) (Localization.Away f) c' := congrArg Subtype.val h
      rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.algebraMap_apply] at h'
      exact HomogeneousLocalization.val_injective _ h',
      fun z => by
        obtain ⟨c, hc⟩ := exists_away_of_mem_twistAway_zero 𝒜 hf z.2
        exact ⟨c, Subtype.ext hc⟩⟩

/-- The image of `c : A₍f₎` under `gradeZeroSubringEquivAway`, viewed in `A[1/f]`, is the
underlying element `c.val`. -/
@[simp]
public theorem coe_gradeZeroSubringEquivAway (hf : f ∈ 𝒜 d) (c : Away 𝒜 f) :
    (gradeZeroSubringEquivAway 𝒜 hf c : Localization.Away f) = c.val :=
  HomogeneousLocalization.algebraMap_apply c

/-- **The right-hand horizontal arrow of the diagram of [Stacks, Tag 01M4] part (1)(f).** It
sends a `ℤ`-graded prime `q` of `A[1/f]` to the prime `q ∩ A₍f₎` of the degree-zero
localization. -/
public def gradedPrimesAwayToSpec (hf : f ∈ 𝒜 d) :
    gradedPrimes (twistAway 𝒜 f d) → PrimeSpectrum (Away 𝒜 f) :=
  PrimeSpectrum.comap (gradeZeroSubringEquivAway 𝒜 hf).toRingHom ∘
    gradedPrimesComparison (twistAway 𝒜 f d)

/-- **The space of `ℤ`-graded primes of `A[1/f]` is homeomorphic to `Spec A₍f₎`.** This is the
right-hand horizontal homeomorphism of the diagram of [Stacks, Tag 01M4] part (1)(f): the
contraction `q ↦ q ∩ A₍f₎` is a homeomorphism from the `ℤ`-graded primes of `A[1/f]`, with the
subspace topology from `Spec A[1/f]`, onto the spectrum of the degree-zero localization. -/
public theorem isHomeomorph_gradedPrimesAwayToSpec (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    IsHomeomorph (gradedPrimesAwayToSpec 𝒜 hf) :=
  IsHomeomorph.comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective
      (gradeZeroSubringEquivAway 𝒜 hf).bijective)
    (gradedPrimesComparison_isHomeomorph (twistAway 𝒜 f d)
      (hasHomogeneousUnitOfPosDegree_twistAway 𝒜 hf hd))

end GradedRing

end Stacks.ProjStandardOpenBaseChange

end
