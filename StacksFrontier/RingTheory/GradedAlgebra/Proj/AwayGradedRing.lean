module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections
public import StacksFrontier.AlgebraicGeometry.TwistAwayBridge.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.Defs
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Multiplication

/-!
# The localization at a homogeneous element, as a `ℤ`-graded ring

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a nonnegatively graded ring and let `f ∈ 𝒜 d` be homogeneous. The
localization `A[1/f]` is graded by `ℤ`, the degree-`t` part being the single fractions `a / f ᵐ`
with `a` homogeneous of degree `m * d + t`; negative degrees occur because the denominator may
outweigh the numerator.

`Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t` is that degree-`t` part, presented as an
`A₍f₎`-submodule of `A[1/f]`. This file equips the family with the multiplicative structure and
the direct-sum decomposition that together make it a grading of the ring `A[1/f]`, and records
that `f` becomes a homogeneous unit of degree `d` there.

## Main results

* `Stacks.ProjStandardOpenBaseChange.mem_twistAway_iff_exists`: an element of `A[1/f]` has
  degree `t` exactly when it is a *single* fraction `a / f ᵐ` with `a` homogeneous of degree
  `m * d + t`.
* `Stacks.ProjStandardOpenBaseChange.gradedMonoidTwistAway`: the degree parts multiply,
  `(A[1/f])_s · (A[1/f])_t ⊆ (A[1/f])_{s+t}`, and `1` has degree `0`.
* `Stacks.ProjStandardOpenBaseChange.gradedRingTwistAway`: `A[1/f]` is a `ℤ`-graded ring.
* `Stacks.ProjStandardOpenBaseChange.hasHomogeneousUnitOfPosDegree_twistAway`: for `0 < d` the
  image of `f` is a unit of `A[1/f]` of degree `d`.

## Implementation notes

The decomposition is not proved from scratch. `Stacks.ProjectiveCohomology.awayGrading` is the
same grading written on the *module* localization `LocalizedModule.Away f A`, and the
independence of its degree parts is already available there; the comparison
`Stacks.AlgebraicGeometry.TwistAwayBridge.localizedAwayEquiv` between the module localization and
the ring localization carries that independence across, degree by degree. The spanning half is
`Stacks.GradedLaurent.iSup_twistAway_eq_top`.

The grading hypothesis `f ∈ 𝒜 d` cannot be found by instance search, so
`gradedRingTwistAway` is not a global instance; downstream statements introduce it with `letI`.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

namespace Stacks.ProjStandardOpenBaseChange

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.TwistAwayBridge
open Stacks.ProjectiveCohomology

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {d : ℕ}

/-- **The degree-`t` part of `A[1/f]` is the set of single fractions.** An element of the
localization is homogeneous of degree `t` exactly when it can be written as one fraction
`a / f ᵐ` whose numerator is homogeneous of degree `m * d + t`; no sums are needed. -/
public theorem mem_twistAway_iff_exists (hf : f ∈ 𝒜 d) (t : ℤ) (z : Localization.Away f) :
    z ∈ twistAway 𝒜 f d t ↔
      ∃ (m : ℕ) (a : A), a ∈ integerGrading (S := A) 𝒜 ((m * d : ℕ) + t) ∧
        z = Localization.mk a
          (⟨f ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers f) m⟩ : Submonoid.powers f) := by
  constructor
  · intro hz
    have hz' : ((localizedAwayEquiv f) ((localizedAwayEquiv f).symm z)) ∈ twistAway 𝒜 f d t := by
      simpa using hz
    obtain ⟨m, a, ha, hw⟩ :=
      (mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf t _).mp
        ((mem_twistAway_iff 𝒜 hf t _).mp hz')
    refine ⟨m, a, ha, ?_⟩
    rw [← LinearEquiv.apply_symm_apply (localizedAwayEquiv f) z, hw, localizedAwayEquiv_mk]
  · rintro ⟨m, a, ha, rfl⟩
    have h := (mem_twistAway_iff 𝒜 hf t
      (LocalizedModule.mk a
        (⟨f ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers f) m⟩ : Submonoid.powers f))).mpr
      ((mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf t _).mpr
        (mk_mem_awayGrading 𝒜 hf ha))
    rwa [localizedAwayEquiv_mk] at h

/-- The image of a homogeneous element of degree `t` is homogeneous of degree `t` in `A[1/f]`. -/
private theorem algebraMap_mem_twistAway (hf : f ∈ 𝒜 d) {t : ℤ} {a : A}
    (ha : a ∈ integerGrading (S := A) 𝒜 t) : algebraMap A (Localization.Away f) a ∈
      twistAway 𝒜 f d t := by
  refine (mem_twistAway_iff_exists 𝒜 hf t _).mpr ⟨0, a, by simpa using ha, ?_⟩
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1
  exact Subtype.ext (pow_zero f).symm

/-- `1` is homogeneous of degree `0` in `A[1/f]`. -/
public theorem one_mem_twistAway (hf : f ∈ 𝒜 d) :
    (1 : Localization.Away f) ∈ twistAway 𝒜 f d 0 := by
  have h1 : (1 : A) ∈ integerGrading (S := A) 𝒜 ((0 : ℕ) : ℤ) := by
    rw [integerGrading_natCast]
    exact (mem_homogeneousSubmodule (S := A) 𝒜 0 1).mpr SetLike.GradedOne.one_mem
  simpa using algebraMap_mem_twistAway 𝒜 hf h1

/-- **The degree parts of `A[1/f]` multiply.** A fraction of degree `s` times a fraction of
degree `t` is a fraction of degree `s + t`. -/
public theorem mul_mem_twistAway (hf : f ∈ 𝒜 d) {s t : ℤ} {x y : Localization.Away f}
    (hx : x ∈ twistAway 𝒜 f d s) (hy : y ∈ twistAway 𝒜 f d t) :
    x * y ∈ twistAway 𝒜 f d (s + t) := by
  obtain ⟨m, a, ha, rfl⟩ := (mem_twistAway_iff_exists 𝒜 hf s x).mp hx
  obtain ⟨n, b, hb, rfl⟩ := (mem_twistAway_iff_exists 𝒜 hf t y).mp hy
  refine (mem_twistAway_iff_exists 𝒜 hf (s + t) _).mpr ⟨m + n, a * b, ?_, ?_⟩
  · rw [show (((m + n) * d : ℕ) : ℤ) + (s + t) = ((m * d : ℕ) : ℤ) + s + (((n * d : ℕ) : ℤ) + t) by
      push_cast; ring]
    exact Stacks.ProjTwistMultiplication.mul_mem_integerGrading 𝒜 ha hb
  · rw [Localization.mk_mul]
    congr 1
    exact Subtype.ext (by simpa using (pow_add f m n).symm)

/-- **The degree parts of `A[1/f]` form a graded monoid.** -/
@[instance_reducible]
public def gradedMonoidTwistAway (hf : f ∈ 𝒜 d) :
    SetLike.GradedMonoid (twistAway 𝒜 f d) where
  one_mem := one_mem_twistAway 𝒜 hf
  mul_mem _ _ _ _ hx hy := mul_mem_twistAway 𝒜 hf hx hy

/-- **The degree parts of `A[1/f]` are independent.** Carried across from the same statement
for the module localization, degree by degree, along the comparison with the ring
localization. -/
public theorem iSupIndep_twistAway (hf : f ∈ 𝒜 d) :
    iSupIndep (twistAway 𝒜 f d) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hv0 e he
  have hmem : ∀ i ∈ s, (localizedAwayEquiv f).symm (v i) ∈ awayGrading 𝒜 hf i := by
    intro i hi
    exact (mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf i _).mp
      ((mem_twistAway_iff 𝒜 hf i _).mp (by simpa using hv i hi))
  have hsum : ∑ i ∈ s, (localizedAwayEquiv f).symm (v i) = 0 := by
    rw [← map_sum, hv0, map_zero]
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (fun i : ℤ => awayGrading 𝒜 hf i)).mp
    (iSupIndep_awayGrading 𝒜 hf) s (fun i => (localizedAwayEquiv f).symm (v i)) hmem hsum e he
  exact (localizedAwayEquiv f).symm.map_eq_zero_iff.mp hzero

/-- **The degree parts of `A[1/f]` decompose it as an internal direct sum.** -/
public theorem isInternal_twistAway (hf : f ∈ 𝒜 d) :
    DirectSum.IsInternal (twistAway 𝒜 f d) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_twistAway 𝒜 hf) (Stacks.GradedLaurent.iSup_twistAway_eq_top 𝒜 d)

/-- **The localization of a nonnegatively graded ring at a homogeneous element is a `ℤ`-graded
ring.** The degree-`t` part is the set of fractions `a / f ᵐ` with `a` homogeneous of degree
`m * d + t`. -/
@[instance_reducible,
  ega "II 2.2.1" "more general",
  ega "II 8.2.1" "special case",
  ega "II 8.2.7" "more general"]
public def gradedRingTwistAway (hf : f ∈ 𝒜 d) : GradedRing (twistAway 𝒜 f d) :=
  { gradedMonoidTwistAway 𝒜 hf, (isInternal_twistAway 𝒜 hf).chooseDecomposition with }

/-- The image of `f` in `A[1/f]` is a unit of degree `d`. -/
public theorem coe_awayUnit_mem_twistAway (hf : f ∈ 𝒜 d) :
    (Stacks.GradedLaurent.awayUnit f : Localization.Away f) ∈ twistAway 𝒜 f d (d : ℤ) := by
  rw [Stacks.GradedLaurent.awayUnit, IsUnit.unit_spec]
  exact algebraMap_mem_twistAway 𝒜 hf (by simpa using hf)

/-- **`A[1/f]` has a homogeneous unit of positive degree** when `f` is homogeneous of positive
degree: the image of `f` itself. -/
public theorem hasHomogeneousUnitOfPosDegree_twistAway [GradedRing (twistAway 𝒜 f d)]
    (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    HasHomogeneousUnitOfPosDegree (twistAway 𝒜 f d) :=
  ⟨(d : ℤ), by exact_mod_cast hd, (Stacks.GradedLaurent.awayUnit f : Localization.Away f),
    coe_awayUnit_mem_twistAway 𝒜 hf, (Stacks.GradedLaurent.awayUnit f).isUnit⟩

end Stacks.ProjStandardOpenBaseChange

end
