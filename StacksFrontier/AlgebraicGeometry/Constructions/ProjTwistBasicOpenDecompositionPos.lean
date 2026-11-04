module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistBasicOpenDecomposition

/-!
# Every section of a twist over a standard open is a fraction with positive exponents

Over `D₊(g)`, `g` homogeneous of positive degree `e`, every section of `𝒪(n)` is `x / g ^ j` with
`j ≥ 1` and `x` homogeneous of positive degree `N = j e + n`: multiply numerator and denominator of
any representation by a further power of `g`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistBasicOpenDecomposition.exists_pow_mul_eq_degreeSection_pos`.

## References

* [Stacks Project, Tag 01MM](https://stacks.math.columbia.edu/tag/01MM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading integerGrading_natCast
  mem_homogeneousSubmodule twistingSheaf)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_mul coe_sectionsTwistEquivGradedPiece_degreeSection)
open Stacks.GradedLocalization (gradedPiece mem_gradedPiece_iff)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistBasicOpenDecomposition

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {g : A} {e : ℕ}

/-- An element of the degree-`n` piece of `A_g` is `x / g ^ j` with `j ≥ 1` and `x` of positive
degree `n + j e`. -/
theorem exists_rep_pos (hg : g ∈ 𝒜 e) (he : 0 < e) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) g n) :
    ∃ (j N : ℕ) (x : 𝒜 N), 0 < j ∧ 0 < N ∧ n + ((j * e : ℕ) : ℤ) = (N : ℤ) ∧
      (y : LocalizedModule.Away g A)
        = LocalizedModule.mk (x : A) (⟨g ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers g) := by
  obtain ⟨m, x, hx, hy⟩ := (mem_gradedPiece_iff 𝒜 (integerGrading (S := A) 𝒜) hg n y.1).1 y.2
  set t : ℕ := (-n).toNat + 1 with ht_def
  set j : ℕ := m + t
  have hj : 0 < n + ((j * e : ℕ) : ℤ) := by
    have ht : -n + 1 ≤ (t : ℤ) := by omega
    have h2 : (t : ℤ) ≤ (t : ℤ) * e := le_mul_of_one_le_right (by omega) (by exact_mod_cast he)
    have h3 : (0 : ℤ) ≤ (m : ℤ) * e := by positivity
    push_cast [j]
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n + ((j * e : ℕ) : ℤ) = (N : ℤ) :=
    ⟨_, (Int.toNat_of_nonneg hj.le).symm⟩
  have hgp : g ^ t ∈ 𝒜 (t • e) := SetLike.pow_mem_graded _ hg
  have hmem : x * g ^ t ∈ integerGrading (S := A) 𝒜 (N : ℤ) := by
    have h1 : g ^ t • x ∈ integerGrading (S := A) 𝒜
        (((t • e : ℕ) : ℤ) + (n + m • (e : ℤ))) := SetLike.GradedSMul.smul_mem hgp hx
    have hdeg : ((t • e : ℕ) : ℤ) + (n + m • (e : ℤ)) = (N : ℤ) := by
      rw [← hN, smul_eq_mul]
      push_cast [j]
      ring
    rw [hdeg] at h1
    rwa [smul_eq_mul, mul_comm] at h1
  rw [integerGrading_natCast, mem_homogeneousSubmodule] at hmem
  refine ⟨j, N, ⟨_, hmem⟩, by omega, by omega, hN, ?_⟩
  rw [hy]
  refine (LocalizedModule.mk_eq).2 ⟨1, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul, j, pow_add]
  ring

/-- **Every section of `𝒪(n)` over `D₊(g)` is a fraction `x / g ^ j` with `j ≥ 1` and `x` of
positive degree `N = j e + n`.** -/
theorem exists_pow_mul_eq_degreeSection_pos (hg : g ∈ 𝒜 e) (he : 0 < e) (n : ℤ)
    (s : (twistingSheaf 𝒜 n).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 g))) :
    ∃ (j N : ℕ) (x : 𝒜 N) (_ : 0 < j) (_ : 0 < N) (_ : ((j * e : ℕ) : ℤ) + n = (N : ℤ)),
      HEq (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜).mul
            ((j * e : ℕ) : ℤ) n).app (op (ProjectiveSpectrum.basicOpen 𝒜 g))
          ((twistingSheaf 𝒜 ((j * e : ℕ) : ℤ)).val.map
            (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ⊤)).op
            (degreeSection 𝒜 (j * e) ⟨g ^ j, by
              simpa [smul_eq_mul] using SetLike.pow_mem_graded j hg⟩)) s)
        ((twistingSheaf 𝒜 (N : ℤ)).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ⊤)).op (degreeSection 𝒜 N x)) := by
  obtain ⟨j, N, x, hj, hNp, hN, hy⟩ :=
    exists_rep_pos 𝒜 hg he n (sectionsTwistEquivGradedPiece 𝒜 hg he n s)
  refine ⟨j, N, x, hj, hNp, (add_comm _ _).trans hN,
    heq_of_coe_eq 𝒜 hg he ((add_comm _ _).trans hN) _ _ ?_⟩
  refine (coe_sectionsTwistEquivGradedPiece_mul 𝒜 hg he ((j * e : ℕ) : ℤ) n _ _).trans ?_
  rw [coe_sectionsTwistEquivGradedPiece_degreeSection,
    coe_sectionsTwistEquivGradedPiece_degreeSection, hy]
  refine (LocalizedModule.mk_mul_mk (R := A) (S := Submonoid.powers g) (A := A)).trans
    ((LocalizedModule.mk_eq).2 ⟨1, ?_⟩)
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul]

end Stacks.AlgebraicGeometry.ProjTwistBasicOpenDecomposition

end
