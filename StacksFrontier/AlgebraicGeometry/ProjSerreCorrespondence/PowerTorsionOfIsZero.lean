module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantModules
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionVanishing

/-!
# A graded module with vanishing associated sheaf is power-torsion in the divisible degrees

Let `S = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj 𝒜`, and `M` a `ℤ`-graded `S`-module whose
associated sheaf `M̃` is the zero object. This file proves that a homogeneous element of `M`
whose degree is a multiple of the degree of a homogeneous `f ∈ S` of positive degree is killed by
a power of `f`.

This is the converse of
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_pow_smul_eq_zero_of_gradeEventuallyZero`,
and it is the direction the module docstring of
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/IrrelevantModules.lean` records as owed to
[Stacks, Tag 0B5R]: it is the first half of the paragraph of that tag beginning "Let `K` be a
finite `A`-module such that `K̃ = 0`", whose counting half is
`Stacks.GradedModule.eq_zero_of_mem_span_of_sum_lt`.

The restriction to degrees divisible by `deg f` is not an artefact. `M̃ = 0` says exactly that the
*degree-zero* part of each localization `M_f` vanishes, and multiplication by `f` shifts degrees
by `deg f`, so only the residue class `0 mod deg f` is reached. For `S = k[f]` with `f` of degree
`2` and `M = S(1)`, concentrated in odd degrees, `M̃` is zero on the one-point space `Proj S`
while no power of `f` kills the generator.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.subsingleton_moduleSections_of_isZero`: a
  zero associated sheaf has trivial section group over every open.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_pow_smul_eq_zero_of_isZero_associatedModuleSheaf`: the power-torsion statement.

## Implementation notes

The section group over the standard open `D₊(f)` is reached through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroToSection_injective` rather than through the
packaged `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`:
injectivity is all that is used, and it avoids carrying the module structure over
`HomogeneousLocalization.Away 𝒜 f` through the argument.

Triviality of the section groups is read off `CategoryTheory.Limits.IsZero.iff_id_eq_zero`, the
same characterisation that `isZero_associatedModuleSheaf_of_subsingleton_moduleFiber` uses in the
other direction.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0BXE](https://stacks.math.columbia.edu/tag/0BXE)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- **A zero associated sheaf has trivial sections over every open.** -/
theorem subsingleton_moduleSections_of_isZero
    (hzero : Limits.IsZero (associatedModuleSheaf 𝒜 𝒨))
    (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Subsingleton (moduleSections 𝒜 𝒨 U) := by
  rw [Limits.IsZero.iff_id_eq_zero] at hzero
  have hall : ∀ a : (associatedModuleSheaf 𝒜 𝒨).val.obj (op U), a = 0 := fun a =>
    congrArg
      (fun φ : associatedModuleSheaf 𝒜 𝒨 ⟶ associatedModuleSheaf 𝒜 𝒨 =>
        (φ.val.app (op U)).hom a) hzero
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

/-- **A homogeneous element whose degree is a multiple of `deg f` is killed by a power of `f`,
when the associated sheaf vanishes.** This is the converse of
`exists_pow_smul_eq_zero_of_gradeEventuallyZero`. -/
theorem exists_pow_smul_eq_zero_of_isZero_associatedModuleSheaf
    (hzero : Limits.IsZero (associatedModuleSheaf 𝒜 𝒨))
    {k : ℕ} (hk : 0 < k) {f : S} (hf : f ∈ 𝒜 k)
    {n : ℕ} {x : M} (hx : x ∈ 𝒨 (n • (k : ℤ))) :
    ∃ j : ℕ, f ^ j • x = 0 := by
  have := subsingleton_moduleSections_of_isZero 𝒜 𝒨 hzero (ProjectiveSpectrum.basicOpen 𝒜 f)
  have hfrac : degreeZeroFraction 𝒜 𝒨 hf n x hx = 0 :=
    degreeZeroToSection_injective 𝒜 𝒨 hf hk
      ((Subsingleton.elim _ _).trans (map_zero (degreeZeroToSection 𝒜 𝒨 f)).symm)
  have hmk : (LocalizedModule.mk x ⟨f ^ n, ⟨n, rfl⟩⟩ :
      LocalizedModule.Away (R := S) f M) = 0 := congrArg Subtype.val hfrac
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers f), LocalizedModule.mk_eq] at hmk
  obtain ⟨u, hu⟩ := hmk
  obtain ⟨j, hj⟩ := u.2
  have hu' : u • x = (0 : M) := by simpa using hu
  exact ⟨j, by rw [show f ^ j = (u : S) from hj]; exact hu'⟩

/-- **A homogeneous element whose degree is divisible by `deg f`, possibly negative, is killed by
a power of `f`, when the associated sheaf vanishes.** -/
theorem exists_pow_smul_eq_zero_of_isZero_of_dvd
    (hzero : Limits.IsZero (associatedModuleSheaf 𝒜 𝒨))
    {k : ℕ} (hk : 0 < k) {f : S} (hf : f ∈ 𝒜 k)
    {c : ℤ} (hc : (k : ℤ) ∣ c) {x : M} (hx : x ∈ 𝒨 c) :
    ∃ j : ℕ, f ^ j • x = 0 := by
  obtain ⟨q, rfl⟩ := hc
  set t : ℕ := (-q).toNat with ht
  have hq : 0 ≤ q + (t : ℤ) := by
    rcases le_or_gt 0 q with h | h
    · have : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
      omega
    · have : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      omega
  have hmem : f ^ t • x ∈ 𝒨 (((q + (t : ℤ)).toNat : ℕ) • (k : ℤ)) := by
    have hft : f ^ t ∈ 𝒜 (t * k) := by
      simpa [mul_comm] using SetLike.pow_mem_graded t hf
    have := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) hft hx
    have hdeg : ((t * k : ℕ) : ℤ) + (k : ℤ) * q = ((q + (t : ℤ)).toNat : ℕ) • (k : ℤ) := by
      rw [nsmul_eq_mul, Int.toNat_of_nonneg hq]
      push_cast
      ring
    rwa [show ((t * k : ℕ) +ᵥ ((k : ℤ) * q)) = ((t * k : ℕ) : ℤ) + (k : ℤ) * q from rfl, hdeg]
      at this
  obtain ⟨j, hj⟩ := exists_pow_smul_eq_zero_of_isZero_associatedModuleSheaf 𝒜 𝒨 hzero hk hf hmem
  exact ⟨j + t, by rw [pow_add, mul_smul]; exact hj⟩

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
