module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Iso

/-!
# The twist comparison of an invertible homomorphism of graded rings

For an invertible homomorphism `φ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings, Tag 01MY's twist
comparison `θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)` is an isomorphism in every degree.

## Main results

* `Stacks.GradedLocalization.isAwayDegreewise_one_of_comp_eq_id`: a homomorphism of graded rings
  with a two-sided inverse is a degreewise localization away from `1`.
* `Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id`: **for an invertible homomorphism of
  graded rings the twist comparison is an isomorphism**, in every degree.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.GradedLocalization

open HomogeneousIdeal

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- **A homomorphism of nonnegatively graded rings with a two-sided inverse is, in each degree,
the localization away from `1`.** The image of `1` is a unit; a homogeneous element of the target
is the image of its value under the inverse, which has the same degree, with no power of `1` to
clear; and a homogeneous element of the kernel is its value under the inverse of `0`. -/
theorem isAwayDegreewise_one_of_comp_eq_id (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒜)
    (hφψ : φ.comp ψ = GradedRingHom.id ℬ) (hψφ : ψ.comp φ = GradedRingHom.id 𝒜) :
    IsAwayDegreewise φ (1 : A) where
  isUnit_map := by simp
  surj n y hy := ⟨0, ψ y, ψ.map_mem hy, by simpa using GradedRingHom.congr_fun hφψ y⟩
  torsion n x _ h :=
    ⟨0, by simpa [h] using (GradedRingHom.congr_fun hψφ x).symm⟩

end Stacks.GradedLocalization

namespace Stacks.ProjTwistComparison

open AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ)

/-- **The twist comparison of an invertible homomorphism of graded rings is an isomorphism**, in
every degree: `θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)` for `r = AlgebraicGeometry.Proj.map φ`.

Such a `φ` is the localization away from `1` in each degree,
`Stacks.GradedLocalization.isAwayDegreewise_one_of_comp_eq_id`, so this is
`Stacks.ProjTwistComparison.isIso_twistMap` at `g = 1`; no bijectivity argument of its own is
needed. -/
theorem isIso_twistMap_of_comp_eq_id (ψ : ℬ →+*ᵍ 𝒜)
    (hφψ : φ.comp ψ = GradedRingHom.id ℬ) (hψφ : ψ.comp φ = GradedRingHom.id 𝒜) :
    IsIso (twistMap φ hφ n) :=
  isIso_twistMap φ hφ n
    (Stacks.GradedLocalization.isAwayDegreewise_one_of_comp_eq_id φ ψ hφψ hψφ)
    (SetLike.one_mem_graded 𝒜)

end Stacks.ProjTwistComparison

end
