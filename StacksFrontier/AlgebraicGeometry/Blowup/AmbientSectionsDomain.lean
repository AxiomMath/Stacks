module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveAmbientSections
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedSectionsIdealPow

/-!
# The canonical map `Iⁿ ⟶ Γ(X, 𝒪_X(n))` is injective in *every* degree over a domain

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec A` in
`I`. [Stacks, Tag 0AG6] part (3) says the canonical map
`Stacks.LocalCohomology.UniformityIII.ambientSections I n : Iⁿ ⟶ Γ(X, 𝒪_X(n))` is bijective for
every **large** `n`, and both halves are proved that way in the library: the injective half is
`Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections` and the surjective
half is `Stacks.Blowup.exists_forall_surjective_ambientSections`.

For an `A` that is a domain and an `I ≠ 0` the injective half needs no threshold at all, and this
file removes it. The threshold of the general argument is there to make the finitely many
generators of the `S₊`-power torsion submodule of the Rees algebra reachable, and over a domain
that submodule is zero: the Rees algebra is a subalgebra of `A[T]`, hence a domain, and the
degree-`N` piece of it contains `aᴺTᴺ ≠ 0` for any `a ∈ I` with `a ≠ 0`.

Consequently `Iⁿ ≅ Γ(X, 𝒪_X(n))` for a degree `n` as soon as the canonical map is *surjective*
there, which is the shape in which the remaining obstruction to [Stacks, Tag 0AGS] part (4) sits:
only surjectivity still carries a threshold.

## Main results

The elided prefix is `Stacks.Blowup`.

* `injective_ambientSections_of_ne_bot`: **the injective half of [Stacks, Tag 0AG6] part (3) with
  no threshold**, for a nonzero ideal of a Noetherian domain.
* `bijective_ambientSections_iff_surjective`: over such a ring bijectivity in a degree is
  surjectivity in that degree.
* `injective_ambientSections_maximalIdeal`: the same for the maximal ideal of a regular local
  ring of dimension two, the setting of [Stacks, Tag 0AGS].

## References

* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Polynomial
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection degreeSection_eq_zero_iff)
open Stacks.LocalCohomology.UniformityIII (ambientSections)

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {I : Ideal A}

omit [IsNoetherianRing A] in
/-- **A nonzero ideal of a domain has a nonzero power in every degree of the Rees algebra.** For
`a ∈ I` nonzero the monomial `aᴺTᴺ` is a nonzero element of the degree-`N` piece. -/
theorem reesGradingEquivPow_pow_ne_zero (hI : I ≠ ⊥) (N : ℕ) :
    ∃ y : reesGrading I N, ((y : reesAlgebra I) : A[X]) ≠ 0 := by
  obtain ⟨a, haI, ha0⟩ := Submodule.ne_bot_iff I |>.1 hI
  refine ⟨reesGradingEquivPow I N ⟨a ^ N, Ideal.pow_mem_pow haI N⟩, ?_⟩
  rw [coe_reesGradingEquivPow]
  simpa using pow_ne_zero N ha0

/-- **The injective half of [Stacks, Tag 0AG6] part (3) in every degree, over a domain.** For a
nonzero ideal `I` of a Noetherian domain `A` the canonical map `Iⁿ ⟶ Γ(X, 𝒪_X(n))` of
`Stacks.LocalCohomology.UniformityIII.ambientSections` is injective for **every** `n`, with no
threshold.

By [Stacks, Tag 0BXK] a homogeneous element of the Rees algebra whose canonical twisted section
vanishes is killed by one whole homogeneous component
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff`, which applies because the
Rees algebra is Noetherian and generated in degree one). That component contains the nonzero
`aᴺTᴺ` of `Stacks.Blowup.reesGradingEquivPow_pow_ne_zero`, and the Rees algebra is a subalgebra
of `A[T]`, hence has no zero divisors; so the element is zero. -/
theorem injective_ambientSections_of_ne_bot (hI : I ≠ ⊥) (n : ℕ) :
    Function.Injective (ambientSections I n) := by
  refine (injective_iff_map_eq_zero (ambientSections I n)).2 fun z hz => ?_
  have hb : degreeSection (reesGrading I) n (reesGradingEquivPow I n z) = 0 := hz
  obtain ⟨N, hN⟩ := (degreeSection_eq_zero_iff (reesGrading I)
    (adjoin_reesGradingZero_reesGrading_one_eq_top I) (reesGradingEquivPow I n z)).1 hb
  obtain ⟨y, hy⟩ := reesGradingEquivPow_pow_ne_zero (I := I) hI N
  have hzero := hN (y : reesAlgebra I) y.2
  have hcoe : (((y : reesAlgebra I) * (reesGradingEquivPow I n z : reesAlgebra I) :
      reesAlgebra I) : A[X]) = 0 := by rw [hzero]; rfl
  rw [Subalgebra.coe_mul, coe_reesGradingEquivPow] at hcoe
  have hz0 : (z : A) = 0 := by
    rcases mul_eq_zero.1 hcoe with h | h
    · exact absurd h hy
    · simpa using congrArg (fun p : A[X] => p.coeff n) h
  exact Subtype.ext hz0

/-- **Over a Noetherian domain the canonical map `Iⁿ ⟶ Γ(X, 𝒪_X(n))` is bijective exactly when it
is surjective.** Its injectivity is unconditional by
`Stacks.Blowup.injective_ambientSections_of_ne_bot`. -/
theorem bijective_ambientSections_iff_surjective (hI : I ≠ ⊥) (n : ℕ) :
    Function.Bijective (ambientSections I n) ↔ Function.Surjective (ambientSections I n) :=
  ⟨And.right, fun h => ⟨injective_ambientSections_of_ne_bot hI n, h⟩⟩

/-- **The canonical map `𝔪ⁿ ⟶ Γ(X, 𝒪_X(n))` is injective in every degree**, for `𝔪` the maximal
ideal of a regular local ring of dimension two and `X` the blowup of `Spec A` in `𝔪`. This is the
setting of [Stacks, Tag 0AGS]; a regular local ring is a domain, and its maximal ideal is nonzero
because its dimension is not zero. -/
theorem injective_ambientSections_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) (n : ℕ) :
    Function.Injective (ambientSections (IsLocalRing.maximalIdeal A) n) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  refine injective_ambientSections_of_ne_bot (fun hbot => ?_) n
  have hfield : IsField A := IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot
  exact (by norm_num : (2 : WithBot ℕ∞) ≠ 0)
    (hdim.symm.trans (ringKrullDim_eq_zero_of_isField hfield))

end Stacks.Blowup

end
