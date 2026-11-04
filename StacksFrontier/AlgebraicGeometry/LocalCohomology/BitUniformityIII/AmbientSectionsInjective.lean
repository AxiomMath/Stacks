module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientSections
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.KernelData
public import StacksCore.Tactic.StacksAttribute

/-!
# The injective half of Serre's computation of the sections, on the blowup

[Stacks, Tag 0AG6] part (3) says that for a graded ring `S` generated in degree one over a
Noetherian `S₀` the canonical map `S_q ⟶ Γ(Proj S, 𝒪(q))` is *bijective* for all large `q`. On
the blowup `X = Proj(⨁ₙ Iⁿ)` of `Spec(A)` in `I` that map is
`Stacks.LocalCohomology.UniformityIII.ambientSections`, and the statement was the field
`amb_serre_sections` of `Stacks.LocalCohomology.UniformityIII.GeometricInput` — an input of the
four clauses of [Stacks, Tag 0GA7] which is a theorem of the source rather than part of the
Situation of [Stacks, Tag 0GA6], and which clause (4) now calls rather than assumes.

This file proves the **injective half** of it, for an arbitrary Noetherian graded ring generated
in degree one, and specialises it to the blowup, so that only the surjective half was left to
supply: see
`Stacks.LocalCohomology.UniformityIII.exists_bijective_ambientSections_of_exists_surjective`, and
`Stacks.Blowup.exists_forall_surjective_ambientSections` for the half itself.

## The argument

By [Stacks, Tag 0BXK] — `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff` —
a homogeneous element whose twisted section vanishes is `S₊`-power torsion. Those elements are
finitely generated:
`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_homogeneous_generators` produces
homogeneous `x j` of degrees `d j` spanning all of them, and each `x j` is annihilated by
`S₊ ^ (N j)` for some `N j`. Now let `q ≥ max (d j + N j)` and let `b ∈ S_q` have vanishing
section. Then `b = ∑ a j * x j` with `a j` homogeneous of degree `q - d j`
(`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_homogeneous_coeffs`), and a homogeneous
element of degree `e` lies in `S₊ ^ e` when `S` is generated in degree one
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_irrelevant_pow_of_mem`). Since
`q - d j ≥ N j`, each `a j` lies in `S₊ ^ (N j)`, which annihilates `x j`; so every summand is
`0` and `b = 0`.

The degree bound is where the finiteness is used, and it is why the conclusion is only for large
`q`: in low degrees the kernel is genuinely nonzero in general.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_forall_eq_zero_of_degreeSection_eq_zero`
  is **the injective half of [Stacks, Tag 0AG6] part (3)** for any Noetherian graded ring generated
  in degree one.
* `Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections`: the same on the
  blowup, for the canonical map `Iᑫ ⟶ H⁰(X, 𝒪_X(q))`.
* `Stacks.LocalCohomology.UniformityIII.exists_bijective_ambientSections_of_exists_surjective`:
  consequently the former field `amb_serre_sections` of
  `Stacks.LocalCohomology.UniformityIII.GeometricInput` follows from its surjective half alone.

## Implementation notes

The degree bound is `Finset.univ.sup (fun j => d j + N j)` rather than a sum, so that
`Finset.le_sup` gives the per-generator inequality directly.

The general statement is phrased as "the element is zero" rather than as injectivity of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`, which is a bare function with no
additive structure recorded at that spelling; injectivity appears on the blowup, where
`Stacks.LocalCohomology.UniformityIII.ambientSections` is an additive map.

## References

* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.ProjLargeDegreeSections

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The injective half of [Stacks, Tag 0AG6] part (3).** For a Noetherian graded ring
generated in degree one over its degree-zero part there is a degree `n₀` beyond which the
canonical map `S_q ⟶ Γ(Proj 𝒮, 𝒪(q))` of [Stacks, Tag 01MP] has trivial kernel.

The homogeneous elements of the kernel are the `𝒮₊`-power torsion ones, finitely many of them
generate the rest, and a homogeneous element of large enough degree has its homogeneous
coefficients deep enough in `𝒮₊` to annihilate every generator. -/
theorem exists_forall_eq_zero_of_degreeSection_eq_zero [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    ∃ n₀ : ℕ, ∀ q : ℕ, n₀ ≤ q → ∀ b : 𝒮 q, degreeSection 𝒮 q b = 0 → (b : S) = 0 := by
  classical
  obtain ⟨r, x, d, hx, hx0, hspan⟩ := exists_homogeneous_generators 𝒮
  choose N hN using fun j : Fin r =>
    exists_irrelevant_pow_le_annihilator_of_degreeSection_eq_zero 𝒮 hgen ⟨x j, hx j⟩ (hx0 j)
  refine ⟨Finset.univ.sup fun j => d j + N j, fun q hq b hb => ?_⟩
  have hbound : ∀ j : Fin r, d j + N j ≤ q := fun j =>
    le_trans (Finset.le_sup (f := fun j => d j + N j) (Finset.mem_univ j)) hq
  have hmem : (b : S) ∈ homogeneousVanishing 𝒮 := ⟨q, b.2, hb⟩
  obtain ⟨a, ha⟩ := exists_homogeneous_coeffs 𝒮 x d (fun j => q - d j) hx
    (fun j => by have := hbound j; omega) b.2 (hspan hmem)
  rw [ha]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 : (a j : S) ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ (q - d j) :=
    mem_irrelevant_pow_of_mem 𝒮 hgen _ (a j).2
  have h2 : (a j : S) ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N j :=
    Ideal.pow_le_pow_right (by have := hbound j; omega) h1
  simpa [smul_eq_mul] using
    (Submodule.mem_annihilator_span_singleton (x j) (a j : S)).mp (hN j h2)

end Stacks.AlgebraicGeometry.ProjLargeDegreeSections

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The injective half of [Stacks, Tag 0AG6] part (3) on the blowup.** For a Noetherian ring
`A` and an ideal `I` there is a degree beyond which the canonical map `Iᑫ ⟶ H⁰(X, 𝒪_X(q))` of
`Stacks.LocalCohomology.UniformityIII.ambientSections` is injective.

This is
`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_forall_eq_zero_of_degreeSection_eq_zero`
at the Rees grading, which is Noetherian because `A` is and generated in degree one by
`Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top`. -/
theorem exists_forall_injective_ambientSections [IsNoetherianRing A] :
    ∃ n₀ : ℕ, ∀ q : ℕ, n₀ ≤ q → Function.Injective (ambientSections I q) := by
  obtain ⟨n₀, hn₀⟩ :=
    Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_forall_eq_zero_of_degreeSection_eq_zero
      (Stacks.Blowup.reesGrading I) (Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top I)
  refine ⟨n₀, fun q hq => (injective_iff_map_eq_zero (ambientSections I q)).2 fun y hy => ?_⟩
  have hzero : ((Stacks.Blowup.reesGradingEquivPow I q y : Stacks.Blowup.reesGrading I q) :
      reesAlgebra I) = 0 :=
    hn₀ q hq (Stacks.Blowup.reesGradingEquivPow I q y) hy
  exact (Stacks.Blowup.reesGradingEquivPow I q).injective
    (Subtype.ext (by simpa using hzero))

/-- **The former field `amb_serre_sections` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput` follows from its surjective half.**

[Stacks, Tag 0AG6] part (3) asserts that `Iᑫ ⟶ H⁰(X, 𝒪_X(q))` is bijective for large `q`; the
injectivity is `exists_forall_injective_ambientSections`, so only the surjectivity has to be
assumed. -/
theorem exists_bijective_ambientSections_of_exists_surjective [IsNoetherianRing A]
    (hsurj : ∃ n₀ : ℕ, ∀ q : ℕ, n₀ ≤ q → Function.Surjective (ambientSections I q)) :
    ∃ n₀ : ℕ, ∀ q : ℕ, n₀ ≤ q → Function.Bijective (ambientSections I q) := by
  obtain ⟨n₁, hn₁⟩ := hsurj
  obtain ⟨n₂, hn₂⟩ := exists_forall_injective_ambientSections I
  exact ⟨max n₁ n₂, fun q hq =>
    ⟨hn₂ q (le_trans (le_max_right n₁ n₂) hq), hn₁ q (le_trans (le_max_left n₁ n₂) hq)⟩⟩

end Stacks.LocalCohomology.UniformityIII

end
