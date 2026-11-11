module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.PrimeAvoidance

/-!
# Finite sets of points of an open subscheme of `Proj` lie in an affine open

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring and `U ⊆ Proj A` an open subscheme. Every finite set
`E ⊆ U` of points lies in a standard open `D₊(f) ⊆ U` with `f` homogeneous of positive degree,
and in particular in an affine open of `U`.

The complement of `U` is the zero locus of the homogeneous ideal `I` of elements lying in every
point of the complement. A point `x ∈ E` is a relevant homogeneous prime with `I ⊄ x`, hence also
`I ∩ A₊ ⊄ x` (as `I · A₊ ⊆ I ∩ A₊` and `A₊ ⊄ x`). Graded prime avoidance gives a homogeneous
`f ∈ I ∩ A₊` of positive degree lying in none of the points of `E`. Then `E ⊆ D₊(f)`, and
`D₊(f) ⊆ U` because `f` vanishes on the complement of `U`. The open `D₊(f)` of `Proj A` is
affine, and its preimage in `U` is affine because `U → Proj A` is an open immersion whose image
contains `D₊(f)`.

This applies in particular to projective space `Proj k[x_i : i ∈ ι]` over a field `k`.

## Main results

* `AlgebraicGeometry.Proj.exists_basicOpen_le_and_subset`: a finite set of points of an open
  `U ⊆ Proj A` lies in some `D₊(f) ⊆ U` with `f` homogeneous of positive degree.
* `AlgebraicGeometry.Proj.exists_isAffineOpen_finite_subset`: a finite set of points of the open
  subscheme `U` of `Proj A` lies in an affine open of `U`.
* `AlgebraicGeometry.Proj.exists_isAffineOpen_finite_subset_mvPolynomial`: the same statement for
  projective space `Proj k[x_i : i ∈ ι]` over a commutative ring, e.g. a field.

## References

* [Stacks Project, Tag 00JS](https://stacks.math.columbia.edu/tag/00JS) (graded prime avoidance)
-/

@[expose] public section

namespace AlgebraicGeometry.Proj

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A finite set `E` of points of an open `U` of `Proj A` is contained in a standard open
`D₊(f) ⊆ U` for some `f` homogeneous of positive degree. -/
theorem exists_basicOpen_le_and_subset (U : (Proj 𝒜).Opens) (E : Set (Proj 𝒜))
    (hE : E.Finite) (hEU : E ⊆ U) :
    ∃ (f : A) (m : ℕ), 0 < m ∧ f ∈ 𝒜 m ∧ basicOpen 𝒜 f ≤ U ∧ E ⊆ basicOpen 𝒜 f := by
  classical
  set Z : Set (ProjectiveSpectrum 𝒜) := (U : Set (Proj 𝒜))ᶜ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  set I : HomogeneousIdeal 𝒜 :=
    ProjectiveSpectrum.vanishingIdeal Z ⊓ HomogeneousIdeal.irrelevant 𝒜 with hIdef
  have hsub :
      ProjectiveSpectrum.zeroLocus 𝒜 (ProjectiveSpectrum.vanishingIdeal Z : Set A) ⊆ Z := by
    rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  have hIp : ∀ x ∈ hE.toFinset, ¬ I ≤ (x : ProjectiveSpectrum 𝒜).asHomogeneousIdeal := by
    intro x hx hle
    have hxE : x ∈ E := hE.mem_toFinset.mp hx
    replace hle : I.toIdeal ≤ (x : ProjectiveSpectrum 𝒜).asHomogeneousIdeal.toIdeal := hle
    rw [hIdef, HomogeneousIdeal.toIdeal_inf] at hle
    have hmul := (Ideal.mul_le_inf).trans hle
    rcases (Ideal.IsPrime.mul_le
        (ProjectiveSpectrum.isPrime (x : ProjectiveSpectrum 𝒜))).mp hmul with h | h
    · exact @hsub x
        (fun a ha => HomogeneousIdeal.mem_iff.mp (h (HomogeneousIdeal.mem_iff.mpr ha))) (hEU hxE)
    · exact (x : ProjectiveSpectrum 𝒜).not_irrelevant_le
        (show (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ _ from h)
  obtain ⟨f, hfI, ⟨d, hd, hfd⟩, hfavoid⟩ :=
    graded_silly_finset 𝒜 (fun x : ProjectiveSpectrum 𝒜 => x.asHomogeneousIdeal) I
      inf_le_right hE.toFinset (fun x _ => ProjectiveSpectrum.isPrime x) hIp
  rw [hIdef, HomogeneousIdeal.toIdeal_inf, Ideal.mem_inf] at hfI
  have hfZ : f ∈ ProjectiveSpectrum.vanishingIdeal Z := HomogeneousIdeal.mem_iff.mp hfI.1
  refine ⟨f, d, hd, hfd, fun y hy => ?_, fun x hx => ?_⟩
  · by_contra hyU
    exact (mem_basicOpen 𝒜 f y).mp hy
      ((ProjectiveSpectrum.mem_vanishingIdeal Z f).mp hfZ y hyU)
  · exact (mem_basicOpen 𝒜 f x).mpr fun h =>
      hfavoid x (hE.mem_toFinset.mpr hx) (HomogeneousIdeal.mem_iff.mpr h)

/-- **Finite sets of points of an open subscheme of `Proj A` lie in an affine open.** If `U` is
an open subscheme of `Proj A` and `E` is a finite set of points of `U`, there is an affine open
`O` of `U` containing `E`; it can be taken to be the preimage of a standard open `D₊(f) ⊆ U`. -/
theorem exists_isAffineOpen_finite_subset (U : (Proj 𝒜).Opens) (E : Set U.toScheme)
    (hE : E.Finite) : ∃ O : U.toScheme.Opens, IsAffineOpen O ∧ E ⊆ O := by
  obtain ⟨f, m, hm, hf, hfU, hEf⟩ :=
    exists_basicOpen_le_and_subset 𝒜 U (U.ι '' E) (hE.image _)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  refine ⟨U.ι ⁻¹ᵁ basicOpen 𝒜 f,
    (isAffineOpen_basicOpen 𝒜 f hf hm).preimage_of_isOpenImmersion U.ι
      (by rw [Scheme.Opens.opensRange_ι]; exact hfU), fun x hx => ?_⟩
  exact hEf ⟨x, hx, rfl⟩

section MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Finite sets of points of an open subscheme of projective space lie in an affine open.**
For a commutative ring `k` (for instance a field) and an open subscheme `U` of
`Proj k[x_i : i ∈ ι]`, every finite set of points of `U` lies in an affine open of `U`. -/
theorem exists_isAffineOpen_finite_subset_mvPolynomial {ι : Type*} (k : Type*) [CommRing k]
    (U : (Proj (MvPolynomial.homogeneousSubmodule ι k)).Opens) (E : Set U.toScheme)
    (hE : E.Finite) : ∃ O : U.toScheme.Opens, IsAffineOpen O ∧ E ⊆ O :=
  exists_isAffineOpen_finite_subset _ U E hE

end MvPolynomial

end AlgebraicGeometry.Proj
