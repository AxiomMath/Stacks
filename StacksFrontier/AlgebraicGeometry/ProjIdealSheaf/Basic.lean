module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCommonMultiple.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal of a closed subscheme of `Proj`, read on affine charts

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring generated in degree one over `𝒮 0`, let
`X = Proj 𝒮`, and let `i : Z ⟶ X` be a closed immersion. The ideal
`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme` is defined by the vanishing of
pulled-back twisted global sections, which is a condition on the scheme `Z` as a whole. This file
converts that condition into one on affine charts of `X`.

The route is the zero scheme. Over a ring generated in degree one every twisting sheaf `𝒪_X(n)` is
invertible — and over an arbitrary graded ring, `𝒪_X(n · D)` is invertible for `D` the common
degree of a covering family — so a global section of such a twist has a zero scheme, and a morphism
kills the section exactly when it factors through that zero scheme. Factoring through a closed
subscheme is an inequality of ideal sheaves, and an inequality of ideal sheaves is checked on
affine opens. So membership in the ideal of `Z` becomes, degree by degree and chart by chart, an
inclusion of ideals of sections of the structure sheaf — a statement about rings, where prime
ideals and associated primes can be spoken of.

## Main results

* `MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top`: a polynomial ring is generated in degree
  one over its degree-zero part, so all of the degree-one machinery applies to projective space.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf`: the
  twisting sheaves of a ring generated in degree one are invertible, in the spelling the zero
  scheme demands.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf`: the same
  on projective space, as an instance.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.algebraicGeometry_isInvertible_twistingSheaf_of_cover`: the twists `𝒪(n · D)` are invertible,
  in the same spelling, whenever the standard opens of a family of homogeneous elements of one
  degree `D` cover `Proj 𝒮` — with **no** hypothesis on the grading. This is the form the proof of
  Stacks Tag 0801 uses.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker`: the twisted section of a
  homogeneous element pulls back to zero on `Z` exactly when its zero scheme contains `Z`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_idealOfClosedSubscheme_iff_zeroScheme_le_ker`:
  **the ideal-sheaf criterion** for membership in the ideal of `Z`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_idealOfClosedSubscheme_iff_forall_affineOpens`
  and `AlgebraicGeometry.ProjectiveSpectrum.Proj.projectiveSpace_mem_idealOfClosedSubscheme_iff`:
  **the chartwise criterion**, in general and on projective space.

## Implementation notes

Two spellings have to be crossed, and the crossing is made once for each of the two sources of
invertibility — degree-one generation, and a common-degree cover. The invertibility of the
twisting sheaves, `Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf`, concludes in
`Stacks.SheafOfModules.IsInvertible`, whereas `AlgebraicGeometry.zeroScheme` consumes
`AlgebraicGeometry.SheafOfModules.IsInvertible`; these are distinct constants with identical
definitions and neither discharges the other by instance search, so the crossing is made once,
through `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

The per-degree bridge is assembled in term mode. A `rw` with
`AlgebraicGeometry.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme` fails, because
`twistingSheaf 𝒮 n` is a `SheafOfModules` over
`sheafCompose … (ProjectiveSpectrum.Proj.structureSheaf 𝒮)` while the lemma is stated over
`(Proj 𝒮).Modules`; the two agree only up to unfolding, which `rw`'s matching does not do.
Applying the equivalence directly and chaining with `Eq.trans` needs no transparency adjustment.

Degree-one generation of a polynomial ring is obtained from Mathlib's
`MvPolynomial.adjoin_range_X` by moving the base up the scalar tower from `R` to the degree-zero
part, which is `Stacks.Algebra.adjoin_eq_top_of_isScalarTower`; the variables are homogeneous of
degree one, so the generating set only has to be enlarged.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A polynomial ring is generated in degree one over its degree-zero part.** The variables are
homogeneous of degree one and generate the ring over the constants, hence a fortiori over the
larger base of all degree-zero elements. -/
theorem adjoin_homogeneousSubmodule_one_eq_top (ι R : Type*) [CommRing R] :
    Algebra.adjoin (homogeneousSubmodule ι R 0)
      ((homogeneousSubmodule ι R 1 : Submodule R (MvPolynomial ι R)) :
        Set (MvPolynomial ι R)) = ⊤ := by
  refine Stacks.Algebra.adjoin_eq_top_of_isScalarTower (R := R) _ (top_unique ?_)
  rw [← adjoin_range_X (R := R) (σ := ι)]
  exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact isHomogeneous_X R i)

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The twisting sheaves of a graded ring generated in degree one are invertible, in the class
`AlgebraicGeometry.zeroScheme` consumes. This is
`Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf` crossed once over the two
coinciding `IsInvertible` classes. -/
@[ega "II 8.6.4" "partial"]
theorem algebraicGeometry_isInvertible_twistingSheaf
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 n) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf 𝒮 hgen n)

/-- **The twists at the multiples of the common degree of a covering family are invertible**, in
the class `AlgebraicGeometry.zeroScheme` consumes.

The standard opens of homogeneous `g k` of one degree `D` cover `Proj 𝒮`, and `𝒪(n · D)` is
trivialized on `D₊(g k)` by `g k ^ n`. **No generation in degree one and no Noetherian hypothesis
is used**: this is the form in which the proof of Stacks Tag 0801 uses invertibility of the
twists, namely
`Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.isInvertible_twistingSheaf_of_cover` crossed
once over the two coinciding `IsInvertible` classes, exactly as
`algebraicGeometry_isInvertible_twistingSheaf` crosses its degree-one counterpart. -/
theorem algebraicGeometry_isInvertible_twistingSheaf_of_cover {ι : Type*} (g : ι → S) (D : ℕ)
    (hg : ∀ k, g k ∈ 𝒮 D) (hcov : ⨆ k, Proj.basicOpen 𝒮 (g k) = ⊤) (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 ((n • D : ℕ) : ℤ)) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.isInvertible_twistingSheaf_of_cover
      𝒮 g (fun _ => D) hg hcov (fun _ => (n : ℤ)) fun _ => by push_cast [smul_eq_mul]; ring)

/-- **The canonical twisted section of a homogeneous element pulls back to zero on `Z` exactly
when the zero scheme of that section contains `Z`.** Vanishing of the pullback is factorization
through the zero scheme (Tag 02OR), and factorization through a closed subscheme is an inequality
of ideal sheaves. -/
theorem pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) {n : ℕ} (b : 𝒮 n)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 (n : ℤ))] :
    pullbackGlobalSections i (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n b) = 0 ↔
      zeroScheme (Proj 𝒮) (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n b) ≤ i.ker :=
  (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme (Proj 𝒮)
      (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n b) i).trans
    (factorsThrough_ideal_iff_ideal_le_ker _ i)

/-- **The ideal-sheaf criterion for the ideal of a closed subscheme of `Proj`.** An element of `S`
lies in the ideal of `Z` exactly when, for every `n`, the zero scheme of the twisted section
attached to its degree-`n` component contains `Z`. -/
theorem mem_idealOfClosedSubscheme_iff_zeroScheme_le_ker {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i]
    [∀ n : ℕ, AlgebraicGeometry.SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 (n : ℤ))] (a : S) :
    a ∈ idealOfClosedSubscheme 𝒮 i ↔
      ∀ n : ℕ, zeroScheme (Proj 𝒮) (twistingSheaf 𝒮 (n : ℤ))
        (degreeSection 𝒮 n (DirectSum.decompose 𝒮 a n)) ≤ i.ker :=
  (mem_idealOfClosedSubscheme_iff 𝒮 i a).trans (forall_congr' fun n =>
    pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker 𝒮 i
      (DirectSum.decompose 𝒮 a n))

/-- **The chartwise criterion for the ideal of a closed subscheme of `Proj`.** An element of `S`
lies in the ideal of `Z` exactly when, for every degree `n` and every affine open `U` of
`Proj 𝒮`, the defining ideal over `U` of the zero scheme of the `n`-th twisted section is carried
to zero by `i`. This is the form in which the condition becomes a statement about ideals of a
commutative ring. -/
theorem mem_idealOfClosedSubscheme_iff_forall_affineOpens {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i]
    [∀ n : ℕ, AlgebraicGeometry.SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 (n : ℤ))] (a : S) :
    a ∈ idealOfClosedSubscheme 𝒮 i ↔
      ∀ (n : ℕ) (U : (Proj 𝒮).affineOpens),
        (zeroScheme (Proj 𝒮) (twistingSheaf 𝒮 (n : ℤ))
            (degreeSection 𝒮 n (DirectSum.decompose 𝒮 a n))).ideal U ≤
          RingHom.ker (i.app U.1).hom :=
  (mem_idealOfClosedSubscheme_iff_zeroScheme_le_ker 𝒮 i a).trans
    (forall_congr' fun _ => Scheme.IdealSheafData.le_ofIdeals_iff)

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (d : ℕ)

/-- Every twisting sheaf on projective space is invertible: a polynomial ring is generated in
degree one. -/
instance projectiveSpace_isInvertible_twistingSheaf (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (Proj (MvPolynomial.homogeneousSubmodule (Fin d) R)).sheaf.obj
      (Proj (MvPolynomial.homogeneousSubmodule (Fin d) R)).ringCatSheaf.property
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin d) R) n) :=
  algebraicGeometry_isInvertible_twistingSheaf _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin d) R) n

/-- **The chartwise criterion on projective space.** A polynomial lies in the homogeneous ideal of
a closed subscheme `Z ⊆ P^{d-1}_R` exactly when, in every degree and over every affine open, the
defining ideal of the zero scheme of the corresponding twisted section dies on `Z`. -/
theorem projectiveSpace_mem_idealOfClosedSubscheme_iff {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin d) R)) [IsClosedImmersion i]
    (a : MvPolynomial (Fin d) R) :
    a ∈ idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin d) R) i ↔
      ∀ (n : ℕ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin d) R)).affineOpens),
        (zeroScheme (Proj (MvPolynomial.homogeneousSubmodule (Fin d) R))
            (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin d) R) (n : ℤ))
            (degreeSection (MvPolynomial.homogeneousSubmodule (Fin d) R) n
              (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin d) R) a n))).ideal U ≤
          RingHom.ker (i.app U.1).hom :=
  mem_idealOfClosedSubscheme_iff_forall_affineOpens _ i a

end ProjectiveSpace

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
