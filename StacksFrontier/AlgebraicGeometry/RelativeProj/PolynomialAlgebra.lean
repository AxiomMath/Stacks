module

public import Mathlib.RingTheory.PolynomialAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.PolynomialGrading

/-!
# Adjoining a variable of degree one to a quasi-coherent graded algebra

Let `𝒜` be a quasi-coherent graded `𝒪_S`-algebra on a scheme `S`, in the affine-open form
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` of Situation 01NN. Adjoining a variable `S`
of degree one gives the quasi-coherent graded `𝒪_S`-algebra `𝒜[S]`: its ring of sections over an
affine open `U` is the polynomial ring `𝒜(U)[S]`, graded by
`Stacks.PolynomialGrading.grading`, with restriction maps acting on coefficients. This is the
graded algebra `𝒞_{Z/X,*}[S]` of [Stacks, Tag 0FBG], clause (5), for the conormal algebra.

Quasi-coherence is inherited: localizing a polynomial ring at a constant is the polynomial ring
over the localization (`Polynomial.isLocalization`).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.polynomial`: the graded algebra `𝒜[S]`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- Localizing a polynomial ring at a constant: if `B` is the localization of `A` away from `g`,
then `B[S]` is the localization of `A[S]` away from `g`, through `Polynomial.map`. -/
theorem polynomial_isLocalization_away {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (g : A) (h : letI := φ.toAlgebra; IsLocalization.Away g B) :
    letI := (Polynomial.mapRingHom φ).toAlgebra
    IsLocalization.Away (C g) B[X] := by
  let := φ.toAlgebra
  let : Algebra A[X] B[X] := Polynomial.algebra A B
  have hl := Polynomial.isLocalization (Submonoid.powers g) B
  rw [Submonoid.map_powers] at hl
  exact hl

/-- **The graded algebra `𝒜[S]`**: the variable `S` adjoined in degree one. Over an affine open
`U` its sections are `𝒜(U)[S]`. An `abbrev`, so that its rings of sections and their gradings
are visibly the polynomial rings and their gradings. -/
abbrev polynomial : GradedAlgebra S where
  ring U := CommRingCat.of (𝒜.ring U)[X]
  grading U := Stacks.PolynomialGrading.grading (𝒜.grading U)
  gradedRing U := Stacks.PolynomialGrading.instGradedRing (𝒜.grading U)
  str U := 𝒜.str U ≫ CommRingCat.ofHom C
  str_mem U r := Stacks.PolynomialGrading.C_mem_grading (𝒜.str_mem U r)
  res h := Stacks.PolynomialGrading.map (𝒜.res h)
  res_id U := by
    refine GradedRingHom.ext fun p => ?_
    change p.map (𝒜.res (le_refl U.toOpens)).toRingHom = p
    rw [𝒜.res_id]
    exact Polynomial.map_id
  res_comp hUV hVW := by
    refine GradedRingHom.ext fun p => ?_
    change p.map (𝒜.res (hUV.trans hVW)).toRingHom =
      (p.map (𝒜.res hVW).toRingHom).map (𝒜.res hUV).toRingHom
    rw [Polynomial.map_map, 𝒜.res_comp]
    rfl
  res_str h r := by
    change ((C ((𝒜.str _).hom r)).map (𝒜.res h).toRingHom) = C ((𝒜.str _).hom _)
    rw [Polynomial.map_C]
    exact congrArg C (𝒜.res_str h r)
  isLocalization U f :=
    polynomial_isLocalization_away (𝒜.res (S.basicOpen_le f)).toRingHom (𝒜.str U f)
      (𝒜.isLocalization U f)

/-- The sections of `𝒜[S]` over `U` are the polynomial ring `𝒜(U)[S]`. -/
theorem polynomial_ring (U : S.AffineZariskiSite) :
    𝒜.polynomial.ring U = CommRingCat.of (𝒜.ring U)[X] :=
  rfl

/-- The structure map of `𝒜[S]` is that of `𝒜` followed by the inclusion of constants. -/
theorem polynomial_str_apply (U : S.AffineZariskiSite) (r : Γ(S, U.toOpens)) :
    𝒜.polynomial.str U r = (C (𝒜.str U r) : (𝒜.ring U)[X]) :=
  rfl

/-- The restriction maps of `𝒜[S]` act on coefficients. -/
theorem polynomial_res_apply {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (p : (𝒜.ring V)[X]) : 𝒜.polynomial.res h p = p.map (𝒜.res h).toRingHom :=
  rfl

end Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra

end
