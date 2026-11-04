module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Localization

/-!
# The converse of Stacks 0F8B at Noetherian stages, at instances with every binder filled in

`AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit` is the substantial direction of
[Stacks, Tag 0F8B] at Noetherian stages, and
`AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty` is the one place it is
applied: to the inverse system of schemes of finite type over the integers that
[Stacks, Tag 01ZA] produces, whose stages are Noetherian.  This file instantiates that
application at two schemes, assuming nothing at all about them, so that neither statement is
vacuous and the existential in the conclusion is actually witnessed.

`Spec R` for an arbitrary ring `R` is the first instance; `ℙⁿ_S` for an affine base `S` is the
second, and it is the one that matters, since it is not affine, need not be Noetherian, and its
system of finite type approximations is therefore not the constant one.

## Main results

* `AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty_spec` and
  `AlgebraicGeometry.exists_isAffineHom_isNoetherian_hasResolutionProperty_projectiveSpace`: the
  reduction of [Stacks, Tag 0F8C] to the Noetherian case, with every binder filled in.

## Implementation notes

No tag is attached: each statement is an instance of a tag already registered elsewhere, not the
statement of one.

## References

* [Stacks Project, Tag 0F8B](https://stacks.math.columbia.edu/tag/0F8B)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion
open Stacks.ProjectiveSpace

universe u

namespace AlgebraicGeometry

/-- **The reduction of [Stacks, Tag 0F8C] to the Noetherian case at `Spec R`, for an arbitrary
ring `R`.**  Every binder is filled in and nothing is assumed. -/
theorem exists_isAffineHom_isNoetherian_hasResolutionProperty_spec (R : CommRingCat.{u}) :
    ∃ (Y : Scheme.{u}) (f : Spec R ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y :=
  have _ : HasResolutionProperty (Spec R) := hasResolutionProperty_of_isAffine (Spec R)
  exists_isAffineHom_isNoetherian_hasResolutionProperty (Spec R)

/-- **The reduction of [Stacks, Tag 0F8C] to the Noetherian case at `ℙⁿ_S` for an affine base
`S`.**  Every binder is filled in and nothing is assumed beyond affineness of the base.

The hyperplane sheaf is ample on `ℙⁿ_S`, which supplies quasi-compactness, the resolution
property ([Stacks, Tag 0F87]) and separatedness.  `ℙⁿ_S` is not affine and need not be
Noetherian, so the inverse system of finite type approximations the proof runs through is not
the constant one and the scheme `Y` produced is not `ℙⁿ_S` itself. -/
theorem exists_isAffineHom_isNoetherian_hasResolutionProperty_projectiveSpace
    (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    ∃ (Y : Scheme.{u}) (f : projectiveSpaceOver n S ⟶ Y),
      IsAffineHom f ∧ IsNoetherian Y ∧ HasResolutionProperty Y :=
  have hL := isAmple_projectiveSpaceTwistingSheaf n S
  have _ : CompactSpace (projectiveSpaceOver n S) := hL.1
  have _ : HasResolutionProperty (projectiveSpaceOver n S) :=
    hasResolutionProperty_of_isAmple (projectiveSpaceTwistingSheaf n S) hL
  have _ : (projectiveSpaceOver n S).IsSeparated :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple (projectiveSpaceOver n S)
      (projectiveSpaceTwistingSheaf n S) hL).isSeparated
  exists_isAffineHom_isNoetherian_hasResolutionProperty (projectiveSpaceOver n S)

end AlgebraicGeometry

end
