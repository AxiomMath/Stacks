module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.KoszulTopDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of the structure sheaf of projective space is the structure sheaf of the base

Let `S` be a scheme and `n` a natural number, and let `f : ℙⁿ_S ⟶ S` be the structure morphism.
The canonical morphism

`𝒪_S ⟶ f_* 𝒪_{ℙⁿ_S}`

is an **isomorphism**, over an arbitrary base. Over an affine base this is the computation
`Γ(ℙⁿ_{Spec R}, 𝒪) = R` of
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.isIso_app_structureMorphism_projectiveSpaceOver`, which is available on the sections over every
affine open of an arbitrary base; the basic opens of the members of an affine open covering form
a basis of the base, and a morphism of sheaves which is invertible on a basis is invertible. That
last step is `Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen`, and it is what assembles
the sectionwise statement into the degree-zero row of [Stacks, Tag 01XW] at the zeroth twist as
an isomorphism of sheaves of modules on `S`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `pushforwardUnitIso`: **`f_* 𝒪_{ℙⁿ_S} ≅ 𝒪_S`.**
* `pushZeroTwistIso`: **`R⁰ f_* 𝒪(0) ≅ 𝒪_S`**, the same statement for the right derived functor
  and the zeroth twist, which is the shape the Koszul resolution of `𝒪(-n-1)` ends in.

## Main results

* `isIso_c_structureMorphism_projectiveSpaceOver`: the comparison of sheaves of rings
  `𝒪_S ⟶ f_* 𝒪_{ℙⁿ_S}` is invertible.
* `isIso_unitToPushforwardUnit_projectiveSpaceOver`: the same for the comparison of sheaves of
  modules.

## Implementation notes

The two spellings of the comparison — `AlgebraicGeometry.Scheme.Hom.c` for sheaves of rings and
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` for sheaves of modules — are identified
by `Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit`;
they are the same morphism, read in two categories.

The passage from the underived direct image to its zeroth right derived functor is
`Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso`, and the zeroth
twist is the structure sheaf by
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit`.

No `stacks` attribute is attached: the degree-zero row of [Stacks, Tag 01XW] at the zeroth twist
carries its attribute on
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.isIso_app_structureMorphism_projectiveSpaceOver`, and what is added below is the assembly of
that sectionwise statement into an isomorphism of sheaves.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistZeroIsoUnit)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- **The comparison `𝒪_S ⟶ f_* 𝒪_{ℙⁿ_S}` of sheaves of rings is invertible**, over an
arbitrary base: it is invertible on the sections over every affine open, in particular over every
basic open of a member of an affine open covering, and those form a basis of the base. -/
theorem isIso_c_structureMorphism_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    IsIso (projectiveSpaceOver n S ↘ S).c :=
  Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen (projectiveSpaceOver n S ↘ S)
    (fun V : S.affineOpens => (V : S.Opens)) (fun V => V.2) (iSup_affineOpens_eq_top S)
    fun V r => isIso_app_structureMorphism_projectiveSpaceOver n S (V.2.basicOpen r)

/-- **The comparison `𝒪_S ⟶ f_* 𝒪_{ℙⁿ_S}` of sheaves of modules is invertible**, over an
arbitrary base. -/
theorem isIso_unitToPushforwardUnit_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    IsIso (Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOver n S ↘ S)) :=
  (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
    (projectiveSpaceOver n S ↘ S)).1 (isIso_c_structureMorphism_projectiveSpaceOver n S)

/-- **`f_* 𝒪_{ℙⁿ_S} ≅ 𝒪_S`**, over an arbitrary base. -/
def pushforwardUnitIso (n : ℕ) (S : Scheme.{u}) :
    (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).obj
        (Scheme.unitModule (projectiveSpaceOver n S)) ≅ Scheme.unitModule S :=
  (@asIso _ _ _ _ _ (isIso_unitToPushforwardUnit_projectiveSpaceOver n S)).symm

/-- **`R⁰ f_* 𝒪(0) ≅ 𝒪_S`**, over an arbitrary base: the zeroth right derived functor of the
direct image is the direct image, and the zeroth twist is the structure sheaf. -/
@[sga "7 XI 1.1" "special case"]
def pushZeroTwistIso (m : ℕ) (S : Scheme.{u}) :
    (push m S 0).obj (twistOver (m + 1) S 0) ≅ Scheme.unitModule S :=
  (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso
      (projectiveSpaceOver (m + 1) S ↘ S)).app (twistOver (m + 1) S 0) ≪≫
    (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).mapIso
      (twistZeroIsoUnit (m + 1) S) ≪≫
    pushforwardUnitIso (m + 1) S

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
