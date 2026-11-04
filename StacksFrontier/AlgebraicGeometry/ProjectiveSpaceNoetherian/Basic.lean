module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective space over a locally Noetherian scheme

Projective `n`-space over a scheme `S` is `AlgebraicGeometry.projectiveSpaceOver n S`, the base
change `S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model along the structure morphism of `S`. This file
shows that `ℙⁿ_S` is locally Noetherian whenever `S` is.

The argument is the standard one: `ℙⁿ_ℤ ⟶ Spec ℤ` is locally of finite type, that property is
stable under base change, and a scheme locally of finite type over a locally Noetherian scheme is
locally Noetherian — the last two steps being Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` and the pullback instances beside it.
So the only thing to prove is that the structure morphism of the integral model is locally of
finite type, and Mathlib's `Proj.toSpecZero` already is, for a graded ring of finite type over its
degree-zero part. Two small facts about the total-degree grading of a polynomial ring close the
gap: the degree-zero part is exactly the ring of constants, and the polynomial ring is of finite
type over it.

## Main results

* `MvPolynomial.algebraMap_homogeneousSubmodule_zero_surjective`: the degree-zero part of the
  total-degree grading of `R[Xᵢ]` is the image of `R`.
* `MvPolynomial.finiteType_homogeneousSubmodule_zero`: that degree-zero part is of finite type
  over `R`.
* `AlgebraicGeometry.locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse`: the structure
  morphism `ℙⁿ_ℤ ⟶ Spec ℤ` of the integral model is locally of finite type.
* `AlgebraicGeometry.projectiveSpaceOver_isLocallyNoetherian`: projective space over a locally
  Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.projectiveSpaceOver_isNoetherian`: projective space over a Noetherian scheme
  is Noetherian, the quasi-compactness half coming from properness of `ℙⁿ_S ⟶ S`.

## Implementation notes

`AlgebraicGeometry.projectiveSpaceOver` is a pullback over the terminal scheme, and the terminal
scheme is not literally `Spec (ULift ℤ)`; the two are identified by the unique isomorphism between
terminal objects. The structure morphism of the integral model therefore factors as
`Proj.toSpecZero` followed by `Spec` of the structure map `ULift ℤ → 𝒜 0` and then by that
isomorphism, the factorisation being forced by uniqueness of morphisms into a terminal object.
Only the middle factor needs an argument, and for it surjectivity of `ULift ℤ → 𝒜 0` is more than
enough.

`SetLike.GradeZero.isScalarTower` is deliberately a theorem rather than an instance, matching the
treatment of the tower in `StacksFrontier/RingTheory/HomogeneousLocalization/BaseAlgebra.lean`: a
global tower instance on the degree-zero part competes with the module structures that file puts
on submodules of a localization.

`StacksFrontier/RingTheory/HomogeneousLocalization/DegreeZero.lean` proves the general statement
`HomogeneousLocalization.gradeZero_finiteType`, that the degree-zero part of a graded algebra of
finite type is of finite type. It is not used here: for the total-degree grading the degree-zero
part is the constants outright, which is both shorter and the sharper statement, and importing
that file would pull in its very large import closure.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
-/

@[expose] public section

open CategoryTheory Limits MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SetLike.GradeZero

/-- The tower `R → 𝒜 0 → A` for a grading of an `R`-algebra `A` by `R`-submodules: the structure
map of `𝒜 0` is the structure map of `A` with its image corestricted, and the structure map of `A`
over `𝒜 0` is the inclusion.

Deliberately not an instance; see the module docstring. -/
public theorem isScalarTower {ι R A : Type*} [AddMonoid ι] [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜] : IsScalarTower R (𝒜 0) A :=
  IsScalarTower.of_algebraMap_eq fun _ => by simp

end SetLike.GradeZero

namespace MvPolynomial

variable (σ : Type*) (R : Type*) [CommRing R]

/-- The degree-zero part of the total-degree grading of a polynomial ring is the image of the
coefficient ring: a polynomial homogeneous of degree `0` is a constant. -/
public theorem algebraMap_homogeneousSubmodule_zero_surjective :
    Function.Surjective (algebraMap R (homogeneousSubmodule σ R 0)) := by
  rintro ⟨p, hp⟩
  rw [homogeneousSubmodule_zero, Submodule.mem_one] at hp
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, Subtype.ext hr⟩

/-- The degree-zero part of the total-degree grading of a polynomial ring is of finite type over
the coefficient ring, being a quotient of it. -/
public theorem finiteType_homogeneousSubmodule_zero :
    Algebra.FiniteType R (homogeneousSubmodule σ R 0) :=
  .of_surjective (Algebra.ofId R _) (algebraMap_homogeneousSubmodule_zero_surjective σ R)

/-- A polynomial ring in finitely many variables is of finite type over the degree-zero part of
its total-degree grading: it is already of finite type over the coefficient ring, which maps into
that degree-zero part. -/
public instance finiteType_of_homogeneousSubmodule_zero [Finite σ] :
    Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  have := SetLike.GradeZero.isScalarTower (homogeneousSubmodule σ R)
  .of_restrictScalars_finiteType R _ _

end MvPolynomial

namespace AlgebraicGeometry

universe u

/-- The structure morphism of the integral model of projective space is locally of finite type.

`Proj.toSpecZero` of the total-degree grading is locally of finite type because the polynomial
ring is of finite type over its degree-zero part, and the remaining factors to the terminal
scheme are `Spec` of the structure map `ULift ℤ → 𝒜 0`, of finite type because that map is
surjective, and an isomorphism of terminal objects. -/
@[ega "II 2.7.1" "locally of finite type"]
public theorem locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse (n : ℕ) :
    LocallyOfFiniteType (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  set 𝒜 := homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)
  let φ : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of (𝒜 0) :=
    CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (𝒜 0))
  let e : Spec (CommRingCat.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  have hfactor : terminal.from (projectiveSpaceAtUniverse.{u} n) =
      (Proj.toSpecZero 𝒜 ≫ Spec.map φ) ≫ e.hom := terminal.hom_ext _ _
  rw [hfactor]
  refine MorphismProperty.comp_mem _ _ _
    (MorphismProperty.comp_mem _ _ _ inferInstance ?_) inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr (finiteType_homogeneousSubmodule_zero _ _)

/-- Projective space over a locally Noetherian scheme is locally Noetherian.

`ℙⁿ_S` is the base change of the integral model along the structure morphism of `S`, and the
structure morphism of the integral model is locally of finite type. -/
@[ega "I 6.3.8" "special case"]
public theorem projectiveSpaceOver_isLocallyNoetherian (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] : IsLocallyNoetherian (projectiveSpaceOver n S) :=
  have := locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse.{u} n
  inferInstance

/-- Projective space over a Noetherian scheme is Noetherian.

`IsNoetherian` is local Noetherianity together with quasi-compactness. The first half is
`projectiveSpaceOver_isLocallyNoetherian`; the second comes from properness of the structure
morphism `ℙⁿ_S ⟶ S`, which is quasi-compact, so `ℙⁿ_S` is quasi-compact whenever `S` is. -/
public theorem projectiveSpaceOver_isNoetherian (n : ℕ) (S : Scheme.{u}) [IsNoetherian S] :
    IsNoetherian (projectiveSpaceOver n S) :=
  have : IsLocallyNoetherian (projectiveSpaceOver n S) :=
    projectiveSpaceOver_isLocallyNoetherian n S
  have : CompactSpace (projectiveSpaceOver n S) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver n S ↘ S)
  {}

end AlgebraicGeometry

end
