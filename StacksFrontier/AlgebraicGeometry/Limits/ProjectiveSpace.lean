module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# Projective space over a scheme

Projective `n`-space over the integers is `Proj` of the polynomial ring in `n + 1` variables
graded by total degree. Projective `n`-space over an arbitrary base scheme `S` is its base
change along `S ⟶ Spec ℤ`, where `Spec ℤ` is realised as the terminal scheme.

The main result is that `ℙⁿ_S ⟶ S` is proper.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceZ` is the integral model of projective `n`-space, placed
  in the universe of the base scheme.
* `AlgebraicGeometry.ProjectiveSpace` is projective `n`-space over a base scheme.
* `AlgebraicGeometry.ProjectiveSpace.toProjectiveSpaceZ` is the projection to the integral
  model.
* `AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv` identifies the coefficient ring of a
  polynomial ring with the degree-zero part of its total-degree grading.
* `AlgebraicGeometry.ProjectiveSpace.baseChangeIso` identifies `ℙⁿ_T ×_T S` with `ℙⁿ_S`.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.isProper_terminal_from` states that the integral model of
  projective space is proper over the terminal scheme.
* `AlgebraicGeometry.ProjectiveSpace.instIsProperOver` states that `ℙⁿ_S ⟶ S` is proper.

## Implementation notes

`ProjectiveSpace n S` is by construction the pullback of `terminal.from S` along
`terminal.from (ProjectiveSpaceZ n)`, which is the same shape as Mathlib's
`AlgebraicGeometry.AffineSpace`. Variables are indexed by `Fin (n + 1)`, so that
`ProjectiveSpace n S` is projective space of dimension `n`.

The total-degree grading `MvPolynomial.gradedAlgebra` is not a global instance in Mathlib, so
it is installed here as a `local instance`; the definitions below therefore do not export it to
importing files, and `ProjectiveSpaceZ n` is definitionally the corresponding `Proj`.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The integral model of projective `n`-space, in the universe of the base scheme: `Proj` of
the polynomial ring in `n + 1` variables over `ULift ℤ`, graded by total degree. -/
def ProjectiveSpaceZ (n : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))

/-- Projective `n`-space over a scheme `S`, defined as the base change of the integral model
`ProjectiveSpaceZ n` along `S ⟶ Spec ℤ`, with `Spec ℤ` realised as the terminal scheme. -/
def ProjectiveSpace (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n))

namespace ProjectiveSpace

section GradeZero

variable (σ : Type*) (R : Type u) [CommRing R]

/-- The degree-zero part of a polynomial ring is an algebra over the coefficient ring,
compatibly with the polynomial ring itself. -/
instance : IsScalarTower R (MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  ⟨fun x y z ↦ by
    change ((x • y : MvPolynomial.homogeneousSubmodule σ R 0) : MvPolynomial σ R) * z = _
    rw [Submodule.coe_smul]
    exact smul_mul_assoc x _ z⟩

/-- A polynomial ring in finitely many variables is of finite type over the degree-zero part of
its total-degree grading. -/
instance [Finite σ] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

/-- The coefficient ring of a polynomial ring is the degree-zero part of its total-degree
grading: a polynomial is homogeneous of degree zero exactly when it is a constant. -/
def gradeZeroEquiv : R ≃+* (MvPolynomial.homogeneousSubmodule σ R 0) :=
  RingEquiv.ofBijective (algebraMap R (MvPolynomial.homogeneousSubmodule σ R 0)) <| by
    refine ⟨fun a b hab ↦ MvPolynomial.C_injective σ R ?_, ?_⟩
    · simpa [SetLike.GradeZero.coe_algebraMap] using congrArg Subtype.val hab
    · rintro ⟨y, hy⟩
      rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_range] at hy
      obtain ⟨r, hr⟩ := hy
      exact ⟨r, Subtype.ext (by simpa [SetLike.GradeZero.coe_algebraMap] using hr)⟩

end GradeZero

variable (n : ℕ) (S : Scheme.{u})

/-- Projective space over `S` is canonically a scheme over `S`. -/
instance over : (ProjectiveSpace n S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The structure morphism of projective space over `S` is the first pullback projection. -/
lemma over_hom : (ProjectiveSpace n S ↘ S) =
    pullback.fst (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n)) :=
  rfl

/-- The projection from projective space over `S` to the integral model. -/
def toProjectiveSpaceZ : ProjectiveSpace n S ⟶ ProjectiveSpaceZ.{u} n :=
  pullback.snd _ _

/-- `Spec` of the degree-zero part of `ULift ℤ[X₀, …, Xₙ]` is a terminal scheme, because that
degree-zero part is `ULift ℤ`. -/
def specGradeZeroIsTerminal :
    IsTerminal (Spec (.of (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0))) :=
  specULiftZIsTerminal.ofIso
    (asIso (Spec.map (gradeZeroEquiv (Fin (n + 1)) (ULift.{u} ℤ)).toCommRingCatIso.hom)).symm

/-- **Projective space is proper over the integers.** The integral model of projective
`n`-space is proper over the terminal scheme. -/
theorem isProper_terminal_from : IsProper (terminal.from (ProjectiveSpaceZ.{u} n)) := by
  show IsProper (terminal.from
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))))
  rw [terminal.hom_ext (terminal.from _) (Proj.toSpecZero _ ≫
      ((specGradeZeroIsTerminal n).uniqueUpToIso terminalIsTerminal).hom),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

/-- **Projective space is proper over its base.** The structure morphism `ℙⁿ_S ⟶ S` is proper,
being the base change of `ℙⁿ_ℤ ⟶ Spec ℤ`. -/
instance instIsProperOver : IsProper (ProjectiveSpace n S ↘ S) := by
  rw [over_hom]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n))).flip
    (isProper_terminal_from n)

/-- Projective space over a quasi-compact base is quasi-compact. -/
instance [CompactSpace S] : CompactSpace (ProjectiveSpace n S) :=
  QuasiCompact.compactSpace_of_compactSpace (ProjectiveSpace n S ↘ S)

/-- Projective space over `T`, base changed along `g : S ⟶ T`, is projective space over `S`. -/
def baseChangeIso {S T : Scheme.{u}} (g : S ⟶ T) :
    pullback (ProjectiveSpace n T ↘ T) g ≅ ProjectiveSpace n S :=
  (pullbackSymmetry (pullback.fst (terminal.from T)
      (terminal.from (ProjectiveSpaceZ.{u} n))) g).trans
    ((pullbackRightPullbackFstIso
        (terminal.from T) (terminal.from (ProjectiveSpaceZ.{u} n)) g).trans
      (pullback.congrHom (terminal.comp_from g) rfl))

/-- The identification `ℙⁿ_T ×_T S ≅ ℙⁿ_S` is compatible with the two structure morphisms
down to `S`. -/
theorem baseChangeIso_hom_over {S T : Scheme.{u}} (g : S ⟶ T) :
    (baseChangeIso n g).hom ≫ (ProjectiveSpace n S ↘ S) =
      pullback.snd (ProjectiveSpace n T ↘ T) g := by
  show ((pullbackSymmetry (pullback.fst (terminal.from T)
      (terminal.from (ProjectiveSpaceZ.{u} n))) g).hom ≫
    (pullbackRightPullbackFstIso
      (terminal.from T) (terminal.from (ProjectiveSpaceZ.{u} n)) g).hom ≫
    (pullback.congrHom (terminal.comp_from g) rfl).hom) ≫
      pullback.fst (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n)) =
    pullback.snd (pullback.fst (terminal.from T)
      (terminal.from (ProjectiveSpaceZ.{u} n))) g
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_fst]

end ProjectiveSpace

end AlgebraicGeometry

end

end
