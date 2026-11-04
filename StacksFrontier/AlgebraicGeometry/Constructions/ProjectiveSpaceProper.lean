module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace

/-!
# Projective space is proper over its base

Projective `n`-space over a scheme `S` is proper over `S`, and absolutely separated as soon as
`S` is.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.isProper_terminalFrom_projectiveSpaceAtUniverse`: the integral model of
  projective space is proper over the terminal scheme.
* `AlgebraicGeometry.projectiveSpaceOver.isProper`: projective `n`-space over a scheme `S` is
  proper over `S`.
* `AlgebraicGeometry.projectiveSpaceOver.isSeparated`: projective `n`-space over a separated
  scheme is separated.

## Implementation notes

Mathlib proves that `AlgebraicGeometry.Proj.toSpecZero` is proper whenever the graded ring is of
finite type over its degree-zero part. For the polynomial ring `R[T₀, …, Tₙ]` graded by total
degree, the degree-zero part is the ring of constants, which the ring map from `R` identifies
with `R`: a homogeneous polynomial of degree zero is a constant, by
`MvPolynomial.totalDegree_eq_zero_iff_eq_C`. Finite type over the degree-zero part then follows
from finite type over `R` along that identification.

The terminal scheme is `Spec (ULift ℤ)` by `AlgebraicGeometry.specULiftZIsTerminal`, so the
structure morphism of the integral model to the terminal scheme agrees with `Proj.toSpecZero`
composed with an isomorphism, which gives properness of the integral model. Projective space
over `S` is the base change of the integral model along `S ⟶ ⊤_ Scheme`, and properness is
stable under base change.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The integral model of projective `n`-space is proper over the terminal scheme. -/
theorem isProper_terminalFrom_projectiveSpaceAtUniverse (n : ℕ) :
    IsProper (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  let R := ULift.{u} ℤ
  let A := MvPolynomial (Fin (n + 1)) R
  let 𝒜 : ℕ → Submodule R A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let : GradedAlgebra 𝒜 := MvPolynomial.gradedAlgebra
  let A₀ := 𝒜 0
  let e : R ≃+* A₀ := RingEquiv.ofBijective (algebraMap R A₀)
    ⟨fun r s hrs ↦ MvPolynomial.C_injective (Fin (n + 1)) R (congrArg Subtype.val hrs), by
      intro p
      have hp0 : p.val.totalDegree = 0 :=
        (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := Fin (n + 1))).2
          p.property
      exact ⟨MvPolynomial.coeff 0 p.val,
        Subtype.ext ((MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := p.val)).mp hp0).symm⟩⟩
  let : IsScalarTower R A₀ A :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A₀) (A := A) fun _ ↦ rfl
  let : Algebra.FiniteType A₀ A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R A₀ A
  let eSpec : Spec (.of A₀) ≅ ⊤_ Scheme :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op ≪≫
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal)
  have hbase : AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫ eSpec.hom =
      terminal.from (projectiveSpaceAtUniverse.{u} n) :=
    terminalIsTerminal.hom_ext _ _
  rw [← hbase]
  exact MorphismProperty.comp_mem @IsProper (AlgebraicGeometry.Proj.toSpecZero 𝒜) eSpec.hom
    inferInstance inferInstance

namespace projectiveSpaceOver

/-- Projective `n`-space over a scheme `S` is proper over `S`. In particular the structure
morphism `ℙⁿ_S ⟶ S` is universally closed, assertion (4) of Stacks 01NH. -/
@[stacks 01NH "universally closed"]
instance isProper (n : ℕ) (S : Scheme.{u}) : IsProper ((projectiveSpaceOver n S) ↘ S) :=
  IsProper.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip
    (isProper_terminalFrom_projectiveSpaceAtUniverse n)

/-- Projective `n`-space over a separated scheme is separated. The structure morphism to the
terminal scheme factors through `S`, and both factors are separated: the first because it is
proper, the second by hypothesis. -/
instance isSeparated (n : ℕ) (S : Scheme.{u}) [Scheme.IsSeparated S] :
    Scheme.IsSeparated (projectiveSpaceOver n S) := by
  refine ⟨?_⟩
  rw [show terminal.from (projectiveSpaceOver n S) =
      (projectiveSpaceOver n S ↘ S) ≫ terminal.from S from terminal.hom_ext _ _]
  infer_instance

end projectiveSpaceOver

end AlgebraicGeometry

end
