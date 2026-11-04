module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGrading
public import StacksCore.Tactic.StacksAttribute

/-!
# The blowup of an affine scheme

The blowup of a scheme `X` in a quasi-coherent sheaf of ideals `ℐ` is the relative `Proj` of
the Rees algebra `⨁_{n ≥ 0} ℐⁿ`. Over an affine open `Spec A` with `ℐ|_U` corresponding to an
ideal `I ⊆ A`, that relative `Proj` is the ordinary `Proj` of the Rees algebra of `I`, by Stacks
tag 0804. This file constructs that affine model: `Stacks.Blowup.blowUpSpec I` is `Proj` of the
grading `Stacks.Blowup.reesGrading I` of `reesAlgebra I`, together with its structure morphism to
`Spec R`.

## Main definitions

* `Stacks.Blowup.blowUpSpec` is the blowup of `Spec R` in the ideal `I`.
* `Stacks.Blowup.toSpec` is its structure morphism to `Spec R`.

## Main results

* `Stacks.Blowup.instIsSeparatedToSpec`: the blowup of an affine scheme is separated over its
  base, with no finiteness hypothesis.
* `Stacks.Blowup.instIsProperToSpec`: the blowup of a Noetherian affine scheme is proper over
  its base.

## Implementation notes

`Proj.toSpecZero` lands in `Spec` of the degree-zero part of the grading, which for the Rees
algebra is a copy of `R` rather than `R` on the nose; `toSpec` composes it with `Spec` of the
identification `Stacks.Blowup.reesGradingZeroEquiv`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/


@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace Stacks.Blowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The blowup of the affine scheme `Spec R` in the ideal `I`: the homogeneous spectrum of the
Rees algebra `⨁_{n ≥ 0} Iⁿ`, graded as in `Stacks.Blowup.reesGrading`. -/
@[sga "7 XV 2.1.1" "partial"]
def blowUpSpec : Scheme.{u} := Proj (reesGrading I)

/-- The degree-zero part of the Rees algebra is an `R`-algebra, compatibly with the Rees algebra
itself. -/
instance instIsScalarTowerReesGradingZero :
    IsScalarTower R (reesGrading I 0) (reesAlgebra I) :=
  ⟨fun x y z ↦ by
    change ((x • y : reesGrading I 0) : reesAlgebra I) * z = _
    rw [Submodule.coe_smul]
    exact smul_mul_assoc x _ z⟩

/-- When `R` is Noetherian the Rees algebra is of finite type over the degree-zero part of its
grading. -/
instance instFiniteTypeReesGradingZero [IsNoetherianRing R] :
    Algebra.FiniteType (reesGrading I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

/-- The structure morphism of the blowup of `Spec R` in `I`. It is `Proj.toSpecZero` followed by
`Spec` of the identification of the degree-zero part of the Rees algebra with `R`. -/
def toSpec : blowUpSpec I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (reesGrading I) ≫
    Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom)

/-- The blowup of `Spec R` in `I` is canonically a scheme over `Spec R`. -/
instance over : (blowUpSpec I).CanonicallyOver (Spec (CommRingCat.of R)) where
  hom := toSpec I

/-- `Spec` of the identification of `R` with the degree-zero part of the Rees algebra is an
isomorphism. -/
instance instIsIsoSpecMapReesGradingZeroEquiv :
    IsIso (Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom)) :=
  inferInstanceAs
    (IsIso (Spec.map (reesGradingZeroEquiv I).toCommRingCatIso.hom))

/-- **The blowup of an affine scheme is separated over its base.** No finiteness hypothesis is
needed: `Proj 𝒜 ⟶ Spec 𝒜₀` is separated for every grading. -/
instance instIsSeparatedToSpec : IsSeparated (toSpec I) := by
  change IsSeparated (Proj.toSpecZero (reesGrading I) ≫
    Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom))
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsSeparated)]
  infer_instance

/-- **The blowup of a Noetherian affine scheme is proper over its base.** -/
instance instIsProperToSpec [IsNoetherianRing R] : IsProper (toSpec I) := by
  change IsProper (Proj.toSpecZero (reesGrading I) ≫
    Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom))
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

/-- The blowup of a Noetherian affine scheme is quasi-compact. -/
instance [IsNoetherianRing R] : CompactSpace (blowUpSpec I) :=
  QuasiCompact.compactSpace_of_compactSpace (toSpec I)

end Stacks.Blowup

end
