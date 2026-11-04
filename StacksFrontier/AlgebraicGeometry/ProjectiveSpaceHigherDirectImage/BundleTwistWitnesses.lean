module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BundleTwistVanishing
public import
  StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeTwistIdentification

/-!
# Non-vacuity of the higher direct images of the twists on a projective bundle

Two statements about the twists on a projective bundle and on projective space —
`Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.isZero_rightDerivedPlus_pushforward_twist`
for the vanishing degrees, and
`Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.TopDegree.topCohomologyTwistIsoSymTensorDet`
for the `q = n` identification — are each quantified over data whose existence is not part of
either statement. This module exhibits that data and shows that neither statement is discharged
by both of its sides being zero.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.Witness`
  `.isFiniteLocallyFreeOfRank_freeModule`: **`𝒪_S^{⊕ r}` is finite locally free of rank `r`** in
  the sense of `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`, the hypothesis the
  vanishing statement binds.
* `…Witness.isZero_rightDerivedPlus_pushforward_twist_freeModule`: the vanishing statement with
  every one of its hypotheses supplied, at `ℰ = 𝒪_S^{n+1}` over an arbitrary scheme `S`.
* `…Witness.not_isZero_symTensorDetDual_projectiveLine`: **the target of the `q = n`
  identification is nonzero** at `R = ℚ`, `n = 1`, `d = -2`. So that identification is not a
  comparison of two zero objects.
* `…Witness.not_forall_isZero_twistCohomology_of_ne_zero`: **the vanishing row of
  [Stacks, Tag 01XX] is false at `q = n`**, so the hypothesis `q < 0 ∨ n < q` of the vanishing
  statement cannot be weakened to the source's `q ≠ 0` alone. The source's row is `0` for
  `q ≠ 0, n`, and `n` is genuinely excluded.

## Implementation notes

`not_forall_isZero_twistCohomology_of_ne_zero` is stated at the level of
`Stacks.ProjectiveSpace.Cohomology.twistCohomology`, the cohomology module of the twist on the
homogeneous-spectrum model, rather than at the level of `R^q π_*` on a projective bundle: the
nonvanishing input `AlgebraicGeometry.not_isZero_twistCohomology_top` lives there.

## References

* [Stacks Project, Tag 01XX](https://stacks.math.columbia.edu/tag/01XX)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.Witness

@[expose] public noncomputable section

/-! ### The hypotheses of the vanishing statement are inhabited -/

/-- **The free module sheaf of rank `r` on a scheme is finite locally free of rank `r`.** -/
public theorem isFiniteLocallyFreeOfRank_freeModule (S : Scheme.{u}) (r : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank
      (Stacks.SymGraded.freeModule (X := S) (ULift.{u} (Fin r))) r := fun _ =>
  ⟨⊤, trivial, ⟨(Scheme.Modules.restrictFreeIso (⊤ : S.Opens).ι (ULift.{u} (Fin r))).symm⟩⟩

/-- **The vanishing clause of [Stacks, Tag 01XX] with every hypothesis supplied**, at
`ℰ = 𝒪_S^{n+1}` over an arbitrary scheme, with the glued twists given by the existence assertion of
[Stacks, Tag 01NR], `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`. -/
public theorem isZero_rightDerivedPlus_pushforward_twist_freeModule (S : Scheme.{u}) (n : ℕ)
    (d : ℤ) (q : ℤ) (hq : q < 0 ∨ (n : ℤ) < q) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.freeSymGradedAlgebra
          (X := S) (ULift.{u} (Fin (n + 1))))).toBase).rightDerivedPlus q).obj
      ((Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra
        (Stacks.SymGraded.freeSymGradedAlgebra
          (X := S) (ULift.{u} (Fin (n + 1))))).algebra.piece d)) :=
  Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.isZero_rightDerivedPlus_pushforward_twist
    (Stacks.SymGraded.freeModule (X := S) (ULift.{u} (Fin (n + 1)))) n
    (Stacks.SymGraded.isQuasicoherentPieces_free _) (isFiniteLocallyFreeOfRank_freeModule S (n + 1))
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _) d q hq

/-! ### The `q = n` identification is not a comparison of two zero objects -/

/-- **The `q = n` identification of [Stacks, Tag 01XX] at `R = ℚ`, `n = 1`, `d = -2`**, with
every binder of
`…ProjectiveBundleVanishing.TopDegree.topCohomologyTwistIsoSymTensorDet` filled by a closed
term: `m = 0`, so `n = m + 1 = 1`; `d = -2 = -n - 1`; and `k = 0 = -n - 1 - d`. -/
public def topCohomologyTwistIsoSymTensorDet_projectiveLine :
    Stacks.ProjectiveSpace.Cohomology.twistCohomology ℚ (0 + 1) (-(1 + 1 : ℤ)) (0 + 1) ≅
      ModuleCat.of ℚ
        (TensorProduct ℚ (SymPow.symmetricPower 0 ℚ (Fin (0 + 1 + 1) → ℚ))
            (⋀[ℚ]^(0 + 1 + 1) (Fin (0 + 1 + 1) → ℚ)) →ₗ[ℚ] ℚ) :=
  TopDegree.topCohomologyTwistIsoSymTensorDet ℚ 0 (-(1 + 1 : ℤ)) 0 (by push_cast)

/-- **The right-hand side of the `q = n` identification is nonzero** at `R = ℚ`, `n = 1`,
`d = -2`: `Hom_ℚ(Sym⁰(ℚ²) ⊗ ⋀²(ℚ²), ℚ) ≠ 0`. -/
public theorem not_isZero_symTensorDetDual_projectiveLine :
    ¬ IsZero (ModuleCat.of ℚ
        (TensorProduct ℚ (SymPow.symmetricPower 0 ℚ (Fin (0 + 1 + 1) → ℚ))
            (⋀[ℚ]^(0 + 1 + 1) (Fin (0 + 1 + 1) → ℚ)) →ₗ[ℚ] ℚ)) := fun h =>
  AlgebraicGeometry.not_isZero_twistCohomology_top ℚ 1
    (topCohomologyTwistIsoSymTensorDet_projectiveLine.isZero_iff.2 h)

/-! ### The degree `q = n` is genuinely excluded from the vanishing row -/

/-- **The vanishing row of [Stacks, Tag 01XX] fails at `q = n`**: it is not the case that
`Hᵠ(ℙⁿ_R, 𝒪(d)) = 0` on the homogeneous-spectrum model for every commutative ring `R`, every `n`,
every `d` and every `q ≠ 0`. -/
public theorem not_forall_isZero_twistCohomology_of_ne_zero :
    ¬ ∀ (R : Type) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ), q ≠ 0 →
        IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology R n d q) := fun h =>
  AlgebraicGeometry.not_isZero_twistCohomology_top ℚ 1 (h ℚ 1 (-(1 + 1 : ℤ)) 1 one_ne_zero)

end

end Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.Witness
