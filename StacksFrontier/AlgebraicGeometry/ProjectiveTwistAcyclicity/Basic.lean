module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSerreDevissage.TwistTransport
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Serre vanishing for the twists of `𝒪_{ℙⁿ_W}` over an affine base

For `W` an affine scheme, `n : ℕ`, `d ≥ 0` and `p > 0`,

`H ᵖ(ℙⁿ_W, 𝒪(d)) = 0`,

and the same with `𝒪(d)` written as the `d`-th tensor power of the hyperplane sheaf `𝒪(1)`. No
Noetherian hypothesis on `W` is needed.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.isZero_Hgroup_twistOver_of_isAffine`:
  `H ᵖ(ℙⁿ_W, 𝒪(d)) = 0` for `W` affine, `d ≥ 0` and `p > 0`.
* `Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.isZero_Hgroup_tensorPowModule`: the same
  with the twist spelled as a tensor power of `𝒪(1)`.
* `Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.twistAcyclicity_projectiveSpace`: the
  conclusion of
  `Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase` at the pair
  `(ℙⁿ_W, 𝒪(1))`.

## Implementation notes

Over `Spec (CommRingCat.of S)`, `twistOver n (Spec (CommRingCat.of S)) d` is
`projectiveTwistingSheaf n d` by definition.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open Stacks.AmpleProjectiveImmersion

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity

attribute [local instance] HasDerivedCategory.standard

/-! ### The base-change model over a ring -/

/-- **`H ᵖ(ℙⁿ_R, 𝒪(d)) = 0` for `d ≥ 0` and `p > 0`**, on the base-change model
`AlgebraicGeometry.projectiveSpaceOverRing`, over an arbitrary commutative ring. -/
@[sga "6 III 2.2.2" "special case"]
theorem isZero_Hgroup_twistOver_specOf (S : Type u) [CommRing S] (n : ℕ) (d : ℤ) (hd : 0 ≤ d)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of S)).ringCatSheaf ⊤ p
      (twistOver n (Spec (CommRingCat.of S)) d)) := by
  have hz0 :=
    Stacks.ProjectiveSpace.SerreVanishing.isZero_Hgroup_twistingSheaf_of_pos S n d hd p hp
  have hz := (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff (projModelIso S n).symm
    (twistingSheaf (polyGrading S n) d) p).2 hz0
  obtain ⟨e⟩ := nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv S n d
    (Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport S n d)
  exact hz.of_iso
    ((Hfunctor (projectiveSpaceOverRing n (CommRingCat.of S)).ringCatSheaf ⊤ p).mapIso e)

/-! ### An arbitrary affine base -/

/-- The morphism of projective spaces induced by an isomorphism of bases is an isomorphism. -/
instance isIso_projectiveSpaceOverMap (n : ℕ) {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] :
    IsIso (projectiveSpaceOverMap n g) :=
  (isPullback_projectiveSpaceOverMap n g).isIso_fst_of_isIso

/-- **`H ᵖ(ℙⁿ_W, 𝒪(d)) = 0` for `W` affine, `d ≥ 0` and `p > 0`.** -/
theorem isZero_Hgroup_twistOver_of_isAffine (n : ℕ) (W : Scheme.{u}) [IsAffine W] (d : ℤ)
    (hd : 0 ≤ d) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup (projectiveSpaceOver n W).ringCatSheaf ⊤ p (twistOver n W d)) := by
  let eP : projectiveSpaceOver n (Spec (CommRingCat.of ↥(Γ(W, ⊤)))) ≅ projectiveSpaceOver n W :=
    asIso (projectiveSpaceOverMap n W.isoSpec.inv)
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff eP (twistOver n W d) p).1 ?_
  refine (isZero_Hgroup_twistOver_specOf ↥(Γ(W, ⊤)) n d hd p hp).of_iso ?_
  exact (Hfunctor
      (projectiveSpaceOver n (Spec (CommRingCat.of ↥(Γ(W, ⊤))))).ringCatSheaf ⊤ p).mapIso
    (twistOverPullbackIso n W.isoSpec.inv d)

/-! ### The tensor-power spelling -/

/-- **`H ᵖ(ℙⁿ_W, 𝒪(1) ^⊗ m) = 0` for `W` affine, `m : ℕ` and `p > 0`.** -/
theorem isZero_Hgroup_tensorPowModule (n : ℕ) (W : Scheme.{u}) [IsAffine W] (m : ℕ) (p : ℕ)
    (hp : 0 < p) :
    IsZero (Hgroup (projectiveSpaceOver n W).ringCatSheaf ⊤ p
      (Stacks.Ample.tensorPowModule (projectiveSpaceOver n W)
        (projectiveSpaceTwistingSheaf n W) (m : ℤ))) :=
  (isZero_Hgroup_twistOver_of_isAffine n W (m : ℤ) (Int.natCast_nonneg m) p hp).of_iso
    ((Hfunctor (projectiveSpaceOver n W).ringCatSheaf ⊤ p).mapIso
      (tensorPowModuleProjectiveTwistIso n W (m : ℤ)))

/-- **The twist-acyclicity hypothesis of
`Stacks.AlgebraicGeometry.RelativeSerreVanishing.TwistAcyclicityOverAffineBase` at the pair
`(ℙⁿ_W, 𝒪(1))`**, for `W` affine, with bound `0`. -/
@[sga "6 III 2.2.2" "special case"]
theorem twistAcyclicity_projectiveSpace (n : ℕ) (W : Scheme.{u}) [IsAffine W] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ p : ℕ, 0 < p →
      IsZero (Hgroup (projectiveSpaceOver n W).ringCatSheaf ⊤ p
        (Stacks.Ample.tensorPowModule (projectiveSpaceOver n W)
          (projectiveSpaceTwistingSheaf n W) (m : ℤ))) :=
  ⟨0, fun m _ p hp => isZero_Hgroup_tensorPowModule n W m p hp⟩

end Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity

end
