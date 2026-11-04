module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.GlobalTop
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.LocalTower
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.LocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Unconditional
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero

/-!
# The projective space bundle formula

Let `(S, δ)` be a base situation of chapter 42, `X` locally of finite type over `S`, `ℰ` a finite
locally free `𝒪_X`-module of rank `n + 1` and `(π : P ⟶ X, 𝒪_P(1))` the projective bundle of `ℰ`.
Then:

* `π_*(c₁(𝒪_P(1))^s ∩ π^*α) = 0` for `s < n` and `= α` for `s = n`;
* the map `⨁_{i = 0}^{n} A_{k + i}(X) ⟶ A_{k + n}(P)`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`, is an
  isomorphism.

## Main results

* `Stacks.Chow.projectiveBundle_projection`: `π_*(c₁(𝒪_P(1))^s ∩ π^*α)` is `0` for `s < n` and `α`
  for `s = n`, with the two cases `Stacks.Chow.projectiveBundle_projection_eq_zero_of_lt` and
  `Stacks.Chow.projectiveBundle_projection_self`.
* `Stacks.Chow.projectiveBundle_formula`: the projective space bundle formula.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
  Stacks.SymGraded

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- The projection of the projective bundle of a module of rank `n + 1` is flat. -/
theorem flat_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    Flat (bundleProj E) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  Stacks.ProjectiveBundle.flat_toBase E (bundlePieces E) n

/-- The projection of the projective bundle of a module of rank `n + 1` is locally of finite
type. -/
theorem locallyOfFiniteType_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    LocallyOfFiniteType (bundleProj E) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  Stacks.ProjectiveBundle.locallyOfFiniteType_toBase E (bundlePieces E) n

/-- The projection of the projective bundle of a module of rank `n + 1` has relative dimension
`n`. -/
theorem relativeDimension_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := locallyOfFiniteType_bundleProj E n
    AlgebraicGeometry.RelativeDimension (bundleProj E) n :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  Stacks.ProjectiveBundle.relativeDimension_toBase E (bundlePieces E) n

/-- The projective bundle of the free module `freeModule (coordIndex n)` over a scheme `U`, with
its tautological twist, is a projective tower, for every scheme `U`. -/
def FreeBundleIsTower (n : ℕ) : Prop :=
  ∀ U : Scheme.{u}, IsProjectiveTower n
    (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
      (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist (freeModule (X := U) (coordIndex.{u} n))
      (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))

/-- The projective bundle of a free module, with its twist, is a projective tower over every
base. -/
theorem freeBundleIsTower : FreeBundleIsTower.{u} n :=
  fun U ↦ isProjectiveTower_freeModule U n

/-- The projective bundle of a module of rank `n + 1`, with its twist, is a projective tower
locally on the base. -/
theorem isLocallyProjectiveTower_bundle :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    IsLocallyProjectiveTower n (bundleProj E) (bundleTwist E) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  Stacks.ProjectiveBundle.isLocallyProjectiveTower_of_free n (freeBundleIsTower n) E
    (bundlePieces E)

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- For the projective bundle of a module of rank `n + 1`, an integer `s < n` and `α ∈ A_k(X)`,
`π_*(c₁(𝒪_P(1))^s ∩ π^*α) = 0`. -/
theorem projectiveBundle_projection_eq_zero_of_lt (s : ℕ) (hs : s < n) (k m : ℤ)
    (h : k + n = m + s) (α : chowGroup C sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    bundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
        (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) s k m
        h α = 0 :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  bundleProjection_eq_zero_of_lt C sX _ _ rfl n _ _ s hs k m h α

/-- For the projective bundle of a module of rank `n + 1` and `α ∈ A_k(X)`,
`π_*(c₁(𝒪_P(1))^n ∩ π^*α) = α`. -/
theorem projectiveBundle_projection_self (k : ℤ)
    (α : chowGroup C sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    bundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
        (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) n k k
        (by ring) α = α :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  (isLocallyProjectiveTower_bundle E n).bundleProjection_self C sX _ rfl _ k α

/-- Flat pullback along an affine space bundle is surjective on Chow groups (Stacks 02TT), in the
form `Stacks.Chow.AffineBundleSurjectivity`. -/
theorem affineBundleSurjectivity (C : ChowSituation.{u}) : AffineBundleSurjectivity C :=
  fun sA _ sB _ f _ _ hf r hr hb k ↦
    flatPullbackChow_surjective_of_isAffineSpaceBundle_general C sA sB f hf r hr hb k

/-- For the projective bundle `π : P ⟶ X` of a module of rank `n + 1`, `α ∈ A_k(X)` and `s ≤ n`,
the class `π_*(c₁(𝒪_P(1))^s ∩ π^*α) ∈ A_{k+n-s}(X)` is `0` if `s < n` and is `α` if `s = n`. -/
@[stacks 02TW]
theorem projectiveBundle_projection (s : ℕ) (hs : s ≤ n) (k m : ℤ) (h : k + n = m + s)
    (α : chowGroup C sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    bundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
        (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) s k m
        h α =
      if hsn : s = n then chowGroupCast C sX (by subst hsn; omega) α else 0 := by
  split_ifs with hsn
  · subst hsn
    obtain rfl : k = m := by omega
    exact projectiveBundle_projection_self E s C sX k α
  · exact projectiveBundle_projection_eq_zero_of_lt E n C sX s (by omega) k m h α

/-- The projective space bundle formula for the projective bundle of a module of rank `n + 1`: the
map `⨁_{i ≤ n} A_{k+i}(X) ⟶ A_{k+n}(P)`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`, is bijective. -/
@[stacks 02TX]
theorem projectiveBundle_formula (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    Function.Bijective (bundleMap C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
      (relativeDimension_bundleProj E n) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) k) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  ⟨(isLocallyProjectiveTower_bundle E n).bundleMap_injective C sX _ rfl _ k,
    (isLocallyProjectiveTower_bundle E n).bundleMap_surjective C
      (affineBundleSurjectivity C) sX _ rfl _ k⟩

end Stacks.Chow

end
