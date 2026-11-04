module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundlePullbackTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClassesFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingInduction

/-!
# Chern classes commute with flat pullback

In Situation 0EDT let `π : P ⟶ Z` be a flat morphism of relative dimension `d` between good
algebraic spaces and `ℳ` a finite locally free `𝒪_Z`-module of rank `r`. Then
`c_n(π^*ℳ) ∩ π^*α = π^*(c_n(ℳ) ∩ α)` for `α ∈ CH_*(Z)`: the Chern classes of Stacks 0ERZ commute
with flat pullback, which is the part of their bivariance (Stacks 0ERY) concerning flat pullback.

For `r = 0` both sides are the Chern classes of zero Segre operations. For `r = d' + 1` the
projective bundle `𝐏(π^*ℳ)` is the base change `P ×_Z 𝐏(ℳ)`
(`AlgebraicGeometry.Space.PrivateChern.isPullback_projectiveBundleSpacePullback`) by a
comparison pulling `𝒪_{𝐏(ℳ)}(1)` back to `𝒪_{𝐏(π^*ℳ)}(1)`
(`AlgebraicGeometry.Space.PrivateChern.exists_iso_projectiveBundlePullbackMap_twist`), so flat
base change of the Segre operations applies
(`AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.chernCap_flatPullbackChow`).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_spaceModulePullback_flatPullbackChow`: the Chern
  classes commute with flat pullback.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local irreducible] AlgebraicGeometry.Space.modulePullback
  Stacks.RelativeProj.symmetricSituationOfQuasicoherent
  Stacks.RelativeProj.symmetricSituation
  Stacks.RelativeProj.Situation.relativeProj
  Stacks.RelativeProj.Data.relativeProj
  SheafOfModules.sheafifiedSymmetricAlgebra
  presheafToSheaf
  Stacks.RelativeProj.Situation.relativeProjToBase
  Stacks.RelativeProj.Data.toBase
  AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace
  AlgebraicGeometry.Space.presentationOfAtlas
  AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison
  AlgebraicGeometry.Space.modulePullbackCompIso

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **The Chern classes commute with flat pullback**: for `π : P ⟶ Z` flat of relative dimension
`d` between good spaces and `ℳ` finite locally free of rank `r` on `Z`,
`c_n(π^*ℳ) ∩ π^*α = π^*(c_n(ℳ) ∩ α)`. -/
theorem chernCap_spaceModulePullback_flatPullbackChow {Z P : D.Ambient} {sZ : Z ⟶ D.space}
    {sP : P ⟶ D.space} (hZ : D.IsGood sZ) (hP : D.IsGood sP) (π : P ⟶ Z) (hπ : π ≫ sZ = sP)
    (d : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π)
    (M : Modules.{u, u} D.site D.base D.base_mem Z hZ.1) (r : ℕ)
    (hM : IsFiniteLocallyFreeOfRank D sZ hZ M r)
    (hM' : IsFiniteLocallyFreeOfRank D sP hP ((spaceModulePullback D hZ.1 hP.1 π).obj M) r)
    (n : ℕ) (α : chowHomology.{u, u + 1} D sZ hZ) :
    chernCap.{u, u + 1} (hX := hP) ((spaceModulePullback D hZ.1 hP.1 π).obj M) r hM' n
        (flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd α) =
      flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd
        (chernCap.{u, u + 1} (hX := hZ) M r hM n α) := by
  cases r with
  | zero =>
    exact (map_chernSeq_of_intertwines (flatPullbackChow.{u, u + 1} D sP hP sZ hZ π hπ d hflat hd)
      (t := fun _ => 0) (t' := fun _ => 0) (fun i x => by simp) n α).symm
  | succ e =>
    let := isQuasicoherentOnSite_of_rank M hM
    have hfree := isFiniteLocallyFreeOnSite_of_rank M hM
    obtain ⟨θ, -⟩ := exists_iso_projectiveBundlePullbackMap_twist
      (ObjectProperty.homMk π : goodSpace hP ⟶ goodSpace hZ) M hfree
    exact ProjectiveBundleDatum.chernCap_flatPullbackChow (projectiveBundleDatum M e hM)
      (projectiveBundleDatum _ e hM') hπ d hflat hd
      (isPullback_projectiveBundleSpacePullback
        (ObjectProperty.homMk π : goodSpace hP ⟶ goodSpace hZ) M hfree) θ n α

end AlgebraicGeometry.Space.PrivateChern

end
