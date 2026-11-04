module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineRestrictTwist
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat

/-!
# The projective bundle of a locally free module is locally a projective tower

Let `ℰ` be a module on a scheme `X`, finite locally free of constant rank `n + 1`, and
`π : 𝐏(ℰ) ⟶ X` its projective bundle with the twist `𝒪(1)`. Every point of `X` has an affine
open neighbourhood `V` on which `ℰ` is free, and over `V` the bundle, with its twist, is
`𝐏(𝒪_V^{n+1})` with its twist (`Stacks.ProjectiveBundle.restrictBundleIso`). So if the bundle of
a free module of rank `n + 1`, with its twist, is a projective tower of fibre dimension `n` over
every base, then `π` with `𝒪(1)` is a projective tower locally on `X`.

## Main results

* `Stacks.ProjectiveBundle.restrictFreeOfLE`: a module free of rank `r` on an open is free of
  rank `r` on every smaller open.
* `Stacks.ProjectiveBundle.exists_affine_restrict_free`: every point has an affine open
  neighbourhood on which a module finite locally free of rank `r` is free of rank `r`.
* `Stacks.ProjectiveBundle.isLocallyProjectiveTower_of_free`: **the projective bundle of a
  module finite locally free of rank `n + 1`, with `𝒪(1)`, is a projective tower of fibre
  dimension `n` locally on the base**, given that the bundle of the free module of rank `n + 1`
  is one over every base.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundle

/-- **A module free of rank `r` on an open is free of rank `r` on every smaller open.** -/
def restrictFreeOfLE {X : Scheme.{u}} (E : X.Modules) {U V : X.Opens} (hVU : V ≤ U) (r : ℕ)
    (e : E.restrict U.ι ≅
      SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) :
    E.restrict V.ι ≅
      SheafOfModules.free.{u} (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVU).symm).app E ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hVU) U.ι).app E ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hVU)).mapIso e ≪≫
    (Scheme.Modules.restrictFreeIso (X.homOfLE hVU) (ULift.{u} (Fin r))).symm

/-- **Every point has an affine open neighbourhood on which a module finite locally free of rank
`r` is free of rank `r`.** -/
theorem exists_affine_restrict_free {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Nonempty (E.restrict V.ι ≅
      SheafOfModules.free.{u} (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ :=
    (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff E r).mpr hE x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  exact ⟨V, hV, hxV, ⟨restrictFreeOfLE E hVU r e⟩⟩

/-- **The projective bundle of a module finite locally free of rank `n + 1`, with its twist
`𝒪(1)`, is a projective tower of fibre dimension `n` locally on the base**, given that the
projective bundle of the free module of rank `n + 1`, with its twist, is a projective tower of
fibre dimension `n` over every base scheme.

Over an affine open `V` on which `ℰ` is free, `Stacks.ProjectiveBundle.restrictBundleIso`
identifies the part of `𝐏(ℰ)` lying over `V` with `𝐏(𝒪_V^{n+1})`, over `V` and compatibly with
the twists, and `Stacks.Chow.IsProjectiveTower.of_iso_left` transports the tower. -/
theorem isLocallyProjectiveTower_of_free (n : ℕ)
    (hfree : ∀ U : Scheme.{u}, Stacks.Chow.IsProjectiveTower n
      (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist
        (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))))
    {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    Stacks.Chow.IsLocallyProjectiveTower n (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  intro x
  obtain ⟨V, hV, hxV, ⟨e⟩⟩ := exists_affine_restrict_free E (n + 1) x
  refine ⟨V, hxV, ?_⟩
  let i := restrictBundleIso E hqc hV (freeModule (X := V.toScheme) (coordIndex.{u} n))
    (isQuasicoherentPieces_free (X := V.toScheme) (coordIndex.{u} n)) e
  refine (hfree V.toScheme).of_iso_left i.symm ?_ ?_
  · rw [Iso.symm_hom, Iso.inv_comp_eq,
      restrictBundleIso_hom_morphismRestrict]
  · exact (pullbackInvHomIso i _).symm ≪≫ (Scheme.Modules.pullback i.inv).mapIso
      (restrictBundleIsoTwistIso E hqc hV _ _ e)

end Stacks.ProjectiveBundle

end
