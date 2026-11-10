module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProperPushforwardChowComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Pushforward along the inclusion of a closed subspace on Chow homology

In Situation 0EDT let `X/B` be good and `i : Y → X` the inclusion of a closed subspace. The
proper pushforward `i_* : CH_*(Y) ⟶ CH_*(X)` is computed on cycles by the pushforward with which
rational equivalence is written, and it satisfies the projection formula for the cap product with
the first Chern class of an invertible `𝒪_X`-module `𝒩`:

  `c₁(𝒩) ∩ i_*β = i_*(c₁(𝒩|_Y) ∩ β)`   in `CH_*(X)`,

which is Stacks 0EQT for a closed immersion: the two cycles differ by an explicit locally finite
sum of principal divisors
(`exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum`, in
`AlgebraicGeometry.Space`).

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.closedSubspacePushforwardChow`: `i_*` on `CH_*`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.closedSubspacePushforwardChow_of_chowClass`:
  `i_*[β] = [i_*β]`.
* `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_closedSubspacePushforwardChow`: the
  projection formula.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
  (hX : D.IsGood sX) (Y : ClosedSubspaces D.site D.base D.base_mem X)

include hX in
/-- The inclusion of a closed subspace is proper (Stacks 04XZ). -/
theorem isProper_closedSubspace_ι : IsProper D.site D.base D.base_mem Y.1.ι :=
  isProper_of_isClosedImmersion D.site D.base D.base_mem Y.2.1 hX.1 Y.1.ι Y.2.2

/-- **The pushforward along the inclusion of a closed subspace on Chow homology.** -/
abbrev closedSubspacePushforwardChow :
    chowHomology.{u, u + 1} D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y) →+
      chowHomology.{u, u + 1} D sX hX :=
  properPushforwardChow.{u, u + 1} D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y) sX hX Y.1.ι
    rfl (isProper_closedSubspace_ι D sX hX Y)

/-- `i_*[β] = [i_*β]`, the pushforward of cycles being the one with which rational equivalence is
written. -/
theorem closedSubspacePushforwardChow_of_chowClass (k : ℤ)
    (b : CycleGroup D (Y.1.ι ≫ sX) k) :
    closedSubspacePushforwardChow D sX hX Y
        (DirectSum.of _ k (chowClass.{u + 1} D _ (isGood_closedSubspace D sX hX Y) k b)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k
        (chowClass.{u + 1} D sX hX k (closedSubspaceCyclePushforward D sX hX Y k b)) := by
  rw [closedSubspacePushforwardChow, properPushforwardChow_of, chowGroupProperPushforward_chowClass]
  congr 2
  exact properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sX hX Y.1 Y.2 k b

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
  (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **The projection formula along the inclusion of a closed subspace** (Stacks 0EQT for a closed
immersion): `c₁(𝒩) ∩ i_*β = i_*(c₁(𝒩|_Y) ∩ β)` in `CH_*(X)`. -/
theorem firstChernCapChow_closedSubspacePushforwardChow
    (β : chowHomology.{u, u + 1} D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)) :
    firstChernCapChow.{u, u + 1} D sX hX N hN (closedSubspacePushforwardChow D sX hX Y β) =
      closedSubspacePushforwardChow D sX hX Y
        (firstChernCapChow.{u, u + 1} D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
          (closedSubspaceModuleRestrict D sX hX N Y)
          (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
            N hN) β) := by
  change ((firstChernCapChow.{u, u + 1} D sX hX N hN).comp
      (closedSubspacePushforwardChow D sX hX Y)) β =
    ((closedSubspacePushforwardChow D sX hX Y).comp
      (firstChernCapChow.{u, u + 1} D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
        (closedSubspaceModuleRestrict D sX hX N Y)
        (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
          N hN))) β
  congr 1
  refine chowHomology_hom_ext D _ (isGood_closedSubspace D sX hX Y) fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, closedSubspacePushforwardChow_of_chowClass,
    firstChernCapChow_of_chowClass, firstChernCapChow_of_chowClass,
    closedSubspacePushforwardChow_of_chowClass]
  congr 1
  refine chowClass_eq_of_chowClassCanonical_eq D sX hX ?_
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  obtain ⟨hk, g, hsum⟩ :=
    exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum D sX hX Y N
      hN b
  refine ⟨_, _, locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX Y b, _,
    fun V => ?_, fun V => isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt D _ _ _
      (g V) (hk V), hsum⟩
  exact (deltaDimension_closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).trans (b.2.2 V.1 V.2)

end AlgebraicGeometry.Space.PrivateChern

end
