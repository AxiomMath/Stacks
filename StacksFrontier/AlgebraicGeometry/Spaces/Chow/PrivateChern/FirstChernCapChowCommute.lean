module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IteratedFirstChernCapCommutativity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne

/-!
# The cap products with two first Chern classes commute on Chow homology

In Situation 0EDT let `X/B` be good and let `ℒ`, `𝒩` be invertible `𝒪_X`-modules. By Stacks 0EQZ
(`AlgebraicGeometry.Space.canonicalFirstChernCap_firstChernCapCycleMap_comm`, on representatives)
the operations `c₁(ℒ) ∩ -` and `c₁(𝒩) ∩ -` on the Chow homology `CH_*(X) = ⨁_k CH_k(X)` commute.
As a consequence the first Chern classes of Stacks 0ERZ of two modules of rank one commute.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_commute`: the two operations on
  `CH_*(X)` commute.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_one_commute`: the first Chern classes of two
  modules of rank one commute.

## References

* [Stacks Project, Tag 0EQZ](https://stacks.math.columbia.edu/tag/0EQZ)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The cap products with the first Chern classes of two invertible modules commute as operations
on `CH_*(X)`. -/
theorem firstChernCapChow_commute (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N) :
    @Commute (AddMonoid.End (chowHomology.{u, u + 1} D sX hX)) _
      (firstChernCapChow.{u, u + 1} D sX hX L hL) (firstChernCapChow.{u, u + 1} D sX hX N hN) := by
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 1 - 1, by ring⟩
  change firstChernCapChow.{u, u + 1} D sX hX L hL (firstChernCapChow.{u, u + 1} D sX hX N hN
      (DirectSum.of _ (j + 1 + 1) (chowClass.{u + 1} D sX hX _ b))) =
    firstChernCapChow.{u, u + 1} D sX hX N hN (firstChernCapChow.{u, u + 1} D sX hX L hL
      (DirectSum.of _ (j + 1 + 1) (chowClass.{u + 1} D sX hX _ b)))
  simp only [firstChernCapChow_of_chowClass]
  exact congrArg _
    (canonicalFirstChernCap_firstChernCapCycleMap_comm.{u + 1, u} D sX hX L hL N hN j b)

/-- **The first Chern classes of two modules of rank one commute**, the first Chern classes being
those of Stacks 0ERZ. -/
theorem chernCap_one_commute {P : D.Ambient} {sP : P ⟶ D.space} (hP : D.IsGood sP)
    (L M : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsFiniteLocallyFreeOfRank D sP hP L 1) (hM : IsFiniteLocallyFreeOfRank D sP hP M 1) :
    Commute (chernCap.{u, u + 1} (hX := hP) L 1 hL 1)
      (chernCap.{u, u + 1} (hX := hP) M 1 hM 1) := by
  have hL' := (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := goodSpace hP) L).2 hL
  have hM' := (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one (Z := goodSpace hP) M).2 hM
  rw [chernCap_one_eq_firstChernCapChow _ hL hL', chernCap_one_eq_firstChernCapChow _ hM hM']
  exact firstChernCapChow_commute D sP hP L M hL' hM'

end AlgebraicGeometry.Space.PrivateChern

end
