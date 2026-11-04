module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ClosedSubspaceChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RelativeEffectiveCartierFlatPullback

/-!
# The first Chern class of a relative effective Cartier divisor on Chow homology

In Situation 0EDT let `p : X ⟶ Y` be a flat morphism of good algebraic spaces of relative
dimension `r + 1`, `ℒ` an invertible `𝒪_X`-module with a global section `s` whose vanishing locus
`i : E = Z(s) → X` is a relative effective Cartier divisor on `X/Y`. Then on Chow homology

  `c₁(ℒ) ∩ p^*α = i_*((p|_E)^*α)`   for `α ∈ CH_*(Y)`,

which is the second identity of Stacks 0ERE
(`AlgebraicGeometry.Space.chowClassCanonical_firstChernCapCycleMap_flatPullbackMap`, on cycles).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_flatPullbackChow_of_vanishingLocus`.

## References

* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X Y : D.Ambient}
  (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
  (p : X ⟶ Y) (hbase : p ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem p)
  (hr : HasRelativeDimension (r + 1) D.site D.base D.base_mem p)
  (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hL : IsInvertibleSheaf D sX hX L)
  (s : L.sections)
  (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
    (ObjectProperty.homMk p : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩) (vanishingLocus D sX hX L s))

/-- **Stacks 0ERE on Chow homology**: `c₁(ℒ) ∩ p^*α = i_*((p|_E)^*α)` for the vanishing locus
`E = Z(s)` of a section of an invertible module, when it is a relative effective Cartier divisor
over `Y`. -/
theorem firstChernCapChow_flatPullbackChow_of_vanishingLocus
    (α : chowHomology.{u, u + 1} D sY hY) :
    firstChernCapChow.{u, u + 1} D sX hX L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)
        (flatPullbackChow.{u, u + 1} D sX hX sY hY p hbase (r + 1) hflat hr α) =
      closedSubspacePushforwardChow D sX hX (vanishingLocus D sX hX L s)
        (flatPullbackChow.{u, u + 1} D _ (isGood_closedSubspace D sX hX _) sY hY
          ((vanishingLocus D sX hX L s).1.ι ≫ p)
          (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
          (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) α) := by
  refine DFunLike.congr_fun (chowHomology_hom_ext (φ :=
    (firstChernCapChow.{u, u + 1} D sX hX L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)).comp
      (flatPullbackChow.{u, u + 1} D sX hX sY hY p hbase (r + 1) hflat hr))
    (ψ := (closedSubspacePushforwardChow D sX hX (vanishingLocus D sX hX L s)).comp
      (flatPullbackChow.{u, u + 1} D _ (isGood_closedSubspace D sX hX _) sY hY
          ((vanishingLocus D sX hX L s).1.ι ≫ p)
          (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
          (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE))) D sY hY
    fun k b => ?_) α
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [AddMonoidHom.comp_apply]
  rw [flatPullbackChow_of_chowClass_eq D sX hX sY hY p hbase (r + 1) hflat hr (j + 1)
      (j + r + 1 + 1) (by push_cast; ring), firstChernCapChow_of_chowClass,
    flatPullbackChow_of_chowClass_eq D _ (isGood_closedSubspace D sX hX _) sY hY _
      (comp_structureMorphism_eq D _ sX sY _ p rfl hbase) r hE.2
      (hasRelativeDimension_ι_comp D sX hX sY hY p hbase r hr _ hE) (j + 1) (j + r + 1)
      (by ring),
    closedSubspacePushforwardChow_of_chowClass]
  exact congrArg _ (chowClass_eq_of_chowClassCanonical_eq D sX hX
    (chowClassCanonical_firstChernCapCycleMap_flatPullbackMap.{0, u} D sX hX sY hY p hbase r hflat
      hr L hL s hE j b))

end AlgebraicGeometry.Space.PrivateChern

end
