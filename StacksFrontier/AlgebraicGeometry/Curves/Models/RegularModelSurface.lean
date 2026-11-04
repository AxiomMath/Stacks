module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GorensteinGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups

/-!
# The total space of a regular proper model is a regular surface

In the situation of [Stacks, Tag 0C61] the total space `X` of a regular proper model is an
integral Noetherian scheme, regular of dimension two. This is the hypothesis that
[Stacks, Tag 0C5R] and [Stacks, Tag 0C5S] impose on their schemes.

## Main results

* `Stacks.Models.RegularProperModelSituation.topologicalKrullDim_X` — `X` has dimension two.
* `Stacks.Models.RegularProperModelSituation.isIntegralRegularSurface` — `X` is an integral
  Noetherian scheme regular of dimension two.

## Implementation notes

The dimension is computed pointwise: the structure morphism is flat, locally of finite type and of
relative dimension one ([Stacks, Tag 0C60]), so the local dimension of `X` at `x` is the local
dimension of `Spec R` at the image plus one ([Stacks, Tag 0AFE]); `Spec R` has dimension one and
the structure morphism is surjective, being closed with the generic point in its image.

## References

* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The total space of a regular proper model has dimension two.** -/
theorem topologicalKrullDim_X : topologicalKrullDim S.X = 2 := by
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.X_to_R
  have hlocal (x : S.X) : localKrullDim S.X x =
      localKrullDim (Spec (.of S.R)) (S.X_to_R x) + 1 := by
    simpa only [topologicalKrullDimAt_eq_localKrullDim, Nat.cast_one] using
      AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_relativeDimension S.X_to_R
        S.relativeDimension_model x
  have hbase : ⨆ y, localKrullDim (Spec (.of S.R)) y = 1 := by
    rw [← topologicalKrullDim_eq_iSup_localKrullDim]
    change topologicalKrullDim (PrimeSpectrum S.R) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one S.R
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [hlocal]
    calc
      localKrullDim (Spec (.of S.R)) (S.X_to_R x) + 1 ≤ 1 + 1 :=
        add_le_add (hbase ▸ le_iSup _ _) le_rfl
      _ = 2 := by norm_num
  · have hpos : (0 : WithBot ℕ∞) < ⨆ y, localKrullDim (Spec (.of S.R)) y := by
      rw [hbase]
      norm_num
    obtain ⟨y, hy⟩ := lt_iSup_iff.mp hpos
    obtain ⟨x, rfl⟩ := S.surjective_X_to_R y
    calc
      (2 : WithBot ℕ∞) = 1 + 1 := by norm_num
      _ ≤ localKrullDim (Spec (.of S.R)) (S.X_to_R x) + 1 :=
          add_le_add (by simpa using ENat.WithBot.add_one_le_iff.mpr hy) le_rfl
      _ = localKrullDim S.X x := (hlocal x).symm
      _ ≤ ⨆ x, localKrullDim S.X x := le_iSup _ _

/-- **The total space of a regular proper model is an integral Noetherian scheme regular of
dimension two.** -/
theorem isIntegralRegularSurface :
    Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface S.X where
  isIntegral := S.toRegularModelSituation.isIntegral_X
  isNoetherian := by
    have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.X_to_R
    have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.X_to_R
    exact ⟨⟩
  isRegular := S.regular
  topologicalKrullDim_eq := S.topologicalKrullDim_X

end Stacks.Models.RegularProperModelSituation

end
