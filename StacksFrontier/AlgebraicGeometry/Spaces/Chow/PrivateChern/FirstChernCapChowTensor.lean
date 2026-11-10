module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperationsCompatibility

/-!
# Additivity of the first Chern class on the Chow homology of a good algebraic space

In Situation 0EDT let `X/B` be good. For invertible `𝒪_X`-modules `ℒ`, `𝒩` the operations
`c₁(-) ∩ -` on `CH_*(X) = ⨁_k CH_k(X)` satisfy

  `c₁(ℒ ⊗ 𝒩) ∩ - = c₁(ℒ) ∩ - + c₁(𝒩) ∩ -`   and   `c₁(𝒪_X) ∩ - = 0`,

which is Stacks 0EQK read on Chow groups: on the class of a cycle `α ∈ Z_{k+1}(X)` the operation
is the class of `c₁(ℒ) ∩ α`, for which the identities are
`AlgebraicGeometry.Space.canonicalFirstChernCap_picardTensorModule` and
`AlgebraicGeometry.Space.canonicalFirstChernCap_tensorUnit_eq_zero`, the two spellings of the
tensor product being identified by `AlgebraicGeometry.Space.canonicalFirstChernCap_congr_iso`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_tensorObj`:
  `c₁(ℒ ⊗ 𝒩) ∩ - = c₁(ℒ) ∩ - + c₁(𝒩) ∩ -`.
* `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_tensorUnit`: `c₁(𝒪_X) ∩ - = 0`.

## Implementation notes

The Chow groups are those whose rational equivalences are indexed in the universe `u + 1`, the
universe at which the cap product is known to respect rational equivalence (Stacks 0EQY,
`AlgebraicGeometry.Space.PrivateChern.respectsRationalEquivalence_firstChernCapCycleMap`). The
tensor product is that of the monoidal structure
`AlgebraicGeometry.Space.modulesMonoidalCategory`, and `𝒪_X` its unit.

## References

* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  (hX : D.IsGood sX)

/-- **Stacks 0EQK on Chow homology, first assertion**:
`c₁(ℒ ⊗ 𝒩) ∩ - = c₁(ℒ) ∩ - + c₁(𝒩) ∩ -` on `CH_*(X)` for invertible `ℒ`, `𝒩`. -/
theorem firstChernCapChow_tensorObj (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (hLN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) (L ⊗ N)) :
    firstChernCapChow.{u, u + 1} D sX hX (L ⊗ N) hLN =
      firstChernCapChow.{u, u + 1} D sX hX L hL + firstChernCapChow.{u, u + 1} D sX hX N hN := by
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [AddMonoidHom.add_apply, firstChernCapChow_of_chowClass, firstChernCapChow_of_chowClass,
    firstChernCapChow_of_chowClass, ← map_add]
  refine congrArg _ ?_
  change canonicalFirstChernCap.{u, u + 1} D sX hX (L ⊗ N) hLN j b =
    canonicalFirstChernCap.{u, u + 1} D sX hX L hL j b +
      canonicalFirstChernCap.{u, u + 1} D sX hX N hN j b
  rw [canonicalFirstChernCap_picardTensorModule hX L N hL hN j b,
    canonicalFirstChernCap_congr_iso hX _ _ hLN
      (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN)
      (modulesTensorObjIso D.site D.base D.base_mem X hX.1 L N) j b]

/-- **Stacks 0EQK on Chow homology, second assertion**: `c₁(𝒪_X) ∩ - = 0` on `CH_*(X)`. -/
theorem firstChernCapChow_tensorUnit
    (h : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))) :
    firstChernCapChow.{u, u + 1} D sX hX (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) h =
      0 := by
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [firstChernCapChow_of_chowClass, AddMonoidHom.zero_apply]
  refine (congrArg _ ?_).trans (map_zero _)
  exact canonicalFirstChernCap_tensorUnit_eq_zero hX j b

end AlgebraicGeometry.Space.PrivateChern

end
