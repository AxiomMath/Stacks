module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat

/-!
# The multiplicative torsor and cycles

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor (`AlgebraicGeometry.Space.torsorOfInvertible`).  This
file proves that `T/B` is good and that `q` is flat of relative dimension one, so that the flat
pullback `q^* : Z_k(X) → Z_{k+1}(T)` of Stacks 0EP8 is defined, and proves the cycle-theoretic
clauses of Stacks 0EQG which follow from that.

## Main results

* `AlgebraicGeometry.Space.isGood_torsorOfInvertible`: `T/B` is good.
* `AlgebraicGeometry.Space.isFlat_torsorOfInvertibleProjection`,
  `AlgebraicGeometry.Space.hasRelativeDimension_torsorOfInvertibleProjection`: `q` is flat of
  relative dimension one.
* `AlgebraicGeometry.Space.torsorOfInvertible_clause_one`: **Stacks 0EQG, clause (1).**
* `AlgebraicGeometry.Space.torsorOfInvertible_clause_six`: **Stacks 0EQG, clause (6).**

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-- **`T/B` is good**: `q` is affine, hence quasi-separated, and smooth, hence locally of finite
type, and both properties are stable under composition with `X ⟶ B`. -/
theorem isGood_torsorOfInvertible :
    D.IsGood ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) :=
  ⟨(torsorOfInvertibleSpace D p hp L hL).property,
    isQuasiSeparated_comp D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).property
      hp.1 _ _ (isQuasiSeparated_of_isAffineHom_hom _
        (isAffineHom_torsorOfInvertibleProjection D p hp L hL)) hp.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem
      (torsorOfInvertibleSpace D p hp L hL).property hp.1 D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_of_isSmooth D.site D.base D.base_mem
        (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).1) hp.2.2⟩

/-- `q` is flat: it is smooth. -/
theorem isFlat_torsorOfInvertibleProjection :
    IsFlat D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom :=
  isFlat_of_isSmooth D.site D.base D.base_mem _
    (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).1

/-- `q` has relative dimension one. -/
theorem hasRelativeDimension_torsorOfInvertibleProjection :
    HasRelativeDimension 1 D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL).hom :=
  (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).2

/-- **Stacks 0EQG, clause (1).** In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible
`𝒪_X`-module.  The morphism `q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X` is surjective,
smooth, affine, and of relative dimension `1`. -/
@[stacks 0EQG "clause (1): q is surjective, smooth, affine, of relative dimension 1"]
theorem torsorOfInvertible_clause_one :
    IsSurjective D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom ∧
      IsSmooth D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom ∧
      IsAffineHom D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom ∧
      HasRelativeDimension 1 D.site D.base D.base_mem
        (torsorOfInvertibleProjection D p hp L hL).hom :=
  ⟨isSurjective_torsorOfInvertibleProjection D p hp L hL,
    (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).1,
    isAffineHom_torsorOfInvertibleProjection D p hp L hL,
    hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL⟩

/-- The flat pullback `q^* : Z_k(X) → Z_{k+1}(T)` along the multiplicative torsor. -/
abbrev torsorOfInvertibleFlatPullback (k : ℤ) :
    CycleGroup D p k →+ CycleGroup D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) (k + 1) :=
  flatPullbackMap D _ (isGood_torsorOfInvertible D p hp L hL) p hp
    (torsorOfInvertibleProjection D p hp L hL).hom rfl 1
    (isFlat_torsorOfInvertibleProjection D p hp L hL)
    (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) k (k + 1) (by norm_num)

/-- **Stacks 0EQG, clause (6).** If `Z ⊆ X` is a closed subspace of `δ`-dimension `≤ k`, then
`q^{-1}(Z)` is a closed subspace of `T` of `δ`-dimension `≤ k + 1`, and
`q^*[Z]_k = [q^{-1}(Z)]_{k+1}`. -/
@[stacks 0EQG "clause (6): q^{-1}(Z) is a closed subspace of T of delta-dimension at most k + 1
and q^*[Z]_k = [q^{-1}(Z)]_{k+1}"]
theorem torsorOfInvertible_clause_six (k : ℤ) (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (hZk : deltaDimensionSubspace D p hp Z hZ ≤ (k : EInt)) :
    ∃ (hZ' : IsClosedSubspace D.site D.base D.base_mem
        (Z.preimage (torsorOfInvertibleProjection D p hp L hL).hom))
      (hdim : deltaDimensionSubspace D _ (isGood_torsorOfInvertible D p hp L hL)
        (Z.preimage (torsorOfInvertibleProjection D p hp L hL).hom) hZ' ≤ ((k + 1 : ℤ) : EInt)),
      torsorOfInvertibleFlatPullback D p hp L hL k (closedSubspaceCycle D p hp Z hZ k hZk) =
        closedSubspaceCycle D _ (isGood_torsorOfInvertible D p hp L hL)
          (Z.preimage (torsorOfInvertibleProjection D p hp L hL).hom) hZ' (k + 1) hdim := by
  obtain ⟨hdim, h⟩ := flatPullback_closedSubspaceCycle_preimage D _
    (isGood_torsorOfInvertible D p hp L hL) p hp (torsorOfInvertibleProjection D p hp L hL).hom
    rfl 1 (isFlat_torsorOfInvertibleProjection D p hp L hL)
    (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) k Z hZ hZk
  exact ⟨_, hdim, h.symm⟩

end AlgebraicGeometry.Space

end
