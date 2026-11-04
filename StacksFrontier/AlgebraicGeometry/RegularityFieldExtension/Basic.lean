module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorCluster.ProjectiveSpaceNoetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.Regularity

/-!
# Projective space over a field extension is a base change

Let `k → K` be an extension of fields. This file constructs the induced morphism
`ℙⁿ_K ⟶ ℙⁿ_k` of projective spaces and identifies it as the base change of
`Spec K ⟶ Spec k` along the structure morphism of `ℙⁿ_k`. Flatness and affineness of
the induced morphism follow, because both properties are stable under base change.

## Main definitions

* `Stacks.AlgebraicGeometry.RegularityFieldExtension.projectiveSpaceFieldExtensionMap`: the
  canonical morphism `ℙⁿ_K ⟶ ℙⁿ_k` induced by `k → K`.

## Main results

* `Stacks.AlgebraicGeometry.RegularityFieldExtension.map_fst`,
  `Stacks.AlgebraicGeometry.RegularityFieldExtension.map_snd`: the induced morphism commutes with
  the projection to the base and with the projection to `ℙⁿ_ℤ`.
* `Stacks.AlgebraicGeometry.RegularityFieldExtension.isPullback_fieldExtensionMap`: the square
  whose top row is the induced morphism and whose bottom row is `Spec K ⟶ Spec k` is cartesian.
* `Stacks.AlgebraicGeometry.RegularityFieldExtension.flat_projectiveSpaceFieldExtensionMap`,
  `Stacks.AlgebraicGeometry.RegularityFieldExtension.isAffineHom_projectiveSpaceFieldExtensionMap`:
  the induced morphism is flat and affine.

## References

* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.RegularityFieldExtension

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (n : ℕ)

/-- The morphism from projective `n`-space over `K` to projective `n`-space over `k` induced by
a field extension `k → K`: the base change of `Spec K ⟶ Spec k` on the first leg of the
pullback defining projective space, and the identity on the integral model. -/
public noncomputable def projectiveSpaceFieldExtensionMap :
    projectiveSpaceOverRing n (.of K) ⟶ projectiveSpaceOverRing n (.of k) :=
  pullback.map _ _ _ _
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- The induced morphism of projective spaces is compatible with the projections to the bases:
following it by `ℙⁿ_k ⟶ Spec k` is the same as projecting to `Spec K` and then applying
`Spec` to the structure map of the extension. -/
public theorem map_fst :
    projectiveSpaceFieldExtensionMap k K n ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  pullback.lift_fst _ _ _

/-- The induced morphism of projective spaces is compatible with the projections to the integral
model: both projective spaces project to the same `ℙⁿ_ℤ`, and the induced morphism commutes
with those projections. -/
public theorem map_snd :
    projectiveSpaceFieldExtensionMap k K n ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) :=
  pullback.lift_snd _ _ _

/-- Projective space over a field extension is a base change: the square with the induced
morphism `ℙⁿ_K ⟶ ℙⁿ_k` on top, the two projections to the bases on the sides and
`Spec K ⟶ Spec k` underneath is cartesian. -/
public theorem isPullback_fieldExtensionMap :
    IsPullback (pullback.fst (terminal.from (Spec (CommRingCat.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (projectiveSpaceFieldExtensionMap k K n)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (pullback.fst (terminal.from (Spec (CommRingCat.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) := by
  refine IsPullback.of_bot ?_ (map_fst k K n).symm (IsPullback.of_hasPullback _ _)
  have h₁ : projectiveSpaceFieldExtensionMap k K n ≫
      pullback.snd (terminal.from (Spec (CommRingCat.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.snd (terminal.from (Spec (CommRingCat.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) := map_snd k K n
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
      terminal.from (Spec (CommRingCat.of k)) =
      terminal.from (Spec (CommRingCat.of K)) := terminal.hom_ext _ _
  rw [h₁, h₂]
  exact IsPullback.of_hasPullback _ _

/-- The induced morphism of projective spaces is flat, being the base change of the flat
morphism `Spec K ⟶ Spec k`. -/
public instance flat_projectiveSpaceFieldExtensionMap :
    Flat (projectiveSpaceFieldExtensionMap k K n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fieldExtensionMap k K n) inferInstance

/-- The induced morphism of projective spaces is affine, being the base change of the affine
morphism `Spec K ⟶ Spec k`. -/
public instance isAffineHom_projectiveSpaceFieldExtensionMap :
    IsAffineHom (projectiveSpaceFieldExtensionMap k K n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fieldExtensionMap k K n) inferInstance

end Stacks.AlgebraicGeometry.RegularityFieldExtension

end
