module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The transition morphism between two base changes of a morphism of schemes

Let `f : X ⟶ S` be a morphism of schemes and let `g : T' ⟶ T` be a morphism of schemes over
`S`. Base changing `f` along `T` and along `T'` produces `X ×_S T` and `X ×_S T'`, and `g`
induces a morphism `X ×_S T' ⟶ X ×_S T` between them, compatible with the projections to `X`.

This transition morphism exhibits `X ×_S T'` as the base change `(X ×_S T) ×_T T'`. Two
consequences are recorded: it is flat as soon as `g` is, and a point of `X ×_S T` lifts along
it as soon as the image of that point in `T` lifts to `T'`.

## Main definitions

* `Stacks.BaseChange.transition` is the morphism `X ×_S T' ⟶ X ×_S T` induced by a morphism
  `T' ⟶ T` of schemes over `S`.

## Main results

* `Stacks.BaseChange.transition_isPullback`: the cartesian square exhibiting `X ×_S T'` as
  `(X ×_S T) ×_T T'`.
* `Stacks.BaseChange.transition_flat`: the transition morphism along a flat morphism of schemes
  over the base is flat.
* `Stacks.BaseChange.exists_transition_preimage`: lifting a point of `X ×_S T` along the
  transition morphism of a flat morphism of schemes over the base.

## Implementation notes

The fibre product is taken with the fixed morphism `f` in the first slot, so that the
projection to `X` is `CategoryTheory.Limits.pullback.fst`; the transition morphism is built with
`CategoryTheory.Limits.pullback.lift`, which makes its composite with that projection a
single-step rewrite. `AlgebraicGeometry.baseChangeTransition` is the same construction with the
varying scheme over `S` in the first slot instead; the two conventions are related by
`CategoryTheory.Limits.pullbackSymmetry` and are not interchangeable without it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.BaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S) {T T' : Over S}

/-- The morphism `X ×_S T' ⟶ X ×_S T` of base changes of `f : X ⟶ S` induced by a morphism
`T' ⟶ T` of schemes over `S`. -/
public noncomputable def transition (g : T' ⟶ T) :
    pullback f T'.hom ⟶ pullback f T.hom :=
  pullback.lift (pullback.fst f T'.hom) (pullback.snd f T'.hom ≫ g.left) (by
    simpa [Category.assoc, g.w] using pullback.condition (f := f) (g := T'.hom))

/-- The transition morphism of base changes is compatible with the projections to `X`. -/
@[simp]
public theorem transition_comp_fst (g : T' ⟶ T) :
    transition f g ≫ pullback.fst f T.hom = pullback.fst f T'.hom :=
  pullback.lift_fst _ _ _

/-- The square formed by the transition morphism of base changes, the two projections to the
schemes over the base, and the given morphism over the base is cartesian: `X ×_S T'` is
`(X ×_S T) ×_T T'`. -/
public theorem transition_isPullback (g : T' ⟶ T) :
    IsPullback (transition f g) (pullback.snd f T'.hom) (pullback.snd f T.hom) g.left := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((pullbackLeftPullbackSndIso f T.hom g.left ≪≫ pullback.congrHom rfl g.w).symm) ?_ ?_
  · exact pullback.lift_snd _ _ _
  · refine pullback.hom_ext ?_ ?_ <;>
      simp [transition, pullback.map]
  · simp [pullback.map]

/-- The transition morphism of base changes induced by a *flat* morphism of schemes over the
base is flat, being a base change of it. -/
public theorem transition_flat (g : T' ⟶ T) (hg : Flat g.left) : Flat (transition f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (transition_isPullback f g).flip hg

/-- If the morphism `T' ⟶ T` of schemes over `S` is flat, a point of `X ×_S T` lifts to
`X ×_S T'` along the transition morphism as soon as its image in `T` lifts to `T'`. -/
public theorem exists_transition_preimage (g : T' ⟶ T) (hg : Flat g.left)
    (z : (pullback f T.hom : Scheme.{u})) (y₀ : T'.left)
    (hy₀ : g.left.base y₀ = (pullback.snd f T.hom).base z) :
    ∃ y, (transition f g).base y = z := by
  have _ : Scheme.IsJointlySurjectivePreserving (@Flat) :=
    Scheme.isJointlySurjectivePreserving _
  obtain ⟨v, hv⟩ := Scheme.IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    (P := @Flat) hg y₀ z hy₀
  have hsq := (transition_isPullback f g).flip
  refine ⟨hsq.isoPullback.inv.base v, ?_⟩
  rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd]
  exact hv

end Stacks.BaseChange
