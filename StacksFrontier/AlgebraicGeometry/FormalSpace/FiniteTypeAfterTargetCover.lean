module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType

/-!
# Locally of finite type implies locally of finite type after a cover of the target

This file proves the implication from condition (1) to condition (4) of **Stacks 0ANL** for a
morphism `f : X ⟶ Y` of formal algebraic spaces, with nothing assumed, together with the case
of the implication from condition (1) to condition (3) that it uses.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_square_of_isAffineFormal`: condition (1)
  implies condition (3) for a square whose chart of the target is an affine formal algebraic
  space, which is the generality in which the source's own proof of condition (4) uses it.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeAfterTargetCover_of_isLocallyOfFiniteType`:
  condition (1) implies condition (4).

## Implementation notes

The general implication from condition (1) to condition (3) is
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType`,
and the equivalence of all the conditions of Stacks 0ANL is
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae`. The case recorded here, a square
whose chart of the target is an affine formal algebraic space, goes through
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp_of_isAffineFormal`; since the
charts of the target in condition (4) are affine by Definition 0AIM, that form gives condition
(1) implies condition (4) directly, which is the implication the proof of **Stacks 0GBB**
clause (5) consumes.

## References

* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ANL, condition (1) implies condition (3), for a square whose chart of the target
is an affine formal algebraic space.** If `f` is locally of finite type and the square

`p ≫ f = t ≫ q`

has `p` representable étale and `V`, the source of its target column, an affine formal
algebraic space, then `t` is locally of finite type.

This is the generality in which the source's own proof of condition (4) uses the implication:
there the chart `Vⱼ` of the target *is* affine. The general implication is
`isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType`.

First `t ≫ q = p ≫ f` is locally of finite type, `p` being locally of finite type by
**Stacks 0AJG** and composition being **Stacks 0AQ4**. Then the cancellation of
**Stacks 0AQ6** removes `q`: it needs the locally-of-finite-type assertion of **Stacks 0AN2**
for the relative diagonal of `q`, which `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType`
`.of_comp_of_isAffineFormal` supplies from affineness of `V`.

Neither column of the square is asked to be surjective, `q` is not asked to be representable
étale, and `U` and `V` are not asked to be formal algebraic spaces beyond affineness of `V`. -/
theorem isLocallyOfFiniteType_square_of_isAffineFormal {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (U V : FppfSheaf B S hS) (p : U ⟶ X) (q : V ⟶ Y)
    (t : U ⟶ V) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hp : IsRepresentableEtale B S hS p) (hsq : p ≫ f = t ≫ q) :
    IsLocallyOfFiniteType B S hS t := by
  have hcomp : IsLocallyOfFiniteType B S hS (t ≫ q) := by
    rw [← hsq]
    exact IsLocallyOfFiniteType.comp B S hS p f
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS p hp) hf
  exact IsLocallyOfFiniteType.of_comp_of_isAffineFormal B S hS t q hV hcomp

/-- **Stacks 0ANL, condition (1) implies condition (4).** The atlas of the target and the
atlases of the fibre products of its members with the source witness condition (4) directly,
without going through condition (3): the chart `Vⱼ` of the target is an affine formal algebraic
space, so `isLocallyOfFiniteType_square_of_isAffineFormal` applies to the square the chart
`Uⱼᵢ` of `Vⱼ ×_Y X` forms with `f` and `Vⱼ ⟶ Y`.

This is the implication the proof of **Stacks 0GBB** clause (5) consumes, where `f` is the
morphism `X_red ⟶ Y_red` on the reductions.

The fibre product `Vⱼ ×_Y X` is a formal algebraic space by the étale case of Stacks 0AJ3,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`, since
`X` is a formal algebraic space and the chart `Vⱼ ⟶ Y` is representable étale. -/
theorem isLocallyOfFiniteTypeAfterTargetCover_of_isLocallyOfFiniteType {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteTypeAfterTargetCover B S hS f := by
  obtain ⟨-, J, V, v, hVaffine, hVetale, hVsurj⟩ := hY
  refine ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, I, U, w, hUaffine, hUetale, hUsurj⟩ :=
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS (v j) f hX (hVetale j)
  refine ⟨I, U, w, ⟨hUaffine, hUetale, hUsurj⟩, fun i ↦ ?_⟩
  refine isLocallyOfFiniteType_square_of_isAffineFormal B S hS f hf (U i) (V j)
    (w i ≫ pullback.snd (v j) f) (v j) (w i ≫ pullback.fst (v j) f) (hVaffine j)
    (IsRepresentableEtale.comp B S hS (hUetale i)
      (isRepresentableEtale_pullback_snd B S hS (v j) f (hVetale j))) ?_
  rw [Category.assoc, Category.assoc, ← pullback.condition]

end AlgebraicGeometry.FormalSpace

end
