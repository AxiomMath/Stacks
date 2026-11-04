module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# Pushing a cycle to the diagonal and back

Part (3) of Tag 0B0U reads `pr_{1,*}([Δ] · α × β) = α · β` on a proper nonsingular variety. Its
proof is part (2), `Δ_*(α · β) = [Δ] · α × β`, followed by the observation that pushing a cycle
forward along the diagonal and then along the first projection returns it unchanged, because
`Δ ≫ pr₁` is the identity. This file proves that observation, as an instance of the
functoriality of proper pushforward (Tag 02R5) and of pushforward along the identity (Tag 02R4).

## Main results

* `Stacks.Chow.properPushforward_fst_properPushforward_diagonal` — `pr_{1,*} ∘ Δ_* = id` on
  `k`-cycles.
* `Stacks.Chow.properPushforward_fst_properPushforward_diagonal_self` — the same for a scheme
  proper over the base of the Chow situation, where both properness hypotheses are automatic.

## Implementation notes

The two properness hypotheses are the ones the source supplies and are taken as instances: the
diagonal of a separated morphism is a closed immersion, hence proper, and the first projection
of `X ×_S X` is the base change of `X ⟶ S`, hence proper exactly when the source assumes `X`
proper — which is where part (3) of Tag 0B0U uses that hypothesis and parts (1) and (2) do not.

The statement is about proper pushforward alone and says nothing about an intersection product,
so it is stated for an arbitrary morphism `f` of schemes and an arbitrary Chow situation rather
than only for a nonsingular variety over a field.

Neither theorem carries a `@[stacks 0B0U]` attribute: what is proved here is the geometric
identity `pr_{1, *} ∘ Δ_* = id`, one half of the proof of part (3), and the tag belongs to the
statement of all three of its parts,
`Stacks.Intersection.ReductionToDiagonal.reductionToDiagonal` in
`StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.Whole`, which consumes the first
of the two theorems below together with part (2).

## References

* [Stacks Project, Lemma 43.19.2 (Tag 0B0U)](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Chow

universe u

/-- **Pushing a cycle to the diagonal and back returns it.** For a morphism `f : X ⟶ S` whose
diagonal and first projection are proper, proper pushforward along `Δ` followed by proper
pushforward along `pr₁` is the identity on `k`-cycles, because `Δ ≫ pr₁ = 𝟙`.

This is the second half of the proof of part (3) of Tag 0B0U: given part (2),
`Δ_*(α · β) = [Δ] · α × β`, applying `pr_{1,*}` to both sides and using this identity gives
`pr_{1,*}([Δ] · α × β) = α · β`. -/
theorem properPushforward_fst_properPushforward_diagonal (C : ChowSituation.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper (pullback.diagonal f)] [IsProper (pullback.fst f f)]
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sP : (pullback f f : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType sP]
    (hd : pullback.diagonal f ≫ sP = sX) (hp : pullback.fst f f ≫ sX = sP) (k : ℤ)
    (α : CycleGroup C sX k) :
    properPushforward C sP sX (pullback.fst f f) hp k
        (properPushforward C sX sP (pullback.diagonal f) hd k α) = α := by
  have hcomp := congrFun
    (properPushforward_comp C sX sP sX (pullback.diagonal f) (pullback.fst f f) hd hp k) α
  rw [Function.comp_apply] at hcomp
  rw [hcomp,
    properPushforward_congr C sX sX (pullback.diagonal f ≫ pullback.fst f f) (𝟙 X)
      (pullback.diagonal_fst f) _ (Category.id_comp sX) k,
    properPushforward_id]

/-- **`pr_{1,*} ∘ Δ_* = id` for a scheme proper over the base of the Chow situation.** The
hypotheses of `properPushforward_fst_properPushforward_diagonal` are automatic there: a proper
morphism is separated, so its diagonal is a closed immersion and hence proper, and the first
projection of `X ×_S X` is a base change of `X ⟶ S`. This is the form in which part (3) of Tag
0B0U consumes the identity, with `X` the proper nonsingular variety of the source. -/
theorem properPushforward_fst_properPushforward_diagonal_self (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsProper sX] (k : ℤ)
    (α : CycleGroup C sX k) :
    letI : IsClosedImmersion (pullback.diagonal sX) := IsSeparated.isClosedImmersion_diagonal
    properPushforward C (pullback.fst sX sX ≫ sX) sX (pullback.fst sX sX) rfl k
        (properPushforward C sX (pullback.fst sX sX ≫ sX) (pullback.diagonal sX)
          (by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]) k α) = α :=
  have : IsClosedImmersion (pullback.diagonal sX) := IsSeparated.isClosedImmersion_diagonal
  properPushforward_fst_properPushforward_diagonal C sX sX _ _ _ k α

end Stacks.Chow

end
