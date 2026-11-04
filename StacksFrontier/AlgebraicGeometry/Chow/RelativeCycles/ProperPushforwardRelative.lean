module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Compatibilities
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationProperPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward preserves relative cycles

Let `S` be a locally Noetherian scheme, let `sX : X ⟶ S` and `sY : Y ⟶ S` be locally of finite
type, let `q : X ⟶ Y` be a proper morphism over `S` and let `r ≥ 0`. This file proves the proper
pushforward clause of [Stacks, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51): the
pushforward `q_*α` of a relative `r`-cycle on `X/S` is a relative `r`-cycle on `Y/S`.

## Main results

* `Stacks.Chow.isRelativeCycle_properPushforwardFamily` — the proper pushforward of a relative
  `r`-cycle on `X/S` is a relative `r`-cycle on `Y/S`.

## References

* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Lemma 0H4M](https://stacks.math.columbia.edu/tag/0H4M)
* [Stacks Project, Lemma 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- Let `S` be locally Noetherian, let `sX : X ⟶ S` and `sY : Y ⟶ S` be locally of finite type, let
`q : X ⟶ Y` be proper with `q ≫ sY = sX` and let `r ≥ 0`. The proper pushforward `q_*α` of a
relative `r`-cycle `α` on `X/S` is a relative `r`-cycle on `Y/S`. -/
@[stacks 0H51 "proper pushforward"]
theorem isRelativeCycle_properPushforwardFamily {X Y S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] [IsLocallyNoetherian S]
    (q : X ⟶ Y) [IsProper q] (hq : q ≫ sY = sX) (r : ℕ) {α : FamilyOfCycles sX r}
    (hα : IsRelativeCycle sX r α) :
    IsRelativeCycle sY r (properPushforwardFamily sX sY q hq r α) := by
  intro R _ _ _ c
  rw [baseChangeFamily_properPushforwardFamily_of_isProper sX sY q hq c r α]
  exact (specializationCycle_fiberProperPushforward (pullback.snd sX c) (pullback.snd sY c)
        (baseChangeMap sX sY q hq c) (baseChangeMap_snd sX sY q hq c) r
        (baseChangeFamily sX c r α (genericPoint (Spec (.of R))))).symm.trans
      (congrArg (fiberProperPushforward (pullback.snd sX c) (pullback.snd sY c)
        (baseChangeMap sX sY q hq c) (baseChangeMap_snd sX sY q hq c)
        (IsLocalRing.closedPoint R) r) (hα R c))

end Stacks.Chow

end
