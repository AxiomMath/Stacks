module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative cycles

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. A family `α` of `r`-cycles on the fibres of `X/S` is a *relative `r`-cycle* when it is
compatible with specialization in the strongest possible sense: for every morphism
`g : Spec R ⟶ S` with `R` a discrete valuation ring, the base change `g^*α` satisfies
`sp_{X'/S'}(α_η) = α_0`, where `η` and `0` are the generic and the closed point of `Spec R` and
`sp_{X'/S'}` is the specialization map of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle`.

The relative `r`-cycles form a subgroup `z(X/S, r)` of the group of all families of `r`-cycles
on the fibres of `X/S`, because base change of families of cycles is a homomorphism of abelian
groups and so is the specialization map.

## Main definitions

* `Stacks.Chow.IsRelativeCycle` — the valuative condition defining a relative `r`-cycle.
* `Stacks.Chow.relativeCycles` — the group `z(X/S, r)` of relative `r`-cycles.

## Main results

* `Stacks.Chow.isRelativeCycle_zero`, `Stacks.Chow.isRelativeCycle_add`,
  `Stacks.Chow.isRelativeCycle_neg` — the valuative condition is preserved by the group
  operations on families of cycles.
* `Stacks.Chow.mem_relativeCycles` — membership in `z(X/S, r)` is the valuative condition.

## References

* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- A family `α` of `r`-cycles on the fibres of `X/S` is a *relative `r`-cycle* when for every
discrete valuation ring `R` and every morphism `g : Spec R ⟶ S` the specialization of the generic
member of the base change `g^*α` is its closed member: `sp_{X'/S'}(α_η) = α_0`. -/
@[stacks 0H50 "relative r-cycles"]
def IsRelativeCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (g : Spec (.of R) ⟶ S),
    specializationCycle (pullback.snd f g) r
        (baseChangeFamily f g r α (genericPoint (Spec (.of R)))) =
      baseChangeFamily f g r α (IsLocalRing.closedPoint R)

/-- The zero family is a relative `r`-cycle. -/
theorem isRelativeCycle_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : IsRelativeCycle f r 0 := by
  intro R _ _ _ g
  simp only [baseChangeFamily_zero, Pi.zero_apply]
  exact specializationCycle_zero (pullback.snd f g) r

/-- A sum of two relative `r`-cycles is a relative `r`-cycle. -/
theorem isRelativeCycle_add {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) {α β : FamilyOfCycles f r} (hα : IsRelativeCycle f r α)
    (hβ : IsRelativeCycle f r β) : IsRelativeCycle f r (α + β) := by
  intro R _ _ _ g
  simp only [baseChangeFamily_add, Pi.add_apply]
  rw [specializationCycle_add, hα R g, hβ R g]
  rfl

/-- The negative of a relative `r`-cycle is a relative `r`-cycle. -/
theorem isRelativeCycle_neg {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    IsRelativeCycle f r (-α) := by
  intro R _ _ _ g
  simp only [baseChangeFamily_neg, Pi.neg_apply]
  rw [← specializationCycleHom_apply, map_neg, specializationCycleHom_apply, hα R g]
  rfl

/-- The group `z(X/S, r)` of relative `r`-cycles on `X/S`: the subgroup of the group of families
of `r`-cycles on the fibres of `X/S` cut out by the valuative condition. -/
@[stacks 0H50 "the group z(X/S, r)"]
def relativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : AddSubgroup (FamilyOfCycles f r) where
  carrier := {α | IsRelativeCycle f r α}
  zero_mem' := isRelativeCycle_zero f r
  add_mem' := fun hα hβ ↦ isRelativeCycle_add f r hα hβ
  neg_mem' := fun hα ↦ isRelativeCycle_neg f r hα

/-- Membership in the group of relative `r`-cycles is the valuative condition. -/
@[simp]
theorem mem_relativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) :
    α ∈ relativeCycles f r ↔ IsRelativeCycle f r α :=
  Iff.rfl

end Stacks.Chow

end
