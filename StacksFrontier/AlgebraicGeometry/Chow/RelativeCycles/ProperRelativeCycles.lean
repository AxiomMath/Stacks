module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper relative cycles

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. A relative `r`-cycle `α` on `X/S` is a *proper relative cycle* when its support is
contained in a closed subset `W ⊆ X` proper over `S`. The proper relative `r`-cycles form a
subgroup `c(X/S, r)` of the group `z(X/S, r)` of relative `r`-cycles, and properness is
inherited by every base change.

## Main definitions

* `Stacks.Chow.IsProperRelativeCycle` — the support is contained in a closed subset proper over
  the base.
* `Stacks.Chow.properRelativeCycles` — the group `c(X/S, r)` of proper relative `r`-cycles.

## Main results

* `Stacks.Chow.supportOfFamily_add_subset`, `Stacks.Chow.supportOfFamily_neg`,
  `Stacks.Chow.supportOfFamily_zero` — the support of a family of cycles is subadditive,
  invariant under negation, and empty for the zero family.
* `Stacks.Chow.supportOfFamily_baseChangeFamily_subset` — the support of a base change is
  contained in the inverse image of the support.
* `Stacks.Chow.properRelativeCycles_le_relativeCycles` — the inclusion
  `c(X/S, r) ⊆ z(X/S, r)`.
* `Stacks.Chow.isProperRelativeCycle_baseChangeFamily` — any base change of a proper relative
  cycle is proper.

## Implementation notes

A closed subset of `X` is an element of `TopologicalSpace.Closeds X` and properness over the
base is `AlgebraicGeometry.IsProperOver`, so the condition is an existential over `Closeds X`.
That the condition defines a subgroup rests on the empty closed subset being proper over the
base and on a union of two closed subsets proper over the base being proper over the base,
together with the subadditivity of the support.

The condition speaks only of the support of a family of cycles on the fibres, so neither the
locally Noetherian hypothesis on `S` nor the relative-cycle condition on `α` is carried by
`Stacks.Chow.IsProperRelativeCycle`; both are carried by `Stacks.Chow.properRelativeCycles`,
whose members are relative `r`-cycles. For the same reason the base-change statement needs no
hypothesis on the new base.

The inclusion of supports under base change is the one direction of the compatibility of the
support with base change that is visible on coefficients: a coefficient of `g^*α` is a
coefficient of `α` at the image point times a multiplicity, so it can only be nonzero where the
coefficient of `α` at the image point is.

## References

* [Stacks Project, Definition 0H61](https://stacks.math.columbia.edu/tag/0H61)
* [Stacks Project, Lemma 0H62](https://stacks.math.columbia.edu/tag/0H62)
* [Stacks Project, Remark 0H4U](https://stacks.math.columbia.edu/tag/0H4U)
* [Stacks Project, Definition 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The support of a family of cycles and the group operations -/

/-- The support of the zero family of `r`-cycles on the fibres of `X/S` is empty. -/
@[simp]
theorem supportOfFamily_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    supportOfFamily f (0 : FamilyOfCycles f r) = ∅ := by
  simp [supportOfFamily]

/-- The support of a sum of two families of `r`-cycles on the fibres of `X/S` is contained in
the union of their supports. -/
theorem supportOfFamily_add_subset {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℕ} (α β : FamilyOfCycles f r) :
    supportOfFamily f (α + β) ⊆ supportOfFamily f α ∪ supportOfFamily f β := by
  intro x hx
  rw [mem_supportOfFamily] at hx
  obtain ⟨s, y, hy, rfl⟩ := hx
  have hcoe : (⇑((α + β) s : AlgebraicCycle (f.fiber s) ℤ)) =
      fun z => (α s : AlgebraicCycle (f.fiber s) ℤ) z +
        (β s : AlgebraicCycle (f.fiber s) ℤ) z := by
    funext z
    simp
  rw [hcoe] at hy
  rcases tsupport_add _ _ hy with h | h
  · exact Or.inl ((mem_supportOfFamily f α _).2 ⟨s, y, h, rfl⟩)
  · exact Or.inr ((mem_supportOfFamily f β _).2 ⟨s, y, h, rfl⟩)

/-- The support of a family of `r`-cycles on the fibres of `X/S` is unchanged by negation. -/
@[simp]
theorem supportOfFamily_neg {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {r : ℕ}
    (α : FamilyOfCycles f r) : supportOfFamily f (-α) = supportOfFamily f α := by
  have hcoe (s : S) : (⇑((-α) s : AlgebraicCycle (f.fiber s) ℤ)) =
      -(⇑(α s : AlgebraicCycle (f.fiber s) ℤ)) := by
    funext z
    simp
  simp only [supportOfFamily, hcoe, tsupport_neg]

/-! ### The support of a base change -/

/-- The support of the base change of a family of `r`-cycles along `g : S' ⟶ S` is contained in
the inverse image of its support under the projection `X ×_S S' ⟶ X`. -/
theorem supportOfFamily_baseChangeFamily_subset {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) :
    supportOfFamily (pullback.snd f g) (baseChangeFamily f g r α) ⊆
      pullback.fst f g ⁻¹' supportOfFamily f α := by
  intro x hx
  obtain ⟨t, y, hy, rfl⟩ := (mem_supportOfFamily _ _ _).1 hx
  let m := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t
  have hsupport : Function.support
      (⇑(baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ)) ⊆
      m ⁻¹' tsupport (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ) := by
    intro z hz
    have hz' : (baseChangeFamily f g r α t :
        AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) z ≠ 0 := hz
    rw [baseChangeFamily_apply f g r α t z] at hz'
    exact subset_closure (left_ne_zero_of_mul hz')
  exact (mem_supportOfFamily f α _).2 ⟨g t, m y,
    closure_minimal hsupport ((isClosed_tsupport _).preimage m.continuous) hy,
    congrArg (fun q : (pullback.snd f g).fiber t ⟶ X => q y)
      (restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)⟩

/-! ### Proper relative cycles -/

/-- **Stacks Project, Definition 0H61.** A family `α` of `r`-cycles on the fibres of `X/S` has
proper support when its support is contained in a closed subset `W ⊆ X` proper over `S`; a
relative `r`-cycle with this property is a *proper relative cycle*. -/
@[stacks 0H61 "the predicate"]
def IsProperRelativeCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) : Prop :=
  ∃ W : Closeds X, supportOfFamily f α ⊆ (W : Set X) ∧ IsProperOver f W

/-- The zero family is a proper relative cycle: its support is empty, and the empty closed
subset is proper over the base. -/
theorem isProperRelativeCycle_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) : IsProperRelativeCycle f r (0 : FamilyOfCycles f r) :=
  ⟨⊥, by simp, isProperOver_bot f⟩

/-- A sum of two families with proper support has proper support: the support of the sum lies in
the union of the two supports, and a union of two closed subsets proper over the base is proper
over the base. -/
theorem isProperRelativeCycle_add {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℕ} {α β : FamilyOfCycles f r} (hα : IsProperRelativeCycle f r α)
    (hβ : IsProperRelativeCycle f r β) : IsProperRelativeCycle f r (α + β) := by
  obtain ⟨W, hW, hWproper⟩ := hα
  obtain ⟨V, hV, hVproper⟩ := hβ
  refine ⟨W ⊔ V, ?_, isProperOver_sup f W V hWproper hVproper⟩
  refine (supportOfFamily_add_subset f α β).trans ?_
  exact Set.union_subset_union hW hV

/-- The negative of a family with proper support has proper support: negation does not change
the support. -/
theorem isProperRelativeCycle_neg {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℕ} {α : FamilyOfCycles f r} (hα : IsProperRelativeCycle f r α) :
    IsProperRelativeCycle f r (-α) := by
  obtain ⟨W, hW, hWproper⟩ := hα
  exact ⟨W, by rwa [supportOfFamily_neg], hWproper⟩

/-- **Stacks Project, Definition 0H61.** The group `c(X/S, r)` of proper relative `r`-cycles on
`X/S`: the subgroup of the group of families of `r`-cycles on the fibres of `X/S` whose members
are the relative `r`-cycles with support contained in a closed subset proper over `S`. -/
@[stacks 0H61 "the group c(X/S, r) of proper relative cycles"]
def properRelativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) : AddSubgroup (FamilyOfCycles f r) where
  carrier := {α | IsRelativeCycle f r α ∧ IsProperRelativeCycle f r α}
  zero_mem' := ⟨isRelativeCycle_zero f r, isProperRelativeCycle_zero f r⟩
  add_mem' := fun hα hβ ↦
    ⟨isRelativeCycle_add f r hα.1 hβ.1, isProperRelativeCycle_add f hα.2 hβ.2⟩
  neg_mem' := fun hα ↦ ⟨isRelativeCycle_neg f r hα.1, isProperRelativeCycle_neg f hα.2⟩

/-- Membership in the group of proper relative `r`-cycles is the conjunction of the valuative
condition defining a relative `r`-cycle and of properness of the support. -/
@[simp]
theorem mem_properRelativeCycles {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) :
    α ∈ properRelativeCycles f r ↔ IsRelativeCycle f r α ∧ IsProperRelativeCycle f r α :=
  Iff.rfl

/-- The group of proper relative `r`-cycles is a subgroup of the group of relative
`r`-cycles. -/
theorem properRelativeCycles_le_relativeCycles {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) :
    properRelativeCycles f r ≤ relativeCycles f r :=
  fun _ hα ↦ hα.1

/-! ### Properness under base change -/

/-- Properness of the support is preserved by base change along any morphism `g : S' ⟶ S`: the
inverse image of a closed subset proper over `S` is a closed subset proper over `S'`, and it
contains the support of the base change. -/
theorem isProperRelativeCycle_baseChangeFamily_of_isProperRelativeCycle {X S S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) {α : FamilyOfCycles f r}
    (hα : IsProperRelativeCycle f r α) (g : S' ⟶ S) :
    IsProperRelativeCycle (pullback.snd f g) r (baseChangeFamily f g r α) := by
  obtain ⟨W, hW, hWproper⟩ := hα
  refine ⟨W.preimage (pullback.fst f g).continuous, ?_, ?_⟩
  · exact (supportOfFamily_baseChangeFamily_subset f g r α).trans (Set.preimage_mono hW)
  · exact isProperOver_preimage_baseChange (pullback.fst f g) (pullback.snd f g) f g
      (IsPullback.of_hasPullback f g) W hWproper

/-- **Stacks Project, Lemma 0H62.** Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of
finite type and let `α` be a relative `r`-cycle on `X/S`. If `α` is proper, then every base
change of `α` along a morphism `S' ⟶ S` is proper. -/
@[stacks 0H62]
theorem isProperRelativeCycle_baseChangeFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) {α : FamilyOfCycles f r}
    (hα : α ∈ properRelativeCycles f r) :
    ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsProperRelativeCycle (pullback.snd f g) r (baseChangeFamily f g r α) :=
  fun _ g ↦ isProperRelativeCycle_baseChangeFamily_of_isProperRelativeCycle f r hα.2 g

end Stacks.Chow

end
