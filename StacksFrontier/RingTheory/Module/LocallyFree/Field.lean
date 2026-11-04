module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite locally free modules of a given rank over a field

Over a field, a module is finite locally free of rank `r` precisely when it is finite dimensional
of dimension `r`. In one direction the covering family may be taken to consist of the single unit
`1`, so that no localization occurs at all; in the other direction any member of the covering
family which is nonzero is already invertible, and localizing at it changes neither the module nor
its dimension.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq`: a module which is finite locally free
  of rank `r` over a field is finite dimensional of dimension `r`.
* `Module.isFiniteLocallyFreeOfRank_of_finrank_eq`: a finite dimensional module of dimension `r`
  over a field is finite locally free of rank `r`.

The equivalence of the two conditions is
`Module.isFiniteLocallyFreeOfRank_iff_finrank_eq` in
`StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field`, which states it with independent
universes for the field and the module; it is not restated here.

## References

* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public section

universe u

namespace Module

/-- A module which is finite locally free of rank `r` over a field is finite dimensional of
dimension `r`. -/
theorem IsFiniteLocallyFreeOfRank.finite_and_finrank_eq {K M : Type u} [Field K]
    [AddCommGroup M] [Module K M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank K M r) :
    Module.Finite K M ∧ Module.finrank K M = r := by
  classical
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  have hfin : Module.Finite K M := by
    refine Module.Finite.of_localizationSpan (Set.range f) hspan ?_
    rintro ⟨g, ⟨i, rfl⟩⟩
    exact Module.Finite.of_basis (hbasis i).some
  have hnonzero : ∃ i, f i ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : Ideal.span (Set.range f) = (⊥ : Ideal K) :=
      Ideal.span_eq_bot.mpr (by rintro x ⟨i, rfl⟩; exact hn i)
    exact (show (⊤ : Ideal K) ≠ ⊥ from top_ne_bot) (hspan.symm.trans hz)
  obtain ⟨i, hi⟩ := hnonzero
  have hp : Submonoid.powers (f i) ≤ nonZeroDivisors K := by
    intro x hx
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff x (f i)).mp hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (hj ▸ pow_ne_zero j hi)
  have : Nontrivial (Localization.Away (f i)) :=
    (IsLocalization.injective (Localization.Away (f i)) hp).nontrivial
  obtain ⟨b⟩ := hbasis i
  have h₁ : Module.finrank (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M) = r := by
    simpa using Module.finrank_eq_card_basis b
  have h₂ : Module.finrank K (LocalizedModule (Submonoid.powers (f i)) M) =
      Module.finrank K M :=
    IsLocalizedModule.finrank_eq (Submonoid.powers (f i)) (LocalizedModule.mkLinearMap _ M) hp
  have h₃ : Module.finrank (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M) =
      Module.finrank K (LocalizedModule (Submonoid.powers (f i)) M) :=
    IsLocalization.finrank_eq (Localization.Away (f i)) (Submonoid.powers (f i)) hp
  exact ⟨hfin, h₂.symm.trans (h₃.symm.trans h₁)⟩

/-- A finite dimensional module of dimension `r` over a field is finite locally free of rank `r`:
the covering family consisting of the single element `1` already trivializes it. -/
theorem isFiniteLocallyFreeOfRank_of_finrank_eq {K M : Type u} [Field K] [AddCommGroup M]
    [Module K M] [Module.Finite K M] {r : ℕ} (h : Module.finrank K M = r) :
    Module.IsFiniteLocallyFreeOfRank K M r := by
  refine ⟨PUnit.{u + 1}, fun _ ↦ 1, ?_, fun _ ↦ ⟨?_⟩⟩
  · rw [show Set.range (fun _ : PUnit.{u + 1} ↦ (1 : K)) = {1} from Set.range_const,
      Ideal.span_singleton_one]
  · exact (Module.finBasisOfFinrankEq K M h).ofIsLocalizedModule
      (Localization.Away (1 : K)) (Submonoid.powers (1 : K))
      (LocalizedModule.mkLinearMap (Submonoid.powers (1 : K)) M)

end Module

end
