module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.Basic

/-!
# Characterizations of closed immersions of schemes

A morphism of schemes is a closed immersion exactly when it is a proper monomorphism. The latter
condition is in turn equivalent to five characterizations using unramifiedness, universal
closedness, universal injectivity, local finite type and formal unramifiedness.

## Main results

* `AlgebraicGeometry.closedImmersion_conditions_tfae` gives the equivalence of the six
  conditions on a proper monomorphism.

## Implementation notes

`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono` covers parts (1) and (2) of the
source and already carries the tag for that implication. The `List.TFAE` here lists parts (2)
through (7), in source order; together the two give the full seven-way equivalence.
Unramifiedness is the local affine condition of Tag 02G4.

## References

* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem properMono_iff_universallyClosed_unramifiedMono
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsProper f ∧ Mono f ↔
      UniversallyClosed f ∧ (Unramified f ∧ Mono f) := by
  have h := universallyInjective_unramified_tfae f
  have h31 := h.out 3 1
  constructor
  · rintro ⟨hp, hm⟩
    have : IsProper f := hp
    exact ⟨inferInstance, h31.mp ⟨inferInstance, hm⟩⟩
  · rintro ⟨huc, hram⟩
    have : Mono f := hram.2
    have : UniversallyClosed f := huc
    have : LocallyOfFiniteType f := (h31.mpr hram).1
    exact ⟨⟨⟩, hram.2⟩

/-- The six equivalent characterizations of a proper monomorphism, hence of a closed immersion,
in parts (2) through (7). -/
@[stacks 04XV "(2) <=> (3) <=> (4) <=> (5) <=> (6) <=> (7)",
  ega "IV 18.12.6" "b) <=> c)",
  ega "IV 8.11.5" "b) <=> c)"]
public theorem closedImmersion_conditions_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE
      [ IsProper f ∧ Mono f,
        IsProper f ∧ (Unramified f ∧ UniversallyInjective f),
        UniversallyClosed f ∧ (Unramified f ∧ Mono f),
        UniversallyClosed f ∧ (Unramified f ∧ UniversallyInjective f),
        UniversallyClosed f ∧ (LocallyOfFiniteType f ∧ Mono f),
        UniversallyClosed f ∧
          (UniversallyInjective f ∧ (LocallyOfFiniteType f ∧ FormallyUnramified f)) ] := by
  refine List.tfae_of_forall (b := UniversallyClosed f ∧ (Unramified f ∧ Mono f)) fun p hp ↦ ?_
  have h := universallyInjective_unramified_tfae f
  have h21 := h.out 2 1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact properMono_iff_universallyClosed_unramifiedMono f
  · constructor
    · rintro ⟨hp, hr, hi⟩
      exact (properMono_iff_universallyClosed_unramifiedMono f).mp ⟨hp, (h21.mp ⟨hr, hi⟩).2⟩
    · intro h
      have hp := (properMono_iff_universallyClosed_unramifiedMono f).mpr h
      have : Mono f := hp.2
      exact ⟨hp.1, h.2.1, inferInstance⟩
  · exact Iff.rfl
  · exact and_congr Iff.rfl h21
  · exact and_congr Iff.rfl (h.out 3 1)
  · exact and_congr Iff.rfl (h.out 4 1)

end AlgebraicGeometry

end
