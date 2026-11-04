module

public import StacksFrontier.Examples.Completion.CompletionNotCompleteLocal
public import StacksFrontier.Examples.Completion.NoncompleteCompletion
import StacksCore.Tactic.StacksAttribute

/-!
# A local ring whose completion is local, incomplete and not adically complete

Stacks 110.7.1 asserts the existence of a local ring `R` with maximal ideal `m` whose `m`-adic
completion `R ^∧` is local with maximal ideal different from `m R ^∧`, is not a complete local
ring, and is not `m`-adically complete as an `R`-module. This file assembles the three statements,
each already proved for the localization of the polynomial ring in countably many variables at
its ideal of variables, into the single existence statement, so that the three pathologies are
exhibited on one ring.

## Main results

* `Stacks.Examples.CountableVarLocalization.exists_isLocalRing_adicCompletion_not_complete`:
  there is a local ring and a maximal ideal of it for which all three conclusions hold.

## Implementation notes

The witness is `binary`, the situation over the field with two elements: part (1) and part (3)
hold over any coefficient field, while part (2) is proved over a finite field of characteristic
prime to the degrees of the witness series.

## References

* [Stacks Project, Tag 05JC](https://stacks.math.columbia.edu/tag/05JC)
-/

@[expose] public noncomputable section

namespace Stacks.Examples

namespace CountableVarLocalization

/-- **Stacks 05JC.** There exists a local ring `R` and a maximal ideal `m` of it such that the
`m`-adic completion `R ^∧` of `R` is local with maximal ideal different from `m R ^∧`, is not
complete for its own maximal ideal, and is not `m`-adically complete as an `R`-module. -/
@[stacks 05JC]
theorem exists_isLocalRing_adicCompletion_not_complete :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (m : Ideal R), m.IsMaximal ∧
      ∃ _ : IsLocalRing (AdicCompletion m R),
        IsLocalRing.maximalIdeal (AdicCompletion m R) ≠ m.map (AdicCompletion.of m R) ∧
        ¬ IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion m R))
            (AdicCompletion m R) ∧
        ¬ IsAdicComplete m (AdicCompletion m R) := by
  refine ⟨binary.A, inferInstance, inferInstance, binary.n, ?_, binary.S_isLocal, ?_, ?_, ?_⟩
  · rw [binary.n_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal binary.A
  · intro heq
    refine binary.maximalIdeal_ne_map ?_
    rw [← binary.maximalIdeal_eq_ker_constantTerm]
    exact heq
  · exact completion_not_isAdicComplete_maximalIdeal
  · exact binary.completion_not_adically_complete

end CountableVarLocalization

end Stacks.Examples

end
