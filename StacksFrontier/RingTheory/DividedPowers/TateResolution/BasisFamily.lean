module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainBasis

/-!
# Freeness without countability, reduced to a coherent family of stage bases

`free_grade_of_countable_indices` proves every homogeneous piece of a graded divided-power
polynomial algebra free over the base ring when the variables are countable. Countability is
used for exactly one thing: it turns the finite subsets of the index set into an increasing
*sequence*, along which the one-step basis transfer `exists_basis_insert` composes by ordinary
recursion on `ℕ`.

Nothing else in that proof needs it. The exhaustion of a homogeneous piece by the stages,
`iSup_inf_finiteVariableStageSubmodule`, is over all finite subsets and carries no hypothesis,
and `free_submodule_of_directed_bases` accepts an arbitrary directed preorder as its index. So
the whole countability hypothesis is the cost of producing a *monotone family of stage bases
indexed by all finite subsets at once*, and this file records that reduction: given such a
family, every homogeneous piece is free, with no hypothesis on the index type.

This isolates what a Tate resolution on an arbitrary — possibly uncountable — family of
variables still owes, which is the family and nothing more.

## Main results

* `DividedPowers.TateResolution.free_grade_of_basis_family` — a monotone family of stage bases
  over all finite subsets of the index set makes every homogeneous piece free over the base
  ring. No countability, and no separate hypothesis that the coefficient algebra is free: the
  member of the family at the empty subset is a basis of the coefficients.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section BasisFamily

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : P →ₐ[R] A}
  (h : GradedDividedPowerPolynomial 𝒜 γ ι)

include h in
/-- **Every homogeneous piece of a graded divided-power polynomial algebra is free over the base
ring as soon as the finite variable stages carry a monotone family of bases.**

The index of `free_submodule_of_directed_bases` is taken to be the finite subsets of the variable
index set, which form a directed preorder without any hypothesis on that set; the exhaustion is
`iSup_inf_finiteVariableStageSubmodule`. So this is `free_grade_of_countable_indices` with the
chain, and with it the countability hypothesis, replaced by the family it was built to
produce. -/
public theorem free_grade_of_basis_family
    (b : Finset (Σ n : ℕ, h.indices n) → ℕ → Set A)
    (hmono : ∀ S T : Finset (Σ n : ℕ, h.indices n), S ⊆ T → ∀ m, b S m ⊆ b T m)
    (hb : ∀ S, IsStageBasis 𝒜 γ ι h.generator S (b S)) (m : ℕ) :
    Module.Free R (𝒜 m) :=
  free_submodule_of_directed_bases (𝒜 m)
    (fun S => 𝒜 m ⊓ finiteVariableStageSubmodule γ ι h.generator S)
    (fun S => b S m) (fun _ _ hST => hmono _ _ hST m)
    (fun S => (hb S).2.1 m) (fun S => (hb S).2.2 m)
    (iSup_inf_finiteVariableStageSubmodule γ ι h.generator h.finite_support m)

end BasisFamily

end DividedPowers.TateResolution

end
