module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLefflerDerivedVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived limits of an inverse system of abelian groups vanish above degree one

For an inverse system `A` of abelian groups indexed by `ℕᵒᵖ`,

`R ⁿ lim (A) = 0` for every `n ≥ 2`,

with no hypothesis on `A` whatsoever.  This is the vanishing half of [Stacks, Tag 07KW], stated
for Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, which is the spelling that
`Stacks.RightDerivedComp.objIsoOfAcyclicImage` and its consumers use;
`Rlim.lim_hasRightDerivedFunctor_and_computations` proves it for a right derived functor on the
unbounded derived category, and nothing in this development carries it across the two indexings.

The proof is the source's: every inverse system embeds in a Mittag--Leffler one
(`Rlim.exists_mono_mittagLeffler`, the tower of initial products), the quotient of a
Mittag--Leffler system is Mittag--Leffler ([Stacks, Tag 02N1]), so `A` has a two-step resolution
by `lim`-acyclic systems, and the long exact sequence of the right derived functors of `lim`
([Stacks, Tag 010Q], `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`) reads
`R ⁿ lim (A/B) ⟶ R ⁿ⁺¹ lim (A) ⟶ R ⁿ⁺¹ lim (B)` with both outer terms zero for `n ≥ 1`.

## Main results

* `Rlim.isZero_rightDerived_lim_of_two_le` — **`R ⁿ lim (A) = 0` for every `n ≥ 2` and every
  inverse system `A` of abelian groups**.

## What is and is not proved

No tag attribute is placed: the vanishing is part of [Stacks, Tag 07KW], which this development
already carries as `Rlim.lim_hasRightDerivedFunctor_and_computations`.  What is added is the
statement in Mathlib's `ℕ`-indexing, which that theorem does not give, together with no
hypothesis on the system.  Nothing is said here about degree one, where `R ¹ lim` is the
cokernel of the product differential and does not vanish in general.

## References

* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 02N1](https://stacks.math.columbia.edu/tag/02N1)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Rlim

universe u

section Vanishing

attribute [local instance] HasDerivedCategory.standard

/-- **The higher derived limits of an inverse system of abelian groups vanish above degree
one**: `R ⁿ lim (A) = 0` for every `n ≥ 2`, with no hypothesis on `A`, in Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`.

Write `0 ⟶ A ⟶ B ⟶ B/A ⟶ 0` for the embedding of `A` into the Mittag--Leffler system
`Rlim.exists_mono_mittagLeffler` produces, and its cokernel; the cokernel is Mittag--Leffler by
[Stacks, Tag 02N1], so both `B` and `B/A` are `lim`-acyclic by
`Rlim.isZero_rightDerived_lim_of_isMittagLeffler`.  In the long exact sequence of
[Stacks, Tag 010Q] the term `R ⁿ⁺¹ lim (A)` sits between `R ⁿ lim (B/A)` and `R ⁿ⁺¹ lim (B)`,
both of which vanish for `n ≥ 1`. -/
theorem isZero_rightDerived_lim_of_two_le (A : Rlim.InvSystemAb.{u}) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).rightDerived n).obj A) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  obtain ⟨B, i, _, hB⟩ := exists_mono_mittagLeffler A
  let S : ShortComplex Rlim.InvSystemAb.{u} :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
  let Δ := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u})
  have h₃ : IsZero ((Δ.functor (m + 1)).obj S.X₃) :=
    isZero_rightDerived_lim_of_isMittagLeffler S.X₃
      (Ab.isMittagLeffler_X₃_of_shortExact S hS hB) (m + 1) (Nat.succ_pos m)
  have h₂ : IsZero ((Δ.functor (m + 1 + 1)).obj S.X₂) :=
    isZero_rightDerived_lim_of_isMittagLeffler S.X₂ hB (m + 1 + 1) (Nat.succ_pos _)
  exact (Δ.exact_δ₂ hS (m + 1)).isZero_X₂_iff.2 ⟨h₃.eq_of_src _ _, h₂.eq_of_tgt _ _⟩

end Vanishing

end Rlim

end
