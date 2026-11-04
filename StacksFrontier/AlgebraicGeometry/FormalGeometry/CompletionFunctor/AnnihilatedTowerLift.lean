module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedFullyFaithful

/-!
# Completion is full on towers of power-annihilated coherent modules

Let `X` be a locally Noetherian scheme and let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves.
Assume hypothesis (1) of [Stacks, Tag 088A]: completion along `ℐ 𝒪_{X_e}` is an equivalence on
`Coh(𝒪_{X_e})` for the closed subscheme `X_e = V(𝒦 ᵉ⁺¹)`, for every `e`. Completion along `ℐ` is
then fully faithful on the coherent modules annihilated by `𝒦 ᵉ⁺¹`, which is
`Stacks.Coherent.exists_unique_completion_preimage_of_power_annihilated`.

The proof of Tag 088A uses that fullness not at one module but along a *tower*: the
algebraizations `G_e` of the reductions `(F_n / 𝒦 ᵉ⁺¹ F_n)` form a sequence indexed by `ℕᵒᵖ`, the
term `e` annihilated by `𝒦 ᵉ⁺¹`, and the comparison with `H ^∧_𝒦` is produced by lifting a
morphism of the `ℐ`-completions of two such towers. This file carries that step: a morphism of
the `ℐ`-completions of two towers of coherent modules, the `e`-th terms of both annihilated by
`𝒦 ᵉ⁺¹`, is the `ℐ`-completion of a morphism of the towers.

The components are the fullness at each level. What has to be checked is that the components
assemble into a natural transformation, and that is faithfulness: the square at the transition
`e + 1 ⟶ e` is a square of morphisms `G_{e+1} ⟶ G'_e`, both of whose sides have the same
`ℐ`-completion by naturality of the given morphism, and both `G_{e+1}` and `G'_e` are annihilated
by `𝒦 ᵉ⁺²` — the second because annihilation by `𝒦 ᵉ⁺¹` implies annihilation by the larger power.
Only the transitions `e + 1 ⟶ e` need to be checked, which is
`CategoryTheory.NatTrans.ofOpSequence`.

## Main results

* `Stacks.Coherent.exists_whiskerRight_completionFunctor_eq_of_power_annihilated_tower` —
  **completion along `ℐ` is full on towers of `𝒦`-power-annihilated coherent modules.**
* `Stacks.Coherent.whiskerRight_completionFunctor_injective_of_power_annihilated_tower` — and
  faithful on them.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData)

/-- The hypothesis (1) of [Stacks, Tag 088A] at every level, as it is consumed here: completion
along `ℐ 𝒪_{X_e}` is an equivalence on `Coh(𝒪_{X_e})` for `X_e = V(𝒦 ᵉ⁺¹)`. -/
public abbrev IsCompletionEquivalenceOnPowerThickenings : Prop :=
  ∀ e : ℕ,
    letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
      isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
    (completionFunctor (K ^ (e + 1)).subscheme
      (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence

variable (S T : ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **Completion along `ℐ` is faithful on towers of `𝒦`-power-annihilated coherent modules.**
Two morphisms of towers whose `e`-th terms are annihilated by `𝒦 ᵉ⁺¹` and which have the same
`ℐ`-completion are equal, because completion is faithful at each level. -/
public theorem whiskerRight_completionFunctor_injective_of_power_annihilated_tower
    (hS : ∀ e : ℕ, idealPowerMultiple K (e + 1) (S.obj (op e)).obj = ⊥)
    (hT : ∀ e : ℕ, idealPowerMultiple K (e + 1) (T.obj (op e)).obj = ⊥)
    (h : IsCompletionEquivalenceOnPowerThickenings I K) {ψ ψ' : S ⟶ T}
    (hψ : Functor.whiskerRight ψ (completionFunctor X I) =
      Functor.whiskerRight ψ' (completionFunctor X I)) : ψ = ψ' := by
  refine NatTrans.ext (funext fun n => ?_)
  refine completion_map_injective_of_power_annihilated I K n.unop (h n.unop)
    (hS n.unop) (hT n.unop) ?_
  exact congrArg (fun φ : S ⋙ completionFunctor X I ⟶ T ⋙ completionFunctor X I =>
    φ.app n) hψ

/-- **Completion along `ℐ` is full on towers of `𝒦`-power-annihilated coherent modules.** Let
`S, T : ℕᵒᵖ ⥤ Coh(𝒪_X)` be towers of coherent modules whose `e`-th terms are annihilated by
`𝒦 ᵉ⁺¹`, and assume hypothesis (1) of [Stacks, Tag 088A] at every level. Then every morphism
`S ⋙ (−) ^∧_ℐ ⟶ T ⋙ (−) ^∧_ℐ` is the termwise `ℐ`-completion of a morphism `S ⟶ T`.

This is the step of the proof of Tag 088A that produces the comparison `(G_e) ⟶ H ^∧_𝒦` along
`𝒦` out of the comparison `α : (F_n) ⟶ H ^∧_ℐ` along `ℐ`: the latter gives a morphism of the
`ℐ`-completions of two towers, and the former is its lift.

The components come from
`Stacks.Coherent.exists_unique_completion_preimage_of_power_annihilated` at each level;
naturality at a transition `e + 1 ⟶ e` is faithfulness there, the two modules involved being
annihilated by `𝒦 ᵉ⁺²`. -/
public theorem exists_whiskerRight_completionFunctor_eq_of_power_annihilated_tower
    (hS : ∀ e : ℕ, idealPowerMultiple K (e + 1) (S.obj (op e)).obj = ⊥)
    (hT : ∀ e : ℕ, idealPowerMultiple K (e + 1) (T.obj (op e)).obj = ⊥)
    (h : IsCompletionEquivalenceOnPowerThickenings I K)
    (φ : S ⋙ completionFunctor X I ⟶ T ⋙ completionFunctor X I) :
    ∃ ψ : S ⟶ T, Functor.whiskerRight ψ (completionFunctor X I) = φ := by
  have hlevel : ∀ e : ℕ, ∃ c : S.obj (op e) ⟶ T.obj (op e),
      (completionFunctor X I).map c = φ.app (op e) := by
    intro e
    obtain ⟨c, hc, -⟩ := exists_unique_completion_preimage_of_power_annihilated I K e (h e)
      (S.obj (op e)) (T.obj (op e)) (hS e) (hT e) (φ.app (op e))
    exact ⟨c, hc⟩
  choose c hc using hlevel
  have hnat : ∀ e : ℕ, S.map (homOfLE (Nat.le_add_right e 1)).op ≫ c e =
      c (e + 1) ≫ T.map (homOfLE (Nat.le_add_right e 1)).op := by
    intro e
    refine completion_map_injective_of_power_annihilated I K (e + 1) (h (e + 1))
      (hS (e + 1)) (idealPowerMultiple_eq_bot_of_le (hT e) (Nat.le_succ (e + 1))) ?_
    rw [(completionFunctor X I).map_comp, (completionFunctor X I).map_comp, hc, hc]
    exact φ.naturality (homOfLE (Nat.le_add_right e 1)).op
  exact ⟨NatTrans.ofOpSequence c hnat, NatTrans.ext (funext fun n => hc n.unop)⟩

end Stacks.Coherent

end
