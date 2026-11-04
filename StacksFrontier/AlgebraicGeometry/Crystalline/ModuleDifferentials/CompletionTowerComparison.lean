module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Completion

/-!
# Two modules with levelwise isomorphic `p`-adic towers have isomorphic completions

`Crystalline.completionLimitEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/Completion.lean` identifies the
`I`-adic completion of a module `M` with the limit of any inverse system of abelian groups which
is levelwise equivalent to the *cofinal* part `M ⧸ I^{N+e} M` of its own tower of quotients.  The
cofinality is the whole point: the comparisons a crystalline computation produces start at a
uniform level `N` — the levels of [Stacks, Proposition 60.20.1, Tag 07JN] are cut out by
`p^{N+e}` and not by `p^e` — and nothing identifies the bottom `N` levels directly.

**This module turns that into the comparison of two completions**, which is the shape every use
of it has.  Given an ideal `I`, a shift `N` and, for every `e`, an equivalence

`X ⧸ I^{N+e} X ≅ Y ⧸ I^{N+e} Y`

commuting with the transition maps, the completions `X^∧` and `Y^∧` are isomorphic, by an
isomorphism whose evaluation at every level beyond the shift is the given one.  Both halves are
`Crystalline.completionLimitEquiv` at the *same* functor — the tower of quotients of `Y` — once
with the given equivalences and once with the identity, so nothing is proved twice and the bottom
`N` levels are never mentioned.

## Main definitions

Everything is in the namespace `Crystalline`.

* `Crystalline.quotPowFunctor` — the tower of quotients `e ↦ M ⧸ I^{N+e} M` as a functor out of
  `ℕᵒᵖ`, which is what `Crystalline.completionLimitEquiv` takes.
* `Crystalline.adicCompletionAddEquivOfQuotEquiv` — **the comparison of the two completions**,
  together with its evaluation at every level beyond the shift.
* `Crystalline.adicCompletionLinearEquivOfQuotEquiv` — the same comparison read as an `R`-linear
  equivalence, when the level equivalences are `R`-linear.

## Main results

* `Crystalline.adicCompletion_ext_of_eval_shift` — an element of an adic completion is determined
  by its values at the levels beyond any fixed shift, the lower levels being their reductions.
  This is what upgrades the comparison from additive to linear.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Crystalline

section TowerComparison

variable {R : Type v} [CommRing R] (I : Ideal R)

/-- **The tower of quotients `e ↦ M ⧸ I^{N+e} M` as a functor out of `ℕᵒᵖ`**, with the transition
maps of the adic system of `M` for its arrows. -/
public noncomputable def quotPowFunctor (M : Type v) [AddCommGroup M] [Module R M] (N : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj e := AddCommGrpCat.of (M ⧸ I ^ (N + e.unop) • (⊤ : Submodule R M))
  map f := AddCommGrpCat.ofHom
    (AdicCompletion.transitionMap I M (Nat.add_le_add_left (leOfHom f.unop) N)).toAddMonoidHom
  map_id e := by
    ext x
    induction x using Submodule.Quotient.induction_on with | _ x => rfl
  map_comp f g := by
    ext x
    induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- The map of `quotPowFunctor I M N` along an arrow `op n ⟶ op m` sends the residue class of
`x` in `M ⧸ I^{N+n} M` to the residue class of `x` in `M ⧸ I^{N+m} M`. -/
@[simp] public theorem quotPowFunctor_map_mk (M : Type v) [AddCommGroup M] [Module R M] (N : ℕ)
    {m n : ℕ} (f : (Opposite.op n : ℕᵒᵖ) ⟶ Opposite.op m) (x : M) :
    (quotPowFunctor I M N).map f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        M ⧸ I ^ (N + m) • (⊤ : Submodule R M)) := rfl

/-- **An element of an adic completion is determined by its values at the levels beyond a fixed
shift.**  The value at a lower level is the reduction of the value at `N + n`, by
`AdicCompletion.transitionMap_comp_eval_apply`. -/
public theorem adicCompletion_ext_of_eval_shift {M : Type v} [AddCommGroup M] [Module R M]
    (N : ℕ) {z w : AdicCompletion I M}
    (h : ∀ e : ℕ, AdicCompletion.eval I M (N + e) z = AdicCompletion.eval I M (N + e) w) :
    z = w := by
  apply AdicCompletion.ext
  intro n
  have H := congrArg (AdicCompletion.transitionMap I M (Nat.le_add_left n N)) (h n)
  simpa only [AdicCompletion.eval_apply, AdicCompletion.transitionMap_comp_eval_apply] using H

variable {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- **Two modules whose `p`-adic towers agree beyond a shift have isomorphic completions.**

`E` is the levelwise comparison and `hE` its compatibility with the transition maps.  Both halves
of the construction are `Crystalline.completionLimitEquiv` at the tower of quotients of `Y`: once
with `E` for the level equivalences, giving `X^∧ ≅ lim`, and once with the identity, giving
`Y^∧ ≅ lim`.  The returned equation pins the comparison at every level beyond the shift, which is
all any consumer uses. -/
public noncomputable def adicCompletionAddEquivOfQuotEquiv (N : ℕ)
    (E : ∀ e : ℕ, (X ⧸ I ^ (N + e) • (⊤ : Submodule R X)) ≃+
      (Y ⧸ I ^ (N + e) • (⊤ : Submodule R Y)))
    (hE : ∀ {m n : ℕ} (h : m ≤ n) x,
      AdicCompletion.transitionMap I Y (Nat.add_le_add_left h N) (E n x) =
        E m (AdicCompletion.transitionMap I X (Nat.add_le_add_left h N) x)) :
    { L : AdicCompletion I X ≃+ AdicCompletion I Y //
      ∀ (e : ℕ) (x : AdicCompletion I X),
        AdicCompletion.eval I Y (N + e) (L x) = E e (AdicCompletion.eval I X (N + e) x) } := by
  obtain ⟨LX, hLX⟩ := completionLimitEquiv I N (quotPowFunctor I Y N) E
    (fun h x ↦ hE h x)
  obtain ⟨LY, hLY⟩ := completionLimitEquiv I N (quotPowFunctor I Y N)
    (fun _ ↦ AddEquiv.refl _) (fun _ _ ↦ rfl)
  refine ⟨LX.trans LY.symm, fun e x ↦ ?_⟩
  have hy := hLY e (LY.symm (LX x))
  rw [LY.apply_symm_apply, hLX e x] at hy
  exact hy.symm

/-- **The comparison of the two completions as an `R`-linear equivalence**, when the level
comparisons are `R`-linear.  Linearity is checked at the levels beyond the shift and transported
by `Crystalline.adicCompletion_ext_of_eval_shift`. -/
public noncomputable def adicCompletionLinearEquivOfQuotEquiv (N : ℕ)
    (E : ∀ e : ℕ, (X ⧸ I ^ (N + e) • (⊤ : Submodule R X)) ≃ₗ[R]
      (Y ⧸ I ^ (N + e) • (⊤ : Submodule R Y)))
    (hE : ∀ {m n : ℕ} (h : m ≤ n) x,
      AdicCompletion.transitionMap I Y (Nat.add_le_add_left h N) (E n x) =
        E m (AdicCompletion.transitionMap I X (Nat.add_le_add_left h N) x)) :
    { L : AdicCompletion I X ≃ₗ[R] AdicCompletion I Y //
      ∀ (e : ℕ) (x : AdicCompletion I X),
        AdicCompletion.eval I Y (N + e) (L x) = E e (AdicCompletion.eval I X (N + e) x) } := by
  obtain ⟨L, hL⟩ := adicCompletionAddEquivOfQuotEquiv I N (fun e ↦ (E e).toAddEquiv) hE
  refine ⟨{ L with map_smul' := fun r x ↦ ?_ }, hL⟩
  change L (r • x) = r • L x
  refine adicCompletion_ext_of_eval_shift I N fun e ↦ ?_
  simp only [hL e, map_smul]
  exact map_smul (E e) r _

end TowerComparison

end Crystalline

end
