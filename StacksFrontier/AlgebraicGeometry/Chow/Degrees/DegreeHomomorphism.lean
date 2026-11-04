module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree homomorphism on the zeroth Chow group

Let `k` be a field and let `p : X ⟶ Spec(k)` be proper. The *degree* of a zero cycle class on `X`
is its proper pushforward to `Spec(k)`, read through the identification `A_0(Spec(k)) = ℤ` that
sends the fundamental cycle `[Spec(k)]` to `1`. That is the definition of Stacks 0AZ1, and it is
`Stacks.Chow.chowDegree`.

Both ingredients are now unconditional. The identification of the Chow group of the base with the
integers is `Stacks.Chow.chowGroupBaseEquivInt` in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`, which needs nothing. Proper
pushforward on Chow groups is `Stacks.Chow.properChowPushforward`, which needs Stacks 02S2; that
is `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper` in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre`.

As in the rest of the chapter the base is kept general — a `Stacks.Chow.ChowSituation` with one
point and vanishing dimension function — and instantiates to a field through
`Stacks.Chow.fieldChowSituation`.

## Main definitions

* `Stacks.Chow.chowDegree` — **Stacks 0AZ1**: the degree homomorphism `A_0(X) ⟶ ℤ`.

## Main results

* `Stacks.Chow.chowDegree_mk` — the degree of the class of a zero cycle is the degree of that
  cycle, namely the coefficient at the point of the base of its proper pushforward.
* `Stacks.Chow.chowDegree_eq_zero_of_mem_rationalEquivalences` — a zero cycle rationally
  equivalent to zero has degree zero.

## References

* [Stacks Project, Tag 0AZ0](https://stacks.math.columbia.edu/tag/0AZ0)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0) [Subsingleton C.S]
  {X : Scheme.{u}} (p : X ⟶ C.S) [IsProper p]

include hδ

/-- **Stacks Project, Tag 0AZ1.** The degree homomorphism `A_0(X) ⟶ ℤ` on the zeroth Chow group
of a scheme `X` proper over a one-point base with vanishing dimension function — the spectrum of a
field.

This is the definition of Stacks 0AZ1 verbatim: proper pushforward `p_* : A_0(X) ⟶ A_0(S)` of
Stacks 0GU8, which exists by Stacks 02S2
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`), composed with the
identification `A_0(S) = ℤ` of `Stacks.Chow.chowGroupBaseEquivInt`, which sends the fundamental
cycle of the base to one. -/
@[stacks 0AZ1 "the degree homomorphism"]
def chowDegree (s : C.S) : chowGroup C p 0 →+ ℤ :=
  (chowGroupBaseEquivInt C hδ s).toAddMonoidHom.comp
    (properChowPushforward C p (𝟙 C.S) p (Category.comp_id p) 0
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C p (𝟙 C.S) p
        (Category.comp_id p) 0))

/-- **Stacks Project, Tag 0AZ1.** The degree of the class of a zero cycle is the degree of that
cycle: the coefficient at the point of the base of its proper pushforward. -/
@[simp]
theorem chowDegree_mk (s : C.S) (α : CycleGroup C p 0) :
    chowDegree C hδ p s (QuotientAddGroup.mk' (rationalEquivalences C p 0) α) =
      cycleDegree C p s α := by
  rw [chowDegree, AddMonoidHom.comp_apply, properChowPushforward_mk, AddEquiv.coe_toAddMonoidHom,
    chowGroupBaseEquivInt_mk, cycleDegree_apply]

omit [Subsingleton C.S] in
/-- A zero cycle rationally equivalent to zero has degree zero, so the degree really is a
function of the rational-equivalence class. -/
theorem chowDegree_eq_zero_of_mem_rationalEquivalences (s : C.S) {α : CycleGroup C p 0}
    (hα : α ∈ rationalEquivalences C p 0) : cycleDegree C p s α = 0 :=
  cycleDegree_eq_zero_of_mem_rationalEquivalences C hδ p s
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C p (𝟙 C.S) p
      (Category.comp_id p) 0) hα

end Stacks.Chow

end
