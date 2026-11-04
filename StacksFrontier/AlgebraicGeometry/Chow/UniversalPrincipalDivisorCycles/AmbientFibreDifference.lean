module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.FibreDifference

/-!
# The principal divisor on `X` as a difference of the ambient fibre cycles

Let `X` be integral and locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `U ⊆ X` be a dense open and let `g` be an invertible section on `U`. Write
`Y` for the closure of the graph of the morphism `U ⟶ ℙ¹_S` whose coordinate is `g`, write
`p : Y ⟶ X` for the projection, and write `Y₀, Y_∞ ⊆ Y` for the pullbacks of the zero and
infinity divisors of `ℙ¹_S`. Both composites `Y₀ ⟶ X` and `Y_∞ ⟶ X` are closed immersions, so
`Y₀` and `Y_∞` are closed subschemes of `X` itself, and this file proves

  `div_X(f) = [Y₀ ⊆ X]_{n-1} - [Y_∞ ⊆ X]_{n-1}`,

the identity of part (6) of Stacks 02RQ, where `n` is the delta-dimension of `X`.

## Main results

* `Stacks.Chow.principalDivisorCycle_eq_sub_imageCycles` — the identity of part (6) of Tag 02RQ;
  the statement in a Chow situation is `Stacks.Chow.principalDivisorCycle_eq_imageFibreCycles_sub`.

## Implementation notes

### The route, and why it needs no part of Stacks 02R6 beyond the closed-immersion case

Part (5) of the tag writes the principal divisor on `X` as the proper pushforward along `p` of
the principal divisor on `Y`, and part (4) writes the latter as the difference of the cycles of
`Y₀` and `Y_∞` *in `Y`*. Proper pushforward is a group homomorphism
(`Stacks.Chow.properPushforward_sub`), so all that remains is to carry each of the two cycles
from `Y` to `X`. That is the pushforward formula of Stacks 02R6 — but only in the case where the
composite of the closed immersion with the proper morphism is again a closed immersion, and in
that case it is
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`,
whose right-hand side is the cycle of a closed subscheme rather than of a coherent sheaf. The
general form of Stacks 02R6, whose right-hand side is the cycle of the coherent direct image
`(i ≫ p)_* O_Z`, is *not* used and is not available: it rests on the cycle of a coherent sheaf
(Stacks 02QX), which is not formalized here, and on the proper mapping theorem (Stacks 02O5),
which is not proved here either. Neither is needed, because the hypotheses of part (6) are
exactly that both composites are closed immersions.

Coherence of the two direct images would in any case be available without Stacks 02O5, since a
closed immersion is finite: that is `Stacks.pushforward_isCoherent_of_isFinite`, which carries
the attribute for Stacks 01Y6.

### The two closed-immersion hypotheses are not restrictions

The two closed immersions are taken as arguments here. They hold unconditionally:
`Stacks.Chow.isClosedImmersion_graphZeroFiber_comp` and
`Stacks.Chow.isClosedImmersion_graphInfinityFiber_comp` prove them for every section of every
open, with no hypothesis on `X`, on `U` or on the section, and the statement in a Chow situation
uses them.

### `[QuasiCompact U.ι]`

The statement here is made for `U ⟶ X` quasi-compact, as in
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles`; in a Chow situation it is
automatic, see
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.GraphConstruction`.

### The rational function

As in part (5), the rational function is the unit of `Stacks.Chow.rationalFunctions` of Tag
01RU, carried to `AlgebraicGeometry.Scheme.functionField` by
`Stacks.Chow.rationalFunctionsEquivFunctionField`, because that is the form
`Stacks.Chow.principalDivisorCycle` takes.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

section Cycles

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens) (g : (Γ(X, U))ˣ)

/-- Viewing `Y₀` and `Y_∞` as closed subschemes of `X`
through the projection `p : Y ⟶ X`, the principal divisor of the rational function on `X` is the
difference of their cycles.

Part (5) writes the left-hand side as `p_*` of the principal divisor on `Y`, part (4) writes
that as the difference of the cycles of `Y₀` and `Y_∞` in `Y`, and the closed-immersion case of
Stacks 02R6 carries each of those two cycles from `Y` to `X`. -/
theorem principalDivisorCycle_eq_sub_imageCycles [QuasiCompact U.ι] (n : ℤ)
    (hn : schemeDeltaDimension C sX = (n : EInt))
    (f : (rationalFunctions X)ˣ) (hU : Dense (U : Set X))
    (hf : ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X))
    (h₀ : IsClosedImmersion ((graphZeroFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g))
    (hInf : IsClosedImmersion
      ((graphInfinityFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g)) :
    letI : IsClosedImmersion
      ((graphZeroFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) := h₀
    letI : IsClosedImmersion
      ((graphInfinityFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) := hInf
    principalDivisorCycle C sX hn ((rationalFunctionsEquivFunctionField X).1 ↑f) =
      cycleAssociatedToClosedSubscheme C sX
          ((graphZeroFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) (n - 1) -
        cycleAssociatedToClosedSubscheme C sX
          ((graphInfinityFiber sX U ↑g).subschemeι ≫ graphProjection sX U ↑g) (n - 1) := by
  have hYint : IsIntegral (graphClosure sX U ↑g) := isIntegral_graphClosure sX U ↑g hU
  have hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) :=
    locallyOfFiniteType_graphBaseMorphism sX U ↑g
  have hp : IsProper (graphProjection sX U ↑g) := graphProjection_isProper sX U ↑g
  have hd : GraphPreimageDense sX U ↑g := dense_graphPreimage sX U ↑g
  have hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt) :=
    schemeDeltaDimension_graphClosure C sX U g n hn hU hYft
  rw [principalDivisorCycle_eq_properPushforward C sX U g n hn f hU hf hd hYint hYft hp hYdim,
    principalDivisorCycle_graphClosure_eq_sub C sX U g n hd hYint hYft hYdim,
    properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl _ (n - 1),
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl _ (n - 1)]

end Cycles

end Stacks.Chow

end
