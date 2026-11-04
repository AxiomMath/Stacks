module

public import StacksFrontier.AlgebraicGeometry.BlowUpSeparatedInput.Basic
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic

/-!
# The density input of Tag 0806, discharged

The reduction of [Stacks, Tag 0806] in
`StacksFrontier/AlgebraicGeometry/BlowUpUniversal/Basic.lean` takes five results of the Stacks
proof as hypotheses;
`Stacks.AlgebraicGeometry.BlowUpSeparatedInput.nonempty_isTerminal_blowUp_of'` removed the
separatedness one, leaving four. This file removes a second: `hdense`, which is
[Stacks, Tag 07ZU] — the open complement of an effective Cartier divisor is
scheme-theoretically dense.

`Stacks.AlgebraicGeometry.CartierComplementDense`
`.isSchemeTheoreticallyDense_supportCompl_of_nonZeroDivisor` proved exactly that statement from
the affine-local nonzerodivisor description of the divisor, which it had to carry as a
hypothesis because the forward direction of [Stacks, Tag 01WS] was missing.
`Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor` supplies it, so
`Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl` is unconditional and
`hdense` is a theorem rather than a hypothesis.

## Main results

* `Stacks.CartierAffineLocal.forall_isSchemeTheoreticallyDense_supportCompl`: the `hdense`
  hypothesis, at the exact shape the two reductions ask for.
* `Stacks.CartierAffineLocal.nonempty_isTerminal_blowUp_of''`: the reduction of
  [Stacks, Tag 0806] with **three** hypotheses, the remaining ones being Tag 02OS (1) and (2)
  and the existence half from Tag 01NS.

## What is not claimed

No `@[stacks 0806]` attribute is attached: three hypotheses that Tag 0806 does not carry
remain. No `@[stacks 07ZU]` either — Tag 07ZU also asserts that the open immersion of the
complement is an affine morphism, which this repository does not prove, so the covering set is
incomplete.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.BlowUpUniversal Stacks.AlgebraicGeometry.BlowUpSeparatedInput

universe u

namespace Stacks.CartierAffineLocal

/-- **[Stacks, Tag 07ZU], density half, at the shape Tag 0806's reduction asks for.** For every
scheme and every effective Cartier divisor on it, the open complement of the support is
scheme-theoretically dense. This is the `hdense` hypothesis of
`Stacks.AlgebraicGeometry.BlowUpUniversal.nonempty_isTerminal_blowUp_of` and of
`Stacks.AlgebraicGeometry.BlowUpSeparatedInput.nonempty_isTerminal_blowUp_of'`, now a
theorem. -/
theorem forall_isSchemeTheoreticallyDense_supportCompl :
    ∀ {W : Scheme.{u}} (D : W.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor D →
      Scheme.Opens.IsSchemeTheoreticallyDense (supportCompl D) :=
  fun D hD => isSchemeTheoreticallyDense_supportCompl D hD

/-- **The reduction of [Stacks, Tag 0806] with the density hypothesis gone.** Three results of
the Stacks proof remain hypotheses: Tag 02OS (2) that the exceptional divisor is an effective
Cartier divisor on the blowup, Tag 02OS (1) that the blowup morphism is an isomorphism over the
complement of the centre, and the existence half from Tag 01NS. -/
theorem nonempty_isTerminal_blowUp_of'' {X : Scheme.{u}} (I : X.IdealSheafData)
    (hcartier : IsCartierOver I (Over.mk (blowUpToBase I)))
    (hiso : IsIso (blowUpToBase I ∣_ supportCompl I))
    (hlift : ∀ Y : Over X, IsCartierOver I Y →
      Nonempty (Y ⟶ Over.mk (blowUpToBase I))) :
    ∃ h : IsCartierOver I (Over.mk (blowUpToBase I)),
      Nonempty (IsTerminal (⟨Over.mk (blowUpToBase I), h⟩ : CartierOver I)) :=
  nonempty_isTerminal_blowUp_of' I hcartier hiso
    forall_isSchemeTheoreticallyDense_supportCompl hlift

end Stacks.CartierAffineLocal

end
