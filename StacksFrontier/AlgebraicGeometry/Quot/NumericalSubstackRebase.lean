module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalize
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalizeEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.FinitePresentationOverFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocus

/-!
# Open and closed conditions on `Coh_{X/Y}` along a change of base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and let `f : X ⟶ Y` be a finitely presented
morphism of algebraic spaces over `W`, with lower-shriek extension `Λ_h f` over `S`.  An object
`(T, 𝓕)` of `Coh_{X/Y}` gives the object of `Coh_{Λ_h X/Λ_h Y}` with the same test scheme
(`AlgebraicGeometry.Space.CoherentSituation.relocalizeObject`), and a morphism gives a morphism
with the same morphism of test schemes
(`AlgebraicGeometry.Space.CoherentSituation.relocalizeCoherentHom`). Consequently a condition on
`Coh_{X/Y}` which agrees, object by object, with an open and closed condition on
`Coh_{Λ_h X/Λ_h Y}` evaluated at the transported object is open and closed.  This is how the
proof of Stacks 0DNE passes from the given base scheme to `Spec ℤ`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition.of_rebase`: open and closed
  conditions are transported along the change of base scheme.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {D : CoherentSituation B W hW}

/-- **Open and closed conditions are transported along the change of base scheme.**  If a
condition `Q` on `Coh_{X/Y}` agrees, object by object, with an open and closed condition `Q'` on
`Coh_{Λ_h X/Λ_h Y}` evaluated at the transported object, then `Q` is open and closed. -/
theorem IsOpenAndClosedCondition.of_rebase {Q' : CoherentObject (D.relocalize h) → Prop}
    (hQ' : IsOpenAndClosedCondition (D.relocalize h) Q') {Q : CoherentObject D → Prop}
    (hQQ' : ∀ A, Q A ↔ Q' (D.relocalizeObject h A)) :
    IsOpenAndClosedCondition D Q := by
  intro A
  obtain ⟨U, hU, hUA⟩ := hQ' (D.relocalizeObject h A)
  exact ⟨U, hU, fun A' φ => (hQQ' A').trans (hUA _ (D.relocalizeCoherentHom h φ))⟩

end AlgebraicGeometry.Space.CoherentSituation

end
