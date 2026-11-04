module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityHeld
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.RimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenVersalityObstruction

/-!
# Openness of versality for `Coh_{X/B}` (Stacks 08WA)

In Situation Stacks 08KB assume that `S` is locally Noetherian, `S = B` and `f : X → B` is flat.
Then `𝒳 = Coh_{X/B}` satisfies openness of versality (Stacks 07XQ).

The proof is the second proof of the source, through Stacks 0CYF: the diagonal is representable
by algebraic spaces (Stacks 08W6), `𝒳` satisfies (RS*) (Stacks 08LQ) and is limit preserving
(Stacks 08KD), and the deformation theory of an object over a Noetherian affine chart is read in
`Ext^i_{X_A}(ℱ, ℱ ⊗ f^*M̃)` (Stacks 08VW, 0CYE), which commutes with countable products by Stacks
08JR.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isOpenVersality_coherentCFG_of_isTerminal`: the
  reduction to the representability of the diagonal and the chart data.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **Openness of versality for `Coh_{X/B}` over the final base, from the diagonal and the chart
data.** With `D.Y` the final algebraic space, (RS*) and limit preservation are those of
`Coh_{X/B}` (Stacks 08LQ, 08KD), so only the representability of the diagonal and the deformation
data over Noetherian affine charts remain. -/
theorem isOpenVersality_coherentCFG_of_isTerminal
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] (hY : IsTerminal D.Y)
    (hΔ : Stack.HasRepresentableDiagonal B S hS (coherentCFG D))
    (hdata : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] [IsNoetherianRing (D.baseRing x)],
      Nonempty (D.ChartObstructionData toS hA x hx (D.satisfiesRSStar_coherentCFG))) :
    ∀ U : Over S, _root_.AlgebraicGeometry.LocallyOfFiniteType U.hom →
      ∀ (y : (coherentCFG D).val.obj)
        (hy : ((coherentCFG D).val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        IsVersalAt U ((coherentCFG D).val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            IsVersalAt U ((coherentCFG D).val.p ⋙ Over.post B.inclusion) u' y hy :=
  D.isOpenVersality_coherentCFG_of_chartObstructionData hΔ D.satisfiesRSStar_coherentCFG
    (D.isLimitPreserving_coherent
      (isLocallyOfFinitePresentation_terminal_from_of_isTerminal hY)) hdata

end AlgebraicGeometry.Space.CoherentSituation

end
