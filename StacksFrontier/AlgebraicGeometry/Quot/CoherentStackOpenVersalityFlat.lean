module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDiagonalAffineFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenVersality
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackChartObstructionIdealSquare
public import StacksFrontier.Deformation.Artin.Versality.OpennessTransfer

/-!
# Openness of versality for `Coh_{X/B}` with `X → B` flat (second proof of Stacks 08WA)

In Situation Stacks 08KB assume that `S` is locally Noetherian, `S = B` (so that `Y` is final)
and `f : X → B` is flat. The second proof of Stacks 08WA applies Stacks 0CYF: the diagonal of
`𝒳 = Coh_{X/B}` is representable by algebraic spaces (Stacks 08W6,
`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicSpaceIsomPresheaf_coherentCFG`), `𝒳`
satisfies (RS*) (Stacks 08LQ) and is limit preserving (Stacks 08KD), and over a Noetherian
affine chart its tangent spaces and obstruction classes are read in
`Ext^i_{X_A}(ℱ, ℱ ⊗ f^*M̃)` (Stacks 08VW, 0CYE).

This file assembles that argument from the naturality of the tangent identification along
surjections of modules and the ideal-square compatibility of
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` at the test maps of surjections
of square-zero thickenings, both taken as hypotheses. This module carries no `@[stacks]`
attribute.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isOpenVersality_coherentCFG_of_isTerminal_of_isFlat`.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **Openness of versality for `Coh_{X/B}` with `X → B` flat** (the second proof of Stacks
08WA, through Stacks 0CYF), given the ideal-square compatibility of `λ` at the test maps of
surjections of square-zero thickenings of charts and the naturality of the tangent
identification `T_x(M) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` along surjections of modules, the latter
granted the ideal-square compatibility at `Spec A[N] ⟶ Spec A[M]`. -/
theorem isOpenVersality_coherentCFG_of_isTerminal_of_isFlat
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] (hY : IsTerminal D.Y)
    (hflat : IsFlat B S hS D.f.hom)
    (hH : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
      (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
      (T₁ : SquareZeroThickening A B S hS toS hA A₁) (T₂ : SquareZeroThickening A B S hS toS hA A₂)
      (f : SquareZeroThickening.Hom T₁ T₂), Function.Surjective f.ringHom →
        D.TestRelativeIdealSquareCompatible hY hflat hx f)
    (hτ : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
      {M N : SiteModule A B} (f : M ⟶ N), Function.Surjective f.hom →
      D.TestRelativeIdealSquareCompatible hY hflat hx
        (squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS) (hA := hA) f) →
      ∀ (t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
        D.satisfiesRSStar_coherentCFG).functor.obj M),
      chartTangentEquiv hY hx N hflat D.satisfiesRSStar_coherentCFG
          ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
            D.satisfiesRSStar_coherentCFG).functor.map f t) =
        D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1
          (chartTangentEquiv hY hx M hflat D.satisfiesRSStar_coherentCFG t)) :
    HasOpenVersality ((coherentCFG D).val.p ⋙ Over.post B.inclusion) :=
  D.isOpenVersality_coherentCFG_of_isTerminal hY
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS (coherentCFG D)).2
      D.isAlgebraicSpaceIsomPresheaf_coherentCFG)
    (fun A _ toS hA x hx _ _ =>
      nonempty_chartObstructionData_of_relativeIdealSquare hY hflat hx
        D.satisfiesRSStar_coherentCFG
        (fun f hf t => hτ A toS hA x hx f hf
          (hH A toS hA x hx _ _ _ _ _ (surjective_squareZeroModuleThickeningHom_ringHom f hf)) t)
        (hH A toS hA x hx))

end AlgebraicGeometry.Space.CoherentSituation

end
