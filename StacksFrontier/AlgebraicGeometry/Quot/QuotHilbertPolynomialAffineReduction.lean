/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorFpqcSheaf

/-!
# `Quot^P_{F/X/B}` is a proper algebraic space once it is so over affine bases

The first step of the proofs of Stacks 0DPB and 0DPC: the question is étale (indeed fppf) local
on the base.  `Quot^{P, L}_{F/X/B}` is an fppf sheaf (Stacks 09TT and the locality of the Hilbert
polynomial condition), its base change to a scheme `W` over `B` is `Quot^{P, L_W}_{F_W/X_W/W}`
(`AlgebraicGeometry.Space.QuotSituation.baseChangeSubfunctor_hilbertPolynomialQuot`), and an
fppf sheaf over `B` whose base changes to all affine schemes over `B` are represented by schemes
proper over them is an algebraic space proper over `B`
(`AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_of_represented`, Stacks 083R).

## Main results

* `QuotSituation.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented`:
  if for every affine scheme `W` over `B` the subfunctor `Quot^{P, L_W}_{F_W/X_W/W}` is
  represented, over `W`, by a scheme proper over `W`, then `Quot^{P, L}_{F/X/B}` is an algebraic
  space proper over `B`.

## References

* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
  (P : ℤ → ℤ)

/-- **The reduction of Stacks 0DPB and 0DPC to affine bases.**  `Quot^{P, L}_{F/X/B}` is an
algebraic space proper over `B` as soon as, for every scheme `W` of the site with affine
underlying scheme and every morphism `ξ : h_W ⟶ B`, the subfunctor `Quot^{P, L_W}_{F_W/X_W/W}` of
the Quot presheaf of the base change of `F/X/B` to `W` (with `L_W` the pullback of `L` to
`X_W = X ×_B W`) is represented, over `W`, by a scheme `Z` whose morphism `Z ⟶ W` is proper.

The fppf sheaf property needed for the descent is unconditional: the Quot presheaf is an fppf
sheaf (`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fppf`, Stacks 09TT) and the
Hilbert polynomial condition is fppf local
(`AlgebraicGeometry.Space.QuotSituation.isSheaf_hilbertPolynomialQuot`). -/
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ D.Y.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (q : Z ⟶ W)
          (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅
            (@hilbertPolynomialQuot B S hS
              (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))
              ((modulePullback B S hS (D.baseChangedSourceProjection
                (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))).obj L)
              (isInvertible_modulePullback B S hS (D.baseChangedSourceProjection
                (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) L) P).toFunctor),
          e.hom ≫ (@hilbertPolynomialQuot B S hS
              (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))
              ((modulePullback B S hS (D.baseChangedSourceProjection
                (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))).obj L)
              (isInvertible_modulePullback B S hS (D.baseChangedSourceProjection
                (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) L) P).ι ≫
            (D.canonicalBaseChanged
              (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)).quotSitePresheafToBase =
            Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u} ∧
          _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q)) :
    D.IsProperAlgebraicSpaceOver (D.hilbertPolynomialQuot L P) := by
  refine D.isProperAlgebraicSpaceOver_of_represented (D.hilbertPolynomialQuot L P)
    (D.isSheaf_hilbertPolynomialQuot L P D.quotSitePresheaf_isSheaf_fppf) fun W ξ hW => ?_
  rw [D.baseChangeSubfunctor_hilbertPolynomialQuot]
  exact h W ξ hW

end AlgebraicGeometry.Space.QuotSituation

end
