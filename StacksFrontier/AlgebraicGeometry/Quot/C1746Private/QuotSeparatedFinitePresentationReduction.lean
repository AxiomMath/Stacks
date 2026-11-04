/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialAffineReduction
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.C1746Private.SeparatedFinitePresentationOfAffine

/-!
# `Quot^P_{F/X/B}` is separated and of finite presentation once it is so over affine bases

The first step of the proof of Stacks 0DPD: the question is étale (indeed fppf) local on the
base. A subfunctor `Q` of the Quot presheaf which is an fppf sheaf, and whose base changes to all
affine schemes `W` over `B` are represented by schemes separated and of finite presentation over
`W`, is an algebraic space separated and of finite presentation over `B`
(`AlgebraicGeometry.Space.isAlgebraicSpace_isSeparated_isFinitePresentation_of_isAffine`).
For `Q = Quot^{P, L}_{F/X/B}` the base change to `W` is `Quot^{P, L_W}_{F_W/X_W/W}`
(`AlgebraicGeometry.Space.QuotSituation.baseChangeSubfunctor_hilbertPolynomialQuot`).

## Main definitions

* `IsSeparatedFinitePresentationAlgebraicSpaceOver`: a subfunctor of the Quot presheaf is an
  algebraic space separated and of finite presentation over `B`.

## Main results

* `isSeparatedFinitePresentationAlgebraicSpaceOver_of_represented`:
  the reduction to affine bases, in terms of the base-changed subfunctors.
* `isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented`:
  `Quot^{P, L}_{F/X/B}` is an algebraic space separated and of finite presentation over `B` once
  all its base changes to affine schemes over `B` are represented by schemes separated and of
  finite presentation over them.

## References

* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- **A subfunctor `Q` of the Quot presheaf is an algebraic space separated and of finite
presentation over `B`**: it has a model in the universe of the site which is an algebraic space
and whose canonical morphism to `B` is separated and of finite presentation. -/
def IsSeparatedFinitePresentationAlgebraicSpaceOver (Q : Subfunctor D.quotSitePresheaf) : Prop :=
  ∃ M : D.SubfunctorModel Q, IsAlgebraicSpace B S hS M.presheaf ∧
    IsSeparated B S hS M.toBase ∧ IsFinitePresentation B S hS M.toBase

/-- **The reduction of Stacks 0DPD to an affine base, through base change.** A subfunctor `Q` of
the Quot presheaf which is an fppf sheaf is an algebraic space separated and of finite
presentation over `B` as soon as, for every object `W` of the site with affine underlying scheme
and every morphism `ξ : h_W ⟶ B`, the subfunctor `Q ×_B W` of the Quot presheaf of the base
change of `F/X/B` to `W` is represented, over `W`, by an object `Z` whose morphism `Z ⟶ W` is
separated and of finite presentation. -/
theorem isSeparatedFinitePresentationAlgebraicSpaceOver_of_represented
    (Q : Subfunctor D.quotSitePresheaf)
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q.toFunctor)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ D.Y.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (q : Z ⟶ W)
          (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅
            (D.baseChangeSubfunctor (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)
              Q).toFunctor),
          e.hom ≫ (D.baseChangeSubfunctor (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)
              Q).ι ≫ (D.canonicalBaseChanged
                (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)).quotSitePresheafToBase =
            Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u} ∧
          (_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map q) ∧
            LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
              QuasiCompact ((BigFppfOver.toScheme B S hS).map q))) :
    D.IsSeparatedFinitePresentationAlgebraicSpaceOver Q := by
  let M := SubfunctorModel.canonical Q
  refine ⟨M, isAlgebraicSpace_isSeparated_isFinitePresentation_of_isAffine B S hS
    (M.isSheaf_presheaf D hQ) D.Y.property M.toBase fun W ξ hW ↦ ?_⟩
  obtain ⟨Z, q, e, he, hq⟩ := h W ξ hW
  obtain ⟨s, hs⟩ := D.exists_isPullback_of_represented Q M ξ q e he
  exact ⟨Z, s, q, hs, hq⟩

/-- **The reduction of Stacks 0DPD to affine bases.** `Quot^{P, L}_{F/X/B}` is an algebraic space
separated and of finite presentation over `B` as soon as, for every scheme `W` of the site with
affine underlying scheme and every morphism `ξ : h_W ⟶ B`, the subfunctor
`Quot^{P, L_W}_{F_W/X_W/W}` of the Quot presheaf of the base change of `F/X/B` to `W` (with `L_W`
the pullback of `L` to `X_W = X ×_B W`) is represented, over `W`, by a scheme `Z` whose morphism
`Z ⟶ W` is separated and of finite presentation. -/
theorem isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ)
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
          (_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map q) ∧
            LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
              QuasiCompact ((BigFppfOver.toScheme B S hS).map q))) :
    D.IsSeparatedFinitePresentationAlgebraicSpaceOver (D.hilbertPolynomialQuot L P) := by
  refine D.isSeparatedFinitePresentationAlgebraicSpaceOver_of_represented
    (D.hilbertPolynomialQuot L P)
    (D.isSheaf_hilbertPolynomialQuot L P D.quotSitePresheaf_isSheaf_fppf) fun W ξ hW => ?_
  rw [D.baseChangeSubfunctor_hilbertPolynomialQuot]
  exact h W ξ hW

end AlgebraicGeometry.Space.QuotSituation

end
