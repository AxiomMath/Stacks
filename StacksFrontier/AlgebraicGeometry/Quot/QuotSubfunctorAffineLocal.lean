/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableOfAffine

/-!
# A subfunctor of the Quot presheaf is a proper algebraic space if it is so over affines

Let `F/X/B` be a Quot situation (Stacks 09TR) and `Q` a subfunctor of its Quot presheaf, such as
`Quot^P_{F/X/B}` (`AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot`). The proofs of
Stacks 0DPB and 0DPC begin: "the question is étale local over `B`, see Morphisms of Spaces,
Lemma 083R; thus we may assume `B` is an affine scheme". This file records that reduction in the
terms of `AlgebraicGeometry.Space.QuotSituation.IsProperAlgebraicSpaceOver`: if `Q` is an fppf
sheaf and, for a model `M` of `Q`, every base change of `M ⟶ B` along a morphism from an affine
scheme `W` is represented by a scheme proper over `W`, then `Q` is an algebraic space proper over
`B`.

The sheaf hypothesis is the one of Stacks 09TT for `Q`. It is supplied for a subfunctor cut out
by a condition that is local on the test scheme, once the Quot presheaf itself is a sheaf
(`AlgebraicGeometry.Space.QuotSituation.isSheaf_toFunctor_of_isSheaf`).

## Main results

* `AlgebraicGeometry.Space.QuotSituation.SubfunctorModel.isSheaf_presheaf`: a model of a sheaf is
  a sheaf.
* `AlgebraicGeometry.Space.QuotSituation.isSheaf_toFunctor_of_isSheaf`: a local subfunctor of a
  sheaf Quot presheaf is a sheaf.
* `AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_of_isAffine`: the reduction
  to affine bases.

## References

* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- **A model of a sheaf subfunctor of the Quot presheaf is a sheaf**: its universe lift is
isomorphic to the subfunctor, and the universe lift reflects the sheaf condition. -/
theorem SubfunctorModel.isSheaf_presheaf {Q : Subfunctor D.quotSitePresheaf}
    (M : D.SubfunctorModel Q)
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q.toFunctor) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) M.presheaf :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ uliftFunctor.{u + 1, u}
    ((Presheaf.isSheaf_of_iso_iff M.iso).2 hQ)

/-- **A subfunctor of a sheaf Quot presheaf cut out by a local condition is a sheaf**: if a
section of the Quot presheaf lies in `Q` as soon as its restrictions to the members of a
covering sieve do, then `Q` is a sheaf. -/
theorem isSheaf_toFunctor_of_isSheaf (Q : Subfunctor D.quotSitePresheaf)
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) D.quotSitePresheaf)
    (hloc : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : D.quotSitePresheaf.obj T),
      Q.sieveOfSection x ∈ BigFppfOver.topology B S hS T.unop → x ∈ Q.obj T) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q.toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  exact (Q.isSheaf_iff hP).2 hloc

/-- **The reduction of Stacks 0DPB and 0DPC to an affine base** (through Stacks 083R): a
subfunctor `Q` of the Quot presheaf which is an fppf sheaf, with a model `M` whose base changes
along morphisms from affine schemes `W` to `B` are represented by schemes proper over `W`, is an
algebraic space proper over `B`. -/
theorem isProperAlgebraicSpaceOver_of_isAffine (Q : Subfunctor D.quotSitePresheaf)
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q.toFunctor) (M : D.SubfunctorModel Q)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ D.Y.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (s : yoneda.obj Z ⟶ M.presheaf) (q : Z ⟶ W),
          IsPullback s (yoneda.map q) M.toBase ξ ∧
            _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q)) :
    D.IsProperAlgebraicSpaceOver Q :=
  ⟨M, isAlgebraicSpace_isProper_of_isAffine B S hS (M.isSheaf_presheaf D hQ) D.Y.property
    M.toBase h⟩

end AlgebraicGeometry.Space.QuotSituation

end
