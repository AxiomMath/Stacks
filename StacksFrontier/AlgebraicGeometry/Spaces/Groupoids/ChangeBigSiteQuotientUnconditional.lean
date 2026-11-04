module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientLocalFull

/-!
# The quotient of a groupoid in algebraic spaces after enlarging the big site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let
`G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space over `S` for `B`,
and let `f` be the morphism of sites determined by the localized inclusion. This file proves
**Stacks 04WX**: there is a canonical equivalence

`[f⁻¹U / f⁻¹R] ⟶ f⁻¹[U/R]`

of stacks over the enlarged localized big fppf site, together with clause (1) of Stacks 02ZN for
the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.

## Main definitions

* `AlgebraicGeometry.Stack.changeBigSiteQuotientEquivalence`: the canonical 1-morphism
  `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`.

## Main results

* `AlgebraicGeometry.Stack.sheafifiesMorPresheaves_changeBigSiteQuotientComparison`: clause (1)
  of Stacks 02ZN for the canonical comparison, unconditionally.
* `AlgebraicGeometry.Stack.isEquivalenceOver_changeBigSiteQuotientEquivalence`: **Stacks 04WX** —
  the canonical 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is an equivalence of stacks over the enlarged
  localized big fppf site.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **Clause (1) of Stacks 02ZN for the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`.** The
induced maps of morphism presheaves are locally injective and locally surjective. -/
theorem sheafifiesMorPresheaves_changeBigSiteQuotientComparison :
    SheafifiesMorPresheaves B B' h S hS G :=
  sheafifiesMorPresheaves_of_locally B B' h S hS G
    (locallyEqual_changeBigSiteQuotientComparison B B' h S hS G)
    (exists_covering_changeBigSiteQuotientComparison_map_comp B B' h S hS G)

/-- **The canonical 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`**, the extension of the canonical
1-morphism `u_p [U/R] ⟶ f⁻¹[U/R]` along the canonical comparison. -/
def changeBigSiteQuotientEquivalence :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj ⥤
      (pullbackQuotientStack h S hS G).obj :=
  changeBigSiteQuotientEquivalenceFunctor B B' h S hS G
    (sheafifiesMorPresheaves_changeBigSiteQuotientComparison B B' h S hS G)

/-- The canonical 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is an equivalence in the 2-category of
fibred categories over the enlarged localized big fppf site: it has a quasi-inverse strictly over
the site, with vertical unit and counit. -/
@[stacks 04WX]
theorem isEquivalenceOver_changeBigSiteQuotientEquivalence :
    Nonempty (Functor.IsEquivalenceOver
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
      (pullbackQuotientStack h S hS G).p
      (changeBigSiteQuotientEquivalence B B' h S hS G)) :=
  isEquivalenceOver_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G
    (sheafifiesMorPresheaves_changeBigSiteQuotientComparison B B' h S hS G)

end AlgebraicGeometry.Stack

end
