module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing
public import StacksFrontier.CategoryTheory.Comma.CostructuredArrowIsoTerminal
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject

/-!
# Serre vanishing on an affine algebraic space, globally on its small étale site

Let `X` be an *affine* algebraic space over a scheme `S` — one representable by an affine scheme
of the ambient big fppf site, `AlgebraicGeometry.Space.IsAffineSpace` — and let `K` be a
quasi-coherent `𝒪_X`-module.  Then the global cohomology of the abelian sheaf underlying `K` on
the small étale site of `X` vanishes in every positive degree.

This is `AlgebraicGeometry.Space.isZero_sheafH'_of_isQuasicoherentOnSite` — the positive-degree
clause of Descent, Proposition 03DW at an affine étale chart — read at the chart presented by the
representing isomorphism, which is a *terminal* object of the small étale site, so that
cohomology over it is global cohomology.

## Main results

* `AlgebraicGeometry.Space.isTerminal_representingChart`: the étale chart of an algebraic space
  presented by an isomorphism `X ≅ yoneda.obj T` is a terminal object of its small étale site.
* `AlgebraicGeometry.Space.subsingleton_sheafH_of_isQuasicoherentOnSite`: **the global
  cohomology of a quasi-coherent module on an affine algebraic space vanishes in positive
  degrees**, in `CategoryTheory.Sheaf.H` form.

## Implementation notes

The terminal object is `AlgebraicGeometry.Space.representingChart`, the chart whose structure map
is the inverse of the representing isomorphism; it is terminal by
`CategoryTheory.CostructuredArrow.mkIsoTerminal`, the generalization of Mathlib's
`CategoryTheory.CostructuredArrow.mkIdTerminal` to a costructured arrow which is an isomorphism
rather than an identity, together with the inheritance of terminality by a full subcategory.
Mathlib's identity-arrow statement is not enough: the small étale site here is that of `X`
itself, not of the algebraic space `yoneda.obj T` representing it, and
`AlgebraicGeometry.Space.isTerminalIdEtaleChart` is the latter.

Cohomology over a terminal object is global cohomology by
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'`; the coefficient
universe is the morphism universe `u` of the small étale site, which is what
`CategoryTheory.Sheaf.H'` asks for, and the `Ext` universe is `u + 1` on both sides.

No `@[stacks]` attribute is claimed: this is the affine case of a tagged statement, read at a
terminal object.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)

/-- **The étale chart presented by a representing isomorphism is a terminal object of the small
étale site.**  An étale chart of `X` is a costructured arrow `yoneda.obj T' ⟶ X`, and the
inverse of an isomorphism `X ≅ yoneda.obj T` is terminal among those because `yoneda` is fully
faithful; the étale charts form a full subcategory, so terminality is inherited. -/
def isTerminal_representingChart (i : X.1 ≅ yoneda.obj T) :
    IsTerminal (representingChart B S hS X T i) :=
  ObjectProperty.isTerminal_of_isTerminal_obj _
    (CostructuredArrow.mkIsoTerminal (S := yoneda) i.inv)

/-- The scheme underlying the chart presented by a representing isomorphism is the representing
scheme. -/
theorem chartScheme_representingChart (i : X.1 ≅ yoneda.obj T) :
    chartScheme (representingChart B S hS X T i) = (BigFppfOver.toScheme B S hS).obj T := rfl

/-! Enough injectives and `Ext`-groups for the abelian sheaves on the small étale site are
`AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale` and
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`, deliberately not instances where they
are declared; they are activated here, the statements below naming the `Ext`-groups they
provide. -/

attribute [local instance] enoughInjectives_sheaf_smallEtale
  hasExt_sheaf_smallEtale

variable {B S hS X}

/-- **The global cohomology of a quasi-coherent module on an affine algebraic space vanishes in
positive degrees.**

Let `X` be an algebraic space over `S` which is representable by an affine scheme of the ambient
big fppf site, and let `K` be an `𝒪_X`-module which is quasi-coherent on its small étale site.
Then `H^q(X, K) = 0` for every `q > 0`, the cohomology being Mathlib's
`CategoryTheory.Sheaf.H`, the global cohomology of the small étale site.

This is `AlgebraicGeometry.Space.isZero_sheafH'_of_isQuasicoherentOnSite` at the chart presented
by the representing isomorphism, which is affine and terminal. -/
theorem subsingleton_sheafH_of_isQuasicoherentOnSite (hX : IsAffineSpace B S hS X.1)
    (K : Modules.{u, u} B S hS X.1 X.2) (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} (J := SmallEtale.topology B S hS X.1)
      ((SheafOfModules.toSheaf
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj K) q) := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hX
  refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'
    (SmallEtale.topology B S hS X.1) _ q (representingChart B S hS X T i)
    (isTerminal_representingChart B S hS X T i)).2 ?_
  refine AddCommGrpCat.isZero_iff_subsingleton.mp ?_
  exact isZero_sheafH'_of_isQuasicoherentOnSite K hK (representingChart B S hS X T i) hT q hq

end AlgebraicGeometry.Space

end
