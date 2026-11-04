module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.MultiplicativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationExamplePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothActionQuotientStackAlgebraic

/-!
# The quotient stack of the weighted multiplicative-group action

The multiplicative group acts on `U = Spec(k[x_0, x_1, x_2, …])` with `x_i` of weight `p^i`,
by `AlgebraicGeometry.PPowerWeighted.action`.  This file forms the quotient stack `[U/𝐆_m]` of
**Stacks 06RE** and shows that it is an algebraic stack.

The quotient stack is the one of Stacks 044Q, part (2), for the action of the group algebraic
space `𝐆_{m,B} = B ×_{Spec ℤ} 𝐆_m` on `B ×_{Spec ℤ} U` over `B`, taken at the terminal algebraic
space `B` of the big fppf site over `Spec ℤ`; there `B ×_{Spec ℤ} U` is `U` and the action is the
one of this file's grading, so `[U/𝐆_m]` is what is formed.  Algebraicity is **Stacks 04TK**,
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfGroupSchemeInSiteOnOver_of_isSmooth`,
whose single hypothesis — smoothness of `B ×_{Spec ℤ} 𝐆_m ⟶ B` — is
`AlgebraicGeometry.Space.isSmooth_prod_fst_multiplicativeGroupULift`.  Nothing beyond that is
carried: in particular Artin's representability theorem, Stacks 06DC, does not enter, because
04TK is the *smooth* criterion and not the flat criterion Stacks 06FI.

## Main definitions

* `AlgebraicGeometry.PPowerWeighted.quotientStack`: **Stacks 06RE**, the quotient stack
  `[U/𝐆_m]`.

## Main results

* `AlgebraicGeometry.PPowerWeighted.isAlgebraicStack_quotientStack`: **Stacks 06RE**, it is an
  algebraic stack over `Spec ℤ`.

## Implementation notes

The one hypothesis carried is that the ambient big fppf site contain `U`, that is
`𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))`.  This is a genuine hypothesis and not a gap:
`k[x_0, x_1, x_2, …]` is not of finite type over `ℤ`, so
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType` does not place it in every site, and the
source's example likewise fixes the field `k` and asks the ambient site to be large enough for
the construction.  It is the same hypothesis the file carries for `Spec k` itself.  The group
`𝐆_m` needs no such hypothesis: `AlgebraicGeometry.Space.contains_multiplicativeGroupULift`
places it in every big fppf site.

The base of the site is `Spec ℤ` rather than `Spec k`, because
`AlgebraicGeometry.GradedGmAction` is the action of the *integral* multiplicative group scheme
on the spectrum of a graded ring — that is the form in which a grading defines an action — and
`𝐆_{m,k}` is its base change.  So `[U/𝐆_m]` is formed here as an algebraic stack over `Spec ℤ`;
`U` is a `k`-scheme and its structure morphism to `Spec ℤ` factors through `Spec k`, but the
site over which the stack is fibred is the big fppf site of `Spec ℤ`.

The strata are exhibited as reduced locally closed substacks of `[U/𝐆_m]`, each a gerbe over a
scheme with group `μ_{p^i}` or `𝐆_m`, and the stratification is shown to admit no coarser
stratification by gerbes, in
`StacksFrontier/AlgebraicGeometry/Stacks/GerbeStratificationStatement.lean`, for the object
`AlgebraicGeometry.PPowerWeighted.weightedQuotientStack` of
`AlgebraicGeometry.Stack.AlgebraicStacks` presented by the action groupoid
(`StacksFrontier/AlgebraicGeometry/Stacks/GerbeStratificationChart.lean`).

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.PPowerWeighted

variable (𝒞 : BigFppfSite.{u}) (k : Type u) [CommRing k] (p : ℕ)

/-- **Stacks 06RE.** The quotient stack `[U/𝐆_m]` of the multiplicative-group action on
`U = Spec(k[x_0, x_1, x_2, …])` in which `x_i` has weight `p^i`.  It is the quotient stack of
Stacks 044Q, part (2), for that action, read at the terminal algebraic space of the big fppf
site over `Spec ℤ`.  The hypothesis is that the site contain `U`. -/
@[stacks 06RE "the quotient stack [U/G_m]"]
noncomputable def quotientStack (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    BasedCategory
      (BigFppfOver 𝒞 (Spec (.of (ULift.{u} ℤ))) (Space.contains_specULiftZ 𝒞)) :=
  Stack.quotientStackOfGroupSchemeInSiteOnOver
    (Space.representedAlgebraicSpace 𝒞 (Spec (.of (ULift.{u} ℤ)))
      (Space.contains_specULiftZ 𝒞)
      (Over.mk (𝟙 (𝒞.obj (Space.contains_specULiftZ 𝒞)))))
    (Space.multiplicativeGroupULiftSiteObject 𝒞)
    (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)
    (action k p).action hU

/-- **Stacks 06RE.** The quotient stack `[U/𝐆_m]` is an algebraic stack over `Spec ℤ`.  This is
Stacks 04TK for the action: the structure morphism of the group algebraic space
`B ×_{Spec ℤ} 𝐆_m ⟶ B` is smooth because the Laurent polynomial ring is a smooth algebra, and
04TK carries nothing beyond that smoothness. -/
@[stacks 06RE "the quotient stack [U/G_m] is an algebraic stack"]
theorem isAlgebraicStack_quotientStack
    (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    Stack.IsAlgebraicStack.{u, w} 𝒞 (Spec (.of (ULift.{u} ℤ)))
      (Space.contains_specULiftZ 𝒞) (quotientStack 𝒞 k p hU) :=
  Stack.isAlgebraicStack_quotientStackOfGroupSchemeInSiteOnOver_of_isSmooth.{u, w}
    (Space.representedAlgebraicSpace 𝒞 (Spec (.of (ULift.{u} ℤ)))
      (Space.contains_specULiftZ 𝒞)
      (Over.mk (𝟙 (𝒞.obj (Space.contains_specULiftZ 𝒞)))))
    (Space.multiplicativeGroupULiftSiteObject 𝒞)
    (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)
    (action k p).action hU
    (Space.isSmooth_prod_fst_multiplicativeGroupULift 𝒞 _
      (isAlgebraicSpace_yoneda 𝒞 (Spec (.of (ULift.{u} ℤ))) (Space.contains_specULiftZ 𝒞)
        (Over.mk (𝟙 (𝒞.obj (Space.contains_specULiftZ 𝒞))))))

end AlgebraicGeometry.PPowerWeighted

end
