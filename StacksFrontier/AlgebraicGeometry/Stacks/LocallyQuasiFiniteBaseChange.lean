module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base change of locally quasi-finite 1-morphisms of algebraic stacks (Stacks 06UB)

A base change of a locally quasi-finite 1-morphism of algebraic stacks over `S` is locally
quasi-finite. Local quasi-finiteness (**Stacks 06PU**) is a conjunction of three conditions, and
each is inherited separately: the quasi-DM condition by **Stacks 050F**, local finite type by
**Stacks 06FU**, and discreteness of the field-valued fibres because a fibre of the base change
is a fibre of the original 1-morphism.

The third condition is where the content is. A field-valued point `Spec(k) ⟶ 𝒴'` of the new
target composes with `g : 𝒴' ⟶ 𝒴` to a field-valued point of the old one, and the iterated
2-fibre product `(𝒳 ×_𝒴 𝒴') ×_{𝒴'} Spec(k)` is a 2-fibre product of the outer cospan
`(f, Spec(k) ⟶ 𝒴' ⟶ 𝒴)` by **Stacks 02XD**. So the fibre of the base change over the new point
*is* a 2-fibre product of the cospan whose fibre the hypothesis describes, and discreteness of
the space of points of a 2-fibre product depends only on the cospan.

## Main results

* `AlgebraicGeometry.Stack.discreteTopology_points_congr`: discreteness of the points of a
  2-fibre product, for the topology of **Stacks 04XL**, is a property of the cospan.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_baseChange`: **Stacks 06UB**.

## Implementation notes

The comparison of the two 2-fibre products is strict where it matters: the 1-morphism
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks` from the given square to the canonical
one has composite with the canonical second projection equal to the given square's second
projection *on the nose*, so the apex of the pasted square of Stacks 02XD is the canonical fibre
of the base change with no transport. What remains is the comparison of two 2-fibre products of
one cospan, and that is a homeomorphism on points: the two composites are 2-isomorphic to the
identities and 2-isomorphic 1-morphisms induce the same map on points.

`AlgebraicGeometry.Stack.pointTopology` is a `def` and not an instance, so the topologies are
supplied explicitly throughout.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UB](https://stacks.math.columbia.edu/tag/06UB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Discreteness on points is a property of the cospan.** Any two 2-fibre products of one
cospan of categories fibred in groupoids over the big fppf site of `S` have discrete spaces of
points together, for the topology of **Stacks 04XL**: the comparison 1-morphism is a
homeomorphism on points, its two composites being 2-isomorphic to the identities while
2-isomorphic 1-morphisms induce the same map on points. -/
theorem discreteTopology_points_congr
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @DiscreteTopology (points B S hS P.pt.val P.pt.property) (pointTopology B S hS P.pt)) :
    @DiscreteTopology (points B S hS Q.pt.val Q.pt.property) (pointTopology B S hS Q.pt) := by
  let _ := pointTopology B S hS P.pt
  let _ := pointTopology B S hS Q.pt
  let _ := h
  let a := Quotient.out (hP.from Q)
  let c := Quotient.out (hQ.from P)
  have key : ∀ {R R' : Bicategory.TwoCommSq g f} (a : R.PreHom R') (c : R'.PreHom R),
      Bicategory.TwoCommSq.PreHom.Rel (a.comp c) (Bicategory.TwoCommSq.PreHom.id R) → ∀ x,
      pointsMap B S hS _ R'.pt.property R.pt.property c.hom.hom
        (pointsMap B S hS _ R.pt.property R'.pt.property a.hom.hom x) = x := by
    rintro R R' a c ⟨θ, -, -⟩ x
    exact (pointsMap_comp B S hS _ _ _ _ a.hom.hom c.hom.hom x).trans
      ((congrFun (pointsMap_eq_of_basedNatTrans B S hS _ _ _ θ.hom.hom) x).trans
        (pointsMap_basedFunctorId B S hS _ x))
  let e : points B S hS Q.pt.val Q.pt.property ≃ₜ points B S hS P.pt.val P.pt.property :=
    { toFun := pointsMap B S hS Q.pt.val Q.pt.property P.pt.property a.hom.hom
      invFun := pointsMap B S hS P.pt.val P.pt.property Q.pt.property c.hom.hom
      left_inv := key a c (Quotient.exact (hQ.hom_ext (Quotient.mk _ (a.comp c)) (𝟙 Q)))
      right_inv := key c a (Quotient.exact (hP.hom_ext (Quotient.mk _ (c.comp a)) (𝟙 P)))
      continuous_toFun := continuous_pointsMap B S hS Q.pt P.pt a.hom.hom
      continuous_invFun := continuous_pointsMap B S hS P.pt Q.pt c.hom.hom }
  exact e.symm.discreteTopology

namespace AlgebraicStacks

/-- **Stacks 06UB.** A base change of a locally quasi-finite 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` is locally quasi-finite: the first projection of any 2-fibre product of the
cospan `(g, f)` is locally quasi-finite as soon as `f` is.

The quasi-DM conjunct is **Stacks 050F** at the exchanged square and local finite type is
**Stacks 06FU**. For the fibre conjunct, a field-valued point `g'` of `𝒴'` gives the outer point
`g' ≫ g` of `𝒴`, and the fibre of the base change over `g'` is by **Stacks 02XD** a 2-fibre
product of the cospan `(f, g' ≫ g)`, whose fibre the hypothesis says has discrete space of
points. -/
@[stacks 06UB]
theorem isLocallyQuasiFinite_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsLocallyQuasiFinite B S hS f) :
    IsLocallyQuasiFinite B S hS P.fst := by
  refine ⟨(isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS P.fst).2
      (isQuasiDM_baseChange_of_isTwoFibreProduct B S hS f g P.swap
        (Bicategory.isTwoFibreProduct_swap hP)
        ((isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).1 hf.1)),
    isLocallyOfFiniteType_baseChange B S hS f g P hP hf.2.1, ?_⟩
  intro k _ hk toBase g'
  set cmp := (canonicalPreHomAlgebraicStacks B S hS f g P.swap).hom with hcmp
  have hequiv : cmp.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS
      (Bicategory.isTwoFibreProduct_swap hP)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)
      (canonicalPreHomAlgebraicStacks B S hS f g P.swap)
  exact discreteTopology_points_congr B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f (g' ≫ g)).underlying
    (cancelSndEquivSquareAlgebraicStacks B S hS f g cmp g' (g' ≫ g) (Iso.refl _)).underlying
    (isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (g' ≫ g)))
    (isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks B S hS f g cmp g'
        (g' ≫ g) (Iso.refl _) hequiv))
    (hf.2.2 k hk toBase (g' ≫ g))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
