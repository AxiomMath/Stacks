module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections

/-!
# Fppf descent of the gerbe condition (Stacks 06QF)

In a 2-fibre-product square

```text
𝒳' ⟶ 𝒳
↓     ↓
𝒴' ⟶ 𝒴
```

of algebraic stacks over `S`, if `𝒴' ⟶ 𝒴` is surjective, flat and locally of finite presentation
and `𝒳'` is a gerbe over `𝒴'`, then `𝒳` is a gerbe over `𝒴`. This is **Stacks 06QF**: being a
gerbe descends along a surjective, flat, locally finitely presented morphism of the base.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_snd_of_isGerbeOver_snd`: the gerbe
  condition on the projection to `𝒴'` is a property of the cospan, not of the chosen model of
  the base change.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_snd_of_isSurjective_isFlat_isLfp`
  is **Stacks 06QF**.

## Implementation notes

The hypothesis is stated at an arbitrary 2-fibre-product square over the cospan, as in
`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct` (**Stacks 06QE**,
the converse implication), so the result applies to every model of the base change `𝒳'`; in a
square over `(f : 𝒳 ⟶ 𝒴, g : 𝒴' ⟶ 𝒴)` the base change of `f` is the projection `snd` to `𝒴'`.

The content is **Stacks 06P4** (`CategoryTheory.IsGerbeOver.of_twoFibreProduct`), which descends
the two local conditions of a gerbe along a 1-morphism `g` all of whose objects are *locally* in
the image, for the *canonical* model `𝒴' ×_𝒴 𝒳` and its first projection. Two inputs carry it to
the situation at hand.

The local surjectivity of `g` is **Stacks 06QA**
(`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`): a surjective, flat, locally finitely
presented 1-morphism admits, over an fppf covering of any object of the site, a lift of any
object of a fibre of its target. That is exactly where the three hypotheses on `g` are used, and
it is the only place they enter.

Passing from the canonical model to the given square `P` is
`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_snd_of_isGerbeOver_snd`, proved here. Its
proof is the one of Stacks 06QE run in the other direction: the comparison 1-morphism between the
apexes of two 2-fibre products of the same cospan is an equivalence over the big fppf site, whose
quasi-inverse, unit and counit come from terminality of the two squares in the category of
2-commutative squares of **Stacks 003O**, so **Stacks 06P0** in the form
`CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base` moves the gerbe condition along it; the
comparison 2-cell `P.snd ≅ c ≫ Q.snd` of the mediating pre-morphism is a vertical isomorphism of
structure functors, which `CategoryTheory.IsGerbeOver.of_verticalNatIso` absorbs. That last step
is needed because a 2-categorical universal property identifies the two 1-morphisms only up to a
2-cell, which is less than the strict equality Stacks 06P0 asks for.

The canonical square of the cospan is the one over `(g, f)`, whose *first* projection goes to
`𝒴'`; `CategoryTheory.Bicategory.TwoCommSq.swap` exchanges its projections to give a 2-fibre
product over `(f, g)`, which is the ordering the statement fixes.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 06P0](https://stacks.math.columbia.edu/tag/06P0)
* [Stacks Project, Tag 06P4](https://stacks.math.columbia.edu/tag/06P4)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QF](https://stacks.math.columbia.edu/tag/06QF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The gerbe condition on the projection to `𝒴'` does not depend on the model of the 2-fibre
product.** If `P` and `Q` are two 2-fibre products of the same cospan
`(f : 𝒳 ⟶ 𝒴, g : 𝒴' ⟶ 𝒴)` of algebraic stacks over `S` and the projection `P.snd` makes `P.pt`
a gerbe over `𝒴'`, then so does `Q.snd` for `Q.pt`.

The comparison 1-morphism `c : P.pt ⟶ Q.pt` supplied by terminality of `Q` is an equivalence over
the big fppf site of `S`; Stacks 06P0 in the form
`CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base` moves the condition from `c ≫ Q.snd` to
`Q.snd`, and the comparison 2-cell `P.snd ≅ c ≫ Q.snd` is absorbed by
`CategoryTheory.IsGerbeOver.of_verticalNatIso`. -/
theorem isGerbeOver_snd_of_isGerbeOver_snd {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    {P Q : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q) (h : IsGerbeOver B S hS P.snd) :
    IsGerbeOver B S hS Q.snd := by
  classical
  -- The comparison pre-morphisms between the two models, and the 2-cells witnessing that they
  -- are inverse to each other.
  obtain ⟨c, -⟩ := Quotient.exists_rep (hQ.from P)
  obtain ⟨d, -⟩ := Quotient.exists_rep (hP.from Q)
  obtain ⟨θ, -, -⟩ := Quotient.exact
    (hP.hom_ext (Quotient.mk _ (c.comp d)) (Quotient.mk _ (Bicategory.TwoCommSq.PreHom.id P)))
  obtain ⟨ε, -, -⟩ := Quotient.exact
    (hQ.hom_ext (Quotient.mk _ (d.comp c)) (Quotient.mk _ (Bicategory.TwoCommSq.PreHom.id Q)))
  -- The comparison is an equivalence over the big fppf site of `S`.
  have eOverPt : Functor.IsEquivalenceOver P.pt.val.val.p Q.pt.val.val.p
      (CatFiberedInGroupoids.homFunctor c.hom.hom) :=
    { inv := CatFiberedInGroupoids.homFunctor d.hom.hom
      inv_over := d.hom.hom.hom.w
      unitIso := underlyingIso B S hS θ
      counitIso := underlyingIso B S hS ε
      unit_vertical := isVerticalNatTrans_underlyingIso B S hS θ
      counit_vertical := isVerticalNatTrans_underlyingIso B S hS ε }
  have hpP : CatFiberedInGroupoids.homFunctor P.snd.hom ⋙ 𝒴'.val.val.p = P.pt.val.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom
  have hpQ : CatFiberedInGroupoids.homFunctor Q.snd.hom ⋙ 𝒴'.val.val.p = Q.pt.val.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p Q.snd.hom
  have hpc : (CatFiberedInGroupoids.homFunctor c.hom.hom ⋙
      CatFiberedInGroupoids.homFunctor Q.snd.hom) ⋙ 𝒴'.val.val.p = P.pt.val.val.p := by
    rw [Functor.assoc, hpQ]
    exact c.hom.hom.hom.w
  -- The comparison 2-cell moves the condition from `P.snd` to `c ≫ Q.snd`.
  have hcomposite : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) 𝒴'.val.val.p
      (CatFiberedInGroupoids.homFunctor c.hom.hom ⋙
        CatFiberedInGroupoids.homFunctor Q.snd.hom) :=
    h.of_verticalNatIso (hpP.trans hpc.symm) (underlyingIso B S hS c.isoSnd)
      (isVerticalNatTrans_underlyingIso B S hS c.isoSnd)
  -- Stacks 06P0 moves it the last step to `Q.snd`.
  have eOver : Functor.IsEquivalenceOver
      ((CatFiberedInGroupoids.homFunctor c.hom.hom ⋙
        CatFiberedInGroupoids.homFunctor Q.snd.hom) ⋙ 𝒴'.val.val.p)
      (CatFiberedInGroupoids.homFunctor Q.snd.hom ⋙ 𝒴'.val.val.p)
      (CatFiberedInGroupoids.homFunctor c.hom.hom) := by
    rw [hpc, hpQ]
    exact eOverPt
  exact CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base rfl eOver hcomposite

/-- **Stacks 06QF.** Let

```text
𝒳' ⟶ 𝒳
↓     ↓
𝒴' ⟶ 𝒴
```

be a 2-fibre-product square of algebraic stacks over `S`, given as a 2-commutative square `P`
over the cospan `(f : 𝒳 ⟶ 𝒴, g : 𝒴' ⟶ 𝒴)` with the 2-categorical universal property, so that
`P.pt` is `𝒳'` and `P.snd` is the base change of `f`. If `g` is surjective, flat and locally of
finite presentation and `P.snd` makes `𝒳'` a gerbe over `𝒴'`, then `f` makes `𝒳` a gerbe over
`𝒴`.

This is the descent direction; the base-change direction is
`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct`, Stacks 06QE. -/
@[stacks 06QF]
theorem isGerbeOver_of_snd_of_isSurjective_isFlat_isLfp {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq f g) (hP : Bicategory.IsTwoFibreProduct P)
    (hgsurj : Stack.IsSurjective B S hS g) (hgflat : IsFlat B S hS g)
    (hglfp : IsLocallyOfFinitePresentation B S hS g)
    (hgerbe : IsGerbeOver B S hS P.snd) :
    IsGerbeOver B S hS f := by
  refine CategoryTheory.IsGerbeOver.of_twoFibreProduct
    (G := CatFiberedInGroupoids.homFunctor g.hom) 𝒴.val.property ?_ ?_ ?_
  · rw [CatFiberedInGroupoids.homFunctor_comp_p]
    exact 𝒳.val.property
  · -- Stacks 06QA: every object of a fibre of `𝒴` is fppf-locally in the image of `g`.
    intro U y hy
    obtain ⟨T, hT, hlift⟩ :=
      exists_fppfCovering_fibre_lift B S hS g hgsurj hgflat hglfp U ⟨y, hy⟩
    exact ⟨T, hT, fun _ _ hk => hlift hk⟩
  · -- Stacks 06P4 asks for the condition at the canonical model of the base change.
    rw [CatFiberedInGroupoids.homFunctor_comp_p g.hom,
      CatFiberedInGroupoids.homFunctor_comp_p f.hom]
    exact isGerbeOver_snd_of_isGerbeOver_snd B S hS hP
      (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare B S hS g f))
      hgerbe

end AlgebraicGeometry.Stack.AlgebraicStacks

end
