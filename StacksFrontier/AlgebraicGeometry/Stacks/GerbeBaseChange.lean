module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.NatIso
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Pullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Base change of a gerbe of algebraic stacks (Stacks 06QE)

In a 2-fibre-product square

```text
𝒳' ⟶ 𝒳
↓     ↓
𝒴' ⟶ 𝒴
```

of algebraic stacks over `S`, if `𝒳` is a gerbe over `𝒴` then `𝒳'` is a gerbe over `𝒴'`. This is
**Stacks 06QE**.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.underlyingIso`: the natural isomorphism of underlying
  functors of a 2-isomorphism of 1-morphisms of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isVerticalNatTrans_underlyingIso`: that natural
  isomorphism is vertical over the big fppf site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct`: **Stacks 06QE**.

## Implementation notes

The hypothesis and the conclusion are stated at an arbitrary 2-fibre-product square over the
cospan, so the result applies to every model of the base change; in a square over `(f, g)` with
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴`, the base change of `f` is the projection `snd` to `𝒴'`.

The content is **Stacks 06P3** (`CategoryTheory.IsGerbeOver.twoFibreProduct`), which is already
available for the *canonical* model `𝒴' ×_𝒴 𝒳` and its first projection. Two steps carry it to an
arbitrary model `P`. First the canonical square over `(g, f)` is turned into one over `(f, g)` by
exchanging its projections (`CategoryTheory.Bicategory.TwoCommSq.swap`), which is again a 2-fibre
product; the comparison 1-morphism `a : P.pt ⟶ Q.pt` into it is then an equivalence over the big
fppf site, so **Stacks 06P0** in the form
`CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base_symm` moves the gerbe condition from
`Q.snd` to `a ≫ Q.snd`. Second, the comparison 2-cell `P.snd ≅ a ≫ Q.snd` of the pre-morphism is
a vertical isomorphism of structure functors, and
`CategoryTheory.IsGerbeOver.of_verticalNatIso` moves the condition the last step to `P.snd`. The
second step is needed exactly because a 2-categorical universal property identifies the two
1-morphisms only up to a 2-cell, which is less than the strict equality that Stacks 06P0 asks for.

The quasi-inverse of the comparison and the two vertical unit and counit isomorphisms come from
terminality of the two squares: the composites of the comparison with the comparison in the other
direction are equivalent, as pre-morphisms, to the identity pre-morphisms, and the mediating
2-cells of that equivalence are the unit and the counit. Their components are automatically
vertical, since every 2-morphism of the 2-category of categories fibred in groupoids has vertical
components.

## References

* [Stacks Project, Tag 06P0](https://stacks.math.columbia.edu/tag/06P0)
* [Stacks Project, Tag 06P3](https://stacks.math.columbia.edu/tag/06P3)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The natural isomorphism of the underlying functors of a 2-isomorphism of 1-morphisms of
algebraic stacks over `S`. This is
`CategoryTheory.CatFiberedInGroupoids.underlyingIso` with the extra layer of the full
sub-2-category of algebraic stacks peeled off. -/
def underlyingIso {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) :
    CatFiberedInGroupoids.homFunctor f.hom ≅ CatFiberedInGroupoids.homFunctor g.hom where
  hom := e.hom.hom.hom.toNatTrans
  inv := e.inv.hom.hom.toNatTrans
  hom_inv_id := congrArg (fun a => a.hom.hom.toNatTrans) e.hom_inv_id
  inv_hom_id := congrArg (fun a => a.hom.hom.toNatTrans) e.inv_hom_id

/-- The natural isomorphism underlying a 2-isomorphism of 1-morphisms of algebraic stacks is
vertical over the big fppf site of `S`: this is clause (3) of Stacks 02XS for the 2-category of
categories fibred in groupoids, with the index of the identity transported along
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`. -/
theorem isVerticalNatTrans_underlyingIso {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) :
    𝒴.val.val.p.IsVerticalNatTrans (underlyingIso B S hS e).hom := by
  intro x
  have hobj : 𝒴.val.val.p.obj ((CatFiberedInGroupoids.homFunctor f.hom).obj x) =
      𝒳.val.val.p.obj x :=
    Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f.hom) x
  rw [hobj]
  exact CatFiberedInGroupoids.isHomLift_app e.hom.hom x

/-- Pre-morphisms of 2-fibre-product squares in opposite directions compose to a pre-morphism
whose 1-morphism is isomorphic to the identity, by terminality of the first square. -/
private theorem nonempty_comp_iso_id {𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴} {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (c : P.PreHom Q) (d : Q.PreHom P) :
    Nonempty ((c.comp d).hom ≅ (Bicategory.TwoCommSq.PreHom.id P).hom) := by
  obtain ⟨θ, -, -⟩ := Quotient.exact
    (hP.hom_ext (Quotient.mk _ (c.comp d)) (Quotient.mk _ (Bicategory.TwoCommSq.PreHom.id P)))
  exact ⟨θ⟩

/-- **Stacks 06QE.** In a 2-fibre-product square of algebraic stacks over `S` with cospan
`(f : 𝒳 ⟶ 𝒴, g : 𝒴' ⟶ 𝒴)`, if `f` makes `𝒳` a gerbe over `𝒴` then the projection to `𝒴'` makes
the apex a gerbe over `𝒴'`. -/
@[stacks 06QE]
theorem isGerbeOver_of_isTwoFibreProduct {𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴} (P : Bicategory.TwoCommSq f g)
    (hP : Bicategory.IsTwoFibreProduct P) (hf : IsGerbeOver B S hS f) :
    IsGerbeOver B S hS P.snd := by
  classical
  set q := 𝒴'.val.val.p
  -- The canonical model of the base change, with its projections exchanged.
  set R := twoFibreProductSquare B S hS g f
  have hR : Bicategory.IsTwoFibreProduct R := isTwoFibreProduct_twoFibreProductSquare B S hS g f
  set Q := R.swap
  have hQ : Bicategory.IsTwoFibreProduct Q := Bicategory.isTwoFibreProduct_swap hR
  -- Stacks 06P3 for the canonical model.
  have hgfib : (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒴.val.val.p).IsFiberedInGroupoids := by
    rw [CatFiberedInGroupoids.homFunctor_comp_p]
    exact 𝒴'.val.property
  have hraw := CategoryTheory.IsGerbeOver.twoFibreProduct
    (J := BigFppfOver.topology B S hS) (q := 𝒴.val.val.p)
    (F := CatFiberedInGroupoids.homFunctor f.hom)
    (G := CatFiberedInGroupoids.homFunctor g.hom) hf hgfib
  rw [CatFiberedInGroupoids.homFunctor_comp_p g.hom,
    CatFiberedInGroupoids.homFunctor_comp_p f.hom] at hraw
  have hQgerbe : IsGerbeOver B S hS Q.snd := hraw
  -- The comparison with the canonical model, and its quasi-inverse.
  obtain ⟨c, -⟩ := Quotient.exists_rep (hQ.from P)
  obtain ⟨d, -⟩ := Quotient.exists_rep (hP.from Q)
  obtain ⟨θ⟩ := nonempty_comp_iso_id B S hS hP c d
  obtain ⟨ε⟩ := nonempty_comp_iso_id B S hS hQ d c
  set a := CatFiberedInGroupoids.homFunctor c.hom.hom
  set b := CatFiberedInGroupoids.homFunctor d.hom.hom
  have hac : a ⋙ Q.pt.val.val.p = P.pt.val.val.p := c.hom.hom.hom.w
  have hbd : b ⋙ P.pt.val.val.p = Q.pt.val.val.p := d.hom.hom.hom.w
  -- The comparison is an equivalence over the big fppf site of `S`.
  have eOverPt : Functor.IsEquivalenceOver P.pt.val.val.p Q.pt.val.val.p a :=
    { inv := b
      inv_over := hbd
      unitIso := underlyingIso B S hS θ
      counitIso := underlyingIso B S hS ε
      unit_vertical := isVerticalNatTrans_underlyingIso B S hS θ
      counit_vertical := isVerticalNatTrans_underlyingIso B S hS ε }
  -- Stacks 06P0 moves the gerbe condition from `Q.snd` to `a ≫ Q.snd`.
  have hpa : (a ⋙ CatFiberedInGroupoids.homFunctor Q.snd.hom) ⋙ q = P.pt.val.val.p := by
    rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p Q.snd.hom]
    exact hac
  have eOver : Functor.IsEquivalenceOver
      ((a ⋙ CatFiberedInGroupoids.homFunctor Q.snd.hom) ⋙ q)
      (CatFiberedInGroupoids.homFunctor Q.snd.hom ⋙ q) a := by
    rw [hpa, CatFiberedInGroupoids.homFunctor_comp_p Q.snd.hom]
    exact eOverPt
  have hcomposite : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) q
      (a ⋙ CatFiberedInGroupoids.homFunctor Q.snd.hom) :=
    CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base_symm rfl eOver hQgerbe
  -- The comparison 2-cell moves it the last step to `P.snd`.
  exact hcomposite.of_verticalNatIso
    (hpa.trans (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom).symm)
    (underlyingIso B S hS c.isoSnd).symm
    (Functor.IsVerticalNatTrans.inv q (underlyingIso B S hS c.isoSnd)
      (isVerticalNatTrans_underlyingIso B S hS c.isoSnd))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
