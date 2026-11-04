module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance

/-!
# Invariance of relative étaleness (Stacks 0457 at étaleness)

**Stacks 0457** says that representability by algebraic spaces, and with it the relative property
of **Stacks 03YK**, is invariant under horizontal equivalences in a 2-commutative square. The
library's statements of that invariance —
`AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences` and
`AlgebraicGeometry.Stack.isRelativelySmooth_of_equivalences` — are about
`AlgebraicGeometry.Stack.HasRelativeProperty`, whose instance arguments include
`P.IsLocalAtTarget (AlgebraicGeometry.Space.Topology.fppf.precoverage B S hS)`, and for étaleness
of morphisms of algebraic spaces that instance is **not** available. That is why
`AlgebraicGeometry.Stack.IsRelativelyEtale` is written longhand, and this module transcribes the
invariance onto the longhand notion.

The consequence the longhand notion is wanted for is the last result below: the étale condition
appearing in **Stacks 0CIF** — *every* comparison 1-morphism from a diagram's cone to *every*
2-fibre product of the cospan is étale — holds as soon as it holds for *one* 2-fibre product and
*one* comparison.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyEtale_of_equivalences`: **Stacks 0457** at étaleness.
* `AlgebraicGeometry.Stack.isRelativelyEtale_congr_twoIso`: two 2-isomorphic 1-morphisms are
  relatively étale together.
* `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_preHom`: relative étaleness passes between
  two comparison 1-morphisms from one 2-commutative square into two 2-fibre products of one
  cospan.
* `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_one`: the same, read as the étale condition
  of Stacks 0CIF, which therefore needs checking at a single 2-fibre product.

## Implementation notes

Nothing here is new mathematics: each statement is the étale reading of the corresponding smooth
one in `StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance`, and the pointwise
invariance `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` — which is stated for an
arbitrary `CategoryTheory.MorphismProperty` with no instance on it, precisely so that it can be
used here — does all the work at `AlgebraicGeometry.Space.etaleMorphisms`. The one thing to
record is that it *applies*: the body of `AlgebraicGeometry.Stack.IsRelativelyEtale` is that
statement's conclusion at `AlgebraicGeometry.Space.etaleMorphisms`, because that property is an
abbreviation for étaleness of the underlying morphism of presheaves.

The universes are pinned, not maximally general, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange`:
`AlgebraicGeometry.Stack.IsRelativelyEtale` is stated for
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, so every category in sight lives
there. The smooth analogues are stated at `CategoryTheory.CatFiberedInGroupoids.{u, v, u + 1, w}`
because `AlgebraicGeometry.Stack.IsRelativelySmooth` is.

Nothing here is registered under Tag 0457: that tag is already on
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`
(`StacksFrontier/AlgebraicGeometry/Stacks/RepresentabilityInvariance.lean`), the declaration this
file applies below and whose covering set it is, exactly as the smooth analogues are left
untagged. Nor is anything here registered under Tag 0CIF: the covering set of that tag is its
three comparison theorems.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳' 𝒴' 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Stacks 0457 at étaleness.** In a 2-commutative square of categories fibred in groupoids
over the big fppf site of `S` whose two horizontal 1-morphisms are equivalences, one vertical
1-morphism is relatively étale in the sense of Stacks 04XB exactly when the other is.

Representability by algebraic spaces transports by Stacks 0457 itself; the étaleness condition
transports by `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` at
`AlgebraicGeometry.Space.etaleMorphisms`, which asks nothing of the property. -/
theorem isRelativelyEtale_of_equivalences
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f.hom ≅ BasedFunctor.comp f'.hom b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (h : IsRelativelyEtale B S hS f) :
    IsRelativelyEtale B S hS f' := by
  obtain ⟨hf, hfet⟩ := h
  exact ⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f'.hom f.hom a b α).1 hf,
    relativeProperty_of_equivalences B S hS (Space.etaleMorphisms B S hS) f'.hom f.hom a b α
      hfet⟩

/-- The identity based functor of a category fibred in groupoids is an equivalence. -/
private instance isEquivalence_basedFunctor_id :
    Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))

/-- **Transport of relative étaleness along a 2-isomorphism of the 1-morphism.** Two
2-isomorphic 1-morphisms of categories fibred in groupoids over the big fppf site of `S` are
relatively étale together, in the sense of Stacks 04XB.

This is `AlgebraicGeometry.Stack.isRelativelyEtale_of_equivalences` with both horizontal
1-morphisms taken to be the identity, for which the two composites of the 2-commutative square
are the two 1-morphisms themselves. -/
theorem isRelativelyEtale_congr_twoIso {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    (h : IsRelativelyEtale B S hS f) : IsRelativelyEtale B S hS g := by
  exact isRelativelyEtale_of_equivalences B S hS g f (BasedFunctor.id 𝒳.val)
    (BasedFunctor.id 𝒴.val) (twoIsoHomIso B S hS e) h

/-- **Transport of relative étaleness along the comparison of two 2-fibre products of one
cospan.** Let `T` be a 2-commutative square over a cospan `g`, `f` of categories fibred in
groupoids over the big fppf site of `S`, and let `Q₁` and `Q₂` be two 2-fibre products of that
cospan (Stacks 003Q). If the 1-morphism underlying one morphism of 2-commutative squares
`T ⟶ Q₁` is relatively étale, then so is the one underlying any morphism of 2-commutative
squares `T ⟶ Q₂`.

Both the choice of 2-fibre product and the morphism into it are moved: the comparison of `Q₂`
with `Q₁` is an equivalence by
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, and terminality of `Q₁` makes
the composite of the given `T ⟶ Q₂` with it 2-isomorphic to the given `T ⟶ Q₁`, so
`AlgebraicGeometry.Stack.isRelativelyEtale_of_equivalences` applies with that equivalence as the
horizontal 1-morphism of targets.

This is the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_preHom_of_isTwoFibreProduct`; it is *not*
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_isTwoFibreProduct`, which asks the source
square to be a 2-fibre product as well and concludes that the comparison is étale outright. -/
theorem isRelativelyEtale_preHom_of_preHom
    {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {T Q₁ Q₂ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (hQ₂ : Bicategory.IsTwoFibreProduct Q₂)
    (k₁ : Bicategory.TwoCommSq.PreHom T Q₁) (k₂ : Bicategory.TwoCommSq.PreHom T Q₂)
    (h : IsRelativelyEtale B S hS k₁.hom) :
    IsRelativelyEtale B S hS k₂.hom := by
  -- the comparison of the two 2-fibre products, as a morphism of 2-commutative squares
  let d : Bicategory.TwoCommSq.PreHom Q₂ Q₁ := Quotient.out (hQ₁.from Q₂)
  have hd : Functor.IsEquivalence d.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQ₂ hQ₁ d
  -- terminality of `Q₁` identifies `k₂ ≫ d` with `k₁` up to a 2-isomorphism
  obtain ⟨θ, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (k₂.comp d) k₁ :=
    Quotient.exact (hQ₁.hom_ext (Quotient.mk _ (k₂.comp d)) (Quotient.mk _ k₁))
  exact isRelativelyEtale_of_equivalences B S hS k₂.hom k₁.hom (BasedFunctor.id T.pt.val)
    d.hom.hom (twoIsoHomIso B S hS θ.symm) h

/-- **The étale condition of Stacks 0CIF needs checking at a single 2-fibre product.** If one
comparison 1-morphism from a 2-commutative square `T` to one 2-fibre product of a cospan is
relatively étale, then *every* comparison 1-morphism from `T` to *every* 2-fibre product of that
cospan is relatively étale.

This is the shape in which the condition occurs in
`AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram` and
`AlgebraicGeometry.Stack.HasPropertyOnSomeEtaleSmoothDiagram`, where it is quantified over every
2-fibre product of `(b, f)` and every comparison out of the diagram's cone so that the condition
does not depend on a chosen product. -/
theorem isRelativelyEtale_preHom_of_one
    {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {T Q₁ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (k₁ : Bicategory.TwoCommSq.PreHom T Q₁)
    (h : IsRelativelyEtale B S hS k₁.hom) :
    ∀ (Q : Bicategory.TwoCommSq g f) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom T Q), IsRelativelyEtale B S hS k.hom :=
  fun _ hQ k => isRelativelyEtale_preHom_of_preHom B S hS hQ₁ hQ k₁ k h

end AlgebraicGeometry.Stack

end
