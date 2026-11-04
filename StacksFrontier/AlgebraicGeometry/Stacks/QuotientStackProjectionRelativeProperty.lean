module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# The relative property of the quotient-stack projection, from one represented base change

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `π : S_U ⟶ [U/R]` be the canonical projection of Stacks 044R
in the form `AlgebraicGeometry.Stack.quotientStackProjectionHom`, and let `P` be a property of
morphisms of algebraic spaces over `S` stable under base change and local on the target for the
fppf precoverage.

This module shows that if the first leg of some 2-fibre product of `π` with itself is, up to
equivalence, a 1-morphism of stacks that are themselves represented by algebraic spaces, then `π`
has `P` relatively as soon as the induced morphism of representing presheaves has `P`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_fst_of_isTwoFibreProduct`: the relative property
  of the first leg passes between any two 2-fibre products of one cospan.
* `AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences_representingMap`: a 1-morphism
  carried by a pair of equivalences onto a morphism of represented stacks has `P` relatively once
  the induced morphism of representing presheaves has `P`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap`: the
  first leg of *every* 2-fibre product of a cospan has `P` relatively once the first leg of *one*
  of them is equivalent to a morphism of represented stacks with `P`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_representingMap`:
  the quotient-stack projection has `P` relatively once the first leg of one 2-fibre product of
  it with itself is equivalent to a morphism of represented stacks with `P`.
* `AlgebraicGeometry.Stack.relativeProperty_fst_of_isTwoFibreProduct`,
  `AlgebraicGeometry.Stack.relativeProperty_of_equivalences_representingMap`,
  `AlgebraicGeometry.Stack.relativeProperty_fst_of_isTwoFibreProduct_representingMap` and
  `AlgebraicGeometry.Stack.relativeProperty_quotientStackProjectionHom_of_representingMap`: the
  same four for `AlgebraicGeometry.Stack.RelativeProperty`, with no witness of
  representability.
* `AlgebraicGeometry.Stack.isRelativelySmooth_quotientStackProjectionHom_of_representingMap`: the
  previous one at `AlgebraicGeometry.Space.smoothMorphismProperty`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section TwoFibreProduct

variable {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- **The relative condition on the first leg passes between two 2-fibre products of one
cospan.** If `Q₁` and `Q₂` are 2-fibre products of one cospan of categories fibred in groupoids
over the big fppf site of `S`, and the first projection of `Q₁` satisfies
`AlgebraicGeometry.Stack.RelativeProperty` at `P`, then so does the first projection of `Q₂`. -/
theorem relativeProperty_fst_of_isTwoFibreProduct
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {Q₁ Q₂ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (hQ₂ : Bicategory.IsTwoFibreProduct Q₂)
    (h : RelativeProperty.{u, v, w} B S hS P Q₁.fst) :
    RelativeProperty.{u, v, w} B S hS P Q₂.fst := by
  let d : Bicategory.TwoCommSq.PreHom Q₂ Q₁ := Quotient.out (hQ₁.from Q₂)
  have hd : Functor.IsEquivalence d.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQ₂ hQ₁ d
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒵.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒵.val.obj))
  exact relativeProperty_of_equivalences B S hS P Q₂.fst.hom Q₁.fst.hom d.hom.hom
    (BasedFunctor.id 𝒵.val) (twoIsoHomIso B S hS d.isoFst.symm) h

/-- **The relative property of the first leg passes between two 2-fibre products of one cospan.**
If `Q₁` and `Q₂` are 2-fibre products (Stacks 003Q) of one cospan of categories fibred in
groupoids over the big fppf site of `S`, and the first projection of `Q₁` has the relative
property `P` of Stacks 03YK, then so does the first projection of `Q₂`. -/
theorem hasRelativeProperty_fst_of_isTwoFibreProduct
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {Q₁ Q₂ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (hQ₂ : Bicategory.IsTwoFibreProduct Q₂)
    (h₁ : IsRepresentableByAlgebraicSpaces B S hS Q₁.fst.hom)
    (h₂ : IsRepresentableByAlgebraicSpaces B S hS Q₂.fst.hom)
    (h : HasRelativeProperty.{u, v, w} B S hS P Q₁.fst h₁) :
    HasRelativeProperty.{u, v, w} B S hS P Q₂.fst h₂ :=
  relativeProperty_fst_of_isTwoFibreProduct B S hS P hQ₁ hQ₂ h

end TwoFibreProduct

section Represented

universe v₁ w₁

/-- **The relative condition across a pair of equivalences onto a morphism of represented
stacks.** Let `f' : 𝒳' ⟶ 𝒴'` be a 1-morphism of categories fibred in groupoids over the big fppf
site of `S` carried by a pair of equivalences `p`, `q` onto a 1-morphism `a : 𝒜 ⟶ 𝒞` which is
representable by algebraic spaces and whose source and target are themselves represented by
algebraic spaces `F` and `G`. Then `f'` satisfies the condition of Stacks 03YK at `P` as soon as
the induced morphism `F ⟶ G` of representing presheaves has `P`. -/
theorem relativeProperty_of_equivalences_representingMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    (f' : 𝒳' ⟶ 𝒴')
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : 𝒳'.val ⥤ᵇ 𝒜.val) (q : 𝒴'.val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp f'.hom q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS))) :
    RelativeProperty.{u, v₁, w₁} B S hS P f' :=
  relativeProperty_of_equivalences B S hS P f'.hom a.hom p q α
    ((hasRelativeProperty_iff_prop_representingMap.{u, t} B S hS P a ha F G hF hG eF eG).mpr hprop)

/-- **The relative property across a pair of equivalences onto a morphism of represented
stacks.** Let `f' : 𝒳' ⟶ 𝒴'` be a 1-morphism of categories fibred in groupoids over the big fppf
site of `S` which is representable by algebraic spaces, and suppose it is carried by a pair of
equivalences `p`, `q` onto a 1-morphism `a : 𝒜 ⟶ 𝒞` whose source and target are themselves
represented by algebraic spaces `F` and `G`. Then `f'` has the relative property `P` of
Stacks 03YK as soon as the induced morphism `F ⟶ G` of representing presheaves has `P`. The
categories `𝒳'`, `𝒴'` may have their morphisms and objects in universes unrelated to those of
`𝒜`, `𝒞`. -/
theorem hasRelativeProperty_of_equivalences_representingMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    (f' : 𝒳' ⟶ 𝒴') (hf' : IsRepresentableByAlgebraicSpaces B S hS f'.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : 𝒳'.val ⥤ᵇ 𝒜.val) (q : 𝒴'.val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp f'.hom q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS))) :
    HasRelativeProperty.{u, v₁, w₁} B S hS P f' hf' :=
  relativeProperty_of_equivalences_representingMap B S hS P f' a ha p q α
    F G hF hG eF eG hprop

end Represented

section Chained

variable {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- **One represented 2-fibre product decides the relative condition on every first leg.** Let
`D` and `Q` be 2-fibre products of one cospan of categories fibred in groupoids over the big fppf
site of `S`. If the first projection of `Q` is carried by a pair of equivalences onto a
1-morphism `a : 𝒜 ⟶ 𝒞` of categories represented by algebraic spaces `F` and `G`, and the
induced morphism `F ⟶ G` has `P`, then the first projection of `D` satisfies the condition of
Stacks 03YK at `P`. -/
theorem relativeProperty_fst_of_isTwoFibreProduct_representingMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {D Q : Bicategory.TwoCommSq g f}
    (hD : Bicategory.IsTwoFibreProduct D) (hQ : Bicategory.IsTwoFibreProduct Q)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : 𝒵.val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS))) :
    RelativeProperty.{u, v, w} B S hS P D.fst :=
  relativeProperty_fst_of_isTwoFibreProduct B S hS P hQ hD
    (relativeProperty_of_equivalences_representingMap B S hS P Q.fst a ha
      p q α F G hF hG eF eG hprop)

/-- **One represented 2-fibre product decides the relative property of every first leg.** Let `D`
and `Q` be 2-fibre products of one cospan of categories fibred in groupoids over the big fppf
site of `S`. If the first projection of `Q` is carried by a pair of equivalences onto a
1-morphism `a : 𝒜 ⟶ 𝒞` of categories represented by algebraic spaces `F` and `G`, and the
induced morphism `F ⟶ G` has `P`, then the first projection of `D` has the relative property `P`
of Stacks 03YK. -/
theorem hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {D Q : Bicategory.TwoCommSq g f}
    (hD : Bicategory.IsTwoFibreProduct D) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hDfst : IsRepresentableByAlgebraicSpaces B S hS D.fst.hom)
    (hQfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : 𝒵.val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS))) :
    HasRelativeProperty.{u, v, w} B S hS P D.fst hDfst :=
  hasRelativeProperty_fst_of_isTwoFibreProduct B S hS P hQ hD hQfst hDfst
    (hasRelativeProperty_of_equivalences_representingMap B S hS P Q.fst hQfst a ha
      p q α F G hF hG eF eG hprop)

end Chained

section Projection

variable {A : AlgebraicSpaces B S hS}

/-- **The relative condition on the quotient-stack projection from one represented 2-fibre
product.** Let `π : S_U ⟶ [U/R]` be the canonical projection of Stacks 044R and let `P` be stable
under base change and local on the target for the fppf precoverage. Suppose some 2-fibre product
`Q` of `π` with itself has its first projection carried by a pair of equivalences onto a
1-morphism `a : 𝒜 ⟶ 𝒞` of categories represented by algebraic spaces `F` and `G`, with the
induced morphism `F ⟶ G` having `P`. Then `π` satisfies the condition of Stacks 03YK at `P`. -/
theorem relativeProperty_quotientStackProjectionHom_of_representingMap
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (F G₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG₀ : IsAlgebraicSpace B S hS G₀)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G₀ ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G₀ eF eG₀ a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G₀, hG₀⟩ : AlgebraicSpaces B S hS))) :
    RelativeProperty B S hS P (quotientStackProjectionHom G) :=
  relativeProperty_quotientStackProjectionHom_of_baseChange G P
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
      (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
      (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (relativeProperty_fst_of_isTwoFibreProduct_representingMap B S hS P
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
        (quotientStackProjectionHom G) (quotientStackProjectionHom G))
      hQ a ha p q α F G₀ hF hG₀ eF eG₀ hprop)

/-- **The relative property of the quotient-stack projection from one represented 2-fibre
product.** Let `π : S_U ⟶ [U/R]` be the canonical projection of Stacks 044R, representable by
algebraic spaces, and let `P` be stable under base change and local on the target for the fppf
precoverage. Suppose some 2-fibre product `Q` of `π` with itself has its first projection carried
by a pair of equivalences onto a 1-morphism `a : 𝒜 ⟶ 𝒞` of categories represented by algebraic
spaces `F` and `G`, with the induced morphism `F ⟶ G` having `P`. Then `π` has `P` relatively. -/
theorem hasRelativeProperty_quotientStackProjectionHom_of_representingMap
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (hf : IsRepresentableByAlgebraicSpaces B S hS (quotientStackProjectionHom G).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (F G₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG₀ : IsAlgebraicSpace B S hS G₀)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G₀ ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G₀ eF eG₀ a) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G₀, hG₀⟩ : AlgebraicSpaces B S hS))) :
    HasRelativeProperty B S hS P (quotientStackProjectionHom G) hf :=
  hasRelativeProperty_quotientStackProjectionHom_of_baseChange G P hf
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
      (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
      (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap B S hS P
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
        (quotientStackProjectionHom G) (quotientStackProjectionHom G))
      hQ _ hQfst a ha p q α F G₀ hF hG₀ eF eG₀ hprop)

/-- **Smoothness of the quotient-stack projection from one represented 2-fibre product.** The
canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R is smooth in the sense of Stacks 04XB as
soon as some 2-fibre product of `π` with itself has its first projection carried by a pair of
equivalences onto a 1-morphism of categories represented by algebraic spaces whose induced
morphism of representing presheaves is smooth. -/
theorem isRelativelySmooth_quotientStackProjectionHom_of_representingMap
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (hf : IsRepresentableByAlgebraicSpaces B S hS (quotientStackProjectionHom G).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (F G₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG₀ : IsAlgebraicSpace B S hS G₀)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G₀ ⋙ typeToCat)).p)
    (hsmooth : Space.IsSmooth B S hS (representingMap B S hS 𝒜 𝒞 F G₀ eF eG₀ a)) :
    IsRelativelySmooth B S hS (quotientStackProjectionHom G) :=
  ⟨hf, hasRelativeProperty_quotientStackProjectionHom_of_representingMap.{u, u} B S hS G
    (Space.smoothMorphismProperty B S hS) hf Q hQ hQfst a ha p q α F G₀ hF hG₀ eF eG₀ hsmooth⟩

end Projection

end AlgebraicGeometry.Stack

end
