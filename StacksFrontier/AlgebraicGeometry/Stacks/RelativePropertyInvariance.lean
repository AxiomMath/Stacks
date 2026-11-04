module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindexSnd

/-!
# The relative property of Stacks 03YK is invariant under equivalence

`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences` is **Stacks 0457**:
in a 2-commutative square of categories fibred in groupoids over the big fppf site of `S` whose
two horizontal 1-morphisms are equivalences, one vertical 1-morphism is representable by algebraic
spaces exactly when the other is. This file proves the same statement for the *relative property*
of **Stacks 03YK** — `AlgebraicGeometry.Stack.HasRelativeProperty` — and draws the two consequences
that the proof of **Stacks 06FM** needs.

The point is that the comparison is pointwise: for a scheme-valued point `y'` of `𝒴'` over a
scheme `U` over `S`, the base change of `f'` along `y'` is equivalent *over the big fppf site of
`U`* to the base change of `f` along the transported point `y' ⋙ b`. So the algebraic space whose
structural morphism the relative property tests is literally the same one on both sides, and no
hypothesis on the property is needed — not stability under base change, not locality at the
target.

The chain of comparisons is the one Stacks 0457 uses, assembled here from the three public
comparison functors rather than from file-private copies:
`CategoryTheory.TwoFibreProductOver.mapBase` postcomposes both legs with the equivalence `b` of
targets; `CategoryTheory.TwoFibreProductOver.reindexSnd` reindexes along the 2-commutativity
isomorphism; and `CategoryTheory.TwoFibreProductOver.precomposeSnd` precomposes the second leg
with the equivalence `a` of sources. Each commutes with the first projection on the nose.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalences`: the pointwise
  comparison of the two base changes.
* `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` and
  `AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences`: **Stacks 0457 for the relative
  property of Stacks 03YK**.
* `AlgebraicGeometry.Stack.isRelativelySmooth_of_equivalences`: the same at the smooth property,
  i.e. for the notion of **Stacks 04XB**.
* `AlgebraicGeometry.Stack.isRelativelySmooth_congr_twoIso`: **transport of smoothness along a
  2-isomorphism of the 1-morphism**, the case `a = b = id` of the previous result.
* `AlgebraicGeometry.Stack.isRelativelySmooth_preHom_of_isTwoFibreProduct`: **transport of
  smoothness along the comparison of two 2-fibre products of one cospan** — if one comparison
  1-morphism from a 2-commutative square into a 2-fibre product of the cospan is smooth, then so
  is every comparison 1-morphism from it into every 2-fibre product of that cospan.

## Implementation notes

The two transport results above are what condition (1) of Stacks 06FM is stated against: that
condition quantifies over *every* 2-fibre product of the cospan and *every* morphism of
2-commutative squares into it, so verifying it requires moving smoothness from one chosen
comparison to all the others, and the comparison of two 2-fibre products is only determined up to
a 2-isomorphism.

`AlgebraicGeometry.Stack.isRelativelySmooth_preHom_of_isTwoFibreProduct` needs no hypothesis on
the apex of the source square and no smoothness of the cospan: the two comparisons differ by an
equivalence, namely the comparison of the two 2-fibre products
(`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`), and transport along an
equivalence of the *target* is exactly what the result above provides. In particular it does not
go through "an equivalence is smooth", which the library does not have.

`AlgebraicGeometry.Stack.twoIsoHomIso` extracts the isomorphism of underlying based functors from
a 2-isomorphism of 1-morphisms; it is the based-functor analogue of
`CategoryTheory.CatFiberedInGroupoids.underlyingIso`, which extracts the isomorphism of the plain
underlying functors instead.

The relative property is written out as the quantifier of
`AlgebraicGeometry.Stack.HasRelativeProperty` in
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, as
`AlgebraicGeometry.Stack.relativeProperty_of_forall_nonempty_equivalenceOver_fst` already does, so
that neither instance hypothesis of that abbreviation has to be supplied; the form stated through
the abbreviation is `AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v v₁ v₂ v₃ v₄ w w₁ w₂ w₃ w₄

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The isomorphism of underlying based functors attached to a 2-isomorphism of 1-morphisms of
categories fibred in groupoids. -/
def twoIsoHomIso {𝒳 𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) : f.hom ≅ g.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.hom_inv_id
  inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.inv_hom_id

section Pointwise

variable {𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
  {𝒴' : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
  {𝒴 : CatFiberedInGroupoids.{u, v₄, u + 1, w₄} (BigFppfOver B S hS)}

/-- **The pointwise comparison behind Stacks 0457.** In a 2-commutative square whose two
horizontal 1-morphisms `a` and `b` are equivalences, the base change of `f'` along a
scheme-valued point `y'` of `𝒴'` is equivalent, over the big fppf site of the scheme the point
lives on, to the base change of `f` along the transported point `y' ⋙ b`.

The comparison is the composite of `CategoryTheory.TwoFibreProductOver.mapBase` along `b`,
`CategoryTheory.TwoFibreProductOver.reindexSnd` along the 2-commutativity isomorphism, and
`CategoryTheory.TwoFibreProductOver.precomposeSnd` along `a`. -/
theorem nonempty_equivalenceOver_fst_of_equivalences
    (f' : 𝒳'.val ⥤ᵇ 𝒴'.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f ≅ BasedFunctor.comp f' b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (U : BigFppfOver B S hS)
    (y' : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴'.val.obj)
    (hy' : y' ⋙ 𝒴'.val.p = Over.map U.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴'.val.p y' f'.toFunctor)
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p (y' ⋙ b.toFunctor)
        f.toFunctor)) := by
  have hb : b.toFunctor ⋙ 𝒴.val.p = 𝒴'.val.p := b.w
  have hG : (y' ⋙ b.toFunctor) ⋙ 𝒴.val.p = Over.map U.hom := by
    rw [Functor.assoc, hb, hy']
  have hf'b : (f'.toFunctor ⋙ b.toFunctor) ⋙ 𝒴.val.p = 𝒳'.val.p := by
    rw [Functor.assoc, hb, f'.w]
  -- (1) postcompose both legs with the equivalence `b` of targets
  obtain ⟨e₁⟩ : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴'.val.p y' f'.toFunctor)
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴.val.p (y' ⋙ b.toFunctor)
        (f'.toFunctor ⋙ b.toFunctor))) :=
    StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (fst_isFiberedInGroupoids_overMap U.hom 𝒳'.val.p 𝒴'.val.p y' f'.toFunctor
        𝒳'.isFiberedInGroupoids 𝒴'.isFiberedInGroupoids hy' f'.w)
      (fst_isFiberedInGroupoids_overMap U.hom 𝒳'.val.p 𝒴.val.p (y' ⋙ b.toFunctor)
        (f'.toFunctor ⋙ b.toFunctor) 𝒳'.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hG hf'b)
      (TwoFibreProductOver.mapBase (pT := Over.map U.hom) (p𝒜 := 𝒳'.val.p) y' f'.toFunctor
        b.toFunctor hb)
      (TwoFibreProductOver.mapBase_comp_fst (pT := Over.map U.hom) (p𝒜 := 𝒳'.val.p) y'
        f'.toFunctor b.toFunctor hb)
      (TwoFibreProductOver.isEquivalence_mapBase (pT := Over.map U.hom) (p𝒜 := 𝒳'.val.p)
        (G := y') (F := f'.toFunctor) hb)
  -- (2) reindex along the 2-commutativity isomorphism
  let α₀ : a.toFunctor ⋙ f.toFunctor ≅ f'.toFunctor ⋙ b.toFunctor :=
    (BasedNatTrans.forgetful 𝒳'.val 𝒴.val).mapIso α
  let e₂ := TwoFibreProductOver.reindexSndEquivalenceOver (p𝒳 := Over.map U.hom)
    (p𝒴 := 𝒳'.val.p) (p𝒮 := 𝒴.val.p) (F := y' ⋙ b.toFunctor) α₀.symm
    fun x => α.inv.isHomLift' x
  -- (3) precompose the second leg with the equivalence `a` of sources
  obtain ⟨e₃⟩ := nonempty_equivalenceOver_fst_of_equivalence_source B S hS a f U
    (y' ⋙ b.toFunctor) hG
  exact ⟨(e₁.trans e₂).trans e₃⟩

/-- **Stacks 0457 for the relative property of Stacks 03YK.** In a 2-commutative square of
categories fibred in groupoids over the big fppf site of `S` whose two horizontal 1-morphisms
are equivalences, the relative property at `P` passes from one vertical 1-morphism to the other.

No hypothesis on `P` is used: by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalences` the algebraic space whose
structural morphism is tested at a point `y'` of `𝒴'` is one of those tested at the transported
point `y' ⋙ b` of `𝒴`. The property is written out as the quantifier of
`AlgebraicGeometry.Stack.HasRelativeProperty` so that neither of its instance hypotheses has to
be in scope. -/
theorem relativeProperty_of_equivalences (P : MorphismProperty (AlgebraicSpaces B S hS))
    (f' : 𝒳'.val ⥤ᵇ 𝒴'.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f ≅ BasedFunctor.comp f' b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y' : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴'.val.obj)
      (_hy' : y' ⋙ 𝒴'.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴'.val.p y' f'.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  rintro U y' hy' F hF ⟨E⟩
  obtain ⟨k⟩ := nonempty_equivalenceOver_fst_of_equivalences B S hS f' f a b α U y' hy'
  exact hP U (y' ⋙ b.toFunctor) (by rw [Functor.assoc, b.w, hy']) F hF ⟨k.symm.trans E⟩

end Pointwise

section Transport

variable {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` stated through the abbreviation
`AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK. The two instance hypotheses of that
abbreviation are not used by the argument; they are in scope because the statement mentions it. -/
theorem hasRelativeProperty_of_equivalences (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f.hom ≅ BasedFunctor.comp f'.hom b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hf' : IsRepresentableByAlgebraicSpaces B S hS f'.hom)
    (h : HasRelativeProperty.{u, v₂, w₂} B S hS P f hf) :
    HasRelativeProperty.{u, v₁, w₁} B S hS P f' hf' :=
  relativeProperty_of_equivalences B S hS P f'.hom f.hom a b α h

/-- **Stacks 0457 at the smooth property of Stacks 04XB.** In a 2-commutative square of
categories fibred in groupoids over the big fppf site of `S` whose two horizontal 1-morphisms are
equivalences, one vertical 1-morphism is smooth exactly when the other is. Representability by
algebraic spaces transports by Stacks 0457 itself. -/
theorem isRelativelySmooth_of_equivalences
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f.hom ≅ BasedFunctor.comp f'.hom b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (h : IsRelativelySmooth.{u, v₂, w₂} B S hS f) :
    IsRelativelySmooth.{u, v₁, w₁} B S hS f' :=
  ⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f'.hom f.hom a b α).1 h.1,
    relativeProperty_of_equivalences B S hS (Space.smoothMorphismProperty B S hS) f'.hom f.hom
      a b α h.2⟩

end Transport

section TwoIso

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- Smoothness transports along an equivalence of targets `b` once the source equivalence is the
identity. -/
private theorem isRelativelySmooth_of_isEquivalence_target
    {𝒳 𝒴' 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f' : 𝒳 ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : f.hom ≅ BasedFunctor.comp f'.hom b) [Functor.IsEquivalence b.toFunctor]
    (h : IsRelativelySmooth.{u, v, w} B S hS f) : IsRelativelySmooth.{u, v, w} B S hS f' :=
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  isRelativelySmooth_of_equivalences B S hS f' f (BasedFunctor.id 𝒳.val) b α h

/-- **Transport of smoothness along a 2-isomorphism of the 1-morphism.** Two 2-isomorphic
1-morphisms of categories fibred in groupoids over the big fppf site of `S` are smooth together,
in the sense of Stacks 04XB.

This is `AlgebraicGeometry.Stack.isRelativelySmooth_of_equivalences` with both horizontal
1-morphisms taken to be the identity, for which the two composites of the 2-commutative square
are the two 1-morphisms themselves. -/
theorem isRelativelySmooth_congr_twoIso {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    (h : IsRelativelySmooth.{u, v, w} B S hS f) : IsRelativelySmooth.{u, v, w} B S hS g := by
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒴.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.obj))
  exact isRelativelySmooth_of_isEquivalence_target B S hS g f (BasedFunctor.id 𝒴.val)
    (twoIsoHomIso B S hS e) h

/-- **Transport of smoothness along the comparison of two 2-fibre products of one cospan.** Let
`T` be a 2-commutative square over a cospan `g`, `f` of categories fibred in groupoids over the
big fppf site of `S`, and let `Q₁` and `Q₂` be two 2-fibre products of that cospan (Stacks 003Q).
If the 1-morphism underlying one morphism of 2-commutative squares `T ⟶ Q₁` is smooth, then so is
the one underlying any morphism of 2-commutative squares `T ⟶ Q₂`.

Both the choice of 2-fibre product and the morphism into it are moved: the comparison of `Q₂`
with `Q₁` is an equivalence by
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, and terminality of `Q₁` makes the
composite of the given `T ⟶ Q₂` with it 2-isomorphic to the given `T ⟶ Q₁`, so
`AlgebraicGeometry.Stack.isRelativelySmooth_of_equivalences` applies with that equivalence as the
horizontal 1-morphism of targets. -/
theorem isRelativelySmooth_preHom_of_isTwoFibreProduct {𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    {T Q₁ Q₂ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (hQ₂ : Bicategory.IsTwoFibreProduct Q₂)
    (k₁ : Bicategory.TwoCommSq.PreHom T Q₁) (k₂ : Bicategory.TwoCommSq.PreHom T Q₂)
    (h : IsRelativelySmooth.{u, v, w} B S hS k₁.hom) :
    IsRelativelySmooth.{u, v, w} B S hS k₂.hom := by
  -- the comparison of the two 2-fibre products, as a morphism of 2-commutative squares
  let d : Bicategory.TwoCommSq.PreHom Q₂ Q₁ := Quotient.out (hQ₁.from Q₂)
  have hd : Functor.IsEquivalence d.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQ₂ hQ₁ d
  -- terminality of `Q₁` identifies `k₂ ≫ d` with `k₁` up to a 2-isomorphism
  obtain ⟨θ, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (k₂.comp d) k₁ :=
    Quotient.exact (hQ₁.hom_ext (Quotient.mk _ (k₂.comp d)) (Quotient.mk _ k₁))
  exact isRelativelySmooth_of_isEquivalence_target B S hS k₂.hom k₁.hom d.hom.hom
    (twoIsoHomIso B S hS θ.symm) h

end TwoIso

end AlgebraicGeometry.Stack

end
