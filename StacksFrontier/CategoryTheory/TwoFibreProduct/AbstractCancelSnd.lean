module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# Cancelling the second factor at a recognised 2-fibre product (Stacks 02XD)

Fix a base category `C` and a cospan `p : 𝒜 ⟶ 𝒳`, `q : ℬ ⟶ 𝒳` of categories fibred in groupoids
over `C`. `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare` — Stacks 02XD
read as a statement about 2-fibre products — is stated for the *canonical* apex of Stacks 003Q: its
iterated apex is spelled `((𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰)` with `𝒜 ×_𝒳 ℬ` the canonical
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`. A consumer which has recognised some
*other* category `𝒲` as a 2-fibre product of `(p, q)` — by a theorem rather than by construction,
as `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare` does for a triple
product — cannot use that statement at `𝒲 ×_ℬ 𝒰` at all.

This file supplies the cancellation there. The input is a comparison 1-morphism
`cmp : 𝒲 ⟶ 𝒜 ×_𝒳 ℬ` into the canonical apex whose underlying functor is an equivalence of
categories; the conclusion is that `𝒲 ×_{cmp ≫ pr₂, ℬ, c} 𝒰` is a 2-fibre product of the cospan
`(p, G)` for any `c : 𝒰 ⟶ ℬ` and any `G : 𝒰 ⟶ 𝒳` identified with `c ≫ q` by an invertible 2-cell:

```text
𝒲 ×_ℬ 𝒰  ≃  𝒜 ×_𝒳 𝒰
```

with the first leg the composite of the outer projection with `cmp ≫ pr₁` and the second leg the
outer projection to `𝒰`.

Also recorded here, because every consumer of the above needs it: the comparison of an arbitrary
2-commutative square with the canonical 2-fibre product square has *identity* comparison 2-cells,
`CategoryTheory.CatFiberedInGroupoids.canonicalPreHom`. That is the pre-morphism built from
`CategoryTheory.TwoFibreProductOver.lift`, and it is the only way to name a comparison into a
2-fibre product whose composites with the two projections are the legs of the source square *on the
nose* rather than up to a 2-cell.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom`: the strict comparison of a
  2-commutative square with the canonical 2-fibre product square.
* `CategoryTheory.CatFiberedInGroupoids.cancelSndEquivSquare`: the outer product
  `𝒲 ×_ℬ 𝒰`, read as a 2-commutative square over the cospan `(p, G)`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom_comp_fst` and `canonicalPreHom_comp_snd`:
  the strict compatibilities of that comparison with the two projections.
* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare`: the outer
  product is a 2-fibre product of `(p, G)`.

## Implementation notes

Nothing is re-proved. The comparison functor is
`CategoryTheory.TwoFibreProductOver.precomposeFst` along `cmp`, which is an equivalence as soon as
`cmp` is and which is strictly compatible with both outer projections — composing it with the first
projection is the first projection followed by `cmp`, and with the second projection is the second
projection, both on the nose. So the comparison is a pre-morphism of 2-commutative squares with
*identity* comparison 2-cells, its Stacks 003O compatibility square is the componentwise identity,
and `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` transports terminality from
`CategoryTheory.CatFiberedInGroupoids.cancelSndSquare`. The filler is defined as the filler of that
square read through the comparison, for the reason recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct`: written that way the two
legs it compares are definitionally the composites of the comparison with the legs of that square.
No 2-cell algebra occurs.

No `@[stacks 02XD]` attribute: that tag stays on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation`, as the records of the two cancellation
files already rule for their own statements.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒜 ℬ 𝒳 𝒰 𝒲 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

section Canonical

variable (p : 𝒜 ⟶ 𝒳) (q : ℬ ⟶ 𝒳)

/-- **The strict comparison of a 2-commutative square with the canonical 2-fibre product
square.** Its underlying 1-morphism is the canonical lift
`CategoryTheory.TwoFibreProductOver.lift`, whose composites with the two projections of the
canonical square are the two legs of the given square *on the nose*; both comparison 2-cells are
therefore identities and the Stacks 003O compatibility square is the componentwise identity. -/
def canonicalPreHom (T : Bicategory.TwoCommSq p q) :
    Bicategory.TwoCommSq.PreHom T (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q) where
  hom := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.lift 𝒜.val.p ℬ.val.p 𝒳.val.p
        p.hom.toFunctor q.hom.toFunctor T.pt.val.p
        T.fst.hom.toFunctor T.snd.hom.toFunctor T.fst.hom.w T.snd.hom.w
        (underlyingIso T.iso) (fun x => T.iso.hom.hom.isHomLift' x)
      w := TwoFibreProductOver.lift_comp_structureFunctor .. }
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ ?_)
    ext x
    exact map_id_comp_id_eq p.hom.toFunctor q.hom.toFunctor (T.iso.hom.hom.toNatTrans.app x)

/-- **The strict comparison is faithful as soon as the given square's second leg is.** Being the
canonical lift of Stacks 0040, its second component is that leg;
`CategoryTheory.TwoFibreProductOver.faithful_lift`. -/
instance faithful_canonicalPreHom (T : Bicategory.TwoCommSq p q)
    [T.snd.hom.toFunctor.Faithful] :
    (canonicalPreHom.{v₁, v₂, u₁, u₂} p q T).hom.hom.toFunctor.Faithful :=
  TwoFibreProductOver.faithful_lift 𝒜.val.p ℬ.val.p 𝒳.val.p p.hom.toFunctor q.hom.toFunctor
    T.pt.val.p T.fst.hom.toFunctor T.snd.hom.toFunctor T.fst.hom.w T.snd.hom.w
    (underlyingIso T.iso) (fun x => T.iso.hom.hom.isHomLift' x)

/-- **The strict comparison is full as soon as the given square's second leg is full and faithful
and the cospan's first leg is faithful.** This is
`CategoryTheory.TwoFibreProductOver.full_lift`. -/
instance full_canonicalPreHom (T : Bicategory.TwoCommSq p q)
    [T.snd.hom.toFunctor.Full] [T.snd.hom.toFunctor.Faithful] [p.hom.toFunctor.Faithful] :
    (canonicalPreHom.{v₁, v₂, u₁, u₂} p q T).hom.hom.toFunctor.Full :=
  TwoFibreProductOver.full_lift 𝒜.val.p ℬ.val.p 𝒳.val.p p.hom.toFunctor q.hom.toFunctor
    T.pt.val.p T.fst.hom.toFunctor T.snd.hom.toFunctor T.fst.hom.w T.snd.hom.w
    (underlyingIso T.iso) (fun x => T.iso.hom.hom.isHomLift' x)

/-- **The strict comparison is essentially surjective when objects lift.** The hypothesis is the
object-lifting datum of `CategoryTheory.TwoFibreProductOver.essSurj_lift`: every object of the
canonical 2-fibre product is, over its own base, the image of an object of the given square's
apex. -/
lemma essSurj_canonicalPreHom (T : Bicategory.TwoCommSq p q)
    (hsurj : ∀ P : TwoFibreProductOver 𝒜.val.p ℬ.val.p 𝒳.val.p p.hom.toFunctor q.hom.toFunctor,
      ∃ (w : T.pt.val.obj) (ι : T.fst.hom.toFunctor.obj w ≅ P.x)
        (κ : T.snd.hom.toFunctor.obj w ≅ P.y),
        𝒜.val.p.IsHomLift (𝟙 P.base) ι.hom ∧ ℬ.val.p.IsHomLift (𝟙 P.base) κ.hom ∧
          p.hom.toFunctor.map ι.hom ≫ P.iso.hom =
            (underlyingIso T.iso).hom.app w ≫ q.hom.toFunctor.map κ.hom) :
    (canonicalPreHom.{v₁, v₂, u₁, u₂} p q T).hom.hom.toFunctor.EssSurj :=
  TwoFibreProductOver.essSurj_lift 𝒜.val.p ℬ.val.p 𝒳.val.p p.hom.toFunctor q.hom.toFunctor
    T.pt.val.p T.fst.hom.toFunctor T.snd.hom.toFunctor T.fst.hom.w T.snd.hom.w
    (underlyingIso T.iso) (fun x => T.iso.hom.hom.isHomLift' x) hsurj

/-- **The strict comparison of a 2-commutative square with the canonical 2-fibre product square is
an equivalence of the underlying categories** when the square's second leg is full and faithful,
the cospan's first leg is faithful, and objects lift. With
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` this recognises the square as a
2-fibre product of its cospan. -/
lemma isEquivalence_canonicalPreHom (T : Bicategory.TwoCommSq p q)
    [T.snd.hom.toFunctor.Full] [T.snd.hom.toFunctor.Faithful] [p.hom.toFunctor.Faithful]
    (hsurj : ∀ P : TwoFibreProductOver 𝒜.val.p ℬ.val.p 𝒳.val.p p.hom.toFunctor q.hom.toFunctor,
      ∃ (w : T.pt.val.obj) (ι : T.fst.hom.toFunctor.obj w ≅ P.x)
        (κ : T.snd.hom.toFunctor.obj w ≅ P.y),
        𝒜.val.p.IsHomLift (𝟙 P.base) ι.hom ∧ ℬ.val.p.IsHomLift (𝟙 P.base) κ.hom ∧
          p.hom.toFunctor.map ι.hom ≫ P.iso.hom =
            (underlyingIso T.iso).hom.app w ≫ q.hom.toFunctor.map κ.hom) :
    (canonicalPreHom.{v₁, v₂, u₁, u₂} p q T).hom.hom.toFunctor.IsEquivalence :=
  { full := full_canonicalPreHom.{v₁, v₂, u₁, u₂} p q T
    faithful := faithful_canonicalPreHom.{v₁, v₂, u₁, u₂} p q T
    essSurj := essSurj_canonicalPreHom.{v₁, v₂, u₁, u₂} p q T hsurj }

/-- The strict comparison of `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom` composed with
the first projection of the canonical square is the first leg of the given square. -/
theorem canonicalPreHom_comp_fst (T : Bicategory.TwoCommSq p q) :
    (canonicalPreHom.{v₁, v₂, u₁, u₂} p q T).hom ≫
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).fst = T.fst := rfl

/-- The strict comparison of `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom` composed with
the second projection of the canonical square is the second leg of the given square. -/
theorem canonicalPreHom_comp_snd (T : Bicategory.TwoCommSq p q) :
    (canonicalPreHom.{v₁, v₂, u₁, u₂} p q T).hom ≫
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd = T.snd := rfl

end Canonical

section CancelSnd

variable (p : 𝒜 ⟶ 𝒳) (q : ℬ ⟶ 𝒳)
  (cmp : 𝒲 ⟶ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).pt)
  (c : 𝒰 ⟶ ℬ) (G : 𝒰 ⟶ 𝒳) (θ : c ≫ q ≅ G)

/-- The comparison functor of the cancellation at a recognised 2-fibre product: changing the first
factor of the outer product along `cmp`. -/
def cancelSndEquivFunctor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (cmp ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd) c).pt.val.obj ⥤
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd c).pt.val.obj :=
  TwoFibreProductOver.precomposeFst 𝒲.val.p
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).pt.val.p 𝒰.val.p ℬ.val.p
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd.hom.toFunctor
    c.hom.toFunctor cmp.hom.toFunctor cmp.hom.w

/-- `CategoryTheory.CatFiberedInGroupoids.cancelSndEquivFunctor` is an equivalence of categories
as soon as the comparison `cmp` is: changing the first factor of a 2-fibre product over `C` along
an equivalence over `C` is an equivalence. -/
theorem isEquivalence_cancelSndEquivFunctor (hcmp : cmp.hom.toFunctor.IsEquivalence) :
    (cancelSndEquivFunctor.{v₁, v₂, u₁, u₂} p q cmp c).IsEquivalence :=
  TwoFibreProductOver.isEquivalence_precomposeFst 𝒲.val.p
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).pt.val.p 𝒰.val.p ℬ.val.p
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd.hom.toFunctor
    c.hom.toFunctor cmp.hom.toFunctor cmp.hom.w
    𝒰.isFiberedInGroupoids 𝒲.isFiberedInGroupoids
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).pt.isFiberedInGroupoids hcmp
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd.hom.w

/-- The comparison 1-morphism of the cancellation at a recognised 2-fibre product, read in the
2-category of categories fibred in groupoids: `𝒲 ×_ℬ 𝒰 ⟶ (𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰`. -/
def cancelSndEquivMor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (cmp ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd) c).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd c).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := cancelSndEquivFunctor.{v₁, v₂, u₁, u₂} p q cmp c
      w := TwoFibreProductOver.precomposeFst_comp_structureFunctor .. }

/-- The cospan `(p, G)` read on the outer product `𝒲 ×_ℬ 𝒰`: the projection to `𝒜` is the
composite of the outer projection with `cmp ≫ pr₁`, and the projection to `𝒰` is the outer one.

The filler is the filler of `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare` read through
the comparison `CategoryTheory.CatFiberedInGroupoids.cancelSndEquivMor`; written this way the two
legs it compares are *definitionally* the composites of the comparison with the legs of that
square, which is what makes the compatibility square of Stacks 003O hold with identity comparison
2-cells. -/
def cancelSndEquivSquare : Bicategory.TwoCommSq p G where
  pt := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (cmp ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd) c).pt
  fst := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (cmp ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd) c).fst ≫
    (cmp ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).fst)
  snd := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (cmp ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd) c).snd
  iso := Bicategory.whiskerLeftIso (cancelSndEquivMor.{v₁, v₂, u₁, u₂} p q cmp c)
    (cancelSndSquare.{v₁, v₂, u₁, u₂} p q c G θ).iso

/-- The comparison, as a pre-morphism of 2-commutative squares over the cospan `(p, G)`. Both
comparison 2-cells are identities, by the nose-compatibility of
`CategoryTheory.TwoFibreProductOver.precomposeFst` with the two outer projections. -/
def cancelSndEquivPreHom :
    Bicategory.TwoCommSq.PreHom (cancelSndEquivSquare.{v₁, v₂, u₁, u₂} p q cmp c G θ)
      (cancelSndSquare.{v₁, v₂, u₁, u₂} p q c G θ) where
  hom := cancelSndEquivMor.{v₁, v₂, u₁, u₂} p q cmp c
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext X
    change (cancelSndSquare.{v₁, v₂, u₁, u₂} p q c G θ).iso.hom.hom.toNatTrans.app
          ((cancelSndEquivFunctor.{v₁, v₂, u₁, u₂} p q cmp c).obj X) ≫
        G.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _
      = p.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
        (cancelSndSquare.{v₁, v₂, u₁, u₂} p q c G θ).iso.hom.hom.toNatTrans.app
          ((cancelSndEquivFunctor.{v₁, v₂, u₁, u₂} p q cmp c).obj X)
    exact map_id_comp_id_eq p.hom.toFunctor G.hom.toFunctor _

/-- **Stacks 02XD at a recognised 2-fibre product.** Let `𝒲` be comparable to the canonical
2-fibre product `𝒜 ×_𝒳 ℬ` by a 1-morphism `cmp` whose underlying functor is an equivalence of
categories. Then the outer product `𝒲 ×_ℬ 𝒰`, with the composite of its outer projection and
`cmp ≫ pr₁` to `𝒜` and its own outer projection to `𝒰`, is a 2-fibre product of the cospan
`p : 𝒜 ⟶ 𝒳`, `G : 𝒰 ⟶ 𝒳`. -/
noncomputable def isTwoFibreProduct_cancelSndEquivSquare (hcmp : cmp.hom.toFunctor.IsEquivalence) :
    Bicategory.IsTwoFibreProduct (cancelSndEquivSquare.{v₁, v₂, u₁, u₂} p q cmp c G θ) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_cancelSndSquare.{v₁, v₂, u₁, u₂} p q c G θ)
    (cancelSndEquivPreHom.{v₁, v₂, u₁, u₂} p q cmp c G θ)
    (isEquivalence_cancelSndEquivFunctor.{v₁, v₂, u₁, u₂} p q cmp c hcmp)

end CancelSnd

end CategoryTheory.CatFiberedInGroupoids

end
