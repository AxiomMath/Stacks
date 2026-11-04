module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComposable
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognition

/-!
# The triple 2-fibre product as a product over its second factor (Stacks 02XC, 04S7)

Fix a base category `C` and three 1-morphisms `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴`, `b : 𝒱 ⟶ 𝒴` of
categories fibred in groupoids over `C`, and write `𝒯 = (𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)` for the triple
product glued along the first factor of both halves.
`StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognition` exhibits `𝒯` as a 2-fibre
product of the cospan `(𝒵 ×_𝒴 𝒳 ⟶ 𝒳, 𝒱 ×_𝒴 𝒳 ⟶ 𝒳)`, with its own projection to `𝒵 ×_𝒴 𝒳` as
the first leg and the pairing `CategoryTheory.CatFiberedInGroupoids.triplePairingMor` as the
second.

This file does the same for the *other* projection:

```text
(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)   is a 2-fibre product of   (𝒵 ×_𝒴 𝒱 ⟶ 𝒱 , 𝒱 ×_𝒴 𝒳 ⟶ 𝒱)
```

with the projection to `𝒵 ×_𝒴 𝒱` as the first leg and *the same pairing* as the second. The two
statements together are what makes a morphism into `𝒯` recognisable as a base change compatibly
with **both** of `𝒯`'s projections, which is what the étale clause of Stacks 0CIF needs: it is the
first that turns the base change into a surjection onto `𝒵 ×_𝒴 𝒳` and the second that turns it
into a morphism with the given property over `𝒵 ×_𝒴 𝒱`, and both have to be read off one apex.

The target of the comparison is the composable-pair category
`CategoryTheory.TwoFibreProductOver.ComposablePairCat` of
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverComposable`, which is literally
`(𝒵 ×_𝒴 𝒱) ×_𝒱 (𝒱 ×_𝒴 𝒳)` — glued along the second projection of its first factor and the first
projection of its second — so no new apex is introduced.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.gluedComparisonSnd`: the comparison
  `(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⥤ (𝒵 ×_𝒴 𝒱) ×_𝒱 (𝒱 ×_𝒴 𝒳)`, which keeps the *second* half untouched
  and replaces the first by the pairing.
* `CategoryTheory.CatFiberedInGroupoids.tripleProductMorSnd`: that comparison, in the 2-category.
* `CategoryTheory.CatFiberedInGroupoids.tripleProductSndSquare`: the 2-commutative square whose
  apex is `(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`, whose first leg is its own projection to `𝒵 ×_𝒴 𝒱` and
  whose second leg is the pairing.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_gluedComparisonSnd`: the comparison is an
  equivalence of categories.
* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSndSquare`: that square is
  a 2-fibre product of `(𝒵 ×_𝒴 𝒱 ⟶ 𝒱, 𝒱 ×_𝒴 𝒳 ⟶ 𝒱)`.

## Implementation notes

The comparison is written out by hand rather than assembled, and the reason is a bracketing. The
assembled candidate — exchange the two halves, apply
`CategoryTheory.TwoFibreProductOver.gluedComparison` with the roles of `𝒳` and `𝒱` exchanged, then
exchange the two factors of the resulting second half — is an equivalence, but its composite with
the second projection is the pairing only up to `CategoryTheory.Category.assoc`: splicing three
comparison isomorphisms and then inverting the splice twice re-brackets them. The whole point of
these statements is that the second leg is the pairing *on the nose*, since both recognitions must
be read at one and the same apex `𝒯 ×_{𝒱 ×_𝒴 𝒳} 𝒰`. So the comparison is defined directly, with
`CategoryTheory.TwoFibreProductOver.gluedPairing` as its second component and the identity as its
gluing isomorphism, and the assembled candidate is then used only to prove it is an equivalence,
through a natural isomorphism all of whose components are identities on both factors.

Everything else is strict: all three of `gluedComparisonSnd_comp_fst`, `_comp_snd` and
`_comp_structureFunctor` hold by `rfl`, the filler of `tripleProductSndSquare` is the identity
2-cell because the two legs it compares are the same functor on the nose, and the Stacks 003O
compatibility square of the pre-morphism is the one-line
`CategoryTheory.CatFiberedInGroupoids.map_id_comp_id_eq`. Terminality is transported by
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`. No 2-cell algebra occurs.

The one transparency attribute is minimal, checked by removing each candidate:
`attribute [local implicit_reducible] fst` is required — without it the `change` in
`CategoryTheory.TwoFibreProductOver.gluedComparisonSndAltIsoApp` leaves `simp` with an unsolved
goal — while `snd`, `structureFunctor` and a per-declaration `@[implicit_reducible]` on the
comparison are not, the file compiling with no diagnostics once they are dropped. The round-trip
`Functor.map_id` obstruction recorded for the sibling construction does not arise here, because the
equivalence is obtained from a composite of three existing equivalences rather than from a
hand-built quasi-inverse, so no object of a round trip is ever read.

Nothing here carries a `@[stacks]` attribute, for the reasons recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognition`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XC](https://stacks.math.columbia.edu/tag/02XC)
* [Stacks Project, Tag 04S7](https://stacks.math.columbia.edu/tag/04S7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

universe vC vZ vX vV vY uC uZ uX uV uY

attribute [local implicit_reducible] fst

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒵 : Type uZ} [Category.{vZ} 𝒵]
  {𝒳 : Type uX} [Category.{vX} 𝒳] {𝒱 : Type uV} [Category.{vV} 𝒱]
  {𝒴 : Type uY} [Category.{vY} 𝒴]

variable {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒱 : 𝒱 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞}
  {G : 𝒵 ⥤ 𝒴} {F : 𝒳 ⥤ 𝒴} {H : 𝒱 ⥤ 𝒴}

/-- **The comparison that keeps the second half**,
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⥤ (𝒵 ×_𝒴 𝒱) ×_𝒱 (𝒱 ×_𝒴 𝒳)`: it keeps the second half untouched,
replaces the first half by the pairing `CategoryTheory.TwoFibreProductOver.gluedPairing`, and
takes the identity of `v` as the new gluing isomorphism. -/
def gluedComparisonSnd (hG : G ⋙ p𝒴 = p𝒵) :
    gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H ⥤ ComposablePairCat p𝒵 p𝒱 p𝒳 p𝒴 G H F where
  obj P :=
    { base := P.base
      x := P.y
      y := (gluedPairing hG).obj P
      hx := P.hy
      hy := rfl
      iso := Iso.refl P.y.y
      vertical := IsHomLift.id (P.y.hy.trans P.hy) }
  map {P Q} φ :=
    { hbase := φ.hbase
      a := φ.b
      b := (gluedPairing hG).map φ
      ha := φ.hb
      hb := structureFunctor_isHomLift _ φ.hbase (isHomLift_b φ.b φ.hbase φ.hb)
      w := (by rw [Category.comp_id, Category.id_comp] :
        φ.b.b ≫ 𝟙 Q.y.y = 𝟙 P.y.y ≫ φ.b.b) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison is strictly compatible with the projections to `𝒵 ×_𝒴 𝒱`. -/
@[simp] lemma gluedComparisonSnd_comp_fst (hG : G ⋙ p𝒴 = p𝒵) :
    gluedComparisonSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG ⋙
      fst (structureFunctor p𝒵 p𝒱 p𝒴 G H) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒱
        (snd p𝒵 p𝒱 p𝒴 G H) (fst p𝒱 p𝒳 p𝒴 H F) =
    snd (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) := rfl

/-- The comparison followed by the projection to `𝒱 ×_𝒴 𝒳` is the pairing. -/
@[simp] lemma gluedComparisonSnd_comp_snd (hG : G ⋙ p𝒴 = p𝒵) :
    gluedComparisonSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG ⋙
      snd (structureFunctor p𝒵 p𝒱 p𝒴 G H) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒱
        (snd p𝒵 p𝒱 p𝒴 G H) (fst p𝒱 p𝒳 p𝒴 H F) =
    gluedPairing (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
      (G := G) (F := F) (H := H) hG := rfl

/-- The comparison is strictly over `𝒞`. -/
@[simp] lemma gluedComparisonSnd_comp_structureFunctor (hG : G ⋙ p𝒴 = p𝒵) :
    gluedComparisonSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG ⋙
      structureFunctor (structureFunctor p𝒵 p𝒱 p𝒴 G H) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒱
        (snd p𝒵 p𝒱 p𝒴 G H) (fst p𝒱 p𝒳 p𝒴 H F) =
    structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) := rfl

section Equivalence

variable (hpZ : p𝒵.IsFiberedInGroupoids) (hpX : p𝒳.IsFiberedInGroupoids)
  (hpV : p𝒱.IsFiberedInGroupoids) (hpY : p𝒴.IsFiberedInGroupoids)
  (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳) (hH : H ⋙ p𝒴 = p𝒱)

/-- The first step of the assembled candidate: exchange the two halves of the triple product. -/
noncomputable def gluedExchange :
    gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H ⥤ gluedAlongFirst p𝒵 p𝒱 p𝒳 p𝒴 G H F :=
  swap (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
    (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H)

/-- The last step of the assembled candidate: exchange the two factors of the second half. -/
noncomputable def gluedExchangeSnd :
    gluedAlongSecond p𝒵 p𝒱 p𝒳 p𝒴 G H F ⥤ ComposablePairCat p𝒵 p𝒱 p𝒳 p𝒴 G H F :=
  precomposeSnd (pT := structureFunctor p𝒵 p𝒱 p𝒴 G H) (pℬ := p𝒱)
    (snd p𝒵 p𝒱 p𝒴 G H) (fst p𝒱 p𝒳 p𝒴 H F)
    (swap p𝒳 p𝒱 p𝒴 F H) (swap_comp_structureFunctor ..)

/-- **The assembled candidate for the comparison.** It is an equivalence, but its composite with
the second projection is the pairing only up to re-bracketing, which is why
`CategoryTheory.TwoFibreProductOver.gluedComparisonSnd` is written out instead. -/
noncomputable def gluedComparisonSndAlt :
    gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H ⥤ ComposablePairCat p𝒵 p𝒱 p𝒳 p𝒴 G H F :=
  gluedExchange ⋙
    gluedComparison (p𝒵 := p𝒵) (p𝒳 := p𝒱) (p𝒱 := p𝒳) (p𝒴 := p𝒴)
      (G := G) (F := H) (H := F) hG ⋙
    gluedExchangeSnd

include hpZ hpX hpV hpY hF hH in
/-- The assembled candidate is an equivalence: each of its three factors is. -/
theorem isEquivalence_gluedComparisonSndAlt :
    (gluedComparisonSndAlt (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
      (G := G) (F := F) (H := H) hG).IsEquivalence := by
  have h₁ : (gluedExchange (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
      (G := G) (F := F) (H := H)).IsEquivalence :=
    inferInstanceAs (Functor.IsEquivalence (swap ..))
  have h₂ := isEquivalence_gluedComparison (p𝒵 := p𝒵) (p𝒳 := p𝒱) (p𝒱 := p𝒳) (p𝒴 := p𝒴)
    (G := G) (F := H) (H := F) hG hH
  have hsw : (swap p𝒳 p𝒱 p𝒴 F H).IsEquivalence := inferInstance
  have h₃ : (gluedExchangeSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
      (G := G) (F := F) (H := H)).IsEquivalence :=
    isEquivalence_precomposeSnd' (pT' := structureFunctor p𝒳 p𝒱 p𝒴 F H)
      (pT := structureFunctor p𝒱 p𝒳 p𝒴 H F) (p𝒜 := structureFunctor p𝒵 p𝒱 p𝒴 G H)
      (pℬ := p𝒱) (Gl := fst p𝒱 p𝒳 p𝒴 H F) (Fl := snd p𝒵 p𝒱 p𝒴 G H)
      (t := swap p𝒳 p𝒱 p𝒴 F H) (ht := swap_comp_structureFunctor ..)
      (isFiberedInGroupoids p𝒳 p𝒱 p𝒴 F H hpX hpV hpY hF hH)
      (isFiberedInGroupoids p𝒱 p𝒳 p𝒴 H F hpV hpX hpY hH hF)
      (isFiberedInGroupoids p𝒵 p𝒱 p𝒴 G H hpZ hpV hpY hG hH) hsw fst_comp_eq
  exact inferInstanceAs (Functor.IsEquivalence (_ ⋙ _ ⋙ _))

include hG in
/-- The component at `P` of the natural isomorphism between the comparison and the assembled
candidate: the identity on both factors, the two objects differing only in the bracketing of the
three spliced comparison isomorphisms. -/
noncomputable def gluedComparisonSndAltIsoApp (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    (gluedComparisonSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG).obj P ≅
      (gluedComparisonSndAlt (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG).obj P := by
  refine isoMkVertical (U := P.base) (Iso.refl P.y)
    (isoMkVertical (U := P.base) (Iso.refl P.y.y) (Iso.refl P.x.y)
      (IsHomLift.id (P.y.hy.trans P.hy)) (IsHomLift.id (P.x.hy.trans P.hx)) ?_)
    (IsHomLift.id P.hy)
    (structureFunctor_isHomLift _ (𝟙 P.base) (IsHomLift.id (P.y.hy.trans P.hy))) ?_
  · change H.map (𝟙 P.y.y) ≫
        (P.x.iso.symm ≪≫ (G.mapIso P.iso.symm).symm ≪≫ P.y.iso).symm.hom
      = (P.y.iso.symm ≪≫ (G.mapIso P.iso).symm ≪≫ P.x.iso).hom ≫ F.map (𝟙 P.x.y)
    simp
  · rfl

include hG in
/-- The comparison and the assembled candidate are naturally isomorphic. -/
noncomputable def gluedComparisonSndAltIso :
    gluedComparisonSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG ≅
      gluedComparisonSndAlt (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
        (G := G) (F := F) (H := H) hG :=
  NatIso.ofComponents (gluedComparisonSndAltIsoApp hG) (fun {P Q} φ =>
    Hom.ext' (show φ.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ φ.b by simp)
      (Hom.ext' (show φ.b.b ≫ 𝟙 Q.y.y = 𝟙 P.y.y ≫ φ.b.b by simp)
        (show φ.a.b ≫ 𝟙 Q.x.y = 𝟙 P.x.y ≫ φ.a.b by simp)))

include hpZ hpX hpV hpY hF hH in
/-- The comparison that keeps the second half is an equivalence of categories. -/
theorem isEquivalence_gluedComparisonSnd :
    (gluedComparisonSnd (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
      (G := G) (F := F) (H := H) hG).IsEquivalence := by
  have h := isEquivalence_gluedComparisonSndAlt hpZ hpX hpV hpY hG hF hH
  exact Functor.isEquivalence_of_iso (gluedComparisonSndAltIso hG).symm

end Equivalence

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒵 𝒳 𝒴 𝒱 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

section

variable (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (b : 𝒱 ⟶ 𝒴)

/-- **The comparison that keeps the second half of the triple 2-fibre product**, read in the
2-category of categories fibred in groupoids:
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⟶ (𝒵 ×_𝒴 𝒱) ×_𝒱 (𝒱 ×_𝒴 𝒳)`. -/
def tripleProductMorSnd :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.gluedComparisonSnd (p𝒵 := 𝒵.val.p) (p𝒳 := 𝒳.val.p)
        (p𝒱 := 𝒱.val.p) (p𝒴 := 𝒴.val.p) (G := g.hom.toFunctor) (F := f.hom.toFunctor)
        (H := b.hom.toFunctor) g.hom.w
      w := TwoFibreProductOver.gluedComparisonSnd_comp_structureFunctor .. }

/-- The comparison is an equivalence of the underlying categories. -/
theorem isEquivalence_tripleProductMorSnd :
    (tripleProductMorSnd.{v₁, v₂, u₁, u₂} g f b).hom.toFunctor.IsEquivalence :=
  TwoFibreProductOver.isEquivalence_gluedComparisonSnd 𝒵.isFiberedInGroupoids
    𝒳.isFiberedInGroupoids 𝒱.isFiberedInGroupoids 𝒴.isFiberedInGroupoids g.hom.w f.hom.w b.hom.w

/-- The comparison is strictly compatible with the projections to `𝒵 ×_𝒴 𝒱`. -/
@[simp] lemma tripleProductMorSnd_comp_fst :
    tripleProductMorSnd.{v₁, v₂, u₁, u₂} g f b ≫
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst).fst =
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).snd := rfl

/-- The comparison followed by the projection to `𝒱 ×_𝒴 𝒳` is the pairing
`CategoryTheory.CatFiberedInGroupoids.triplePairingMor`, on the nose. -/
@[simp] lemma tripleProductMorSnd_comp_snd :
    tripleProductMorSnd.{v₁, v₂, u₁, u₂} g f b ≫
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst).snd =
      triplePairingMor.{v₁, v₂, u₁, u₂} g f b := rfl

/-- **The cospan `(𝒵 ×_𝒴 𝒱 ⟶ 𝒱, 𝒱 ×_𝒴 𝒳 ⟶ 𝒱)` read on the triple 2-fibre product
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`**: the leg to `𝒵 ×_𝒴 𝒱` is that apex's own second projection and the
leg to `𝒱 ×_𝒴 𝒳` is the pairing.

The filler is the identity 2-cell: the two legs it compares are, by
`CategoryTheory.CatFiberedInGroupoids.triplePairingMor_comp_fst`, the same 1-morphism. -/
def tripleProductSndSquare :
    Bicategory.TwoCommSq (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst where
  pt := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).pt
  fst := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).snd
  snd := triplePairingMor.{v₁, v₂, u₁, u₂} g f b
  iso := Iso.refl _

/-- The comparison, as a pre-morphism of 2-commutative squares over the cospan
`(𝒵 ×_𝒴 𝒱 ⟶ 𝒱, 𝒱 ×_𝒴 𝒳 ⟶ 𝒱)`. Both comparison 2-cells are identities, by the strict
compatibilities `CategoryTheory.CatFiberedInGroupoids.tripleProductMorSnd_comp_fst` and
`tripleProductMorSnd_comp_snd`. -/
def tripleProductSndPreHom :
    Bicategory.TwoCommSq.PreHom (tripleProductSndSquare.{v₁, v₂, u₁, u₂} g f b)
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst) where
  hom := tripleProductMorSnd.{v₁, v₂, u₁, u₂} g f b
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext P
    exact map_id_comp_id_eq _ _ _

/-- **The second-projection recognition form of the triple product.** The apex
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`, with its own second projection to `𝒵 ×_𝒴 𝒱` and with the pairing
`CategoryTheory.CatFiberedInGroupoids.triplePairingMor` to `𝒱 ×_𝒴 𝒳`, is a 2-fibre product of the
cospan `(𝒵 ×_𝒴 𝒱 ⟶ 𝒱, 𝒱 ×_𝒴 𝒳 ⟶ 𝒱)` (**Stacks 003Q**).

Together with `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare` this
reads the one triple-product identity of Stacks 02XC compatibly with *both* projections of
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`, the pairing being the same 1-morphism in the two statements. -/
noncomputable def isTwoFibreProduct_tripleProductSndSquare :
    Bicategory.IsTwoFibreProduct (tripleProductSndSquare.{v₁, v₂, u₁, u₂} g f b) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst)
    (tripleProductSndPreHom.{v₁, v₂, u₁, u₂} g f b)
    (isEquivalence_tripleProductMorSnd.{v₁, v₂, u₁, u₂} g f b)

end

end CategoryTheory.CatFiberedInGroupoids

end
