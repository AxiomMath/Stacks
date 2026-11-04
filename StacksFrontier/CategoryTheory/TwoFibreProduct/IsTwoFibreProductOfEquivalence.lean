module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# A square comparable to a 2-fibre product is a 2-fibre product (Stacks 003Q)

Fix a cospan `f : x ⟶ z`, `g : y ⟶ z` in a bicategory and let `P` be a 2-fibre product of it
(`CategoryTheory.Bicategory.IsTwoFibreProduct`, **Stacks 003Q**), that is, a terminal object of
the category of 2-commutative squares of **Stacks 003O**.
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` says that a comparison
1-morphism between two 2-fibre products of one cospan of categories fibred in groupoids is an
equivalence of the underlying categories. This file proves the **converse**: a 2-commutative
square that is comparable to a 2-fibre product by a 1-morphism with a section is itself a
2-fibre product.

The general bicategorical statement asks only for a *section*: given a pre-morphism of squares
`a : P ⟶ Q` out of a 2-fibre product `P` together with `k : Q.pt ⟶ P.pt` and an invertible
2-cell `k ≫ a.hom ≅ 𝟙 Q.pt`, the square `Q` is a 2-fibre product. Only one of the two
2-cells of an equivalence is needed, because the other half of the isomorphism `P ≅ Q` in the
category of 2-commutative squares is free: both composites `P ⟶ P` agree by terminality of `P`.
In particular **no triangle identity of an adjoint equivalence is used**.

For categories fibred in groupoids the hypothesis is the bare one, that the comparison is an
equivalence of the underlying categories: **Stacks 003Z (2)**
(`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`) upgrades it to an equivalence
in the 2-category, supplying both a quasi-inverse 1-morphism *over the base* and two 2-cells all
of whose components lie over identities. Both directions of comparison are recorded, since the
one that terminality supplies for free points *into* the 2-fibre product.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofSection`: the pre-morphism of squares carried by
  a section of the 1-morphism underlying a pre-morphism.
* `CategoryTheory.Bicategory.squareIsoOfSection`: the resulting isomorphism of 2-commutative
  squares.

## Main results

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.iso_hom_eq`: the compatibility square of
  Stacks 003O, solved for the filler of the source square.
* `CategoryTheory.Bicategory.isTwoFibreProduct_of_section`: the converse above, in any
  bicategory.
* `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_from` and
  `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`: the converse of
  `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` for categories fibred in
  groupoids, for a comparison pointing out of, respectively into, the 2-fibre product.

## Implementation notes

The one computation with content is the compatibility square of Stacks 003O for
`TwoCommSq.PreHom.ofSection`. It is the compatibility square of the given pre-morphism,
whiskered by the section, up to coherence and one instance of the exchange law — the 2-cell
`𝟙 Q.pt ⟶ k ≫ a.hom` has to be moved past the filler of `Q`. The exchange law is **not**
part of what `bicategory` normalises away: on this goal the tactic reduces both sides to a normal
form in which the two uninterpreted 2-cells still appear in the wrong order. So the move is done
once and for all in `comp_unit_naturality`, which is the naturality of `t ↦ k ≫ (a.hom ≫ t)` on
the hom-category, and the two surrounding coherence steps are left to `bicategory`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- **Naturality of the 2-cell attached to a section.** A 2-cell `u : 𝟙 q ⟶ k ≫ A` makes
`t ↦ k ≫ (A ≫ t)` a transformation of the identity of the hom-category `Hom(q, z)`, and this is
its naturality: the composite `t ⟶ k ≫ (A ≫ t)` built from `u` commutes with any 2-cell
`θ : t ⟶ t'`. -/
private theorem comp_unit_naturality {p q : B} (k : q ⟶ p) (A : p ⟶ q) (u : 𝟙 q ⟶ k ≫ A)
    {z : B} {t t' : q ⟶ z} (θ : t ⟶ t') :
    θ ≫ (λ_ t').inv ≫ (u ▷ t') ≫ (α_ k A t').hom
      = ((λ_ t).inv ≫ (u ▷ t) ≫ (α_ k A t).hom) ≫ k ◁ (A ◁ θ) := by
  rw [Category.assoc, Category.assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, associator_naturality_right]

/-- **`comp_unit_naturality` read on a 2-cell between composites.** For a 2-cell
`η : m ≫ f ⟶ n ≫ g`, the two composites built from `u : 𝟙 q ⟶ k ≫ A` on the legs `m` and `n`
are exchanged with `η`. -/
private theorem comp_unit_exchange {p q : B} (k : q ⟶ p) (A : p ⟶ q) (u : 𝟙 q ⟶ k ≫ A)
    {x y z : B} (m : q ⟶ x) (n : q ⟶ y) (f : x ⟶ z) (g : y ⟶ z) (η : m ≫ f ⟶ n ≫ g) :
    η ≫ (((λ_ n).inv ≫ (u ▷ n) ≫ (α_ k A n).hom) ▷ g) ≫ (α_ k (A ≫ n) g).hom
      = (((λ_ m).inv ≫ (u ▷ m) ≫ (α_ k A m).hom) ▷ f) ≫ (α_ k (A ≫ m) f).hom
        ≫ k ◁ ((α_ A m f).hom ≫ (A ◁ η) ≫ (α_ A n g).inv) :=
  calc η ≫ (((λ_ n).inv ≫ (u ▷ n) ≫ (α_ k A n).hom) ▷ g) ≫ (α_ k (A ≫ n) g).hom
      = (η ≫ (λ_ (n ≫ g)).inv ≫ (u ▷ (n ≫ g)) ≫ (α_ k A (n ≫ g)).hom)
          ≫ k ◁ (α_ A n g).inv := by bicategory
    _ = (((λ_ (m ≫ f)).inv ≫ (u ▷ (m ≫ f)) ≫ (α_ k A (m ≫ f)).hom) ≫ k ◁ (A ◁ η))
          ≫ k ◁ (α_ A n g).inv := by rw [comp_unit_naturality]
    _ = (((λ_ m).inv ≫ (u ▷ m) ≫ (α_ k A m).hom) ▷ f) ≫ (α_ k (A ≫ m) f).hom
          ≫ k ◁ ((α_ A m f).hom ≫ (A ◁ η) ≫ (α_ A n g).inv) := by bicategory

variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- **The compatibility square of Stacks 003O, solved for the filler of the source square.** For
a pre-morphism of 2-commutative squares `a : T ⟶ S`, the filler of `T` is the filler of `S` read
through the comparison 2-cells of `a`. -/
theorem TwoCommSq.PreHom.iso_hom_eq {T S : TwoCommSq f g} (a : TwoCommSq.PreHom T S) :
    (a.isoFst.inv ▷ f) ≫ T.iso.hom
      = (α_ a.hom S.fst f).hom ≫ (a.hom ◁ S.iso.hom) ≫ (α_ a.hom S.snd g).inv ≫
        (a.isoSnd.inv ▷ g) := by
  have h := a.compat
  have h2 : (α_ a.hom S.fst f).hom ≫ (a.hom ◁ S.iso.hom)
      = (a.isoFst.inv ▷ f) ≫ T.iso.hom ≫ (a.isoSnd.hom ▷ g) ≫ (α_ a.hom S.snd g).hom := by
    rw [h]
    simp
  rw [reassoc_of% h2]
  simp [← comp_whiskerRight]

/-- **A section of a pre-morphism of 2-commutative squares is a pre-morphism the other way.**
Let `a : T ⟶ S` be a pre-morphism of 2-commutative squares over `(f, g)` and let
`ε : k ≫ a.hom ≅ 𝟙 S.pt` exhibit `k : S.pt ⟶ T.pt` as a section of its underlying 1-morphism.
Then `k` is the 1-morphism of a pre-morphism `S ⟶ T`, whose two comparison 2-cells are those of
`a` read backwards through `ε`. -/
def TwoCommSq.PreHom.ofSection {T S : TwoCommSq f g} (a : TwoCommSq.PreHom T S)
    (k : S.pt ⟶ T.pt) (ε : k ≫ a.hom ≅ 𝟙 S.pt) : TwoCommSq.PreHom S T where
  hom := k
  isoFst := (λ_ S.fst).symm ≪≫ whiskerRightIso ε.symm S.fst ≪≫ α_ k a.hom S.fst ≪≫
    whiskerLeftIso k a.isoFst.symm
  isoSnd := (λ_ S.snd).symm ≪≫ whiskerRightIso ε.symm S.snd ≪≫ α_ k a.hom S.snd ≪≫
    whiskerLeftIso k a.isoSnd.symm
  compat :=
    calc S.iso.hom ≫ (((λ_ S.snd).inv ≫ (ε.inv ▷ S.snd) ≫ (α_ k a.hom S.snd).hom ≫
          (k ◁ a.isoSnd.inv)) ▷ g) ≫ (α_ k T.snd g).hom
        = (S.iso.hom ≫ (((λ_ S.snd).inv ≫ (ε.inv ▷ S.snd) ≫ (α_ k a.hom S.snd).hom) ▷ g)
            ≫ (α_ k (a.hom ≫ S.snd) g).hom) ≫ (k ◁ (a.isoSnd.inv ▷ g)) := by bicategory
      _ = ((((λ_ S.fst).inv ≫ (ε.inv ▷ S.fst) ≫ (α_ k a.hom S.fst).hom) ▷ f)
            ≫ (α_ k (a.hom ≫ S.fst) f).hom ≫ k ◁ ((α_ a.hom S.fst f).hom ≫
              (a.hom ◁ S.iso.hom) ≫ (α_ a.hom S.snd g).inv)) ≫ (k ◁ (a.isoSnd.inv ▷ g)) := by
          rw [comp_unit_exchange]
      _ = (((λ_ S.fst).inv ≫ (ε.inv ▷ S.fst) ≫ (α_ k a.hom S.fst).hom) ▷ f)
            ≫ (α_ k (a.hom ≫ S.fst) f).hom
            ≫ k ◁ ((a.isoFst.inv ▷ f) ≫ T.iso.hom) := by rw [a.iso_hom_eq]; bicategory
      _ = (((λ_ S.fst).inv ≫ (ε.inv ▷ S.fst) ≫ (α_ k a.hom S.fst).hom ≫
          (k ◁ a.isoFst.inv)) ▷ f) ≫ (α_ k T.fst f).hom ≫ (k ◁ T.iso.hom) := by bicategory

/-- **`TwoCommSq.PreHom.ofSection` is a section in the category of 2-commutative squares.** Its
composite with `a` is equivalent to the identity of `S` for the 2-cell equivalence of
Stacks 003O, the mediating 2-cell being the given one. -/
theorem TwoCommSq.PreHom.ofSection_comp_rel {T S : TwoCommSq f g} (a : TwoCommSq.PreHom T S)
    (k : S.pt ⟶ T.pt) (ε : k ≫ a.hom ≅ 𝟙 S.pt) :
    TwoCommSq.PreHom.Rel ((a.ofSection k ε).comp a) (TwoCommSq.PreHom.id S) :=
  ⟨ε, by simp [ofSection, comp, id, ← comp_whiskerRight]⟩

/-- **A square comparable to a 2-fibre product is isomorphic to it.** If `P` is a 2-fibre product
of `(f, g)` and `a : P ⟶ Q` is a pre-morphism of 2-commutative squares whose underlying
1-morphism has a section, then `P` and `Q` are isomorphic objects of the category of
2-commutative squares of Stacks 003O. -/
noncomputable def squareIsoOfSection {P Q : TwoCommSq f g} (hP : IsTwoFibreProduct P)
    (a : TwoCommSq.PreHom P Q) (k : Q.pt ⟶ P.pt) (ε : k ≫ a.hom ≅ 𝟙 Q.pt) : P ≅ Q where
  hom := _root_.Quotient.mk _ a
  inv := _root_.Quotient.mk _ (a.ofSection k ε)
  hom_inv_id := hP.hom_ext _ _
  inv_hom_id := _root_.Quotient.sound (a.ofSection_comp_rel k ε)

/-- **The converse of `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, in any
bicategory.** A 2-commutative square receiving a pre-morphism from a 2-fibre product of the same
cospan whose underlying 1-morphism has a section is itself a 2-fibre product (**Stacks 003Q**). -/
noncomputable def isTwoFibreProduct_of_section {P Q : TwoCommSq f g} (hP : IsTwoFibreProduct P)
    (a : TwoCommSq.PreHom P Q) (k : Q.pt ⟶ P.pt) (ε : k ≫ a.hom ≅ 𝟙 Q.pt) :
    IsTwoFibreProduct Q :=
  IsTerminal.ofIso hP (squareIsoOfSection hP a k ε)

section CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {X Y Z : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C} {f' : X ⟶ Z} {g' : Y ⟶ Z}

/-- **The converse of `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, for a
comparison out of the 2-fibre product.** Let `P` be a 2-fibre product of a cospan of categories
fibred in groupoids over `C` and let `a : P ⟶ Q` be a pre-morphism of 2-commutative squares whose
underlying functor is an equivalence of categories. Then `Q` is a 2-fibre product too. -/
noncomputable def isTwoFibreProduct_of_isEquivalence_from {P Q : TwoCommSq f' g'}
    (hP : IsTwoFibreProduct P) (a : TwoCommSq.PreHom P Q)
    (ha : a.hom.hom.toFunctor.IsEquivalence) : IsTwoFibreProduct Q := by
  refine Nonempty.some ?_
  obtain ⟨F, hF, _, ε, _, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over P.pt.val.p Q.pt.val.p
      P.pt.isFiberedInGroupoids Q.pt.isFiberedInGroupoids a.hom.hom.toFunctor a.hom.hom.w ha
  exact ⟨isTwoFibreProduct_of_section hP a
    (InducedBicategory.mkHom { toFunctor := F, w := hF })
    (InducedBicategory.isoMk (BasedNatIso.mkNatIso ε hε))⟩

/-- **The converse of `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, for a
comparison into the 2-fibre product.** Let `P` be a 2-fibre product of a cospan of categories
fibred in groupoids over `C` and let `c : Q ⟶ P` be a pre-morphism of 2-commutative squares whose
underlying functor is an equivalence of categories. Then `Q` is a 2-fibre product too. -/
noncomputable def isTwoFibreProduct_of_isEquivalence_to {P Q : TwoCommSq f' g'}
    (hP : IsTwoFibreProduct P) (c : TwoCommSq.PreHom Q P)
    (hc : c.hom.hom.toFunctor.IsEquivalence) : IsTwoFibreProduct Q := by
  refine Nonempty.some ?_
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over Q.pt.val.p P.pt.val.p
      Q.pt.isFiberedInGroupoids P.pt.isFiberedInGroupoids c.hom.hom.toFunctor c.hom.hom.w hc
  exact ⟨isTwoFibreProduct_of_section hP
    (c.ofSection (InducedBicategory.mkHom { toFunctor := F, w := hF })
      (InducedBicategory.isoMk (BasedNatIso.mkNatIso ε hε)))
    c.hom (InducedBicategory.isoMk (BasedNatIso.mkNatIso η hη))⟩

end CatFiberedInGroupoids

end CategoryTheory.Bicategory

end
