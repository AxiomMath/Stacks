module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# The 2-fibre product of a cospan one leg of which is an identity

Fix a bicategory and a 1-morphism `g : y ⟶ z`. The 2-commutative square

```text
  y ---- g ----> z
  |              |
 𝟙 y            𝟙 z
  |              |
  v              v
  y ---- g ----> z
```

with apex `y`, first leg `g` and second leg `𝟙 y` is a 2-fibre product of the cospan
`(𝟙 z, g)`, the cospan whose first leg is the identity of `z` and whose second leg is `g`: this
is the degenerate case `z \times_z y = y`. For any 2-commutative square `Z` over `(𝟙 z, g)`
the comparison into this one is the second leg of `Z` itself.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.idCospan`: the square displayed above.
* `CategoryTheory.Bicategory.toIdCospan`: the comparison into it, on the second leg.

## Main results

* `CategoryTheory.Bicategory.rel_toIdCospan`: every comparison into it is equivalent to that one.
* `CategoryTheory.Bicategory.isTwoFibreProduct_idCospan`: it is a 2-fibre product.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]
variable {y z : B}

/-- The 2-commutative square over the cospan `(𝟙 z, g)` with apex the source of `g`, first leg
`g`, second leg the identity, and filler the comparison of the two unitors. -/
@[reducible]
def TwoCommSq.idCospan (g : y ⟶ z) : TwoCommSq (𝟙 z) g where
  pt := y
  fst := g
  snd := 𝟙 y
  iso := ρ_ g ≪≫ (λ_ g).symm

/-- The comparison of a square over `(𝟙 z, g)` into
`CategoryTheory.Bicategory.TwoCommSq.idCospan` whose 1-morphism is the second leg of the given
square. Its first comparison 2-cell is the filler of the given square read through the right
unitor, and its second is a right unitor. -/
def toIdCospan {g : y ⟶ z} (Z : TwoCommSq (𝟙 z) g) :
    TwoCommSq.PreHom Z (TwoCommSq.idCospan g) where
  hom := Z.snd
  isoFst := (ρ_ Z.fst).symm ≪≫ Z.iso
  isoSnd := (ρ_ Z.snd).symm
  compat := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    bicategory

/-- The underlying 1-morphism of `CategoryTheory.Bicategory.toIdCospan Z` is the second leg of
`Z`. -/
theorem toIdCospan_hom {g : y ⟶ z} (Z : TwoCommSq (𝟙 z) g) :
    (toIdCospan Z).hom = Z.snd := rfl

/-- Every comparison into `CategoryTheory.Bicategory.TwoCommSq.idCospan` is equivalent to
`CategoryTheory.Bicategory.toIdCospan`. -/
theorem rel_toIdCospan {g : y ⟶ z} {Z : TwoCommSq (𝟙 z) g}
    (F : TwoCommSq.PreHom Z (TwoCommSq.idCospan g)) :
    TwoCommSq.PreHom.Rel F (toIdCospan Z) := by
  have hc : Z.iso.hom ≫ (F.isoSnd.hom ▷ g) ≫ (α_ F.hom (𝟙 y) g).hom =
      (F.isoFst.hom ▷ (𝟙 z)) ≫ (α_ F.hom g (𝟙 z)).hom ≫
        (F.hom ◁ ((ρ_ g).hom ≫ (λ_ g).inv)) := F.compat
  have hZ : Z.iso.hom =
      ((F.isoFst.hom ▷ (𝟙 z)) ≫ (α_ F.hom g (𝟙 z)).hom ≫
        (F.hom ◁ ((ρ_ g).hom ≫ (λ_ g).inv))) ≫
          ((α_ F.hom (𝟙 y) g).inv ≫ (F.isoSnd.inv ▷ g)) := by
    rw [← hc]
    simp [← comp_whiskerRight]
  refine ⟨(ρ_ F.hom).symm ≪≫ F.isoSnd.symm, ?_, ?_⟩
  · change F.isoFst.hom ≫ (((ρ_ F.hom).inv ≫ F.isoSnd.inv) ▷ g) = (ρ_ Z.fst).inv ≫ Z.iso.hom
    rw [hZ]
    bicategory
  · change F.isoSnd.hom ≫ (((ρ_ F.hom).inv ≫ F.isoSnd.inv) ▷ (𝟙 y)) = (ρ_ Z.snd).inv
    simp [whiskerRight_id]

/-- The square `CategoryTheory.Bicategory.TwoCommSq.idCospan g` is a 2-fibre product of the
cospan `(𝟙 z, g)`. -/
noncomputable def isTwoFibreProduct_idCospan (g : y ⟶ z) :
    IsTwoFibreProduct (TwoCommSq.idCospan g) :=
  IsTerminal.ofUniqueHom (fun Z => _root_.Quotient.mk _ (toIdCospan Z))
    (fun _ m => _root_.Quotient.inductionOn m fun F =>
      _root_.Quotient.sound (rel_toIdCospan F))

end CategoryTheory.Bicategory

end
