module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# The two bracketings of a triple 2-fibre product, as 2-fibre products (Stacks 02XC, 04S7)

Fix a base category `C` and three 1-morphisms `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴`, `b : 𝒱 ⟶ 𝒴` of
categories fibred in groupoids over `C`. The canonical 2-fibre product squares of Stacks 003Q
(`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`) give two different apexes for the
triple product `𝒵 ×_𝒴 𝒳 ×_𝒴 𝒱`, according to which factor the two halves are glued along:

```text
(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)        and        (𝒵 ×_𝒴 𝒳) ×_𝒳 (𝒱 ×_𝒴 𝒳)
```

This file identifies them and exhibits the **first** apex as a 2-fibre product of the cospan
`(𝒵 ×_𝒴 𝒳 ⟶ 𝒳, 𝒱 ×_𝒴 𝒳 ⟶ 𝒳)` *with its own projection to `𝒵 ×_𝒴 𝒳` as the first leg*.

## Why this is not an instance of either cancellation

Both `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare` and
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare` read an iterated product
`(𝒜 ×_𝒴 ℬ) ×_ℬ 𝒰`, resp. `(𝒜 ×_𝒴 ℬ) ×_𝒜 𝒰`, as a 2-fibre product of a cospan whose legs are the
*outer* projection and a composite through an *inner* projection. Every such reading of
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)` therefore exposes a leg of the form `pr₁ ≫ pr₂`, never the outer
projection `pr₁` itself — and `pr₁` is the leg wanted here, because its target `𝒵 ×_𝒴 𝒳` is itself
a 2-fibre product. So a cancellation never exposes a leg whose target is a 2-fibre product, and
this statement has to be proved rather than instantiated.

Nor does the composable-pair comparison of
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverComposable` apply: its
`CategoryTheory.TwoFibreProductOver.ComposablePairCat` is glued along the *second* projection of
its first factor and the *first* projection of its second factor, whereas both apexes above are
glued along two projections of the same index — the first two for `gluedAlongFirst`, the second
two for `gluedAlongSecond`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.gluedAlongFirst` and
  `CategoryTheory.TwoFibreProductOver.gluedAlongSecond`: the two apexes, over `C`.
* `CategoryTheory.TwoFibreProductOver.gluedPairing`: the pairing
  `(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⥤ 𝒱 ×_𝒴 𝒳`, which forgets the two copies of `𝒵` and splices their
  comparison isomorphisms.
* `CategoryTheory.TwoFibreProductOver.gluedComparison` and
  `CategoryTheory.TwoFibreProductOver.gluedComparisonInv`: the comparison between the two apexes
  and its quasi-inverse.
* `CategoryTheory.CatFiberedInGroupoids.triplePairingMor`: the pairing, in the 2-category.
* `CategoryTheory.CatFiberedInGroupoids.tripleProductSquare`: the 2-commutative square whose apex
  is `(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`, whose first leg is its own projection to `𝒵 ×_𝒴 𝒳` and whose
  second leg is the pairing.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_gluedComparison`: the comparison is an
  equivalence of categories.
* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare`: that square is a
  2-fibre product of `(𝒵 ×_𝒴 𝒳 ⟶ 𝒳, 𝒱 ×_𝒴 𝒳 ⟶ 𝒳)`.

## Implementation notes

The comparison is *strictly* compatible with both projections and with the structure functor —
`CategoryTheory.TwoFibreProductOver.gluedComparison_comp_fst`, `_comp_snd` and
`_comp_structureFunctor` all hold by `rfl` — and the filler of `tripleProductSquare` is the
identity 2-cell, because the two legs it compares are the *same* functor on the nose. That is why
`CategoryTheory.CatFiberedInGroupoids.tripleProductPreHom` has identity comparison 2-cells and its
compatibility square of Stacks 003O is the one-line
`CategoryTheory.CatFiberedInGroupoids.map_id_comp_id_eq`; terminality is then transported by
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`, exactly as in the two
cancellation files. No 2-cell algebra occurs anywhere.

The three functors are marked `@[implicit_reducible]` for the reason recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Swap`: the components of the unit and the counit are
typed through `(gluedComparison hG ⋙ gluedComparisonInv hF).obj P`, and without the attribute
those types are not type-correct at the `implicit` transparency level at which Lean checks
implicit arguments, so `simp` declines to enter them and reports its lemmas unused.

One step resists even that. A structure field of the form `iso : F.obj P.x ≅ G.obj Q.x` applied to
an object of a round trip presents `Functor.map` with two *different but definitionally equal*
index terms, and `Functor.map_id` — whose pattern needs the two indices to be syntactically one —
cannot fire. The remedy is `change`, which checks definitional equality at the default
transparency level and so may spell both indices the same way; it is used once, in
`CategoryTheory.TwoFibreProductOver.gluedCounitApp`.

Nothing here carries a `@[stacks]` attribute. The `02XC` tag is on
`CategoryTheory.Limits.CategoricalPullback.assoc` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Associativity`, the `02XD` tag on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation` and the `04S7` tag on
`CategoryTheory.Limits.CategoricalPullback.pr₀₂` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProjection`.

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

attribute [local implicit_reducible] fst snd structureFunctor

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒵 : Type uZ} [Category.{vZ} 𝒵]
  {𝒳 : Type uX} [Category.{vX} 𝒳] {𝒱 : Type uV} [Category.{vV} 𝒱]
  {𝒴 : Type uY} [Category.{vY} 𝒴]

variable (p𝒵 : 𝒵 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒱 : 𝒱 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞)
  (G : 𝒵 ⥤ 𝒴) (F : 𝒳 ⥤ 𝒴) (H : 𝒱 ⥤ 𝒴)

/-- The triple 2-fibre product over `𝒞` glued along the **first** factor of both halves:
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`. An object over `U` is a pair of objects `(U, z, x, ψ)` and
`(U, z', v, χ)` together with a vertical isomorphism `ρ : z ≅ z'`. -/
abbrev gluedAlongFirst : Type _ :=
  TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
    (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H)

/-- The triple 2-fibre product over `𝒞` glued along the **second** factor of both halves:
`(𝒵 ×_𝒴 𝒳) ×_𝒳 (𝒱 ×_𝒴 𝒳)`. An object over `U` is a pair of objects `(U, z, x, ψ)` and
`(U, v, x', ω)` together with a vertical isomorphism `σ : x ≅ x'`. -/
abbrev gluedAlongSecond : Type _ :=
  TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒳
    (snd p𝒵 p𝒳 p𝒴 G F) (snd p𝒱 p𝒳 p𝒴 H F)

variable {p𝒵 p𝒳 p𝒱 p𝒴 G F H}

/-- **The pairing of the two outer factors**, `(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⥤ 𝒱 ×_𝒴 𝒳`: it forgets
the two copies of `𝒵` and splices the three comparison isomorphisms, sending
`((U, z, x, ψ), (U, z', v, χ), ρ)` to `(U, v, x, ψ ∘ G(ρ)⁻¹ ∘ χ⁻¹)`.

Only `G` is required to be over `𝒞`: that is what makes the image under `G` of the vertical
isomorphism `ρ` of `𝒵` vertical in `𝒴`. Nothing is required of `F` or `H`. -/
@[implicit_reducible]
def gluedPairing (hG : G ⋙ p𝒴 = p𝒵) :
    gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H ⥤ TwoFibreProductOver p𝒱 p𝒳 p𝒴 H F where
  obj P :=
    { base := P.base
      x := P.y.y
      y := P.x.y
      hx := P.y.hy.trans P.hy
      hy := P.x.hy.trans P.hx
      iso := P.y.iso.symm ≪≫ (G.mapIso P.iso).symm ≪≫ P.x.iso
      vertical := by
        have hv := P.vertical
        have h₀ : p𝒴.IsHomLift (𝟙 P.base) P.y.iso.hom := P.hy ▸ P.y.vertical
        have h₀' : p𝒴.IsHomLift (𝟙 P.base) P.y.iso.inv := inferInstance
        have h₁ : p𝒵.IsHomLift (𝟙 P.base) P.iso.inv := inferInstance
        have h₂ : p𝒴.IsHomLift (𝟙 P.base) (G.map P.iso.inv) :=
          Functor.isHomLift_map_of_comp_eq hG (𝟙 P.base) P.iso.inv
        have h₃ : p𝒴.IsHomLift (𝟙 P.base) P.x.iso.hom := P.hx ▸ P.x.vertical
        exact (inferInstance : p𝒴.IsHomLift (𝟙 P.base)
          (P.y.iso.inv ≫ G.map P.iso.inv ≫ P.x.iso.hom)) }
  map {P Q} φ :=
    { hbase := φ.hbase
      a := φ.b.b
      b := φ.a.b
      ha := isHomLift_b φ.b φ.hbase φ.hb
      hb := isHomLift_b φ.a φ.hbase φ.ha
      w := by
        have hw : φ.a.a ≫ Q.iso.hom = P.iso.hom ≫ φ.b.a := φ.w
        have hb : H.map φ.b.b = P.y.iso.inv ≫ G.map φ.b.a ≫ Q.y.iso.hom := by
          rw [φ.b.w]; simp
        have hz : φ.b.a ≫ Q.iso.inv = P.iso.inv ≫ φ.a.a := by
          rw [Iso.comp_inv_eq, Category.assoc, hw]; simp
        have key : G.map φ.b.a ≫ G.map Q.iso.inv = G.map P.iso.inv ≫ G.map φ.a.a := by
          rw [← G.map_comp, ← G.map_comp, hz]
        dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Functor.mapIso_hom]
        rw [hb]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        slice_lhs 2 3 => rw [key]
        simp only [Category.assoc]
        rw [φ.a.w] }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The pairing is strictly over `𝒞`. -/
@[simp] lemma gluedPairing_comp_structureFunctor (hG : G ⋙ p𝒴 = p𝒵) :
    gluedPairing (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F) (H := H) hG ⋙
      structureFunctor p𝒱 p𝒳 p𝒴 H F =
    structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) := rfl

/-- The pairing followed by the projection to `𝒱` is the projection to `𝒵 ×_𝒴 𝒱` followed by
*its* projection to `𝒱`, on the nose. -/
@[simp] lemma gluedPairing_comp_fst (hG : G ⋙ p𝒴 = p𝒵) :
    gluedPairing (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F) (H := H) hG ⋙
      fst p𝒱 p𝒳 p𝒴 H F =
    snd (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) ⋙ snd p𝒵 p𝒱 p𝒴 G H := rfl

/-- The pairing followed by the projection to `𝒳` is the projection to `𝒵 ×_𝒴 𝒳` followed by
*its* projection to `𝒳`, on the nose. This identity is the filler of
`CategoryTheory.CatFiberedInGroupoids.tripleProductSquare`. -/
@[simp] lemma gluedPairing_comp_snd (hG : G ⋙ p𝒴 = p𝒵) :
    gluedPairing (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F) (H := H) hG ⋙
      snd p𝒱 p𝒳 p𝒴 H F =
    fst (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) ⋙ snd p𝒵 p𝒳 p𝒴 G F := rfl

/-- The base of an object in the image of the pairing. -/
@[simp] lemma gluedPairing_obj_base (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) : ((gluedPairing hG).obj P).base = P.base := rfl

/-- The `𝒱`-component of an object in the image of the pairing. -/
@[simp] lemma gluedPairing_obj_x (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) : ((gluedPairing hG).obj P).x = P.y.y := rfl

/-- The `𝒳`-component of an object in the image of the pairing. -/
@[simp] lemma gluedPairing_obj_y (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) : ((gluedPairing hG).obj P).y = P.x.y := rfl

/-- The comparison isomorphism of an object in the image of the pairing: the three given ones
spliced. -/
@[simp] lemma gluedPairing_obj_iso (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedPairing hG).obj P).iso = P.y.iso.symm ≪≫ (G.mapIso P.iso).symm ≪≫ P.x.iso := rfl

/-- The `𝒱`-component of a morphism in the image of the pairing. -/
@[simp] lemma gluedPairing_map_a (hG : G ⋙ p𝒴 = p𝒵)
    {P Q : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H} (φ : P ⟶ Q) :
    ((gluedPairing hG).map φ).a = φ.b.b := rfl

/-- The `𝒳`-component of a morphism in the image of the pairing. -/
@[simp] lemma gluedPairing_map_b (hG : G ⋙ p𝒴 = p𝒵)
    {P Q : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H} (φ : P ⟶ Q) :
    ((gluedPairing hG).map φ).b = φ.a.b := rfl

/-- **The comparison of the two bracketings**,
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⥤ (𝒵 ×_𝒴 𝒳) ×_𝒳 (𝒱 ×_𝒴 𝒳)`: it keeps the first half untouched,
replaces the second half by the pairing, and takes the identity of `x` as the new gluing
isomorphism. -/
@[implicit_reducible]
def gluedComparison (hG : G ⋙ p𝒴 = p𝒵) :
    gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H ⥤ gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H where
  obj P :=
    { base := P.base
      x := P.x
      y := (gluedPairing hG).obj P
      hx := P.hx
      hy := rfl
      iso := Iso.refl P.x.y
      vertical := IsHomLift.id (P.x.hy.trans P.hx) }
  map {P Q} φ :=
    { hbase := φ.hbase
      a := φ.a
      b := (gluedPairing hG).map φ
      ha := φ.ha
      hb := structureFunctor_isHomLift _ φ.hbase (isHomLift_b φ.b φ.hbase φ.hb)
      w := (by rw [Category.comp_id, Category.id_comp] :
        φ.a.b ≫ 𝟙 Q.x.y = 𝟙 P.x.y ≫ φ.a.b) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison is strictly compatible with the projections to `𝒵 ×_𝒴 𝒳`. -/
@[simp] lemma gluedComparison_comp_fst (hG : G ⋙ p𝒴 = p𝒵) :
    gluedComparison (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F) (H := H) hG ⋙
      fst (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒳
        (snd p𝒵 p𝒳 p𝒴 G F) (snd p𝒱 p𝒳 p𝒴 H F) =
    fst (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) := rfl

/-- The comparison followed by the projection to `𝒱 ×_𝒴 𝒳` is the pairing. -/
@[simp] lemma gluedComparison_comp_snd (hG : G ⋙ p𝒴 = p𝒵) :
    gluedComparison (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F) (H := H) hG ⋙
      snd (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒳
        (snd p𝒵 p𝒳 p𝒴 G F) (snd p𝒱 p𝒳 p𝒴 H F) = gluedPairing hG := rfl

/-- The comparison is strictly over `𝒞`. -/
@[simp] lemma gluedComparison_comp_structureFunctor (hG : G ⋙ p𝒴 = p𝒵) :
    gluedComparison (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F) (H := H) hG ⋙
      structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒱 p𝒳 p𝒴 H F) p𝒳
        (snd p𝒵 p𝒳 p𝒴 G F) (snd p𝒱 p𝒳 p𝒴 H F) =
    structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 G F) (structureFunctor p𝒵 p𝒱 p𝒴 G H) p𝒵
      (fst p𝒵 p𝒳 p𝒴 G F) (fst p𝒵 p𝒱 p𝒴 G H) := rfl

/-- The base of an object in the image of the comparison. -/
@[simp] lemma gluedComparison_obj_base (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) : ((gluedComparison hG).obj P).base = P.base := rfl

/-- The comparison leaves the first half untouched. -/
@[simp] lemma gluedComparison_obj_x (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) : ((gluedComparison hG).obj P).x = P.x := rfl

/-- The second half of an object in the image of the comparison is its pairing. -/
@[simp] lemma gluedComparison_obj_y (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparison hG).obj P).y = (gluedPairing hG).obj P := rfl

/-- The new gluing isomorphism of an object in the image of the comparison is the identity. -/
@[simp] lemma gluedComparison_obj_iso (hG : G ⋙ p𝒴 = p𝒵)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparison hG).obj P).iso = Iso.refl P.x.y := rfl

/-- The first component of a morphism in the image of the comparison. -/
@[simp] lemma gluedComparison_map_a (hG : G ⋙ p𝒴 = p𝒵)
    {P Q : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H} (φ : P ⟶ Q) :
    ((gluedComparison hG).map φ).a = φ.a := rfl

/-- The second component of a morphism in the image of the comparison. -/
@[simp] lemma gluedComparison_map_b (hG : G ⋙ p𝒴 = p𝒵)
    {P Q : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H} (φ : P ⟶ Q) :
    ((gluedComparison hG).map φ).b = (gluedPairing hG).map φ := rfl

/-- **The quasi-inverse of the comparison**,
`(𝒵 ×_𝒴 𝒳) ×_𝒳 (𝒱 ×_𝒴 𝒳) ⥤ (𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`: it keeps the first half untouched, forms
the second half out of the two `𝒵`- and `𝒱`-components with the gluing isomorphism spliced in,
and takes the identity of `z` as the new gluing isomorphism.

Here it is `F` that must be over `𝒞`, since this time it is the image under `F` of the gluing
isomorphism of `𝒳` that has to be vertical. -/
@[implicit_reducible]
def gluedComparisonInv (hF : F ⋙ p𝒴 = p𝒳) :
    gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H ⥤ gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H where
  obj R :=
    { base := R.base
      x := R.x
      y :=
        { base := R.base
          x := R.x.x
          y := R.y.x
          hx := R.x.hx.trans R.hx
          hy := R.y.hx.trans R.hy
          iso := R.x.iso ≪≫ F.mapIso R.iso ≪≫ R.y.iso.symm
          vertical := by
            have hv := R.vertical
            have h₀ : p𝒴.IsHomLift (𝟙 R.base) R.x.iso.hom := R.hx ▸ R.x.vertical
            have h₁ : p𝒴.IsHomLift (𝟙 R.base) (F.map R.iso.hom) :=
              Functor.isHomLift_map_of_comp_eq hF (𝟙 R.base) R.iso.hom
            have h₂ : p𝒴.IsHomLift (𝟙 R.base) R.y.iso.hom := R.hy ▸ R.y.vertical
            have h₂' : p𝒴.IsHomLift (𝟙 R.base) R.y.iso.inv := inferInstance
            exact (inferInstance : p𝒴.IsHomLift (𝟙 R.base)
              (R.x.iso.hom ≫ F.map R.iso.hom ≫ R.y.iso.inv)) }
      hx := R.hx
      hy := rfl
      iso := Iso.refl R.x.x
      vertical := IsHomLift.id (R.x.hx.trans R.hx) }
  map {R S} ψ :=
    { hbase := ψ.hbase
      a := ψ.a
      b :=
        { hbase := ψ.hbase
          a := ψ.a.a
          b := ψ.b.a
          ha := isHomLift_a ψ.a ψ.hbase ψ.ha
          hb := isHomLift_a ψ.b ψ.hbase ψ.hb
          w := by
            have hw : ψ.a.b ≫ S.iso.hom = R.iso.hom ≫ ψ.b.b := ψ.w
            have hy : F.map ψ.b.b ≫ S.y.iso.inv = R.y.iso.inv ≫ H.map ψ.b.a := by
              rw [Iso.comp_inv_eq, Category.assoc, ψ.b.w]; simp
            dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
            slice_lhs 1 2 => rw [ψ.a.w]
            simp only [Category.assoc]
            slice_lhs 2 3 => rw [← F.map_comp, hw, F.map_comp]
            simp only [Category.assoc]
            rw [hy] }
      ha := ψ.ha
      hb := structureFunctor_isHomLift _ ψ.hbase (isHomLift_a ψ.a ψ.hbase ψ.ha)
      w := (by rw [Category.comp_id, Category.id_comp] :
        ψ.a.a ≫ 𝟙 S.x.x = 𝟙 R.x.x ≫ ψ.a.a) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The base of an object in the image of the quasi-inverse. -/
@[simp] lemma gluedComparisonInv_obj_base (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparisonInv hF).obj R).base = R.base := rfl

/-- The quasi-inverse leaves the first half untouched. -/
@[simp] lemma gluedComparisonInv_obj_x (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) : ((gluedComparisonInv hF).obj R).x = R.x := rfl

/-- The `𝒵`-component of the second half of an object in the image of the quasi-inverse. -/
@[simp] lemma gluedComparisonInv_obj_y_x (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparisonInv hF).obj R).y.x = R.x.x := rfl

/-- The `𝒱`-component of the second half of an object in the image of the quasi-inverse. -/
@[simp] lemma gluedComparisonInv_obj_y_y (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparisonInv hF).obj R).y.y = R.y.x := rfl

/-- The comparison isomorphism of the second half of an object in the image of the quasi-inverse:
the two given ones with the gluing isomorphism spliced in. -/
@[simp] lemma gluedComparisonInv_obj_y_iso (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparisonInv hF).obj R).y.iso = R.x.iso ≪≫ F.mapIso R.iso ≪≫ R.y.iso.symm := rfl

/-- The new gluing isomorphism of an object in the image of the quasi-inverse is the identity. -/
@[simp] lemma gluedComparisonInv_obj_iso (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    ((gluedComparisonInv hF).obj R).iso = Iso.refl R.x.x := rfl

/-- The first component of a morphism in the image of the quasi-inverse. -/
@[simp] lemma gluedComparisonInv_map_a (hF : F ⋙ p𝒴 = p𝒳)
    {R S : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H} (ψ : R ⟶ S) :
    ((gluedComparisonInv hF).map ψ).a = ψ.a := rfl

/-- The `𝒵`-component of the second half of a morphism in the image of the quasi-inverse. -/
@[simp] lemma gluedComparisonInv_map_b_a (hF : F ⋙ p𝒴 = p𝒳)
    {R S : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H} (ψ : R ⟶ S) :
    ((gluedComparisonInv hF).map ψ).b.a = ψ.a.a := rfl

/-- The `𝒱`-component of the second half of a morphism in the image of the quasi-inverse. -/
@[simp] lemma gluedComparisonInv_map_b_b (hF : F ⋙ p𝒴 = p𝒳)
    {R S : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H} (ψ : R ⟶ S) :
    ((gluedComparisonInv hF).map ψ).b.b = ψ.b.a := rfl

/-- The component of `CategoryTheory.TwoFibreProductOver.gluedUnit` at `P`: the identity on the
first half, and the inverse of the gluing isomorphism `ρ` on the `𝒵`-component of the second. -/
noncomputable def gluedUnitApp (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳)
    (P : gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    P ≅ (gluedComparison hG ⋙ gluedComparisonInv hF).obj P := by
  have hv := P.vertical
  have hvi : p𝒵.IsHomLift (𝟙 P.base) P.iso.inv := inferInstance
  refine isoMkVertical (U := P.base) (Iso.refl P.x) (isoMkVertical (U := P.base) P.iso.symm
    (Iso.refl P.y.y) hvi (IsHomLift.id (P.y.hy.trans P.hy)) ?_)
    (IsHomLift.id P.hx) (structureFunctor_isHomLift _ (𝟙 P.base) hvi) ?_
  · simp only [Functor.comp_obj, gluedComparison_obj_x, gluedComparison_obj_y,
      gluedComparison_obj_iso, gluedComparisonInv_obj_y_iso, gluedPairing_obj_iso, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Functor.mapIso_hom,
      Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
  · change (fst p𝒵 p𝒳 p𝒴 G F).map (Iso.refl P.x).hom ≫ 𝟙 ((fst p𝒵 p𝒳 p𝒴 G F).obj P.x)
        = P.iso.hom ≫ P.iso.inv
    rw [Iso.hom_inv_id, Iso.refl_hom, Functor.map_id, Category.id_comp]

/-- **The unit of the comparison equivalence.** Going round the triple product one way replaces
the `𝒵`-component of the second half by that of the first, and the gluing isomorphism `ρ` by the
identity, so the unit is `ρ⁻¹` there and the identity elsewhere. -/
noncomputable def gluedUnit (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳) :
    𝟭 (gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H) ≅ gluedComparison hG ⋙ gluedComparisonInv hF :=
  NatIso.ofComponents (gluedUnitApp hG hF) (fun {P Q} φ => by
    have hw : φ.a.a ≫ Q.iso.hom = P.iso.hom ≫ φ.b.a := φ.w
    have hz : φ.b.a ≫ Q.iso.inv = P.iso.inv ≫ φ.a.a := by
      rw [Iso.comp_inv_eq, Category.assoc, hw]; simp
    exact Hom.ext' (show φ.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ φ.a by simp)
      (Hom.ext' hz (show φ.b.b ≫ 𝟙 Q.y.y = 𝟙 P.y.y ≫ φ.b.b by simp)))

/-- The component of `CategoryTheory.TwoFibreProductOver.gluedCounit` at `R`: the identity on the
first half, and the gluing isomorphism `σ` on the `𝒳`-component of the second. -/
noncomputable def gluedCounitApp (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳)
    (R : gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :
    (gluedComparisonInv hF ⋙ gluedComparison hG).obj R ≅ R := by
  refine isoMkVertical (U := R.base) (Iso.refl R.x)
    (isoMkVertical (U := R.base) (Iso.refl R.y.x) R.iso (IsHomLift.id (R.y.hx.trans R.hy))
      R.vertical ?_)
    (IsHomLift.id R.hx)
    (structureFunctor_isHomLift _ (𝟙 R.base) (IsHomLift.id (R.y.hx.trans R.hy))) ?_
  · simp only [Functor.comp_obj, gluedComparison_obj_y, gluedPairing_obj_iso,
      gluedComparisonInv_obj_x, gluedComparisonInv_obj_iso, gluedComparisonInv_obj_y_iso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Iso.refl_inv,
      Functor.mapIso_inv, Category.assoc]
    change H.map (𝟙 R.y.x) ≫ R.y.iso.hom = R.y.iso.hom ≫ F.map R.iso.inv ≫ R.x.iso.inv ≫
      G.map (𝟙 R.x.x) ≫ R.x.iso.hom ≫ F.map R.iso.hom
    rw [H.map_id, G.map_id, Category.id_comp, Category.id_comp, Iso.inv_hom_id_assoc,
      ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  · rfl

/-- **The counit of the comparison equivalence.** Going round the triple product the other way
replaces the `𝒳`-component of the second half by that of the first, and the gluing isomorphism
`σ` by the identity, so the counit is `σ` there and the identity elsewhere. -/
noncomputable def gluedCounit (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳) :
    gluedComparisonInv hF ⋙ gluedComparison hG ≅
      𝟭 (gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H) :=
  NatIso.ofComponents (gluedCounitApp hG hF) (fun {R S} ψ =>
    Hom.ext' (show ψ.a ≫ 𝟙 S.x = 𝟙 R.x ≫ ψ.a by simp)
      (Hom.ext' (show ψ.b.a ≫ 𝟙 S.y.x = 𝟙 R.y.x ≫ ψ.b.a by simp)
        (ψ.w : ψ.a.b ≫ S.iso.hom = R.iso.hom ≫ ψ.b.b)))

/-- **The two bracketings of the triple 2-fibre product over `𝒞` are equivalent**, by the
comparison `CategoryTheory.TwoFibreProductOver.gluedComparison`. -/
noncomputable def gluedEquivalence (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳) :
    gluedAlongFirst p𝒵 p𝒳 p𝒱 p𝒴 G F H ≌ gluedAlongSecond p𝒵 p𝒳 p𝒱 p𝒴 G F H :=
  CategoryTheory.Equivalence.mk (gluedComparison hG) (gluedComparisonInv hF)
    (gluedUnit hG hF) (gluedCounit hG hF)

/-- The comparison of the two bracketings is an equivalence of categories. -/
theorem isEquivalence_gluedComparison (hG : G ⋙ p𝒴 = p𝒵) (hF : F ⋙ p𝒴 = p𝒳) :
    (gluedComparison (p𝒵 := p𝒵) (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (G := G) (F := F)
      (H := H) hG).IsEquivalence :=
  (gluedEquivalence hG hF).isEquivalence_functor

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒵 𝒳 𝒴 𝒱 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

section

variable (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (b : 𝒱 ⟶ 𝒴)

/-- **The pairing of the two outer factors of the triple 2-fibre product**, read in the
2-category of categories fibred in groupoids:
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⟶ 𝒱 ×_𝒴 𝒳`. -/
def triplePairingMor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.gluedPairing (p𝒵 := 𝒵.val.p) (p𝒳 := 𝒳.val.p)
        (p𝒱 := 𝒱.val.p) (p𝒴 := 𝒴.val.p) (G := g.hom.toFunctor) (F := f.hom.toFunctor)
        (H := b.hom.toFunctor) g.hom.w
      w := TwoFibreProductOver.gluedPairing_comp_structureFunctor .. }

/-- The pairing followed by the projection to `𝒱` is the projection to `𝒵 ×_𝒴 𝒱` followed by its
own projection to `𝒱`, on the nose. -/
@[simp] lemma triplePairingMor_comp_fst :
    triplePairingMor.{v₁, v₂, u₁, u₂} g f b ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).fst =
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).snd ≫
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).snd := rfl

/-- The pairing followed by the projection to `𝒳` is the projection to `𝒵 ×_𝒴 𝒳` followed by its
own projection to `𝒳`, on the nose. This is the filler of
`CategoryTheory.CatFiberedInGroupoids.tripleProductSquare`. -/
@[simp] lemma triplePairingMor_comp_snd :
    triplePairingMor.{v₁, v₂, u₁, u₂} g f b ≫ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).snd =
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).fst ≫
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd := rfl

/-- **The cospan `(𝒵 ×_𝒴 𝒳 ⟶ 𝒳, 𝒱 ×_𝒴 𝒳 ⟶ 𝒳)` read on the triple 2-fibre product
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`**: the leg to `𝒵 ×_𝒴 𝒳` is that apex's own first projection and the
leg to `𝒱 ×_𝒴 𝒳` is the pairing.

The filler is the identity 2-cell: the two legs it compares are, by
`CategoryTheory.CatFiberedInGroupoids.triplePairingMor_comp_snd`, the same 1-morphism. -/
def tripleProductSquare :
    Bicategory.TwoCommSq (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).snd where
  pt := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).pt
  fst := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).fst
  snd := triplePairingMor.{v₁, v₂, u₁, u₂} g f b
  iso := Iso.refl _

/-- **The comparison of the two bracketings of the triple 2-fibre product**, read in the
2-category of categories fibred in groupoids:
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ⟶ (𝒵 ×_𝒴 𝒳) ×_𝒳 (𝒱 ×_𝒴 𝒳)`. -/
def tripleProductMor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g b).fst).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).snd).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.gluedComparison (p𝒵 := 𝒵.val.p) (p𝒳 := 𝒳.val.p)
        (p𝒱 := 𝒱.val.p) (p𝒴 := 𝒴.val.p) (G := g.hom.toFunctor) (F := f.hom.toFunctor)
        (H := b.hom.toFunctor) g.hom.w
      w := TwoFibreProductOver.gluedComparison_comp_structureFunctor .. }

/-- The comparison of the two bracketings is an equivalence of the underlying categories. -/
theorem isEquivalence_tripleProductMor :
    (tripleProductMor.{v₁, v₂, u₁, u₂} g f b).hom.toFunctor.IsEquivalence :=
  TwoFibreProductOver.isEquivalence_gluedComparison g.hom.w f.hom.w

/-- The comparison, as a pre-morphism of 2-commutative squares over the cospan
`(𝒵 ×_𝒴 𝒳 ⟶ 𝒳, 𝒱 ×_𝒴 𝒳 ⟶ 𝒳)`. Both comparison 2-cells are identities, by the strict
compatibilities `CategoryTheory.TwoFibreProductOver.gluedComparison_comp_fst` and
`gluedComparison_comp_snd`, so the compatibility square of Stacks 003O is the componentwise
statement that both fillers are identities. -/
def tripleProductPreHom :
    Bicategory.TwoCommSq.PreHom (tripleProductSquare.{v₁, v₂, u₁, u₂} g f b)
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).snd) where
  hom := tripleProductMor.{v₁, v₂, u₁, u₂} g f b
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    exact NatTrans.ext <| funext fun _ => map_id_comp_id_eq _ _ _

/-- **The 2-fibre-product recognition form of the triple product.** The apex
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱)`, with its own first projection to `𝒵 ×_𝒴 𝒳` and with the pairing
`CategoryTheory.CatFiberedInGroupoids.triplePairingMor` to `𝒱 ×_𝒴 𝒳`, is a 2-fibre product of the
cospan `(𝒵 ×_𝒴 𝒳 ⟶ 𝒳, 𝒱 ×_𝒴 𝒳 ⟶ 𝒳)` (**Stacks 003Q**).

This is the triple-product identity
`(𝒵 ×_𝒴 𝒳) ×_𝒵 (𝒵 ×_𝒴 𝒱) ≅ (𝒵 ×_𝒴 𝒳) ×_𝒳 (𝒱 ×_𝒴 𝒳)` of Stacks 02XC read *compatibly with the
projection to `𝒵 ×_𝒴 𝒳`*. -/
noncomputable def isTwoFibreProduct_tripleProductSquare :
    Bicategory.IsTwoFibreProduct (tripleProductSquare.{v₁, v₂, u₁, u₂} g f b) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} b f).snd)
    (tripleProductPreHom.{v₁, v₂, u₁, u₂} g f b)
    (isEquivalence_tripleProductMor.{v₁, v₂, u₁, u₂} g f b)

end

end CategoryTheory.CatFiberedInGroupoids

end
