module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange

/-!
# The self-product of a base change is a base change of its first projection

Fix a base category `𝒞` and categories `𝒳`, `𝒱`, `𝒴` over `𝒞` with 1-morphisms `h : 𝒳 ⥤ 𝒴` and
`s : 𝒱 ⥤ 𝒴`. Write `𝒰 = 𝒳 ×_𝒴 𝒱` for the 2-fibre product over `𝒞` of Stacks 0040, `r : 𝒰 ⥤ 𝒳`
for its first projection, `f' : 𝒰 ⥤ 𝒱` for its second, `𝒲 = 𝒰 ×_𝒱 𝒰` for the self-product of `𝒰`
over `𝒱` along `f'`, and `𝒟 = 𝒳 ×_𝒴 𝒳`.
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange` builds the 1-morphism
`r × r : 𝒲 ⥤ 𝒟` (`CategoryTheory.TwoFibreProductOver.mapDiag`) and exhibits the diagonal of `f'`
as a base change of the diagonal of `h` along it. This file identifies `r × r` itself:

```text
            r × r
    𝒲  ------------->  𝒟 = 𝒳 ×_𝒴 𝒳
    |                       |
pr₁ |                       | pr₁
    v                       v
    𝒰  --r----------->  𝒳
```

is a 2-fibre product square, so **`r × r` is a base change of `r`** — and `r` is a base change of
`s`, so `r × r` is a base change of the cover `s` along the structural 1-morphism `𝒟 ⥤ 𝒴`.

The content is the elementary identification `𝒰 ×_𝒱 𝒰 ≃ 𝒟 ×_𝒳 𝒰`: an object of the left side is
a pair `(x₁, y₁, ψ₁)`, `(x₂, y₂, ψ₂)` of objects of `𝒰` together with a vertical isomorphism
`σ : y₁ ≅ y₂`, and an object of the right side is an object `(x₁, x₂, α)` of `𝒟`, an object
`(x, y, ψ)` of `𝒰` and a vertical isomorphism `x₁ ≅ x`; the comparison keeps `(x₁, y₁, ψ₁)` and
replaces the second factor by `r × r` of the pair, splicing `σ` into the comparison isomorphism,
and it is an equivalence because the second factor's `𝒱`-component and its comparison isomorphism
are recoverable from `σ`.

This is **not** an instance of either cancellation of
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct` or
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct`, for the reason recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognition`: a cancellation reads
`(𝒜 ×_𝒴 ℬ) ×_ℬ 𝒰` as a 2-fibre product of a cospan whose legs are the outer projection and a
composite through an inner projection, so it never exposes a leg whose *target* is itself a
2-fibre product — and `r × r`, whose target is `𝒟`, is exactly such a leg. Nor is it an instance
of `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare`, which recognises
the triple product glued along the **first** factor of both halves, while `𝒲` is glued along the
**second**: in the notation there `𝒲` is `gluedAlongSecond` with `𝒵 = 𝒱 = 𝒳` exchanged against
`𝒳 = 𝒱`, and that file's recognition is proved for `gluedAlongFirst` only.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.CoverBaseChange`: the canonical 2-fibre product
  `𝒟 ×_𝒳 𝒰` of the cospan `(pr₁ : 𝒟 ⥤ 𝒳, r : 𝒰 ⥤ 𝒳)`.
* `CategoryTheory.TwoFibreProductOver.coverComparison`: the comparison `𝒲 ⥤ 𝒟 ×_𝒳 𝒰`.

## Main results

* `CategoryTheory.TwoFibreProductOver.coverComparison_comp_fst` and `_comp_snd`: the comparison
  carries the two projections of `𝒟 ×_𝒳 𝒰` to `r × r` and to the first projection of `𝒲`, on the
  nose.
* `CategoryTheory.TwoFibreProductOver.instIsEquivalenceCoverComparison`: the comparison is an
  equivalence of categories.

## Implementation notes

The comparison is *strictly* compatible with both projections and with the structure functor, and
its comparison isomorphism is the identity, because `r × r` and the first projection of `𝒲` have
the same `𝒳`-component on the nose (`CategoryTheory.TwoFibreProductOver.mapDiag_obj_x` is `rfl`).
That is what lets the 2-commutative square assembled from it in
`StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCoverBaseChangeSquare` carry identity comparison
2-cells, exactly as the two cancellation files do.

Equivalence is proved by faithful + full + essentially surjective rather than by an explicit
quasi-inverse: the round trip replaces the second factor `(x₂, y₂, ψ₂)` of an object of `𝒲` by
`(x₂, y₁, ψ₂ ∘ s(σ)⁻¹)`, which differs from it by `σ`, so a unit would carry `σ` anyway.

Essential surjectivity is the only part needing `hh : h ⋙ p𝒴 = p𝒳`: the comparison isomorphism
of the object of `𝒰` built out of an object of `𝒟 ×_𝒳 𝒰` has `h` applied to the vertical
isomorphism of that object, and `h` sends vertical morphisms to vertical morphisms only when it
is a 1-morphism over `𝒞`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

attribute [local implicit_reducible] fst snd structureFunctor mapDiag

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒱 : Type u₃} [Category.{v₃} 𝒱] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒱 : 𝒱 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {h : 𝒳 ⥤ 𝒴} {s : 𝒱 ⥤ 𝒴}

/-- `𝒰 = 𝒳 ×_𝒴 𝒱`, the base change of `h` along `s`. -/
local notation "𝒰" => TwoFibreProductOver p𝒳 p𝒱 p𝒴 h s

/-- `𝒲 = 𝒰 ×_𝒱 𝒰`, the self-product of `𝒰` over `𝒱`. -/
local notation "𝒲" =>
  TwoFibreProductOver (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
    (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s)

/-- `𝒟 = 𝒳 ×_𝒴 𝒳`, the target of `r × r`. -/
local notation "𝒟" => TwoFibreProductOver p𝒳 p𝒳 p𝒴 h h

/-- The canonical 2-fibre product `𝒟 ×_𝒳 𝒰` of the cospan `(pr₁ : 𝒟 ⥤ 𝒳, r : 𝒰 ⥤ 𝒳)`: the base
change of the first projection of `𝒰` along the first projection of `𝒟`. -/
abbrev CoverBaseChange : Type _ :=
  TwoFibreProductOver (structureFunctor p𝒳 p𝒳 p𝒴 h h) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒳
    (fst p𝒳 p𝒳 p𝒴 h h) (fst p𝒳 p𝒱 p𝒴 h s)

/-- **The comparison `𝒰 ×_𝒱 𝒰 ⥤ 𝒟 ×_𝒳 𝒰`.** It sends `w = (U, u₁, u₂, σ)` to the object whose
`𝒟`-component is `(r × r) w`, whose `𝒰`-component is `u₁`, and whose comparison isomorphism is
the identity, the `𝒳`-component of `(r × r) w` being the `𝒳`-component of `u₁` on the nose. -/
def coverComparison (hs : s ⋙ p𝒴 = p𝒱) : 𝒲 ⥤ CoverBaseChange (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴)
    (h := h) (s := s) where
  obj w :=
    { base := w.base
      x := (mapDiag hs).obj w
      y := w.x
      hx := rfl
      hy := w.hx
      iso := Iso.refl w.x.x
      vertical := IsHomLift.id (w.x.hx.trans w.hx) }
  map f :=
    { hbase := f.hbase
      a := (mapDiag hs).map f
      b := f.a
      ha := structureFunctor_isHomLift _ f.hbase (isHomLift_a f.a f.hbase f.ha)
      hb := f.ha
      w := (Category.comp_id f.a.a).trans (Category.id_comp f.a.a).symm }
  map_id w := Hom.ext' ((mapDiag hs).map_id w) rfl
  map_comp f g := Hom.ext' ((mapDiag hs).map_comp f g) rfl

attribute [local implicit_reducible] coverComparison

/-- The `𝒟`-component of the image of an object is `(r × r) w`. -/
@[simp] lemma coverComparison_obj_x (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) :
    ((coverComparison hs).obj w).x = (mapDiag hs).obj w := rfl

/-- The `𝒰`-component of the image of an object is the first factor. -/
@[simp] lemma coverComparison_obj_y (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) :
    ((coverComparison hs).obj w).y = w.x := rfl

/-- The comparison isomorphism of the image of an object is the identity. -/
@[simp] lemma coverComparison_obj_iso (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) :
    ((coverComparison hs).obj w).iso = Iso.refl w.x.x := rfl

/-- The `𝒟`-component of the image of a morphism is `(r × r) f`. -/
@[simp] lemma coverComparison_map_a (hs : s ⋙ p𝒴 = p𝒱) {w w' : 𝒲} (f : w ⟶ w') :
    ((coverComparison hs).map f).a = (mapDiag hs).map f := rfl

/-- The `𝒰`-component of the image of a morphism is its first component. -/
@[simp] lemma coverComparison_map_b (hs : s ⋙ p𝒴 = p𝒱) {w w' : 𝒲} (f : w ⟶ w') :
    ((coverComparison hs).map f).b = f.a := rfl

/-- The comparison is strictly a 1-morphism of categories over `𝒞`. -/
@[simp] lemma coverComparison_comp_structureFunctor (hs : s ⋙ p𝒴 = p𝒱) :
    coverComparison hs ⋙ structureFunctor (structureFunctor p𝒳 p𝒳 p𝒴 h h)
        (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒳 (fst p𝒳 p𝒳 p𝒴 h h) (fst p𝒳 p𝒱 p𝒴 h s) =
      structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
        (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s) := rfl

/-- The comparison followed by the projection to `𝒟` is `r × r`, on the nose. -/
@[simp] lemma coverComparison_comp_fst (hs : s ⋙ p𝒴 = p𝒱) :
    coverComparison hs ⋙ fst (structureFunctor p𝒳 p𝒳 p𝒴 h h)
        (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒳 (fst p𝒳 p𝒳 p𝒴 h h) (fst p𝒳 p𝒱 p𝒴 h s) =
      mapDiag hs := rfl

/-- The comparison followed by the projection to `𝒰` is the first projection of `𝒲`, on the
nose. -/
@[simp] lemma coverComparison_comp_snd (hs : s ⋙ p𝒴 = p𝒱) :
    coverComparison hs ⋙ snd (structureFunctor p𝒳 p𝒳 p𝒴 h h)
        (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒳 (fst p𝒳 p𝒳 p𝒴 h h) (fst p𝒳 p𝒱 p𝒴 h s) =
      fst (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
        (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s) := rfl

/-- The `𝒱`-component of the second factor of a morphism of `𝒲` is determined by that of the
first factor, through the two structural isomorphisms. -/
lemma snd_b_eq {w w' : 𝒲} (f : w ⟶ w') :
    f.b.b = w.iso.inv ≫ f.a.b ≫ w'.iso.hom :=
  ((Iso.inv_comp_eq w.iso).2 f.w).symm

/-- The comparison `𝒲 ⥤ 𝒟 ×_𝒳 𝒰` is faithful. -/
instance instFaithfulCoverComparison (hs : s ⋙ p𝒴 = p𝒱) :
    (coverComparison (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (h := h) (s := s) hs).Faithful where
  map_injective {w w'} {u u'} hu := by
    have hb : u.a = u'.a := congrArg Hom.b hu
    refine Hom.ext' hb (Hom.ext' (congrArg Hom.b (congrArg Hom.a hu)) ?_)
    rw [snd_b_eq u, snd_b_eq u', hb]

/-- The two `𝒳`-components of a morphism out of the image of the comparison agree: the
comparison isomorphism of an image object is the identity. -/
lemma coverComparison_hom_rel (hs : s ⋙ p𝒴 = p𝒱) {w w' : 𝒲}
    (ρ : (coverComparison hs).obj w ⟶ (coverComparison hs).obj w') : ρ.a.a = ρ.b.a := by
  exact (Category.comp_id _).symm.trans (ρ.w.trans (Category.id_comp _))

/-- The comparison `𝒲 ⥤ 𝒟 ×_𝒳 𝒰` is full. -/
instance instFullCoverComparison (hs : s ⋙ p𝒴 = p𝒱) :
    (coverComparison (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (h := h) (s := s) hs).Full where
  map_surjective {w w'} ρ := by
    have hab : ρ.a.a = ρ.b.a := coverComparison_hom_rel hs ρ
    have hρab : p𝒳.IsHomLift ρ.hbase ρ.a.b := isHomLift_b ρ.a ρ.hbase ρ.ha
    have hcomp : p𝒱.IsHomLift ρ.hbase (w.iso.inv ≫ ρ.b.b ≫ w'.iso.hom) := by
      obtain ⟨k, hk⟩ : ∃ k : w.base ⟶ w'.base, k = ρ.hbase := ⟨ρ.hbase, rfl⟩
      obtain ⟨Bb, hBb⟩ : ∃ B : w.x.y ⟶ w'.x.y, B = ρ.b.b := ⟨ρ.b.b, rfl⟩
      have h₁ : p𝒱.IsHomLift (𝟙 w.base) w.iso.inv := by
        have := w.vertical
        infer_instance
      have h₂ : p𝒱.IsHomLift k Bb := by
        rw [hk, hBb]
        exact isHomLift_b ρ.b ρ.hbase ρ.hb
      have h₃ : p𝒱.IsHomLift (𝟙 w'.base) w'.iso.hom := w'.vertical
      have hc : p𝒱.IsHomLift k (w.iso.inv ≫ Bb ≫ w'.iso.hom) := inferInstance
      rw [hk, hBb] at hc
      exact hc
    have hB : h.map ρ.b.a ≫ w'.x.iso.hom = w.x.iso.hom ≫ s.map ρ.b.b := ρ.b.w
    have hsq : h.map ρ.a.b ≫ w'.y.iso.hom
        = w.y.iso.hom ≫ s.map (w.iso.inv ≫ ρ.b.b ≫ w'.iso.hom) := by
      have hA := ρ.a.w
      simp only [coverComparison_obj_x, mapDiag_obj_iso, mapDiagIso_hom, sndIso_hom] at hA
      rw [hab] at hA
      have hD : s.map ρ.b.b ≫ s.map w'.iso.hom ≫ w'.y.iso.inv
          = s.map w.iso.hom ≫ w.y.iso.inv ≫ h.map ρ.a.b := by
        refine (cancel_epi w.x.iso.hom).1 ?_
        rw [← reassoc_of% hB]
        simpa only [Category.assoc] using hA
      have hE : s.map w.iso.inv ≫ s.map ρ.b.b ≫ s.map w'.iso.hom ≫ w'.y.iso.inv
          = w.y.iso.inv ≫ h.map ρ.a.b := by
        rw [hD, ← reassoc_of% (s.map_comp w.iso.inv w.iso.hom)]
        simp
      have hF := congrArg (fun t => w.y.iso.hom ≫ t ≫ w'.y.iso.hom) hE
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.hom_inv_id_assoc] at hF
      rw [s.map_comp, s.map_comp]
      exact hF.symm
    refine ⟨{ hbase := ρ.hbase
              a := ρ.b
              b := { hbase := eqToHom w.hy ≫ ρ.hbase ≫ eqToHom w'.hy.symm
                     a := ρ.a.b
                     b := w.iso.inv ≫ ρ.b.b ≫ w'.iso.hom
                     ha := by have := hρab; infer_instance
                     hb := by have := hcomp; infer_instance
                     w := hsq }
              ha := ρ.hb
              hb := structureFunctor_isHomLift _ ρ.hbase hρab
              w := (Iso.hom_inv_id_assoc w.iso (ρ.b.b ≫ w'.iso.hom)).symm }, ?_⟩
    exact Hom.ext' (Hom.ext' hab.symm rfl) rfl

/-- **The comparison is essentially surjective.** An object of `𝒟 ×_𝒳 𝒰` is
`((x₁, x₂, α), (x, y, ψ), χ : x₁ ≅ x)`, and it is the image of the object of `𝒰 ×_𝒱 𝒰` whose two
factors are `(x₁, y, h(χ) ∘ ψ)` and `(x₂, y, α⁻¹ ∘ h(χ) ∘ ψ)` glued along the identity of `y`.
This is the only part of the equivalence that needs `h` to be a 1-morphism over `𝒞`: the
comparison isomorphism of the first factor applies `h` to the vertical isomorphism `χ`. -/
theorem essSurj_coverComparison (hh : h ⋙ p𝒴 = p𝒳) (hs : s ⋙ p𝒴 = p𝒱) :
    (coverComparison (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (h := h) (s := s) hs).EssSurj where
  mem_essImage P := by
    have hPx : p𝒳.obj P.x.x = P.base := P.x.hx.trans P.hx
    have hPx' : p𝒳.obj P.x.y = P.base := P.x.hy.trans P.hx
    have hPy : p𝒱.obj P.y.y = P.base := P.y.hy.trans P.hy
    have hPv : p𝒳.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    have hv {U : 𝒞} (hU : U = P.base) {a b : 𝒴} {e : a ⟶ b} (he : p𝒴.IsHomLift (𝟙 U) e) :
        p𝒴.IsHomLift (𝟙 P.base) e := hU ▸ he
    have hvert : p𝒴.IsHomLift (𝟙 P.base) (h.map P.iso.hom ≫ P.y.iso.hom) := by
      have := Functor.isHomLift_map_of_comp_eq hh (𝟙 P.base) P.iso.hom
      have := hv P.hy P.y.vertical
      infer_instance
    have hvert' : p𝒴.IsHomLift (𝟙 P.base)
        (P.x.iso.inv ≫ h.map P.iso.hom ≫ P.y.iso.hom) := by
      have := hv P.hx P.x.vertical
      infer_instance
    refine ⟨{ base := P.base
              x := { base := P.base
                     x := P.x.x
                     y := P.y.y
                     hx := hPx
                     hy := hPy
                     iso := h.mapIso P.iso ≪≫ P.y.iso
                     vertical := hvert }
              y := { base := P.base
                     x := P.x.y
                     y := P.y.y
                     hx := hPx'
                     hy := hPy
                     iso := P.x.iso.symm ≪≫ h.mapIso P.iso ≪≫ P.y.iso
                     vertical := hvert' }
              hx := rfl
              hy := rfl
              iso := Iso.refl P.y.y
              vertical := IsHomLift.id hPy }, ⟨?_⟩⟩
    refine isoMkVertical (U := P.base) (isoMkVertical (U := P.base) (Iso.refl P.x.x)
      (Iso.refl P.x.y) (IsHomLift.id hPx) (IsHomLift.id hPx') ?_)
      (isoMkVertical (U := P.base) P.iso (Iso.refl P.y.y) hPv (IsHomLift.id hPy) ?_)
      ?_ ?_ rfl
    · simp
    · show h.map P.iso.hom ≫ P.y.iso.hom
        = (h.mapIso P.iso ≪≫ P.y.iso).hom ≫ s.map (𝟙 P.y.y)
      simp
    · exact structureFunctor_isHomLift _ (𝟙 P.base) (IsHomLift.id hPx)
    · exact structureFunctor_isHomLift _ (𝟙 P.base) hPv

/-- **The comparison `𝒰 ×_𝒱 𝒰 ⥤ 𝒟 ×_𝒳 𝒰` is an equivalence of categories.** -/
theorem isEquivalence_coverComparison (hh : h ⋙ p𝒴 = p𝒳) (hs : s ⋙ p𝒴 = p𝒱) :
    (coverComparison (p𝒳 := p𝒳) (p𝒱 := p𝒱) (p𝒴 := p𝒴) (h := h) (s := s) hs).IsEquivalence :=
  have := essSurj_coverComparison hh hs
  Functor.IsEquivalence.mk

end CategoryTheory.TwoFibreProductOver

end
