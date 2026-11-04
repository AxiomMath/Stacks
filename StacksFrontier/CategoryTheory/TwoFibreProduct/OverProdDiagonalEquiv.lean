module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal

/-!
# A 2-fibre product over a base is a base change of the diagonal, as an equivalence

Fix a base category `𝒞` and categories `𝒳`, `𝒴`, `𝒮` over `𝒞` with 1-morphisms `F : 𝒳 ⥤ 𝒮`,
`G : 𝒴 ⥤ 𝒮`. `StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal` exhibits
`𝒳 ×_𝒮 𝒴` as a 2-fibre product of the cospan

```text
F × G : 𝒳 × 𝒴 ⟶ 𝒮 × 𝒮,        Δ : 𝒮 ⟶ 𝒮 × 𝒮
```

through a 2-universal property stated cone by cone. This file turns that universal property into
a *comparison equivalence*: the mediating 1-morphism out of the canonical 2-fibre product
`(𝒳 × 𝒴) ×_{F × G, 𝒮 × 𝒮, Δ} 𝒮` of the cospan is an equivalence of categories, and it commutes
with the two structure functors on the nose.

That is the form in which Stacks 02XE is consumed by the equivalences of Stacks 045G: condition
(1) quantifies over 1-morphisms into `𝒮 × 𝒮` and the conditions on 2-fibre products quantify over
`𝒳 ×_𝒮 𝒴`, and an equivalence *over `𝒞`* between the two apexes is what moves a representability
statement from one quantifier to the other.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.ProdDiag`: the 2-fibre product of the cospan
  `(F × G, Δ)`.
* `CategoryTheory.TwoFibreProductOver.prodDiagComparison`: the mediating 1-morphism
  `ProdDiag ⥤ 𝒳 ×_𝒮 𝒴`, which is `CategoryTheory.TwoFibreProductOver.coneLift` applied to the
  canonical cone of `ProdDiag`.

## Main results

* `CategoryTheory.TwoFibreProductOver.prodDiagComparison_comp_structureFunctor`: the comparison
  is strictly a 1-morphism over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.instIsEquivalenceProdDiagComparison`: it is an
  equivalence.
* `CategoryTheory.TwoFibreProductOver.prodDiagComparisonToProductIso`: the comparison carries the
  first leg of the square to the projection
  `CategoryTheory.TwoFibreProductOver.toProduct`, up to a 2-isomorphism over `𝒞`. This is what a
  representability statement about `toProduct` is transported along: the first leg of a 2-fibre
  product square is where Stacks 0302 applies, and `toProduct` is the 1-morphism a consumer has
  in hand.

## Implementation notes

An object of `ProdDiag` is a quadruple `(T, (x, y, _), s, φ)` with `φ : (F x, G y) ≅ (s, s)` a
vertical isomorphism of the product `𝒮 × 𝒮`, i.e. a pair of isomorphisms `φ_a : F x ≅ s` and
`φ_b : G y ≅ s`; the comparison sends it to `(T, x, y, φ_a ∘ φ_b⁻¹)`. Both halves of the
equivalence are therefore elementary cancellations: the `𝒮`-component `s` of a morphism of
`ProdDiag` is determined by its `𝒳 × 𝒴`-component through the `a`-component of the comparison
square, which is what makes the comparison faithful and full, and every object of `𝒳 ×_𝒮 𝒴`
arises with `s = G y` and `φ = (ψ, 𝟙)`, which is the 2-cell
`CategoryTheory.TwoFibreProductOver.toProductDiagonalIso` evaluated at it.

The comparison isomorphism of an object of a *product* over `𝒞` is forced to be an `eqToHom`
(`CategoryTheory.TwoFibreProductOver.prodOver_iso_hom`), so no compatibility beyond the two
components has to be supplied when a morphism of the product is built by hand.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe vC vX vY vS uC uX uY uS

attribute [local implicit_reducible] fst snd structureFunctor diagonal

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uX} [Category.{vX} 𝒳]
  {𝒴 : Type uY} [Category.{vY} 𝒴] {𝒮 : Type uS} [Category.{vS} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞}
  (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)

/-- The 2-fibre product of the cospan `(F × G, Δ)` over `𝒞`, whose apex Stacks 02XE identifies
with `𝒳 ×_𝒮 𝒴`. -/
abbrev ProdDiag : Type _ :=
  TwoFibreProductOver (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) p𝒮
    (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮) (prodMap F G hF hG) (diagonal (Functor.comp_id p𝒮))

/-- The mediating 1-morphism `(𝒳 × 𝒴) ×_{𝒮 × 𝒮} 𝒮 ⥤ 𝒳 ×_𝒮 𝒴` of Stacks 02XE, obtained by
applying the 2-universal property of `𝒳 ×_𝒮 𝒴` to the canonical cone of `ProdDiag`. -/
noncomputable def prodDiagComparison :
    ProdDiag F G hF hG ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
  coneLift hF hG
    (structureFunctor (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) p𝒮
      (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮) (prodMap F G hF hG) (diagonal (Functor.comp_id p𝒮)))
    (fst _ _ _ _ _) (snd _ _ _ _ _) (psiIso _ _ _ _ _) fst_comp_eq (fun w => w.vertical)

attribute [local implicit_reducible] prodDiagComparison

/-- The `𝒳`-component of the image of an object. -/
@[simp] lemma prodDiagComparison_obj_x (w : ProdDiag F G hF hG) :
    ((prodDiagComparison F G hF hG).obj w).x = w.x.x := rfl

/-- The `𝒴`-component of the image of an object. -/
@[simp] lemma prodDiagComparison_obj_y (w : ProdDiag F G hF hG) :
    ((prodDiagComparison F G hF hG).obj w).y = w.x.y := rfl

/-- The comparison isomorphism of the image of an object. -/
@[simp] lemma prodDiagComparison_obj_iso_hom (w : ProdDiag F G hF hG) :
    ((prodDiagComparison F G hF hG).obj w).iso.hom = w.iso.hom.a ≫ w.iso.inv.b := rfl

/-- The `𝒳`-component of the image of a morphism. -/
@[simp] lemma prodDiagComparison_map_a {w w' : ProdDiag F G hF hG} (u : w ⟶ w') :
    ((prodDiagComparison F G hF hG).map u).a = u.a.a := rfl

/-- The `𝒴`-component of the image of a morphism. -/
@[simp] lemma prodDiagComparison_map_b {w w' : ProdDiag F G hF hG} (u : w ⟶ w') :
    ((prodDiagComparison F G hF hG).map u).b = u.a.b := rfl

/-- The comparison 1-morphism is strictly a 1-morphism of categories over `𝒞`. -/
lemma prodDiagComparison_comp_structureFunctor :
    prodDiagComparison F G hF hG ⋙ structureFunctor p𝒳 p𝒴 p𝒮 F G =
      structureFunctor (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) p𝒮
        (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮) (prodMap F G hF hG)
        (diagonal (Functor.comp_id p𝒮)) :=
  coneLift_comp_structureFunctor ..

/-- The `a`-component of the comparison isomorphism of an object of `ProdDiag` is an
isomorphism, being the image of one under the first projection. -/
instance isIso_prodDiag_iso_hom_a (w : ProdDiag F G hF hG) : IsIso (w.iso.hom.a) := by
  have h : IsIso ((fst p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).map w.iso.hom) := inferInstance
  exact h

/-- The defining relation between the `𝒮`-component of a morphism of `ProdDiag` and its
`𝒳 × 𝒴`-component. -/
lemma prodDiag_hom_rel {w w' : ProdDiag F G hF hG} (u : w ⟶ w') :
    w.iso.hom.a ≫ u.b = F.map u.a.a ≫ w'.iso.hom.a := by
  have h := congrArg Hom.a u.w
  simp only [comp_a, prodMap_map_a, diagonal_map_a] at h
  exact h.symm

/-- The companion relation for the `𝒴`-component. -/
lemma prodDiag_hom_rel' {w w' : ProdDiag F G hF hG} (u : w ⟶ w') :
    w.iso.hom.b ≫ u.b = G.map u.a.b ≫ w'.iso.hom.b := by
  have h := congrArg Hom.b u.w
  simp only [comp_b, prodMap_map_b, diagonal_map_b] at h
  exact h.symm

/-- The comparison 1-morphism `prodDiagComparison` is faithful. -/
instance : (prodDiagComparison F G hF hG).Faithful where
  map_injective {w w'} {u u'} h := by
    have ha : u.a.a = u'.a.a := by
      have h' := congrArg Hom.a h
      exact h'
    have hb : u.a.b = u'.a.b := by
      have h' := congrArg Hom.b h
      exact h'
    refine Hom.ext' (Hom.ext' ha hb) ?_
    have h1 := prodDiag_hom_rel F G hF hG u
    have h2 := prodDiag_hom_rel F G hF hG u'
    rw [← ha] at h2
    exact (cancel_epi (w.iso.hom.a)).1 (h1.trans h2.symm)

/-- The comparison 1-morphism `prodDiagComparison` is full. -/
instance : (prodDiagComparison F G hF hG).Full where
  map_surjective {w w'} ρ := by
    obtain ⟨k, hK⟩ : ∃ k : w.base ⟶ w'.base, k = ρ.hbase := ⟨ρ.hbase, rfl⟩
    obtain ⟨a, hA⟩ : ∃ a : w.x.x ⟶ w'.x.x, a = ρ.a := ⟨ρ.a, rfl⟩
    obtain ⟨b, hB⟩ : ∃ b : w.x.y ⟶ w'.x.y, b = ρ.b := ⟨ρ.b, rfl⟩
    -- the components of the two comparison isomorphisms, at their reduced types
    obtain ⟨αa, hαa⟩ : ∃ t : F.obj w.x.x ⟶ w.y, t = w.iso.hom.a := ⟨w.iso.hom.a, rfl⟩
    obtain ⟨ia, hia⟩ : ∃ t : w.y ⟶ F.obj w.x.x, t = w.iso.inv.a := ⟨w.iso.inv.a, rfl⟩
    obtain ⟨αb, hαb⟩ : ∃ t : G.obj w.x.y ⟶ w.y, t = w.iso.hom.b := ⟨w.iso.hom.b, rfl⟩
    obtain ⟨βb, hβb⟩ : ∃ t : w.y ⟶ G.obj w.x.y, t = w.iso.inv.b := ⟨w.iso.inv.b, rfl⟩
    obtain ⟨αa', hαa'⟩ : ∃ t : F.obj w'.x.x ⟶ w'.y, t = w'.iso.hom.a := ⟨w'.iso.hom.a, rfl⟩
    obtain ⟨αb', hαb'⟩ : ∃ t : G.obj w'.x.y ⟶ w'.y, t = w'.iso.hom.b := ⟨w'.iso.hom.b, rfl⟩
    obtain ⟨βb', hβb'⟩ : ∃ t : w'.y ⟶ G.obj w'.x.y, t = w'.iso.inv.b := ⟨w'.iso.inv.b, rfl⟩
    have hia1 : αa ≫ ia = 𝟙 (F.obj w.x.x) := by
      rw [hαa, hia]
      have h0 := congrArg Hom.a w.iso.hom_inv_id
      simp only [comp_a, id_a] at h0
      exact h0
    have hia2 : ia ≫ αa = 𝟙 w.y := by
      rw [hαa, hia]
      have h0 := congrArg Hom.a w.iso.inv_hom_id
      simp only [comp_a, id_a] at h0
      exact h0
    have hiw : αb ≫ βb = 𝟙 (G.obj w.x.y) := by
      rw [hαb, hβb]
      have h0 := congrArg Hom.b w.iso.hom_inv_id
      simp only [comp_b, id_b] at h0
      exact h0
    have hiw' : βb' ≫ αb' = 𝟙 w'.y := by
      rw [hαb', hβb']
      have h0 := congrArg Hom.b w'.iso.inv_hom_id
      simp only [comp_b, id_b] at h0
      exact h0
    have hax : p𝒳.IsHomLift k a := by rw [hK, hA]; exact ρ.ha
    have hby : p𝒴.IsHomLift k b := by rw [hK, hB]; exact ρ.hb
    have hkx : p𝒳.IsHomLift (eqToHom w.hx ≫ k ≫ eqToHom w'.hx.symm) a :=
      by have := hax; infer_instance
    have hky : p𝒴.IsHomLift (eqToHom w.hx ≫ k ≫ eqToHom w'.hx.symm) b :=
      by have := hby; infer_instance
    have hprodw : p𝒳.map a ≫ (w'.x).iso.hom = (w.x).iso.hom ≫ p𝒴.map b := by
      rw [prodOver_iso_hom (w.x), prodOver_iso_hom (w'.x)]
      exact prodOver_w_eqToHom (w.x).hx (w.x).hy (w'.x).hx (w'.x).hy hkx hky
    -- the `𝒮`-component is forced by the `a`-half of the comparison square
    have h1 : p𝒮.IsHomLift (𝟙 w.base) (w.iso.hom.a) :=
      isHomLift_a w.iso.hom (𝟙 w.base) w.vertical
    have h3 : p𝒮.IsHomLift (𝟙 w'.base) αa' := by
      rw [hαa']; exact isHomLift_a w'.iso.hom (𝟙 w'.base) w'.vertical
    have hvinv : (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).IsHomLift (𝟙 w.base) w.iso.inv :=
      @IsHomLift.lift_id_inv 𝒞 (TwoFibreProductOver p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮) _ _
        (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮) w.base _ _ w.iso w.vertical
    have h1' : p𝒮.IsHomLift (𝟙 w.base) ia := by
      rw [hia]
      exact isHomLift_a w.iso.inv (𝟙 w.base) hvinv
    have h2 : p𝒮.IsHomLift k (F.map a) :=
      @Functor.isHomLift_map_of_comp_eq 𝒞 _ 𝒳 _ 𝒮 _ p𝒳 p𝒮 F hF _ _ k _ _ a hax
    have h23 : p𝒮.IsHomLift (k ≫ 𝟙 w'.base) (F.map a ≫ αa') :=
      @IsHomLift.comp 𝒞 𝒮 _ _ p𝒮 _ _ _ _ _ _ k (𝟙 w'.base) (F.map a) αa' h2 h3
    have hc : p𝒮.IsHomLift (𝟙 w.base ≫ k ≫ 𝟙 w'.base) (ia ≫ F.map a ≫ αa') :=
      @IsHomLift.comp 𝒞 𝒮 _ _ p𝒮 _ _ _ _ _ _ (𝟙 w.base) (k ≫ 𝟙 w'.base)
        ia (F.map a ≫ αa') h1' h23
    rw [Category.id_comp, Category.comp_id] at hc
    have hsq : F.map a ≫ αa' ≫ βb' = αa ≫ βb ≫ G.map b := by
      rw [hαa, hβb, hαa', hβb']
      have h := ρ.w
      rw [← hA, ← hB] at h
      simp only [prodDiagComparison_obj_iso_hom] at h
      exact h.trans (Category.assoc _ _ _)
    have step : ia ≫ F.map a ≫ αa' ≫ βb' = βb ≫ G.map b := by
      rw [hsq, ← Category.assoc, hia2, Category.id_comp]
    have hkey : αb ≫ ia ≫ F.map a ≫ αa' = G.map b ≫ αb' := by
      have h := congrArg (fun t : w.y ⟶ G.obj w'.x.y => αb ≫ t ≫ αb') step
      simp only [Category.assoc, hiw', Category.comp_id] at h
      rw [← Category.assoc αb βb, hiw, Category.id_comp] at h
      exact h
    refine ⟨{ hbase := k
              a := { hbase := eqToHom w.hx ≫ k ≫ eqToHom w'.hx.symm
                     a := a
                     b := b
                     ha := hkx
                     hb := hky
                     w := hprodw }
              b := ia ≫ F.map a ≫ αa'
              ha := structureFunctor_isHomLift _ k hax
              hb := hc
              w := ?_ }, ?_⟩
    · refine Hom.ext' ?_ ?_
      · simp only [comp_a, prodMap_map_a, diagonal_map_a]
        rw [← hαa, ← hαa']
        exact ((Category.id_comp (F.map a ≫ αa')).symm.trans
          (congrArg (fun t => t ≫ F.map a ≫ αa') hia1.symm)).trans
            (Category.assoc αa ia (F.map a ≫ αa'))
      · simp only [comp_b, prodMap_map_b, diagonal_map_b]
        rw [← hαb, ← hαb']
        exact hkey.symm
    · exact Hom.ext' hA hB

/-- The comparison 1-morphism `prodDiagComparison` is essentially surjective. -/
instance : (prodDiagComparison F G hF hG).EssSurj where
  mem_essImage P := by
    have he2 : ((toProductDiagonalIso F G hF hG).app P).hom.b = 𝟙 (G.obj P.y) := rfl
    have hbinv : ((toProductDiagonalIso F G hF hG).app P).inv.b = 𝟙 (G.obj P.y) := by
      have h0 := congrArg Hom.b ((toProductDiagonalIso F G hF hG).app P).hom_inv_id
      simp only [comp_b, id_b] at h0
      have h1 : 𝟙 (G.obj P.y) ≫ ((toProductDiagonalIso F G hF hG).app P).inv.b
          = 𝟙 (G.obj P.y) := h0
      exact (Category.id_comp _).symm.trans h1
    have he : ((toProductDiagonalIso F G hF hG).app P).hom.a = P.iso.hom := rfl
    refine ⟨{ base := P.base
              x := (toProduct p𝒳 p𝒴 p𝒮 F G).obj P
              y := G.obj P.y
              hx := rfl
              hy := obj_eq_of_comp_eq hG P.hy
              iso := (toProductDiagonalIso F G hF hG).app P
              vertical := structureFunctor_isHomLift _ (𝟙 P.base) (by
                have h : p𝒮.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
                rw [he]
                exact h) }, ⟨?_⟩⟩
    refine isoMkVertical (U := P.base) (Iso.refl P.x) (Iso.refl P.y)
      (IsHomLift.id P.hx) (IsHomLift.id P.hy) ?_
    have hi : ((toProductDiagonalIso F G hF hG).app P).hom.a ≫
        ((toProductDiagonalIso F G hF hG).app P).inv.b = P.iso.hom := by
      rw [he, hbinv]
      exact Category.comp_id _
    have hL : F.map (𝟙 P.x) ≫ P.iso.hom = P.iso.hom := by simp
    have hR : P.iso.hom ≫ G.map (𝟙 P.y) = P.iso.hom := by simp
    exact hL.trans (hR.symm.trans (congrArg (fun t => t ≫ G.map (𝟙 P.y)) hi.symm))

/-- The comparison 1-morphism `prodDiagComparison` is an equivalence of categories. -/
instance instIsEquivalenceProdDiagComparison :
    (prodDiagComparison F G hF hG).IsEquivalence :=
  Functor.IsEquivalence.mk

attribute [local implicit_reducible] toProduct

/-- The first leg of the 2-fibre product square of the cospan `(F × G, Δ)`: the projection of
`ProdDiag` to the product `𝒳 × 𝒴`. -/
abbrev prodDiagFst : ProdDiag F G hF hG ⥤ TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 :=
  fst (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) p𝒮
    (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮) (prodMap F G hF hG)
    (diagonal (Functor.comp_id p𝒮))

/-- The component at `w` of `prodDiagComparisonToProductIso`: both objects have the same two
components, and their comparison isomorphisms are the forced `eqToHom` of a product over `𝒞`, so
the isomorphism is the identity in both components. -/
noncomputable def prodDiagComparisonToProductIsoApp (w : ProdDiag F G hF hG) :
    (toProduct p𝒳 p𝒴 p𝒮 F G).obj ((prodDiagComparison F G hF hG).obj w) ≅
      (prodDiagFst F G hF hG).obj w :=
  isoMkVertical (U := w.base) (Iso.refl w.x.x) (Iso.refl w.x.y)
    (IsHomLift.id (w.x.hx.trans w.hx)) (IsHomLift.id (w.x.hy.trans w.hx))
    (by
      simp only [toProduct_obj_x, prodDiagComparison_obj_x, Iso.refl_hom, Functor.map_id,
        Category.id_comp, toProduct_obj_y, prodDiagComparison_obj_y, toProduct_obj_iso,
        Category.comp_id]
      exact prodOver_iso_hom _)

/-- The `𝒳`-component of `prodDiagComparisonToProductIsoApp` is the identity. -/
@[simp] lemma prodDiagComparisonToProductIsoApp_hom_a (w : ProdDiag F G hF hG) :
    (prodDiagComparisonToProductIsoApp F G hF hG w).hom.a = 𝟙 _ := rfl

/-- The `𝒴`-component of `prodDiagComparisonToProductIsoApp` is the identity. -/
@[simp] lemma prodDiagComparisonToProductIsoApp_hom_b (w : ProdDiag F G hF hG) :
    (prodDiagComparisonToProductIsoApp F G hF hG w).hom.b = 𝟙 _ := rfl

/-- **The comparison equivalence of Stacks 02XE identifies `toProduct` with the first leg of the
square.** Composing the comparison `ProdDiag ⥤ 𝒳 ×_𝒮 𝒴` with the projection to `𝒳 × 𝒴` gives the
first projection of `ProdDiag`, up to an isomorphism which is the identity in both components. -/
noncomputable def prodDiagComparisonToProductIso :
    prodDiagComparison F G hF hG ⋙ toProduct p𝒳 p𝒴 p𝒮 F G ≅ prodDiagFst F G hF hG :=
  NatIso.ofComponents (prodDiagComparisonToProductIsoApp F G hF hG) (by
    intro w w' u
    exact Hom.ext' (by simp) (by simp))

/-- The components of `prodDiagComparisonToProductIso` are vertical, so it is a 2-isomorphism
over `𝒞`. -/
lemma isHomLift_prodDiagComparisonToProductIso_hom_app (w : ProdDiag F G hF hG) :
    (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 w.base)
      ((prodDiagComparisonToProductIso F G hF hG).hom.app w) :=
  structureFunctor_isHomLift _ (𝟙 w.base) (IsHomLift.id (w.x.hx.trans w.hx))

end CategoryTheory.TwoFibreProductOver

end
