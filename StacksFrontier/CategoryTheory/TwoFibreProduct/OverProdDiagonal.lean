module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# A 2-fibre product over a base as a base change of the diagonal (Stacks 02XE, over `𝒞`)

Fix a base category `𝒞` and categories `𝒳`, `𝒴`, `𝒮` over `𝒞` with 1-morphisms `F : 𝒳 ⥤ 𝒮`
and `G : 𝒴 ⥤ 𝒮`. Alongside the 2-fibre product `𝒳 ×_𝒮 𝒴` over `𝒞` of Stacks 0040
(`CategoryTheory.TwoFibreProductOver`) one has the *product* `𝒳 × 𝒴`, namely the 2-fibre
product over the final object `𝟭 𝒞`, and the cospan

```text
F × G : 𝒳 × 𝒴 ⟶ 𝒮 × 𝒮,        Δ : 𝒮 ⟶ 𝒮 × 𝒮
```

of the product of the two 1-morphisms with the diagonal of `𝒮`. Stacks 02XE says that
`𝒳 ×_𝒮 𝒴` is a 2-fibre product of that cospan. This file provides the square and the
2-universal property of its apex, all in the 2-category of categories *over* `𝒞`:

* `CategoryTheory.TwoFibreProductOver.prodMap` and
  `CategoryTheory.TwoFibreProductOver.toProduct` are the 1-morphism `F × G` and the
  projection `𝒳 ×_𝒮 𝒴 ⥤ 𝒳 × 𝒴`, which is the first leg of the square; the second leg is
  `snd ⋙ G`, and `CategoryTheory.TwoFibreProductOver.toProductDiagonalIso` is the 2-cell
  filling it, with components `(φ, 𝟙)` on an object `(U, x, y, φ)`;
* `CategoryTheory.TwoFibreProductOver.coneLift` is the mediating 1-morphism of a test cone,
  `CategoryTheory.TwoFibreProductOver.coneCompat` its compatibility, and
  `CategoryTheory.TwoFibreProductOver.coneLiftIso` the uniqueness.

Everything here is the over-`𝒞` form of Stacks 02XE. The absolute version, for Mathlib's
`CategoryTheory.Limits.CategoricalPullback` (Stacks 003R), is in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Diagonal`, and it does **not** give these: the
comparison isomorphism of an object is arbitrary in the absolute 2-fibre product and vertical
in the relative one, and the two notions are inequivalent.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.prodMap`: the product `F × G : 𝒳 × 𝒴 ⥤ 𝒮 × 𝒮'` of two
  1-morphisms over `𝒞`, with independent targets.
* `CategoryTheory.TwoFibreProductOver.toProduct`: the projection `𝒳 ×_𝒮 𝒴 ⥤ 𝒳 × 𝒴`.
* `CategoryTheory.TwoFibreProductOver.toProductDiagonalIso`: the 2-cell filling the square.
* `CategoryTheory.TwoFibreProductOver.coneLift`: the mediating 1-morphism of a test cone over
  the cospan `(F × G, Δ)`.

## Main results

* `CategoryTheory.TwoFibreProductOver.coneCompat`: the mediating 1-morphism is a morphism of
  test cones.
* `CategoryTheory.TwoFibreProductOver.coneLiftIso`,
  `CategoryTheory.TwoFibreProductOver.coneRelFst` and
  `CategoryTheory.TwoFibreProductOver.coneRelSnd`: it is the only one, up to a 2-isomorphism
  over `𝒞` compatible with both comparison 2-cells.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe vC vX vY vS vS' vT uC uX uY uS uS' uT

attribute [local implicit_reducible] fst snd structureFunctor diagonal

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uX} [Category.{vX} 𝒳]
  {𝒴 : Type uY} [Category.{vY} 𝒴] {𝒮 : Type uS} [Category.{vS} 𝒮]
  {𝒮' : Type uS'} [Category.{vS'} 𝒮']
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞}

/-- An elementary cancellation: from `τ ≫ s = e₂` one gets `s ≫ e₂⁻¹ = τ⁻¹`. -/
lemma iso_cancel_inv {D : Type uT} [Category.{vT} D] {B₁ B₂ C : D} (e₂ : B₁ ≅ B₂) (τ : B₁ ≅ C)
    (s : C ≅ B₂) (hcb : τ.hom ≫ s.hom = e₂.hom) : s.hom ≫ e₂.inv = τ.inv := by
  rw [← Category.id_comp (s.hom ≫ e₂.inv), ← τ.inv_hom_id, Category.assoc,
    ← Category.assoc τ.hom, hcb, e₂.hom_inv_id, Category.comp_id]

/-- An elementary cancellation: from `ψ ≫ s = e₁ ≫ g` and `τ ≫ s = e₂` one gets
`e₁⁻¹ ≫ ψ ≫ τ⁻¹ = g ≫ e₂⁻¹`. -/
lemma iso_cancel_aux {D : Type uT} [Category.{vT} D] {A₁ A₂ B₁ B₂ C : D} (e₁ : A₁ ≅ A₂)
    (e₂ : B₁ ≅ B₂) (τ : B₁ ≅ C) (s : C ≅ B₂) (ψ : A₁ ⟶ C) (g : A₂ ⟶ B₂)
    (hca : ψ ≫ s.hom = e₁.hom ≫ g) (hcb : τ.hom ≫ s.hom = e₂.hom) :
    e₁.inv ≫ ψ ≫ τ.inv = g ≫ e₂.inv := by
  rw [← iso_cancel_inv e₂ τ s hcb, ← Category.assoc ψ, hca, Category.assoc, ← Category.assoc,
    e₁.inv_hom_id, Category.id_comp]

/-- An `eqToHom` between objects of `𝒞` equal to `U` lies over `𝟙 U` for the identity functor. -/
lemma isHomLift_id_eqToHom {U A B : 𝒞} (hA : A = U) (hB : B = U) (h : A = B) :
    (𝟭 𝒞).IsHomLift (𝟙 U) (eqToHom h) :=
  IsHomLift.of_fac' (𝟭 𝒞) (𝟙 U) (eqToHom h) hA hB (by subst hA; subst hB; simp)

/-- The comparison isomorphism of an object of the product over `𝒞` is the canonical `eqToHom`
identifying the images of its two components. -/
lemma prodOver_iso_hom (P : TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) :
    P.iso.hom = eqToHom (P.hx.trans P.hy.symm) := by
  have := P.vertical
  have h := IsHomLift.fac' (𝟭 𝒞) (𝟙 P.base) P.iso.hom
  simpa using h

/-- If `a` and `b` lie over the same morphism `k`, then `p𝒳.map a` and `p𝒴.map b` commute with
the canonical `eqToHom` comparisons of source and target. -/
lemma prodOver_w_eqToHom {base base' : 𝒞} {x x' : 𝒳} {y y' : 𝒴}
    (hx : p𝒳.obj x = base) (hy : p𝒴.obj y = base)
    (hx' : p𝒳.obj x' = base') (hy' : p𝒴.obj y' = base')
    {k : base ⟶ base'} {a : x ⟶ x'} {b : y ⟶ y'}
    (ha : p𝒳.IsHomLift k a) (hb : p𝒴.IsHomLift k b) :
    p𝒳.map a ≫ eqToHom (hx'.trans hy'.symm) = eqToHom (hx.trans hy.symm) ≫ p𝒴.map b := by
  have := ha
  have := hb
  rw [IsHomLift.fac' p𝒳 k a, IsHomLift.fac' p𝒴 k b]
  simp

/-- An object lying over `U` has its image under a 1-morphism over `𝒞` lying over `U`. -/
lemma obj_eq_of_comp_eq {F : 𝒳 ⥤ 𝒮} (hF : F ⋙ p𝒮 = p𝒳) {x : 𝒳} {U : 𝒞} (h : p𝒳.obj x = U) :
    p𝒮.obj (F.obj x) = U :=
  (show p𝒮.obj (F.obj x) = p𝒳.obj x from Functor.congr_obj hF x).trans h

/-- The product `F × G : 𝒳 × 𝒴 ⥤ 𝒮 × 𝒮'` of two 1-morphisms over `𝒞`, with independent
targets. -/
def prodMap (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮') (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮' = p𝒴) :
    TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 ⥤ TwoFibreProductOver p𝒮 p𝒮' (𝟭 𝒞) p𝒮 p𝒮' where
  obj P :=
    { base := P.base
      x := F.obj P.x
      y := G.obj P.y
      hx := obj_eq_of_comp_eq hF P.hx
      hy := obj_eq_of_comp_eq hG P.hy
      iso := eqToIso ((obj_eq_of_comp_eq hF P.hx).trans (obj_eq_of_comp_eq hG P.hy).symm)
      vertical := isHomLift_id_eqToHom (obj_eq_of_comp_eq hF P.hx) (obj_eq_of_comp_eq hG P.hy)
        ((obj_eq_of_comp_eq hF P.hx).trans (obj_eq_of_comp_eq hG P.hy).symm) }
  map {P Q} u :=
    { hbase := u.hbase
      a := F.map u.a
      b := G.map u.b
      ha := by
        have : p𝒳.IsHomLift u.hbase u.a := u.ha
        exact Functor.isHomLift_map_of_comp_eq hF u.hbase u.a
      hb := by
        have : p𝒴.IsHomLift u.hbase u.b := u.hb
        exact Functor.isHomLift_map_of_comp_eq hG u.hbase u.b
      w := by
        have h1 : p𝒮.IsHomLift u.hbase (F.map u.a) := by
          have : p𝒳.IsHomLift u.hbase u.a := u.ha
          exact Functor.isHomLift_map_of_comp_eq hF u.hbase u.a
        have h2 : p𝒮'.IsHomLift u.hbase (G.map u.b) := by
          have : p𝒴.IsHomLift u.hbase u.b := u.hb
          exact Functor.isHomLift_map_of_comp_eq hG u.hbase u.b
        exact prodOver_w_eqToHom (obj_eq_of_comp_eq hF P.hx) (obj_eq_of_comp_eq hG P.hy)
          (obj_eq_of_comp_eq hF Q.hx) (obj_eq_of_comp_eq hG Q.hy) h1 h2 }
  map_id _ := by apply Hom.ext' <;> simp
  map_comp _ _ := by apply Hom.ext' <;> simp

section ProdMapSimp

variable (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮') (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮' = p𝒴)

/-- The base of the image of an object under `prodMap` is the base of the object. -/
@[simp] lemma prodMap_obj_base (P : TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) :
    ((prodMap F G hF hG).obj P).base = P.base := rfl

/-- The first component of the image of an object under `prodMap` is its image under `F`. -/
@[simp] lemma prodMap_obj_x (P : TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) :
    ((prodMap F G hF hG).obj P).x = F.obj P.x := rfl

/-- The second component of the image of an object under `prodMap` is its image under `G`. -/
@[simp] lemma prodMap_obj_y (P : TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) :
    ((prodMap F G hF hG).obj P).y = G.obj P.y := rfl

/-- The first component of the image of a morphism under `prodMap` is its image under `F`. -/
@[simp] lemma prodMap_map_a {P Q : TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴} (u : P ⟶ Q) :
    ((prodMap F G hF hG).map u).a = F.map u.a := rfl

/-- The second component of the image of a morphism under `prodMap` is its image under `G`. -/
@[simp] lemma prodMap_map_b {P Q : TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴} (u : P ⟶ Q) :
    ((prodMap F G hF hG).map u).b = G.map u.b := rfl

end ProdMapSimp

/-- `prodMap F G` followed by the first projection is the first projection followed by `F`. -/
@[simp] lemma prodMap_comp_fst (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮') (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮' = p𝒴) :
    prodMap F G hF hG ⋙ fst p𝒮 p𝒮' (𝟭 𝒞) p𝒮 p𝒮' = fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 ⋙ F := rfl

/-- `prodMap F G` followed by the second projection is the second projection followed by `G`. -/
@[simp] lemma prodMap_comp_snd (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮') (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮' = p𝒴) :
    prodMap F G hF hG ⋙ snd p𝒮 p𝒮' (𝟭 𝒞) p𝒮 p𝒮' = snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 ⋙ G := rfl

/-- `prodMap F G` commutes with the structure functors to `𝒞`. -/
@[simp] lemma prodMap_comp_structureFunctor (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮') (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮' = p𝒴) :
    prodMap F G hF hG ⋙ structureFunctor p𝒮 p𝒮' (𝟭 𝒞) p𝒮 p𝒮' =
      structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 := rfl

/-- The projection of a 2-fibre product over `𝒞` to the product. -/
def toProduct (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤ TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := eqToIso (P.hx.trans P.hy.symm)
      vertical := isHomLift_id_eqToHom P.hx P.hy (P.hx.trans P.hy.symm) }
  map {P Q} u :=
    { hbase := u.hbase
      a := u.a
      b := u.b
      ha := u.ha
      hb := u.hb
      w := prodOver_w_eqToHom P.hx P.hy Q.hx Q.hy u.ha u.hb }
  map_id _ := rfl
  map_comp _ _ := rfl

section ToProductSimp

variable (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-- The base of the image of an object under `toProduct` is the base of the object. -/
@[simp] lemma toProduct_obj_base (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((toProduct p𝒳 p𝒴 p𝒮 F G).obj P).base = P.base := rfl

/-- The first component of the image of an object under `toProduct` is its first component. -/
@[simp] lemma toProduct_obj_x (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((toProduct p𝒳 p𝒴 p𝒮 F G).obj P).x = P.x := rfl

/-- The second component of the image of an object under `toProduct` is its second component. -/
@[simp] lemma toProduct_obj_y (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((toProduct p𝒳 p𝒴 p𝒮 F G).obj P).y = P.y := rfl

/-- The comparison isomorphism of the image of an object under `toProduct` is the canonical
`eqToIso`. -/
@[simp] lemma toProduct_obj_iso (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((toProduct p𝒳 p𝒴 p𝒮 F G).obj P).iso = eqToIso (P.hx.trans P.hy.symm) := rfl

/-- The first component of the image of a morphism under `toProduct` is its first component. -/
@[simp] lemma toProduct_map_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (u : P ⟶ Q) :
    ((toProduct p𝒳 p𝒴 p𝒮 F G).map u).a = u.a := rfl

/-- The second component of the image of a morphism under `toProduct` is its second component. -/
@[simp] lemma toProduct_map_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (u : P ⟶ Q) :
    ((toProduct p𝒳 p𝒴 p𝒮 F G).map u).b = u.b := rfl

end ToProductSimp

/-- `toProduct` followed by the first projection of the product is the first projection. -/
@[simp] lemma toProduct_comp_fst (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    toProduct p𝒳 p𝒴 p𝒮 F G ⋙ fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 = fst p𝒳 p𝒴 p𝒮 F G := rfl

/-- `toProduct` followed by the second projection of the product is the second projection. -/
@[simp] lemma toProduct_comp_snd (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    toProduct p𝒳 p𝒴 p𝒮 F G ⋙ snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 = snd p𝒳 p𝒴 p𝒮 F G := rfl

/-- `toProduct` commutes with the structure functors to `𝒞`. -/
@[simp] lemma toProduct_comp_structureFunctor (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    toProduct p𝒳 p𝒴 p𝒮 F G ⋙ structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 =
      structureFunctor p𝒳 p𝒴 p𝒮 F G := rfl

/-- The 2-cell filling the square comparing a 2-fibre product over `𝒞` with the product. -/
noncomputable def toProductDiagonalIso (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮 = p𝒴) :
    toProduct p𝒳 p𝒴 p𝒮 F G ⋙ prodMap F G hF hG ≅
      (snd p𝒳 p𝒴 p𝒮 F G ⋙ G) ⋙ diagonal (Functor.comp_id p𝒮) :=
  NatIso.ofComponents
    (fun P => isoMkVertical (U := P.base) P.iso (Iso.refl (G.obj P.y)) P.vertical
      (IsHomLift.id (obj_eq_of_comp_eq hG P.hy))
      (show p𝒮.map P.iso.hom ≫ 𝟙 (p𝒮.obj (G.obj P.y)) =
          eqToHom ((obj_eq_of_comp_eq hF P.hx).trans (obj_eq_of_comp_eq hG P.hy).symm) ≫
            p𝒮.map (𝟙 (G.obj P.y)) by
        have hv : p𝒮.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
        rw [IsHomLift.fac' p𝒮 (𝟙 P.base) P.iso.hom]
        simp))
    (fun {P Q} u => Hom.ext' u.w
      (show G.map u.b ≫ 𝟙 (G.obj Q.y) = 𝟙 (G.obj P.y) ≫ G.map u.b by simp))

/-- The first component of `toProductDiagonalIso` at an object is its comparison isomorphism. -/
@[simp] lemma toProductDiagonalIso_hom_app_a (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮 = p𝒴) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((toProductDiagonalIso F G hF hG).hom.app P).a = P.iso.hom := rfl

/-- The second component of `toProductDiagonalIso` at an object is the identity. -/
@[simp] lemma toProductDiagonalIso_hom_app_b (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) (hF : F ⋙ p𝒮 = p𝒳)
    (hG : G ⋙ p𝒮 = p𝒴) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((toProductDiagonalIso F G hF hG).hom.app P).b = 𝟙 (G.obj P.y) := rfl

/-- The inverse of an isomorphism of the 2-fibre product over an identity has `𝒴`-component over
that identity. -/
private lemma isHomLift_inv_b {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (e : P ≅ Q) {U : 𝒞}
    (he : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 U) e.hom) :
    p𝒴.IsHomLift (𝟙 U) e.inv.b :=
  isHomLift_b e.inv (𝟙 U) (IsHomLift.lift_id_inv _ U e)

section Cone

variable {𝒯 : Type uT} [Category.{vT} 𝒯]
  {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮} (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)
  (p𝒯 : 𝒯 ⥤ 𝒞) (A : 𝒯 ⥤ TwoFibreProductOver p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) (Bb : 𝒯 ⥤ 𝒮)
  (t : A ⋙ prodMap F G hF hG ≅ Bb ⋙ diagonal (Functor.comp_id p𝒮))

/-- First leg of the filler of a test cone. -/
def coneFstIso : (A ⋙ fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) ⋙ F ≅ Bb :=
  Functor.isoWhiskerRight t (fst p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮)

/-- Second leg of the filler of a test cone. -/
def coneSndIso : (A ⋙ snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) ⋙ G ≅ Bb :=
  Functor.isoWhiskerRight t (snd p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮)

/-- The component of `coneFstIso` is the first component of the component of `t`. -/
@[simp] lemma coneFstIso_hom_app (w : 𝒯) :
    (coneFstIso hF hG A Bb t).hom.app w = (t.hom.app w).a := rfl

/-- The inverse component of `coneFstIso` is the first component of the inverse of `t`. -/
@[simp] lemma coneFstIso_inv_app (w : 𝒯) :
    (coneFstIso hF hG A Bb t).inv.app w = (t.inv.app w).a := rfl

/-- The component of `coneSndIso` is the second component of the component of `t`. -/
@[simp] lemma coneSndIso_hom_app (w : 𝒯) :
    (coneSndIso hF hG A Bb t).hom.app w = (t.hom.app w).b := rfl

/-- The inverse component of `coneSndIso` is the second component of the inverse of `t`. -/
@[simp] lemma coneSndIso_inv_app (w : 𝒯) :
    (coneSndIso hF hG A Bb t).inv.app w = (t.inv.app w).b := rfl

/-- The comparison isomorphism of the object the mediating 1-morphism assigns. -/
def coneIso :
    (A ⋙ fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) ⋙ F ≅ (A ⋙ snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) ⋙ G :=
  coneFstIso hF hG A Bb t ≪≫ (coneSndIso hF hG A Bb t).symm

/-- The component of `coneIso` at `w` is `(t w).a ≫ (t w)⁻¹.b`. -/
@[simp] lemma coneIso_hom_app (w : 𝒯) :
    (coneIso hF hG A Bb t).hom.app w = (t.hom.app w).a ≫ (t.inv.app w).b := rfl

/-- If every component of `t` lies over an identity, then so does every component of
`coneIso`. -/
lemma coneIso_hom_app_isHomLift
    (ht : ∀ w, (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).IsHomLift (𝟙 (p𝒯.obj w)) (t.hom.app w))
    (w : 𝒯) : p𝒮.IsHomLift (𝟙 (p𝒯.obj w)) ((coneIso hF hG A Bb t).hom.app w) := by
  have h1 : p𝒮.IsHomLift (𝟙 (p𝒯.obj w)) ((t.hom.app w).a) :=
    isHomLift_a (t.hom.app w) (𝟙 (p𝒯.obj w)) (ht w)
  have h2 : p𝒮.IsHomLift (𝟙 (p𝒯.obj w)) ((t.inv.app w).b) := isHomLift_inv_b (t.app w) (ht w)
  exact (inferInstance : p𝒮.IsHomLift (𝟙 (p𝒯.obj w)) ((t.hom.app w).a ≫ (t.inv.app w).b))

variable (hA : A ⋙ structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴 = p𝒯)

include hA in
/-- The first leg of a test cone is a 1-morphism over `𝒞`. -/
lemma coneFst_comp_eq : (A ⋙ fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) ⋙ p𝒳 = p𝒯 := by
  rw [Functor.assoc, fst_comp_eq, hA]

include hA in
/-- The second leg of a test cone is a 1-morphism over `𝒞`. -/
lemma coneSnd_comp_eq : (A ⋙ snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) ⋙ p𝒴 = p𝒯 := by
  rw [Functor.assoc, snd_comp_eq, hA]

/-- The mediating 1-morphism of a test cone over the cospan `(F × G, Δ)`. -/
def coneLift
    (ht : ∀ w, (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).IsHomLift (𝟙 (p𝒯.obj w)) (t.hom.app w)) :
    𝒯 ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
  lift p𝒳 p𝒴 p𝒮 F G p𝒯 (A ⋙ fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴) (A ⋙ snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴)
    (coneFst_comp_eq p𝒯 A hA) (coneSnd_comp_eq p𝒯 A hA) (coneIso hF hG A Bb t)
    (coneIso_hom_app_isHomLift hF hG p𝒯 A Bb t ht)

variable (ht : ∀ w, (structureFunctor p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).IsHomLift (𝟙 (p𝒯.obj w)) (t.hom.app w))

/-- The base of the object `coneLift` assigns to `w` is the image of `w` in `𝒞`. -/
@[simp] lemma coneLift_obj_base (w : 𝒯) :
    ((coneLift hF hG p𝒯 A Bb t hA ht).obj w).base = p𝒯.obj w := rfl

/-- The first component of the object `coneLift` assigns to `w` is that of `A.obj w`. -/
@[simp] lemma coneLift_obj_x (w : 𝒯) :
    ((coneLift hF hG p𝒯 A Bb t hA ht).obj w).x = (A.obj w).x := rfl

/-- The second component of the object `coneLift` assigns to `w` is that of `A.obj w`. -/
@[simp] lemma coneLift_obj_y (w : 𝒯) :
    ((coneLift hF hG p𝒯 A Bb t hA ht).obj w).y = (A.obj w).y := rfl

/-- The comparison isomorphism of the object `coneLift` assigns to `w` is the component of
`coneIso`. -/
@[simp] lemma coneLift_obj_iso (w : 𝒯) :
    ((coneLift hF hG p𝒯 A Bb t hA ht).obj w).iso = (coneIso hF hG A Bb t).app w := rfl

/-- The first component of the image of a morphism under `coneLift` is that of its image
under `A`. -/
@[simp] lemma coneLift_map_a {w w' : 𝒯} (u : w ⟶ w') :
    ((coneLift hF hG p𝒯 A Bb t hA ht).map u).a = (A.map u).a := rfl

/-- The second component of the image of a morphism under `coneLift` is that of its image
under `A`. -/
@[simp] lemma coneLift_map_b {w w' : 𝒯} (u : w ⟶ w') :
    ((coneLift hF hG p𝒯 A Bb t hA ht).map u).b = (A.map u).b := rfl

/-- The mediating 1-morphism `coneLift` is a 1-morphism over `𝒞`. -/
lemma coneLift_comp_structureFunctor :
    coneLift hF hG p𝒯 A Bb t hA ht ⋙ structureFunctor p𝒳 p𝒴 p𝒮 F G = p𝒯 :=
  lift_comp_structureFunctor ..

include hA in
/-- The first component of `A.obj w` lies over the image of `w` in `𝒞`. -/
lemma coneObj_hx (w : 𝒯) : p𝒳.obj ((A.obj w).x) = p𝒯.obj w :=
  (A.obj w).hx.trans (show (A.obj w).base = p𝒯.obj w from Functor.congr_obj hA w)

include hA in
/-- The second component of `A.obj w` lies over the image of `w` in `𝒞`. -/
lemma coneObj_hy (w : 𝒯) : p𝒴.obj ((A.obj w).y) = p𝒯.obj w :=
  (A.obj w).hy.trans (show (A.obj w).base = p𝒯.obj w from Functor.congr_obj hA w)

/-- The comparison 2-isomorphism identifying the first leg of a test cone with the first leg of
the mediating 1-morphism: both components are identities. -/
noncomputable def coneLiftProductIso :
    A ≅ coneLift hF hG p𝒯 A Bb t hA ht ⋙ toProduct p𝒳 p𝒴 p𝒮 F G :=
  NatIso.ofComponents
    (fun w => isoMkVertical (U := p𝒯.obj w) (Iso.refl ((A.obj w).x)) (Iso.refl ((A.obj w).y))
      (IsHomLift.id (coneObj_hx p𝒯 A hA w)) (IsHomLift.id (coneObj_hy p𝒯 A hA w))
      (by simp [prodOver_iso_hom]; rfl))
    (fun {w w'} u => Hom.ext'
      (show (A.map u).a ≫ 𝟙 ((A.obj w').x) = 𝟙 ((A.obj w).x) ≫ (A.map u).a by simp)
      (show (A.map u).b ≫ 𝟙 ((A.obj w').y) = 𝟙 ((A.obj w).y) ≫ (A.map u).b by simp))

/-- The first component of `coneLiftProductIso` is the identity. -/
@[simp] lemma coneLiftProductIso_hom_app_a (w : 𝒯) :
    ((coneLiftProductIso hF hG p𝒯 A Bb t hA ht).hom.app w).a = 𝟙 ((A.obj w).x) := rfl

/-- The second component of `coneLiftProductIso` is the identity. -/
@[simp] lemma coneLiftProductIso_hom_app_b (w : 𝒯) :
    ((coneLiftProductIso hF hG p𝒯 A Bb t hA ht).hom.app w).b = 𝟙 ((A.obj w).y) := rfl

/-- Every component of `coneLiftProductIso` lies over an identity of `𝒞`. -/
lemma coneLiftProductIso_hom_app_isHomLift (w : 𝒯) :
    (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 (p𝒯.obj w))
      ((coneLiftProductIso hF hG p𝒯 A Bb t hA ht).hom.app w) :=
  structureFunctor_isHomLift _ (𝟙 (p𝒯.obj w)) (IsHomLift.id (coneObj_hx p𝒯 A hA w))

/-- The comparison 2-isomorphism identifying the second leg of a test cone with the second leg
of the mediating 1-morphism. -/
def coneLiftBaseIso : Bb ≅ coneLift hF hG p𝒯 A Bb t hA ht ⋙ (snd p𝒳 p𝒴 p𝒮 F G ⋙ G) :=
  (coneSndIso hF hG A Bb t).symm

/-- The component of `coneLiftBaseIso` is the second component of the inverse of `t`. -/
@[simp] lemma coneLiftBaseIso_hom_app (w : 𝒯) :
    (coneLiftBaseIso hF hG p𝒯 A Bb t hA ht).hom.app w = (t.inv.app w).b := rfl

/-- The mediating 1-morphism is a morphism of test cones: the compatibility square of
Stacks 003O for its two comparison 2-isomorphisms. -/
lemma coneCompat (w : 𝒯) :
    t.hom.app w ≫ (diagonal (Functor.comp_id p𝒮)).map
        ((coneLiftBaseIso hF hG p𝒯 A Bb t hA ht).hom.app w) =
      (prodMap F G hF hG).map ((coneLiftProductIso hF hG p𝒯 A Bb t hA ht).hom.app w) ≫
        (toProductDiagonalIso F G hF hG).hom.app ((coneLift hF hG p𝒯 A Bb t hA ht).obj w) := by
  have hbb : (t.hom.app w) ≫ (t.inv.app w) = 𝟙 _ :=
    NatTrans.congr_app t.hom_inv_id w
  have h := congrArg Hom.b hbb
  simp only [comp_b, id_b] at h
  exact Hom.ext'
    (show (t.hom.app w).a ≫ (t.inv.app w).b =
        F.map (𝟙 ((A.obj w).x)) ≫ ((t.hom.app w).a ≫ (t.inv.app w).b) by simp)
    (show (t.hom.app w).b ≫ (t.inv.app w).b =
        G.map (𝟙 ((A.obj w).y)) ≫ 𝟙 (G.obj ((A.obj w).y)) by
      simp only [Functor.map_id, Category.id_comp]
      exact h)

/-- `coneCompat` with the identities that a strict bicategory's unitors and associator leave
behind. -/
lemma coneCompat_id (w : 𝒯) :
    t.hom.app w ≫ (diagonal (Functor.comp_id p𝒮)).map
          ((coneLiftBaseIso hF hG p𝒯 A Bb t hA ht).hom.app w) ≫ 𝟙 _ =
      (prodMap F G hF hG).map ((coneLiftProductIso hF hG p𝒯 A Bb t hA ht).hom.app w) ≫ 𝟙 _ ≫
        (toProductDiagonalIso F G hF hG).hom.app ((coneLift hF hG p𝒯 A Bb t hA ht).obj w) := by
  rw [Category.comp_id, Category.id_comp]
  exact coneCompat hF hG p𝒯 A Bb t hA ht w

/-- Every component of `coneLiftBaseIso` lies over an identity of `𝒞`. -/
lemma coneLiftBaseIso_hom_app_isHomLift (w : 𝒯) :
    p𝒮.IsHomLift (𝟙 (p𝒯.obj w)) ((coneLiftBaseIso hF hG p𝒯 A Bb t hA ht).hom.app w) :=
  isHomLift_inv_b (t.app w) (ht w)

section Unique

variable (γ : 𝒯 ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
  (iFst : A ≅ γ ⋙ toProduct p𝒳 p𝒴 p𝒮 F G)
  (hiFst : ∀ w, (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 (p𝒯.obj w)) (iFst.hom.app w))
  (iSnd : Bb ≅ γ ⋙ (snd p𝒳 p𝒴 p𝒮 F G ⋙ G))
  (hc : ∀ w, t.hom.app w ≫ (diagonal (Functor.comp_id p𝒮)).map (iSnd.hom.app w) ≫ 𝟙 _ =
    (prodMap F G hF hG).map (iFst.hom.app w) ≫ 𝟙 _ ≫
      (toProductDiagonalIso F G hF hG).hom.app (γ.obj w))

/-- Uniqueness of the mediating 1-morphism: any factorisation of a test cone through the
2-fibre product is 2-isomorphic over `𝒞` to `coneLift`. -/
noncomputable def coneLiftIso : γ ≅ coneLift hF hG p𝒯 A Bb t hA ht := by
  have hc' : ∀ w, t.hom.app w ≫ (diagonal (Functor.comp_id p𝒮)).map (iSnd.hom.app w) =
      (prodMap F G hF hG).map (iFst.hom.app w) ≫
        (toProductDiagonalIso F G hF hG).hom.app (γ.obj w) := by
    intro w
    have h := hc w
    rwa [Category.comp_id, Category.id_comp] at h
  have hinv : ∀ w, (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 (p𝒯.obj w))
      (iFst.app w).inv := by
    intro w
    have : (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 (p𝒯.obj w)) (iFst.app w).hom :=
      hiFst w
    exact IsHomLift.lift_id_inv _ (p𝒯.obj w) (iFst.app w)
  refine liftIso γ (Functor.isoWhiskerRight iFst.symm (fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴))
    (Functor.isoWhiskerRight iFst.symm (snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴))
    (fun w => isHomLift_a (iFst.inv.app w) (𝟙 (p𝒯.obj w)) (hinv w))
    (fun w => isHomLift_b (iFst.inv.app w) (𝟙 (p𝒯.obj w)) (hinv w)) ?_
    (coneFst_comp_eq p𝒯 A hA) (coneSnd_comp_eq p𝒯 A hA)
    (coneIso_hom_app_isHomLift hF hG p𝒯 A Bb t ht)
  ext w
  have hca := congrArg Hom.a (hc' w)
  have hcb := congrArg Hom.b (hc' w)
  simp only [comp_a, comp_b, diagonal_map_a, diagonal_map_b, prodMap_map_a, prodMap_map_b,
    toProductDiagonalIso_hom_app_a, toProductDiagonalIso_hom_app_b] at hca hcb
  have hca' : (t.hom.app w).a ≫ (iSnd.app w).hom =
      (F.mapIso ((fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).mapIso (iFst.app w))).hom ≫ (γ.obj w).iso.hom := hca
  have hcb' : ((snd p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).mapIso (t.app w)).hom ≫ (iSnd.app w).hom =
      (G.mapIso ((snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).mapIso (iFst.app w))).hom :=
    hcb.trans (Category.comp_id _)
  exact iso_cancel_aux (F.mapIso ((fst p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).mapIso (iFst.app w)))
    (G.mapIso ((snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).mapIso (iFst.app w)))
    ((snd p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).mapIso (t.app w)) (iSnd.app w) ((t.hom.app w).a)
    ((γ.obj w).iso.hom) hca' hcb'

/-- The first component of `coneLiftIso` is the first component of the inverse of `iFst`. -/
@[simp] lemma coneLiftIso_hom_app_a (w : 𝒯) :
    ((coneLiftIso hF hG p𝒯 A Bb t hA ht γ iFst hiFst iSnd hc).hom.app w).a =
      (iFst.inv.app w).a := rfl

/-- The second component of `coneLiftIso` is the second component of the inverse of `iFst`. -/
@[simp] lemma coneLiftIso_hom_app_b (w : 𝒯) :
    ((coneLiftIso hF hG p𝒯 A Bb t hA ht γ iFst hiFst iSnd hc).hom.app w).b =
      (iFst.inv.app w).b := rfl

/-- Every component of `coneLiftIso` lies over an identity of `𝒞`. -/
lemma coneLiftIso_hom_app_isHomLift (w : 𝒯) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 (p𝒯.obj w))
      ((coneLiftIso hF hG p𝒯 A Bb t hA ht γ iFst hiFst iSnd hc).hom.app w) := by
  have hhom : (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 (p𝒯.obj w))
      (iFst.app w).hom := hiFst w
  have hinv : (structureFunctor p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).IsHomLift (𝟙 (p𝒯.obj w))
      (iFst.app w).inv := IsHomLift.lift_id_inv _ (p𝒯.obj w) (iFst.app w)
  exact structureFunctor_isHomLift _ (𝟙 (p𝒯.obj w))
    (isHomLift_a (iFst.inv.app w) (𝟙 (p𝒯.obj w)) hinv)

/-- The first compatibility making `coneLiftIso` an equivalence of cone morphisms. -/
lemma coneRelFst (w : 𝒯) :
    iFst.hom.app w ≫ (toProduct p𝒳 p𝒴 p𝒮 F G).map
        ((coneLiftIso hF hG p𝒯 A Bb t hA ht γ iFst hiFst iSnd hc).hom.app w) =
      (coneLiftProductIso hF hG p𝒯 A Bb t hA ht).hom.app w := by
  have h : iFst.hom.app w ≫ iFst.inv.app w = 𝟙 (A.obj w) :=
    NatTrans.congr_app iFst.hom_inv_id w
  have ha := congrArg Hom.a h
  have hb := congrArg Hom.b h
  simp only [comp_a, comp_b, id_a, id_b] at ha hb
  exact Hom.ext' ha hb

/-- The second compatibility making `coneLiftIso` an equivalence of cone morphisms. -/
lemma coneRelSnd (w : 𝒯) :
    iSnd.hom.app w ≫ G.map
        ((coneLiftIso hF hG p𝒯 A Bb t hA ht γ iFst hiFst iSnd hc).hom.app w).b =
      (coneLiftBaseIso hF hG p𝒯 A Bb t hA ht).hom.app w := by
  have hc' : ∀ w, t.hom.app w ≫ (diagonal (Functor.comp_id p𝒮)).map (iSnd.hom.app w) =
      (prodMap F G hF hG).map (iFst.hom.app w) ≫
        (toProductDiagonalIso F G hF hG).hom.app (γ.obj w) := by
    intro w
    have h := hc w
    rwa [Category.comp_id, Category.id_comp] at h
  have hcb := congrArg Hom.b (hc' w)
  simp only [comp_b, diagonal_map_b, prodMap_map_b, toProductDiagonalIso_hom_app_b] at hcb
  have hcb' : ((snd p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).mapIso (t.app w)).hom ≫ (iSnd.app w).hom =
      (G.mapIso ((snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).mapIso (iFst.app w))).hom :=
    hcb.trans (Category.comp_id _)
  exact iso_cancel_inv (G.mapIso ((snd p𝒳 p𝒴 (𝟭 𝒞) p𝒳 p𝒴).mapIso (iFst.app w)))
    ((snd p𝒮 p𝒮 (𝟭 𝒞) p𝒮 p𝒮).mapIso (t.app w)) (iSnd.app w) hcb'

end Unique

end Cone

end CategoryTheory.TwoFibreProductOver

end
