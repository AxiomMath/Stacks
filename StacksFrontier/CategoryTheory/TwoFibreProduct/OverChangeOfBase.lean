module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Enlarging the base of a 2-fibre product over a site

Let `𝒳`, `𝒴`, `𝒵`, `𝒯` be categories over a base category `𝒞` and let `F : 𝒳 ⥤ 𝒵`, `G : 𝒴 ⥤ 𝒵`
and `H : 𝒵 ⥤ 𝒯` be functors over `𝒞`. Composing with `H` turns the cospan `(F, G)` into the
cospan `(F ⋙ H, G ⋙ H)`. The comparison functor

```text
  i = CategoryTheory.TwoFibreProductOver.mapBase : 𝒳 ×_𝒵 𝒴 ⥤ 𝒳 ×_𝒯 𝒴
```

between the two 2-fibre products over `𝒞` is already available; this file identifies it as a base
change of the relative diagonal `Δ_H : 𝒵 ⥤ 𝒵 ×_𝒯 𝒵`, which is the categorical content of the
first part of Stacks 050H.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.mapCospan`: the functor `𝒳 ×_𝒯 𝒴 ⥤ 𝒵 ×_𝒯 𝒵` applying `F`
  to the first factor and `G` to the second.
* `CategoryTheory.TwoFibreProductOver.changeOfBaseLift`: the mediating 1-morphism of a test cone
  over the cospan `(mapCospan, Δ_H)`, and `changeOfBaseLiftCospanIso`,
  `changeOfBaseLiftBaseIso` its two comparison 2-isomorphisms.

## Main results

* `CategoryTheory.TwoFibreProductOver.diagonalObjIsoMapCospan`: an object of `𝒳 ×_𝒵 𝒴` is carried
  by `i` followed by `CategoryTheory.TwoFibreProductOver.mapCospan` to an object in the image of
  the diagonal `Δ_H`, canonically.
* `CategoryTheory.TwoFibreProductOver.fstCompFCompDiagonalIso`: those identifications assemble
  into a natural isomorphism `fst ⋙ F ⋙ Δ_H ≅ i ⋙ mapCospan`, i.e. into the 2-commutative square

  ```text
    𝒳 ×_𝒵 𝒴  --- i --->  𝒳 ×_𝒯 𝒴
       |                    |
    fst ≫ F           mapCospan
       v                    v
       𝒵     --- Δ_H --->  𝒵 ×_𝒯 𝒵
  ```
* `CategoryTheory.TwoFibreProductOver.changeOfBaseCompat_id`: the mediating 1-morphism is a
  morphism of test cones, i.e. the square of Stacks 003O for its two comparison 2-isomorphisms
  commutes.
* `CategoryTheory.TwoFibreProductOver.changeOfBaseLiftIso`,
  `CategoryTheory.TwoFibreProductOver.changeOfBaseRelFst` and
  `CategoryTheory.TwoFibreProductOver.changeOfBaseRelSnd`: the mediating 1-morphism is the only
  one, up to a 2-isomorphism over `𝒞` compatible with both comparison 2-cells. So the square is
  2-cartesian, which is the categorical content of Stacks 050H.

## Implementation notes

`CategoryTheory.TwoFibreProductOver.mapCospan` needs `F` and `G` to be functors over `𝒞`, since
it moves the two factors between the three categories, whereas
`CategoryTheory.TwoFibreProductOver.mapBase` needs only that `H` is one: the comparison
isomorphism of the image is `H` applied to the given one, and verticality transports by
`CategoryTheory.Functor.isHomLift_map_of_comp_eq`.

As in `StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal`, the data of a test cone and
of a factorisation are spelled out componentwise rather than as 2-cells of a bicategory, so that a
consumer working in a sub-2-category — the categories fibred in groupoids of Stacks 02XS — can
feed in its own square after unfolding only the underlying natural isomorphism. The projection
identities `mapCospan_comp_fst`, `mapCospan_comp_snd`, `mapBase_comp_snd`, `diagonal_comp_fst` and
`diagonal_comp_snd` recorded here are all `rfl`, and they are what lets a test cone over
`(mapCospan, Δ_H)` be turned into one over `(F, G)` by whiskering with no comparison to carry.

The object-level identification is built from
`CategoryTheory.TwoFibreProductOver.homDiagonal`, which produces the comparison morphism out of
the diagonal determined by a morphism with the right image under `H`; here that morphism is the
comparison isomorphism of the object of `𝒳 ×_𝒵 𝒴`, so the result is invertible. Its inverse is
written out rather than taken as `CategoryTheory.asIso` of it, so that both components are
literally `𝟙` and the comparison isomorphism of the object; this keeps the naturality square and
the verticality check free of `inv`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒵 : Type u₄} [Category.{v₄} 𝒵]
  {𝒯 : Type u₅} [Category.{v₅} 𝒯]
variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (p𝒯 : 𝒯 ⥤ 𝒞)
  (F : 𝒳 ⥤ 𝒵) (G : 𝒴 ⥤ 𝒵) (H : 𝒵 ⥤ 𝒯)

/-- **The functor `𝒳 ×_𝒯 𝒴 ⥤ 𝒵 ×_𝒯 𝒵`** applying `F` to the first factor and `G` to the second.
Both are functors over `𝒞`, so the images still lie over the base object, and the comparison
isomorphism is unchanged. -/
def mapCospan (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) ⥤ TwoFibreProductOver p𝒵 p𝒵 p𝒯 H H where
  obj P :=
    { base := P.base
      x := F.obj P.x
      y := G.obj P.y
      hx := (Functor.congr_obj hF P.x).trans P.hx
      hy := (Functor.congr_obj hG P.y).trans P.hy
      iso := P.iso
      vertical := P.vertical }
  map φ := by
    letI : p𝒳.IsHomLift φ.hbase φ.a := φ.ha
    letI : p𝒴.IsHomLift φ.hbase φ.b := φ.hb
    exact
      { hbase := φ.hbase
        a := F.map φ.a
        b := G.map φ.b
        ha := Functor.isHomLift_map_of_comp_eq hF φ.hbase φ.a
        hb := Functor.isHomLift_map_of_comp_eq hG φ.hbase φ.b
        w := by simpa only [Functor.comp_map] using φ.w }
  map_id _ := by apply Hom.ext' <;> simp
  map_comp _ _ := by apply Hom.ext' <;> simp

/-- **The square commutes at an object.** For an object `P = (U, x, y, φ)` of `𝒳 ×_𝒵 𝒴`, the
object `Δ_H (F x)` of `𝒵 ×_𝒯 𝒵` is canonically isomorphic to the image of `P` under
`mapBase` followed by `mapCospan`, namely `(U, F x, G y, H φ)`. The isomorphism is the identity
on the first factor and `φ` on the second. -/
noncomputable def diagonalObjIsoMapCospan (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴)
    (hH : H ⋙ p𝒯 = p𝒵) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    (diagonal hH).obj (F.obj P.x) ≅
      (mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).obj
        ((mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH).obj P) := by
  set Q := (mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).obj
    ((mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH).obj P)
  let φ := homDiagonal hH Q P.iso.hom rfl
  haveI : IsIso φ.hbase := by
    change IsIso (eqToHom Q.hx)
    infer_instance
  haveI : IsIso φ.a := by
    change IsIso (𝟙 _)
    infer_instance
  haveI : IsIso φ.b := by
    change IsIso P.iso.hom
    infer_instance
  letI := isIso_of_components φ
  let e := asIso φ
  have ha : e.inv.a = 𝟙 _ := by
    have he := congrArg Hom.a e.hom_inv_id
    change 𝟙 _ ≫ e.inv.a = 𝟙 _ at he
    exact (Category.id_comp _).symm.trans he
  have hb : e.inv.b = P.iso.inv := by
    have he := congrArg Hom.b e.hom_inv_id
    change P.iso.hom ≫ e.inv.b = 𝟙 _ at he
    exact (cancel_epi P.iso.hom).mp (he.trans P.iso.hom_inv_id.symm)
  exact
    { hom := φ
      inv :=
        { hbase := e.inv.hbase
          a := 𝟙 _
          b := P.iso.inv
          ha := by rw [← ha]; exact e.inv.ha
          hb := by rw [← hb]; exact e.inv.hb
          w := by rw [← ha, ← hb]; exact e.inv.w }
      hom_inv_id := Hom.ext' (Category.id_comp _) P.iso.hom_inv_id
      inv_hom_id := Hom.ext' (Category.id_comp _) P.iso.inv_hom_id }

/-- **The comparison functor is a base change of the relative diagonal of `H`.** The square

```text
  𝒳 ×_𝒵 𝒴  --- mapBase --->  𝒳 ×_𝒯 𝒴
     |                           |
  fst ≫ F                   mapCospan
     v                           v
     𝒵     ---  Δ_H  --->     𝒵 ×_𝒯 𝒵
```

commutes up to the natural isomorphism assembled from
`CategoryTheory.TwoFibreProductOver.diagonalObjIsoMapCospan`. -/
noncomputable def fstCompFCompDiagonalIso (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴)
    (hH : H ⋙ p𝒯 = p𝒵) :
    fst p𝒳 p𝒴 p𝒵 F G ⋙ F ⋙ diagonal hH ≅
      mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH ⋙ mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG := by
  refine NatIso.ofComponents (diagonalObjIsoMapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH) ?_
  intro P P' φ
  apply Hom.ext'
  · change F.map φ.a ≫ 𝟙 _ = 𝟙 _ ≫ F.map φ.a
    simp
  · change F.map φ.a ≫ P'.iso.hom = P.iso.hom ≫ G.map φ.b
    exact φ.w

/-! ### The projection identities the square is read through

The three functors entering the square commute with the projections of the two 2-fibre products
over `𝒯` on the nose; these identities are what lets a test cone over the cospan
`(mapCospan, Δ_H)` be turned into a test cone over the cospan `(F, G)` by whiskering, with no
comparison isomorphism to carry. -/

/-- `mapBase` followed by the second projection of `𝒳 ×_𝒯 𝒴` is the second projection of
`𝒳 ×_𝒵 𝒴`. -/
@[simp] lemma mapBase_comp_snd (hH : H ⋙ p𝒯 = p𝒵) :
    mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH ⋙ snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) =
      snd p𝒳 p𝒴 p𝒵 F G :=
  rfl

/-- `mapCospan` followed by the first projection of `𝒵 ×_𝒯 𝒵` is the first projection of
`𝒳 ×_𝒯 𝒴` followed by `F`. -/
@[simp] lemma mapCospan_comp_fst (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴) :
    mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG ⋙ fst p𝒵 p𝒵 p𝒯 H H =
      fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) ⋙ F :=
  rfl

/-- `mapCospan` followed by the second projection of `𝒵 ×_𝒯 𝒵` is the second projection of
`𝒳 ×_𝒯 𝒴` followed by `G`. -/
@[simp] lemma mapCospan_comp_snd (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴) :
    mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG ⋙ snd p𝒵 p𝒵 p𝒯 H H =
      snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) ⋙ G :=
  rfl

/-- `mapCospan` is a functor over `𝒞`: it commutes with the structure functors of `𝒳 ×_𝒯 𝒴`
and `𝒵 ×_𝒯 𝒵`. -/
@[simp] lemma mapCospan_comp_structureFunctor (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴) :
    mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG ⋙ structureFunctor p𝒵 p𝒵 p𝒯 H H =
      structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) :=
  rfl

/-- The first component of the image of a morphism `φ` under `mapCospan` is `F.map φ.a`. -/
@[simp] lemma mapCospan_map_a (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴)
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)} (φ : P ⟶ Q) :
    ((mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).map φ).a = F.map φ.a :=
  rfl

/-- The second component of the image of a morphism `φ` under `mapCospan` is `G.map φ.b`. -/
@[simp] lemma mapCospan_map_b (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴)
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)} (φ : P ⟶ Q) :
    ((mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).map φ).b = G.map φ.b :=
  rfl

/-- The comparison isomorphism of the image of `P` under `mapBase` is `H` applied to the
comparison isomorphism of `P`. -/
@[simp] lemma mapBase_obj_iso (hH : H ⋙ p𝒯 = p𝒵) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    ((mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH).obj P).iso = H.mapIso P.iso :=
  rfl

/-- The diagonal `Δ_H` followed by the first projection of `𝒵 ×_𝒯 𝒵` is the identity. -/
@[simp] lemma diagonal_comp_fst (hH : H ⋙ p𝒯 = p𝒵) :
    diagonal hH ⋙ fst p𝒵 p𝒵 p𝒯 H H = 𝟭 𝒵 :=
  rfl

/-- The diagonal `Δ_H` followed by the second projection of `𝒵 ×_𝒯 𝒵` is the identity. -/
@[simp] lemma diagonal_comp_snd (hH : H ⋙ p𝒯 = p𝒵) :
    diagonal hH ⋙ snd p𝒵 p𝒵 p𝒯 H H = 𝟭 𝒵 :=
  rfl

/-! ### The universal property of the square

The square of `CategoryTheory.TwoFibreProductOver.fstCompFCompDiagonalIso` is 2-cartesian: a test
cone over the cospan `(mapCospan, Δ_H)` factors through `𝒳 ×_𝒵 𝒴`, uniquely up to a unique
2-isomorphism over `𝒞`. As in `StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal`, the
data of the test cone and of the factorisation are spelled out componentwise rather than as
2-cells of a bicategory, so that a consumer working in a sub-2-category — such as the categories
fibred in groupoids of Stacks 02XS — can feed in its own square after unfolding only the
underlying natural isomorphism. -/

/-- An elementary cancellation: from `ψ ≫ s = e₁` one gets `s ≫ e₁⁻¹ = ψ⁻¹`. -/
lemma iso_cancel_leg {D : Type u₆} [Category.{v₆} D] {A₁ A₂ C : D} (e₁ : A₁ ≅ A₂) (s : C ≅ A₂)
    (ψ : A₁ ≅ C) (hca : ψ.hom ≫ s.hom = e₁.hom) : s.hom ≫ e₁.inv = ψ.inv := by
  rwa [Iso.comp_inv_eq, Iso.eq_inv_comp]

/-- An elementary cancellation: from `ψ ≫ s = e₁` and `τ ≫ s = e₂ ≫ gIso⁻¹` one gets
`e₁⁻¹ ≫ ψ ≫ τ⁻¹ = gIso ≫ e₂⁻¹`. This is the computation that identifies the comparison
isomorphism of a factorisation with the one the mediating 1-morphism carries. -/
lemma iso_cancel_fst_leg {D : Type u₆} [Category.{v₆} D] {A₁ A₂ B₁ B₂ C : D} (e₁ : A₁ ≅ A₂)
    (e₂ : B₁ ≅ B₂) (τ : B₁ ≅ C) (s : C ≅ A₂) (gIso : A₂ ≅ B₂) (ψ : A₁ ⟶ C)
    (hca : ψ ≫ s.hom = e₁.hom) (hcb : τ.hom ≫ s.hom = e₂.hom ≫ gIso.inv) :
    e₁.inv ≫ ψ ≫ τ.inv = gIso.hom ≫ e₂.inv := by
  have h1 : e₁.inv ≫ ψ = s.inv := by
    rw [Iso.inv_comp_eq, ← hca, Category.assoc, s.hom_inv_id, Category.comp_id]
  have key : τ.hom ≫ s.hom ≫ gIso.hom ≫ e₂.inv = 𝟙 B₁ := by
    rw [← Category.assoc, hcb]
    simp
  have h2 : s.hom ≫ gIso.hom ≫ e₂.inv = τ.inv := by
    simpa only [Iso.inv_hom_id_assoc, Category.comp_id] using congrArg (τ.inv ≫ ·) key
  rw [← Category.assoc, h1, ← h2, Iso.inv_hom_id_assoc]

-- The square's two legs are built from `fst`, `snd` and `structureFunctor` of three different
-- 2-fibre products, and the comparison isomorphism of an object of one of them is defeq to that
-- of its image in another only after `mapCospan`, `mapBase` and `diagonal` are unfolded. See
-- `StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal`, which needs the same.
attribute [local implicit_reducible] fst snd structureFunctor diagonal mapCospan mapBase lift

/-- The comparison square of a morphism of a 2-fibre product whose two components are
identities: it reduces to the equality of the two comparison isomorphisms. Stated for variable
functors, which is what lets the two `Functor.map_id`s be used — at the composite functors
`F ⋙ H` and `G ⋙ H` that the 2-fibre product over `𝒯` is taken along, they are not available to
`simp`. -/
lemma map_refl_comp_eq_comp_map_refl {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]
    {𝒮 : Type*} [Category 𝒮] (F' : 𝒜 ⥤ 𝒮) (G' : ℬ ⥤ 𝒮) {a : 𝒜} {b : ℬ}
    {q p : F'.obj a ⟶ G'.obj b} (h : q = p) :
    F'.map (Iso.refl a).hom ≫ q = p ≫ G'.map (Iso.refl b).hom := by
  simp [h]

/-- The components of the inverse of a natural isomorphism into a 2-fibre product are vertical
as soon as those of the isomorphism are. -/
private lemma isHomLift_inv_app_of_hom {W : Type u₆} [Category.{v₆} W]
    {pW : W ⥤ 𝒞} {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {F' : 𝒳 ⥤ 𝒯} {G' : 𝒴 ⥤ 𝒯}
    {A B : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒯 F' G'} (e : A ≅ B)
    (he : ∀ w, (structureFunctor p𝒳 p𝒴 p𝒯 F' G').IsHomLift (𝟙 (pW.obj w)) (e.hom.app w))
    (w : W) : (structureFunctor p𝒳 p𝒴 p𝒯 F' G').IsHomLift (𝟙 (pW.obj w)) (e.inv.app w) := by
  have : (structureFunctor p𝒳 p𝒴 p𝒯 F' G').IsHomLift (𝟙 (pW.obj w)) (e.app w).hom := he w
  exact IsHomLift.lift_id_inv _ (pW.obj w) (e.app w)

section Cone

variable {p𝒳 p𝒴 p𝒵 p𝒯 F G H}
variable {hF : F ⋙ p𝒵 = p𝒳} {hG : G ⋙ p𝒵 = p𝒴} {hH : H ⋙ p𝒯 = p𝒵}
  {W : Type u₆} [Category.{v₆} W] {pW : W ⥤ 𝒞}
  (A : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) (Z : W ⥤ 𝒵)
  (τ : A ⋙ mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG ≅ Z ⋙ diagonal hH)

/-- The first leg of the filler of a test cone: the `𝒵`-valued comparison obtained by projecting
the filler of the cone to the first factor of `𝒵 ×_𝒯 𝒵`. -/
def changeOfBaseFstIso : (A ⋙ fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) ⋙ F ≅ Z :=
  Functor.isoWhiskerRight τ (fst p𝒵 p𝒵 p𝒯 H H)

/-- The second leg of the filler of a test cone, obtained by projecting to the second factor. -/
def changeOfBaseSndIso : (A ⋙ snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) ⋙ G ≅ Z :=
  Functor.isoWhiskerRight τ (snd p𝒵 p𝒵 p𝒯 H H)

/-- The component of `changeOfBaseFstIso` at `w` is the first component of `τ.hom.app w`. -/
@[simp] lemma changeOfBaseFstIso_hom_app (w : W) :
    (changeOfBaseFstIso A Z τ).hom.app w = (τ.hom.app w).a := rfl

/-- The inverse of `changeOfBaseFstIso` at `w` is the first component of `τ.inv.app w`. -/
@[simp] lemma changeOfBaseFstIso_inv_app (w : W) :
    (changeOfBaseFstIso A Z τ).inv.app w = (τ.inv.app w).a := rfl

/-- The component of `changeOfBaseSndIso` at `w` is the second component of `τ.hom.app w`. -/
@[simp] lemma changeOfBaseSndIso_hom_app (w : W) :
    (changeOfBaseSndIso A Z τ).hom.app w = (τ.hom.app w).b := rfl

/-- The inverse of `changeOfBaseSndIso` at `w` is the second component of `τ.inv.app w`. -/
@[simp] lemma changeOfBaseSndIso_inv_app (w : W) :
    (changeOfBaseSndIso A Z τ).inv.app w = (τ.inv.app w).b := rfl

/-- The comparison isomorphism of the object that the mediating 1-morphism assigns: the two legs
of the filler of the test cone, composed. -/
def changeOfBaseIso :
    (A ⋙ fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) ⋙ F ≅
      (A ⋙ snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) ⋙ G :=
  changeOfBaseFstIso A Z τ ≪≫ (changeOfBaseSndIso A Z τ).symm

/-- The component of `changeOfBaseIso` at `w` is `(τ.hom.app w).a ≫ (τ.inv.app w).b`. -/
@[simp] lemma changeOfBaseIso_hom_app (w : W) :
    (changeOfBaseIso A Z τ).hom.app w = (τ.hom.app w).a ≫ (τ.inv.app w).b := rfl

/-- The inverse of `changeOfBaseIso` at `w` is `(τ.hom.app w).b ≫ (τ.inv.app w).a`. -/
@[simp] lemma changeOfBaseIso_inv_app (w : W) :
    (changeOfBaseIso A Z τ).inv.app w = (τ.hom.app w).b ≫ (τ.inv.app w).a := rfl

variable (hτ : ∀ w, (structureFunctor p𝒵 p𝒵 p𝒯 H H).IsHomLift (𝟙 (pW.obj w)) (τ.hom.app w))

include hτ in
/-- If the components of `τ` are vertical, then so are those of `changeOfBaseIso`: each lies over
the identity of `pW w`. -/
lemma changeOfBaseIso_hom_app_isHomLift (w : W) :
    p𝒵.IsHomLift (𝟙 (pW.obj w)) ((changeOfBaseIso A Z τ).hom.app w) := by
  have h1 : p𝒵.IsHomLift (𝟙 (pW.obj w)) ((τ.hom.app w).a) :=
    isHomLift_a (τ.hom.app w) (𝟙 (pW.obj w)) (hτ w)
  have h2 : p𝒵.IsHomLift (𝟙 (pW.obj w)) ((τ.inv.app w).b) :=
    isHomLift_b (τ.inv.app w) (𝟙 (pW.obj w)) (isHomLift_inv_app_of_hom τ hτ w)
  exact IsHomLift.comp_of_lift_id p𝒵 (pW.obj w) ((τ.hom.app w).a) ((τ.inv.app w).b)

variable (hA : A ⋙ structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) = pW)

include hA in
/-- If `A` is a functor over `𝒞`, then so is `A` followed by the first projection. -/
lemma changeOfBaseFst_comp_eq : (A ⋙ fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) ⋙ p𝒳 = pW := by
  rw [Functor.assoc, fst_comp_eq, hA]

include hA in
/-- If `A` is a functor over `𝒞`, then so is `A` followed by the second projection. -/
lemma changeOfBaseSnd_comp_eq : (A ⋙ snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) ⋙ p𝒴 = pW := by
  rw [Functor.assoc, snd_comp_eq, hA]

include hA in
/-- If `A` is a functor over `𝒞`, the first factor of `A w` lies over `pW w`. -/
lemma changeOfBaseObj_hx (w : W) : p𝒳.obj ((A.obj w).x) = pW.obj w :=
  (A.obj w).hx.trans (show (A.obj w).base = pW.obj w from Functor.congr_obj hA w)

include hA in
/-- If `A` is a functor over `𝒞`, the second factor of `A w` lies over `pW w`. -/
lemma changeOfBaseObj_hy (w : W) : p𝒴.obj ((A.obj w).y) = pW.obj w :=
  (A.obj w).hy.trans (show (A.obj w).base = pW.obj w from Functor.congr_obj hA w)

/-- **The mediating 1-morphism of a test cone over the cospan `(mapCospan, Δ_H)`.** It sends `w`
to the quadruple `(pW w, (A w).x, (A w).y, φ)` with `φ` the composite of the two legs of the
filler of the cone. -/
def changeOfBaseLift : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G :=
  lift p𝒳 p𝒴 p𝒵 F G pW (A ⋙ fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H))
    (A ⋙ snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) (changeOfBaseFst_comp_eq A hA)
    (changeOfBaseSnd_comp_eq A hA) (changeOfBaseIso A Z τ)
    (changeOfBaseIso_hom_app_isHomLift A Z τ hτ)

/-- The first factor of `changeOfBaseLift` at `w` is the first factor of `A w`. -/
@[simp] lemma changeOfBaseLift_obj_x (w : W) :
    ((changeOfBaseLift A Z τ hτ hA).obj w).x = (A.obj w).x := rfl

/-- The second factor of `changeOfBaseLift` at `w` is the second factor of `A w`. -/
@[simp] lemma changeOfBaseLift_obj_y (w : W) :
    ((changeOfBaseLift A Z τ hτ hA).obj w).y = (A.obj w).y := rfl

/-- The comparison isomorphism of `changeOfBaseLift` at `w` is the component of
`changeOfBaseIso` at `w`. -/
@[simp] lemma changeOfBaseLift_obj_iso (w : W) :
    ((changeOfBaseLift A Z τ hτ hA).obj w).iso = (changeOfBaseIso A Z τ).app w := rfl

/-- The first component of `changeOfBaseLift` on a morphism `u` is that of `A.map u`. -/
@[simp] lemma changeOfBaseLift_map_a {w w' : W} (u : w ⟶ w') :
    ((changeOfBaseLift A Z τ hτ hA).map u).a = (A.map u).a := rfl

/-- The second component of `changeOfBaseLift` on a morphism `u` is that of `A.map u`. -/
@[simp] lemma changeOfBaseLift_map_b {w w' : W} (u : w ⟶ w') :
    ((changeOfBaseLift A Z τ hτ hA).map u).b = (A.map u).b := rfl

/-- `changeOfBaseLift` is a functor over `𝒞`. -/
lemma changeOfBaseLift_comp_structureFunctor :
    changeOfBaseLift A Z τ hτ hA ⋙ structureFunctor p𝒳 p𝒴 p𝒵 F G = pW :=
  lift_comp_structureFunctor ..

/-- **The first comparison 2-isomorphism of the factorisation**: the test cone's 1-morphism to
`𝒳 ×_𝒯 𝒴` is the mediating 1-morphism followed by
`CategoryTheory.TwoFibreProductOver.mapBase`. Both components are identities; the content is that
`H` applied to the composite of the two legs of the filler recovers the comparison isomorphism of
the test object, which is the comparison square of the filler. -/
noncomputable def changeOfBaseLiftCospanIso :
    A ≅ changeOfBaseLift A Z τ hτ hA ⋙ mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH :=
  NatIso.ofComponents
    (fun w => isoMkVertical (U := pW.obj w) (Iso.refl ((A.obj w).x)) (Iso.refl ((A.obj w).y))
      (IsHomLift.id (changeOfBaseObj_hx A hA w)) (IsHomLift.id (changeOfBaseObj_hy A hA w))
      (by
        have hbb : (τ.hom.app w) ≫ (τ.inv.app w) = 𝟙 _ := NatTrans.congr_app τ.hom_inv_id w
        have hb := congrArg Hom.b hbb
        simp only [comp_b, id_b] at hb
        have hsq := (Category.comp_id (H.map ((τ.hom.app w).a))).symm.trans (τ.hom.app w).w
        have key : H.map ((τ.hom.app w).a ≫ (τ.inv.app w).b) = (A.obj w).iso.hom := by
          rw [H.map_comp, hsq, Category.assoc, ← H.map_comp, hb, Functor.map_id,
            Category.comp_id]
          exact rfl
        exact map_refl_comp_eq_comp_map_refl (F ⋙ H) (G ⋙ H) key))
    (fun {w w'} u => Hom.ext'
      (show (A.map u).a ≫ 𝟙 ((A.obj w').x) = 𝟙 ((A.obj w).x) ≫ (A.map u).a by simp)
      (show (A.map u).b ≫ 𝟙 ((A.obj w').y) = 𝟙 ((A.obj w).y) ≫ (A.map u).b by simp))

/-- The first component of `changeOfBaseLiftCospanIso` at `w` is the identity. -/
@[simp] lemma changeOfBaseLiftCospanIso_hom_app_a (w : W) :
    ((changeOfBaseLiftCospanIso A Z τ hτ hA).hom.app w).a = 𝟙 ((A.obj w).x) := rfl

/-- The second component of `changeOfBaseLiftCospanIso` at `w` is the identity. -/
@[simp] lemma changeOfBaseLiftCospanIso_hom_app_b (w : W) :
    ((changeOfBaseLiftCospanIso A Z τ hτ hA).hom.app w).b = 𝟙 ((A.obj w).y) := rfl

include hA in
/-- The components of `changeOfBaseLiftCospanIso` are vertical: each lies over the identity of
`pW w`. -/
lemma changeOfBaseLiftCospanIso_hom_app_isHomLift (w : W) :
    (structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).IsHomLift (𝟙 (pW.obj w))
      ((changeOfBaseLiftCospanIso A Z τ hτ hA).hom.app w) :=
  structureFunctor_isHomLift _ (𝟙 (pW.obj w)) (IsHomLift.id (changeOfBaseObj_hx A hA w))

/-- **The second comparison 2-isomorphism of the factorisation**: the test cone's 1-morphism to
`𝒵` is the mediating 1-morphism followed by the first projection and `F`. -/
def changeOfBaseLiftBaseIso :
    Z ≅ changeOfBaseLift A Z τ hτ hA ⋙ (fst p𝒳 p𝒴 p𝒵 F G ⋙ F) :=
  (changeOfBaseFstIso A Z τ).symm

/-- The component of `changeOfBaseLiftBaseIso` at `w` is the first component of
`τ.inv.app w`. -/
@[simp] lemma changeOfBaseLiftBaseIso_hom_app (w : W) :
    (changeOfBaseLiftBaseIso A Z τ hτ hA).hom.app w = (τ.inv.app w).a := rfl

include hτ in
/-- If the components of `τ` are vertical, then so are those of `changeOfBaseLiftBaseIso`. -/
lemma changeOfBaseLiftBaseIso_hom_app_isHomLift (w : W) :
    p𝒵.IsHomLift (𝟙 (pW.obj w)) ((changeOfBaseLiftBaseIso A Z τ hτ hA).hom.app w) := by
  exact isHomLift_a (τ.inv.app w) (𝟙 (pW.obj w)) (isHomLift_inv_app_of_hom τ hτ w)

/-- The first component of the inverse of `fstCompFCompDiagonalIso` at `P` is the identity. -/
@[simp] lemma fstCompFCompDiagonalIso_inv_app_a
    (P : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    ((fstCompFCompDiagonalIso p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).inv.app P).a =
      𝟙 (F.obj P.x) := rfl

/-- The second component of the inverse of `fstCompFCompDiagonalIso` at `P` is the inverse of the
comparison isomorphism of `P`. -/
@[simp] lemma fstCompFCompDiagonalIso_inv_app_b
    (P : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    ((fstCompFCompDiagonalIso p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).inv.app P).b = P.iso.inv := rfl

/-- **The mediating 1-morphism is a morphism of test cones**: the compatibility square of
Stacks 003O for its two comparison 2-isomorphisms, at an object. -/
lemma changeOfBaseCompat (w : W) :
    τ.hom.app w ≫ (diagonal hH).map ((changeOfBaseLiftBaseIso A Z τ hτ hA).hom.app w) =
      (mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).map
          ((changeOfBaseLiftCospanIso A Z τ hτ hA).hom.app w) ≫
        (fstCompFCompDiagonalIso p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).inv.app
          ((changeOfBaseLift A Z τ hτ hA).obj w) := by
  have hbb : (τ.hom.app w) ≫ (τ.inv.app w) = 𝟙 _ := NatTrans.congr_app τ.hom_inv_id w
  have ha : (τ.hom.app w).a ≫ (τ.inv.app w).a = 𝟙 (F.obj ((A.obj w).x)) :=
    congrArg Hom.a hbb
  have hFid : F.map (𝟙 ((A.obj w).x)) ≫ 𝟙 (F.obj ((A.obj w).x)) = 𝟙 (F.obj ((A.obj w).x)) := by
    rw [Functor.map_id, Category.id_comp]
  have hGid : G.map (𝟙 ((A.obj w).y)) ≫ ((τ.hom.app w).b ≫ (τ.inv.app w).a) =
      (τ.hom.app w).b ≫ (τ.inv.app w).a := by
    rw [Functor.map_id, Category.id_comp]
  exact Hom.ext' (ha.trans hFid.symm) hGid.symm

/-- `changeOfBaseCompat` with the identities that a strict bicategory's unitors and associator
leave behind. This is the form in which the compatibility condition of a morphism of
2-commutative squares (Stacks 003O) presents itself. -/
lemma changeOfBaseCompat_id (w : W) :
    τ.hom.app w ≫ (diagonal hH).map ((changeOfBaseLiftBaseIso A Z τ hτ hA).hom.app w) ≫ 𝟙 _ =
      (mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).map
          ((changeOfBaseLiftCospanIso A Z τ hτ hA).hom.app w) ≫ 𝟙 _ ≫
        (fstCompFCompDiagonalIso p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).inv.app
          ((changeOfBaseLift A Z τ hτ hA).obj w) := by
  simpa only [Category.comp_id, Category.id_comp] using changeOfBaseCompat A Z τ hτ hA w

section Unique

variable (γ : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G)
  (iFst : A ≅ γ ⋙ mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH)
  (hiFst : ∀ w, (structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).IsHomLift (𝟙 (pW.obj w))
    (iFst.hom.app w))
  (iSnd : Z ≅ γ ⋙ (fst p𝒳 p𝒴 p𝒵 F G ⋙ F))
  (hc : ∀ w, τ.hom.app w ≫ (diagonal hH).map (iSnd.hom.app w) ≫ 𝟙 _ =
    (mapCospan p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).map (iFst.hom.app w) ≫ 𝟙 _ ≫
      (fstCompFCompDiagonalIso p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).inv.app (γ.obj w))

include hc in
/-- The first component of the compatibility square of an arbitrary factorisation. -/
lemma changeOfBaseCompatFst (w : W) :
    (τ.hom.app w).a ≫ iSnd.hom.app w =
      (F.mapIso ((fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).mapIso (iFst.app w))).hom := by
  have h := hc w
  rw [Category.comp_id, Category.id_comp] at h
  have ha : (τ.hom.app w).a ≫ iSnd.hom.app w =
      F.map ((iFst.hom.app w).a) ≫ 𝟙 (F.obj ((γ.obj w).x)) := congrArg Hom.a h
  exact ha.trans (Category.comp_id _)

include hc in
/-- The second component of the compatibility square of an arbitrary factorisation. -/
lemma changeOfBaseCompatSnd (w : W) :
    ((snd p𝒵 p𝒵 p𝒯 H H).mapIso (τ.app w)).hom ≫ iSnd.hom.app w =
      (G.mapIso ((snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).mapIso (iFst.app w))).hom ≫
        (γ.obj w).iso.inv := by
  have h := hc w
  rw [Category.comp_id, Category.id_comp] at h
  exact congrArg Hom.b h

/-- **Uniqueness of the mediating 1-morphism.** Any factorisation of a test cone over the cospan
`(mapCospan, Δ_H)` through `𝒳 ×_𝒵 𝒴` is 2-isomorphic over `𝒞` to
`CategoryTheory.TwoFibreProductOver.changeOfBaseLift`. -/
noncomputable def changeOfBaseLiftIso : γ ≅ changeOfBaseLift A Z τ hτ hA := by
  have hinv : ∀ w, (structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).IsHomLift (𝟙 (pW.obj w))
      (iFst.app w).inv := by
    intro w
    have : (structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).IsHomLift (𝟙 (pW.obj w))
        (iFst.app w).hom := hiFst w
    exact IsHomLift.lift_id_inv _ (pW.obj w) (iFst.app w)
  refine liftIso γ (Functor.isoWhiskerRight iFst.symm (fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)))
    (Functor.isoWhiskerRight iFst.symm (snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)))
    (fun w => isHomLift_a (iFst.inv.app w) (𝟙 (pW.obj w)) (hinv w))
    (fun w => isHomLift_b (iFst.inv.app w) (𝟙 (pW.obj w)) (hinv w)) ?_
    (changeOfBaseFst_comp_eq A hA) (changeOfBaseSnd_comp_eq A hA)
    (changeOfBaseIso_hom_app_isHomLift A Z τ hτ)
  ext w
  exact iso_cancel_fst_leg (F.mapIso ((fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).mapIso (iFst.app w)))
    (G.mapIso ((snd p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).mapIso (iFst.app w)))
    ((snd p𝒵 p𝒵 p𝒯 H H).mapIso (τ.app w)) (iSnd.app w) ((γ.obj w).iso) ((τ.hom.app w).a)
    (changeOfBaseCompatFst A Z τ γ iFst iSnd hc w)
    (changeOfBaseCompatSnd A Z τ γ iFst iSnd hc w)

/-- The first component of `changeOfBaseLiftIso` at `w` is that of `iFst.inv.app w`. -/
@[simp] lemma changeOfBaseLiftIso_hom_app_a (w : W) :
    ((changeOfBaseLiftIso A Z τ hτ hA γ iFst hiFst iSnd hc).hom.app w).a =
      (iFst.inv.app w).a := rfl

/-- The second component of `changeOfBaseLiftIso` at `w` is that of `iFst.inv.app w`. -/
@[simp] lemma changeOfBaseLiftIso_hom_app_b (w : W) :
    ((changeOfBaseLiftIso A Z τ hτ hA γ iFst hiFst iSnd hc).hom.app w).b =
      (iFst.inv.app w).b := rfl

include hiFst in
/-- If the components of `iFst` are vertical, then so are those of `changeOfBaseLiftIso`. -/
lemma changeOfBaseLiftIso_hom_app_isHomLift (w : W) :
    (structureFunctor p𝒳 p𝒴 p𝒵 F G).IsHomLift (𝟙 (pW.obj w))
      ((changeOfBaseLiftIso A Z τ hτ hA γ iFst hiFst iSnd hc).hom.app w) := by
  exact structureFunctor_isHomLift _ (𝟙 (pW.obj w))
    (isHomLift_a (iFst.inv.app w) (𝟙 (pW.obj w)) (isHomLift_inv_app_of_hom iFst hiFst w))

/-- The first compatibility making `changeOfBaseLiftIso` an equivalence of cone morphisms. -/
lemma changeOfBaseRelFst (w : W) :
    iFst.hom.app w ≫ (mapBase (pT := p𝒳) (p𝒜 := p𝒴) F G H hH).map
        ((changeOfBaseLiftIso A Z τ hτ hA γ iFst hiFst iSnd hc).hom.app w) =
      (changeOfBaseLiftCospanIso A Z τ hτ hA).hom.app w := by
  have h : iFst.hom.app w ≫ iFst.inv.app w = 𝟙 (A.obj w) := NatTrans.congr_app iFst.hom_inv_id w
  have ha : (iFst.hom.app w).a ≫ (iFst.inv.app w).a = 𝟙 ((A.obj w).x) := congrArg Hom.a h
  have hb : (iFst.hom.app w).b ≫ (iFst.inv.app w).b = 𝟙 ((A.obj w).y) := congrArg Hom.b h
  exact Hom.ext' ha hb

/-- The second compatibility making `changeOfBaseLiftIso` an equivalence of cone morphisms. -/
lemma changeOfBaseRelSnd (w : W) :
    iSnd.hom.app w ≫ F.map
        ((changeOfBaseLiftIso A Z τ hτ hA γ iFst hiFst iSnd hc).hom.app w).a =
      (changeOfBaseLiftBaseIso A Z τ hτ hA).hom.app w :=
  iso_cancel_leg (F.mapIso ((fst p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)).mapIso (iFst.app w)))
    (iSnd.app w) ((fst p𝒵 p𝒵 p𝒯 H H).mapIso (τ.app w))
    (changeOfBaseCompatFst A Z τ γ iFst iSnd hc w)

end Unique

end Cone

end CategoryTheory.TwoFibreProductOver

end
