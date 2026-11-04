module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Changing the first leg of a 2-fibre product over a base by a vertical isomorphism

Fix a base category `𝒞` and categories `A`, `X`, `Z` over it. The 2-fibre product over `𝒞` of
`y : A ⥤ Z` and `G : X ⥤ Z` is `CategoryTheory.TwoFibreProductOver`: an object is
`(U, a, x, φ : y a ≅ G x)` with `φ` vertical over `U`. Replacing `y` by `y'` along a natural
isomorphism `θ : y ≅ y'` whose components are vertical changes nothing but the comparison
isomorphism of each object, which becomes `θ⁻¹ ≫ φ`; this gives an equivalence of the two first
projections over `A`, and an isomorphism of any two presheaves representing the two 2-fibre
products, which is computed on the section named by an object.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.mapFstIso`: the functor induced by a vertical isomorphism of
  the first legs.
* `CategoryTheory.TwoFibreProductOver.mapFstIsoUnit` and
  `CategoryTheory.TwoFibreProductOver.mapFstIsoCounit`: the unit and counit of that equivalence.
* `CategoryTheory.TwoFibreProductOver.mapFstIsoEquivalenceOver`: the equivalence of the first
  projections it gives, over the first factor.
* `CategoryTheory.TwoFibreProductOver.mapFstIsoPresheafIso`: the isomorphism of two presheaves
  representing the two 2-fibre products.

## Main results

* `CategoryTheory.TwoFibreProductOver.mapFstIsoPresheafIso_hom_app_sectionOfObj`: that
  isomorphism carries the section named by an object `R` to the section named by its image
  under `mapFstIso`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section MapFstIso

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A : Type u₂} [Category.{v₂} A]
  {X : Type u₃} [Category.{v₃} X] {Z : Type u₄} [Category.{v₄} Z]
  {pA : A ⥤ 𝒞} {pX : X ⥤ 𝒞} {pZ : Z ⥤ 𝒞} {y₁ y₂ : A ⥤ Z} {G : X ⥤ Z}
  (θ : y₁ ≅ y₂) (hθ : ∀ a, pZ.IsHomLift (𝟙 (pA.obj a)) (θ.hom.app a))

/-- The functor between 2-fibre products over the base induced by a vertical isomorphism
`θ : y₁ ≅ y₂` of the first legs: an object `(U, a, x, φ)` goes to `(U, a, x, θ⁻¹ ≫ φ)` and a
morphism keeps its two components. -/
def mapFstIso : TwoFibreProductOver pA pX pZ y₁ G ⥤ TwoFibreProductOver pA pX pZ y₂ G where
  obj R :=
    { base := R.base
      x := R.x
      y := R.y
      hx := R.hx
      hy := R.hy
      iso := (θ.app R.x).symm ≪≫ R.iso
      vertical := by
        have h1 := R.vertical
        have h2 : pZ.IsHomLift (𝟙 R.base) (θ.inv.app R.x) := by
          rw [← R.hx]
          have : pZ.IsHomLift (𝟙 (pA.obj R.x)) (θ.app R.x).hom := hθ R.x
          exact IsHomLift.lift_id_inv pZ (pA.obj R.x) (θ.app R.x)
        simpa using IsHomLift.comp pZ (𝟙 R.base) (𝟙 R.base) (θ.inv.app R.x) R.iso.hom }
  map {R R'} φ :=
    { hbase := φ.hbase
      a := φ.a
      b := φ.b
      ha := φ.ha
      hb := φ.hb
      w := by
        have hw : y₁.map φ.a ≫ R'.iso.hom = R.iso.hom ≫ G.map φ.b := φ.w
        change y₂.map φ.a ≫ θ.inv.app R'.x ≫ R'.iso.hom = (θ.inv.app R.x ≫ R.iso.hom) ≫ G.map φ.b
        rw [← Category.assoc, θ.inv.naturality φ.a, Category.assoc, hw, Category.assoc] }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `mapFstIso` does not change the first component of an object. -/
@[simp] lemma mapFstIso_obj_x (R : TwoFibreProductOver pA pX pZ y₁ G) :
    ((mapFstIso θ hθ).obj R).x = R.x := rfl

/-- `mapFstIso` does not change the second component of an object. -/
@[simp] lemma mapFstIso_obj_y (R : TwoFibreProductOver pA pX pZ y₁ G) :
    ((mapFstIso θ hθ).obj R).y = R.y := rfl

/-- `mapFstIso` precomposes the comparison isomorphism of an object with `θ⁻¹`. -/
@[simp] lemma mapFstIso_obj_iso (R : TwoFibreProductOver pA pX pZ y₁ G) :
    ((mapFstIso θ hθ).obj R).iso = (θ.app R.x).symm ≪≫ R.iso := rfl

include hθ in
/-- The components of the inverse `θ.symm` of a vertical isomorphism of the first legs are
vertical. -/
theorem isHomLift_symm_hom_app (a : A) : pZ.IsHomLift (𝟙 (pA.obj a)) (θ.symm.hom.app a) := by
  have : pZ.IsHomLift (𝟙 (pA.obj a)) (θ.app a).hom := hθ a
  exact IsHomLift.lift_id_inv pZ (pA.obj a) (θ.app a)

/-- The unit of the equivalence induced by a vertical isomorphism of the first legs: the
identity on both components. -/
noncomputable def mapFstIsoUnit :
    𝟭 (TwoFibreProductOver pA pX pZ y₁ G) ≅
      mapFstIso θ hθ ⋙ mapFstIso θ.symm (isHomLift_symm_hom_app θ hθ) :=
  NatIso.ofComponents
    (fun R => isoMkVertical (U := R.base) (Iso.refl R.x) (Iso.refl R.y) (IsHomLift.id R.hx)
      (IsHomLift.id R.hy) (by
        change y₁.map (𝟙 R.x) ≫ θ.hom.app R.x ≫ θ.inv.app R.x ≫ R.iso.hom =
          R.iso.hom ≫ G.map (𝟙 R.y)
        simp))
    (fun {R R'} φ => Hom.ext' (by
        change φ.a ≫ 𝟙 R'.x = 𝟙 R.x ≫ φ.a
        simp) (by
        change φ.b ≫ 𝟙 R'.y = 𝟙 R.y ≫ φ.b
        simp))

/-- The counit of the equivalence induced by a vertical isomorphism of the first legs: the
identity on both components. -/
noncomputable def mapFstIsoCounit :
    mapFstIso θ.symm (isHomLift_symm_hom_app θ hθ) ⋙ mapFstIso θ hθ ≅
      𝟭 (TwoFibreProductOver pA pX pZ y₂ G) :=
  NatIso.ofComponents
    (fun R => isoMkVertical (U := R.base) (Iso.refl R.x) (Iso.refl R.y) (IsHomLift.id R.hx)
      (IsHomLift.id R.hy) (by
        change y₂.map (𝟙 R.x) ≫ R.iso.hom =
          (θ.inv.app R.x ≫ θ.hom.app R.x ≫ R.iso.hom) ≫ G.map (𝟙 R.y)
        simp))
    (fun {R R'} φ => Hom.ext' (by
        change φ.a ≫ 𝟙 R'.x = 𝟙 R.x ≫ φ.a
        simp) (by
        change φ.b ≫ 𝟙 R'.y = 𝟙 R.y ≫ φ.b
        simp))

/-- A vertical isomorphism of the first legs induces an equivalence of 2-fibre products over the
base, strictly over the first factor. -/
noncomputable def mapFstIsoEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (fst pA pX pZ y₁ G) (fst pA pX pZ y₂ G) where
  hom := ⟨mapFstIso θ hθ, rfl⟩
  inv := ⟨mapFstIso θ.symm (isHomLift_symm_hom_app θ hθ), rfl⟩
  unitIso := mapFstIsoUnit θ hθ
  counitIso := mapFstIsoCounit θ hθ
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_refl _ _).symm
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_refl _ _).symm

end MapFstIso

section Presheaf

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A : Type u₂} [Category.{v₂} A]
  {X : Type u₃} [Category.{v₃} X] {Z : Type u₄} [Category.{v₄} Z]
  {pA : A ⥤ 𝒞} {pX : X ⥤ 𝒞} {pZ : Z ⥤ 𝒞} {y₁ y₂ : A ⥤ Z} {G : X ⥤ Z}
  (θ : y₁ ≅ y₂) (hθ : ∀ a, pZ.IsHomLift (𝟙 (pA.obj a)) (θ.hom.app a))
  {P₁ P₂ : Aᵒᵖ ⥤ Type v₂}
  (e₁ : StacksRepresentableCFG.EquivalenceOver (fst pA pX pZ y₁ G)
    (presheafOfCategories (P₁ ⋙ typeToCat)).p)
  (e₂ : StacksRepresentableCFG.EquivalenceOver (fst pA pX pZ y₂ G)
    (presheafOfCategories (P₂ ⋙ typeToCat)).p)

/-- Presheaves representing the 2-fibre products along two vertically isomorphic first legs are
isomorphic. -/
noncomputable def mapFstIsoPresheafIso : P₁ ≅ P₂ :=
  PresheafOfCategories.isoOfEquivalenceOver e₁ ((mapFstIsoEquivalenceOver θ hθ).trans e₂)

/-- The isomorphism `mapFstIsoPresheafIso` carries the section of `P₁` named by an object `R` of
the first 2-fibre product to the section of `P₂` named by the image of `R` under `mapFstIso`. -/
theorem mapFstIsoPresheafIso_hom_app_sectionOfObj (R : TwoFibreProductOver pA pX pZ y₁ G)
    {W : A} (h : R.x = W) :
    (mapFstIsoPresheafIso θ hθ e₁ e₂).hom.app (op W)
        (PresheafOfCategories.sectionOfObj e₁ R h) =
      PresheafOfCategories.sectionOfObj e₂ ((mapFstIso θ hθ).obj R) h := by
  let E := (mapFstIsoEquivalenceOver θ hθ).trans e₂
  set s := PresheafOfCategories.sectionOfObj e₁ R h with hs
  let o : (presheafOfCategories (P₁ ⋙ typeToCat)).obj := ⟨W, Discrete.mk s⟩
  have ho : (fst pA pX pZ y₁ G).obj (e₁.inv.functor.obj o) = W := Functor.congr_obj e₁.inv.w o
  have hkey : (mapFstIsoPresheafIso θ hθ e₁ e₂).hom.app (op W) s =
      PresheafOfCategories.sectionOfObj E (e₁.inv.functor.obj o) ho := rfl
  have hsame : PresheafOfCategories.sectionOfObj e₁ (e₁.inv.functor.obj o) ho =
      PresheafOfCategories.sectionOfObj e₁ R h :=
    PresheafOfCategories.sectionOfObj_inv_obj e₁ o
  rw [hkey, PresheafOfCategories.sectionOfObj_eq_of_fiberIso E ho h
    (PresheafOfCategories.fiberIsoOfSectionOfObj_eq e₁ ho h hsame)]
  rfl

end Presheaf

end CategoryTheory.TwoFibreProductOver

end
