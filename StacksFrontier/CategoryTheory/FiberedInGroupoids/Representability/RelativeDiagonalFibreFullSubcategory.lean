module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre

/-!
# The fibre of the relative diagonal at a diagonal point does not see a full subcategory

Let `p : X ⥤ 𝒞` be fibred in groupoids, let `F : X ⥤ 𝒴` be a 1-morphism strictly over `𝒞` and
let `P` be a property of the objects of `X`. Restricting `p` and `F` to the full subcategory on
`P` gives a 1-morphism `P.ι ⋙ F` strictly over `𝒞` out of a category over `𝒞`, and for a
1-morphism `x : 𝒯 ⥤ P.FullSubcategory` the fibre of the relative diagonal of `P.ι ⋙ F` at the
diagonal point `(x, x, id)` is the presheaf of vertical morphisms `x ⟶ x` of the full
subcategory lying over identities of `𝒴`
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf`).

The full subcategory is full, so those are the vertical morphisms `x ⟶ x` of `X`: the presheaf is
isomorphic to the one of `F` at the diagonal point `(x ⋙ P.ι, x ⋙ P.ι, id)`. That is
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheafFullSubcategoryIso`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheafFullSubcategoryIso`:
  the isomorphism.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}
  (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p)
  (P : ObjectProperty X) (hpP : (P.ι ⋙ p).IsFiberedInGroupoids)
  (x : 𝒯 ⥤ P.FullSubcategory)
  (hFP : (P.ι ⋙ F) ⋙ q = P.ι ⋙ p)
  (hxP : (x ⋙ RelDiag hFP) ⋙ RelProdP (P.ι ⋙ p) q (P.ι ⋙ F) = p𝒯)
  (hx : ((x ⋙ P.ι) ⋙ RelDiag hF) ⋙ RelProdP p q F = p𝒯)

/-- A vertical endomorphism of an object of the full subcategory lying over an identity of `𝒴`
is one of the underlying object of `X`. -/
def relVertHomFullSubcategoryToFun {a : 𝒯}
    (m : RelVertHom p𝒯 (x ⋙ RelDiag hFP) a) :
    RelVertHom p𝒯 ((x ⋙ P.ι) ⋙ RelDiag hF) a :=
  ⟨⟨m.1.1.hom, by
    have := m.1.2
    exact Functor.isHomLift_map_of_comp_eq (G := P.ι) (p := P.ι ⋙ p) (q := p) rfl _ m.1.1⟩,
    m.2⟩

/-- A vertical endomorphism of an object of `X` lying over an identity of `𝒴`, read in the full
subcategory. -/
def relVertHomFullSubcategoryInvFun {a : 𝒯}
    (m : RelVertHom p𝒯 ((x ⋙ P.ι) ⋙ RelDiag hF) a) :
    RelVertHom p𝒯 (x ⋙ RelDiag hFP) a :=
  ⟨⟨ObjectProperty.homMk m.1.1, by
    have h : p.IsHomLift (𝟙 (p𝒯.obj a)) m.1.1 := m.1.2
    have hfac := IsHomLift.fac' p (𝟙 (p𝒯.obj a)) m.1.1
    exact IsHomLift.of_fac' (P.ι ⋙ p) _ _ (Functor.congr_obj hx a) (Functor.congr_obj hx a)
      hfac⟩,
    m.2⟩

/-- **The fibre of the relative diagonal at a diagonal point does not see a full subcategory.**
For a 1-morphism `x : 𝒯 ⥤ P.FullSubcategory`, the presheaf of vertical endomorphisms of `x` in
the full subcategory lying over identities of `𝒴` is isomorphic to that of `x ⋙ P.ι` in `X`. -/
noncomputable def relVertHomPresheafFullSubcategoryIso :
    relVertHomPresheaf hq hpP hxP hFP ≅
      relVertHomPresheaf hq hp hx hF :=
  NatIso.ofComponents
    (fun a => Equiv.toIso
      { toFun := relVertHomFullSubcategoryToFun hF P x hFP
        invFun := relVertHomFullSubcategoryInvFun hF P x hFP hx
        left_inv := fun m => RelVertHom.ext rfl
        right_inv := fun m => RelVertHom.ext rfl })
    (fun {a b} h => by
      ext m
      change relVertHomFullSubcategoryToFun hF P x hFP
          (RelVertHom.restrict hq hpP hxP hFP h.unop m) =
        RelVertHom.restrict hq hp hx hF h.unop (relVertHomFullSubcategoryToFun hF P x hFP m)
      refine RelVertHom.restrict_uniq hq hp hx hF h.unop _ _ ?_
      change (RelVertHom.restrict hq hpP hxP hFP h.unop m).1.1.hom ≫
          (x.map h.unop).hom = (x.map h.unop).hom ≫ m.1.1.hom
      have := VertHom.restrict_fac hpP (h1' hxP) (h2' hxP) h.unop m.1
      exact congrArg InducedCategory.Hom.hom this)

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

end
