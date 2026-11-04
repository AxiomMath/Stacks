module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre

/-!
# Global sections of the presheaf of vertical morphisms over the comparison

Let `p : X ⥤ 𝒞`, `q : 𝒴 ⥤ 𝒞` be categories fibred in groupoids, `F : X ⥤ 𝒴` a 1-morphism
strictly over `𝒞`, and `Y : 𝒯 ⥤ X ×_𝒴 X` a point over `p𝒯 : 𝒯 ⥤ 𝒞`, with components
`Y₁, Y₂ : 𝒯 ⥤ X` and comparison isomorphism `F Y₁ ≅ F Y₂`. The presheaf
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf` on `𝒯` has as
sections over `a` the vertical morphisms `Y₁ a ⟶ Y₂ a` lying over the comparison at `a`. This file
identifies its global sections (families compatible with restriction) with the natural families
of such morphisms, i.e. with the vertical natural transformations `Y₁ ⟶ Y₂` lifting the
comparison isomorphism.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.RelVertFamily`: the natural families
  of vertical morphisms `Y₁ a ⟶ Y₂ a` lying over the comparison isomorphism.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomGlobalSectionEquiv`: the
  global sections of `relVertHomPresheaf` are these families.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
variable {p : X ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}

variable (p𝒯 : 𝒯 ⥤ 𝒞) (Y : 𝒯 ⥤ RelProd p q F)

/-- **Natural families of vertical morphisms over the comparison.** Families
`ψ a : Y₁ a ⟶ Y₂ a` of morphisms lying over the identity of `p𝒯 a`, with `F (ψ a)` the comparison
isomorphism of `Y` at `a`, natural in `a`. -/
def RelVertFamily : Type _ :=
  {ψ : ∀ a : 𝒯, (Y₁' Y).obj a ⟶ (Y₂' Y).obj a //
    (∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (ψ a)) ∧ (∀ a, F.map (ψ a) = (Y.obj a).iso.hom) ∧
      ∀ {a' a : 𝒯} (h : a' ⟶ a), ψ a' ≫ (Y₂' Y).map h = (Y₁' Y).map h ≫ ψ a}

variable {p𝒯 Y}

/-- Two natural families of vertical morphisms with the same components are equal. -/
@[ext]
lemma RelVertFamily.ext {ψ ψ' : RelVertFamily p𝒯 Y} (h : ∀ a, ψ.1 a = ψ'.1 a) : ψ = ψ' :=
  Subtype.ext (funext h)

variable (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
  (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p)

/-- **Global sections of `relVertHomPresheaf` are natural families of vertical morphisms over the
comparison.** A family of sections `t a` compatible with restriction is natural: the restriction
of `t a` along `h : a' ⟶ a` is the unique vertical fill-in of the square with sides `Y₁ h` and
`Y₂ h`. -/
noncomputable def relVertHomGlobalSectionEquiv :
    {t : ∀ a : 𝒯, (relVertHomPresheaf hq hp hY hF).obj (op a) //
      ∀ {a' a : 𝒯} (h : a' ⟶ a), (relVertHomPresheaf hq hp hY hF).map h.op (t a) = t a'} ≃
      RelVertFamily p𝒯 Y where
  toFun t := ⟨fun a => (t.1 a).1.1, fun a => (t.1 a).1.2, fun a => (t.1 a).2, fun {a' a} h => by
    have e : (t.1 a').1.1 = (VertHom.restrict hp (h1' hY) (h2' hY) h (t.1 a).1).1 :=
      (congrArg (fun m : RelVertHom p𝒯 Y a' => m.1.1) (t.2 h)).symm
    change (t.1 a').1.1 ≫ _ = _ ≫ (t.1 a).1.1
    rw [e]
    exact VertHom.restrict_fac hp (h1' hY) (h2' hY) h (t.1 a).1⟩
  invFun ψ := ⟨fun a => ⟨⟨ψ.1 a, ψ.2.1 a⟩, ψ.2.2.1 a⟩, fun {a' a} h =>
    (RelVertHom.restrict_uniq hq hp hY hF h ⟨⟨ψ.1 a, ψ.2.1 a⟩, ψ.2.2.1 a⟩
      ⟨⟨ψ.1 a', ψ.2.1 a'⟩, ψ.2.2.1 a'⟩ (ψ.2.2.2 h)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The component at `a` of the natural family attached to a global section `t` is the underlying
morphism `Y₁ a ⟶ Y₂ a` of the section `t a`. -/
@[simp]
lemma relVertHomGlobalSectionEquiv_apply_coe
    (t : {t : ∀ a : 𝒯, (relVertHomPresheaf hq hp hY hF).obj (op a) //
      ∀ {a' a : 𝒯} (h : a' ⟶ a), (relVertHomPresheaf hq hp hY hF).map h.op (t a) = t a'})
    (a : 𝒯) : (relVertHomGlobalSectionEquiv hq hp hY hF t).1 a = (t.1 a).1.1 :=
  rfl

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

end
