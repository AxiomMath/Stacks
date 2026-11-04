module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Transporting shifted morphisms along a fully faithful functor

Let `Φ : C ⥤ D` be a fully faithful additive functor commuting with the shift, and let
`ε : Φ(X) ≅ X'`, `σ : Φ(Y) ≅ Y'` be isomorphisms. Then `f ↦ ε⁻¹ ≫ Φ(f) ≫ σ[i]` is an additive
bijection `ShiftedHom X Y i ≃+ ShiftedHom X' Y' i`. This file names it and records how it
interacts with composition of shifted morphisms.

## Main definitions

* `CategoryTheory.ShiftedHom.conjMapAddEquiv`: the bijection.

## Main results

* `CategoryTheory.ShiftedHom.conj_map_comp`: transport of a composite whose second factor is
  carried, up to the isomorphisms at its ends, to a given shifted morphism.
* `CategoryTheory.ShiftedHom.conjMapAddEquiv_comp_mk₀`: transport of a composite with a
  morphism of degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.ShiftedHom

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (Φ : C ⥤ D) [Φ.CommShift ℤ]

/-- Transporting a composite of shifted morphisms along a functor commuting with the shift and
along isomorphisms at the three objects: if the image of `δ` is `δ'` up to the isomorphisms at
its source and target, the transport of `f.comp δ` is the transport of `f` composed with `δ'`. -/
theorem conj_map_comp {X Y₃ Y₁ : C} {X' Z₃ Z₁ : D} (ε : Φ.obj X ≅ X') (σ₃ : Φ.obj Y₃ ≅ Z₃)
    (σ₁ : Φ.obj Y₁ ≅ Z₁) {a i j : ℤ} (f : ShiftedHom X Y₃ i) (δ : ShiftedHom Y₃ Y₁ a)
    (δ' : ShiftedHom Z₃ Z₁ a) (hδ : δ.map Φ = σ₃.hom ≫ δ' ≫ σ₁.inv⟦a⟧')
    (h : a + i = j) :
    ε.inv ≫ (f.comp δ h).map Φ ≫ σ₁.hom⟦j⟧' =
      ShiftedHom.comp (show ShiftedHom X' Z₃ i from ε.inv ≫ f.map Φ ≫ σ₃.hom⟦i⟧') δ' h := by
  have hn : (shiftFunctor D i).map ((shiftFunctor D a).map σ₁.inv) ≫
        (shiftFunctorAdd' D a i j h).inv.app (Φ.obj Y₁) =
      (shiftFunctorAdd' D a i j h).inv.app Z₁ ≫ (shiftFunctor D j).map σ₁.inv :=
    (shiftFunctorAdd' D a i j h).inv.naturality σ₁.inv
  rw [ShiftedHom.map_comp, hδ]
  simp only [ShiftedHom.comp, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hn, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]

variable [Preadditive C] [Preadditive D] [Φ.Additive] [∀ i : ℤ, (shiftFunctor D i).Additive]

/-- **Transport of shifted morphisms along a fully faithful functor**, `f ↦ ε⁻¹ ≫ Φ(f) ≫ σ[i]`,
for isomorphisms `ε : Φ(X) ≅ X'` and `σ : Φ(Y) ≅ Y'`. -/
def conjMapAddEquiv (hΦ : Φ.FullyFaithful) {X Y : C} {X' Y' : D} (ε : Φ.obj X ≅ X')
    (σ : Φ.obj Y ≅ Y') (i : ℤ) : ShiftedHom X Y i ≃+ ShiftedHom X' Y' i := by
  let φ : ShiftedHom X Y i →+ ShiftedHom X' Y' i :=
    { toFun := fun f => ε.inv ≫ f.map Φ ≫ σ.hom⟦i⟧'
      map_zero' := by simp [ShiftedHom.map]
      map_add' := fun f g => by
        simp [ShiftedHom.map, Preadditive.add_comp, Preadditive.comp_add] }
  refine AddEquiv.ofBijective φ ?_
  have h1 : Function.Bijective (fun g : Φ.obj X ⟶ Φ.obj (Y⟦i⟧) =>
      ε.inv ≫ g ≫ (Φ.commShiftIso i).hom.app Y ≫ σ.hom⟦i⟧') :=
    (Iso.homCongr ε ((Φ.commShiftIso i).app Y ≪≫ (shiftFunctor D i).mapIso σ)).bijective
  convert h1.comp (hΦ.map_bijective X (Y⟦i⟧)) using 1
  funext f
  simp [φ, ShiftedHom.map]

omit [∀ (i : ℤ), (shiftFunctor D i).Additive] in
/-- `conjMapAddEquiv Φ hΦ ε σ i` sends `f` to `ε⁻¹ ≫ Φ(f) ≫ σ[i]`. -/
theorem conjMapAddEquiv_apply (hΦ : Φ.FullyFaithful) {X Y : C} {X' Y' : D} (ε : Φ.obj X ≅ X')
    (σ : Φ.obj Y ≅ Y') (i : ℤ) (f : ShiftedHom X Y i) :
    conjMapAddEquiv Φ hΦ ε σ i f = ε.inv ≫ f.map Φ ≫ σ.hom⟦i⟧' :=
  rfl

omit [∀ (i : ℤ), (shiftFunctor D i).Additive] in
/-- The transport of a composite with a morphism of degree zero. -/
theorem conjMapAddEquiv_comp_mk₀ (hΦ : Φ.FullyFaithful) {X Y Y₂ : C} {X' Y' Y₂' : D}
    (ε : Φ.obj X ≅ X') (σ : Φ.obj Y ≅ Y') (σ₂ : Φ.obj Y₂ ≅ Y₂') (g : Y ⟶ Y₂) (g' : Y' ⟶ Y₂')
    (hg : Φ.map g ≫ σ₂.hom = σ.hom ≫ g') (i : ℤ) (f : ShiftedHom X Y i) :
    conjMapAddEquiv Φ hΦ ε σ₂ i (f.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g) (zero_add i)) =
      (conjMapAddEquiv Φ hΦ ε σ i f).comp (ShiftedHom.mk₀ (0 : ℤ) rfl g') (zero_add i) := by
  simp only [conjMapAddEquiv_apply, ShiftedHom.comp_mk₀, ShiftedHom.map, Functor.map_comp,
    Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  simp only [← Functor.map_comp, hg]

end CategoryTheory.ShiftedHom
