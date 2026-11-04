module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Transporting a derived-limit triangle along isomorphisms of towers

Let `(Yₙ, sₙ)` and `(Zₙ, tₙ)` be two towers in a pretriangulated category with countable products,
and let `χₙ : Yₙ ≅ Zₙ` be isomorphisms compatible with the transition maps. A distinguished
triangle `M ⟶ ∏ Yₙ ⟶ ∏ Yₙ ⟶ M[1]` whose middle map is `1 - shift` is carried by `∏ χₙ` to a
distinguished triangle `M ⟶ ∏ Zₙ ⟶ ∏ Zₙ ⟶ M[1]` of the same shape, whose first map is the first
map of the given triangle followed by `∏ χₙ`. Precomposing the first map with an isomorphism
`M' ≅ M` likewise gives a distinguished triangle of the same shape.

## Main results

* `CategoryTheory.Pretriangulated.distTriang_derivedLimit_of_iso`: the transport along `χ`.
* `CategoryTheory.Pretriangulated.distTriang_derivedLimit_precomp_iso`: the precomposition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A derived-limit triangle transported along isomorphisms of towers.** -/
theorem distTriang_derivedLimit_of_iso {Y Z : ℕ → C} [HasProduct Y] [HasProduct Z]
    (s : ∀ n : ℕ, Y (n + 1) ⟶ Y n) (t : ∀ n : ℕ, Z (n + 1) ⟶ Z n) (χ : ∀ n : ℕ, Y n ≅ Z n)
    (hχ : ∀ n : ℕ, (χ (n + 1)).hom ≫ t n = s n ≫ (χ n).hom) {M : C} (p : M ⟶ ∏ᶜ Y)
    (δ : ∏ᶜ Y ⟶ M⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π Y n - Pi.π Y (n + 1) ≫ s n) δ ∈ distTriang C) :
    Triangle.mk (p ≫ Limits.Pi.map fun n => (χ n).hom)
        (Pi.lift fun n : ℕ => Pi.π Z n - Pi.π Z (n + 1) ≫ t n)
        (Limits.Pi.map (fun n => (χ n).inv) ≫ δ) ∈ distTriang C := by
  let Φ : ∏ᶜ Y ≅ ∏ᶜ Z :=
    { hom := Limits.Pi.map fun n => (χ n).hom
      inv := Limits.Pi.map fun n => (χ n).inv
      hom_inv_id := Pi.hom_ext _ _ fun n => by simp
      inv_hom_id := Pi.hom_ext _ _ fun n => by simp }
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl M) Φ.symm Φ.symm ?_ ?_ ?_)
  · exact Pi.hom_ext _ _ fun n => by simp [Φ]
  · refine Pi.hom_ext _ _ fun n => ?_
    have ht : t n ≫ (χ n).inv = (χ (n + 1)).inv ≫ s n := by
      rw [Iso.eq_inv_comp, reassoc_of% hχ, Iso.hom_inv_id, Category.comp_id]
    simp only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Iso.symm_hom, Φ,
      Category.assoc, limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Preadditive.comp_sub,
      Preadditive.sub_comp, Limits.Pi.map_π, Limits.Pi.map_π_assoc, ht]
  · simp [Φ]

/-- **A derived-limit triangle with its first map precomposed with an isomorphism.** -/
theorem distTriang_derivedLimit_precomp_iso {Y : ℕ → C} [HasProduct Y]
    (s : ∀ n : ℕ, Y (n + 1) ⟶ Y n) {M M' : C} (a : M' ≅ M) (p : M ⟶ ∏ᶜ Y)
    (δ : ∏ᶜ Y ⟶ M⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π Y n - Pi.π Y (n + 1) ≫ s n) δ ∈ distTriang C) :
    Triangle.mk (a.hom ≫ p) (Pi.lift fun n : ℕ => Pi.π Y n - Pi.π Y (n + 1) ≫ s n)
        (δ ≫ (shiftFunctor C (1 : ℤ)).map a.inv) ∈ distTriang C := by
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ a (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_)
  simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Iso.refl_hom,
    Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

end CategoryTheory.Pretriangulated
