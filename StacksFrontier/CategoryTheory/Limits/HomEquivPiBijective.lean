module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Morphisms into a product, read through a natural bijection

For a family `N` of objects of `M` with a product and a functor `A : M ⥤ C`, write
`Φ_A : (X ⟶ A (∏ N)) → ∀ i, (X ⟶ A (N i))` for the map `φ ↦ (φ ≫ A (π i))ᵢ`. It is bijective
when `A` preserves the product. This file records that, and that bijectivity of `Φ` is carried
along a bijection `(X ⟶ A m) ≃ (Y ⟶ B m)` natural in `m`.

## Main results

* `CategoryTheory.Limits.bijective_comp_map_π_of_preservesLimit`: `Φ_A` is bijective when `A`
  preserves the product of `N`.
* `CategoryTheory.Limits.bijective_comp_map_π_of_equiv`: if `Φ_B` is bijective and
  `(X ⟶ A m) ≃ (Y ⟶ B m)` naturally in `m`, then `Φ_A` is bijective.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C D M : Type*} [Category C] [Category D] [Category M]

/-- The universal property of a product, as bijectivity of `φ ↦ (φ ≫ π i)ᵢ`. -/
lemma bijective_comp_π {ι : Type*} (F : ι → C) [HasProduct F] (X : C) :
    Function.Bijective (fun φ : X ⟶ ∏ᶜ F => fun i => φ ≫ Pi.π F i) :=
  ⟨fun _ _ h => Pi.hom_ext _ _ fun i => congrFun h i,
    fun g => ⟨Pi.lift g, funext fun i => Pi.lift_comp_π g i⟩⟩

/-- If `A` preserves the product of `N`, then `φ ↦ (φ ≫ A (π i))ᵢ` is bijective on morphisms
into `A (∏ N)`. -/
lemma bijective_comp_map_π_of_preservesLimit {ι : Type*} (A : M ⥤ C) (N : ι → M)
    [HasProduct N] [HasProduct fun i => A.obj (N i)] [PreservesLimit (Discrete.functor N) A]
    (X : C) :
    Function.Bijective (fun φ : X ⟶ A.obj (∏ᶜ N) => fun i => φ ≫ A.map (Pi.π N i)) := by
  convert (bijective_comp_π _ X).comp
    ((Iso.refl X).homCongr (asIso (piComparison A N))).bijective using 1
  funext φ i
  simp

/-- **Bijectivity of `φ ↦ (φ ≫ A (π i))ᵢ` is carried along a natural bijection.** If
`(X ⟶ A m) ≃ (Y ⟶ B m)` naturally in `m` and the map is bijective for `B`, it is bijective for
`A`. -/
lemma bijective_comp_map_π_of_equiv {A : M ⥤ C} {B : M ⥤ D} {X : C} {Y : D}
    (β : ∀ m, (X ⟶ A.obj m) ≃ (Y ⟶ B.obj m))
    (hβ : ∀ {m m' : M} (g : m ⟶ m') (φ : X ⟶ A.obj m), β m' (φ ≫ A.map g) = β m φ ≫ B.map g)
    {ι : Type*} (N : ι → M) [HasProduct N]
    (h : Function.Bijective (fun ψ : Y ⟶ B.obj (∏ᶜ N) => fun i => ψ ≫ B.map (Pi.π N i))) :
    Function.Bijective (fun φ : X ⟶ A.obj (∏ᶜ N) => fun i => φ ≫ A.map (Pi.π N i)) := by
  convert (Equiv.piCongrRight fun i => (β (N i)).symm).bijective.comp
    (h.comp (β (∏ᶜ N)).bijective) using 1
  funext φ i
  simp [← hβ]

end CategoryTheory.Limits
