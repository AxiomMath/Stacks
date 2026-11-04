module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The unit of an adjunction at an object with commutative endomorphisms

Let `L ⊣ R` be an adjunction and `N` an object with `N ≅ R(L(N))` by some isomorphism. The unit
`N ⟶ R(L(N))` has a retraction built from the counit, so after composing with the given
isomorphism it is a split monomorphism `N ⟶ N`; when the endomorphisms of `N` commute with each
other it is therefore invertible, and so is the unit. When the unit at `N` is invertible, `R`
is bijective on morphisms out of `L(N)`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : D ⥤ C} {R : C ⥤ D}

/-- **The unit is invertible at an object with commutative endomorphisms and `N ≅ R(L(N))`.** -/
theorem isIso_unit_app_of_iso_of_commute (adj : L ⊣ R) (N : D) (χ : N ≅ R.obj (L.obj N))
    (hcomm : ∀ g h : N ⟶ N, g ≫ h = h ≫ g) : IsIso (adj.unit.app N) := by
  let mu : N ⟶ N := χ.hom ≫ R.map (L.map χ.hom) ≫ R.map (adj.counit.app (L.obj N)) ≫ χ.inv
  have h : (adj.unit.app N ≫ χ.inv) ≫ mu = 𝟙 N := by
    simp [mu, reassoc_of% (adj.unit_naturality χ.hom)]
  have : IsIso (adj.unit.app N ≫ χ.inv) := ⟨⟨mu, h, (hcomm _ _).trans h⟩⟩
  exact IsIso.of_isIso_comp_right _ χ.inv

/-- **`R` is bijective on morphisms out of `L(N)` when the unit at `N` is invertible.** -/
theorem bijective_map_leftAdjoint_obj_of_isIso_unit_app (adj : L ⊣ R) (N : D)
    [IsIso (adj.unit.app N)]
    (K : C) : Function.Bijective (fun f : L.obj N ⟶ K => R.map f) := by
  have h : (fun f : L.obj N ⟶ K => R.map f) =
      (fun g : N ⟶ R.obj K => inv (adj.unit.app N) ≫ g) ∘ adj.homEquiv N K := by
    funext f
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact .comp ⟨fun _ _ hg => (cancel_epi _).1 hg, fun g => ⟨adj.unit.app N ≫ g, by simp⟩⟩
    (adj.homEquiv N K).bijective

end CategoryTheory.Adjunction
