module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Yoneda

/-!
# Bijectivity of a functor on morphisms along isomorphisms of functors and composites

Bijectivity of a functor `L` on the morphisms `Y ⟶ X` is invariant under isomorphisms of
functors and is read off a composite `L ⋙ L'` when `L'` is bijective on the relevant morphisms.
By `CategoryTheory.Adjunction.isIso_unit_app_iff_bijective_map` this transports invertibility
of the unit of an adjunction at `X`.

## Main results

* `CategoryTheory.Functor.bijective_map_iff_of_natIso_unitIsoMapBijective` and
  `CategoryTheory.Functor.bijective_comp_map_iff_unitIsoMapBijective`: transport along
  isomorphisms and composites.
* `CategoryTheory.Functor.nonempty_iso_of_bijective_map_unitIsoMapBijective`: such a functor
  reflects isomorphic objects.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]

namespace Functor

/-- Bijectivity of a functor on the morphisms `Y ⟶ X` is invariant under isomorphism of
functors. -/
theorem bijective_map_iff_of_natIso_unitIsoMapBijective {L L' : C ⥤ D} (e : L ≅ L') (Y X : C) :
    Function.Bijective (fun f : Y ⟶ X ↦ L.map f) ↔
      Function.Bijective (fun f : Y ⟶ X ↦ L'.map f) := by
  have h : (fun f : Y ⟶ X ↦ L'.map f) =
      ((e.app Y).homCongr (e.app X)) ∘ (fun f : Y ⟶ X ↦ L.map f) := by
    funext f
    simp [Iso.homCongr_apply]
  rw [h, ((e.app Y).homCongr (e.app X)).bijective.of_comp_iff']

/-- A composite `L ⋙ L'` is bijective on the morphisms `Y ⟶ X` exactly when `L` is, provided
`L'` is bijective on the morphisms `L Y ⟶ L X`. -/
theorem bijective_comp_map_iff_unitIsoMapBijective {L : C ⥤ D} {L' : D ⥤ E} {Y X : C}
    (h : Function.Bijective (fun g : L.obj Y ⟶ L.obj X ↦ L'.map g)) :
    Function.Bijective (fun f : Y ⟶ X ↦ (L ⋙ L').map f) ↔
      Function.Bijective (fun f : Y ⟶ X ↦ L.map f) :=
  h.of_comp_iff' (fun f : Y ⟶ X ↦ L.map f)

/-- A functor which is bijective on the morphisms into `X` and into `Y` reflects isomorphisms
`L X ≅ L Y` to isomorphisms `X ≅ Y`. -/
theorem nonempty_iso_of_bijective_map_unitIsoMapBijective (L : C ⥤ D) {X Y : C}
    (hX : ∀ Z : C, Function.Bijective (fun f : Z ⟶ X ↦ L.map f))
    (hY : ∀ Z : C, Function.Bijective (fun f : Z ⟶ Y ↦ L.map f)) (e : L.obj X ≅ L.obj Y) :
    Nonempty (X ≅ Y) := by
  obtain ⟨φ, hφ⟩ := (hY X).2 e.hom
  obtain ⟨ψ, hψ⟩ := (hX Y).2 e.inv
  refine ⟨⟨φ, ψ, (hX X).1 ?_, (hY Y).1 ?_⟩⟩ <;> simp [hφ, hψ]

end Functor

end CategoryTheory

end
