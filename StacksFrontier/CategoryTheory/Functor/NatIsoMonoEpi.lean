module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.NatIso

/-!
# Naturally isomorphic functors agree on monomorphy and epimorphy

If `F ≅ G` then `F.map f` is a monomorphism exactly when `G.map f` is, and likewise for
epimorphisms: conjugating by the isomorphism's components changes a map only by isomorphisms on
either side. These are the `Mono` and `Epi` companions of
`CategoryTheory.NatIso.isIso_map_iff`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- Naturally isomorphic functors send a morphism to an epimorphism, or not, together. This is
the `Epi` companion of `CategoryTheory.NatIso.isIso_map_iff`. -/
public theorem NatIso.epi_map_iff {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) : Epi (F.map f) ↔ Epi (G.map f) := by
  constructor <;> intro h
  · rw [show G.map f = e.inv.app A ≫ F.map f ≫ e.hom.app B by simp]
    have : Epi (e.inv.app A) := IsIso.epi_of_iso _
    have : Epi (e.hom.app B) := IsIso.epi_of_iso _
    exact epi_comp _ _
  · rw [show F.map f = e.hom.app A ≫ G.map f ≫ e.inv.app B by simp]
    have : Epi (e.hom.app A) := IsIso.epi_of_iso _
    have : Epi (e.inv.app B) := IsIso.epi_of_iso _
    exact epi_comp _ _

/-- Naturally isomorphic functors send a morphism to a monomorphism, or not, together. -/
public theorem NatIso.mono_map_iff {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) : Mono (F.map f) ↔ Mono (G.map f) := by
  constructor <;> intro h
  · rw [show G.map f = e.inv.app A ≫ F.map f ≫ e.hom.app B by simp]
    have : Mono (e.inv.app A) := IsIso.mono_of_iso _
    have : Mono (e.hom.app B) := IsIso.mono_of_iso _
    exact mono_comp _ _
  · rw [show F.map f = e.hom.app A ≫ G.map f ≫ e.inv.app B by simp]
    have : Mono (e.hom.app A) := IsIso.mono_of_iso _
    have : Mono (e.inv.app B) := IsIso.mono_of_iso _
    exact mono_comp _ _

end CategoryTheory

end
