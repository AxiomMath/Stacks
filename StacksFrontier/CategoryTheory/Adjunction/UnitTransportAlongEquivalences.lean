module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjunctionUnitTruncations

/-!
# Invertibility of units transported along equivalences

Let `F ⊣ G` and `F' ⊣ G'` be two adjunctions and let `P`, `Q` be equivalences of categories with
`P ⋙ F ≅ F' ⋙ Q`. Then the unit of the first adjunction is invertible at `P N` exactly when the
unit of the second is invertible at `N`. Only the left adjoints and the equivalences enter: by
`Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app_iff_bijective` a unit at `X` is
invertible exactly when its left adjoint is bijective on morphisms into `X`, and bijectivity is
carried across fully faithful, essentially surjective functors.

## Main results

* `CategoryTheory.Adjunction.isIso_unit_app_iff_of_isEquivalence`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

open Stacks.DerivedCategory.AdjunctionUnitTruncations

variable {B : Type*} [Category* B] {A : Type*} [Category* A] {B' : Type*} [Category* B']
  {A' : Type*} [Category* A']

/-- Bijectivity of a functor on the morphisms into a fixed object is invariant under replacing
the source by an isomorphic object. -/
theorem bijective_map_of_iso_source (F : B ⥤ A) {Z Z' X : B} (e : Z ≅ Z')
    (h : Function.Bijective (fun f : Z' ⟶ X ↦ F.map f)) :
    Function.Bijective (fun f : Z ⟶ X ↦ F.map f) := by
  have : (fun f : Z ⟶ X ↦ F.map f) =
      (fun g : F.obj Z' ⟶ F.obj X ↦ F.map e.hom ≫ g) ∘ (fun f : Z' ⟶ X ↦ F.map f) ∘
        (fun f : Z ⟶ X ↦ e.inv ≫ f) := by
    funext f
    simp [← F.map_comp_assoc]
  rw [this]
  refine Function.Bijective.comp ⟨fun a b hab ↦ ?_, fun g ↦ ⟨F.map e.inv ≫ g, by
    simp [← F.map_comp_assoc]⟩⟩ (Function.Bijective.comp h ⟨fun a b hab ↦ ?_,
      fun g ↦ ⟨e.hom ≫ g, by simp⟩⟩)
  · simpa [← F.map_comp_assoc] using congrArg (F.map e.inv ≫ ·) hab
  · simpa using congrArg (e.hom ≫ ·) hab

/-- **Bijectivity of left adjoints on morphisms, across equivalences.** If `P ⋙ F ≅ F' ⋙ Q` with
`P` and `Q` fully faithful and `P` essentially surjective, then `F` is bijective on morphisms into
`P N` exactly when `F'` is bijective on morphisms into `N`. -/
theorem forall_bijective_map_iff (F : B ⥤ A) (F' : B' ⥤ A') (P : B' ⥤ B) (Q : A' ⥤ A)
    [P.Full] [P.Faithful] [P.EssSurj] [Q.Full] [Q.Faithful] (Φ : P ⋙ F ≅ F' ⋙ Q) (N : B') :
    (∀ Z : B, Function.Bijective (fun f : Z ⟶ P.obj N ↦ F.map f)) ↔
      ∀ Z' : B', Function.Bijective (fun f : Z' ⟶ N ↦ F'.map f) := by
  have key : ∀ Z' : B', (fun f : Z' ⟶ N ↦ F.map (P.map f)) =
      (fun g : Q.obj (F'.obj Z') ⟶ Q.obj (F'.obj N) ↦ Φ.hom.app Z' ≫ g ≫ Φ.inv.app N) ∘
        (fun g : F'.obj Z' ⟶ F'.obj N ↦ Q.map g) ∘ (fun f : Z' ⟶ N ↦ F'.map f) :=
    fun Z' ↦ funext fun f ↦ by simpa using Φ.hom.naturality_assoc f (Φ.inv.app N)
  have hconj : ∀ Z' : B', Function.Bijective
      (fun g : Q.obj (F'.obj Z') ⟶ Q.obj (F'.obj N) ↦ Φ.hom.app Z' ≫ g ≫ Φ.inv.app N) :=
    fun Z' ↦ ⟨fun a b hab ↦ by simpa using congrArg (Φ.inv.app Z' ≫ · ≫ Φ.hom.app N) hab,
      fun g ↦ ⟨Φ.inv.app Z' ≫ g ≫ Φ.hom.app N, by simp⟩⟩
  have hiff : ∀ Z' : B', Function.Bijective (fun f : P.obj Z' ⟶ P.obj N ↦ F.map f) ↔
      Function.Bijective (fun f : Z' ⟶ N ↦ F'.map f) := by
    intro Z'
    rw [← Function.Bijective.of_comp_iff (fun f : P.obj Z' ⟶ P.obj N ↦ F.map f)
      ((Functor.FullyFaithful.ofFullyFaithful P).map_bijective Z' N)]
    change Function.Bijective (fun f : Z' ⟶ N ↦ F.map (P.map f)) ↔ _
    rw [key Z', Function.Bijective.of_comp_iff' (hconj Z'),
      Function.Bijective.of_comp_iff' ((Functor.FullyFaithful.ofFullyFaithful Q).map_bijective _ _)]
  exact ⟨fun h Z' ↦ (hiff Z').1 (h _),
    fun h Z ↦ bijective_map_of_iso_source F (P.objObjPreimageIso Z).symm ((hiff _).2 (h _))⟩

/-- **Invertibility of units, across equivalences.** Let `F ⊣ G` and `F' ⊣ G'` be adjunctions,
`P` an equivalence and `Q` fully faithful with `P ⋙ F ≅ F' ⋙ Q`. Then the unit of `F ⊣ G` is
invertible at `P N` exactly when the unit of `F' ⊣ G'` is invertible at `N`. -/
theorem isIso_unit_app_iff_of_isEquivalence {F : B ⥤ A} {G : A ⥤ B} {F' : B' ⥤ A'}
    {G' : A' ⥤ B'} (adj : F ⊣ G) (adj' : F' ⊣ G') (P : B' ⥤ B) (Q : A' ⥤ A)
    [P.Full] [P.Faithful] [P.EssSurj] [Q.Full] [Q.Faithful] (Φ : P ⋙ F ≅ F' ⋙ Q) (N : B') :
    IsIso (adj.unit.app (P.obj N)) ↔ IsIso (adj'.unit.app N) := by
  rw [isIso_unit_app_iff_bijective adj, isIso_unit_app_iff_bijective adj']
  exact forall_bijective_map_iff F F' P Q Φ N

end CategoryTheory.Adjunction
