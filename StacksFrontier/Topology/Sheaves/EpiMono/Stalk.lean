module

public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Mono, epi and iso for sheaves of sets are detected on stalks

Let `X` be a topological space and `φ : F ⟶ G` a morphism of sheaves of sets on `X`. Then `φ` is
a monomorphism, an epimorphism, or an isomorphism in the category of sheaves precisely when the
induced map on stalks `φ_x : F_x → G_x` is injective, surjective, or bijective for every point
`x` of `X`.

## Main definitions

* `Stacks.Topology.SheafStalk.stalkMap`: the map `φ_x` induced by `φ` on stalks at `x`.

## Main results

* `Stacks.Topology.SheafStalk.mono_iff_stalk_injective`: `φ` is a monomorphism if and only if
  every `φ_x` is injective.
* `Stacks.Topology.SheafStalk.epi_iff_stalk_surjective`: `φ` is an epimorphism if and only if
  every `φ_x` is surjective.
* `Stacks.Topology.SheafStalk.isIso_iff_stalk_bijective`: `φ` is an isomorphism if and only if
  every `φ_x` is bijective.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Topology.SheafStalk

/-- The map on stalks at `x` induced by a morphism of sheaves of types. -/
noncomputable def stalkMap {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X}
    (φ : F ⟶ G) (x : X) : F.presheaf.stalk x → G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom

/-- A morphism of sheaves of sets is a monomorphism in the category of
sheaves if and only if it is injective on stalks at every point. -/
@[stacks 007T "(1)"]
theorem mono_iff_stalk_injective {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X}
    (φ : F ⟶ G) : Mono φ ↔ ∀ x : X, Function.Injective (stalkMap φ x) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono φ]
  exact forall_congr' fun _ => CategoryTheory.mono_iff_injective _

/-- The stalk maps of an epimorphism of sheaves of sets are surjective. -/
lemma stalk_surjective_of_epi {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X}
    (φ : F ⟶ G) [Epi φ] (x : X) : Function.Surjective (stalkMap φ x) := by
  classical
  have hpres : (TopCat.Sheaf.forget (Type u) X ⋙
      TopCat.Presheaf.stalkFunctor (Type u) x).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (stalkSkyscraperSheafAdjunction (X := X) (C := Type u) x)
  have hepi : Epi ((TopCat.Sheaf.forget (Type u) X ⋙
      TopCat.Presheaf.stalkFunctor (Type u) x).map φ) := hpres.preserves φ
  exact (CategoryTheory.epi_iff_surjective _).mp hepi

/-- A morphism of sheaves of sets which is surjective on every stalk is an epimorphism. -/
lemma epi_of_stalk_surjective {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X}
    (φ : F ⟶ G) (h : ∀ x : X, Function.Surjective (stalkMap φ x)) : Epi φ := by
  refine ⟨fun {H} α β hαβ => ?_⟩
  apply Sheaf.hom_ext
  ext ⟨U⟩ s
  apply TopCat.Presheaf.section_ext H U
  intro x hx
  obtain ⟨t, ht⟩ := h x ((TopCat.Presheaf.germ G.obj U x hx) s)
  have hval : φ.hom ≫ α.hom = φ.hom ≫ β.hom := congrArg (·.hom) hαβ
  have key : ∀ γ : G ⟶ H,
      (CategoryTheory.ConcreteCategory.hom (H.presheaf.germ U x hx))
        ((γ.hom.app (Opposite.op U)) s) =
      (TopCat.Presheaf.stalkFunctor (Type u) x).map γ.hom (stalkMap φ x t) := fun γ => by
    rw [ht]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx γ.hom s).symm
  have hmid : (TopCat.Presheaf.stalkFunctor (Type u) x).map α.hom (stalkMap φ x t) =
      (TopCat.Presheaf.stalkFunctor (Type u) x).map β.hom (stalkMap φ x t) := by
    change ((TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map α.hom) t =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map β.hom) t
    rw [← Functor.map_comp, ← Functor.map_comp, hval]
  exact (key α).trans (hmid.trans (key β).symm)

/-- A morphism of sheaves of sets is an epimorphism in the category of
sheaves if and only if it is surjective on stalks at every point. -/
@[stacks 007T "(2)"]
theorem epi_iff_stalk_surjective {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X}
    (φ : F ⟶ G) : Epi φ ↔ ∀ x : X, Function.Surjective (stalkMap φ x) :=
  ⟨fun _ x => stalk_surjective_of_epi φ x, epi_of_stalk_surjective φ⟩

/-- A morphism of sheaves of sets is an isomorphism if and only if it is
bijective on stalks at every point. -/
@[stacks 007T "(3)"]
theorem isIso_iff_stalk_bijective {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X}
    (φ : F ⟶ G) : IsIso φ ↔ ∀ x : X, Function.Bijective (stalkMap φ x) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso φ]
  exact forall_congr' fun _ => isIso_iff_bijective _

end Stacks.Topology.SheafStalk
