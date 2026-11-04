module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso

/-!
# Local bijectivity of homology maps under extension by zero

A map of presheaves is locally surjective (resp. locally injective) exactly when any map
isomorphic to it in the arrow category is. Consequently, for a map `φ` of `ℕ`-indexed cochain
complexes of presheaves of modules whose homology maps are locally surjective (resp. locally
injective) in every degree, the same holds in every degree of its extension by zero to a map of
`ℤ`-indexed complexes: in a degree `n ≥ 0` the homology map of the extension is the one of `φ`
in degree `n`, read through `HomologicalComplex.extendHomologyIso`, and in a negative degree
both homology objects vanish, so the map is invertible.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_iff_of_arrowIso` and
  `CategoryTheory.Presheaf.isLocallyInjective_iff_of_arrowIso`: local surjectivity and local
  injectivity are invariant under isomorphisms of arrows.
* `PresheafOfModules.isLocallySurjective_homologyMap_extendMap` and
  `PresheafOfModules.isLocallyInjective_homologyMap_extendMap`: the homology maps of the
  extension by zero of a map of `ℕ`-indexed complexes along `ComplexShape.embeddingUpNat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v' u' v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} {g : G₁ ⟶ G₂}

/-- **Local surjectivity is invariant under isomorphisms of arrows.** -/
theorem isLocallySurjective_iff_of_arrowIso (e : Arrow.mk f ≅ Arrow.mk g) :
    IsLocallySurjective J f ↔ IsLocallySurjective J g := by
  have key : ∀ {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} {g : G₁ ⟶ G₂}
      (_ : Arrow.mk f ≅ Arrow.mk g), IsLocallySurjective J f → IsLocallySurjective J g := by
    intro _ _ _ _ f g e _
    rw [Arrow.iso_w' e]
    infer_instance
  exact ⟨key e, key e.symm⟩

/-- **Local injectivity is invariant under isomorphisms of arrows.** -/
theorem isLocallyInjective_iff_of_arrowIso (e : Arrow.mk f ≅ Arrow.mk g) :
    IsLocallyInjective J f ↔ IsLocallyInjective J g := by
  have key : ∀ {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} {g : G₁ ⟶ G₂}
      (_ : Arrow.mk f ≅ Arrow.mk g), IsLocallyInjective J f → IsLocallyInjective J g := by
    intro _ _ _ _ f g e _
    rw [Arrow.iso_w' e]
    infer_instance
  exact ⟨key e, key e.symm⟩

end CategoryTheory.Presheaf

namespace PresheafOfModules

open HomologicalComplex

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R₀ : Cᵒᵖ ⥤ RingCat.{u}}
  {K L : CochainComplex (PresheafOfModules.{v} R₀) ℕ} (φ : K ⟶ L)

/-- The homology map of the extension by zero of `φ` in degree `n : ℤ`, as an arrow of
presheaves of abelian groups, is isomorphic to the homology map of `φ` in degree `m` whenever
`n = m`. -/
noncomputable def arrowIsoHomologyMapExtendMap {n : ℤ} {m : ℕ}
    (hn : ComplexShape.embeddingUpNat.f m = n) :
    Arrow.mk ((toPresheaf R₀).map (homologyMap φ m)) ≅
      Arrow.mk ((toPresheaf R₀).map
        (homologyMap (extendMap φ ComplexShape.embeddingUpNat) n)) :=
  (Arrow.isoMk ((toPresheaf R₀).mapIso (K.extendHomologyIso _ hn))
    ((toPresheaf R₀).mapIso (L.extendHomologyIso _ hn)) (by
      dsimp
      rw [← Functor.map_comp, ← Functor.map_comp,
        extendHomologyIso_hom_naturality φ ComplexShape.embeddingUpNat hn])).symm

/-- In a degree `n : ℤ` outside the image of `ℕ`, the homology map of the extension by zero is
invertible. -/
theorem isIso_homologyMap_extendMap_of_neg (n : ℤ)
    (hn : ∀ m, ComplexShape.embeddingUpNat.f m ≠ n) :
    IsIso ((toPresheaf R₀).map (homologyMap (extendMap φ ComplexShape.embeddingUpNat) n)) :=
  HomologicalComplex.isIso_map_homologyMap_extendMap φ _ (toPresheaf R₀) n hn

/-- **Extension by zero preserves local surjectivity of the homology maps.** If the homology
maps of a map `φ` of `ℕ`-indexed cochain complexes of presheaves of modules are locally
surjective in every degree, so are those of its extension by zero to `ℤ`-indexed complexes. -/
theorem isLocallySurjective_homologyMap_extendMap
    (h : ∀ n : ℕ, Presheaf.IsLocallySurjective J ((toPresheaf R₀).map (homologyMap φ n)))
    (n : ℤ) :
    Presheaf.IsLocallySurjective J
      ((toPresheaf R₀).map (homologyMap (extendMap φ ComplexShape.embeddingUpNat) n)) := by
  by_cases hn : ∃ m, ComplexShape.embeddingUpNat.f m = n
  · obtain ⟨m, hm⟩ := hn
    exact (Presheaf.isLocallySurjective_iff_of_arrowIso J
      (arrowIsoHomologyMapExtendMap φ hm)).1 (h m)
  · have := isIso_homologyMap_extendMap_of_neg φ n (fun m hm ↦ hn ⟨m, hm⟩)
    infer_instance

/-- **Extension by zero preserves local injectivity of the homology maps.** If the homology
maps of a map `φ` of `ℕ`-indexed cochain complexes of presheaves of modules are locally
injective in every degree, so are those of its extension by zero to `ℤ`-indexed complexes. -/
theorem isLocallyInjective_homologyMap_extendMap
    (h : ∀ n : ℕ, Presheaf.IsLocallyInjective J ((toPresheaf R₀).map (homologyMap φ n)))
    (n : ℤ) :
    Presheaf.IsLocallyInjective J
      ((toPresheaf R₀).map (homologyMap (extendMap φ ComplexShape.embeddingUpNat) n)) := by
  by_cases hn : ∃ m, ComplexShape.embeddingUpNat.f m = n
  · obtain ⟨m, hm⟩ := hn
    exact (Presheaf.isLocallyInjective_iff_of_arrowIso J
      (arrowIsoHomologyMapExtendMap φ hm)).1 (h m)
  · have := isIso_homologyMap_extendMap_of_neg φ n (fun m hm ↦ hn ⟨m, hm⟩)
    infer_instance

end PresheafOfModules
