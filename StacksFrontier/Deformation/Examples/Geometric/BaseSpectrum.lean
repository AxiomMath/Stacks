module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Examples.Geometric.Base

/-!
# Spectra of the objects of the base category

The geometric deformation problems of Stacks chapter 93 are problems about schemes over the
spectrum of an object of `𝒞_Λ`. This file names that spectrum and the map of spectra induced
by a morphism of `𝒞_Λ`, records that the assignment is contravariantly functorial, and names
the closed-point immersion of the residue field.

## Main definitions

* `Deformation.Examples.baseSpec`: the spectrum of an object of `𝒞_Λ`.
* `Deformation.Examples.baseSpecMap`: the map of spectra induced by a morphism of `𝒞_Λ`.
* `Deformation.Examples.residueSpecMap`: the map from the spectrum of the residue field to the
  spectrum of an object of `𝒞_Λ`.

## Main results

* `Deformation.Examples.baseSpecMap_id` and `Deformation.Examples.baseSpecMap_comp`: taking
  spectra is a contravariant functor on `𝒞_Λ`.
* `Deformation.Examples.residueSpecMap_naturality`: the closed points of the spectra are
  compatible with the maps of spectra, because a morphism of `𝒞_Λ` respects the chosen
  identifications of the residue fields with `k`.

## Implementation notes

The carrier universe of the object, the universe of `Λ` and the universe of `k` stay
independent, so that the families of schemes built on top of these names are as general as the
category `𝒞_Λ` itself. The residue map of Stacks 07T4 is only available when all three
coincide, so `residueSpecMap` is stated in that case.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The spectrum of an object of `𝒞_Λ`. -/
noncomputable abbrev baseSpec (A : ArtinianLocalAlgCat.{u, v, w} Λ k) : Scheme.{v} :=
  Spec (.of A)

/-- The map of spectra induced by a morphism of `𝒞_Λ`. -/
noncomputable abbrev baseSpecMap {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) :
    baseSpec B ⟶ baseSpec A :=
  Spec.map (CommRingCat.ofHom f.hom.toRingHom)

/-- The map of spectra induced by the identity of an object of `𝒞_Λ` is the identity. -/
@[simp]
theorem baseSpecMap_id (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    baseSpecMap (𝟙 A) = 𝟙 (baseSpec A) := by
  simp [baseSpecMap, ArtinianLocalAlgCat.id_hom, ← CommRingCat.ofHom_id]

/-- The map of spectra induced by a composite `f ≫ g` of morphisms of `𝒞_Λ` is the composite
`baseSpecMap g ≫ baseSpecMap f`. -/
theorem baseSpecMap_comp {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    baseSpecMap (f ≫ g) = baseSpecMap g ≫ baseSpecMap f := by
  simp only [baseSpecMap, ArtinianLocalAlgCat.comp_hom]
  change Spec.map (CommRingCat.ofHom (g.hom.toRingHom.comp f.hom.toRingHom)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/-- The closed point of the spectrum of an object of `𝒞_Λ`, as a map from the spectrum of the
residue field. -/
noncomputable abbrev residueSpecMap {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) : Spec (.of k) ⟶ baseSpec A :=
  Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A))

/-- **The closed points of the spectra of `𝒞_Λ` are compatible with the maps of spectra.** For a
morphism `f : A ⟶ B` of `𝒞_Λ` the closed point of `Spec A` is the closed point of `Spec B`
followed by `Spec f`, because a morphism of `𝒞_Λ` respects the chosen identifications of the
residue fields with `k`. -/
theorem residueSpecMap_naturality {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    residueSpecMap B ≫ baseSpecMap f = residueSpecMap A := by
  have hring : (CommRingCat.ofHom f.hom.toRingHom : CommRingCat.of A ⟶ CommRingCat.of B) ≫
      CommRingCat.ofHom (Deformation.Artin.residueMap B) =
      CommRingCat.ofHom (Deformation.Artin.residueMap A) := by
    ext a
    exact f.residue_comm a
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, hring]

end Deformation.Examples
