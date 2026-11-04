module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms between spectra of product rings

The spectrum of a product of two rings is the disjoint union of the two spectra, and the
spectrum of a componentwise product of ring maps is the disjoint union of the two induced
morphisms. Consequently any property of morphisms of schemes that is Zariski-local at the
target — being detected on the members of an open cover of the target — may be checked on the
two factors.

## Main results

* `AlgebraicGeometry.coprodMap_specMap_comp_coprodSpec`: the naturality square identifying
  `Spec` of a componentwise product of ring maps with the coproduct of the two induced
  morphisms.
* `AlgebraicGeometry.IsZariskiLocalAtTarget.specMap_prodMap`: a property of morphisms of
  schemes which is Zariski-local at the target holds for `Spec` of a componentwise product of
  two ring maps as soon as it holds for each factor.

## Implementation notes

`AlgebraicGeometry.coprodSpec` is the comparison morphism from the coproduct of the two spectra
to the spectrum of the product ring, and it is an isomorphism. The naturality square is checked
on the two coproduct inclusions, where both sides become `Spec` of a composite of a projection
with a factor map, and the two composites agree because
`RingHom.fst _ _ ∘ RingHom.prodMap f₁ f₂ = f₁ ∘ RingHom.fst _ _` definitionally.

The hypothesis is Zariski-locality at the target rather than stability under coproducts because
that is the hypothesis `AlgebraicGeometry.IsZariskiLocalAtTarget.coprodMap` carries, and no
morphism property in Mathlib is registered as stable under coproducts. A property of the form
`AlgebraicGeometry.geometrically P` for `P` closed under isomorphisms is Zariski-local at the
target, so the result applies in particular to `AlgebraicGeometry.GeometricallyIrreducible`
after rewriting with `AlgebraicGeometry.GeometricallyIrreducible.eq_geometrically`; the
geometric conditions of a disjoint-union base are detected on its pieces because a field-valued
point of the base lands in exactly one of them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- **The spectrum of a componentwise product of ring maps is the coproduct of the two induced
morphisms.** The square formed by the two comparison isomorphisms
`AlgebraicGeometry.coprodSpec` commutes. -/
public theorem coprodMap_specMap_comp_coprodSpec {R₁ R₂ A₁ A₂ : Type u} [CommRing R₁]
    [CommRing R₂] [CommRing A₁] [CommRing A₂] (f₁ : R₁ →+* A₁) (f₂ : R₂ →+* A₂) :
    coprod.map (Spec.map (ofHom f₁)) (Spec.map (ofHom f₂)) ≫ coprodSpec R₁ R₂ =
      coprodSpec A₁ A₂ ≫ Spec.map (ofHom (f₁.prodMap f₂)) := by
  ext1
  · rw [coprod.inl_map_assoc, coprodSpec_inl, ← Category.assoc, coprodSpec_inl,
      ← Spec.map_comp, ← Spec.map_comp, ← ofHom_comp, ← ofHom_comp]
    rfl
  · rw [coprod.inr_map_assoc, coprodSpec_inr, ← Category.assoc, coprodSpec_inr,
      ← Spec.map_comp, ← Spec.map_comp, ← ofHom_comp, ← ofHom_comp]
    rfl

/-- **A property of morphisms of schemes that is Zariski-local at the target is detected on the
pieces of a disjoint-union base.** If `P` holds for `Spec A₁ ⟶ Spec R₁` and for
`Spec A₂ ⟶ Spec R₂`, then it holds for `Spec (A₁ × A₂) ⟶ Spec (R₁ × R₂)`. -/
public theorem IsZariskiLocalAtTarget.specMap_prodMap {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] {R₁ R₂ A₁ A₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing A₁]
    [CommRing A₂] (f₁ : R₁ →+* A₁) (f₂ : R₂ →+* A₂) (h₁ : P (Spec.map (ofHom f₁)))
    (h₂ : P (Spec.map (ofHom f₂))) : P (Spec.map (ofHom (f₁.prodMap f₂))) := by
  have hfac : Spec.map (ofHom (f₁.prodMap f₂)) =
      inv (coprodSpec A₁ A₂) ≫
        coprod.map (Spec.map (ofHom f₁)) (Spec.map (ofHom f₂)) ≫ coprodSpec R₁ R₂ := by
    rw [coprodMap_specMap_comp_coprodSpec, IsIso.inv_hom_id_assoc]
  rw [hfac]
  exact MorphismProperty.RespectsIso.precomp _ (inv (coprodSpec A₁ A₂)) _
    (MorphismProperty.RespectsIso.postcomp _ (coprodSpec R₁ R₂) _
      (IsZariskiLocalAtTarget.coprodMap _ _ h₁ h₂))

end AlgebraicGeometry

end
