module

public import StacksFrontier.Deformation.Representation.Cofibered
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.Examples.Linear.RepresentationsRimSchlessinger
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport

/-!
# Deformations of a representation form a deformation category (Stacks 0DVS)

The library carries two presentations of the category `ℱ` of Stacks Project, Tag 0D3J:
`Deformation.RepresentationCategory`, in which the infinitesimal-automorphism and tangent-space
results of Tag 0DVT are written, and `Deformation.Examples.FiniteProjectiveRepresentation`, in
which the Rim–Schlessinger condition of Tag 0DVS is proved. The two structures have the same
fields, so the first embeds in the second by the identity on every component; this file records
that comparison functor and transports Tag 0DVS across it, so that
`Deformation.deformationCategoryProjection` — the projection the Tag 0DVT results are stated
over — is known to be a deformation category.

The transport is `Deformation.Examples.satisfiesRS_comp`, which needs the comparison functor to
be full, faithful and surjective on objects on the nose; all three hold because the comparison
is the identity on fields. The deformation-category property of the slice is then
`Deformation.Examples.isDeformationCategory_objectsOverFunctor_of_baseIso` applied to
`Deformation.Examples.residueFieldBaseIso`, the comparison of the two spellings of the residue
field as an object of `𝒞_Λ`.

## Main definitions

* `Deformation.RepresentationCategory.toFiniteProjective`: the comparison functor.

## Main results

* `Deformation.RepresentationCategory.satisfiesRS_representationProjection`: condition (RS)
  for the projection of the representation category.
* `Deformation.isDeformationCategory_deformationCategoryProjection`: **Stacks 0DVS** for
  `Deformation.deformationCategoryProjection`.

## References

* [Stacks Project, Tag 0DVS](https://stacks.math.columbia.edu/tag/0DVS)
* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
-/

@[expose] public section

open CategoryTheory Deformation.Examples

namespace Deformation

universe u v w m x

namespace RepresentationCategory

variable {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]

/-- The comparison functor from the representation category of Tag 0D3J to its presentation as
finite projective representations: the identity on every field. -/
def toFiniteProjective :
    RepresentationCategory.{u, v, w, m, x} Λ k Γ ⥤
      FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ where
  obj X := { base := X.base, carrier := X.carrier, action := X.action }
  map f :=
    { base := f.base
      map := f.map
      map_smul := f.map_smul
      equivariant := f.equivariant
      isBaseChange := f.isBaseChange }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor lies over the identity of the coefficient algebras. -/
theorem toFiniteProjective_comp_projection :
    toFiniteProjective.{u, v, w, m, x} (Λ := Λ) (k := k) (Γ := Γ) ⋙
        FiniteProjectiveRepresentation.projection = representationProjection :=
  rfl

/-- The comparison functor `toFiniteProjective` is full: every morphism of finite projective
representations is the image of a morphism of the representation category. -/
instance : (toFiniteProjective.{u, v, w, m, x} (Λ := Λ) (k := k) (Γ := Γ)).Full where
  map_surjective f :=
    ⟨{ base := f.base
       map := f.map
       map_smul := f.map_smul
       equivariant := f.equivariant
       isBaseChange := f.isBaseChange }, rfl⟩

/-- The comparison functor `toFiniteProjective` is faithful: it is injective on morphisms. -/
instance : (toFiniteProjective.{u, v, w, m, x} (Λ := Λ) (k := k) (Γ := Γ)).Faithful where
  map_injective := by
    intro X Y f g h
    refine Hom.ext (congrArg (fun q => q.base) h) ?_
    exact eq_of_heq (heq_of_eq (congrArg (fun q => q.map) h))

/-- The comparison functor `toFiniteProjective` is surjective on objects on the nose, which is
what the transport of condition (RS) requires. -/
theorem toFiniteProjective_obj_surjective :
    Function.Surjective
      (toFiniteProjective.{u, v, w, m, x} (Λ := Λ) (k := k) (Γ := Γ)).obj :=
  fun Y => ⟨{ base := Y.base, carrier := Y.carrier, action := Y.action }, rfl⟩

/-- Finite projective representations in the presentation of Tag 0D3J satisfy the
Rim–Schlessinger condition. -/
theorem satisfiesRS_representationProjection :
    SatisfiesRS
      (representationProjection.{u, w, w, m, x} (Λ := Λ) (k := k) (Γ := Γ)) :=
  satisfiesRS_comp toFiniteProjective.{u, w, w, m, x}
    toFiniteProjective_obj_surjective _
    FiniteProjectiveRepresentation.satisfiesRS_projection_carrierUniverse

end RepresentationCategory

/-- The deformations of a finite-dimensional representation form a deformation category, for the
projection the Tag 0DVT results are written over. -/
theorem isDeformationCategory_deformationCategoryProjection
    {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) :
    IsDeformationCategory (deformationCategoryProjection (Λ := Λ) V ρ₀) :=
  isDeformationCategory_objectsOverFunctor_of_baseIso _
    RepresentationCategory.satisfiesRS_representationProjection
    (RepresentationCategory.specialFiber (Λ := Λ) V ρ₀)
    (Examples.residueFieldBaseIso (Λ := Λ) (k := k))

end Deformation

end
