module

public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModulePropagation
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFullness

/-!
# Full faithfulness of `(-)ᵃ` on the slice of a small étale site at an affine chart

Let `X` be an étale chart of an algebraic space whose underlying scheme is affine. For
quasi-coherent modules `M`, `N` on that scheme, the map `φ ↦ φᵃ` from morphisms `M ⟶ N` to maps of
associated presheaves of modules on the slice of the small étale site at `X` is bijective; this is
the full faithfulness of [Stacks, Tag 0GN7] on that slice. The object
`CategoryTheory.Over.mk (𝟙 X)` is terminal in the slice and its structure morphism to the chart's
scheme is the identity, which gives the affine-local half of fullness.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.nonempty_hom_mk_id_slice`: every object of the slice at `X`
  has a morphism to `CategoryTheory.Over.mk (𝟙 X)`.
* `AlgebraicGeometry.Space.SmallEtale.exists_hom_associatedModuleMap_app_eq_slice`: every map
  `Mᵃ ⟶ Nᵃ` agrees over the affine objects of the slice with `φᵃ` for some `φ : M ⟶ N`.
* `AlgebraicGeometry.Space.SmallEtale.surjective_associatedModuleMap_slice_of_isAffineChart`:
  the map `φ ↦ φᵃ` is surjective.
* `AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice`: the map `φ ↦ φᵃ` is
  bijective.

## Implementation notes

The invertibility of the structure morphism of `CategoryTheory.Over.mk (𝟙 X)` is supplied by a
`have` with its type written out, transported along
`AlgebraicGeometry.Space.SmallEtale.sliceToOver_obj_mk_id_hom`: instance search does not reduce
`((sliceToOver B S hS F X).obj (Over.mk (𝟙 X))).hom` to an identity on its own, that functor being
a `CategoryTheory.Over.post` of a composite.

## References

* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F)

/-- Every object `Z` of the slice `CategoryTheory.Over X` has a morphism to
`CategoryTheory.Over.mk (𝟙 X)`, given by the structure morphism of `Z`. -/
public theorem nonempty_hom_mk_id_slice (Z : Over X) : Nonempty (Z ⟶ Over.mk (𝟙 X)) :=
  ⟨Over.homMk Z.hom⟩

/-- Let `X` be an étale chart of an algebraic space whose underlying scheme is affine and let `M`,
`N` be quasi-coherent modules on that scheme. Then every map `a : Mᵃ ⟶ Nᵃ` of associated presheaves
of modules on the slice of the small étale site at `X` agrees, over the objects of the slice whose
underlying scheme is affine, with the map induced by some morphism `φ : M ⟶ N`. -/
public theorem exists_hom_associatedModuleMap_app_eq_slice [IsAffine (chartScheme X)]
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : Stacks.Sites.associatedModulePresheaf (chartScheme X) M
        (sliceToOver B S hS F X) ⟶
      Stacks.Sites.associatedModulePresheaf (chartScheme X) N
        (sliceToOver B S hS F X)) :
    ∃ φ : M ⟶ N, ∀ Z : Over X, IsAffine (chartScheme Z.left) →
      (Stacks.Sites.associatedModuleMap (chartScheme X)
        (sliceToOver B S hS F X) φ).app (op Z) = a.app (op Z) :=
  have : CategoryTheory.IsIso ((sliceToOver B S hS F X).obj (Over.mk (𝟙 X))).hom :=
    sliceToOver_obj_mk_id_hom B S hS F X ▸ CategoryTheory.IsIso.id _
  Stacks.Sites.exists_hom_associatedModuleMap_app_eq_of_isAffine (chartScheme X)
    (sliceToOver B S hS F X) (Over.mk (𝟙 X)) (nonempty_hom_mk_id_slice B S hS F X) a

include hF in
/-- If the associated presheaf of `N` satisfies the sheaf condition, then the map `φ ↦ φᵃ` from
morphisms of quasi-coherent modules on the scheme underlying an affine chart `X` to maps of
associated presheaves of modules on the slice at `X` is surjective. -/
public theorem surjective_associatedModuleMap_slice_of_isAffineChart
    [IsAffine (chartScheme X)]
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) N (sliceToOver B S hS F X))) :
    Function.Surjective fun φ : M ⟶ N =>
      Stacks.Sites.associatedModuleMap (chartScheme X) (sliceToOver B S hS F X) φ :=
  surjective_associatedModuleMap_slice B S hS F hF X hN
    (exists_hom_associatedModuleMap_app_eq_slice B S hS F X)

include hF in
/-- **Full faithfulness of `M ↦ Mᵃ` on the slice of the small étale site at an affine chart.**
If the associated presheaf of `N` satisfies the sheaf condition, then the map `φ ↦ φᵃ` from
morphisms of quasi-coherent modules on the scheme underlying an affine chart `X` to maps of
associated presheaves of modules on the slice at `X` is bijective. -/
public theorem bijective_associatedModuleMap_slice [IsAffine (chartScheme X)]
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) N (sliceToOver B S hS F X))) :
    Function.Bijective fun φ : M ⟶ N =>
      Stacks.Sites.associatedModuleMap (chartScheme X) (sliceToOver B S hS F X) φ :=
  ⟨injective_associatedModuleMap_slice B S hS F X,
    surjective_associatedModuleMap_slice_of_isAffineChart B S hS F hF X hN⟩

end AlgebraicGeometry.Space.SmallEtale

end
