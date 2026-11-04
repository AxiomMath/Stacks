module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FaithfullyFlatExtendScalars

/-!
# Local faithful flatness of the restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`

The presheaf of commutative rings `(f : V → S) ↦ 𝒪_S(f(V))` on the small étale site of `S`
sheafifies to `ε⁻¹𝒪_{S_Zar}`, and the morphism to the structure sheaf of the site which
sheafifies to the structure map of `ε` is
`AlgebraicGeometry.SmallEtale.imageSectionsRestriction`.  Flatness of that morphism on the
affine-image covering is what the flatness criterion of Stacks 0GN1 consumes in the proof of
Stacks 0GNA.

This module records that the same covering witnesses *faithful* flatness.  On a member `V` of
the affine-image covering the structure morphism of `V` is an étale morphism of affine schemes
whose image is exactly the affine open `U` recorded by the index, so the sections map
`𝒪_S(U) ⟶ Γ(V, 𝒪_V)` is not merely flat but faithfully flat: it is flat because `V` is étale
over `S`, and `Spec` of it is surjective because every point of `U` is in the image.  Since
`U` is the image open of `V`, that sections map is the value of
`AlgebraicGeometry.SmallEtale.imageSectionsRestriction` at `V`.

The resulting hypothesis is
`Stacks.Sheaves.RingedToposModules.LocallyFaithfullyFlat`, under which extension of scalars
reflects the zero sheaf.  It is the faithful-flatness input to the third assertion of
Stacks 08H8, that `ε^*𝓕 = 0` forces `𝓕 = 0`.

## Main results

* `AlgebraicGeometry.SmallEtale.faithfullyFlat_imageSectionsRestriction_app_affineImageCover`:
  the restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is faithfully flat at a member of the affine-image
  covering.
* `AlgebraicGeometry.SmallEtale.locallyFaithfullyFlat_imageSectionsRestriction`: the restriction
  is locally faithfully flat for the small étale topology, the affine-image covering being the
  witness.

## References

* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is faithfully flat on the affine-image
covering.**  At a member of `AlgebraicGeometry.SmallEtale.affineImageCover` the image open is
the affine open recorded by the index, so the restriction is the sections map of an étale
morphism of affine schemes onto an affine open contained in its image, which is faithfully
flat. -/
public theorem faithfullyFlat_imageSectionsRestriction_app_affineImageCover
    (T : SmallEtale B S hS) (i : AffineImageIndex B S hS T) :
    ((imageSectionsRestriction B S hS).app
      (Opposite.op ((affineImageCover B S hS T).X i))).hom.FaithfullyFlat := by
  have himg : imageOpen B S hS ((affineImageCover B S hS T).X i) = (i.down.2.1 : S.Opens) :=
    TopologicalSpace.Opens.ext
      ((imageOpen_coe B S hS _).trans (range_affineImageCover_X B S hS T i))
  have e : (⊤ : ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)).Opens) ≤
      ((affineImageCover B S hS T).X i).obj.hom.hom ⁻¹ᵁ
        imageOpen B S hS ((affineImageCover B S hS T).X i) :=
    fun x _ => ⟨x, rfl⟩
  rw [imageSectionsRestriction_app_eq_appLE B S hS _ e]
  exact ((((affineImageCover B S hS T).X i).obj.hom.hom).appLE_congr e himg rfl
    (fun φ => φ.hom.FaithfullyFlat)).mpr (faithfullyFlat_appLE_affineImageCover B S hS T i _)

/-- **The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is locally faithfully flat.**  Every object of
the small étale site of `S` is covered by its affine opens whose image in `S` is an affine open,
and over such a member the restriction is faithfully flat.  This is the hypothesis under which
extension of scalars along the morphism reflects the zero sheaf. -/
public theorem locallyFaithfullyFlat_imageSectionsRestriction :
    Stacks.Sheaves.RingedToposModules.LocallyFaithfullyFlat
      (topology B S hS) (imageSectionsRestriction B S hS) :=
  fun T => ⟨AffineImageIndex B S hS T, (affineImageCover B S hS T).X,
    (affineImageCover B S hS T).f, mem_topology_sieve₀_affineImageCover B S hS T,
    faithfullyFlat_imageSectionsRestriction_app_affineImageCover B S hS T⟩

end AlgebraicGeometry.SmallEtale

end
